"""
gelfand.sage — Forge-grade Gelfand-pair screen for commutative Schurian
association schemes.

Enumerates pairs (G, H) with G nonabelian from SmallGroups, H over
conjugacy classes of subgroups; keeps Gelfand pairs (permutation character
1_H^G multiplicity-free); computes per-pair scheme quantities and the
verdict cascade from Cc2-ccsieve-spec.md (rev2); emits sharded JSONL.

Library survey (mandatory per card Fg4):

  (a) CharacterTable + Irr caching per G:
      CharacterTable(G) is a GAP attribute — cached on the GAP object
      after the first call. Irr(CharacterTable(G)) similarly cached.
      We cache the Python-side binding (ct, irrs) per SmallGroup(order,
      gidx) and pass them to is_gelfand for every (G, H) pair.

  (b) InducedClassFunction vs InducedClassFunctionsByFusionMap:
      InducedClassFunction(triv_H, G) uses class-function induction via
      the full conjugacy-class fusion map. InducedClassFunctionsByFusionMap
      is lower-level and requires a pre-computed fusion; for our use
      (one induction per pair, small groups), InducedClassFunction is
      canonical and not a bottleneck.

  (c) FactorCosetAction image degree:
      FactorCosetAction(G, H) returns a group homomorphism; Image() gives
      a permutation group on [1..N] where N = [G:H]. Degree = N.

  (d) Orbits with OnTuples on Cartesian:
      Orbits(permG, Cartesian([1..N],[1..N]), OnTuples) materializes all
      N^2 tuples in GAP. For N <= ~200 (orders 2-255), this is at most
      40,000 tuples per pair — fine. OrbitsDomain is equivalent on a
      finite domain.  For N > 500, a seed-based orbit walk would be
      cheaper, but not needed at this scale.

  (e) ConjugacyClassesSubgroups cost at order 128-255:
      This is the main per-group bottleneck for 2-groups: order-128
      groups may have hundreds of conjugacy classes of subgroups.
      Measured: the median cost is ~0.1s per group at order 128,
      but outliers reach 1-2s.  The per-pair budget guards against
      pathological orbital computation, not subgroup enumeration.

  (f) IdSmallGroup:
      Not all orders/sizes are in the IdSmallGroup range.  We guard
      with try/except and emit [h_order, null] on failure.

Spec: .tasks/f5exp/docs/Cc2-ccsieve-spec.md (rev2)
Campaign: f5exp / Fg4.

Modes:
  --toy              Orders 2..24, single-process, fast; exercises
                     shard/checkpoint/resume paths.
  (default)          Full: orders 2..255. Requires --pilot before committing.
  --order-min N      Override minimum order (default 2).
  --order-max N      Override maximum order (default 255).
  --include-256      Allow order 256 (56,092 groups; explicit opt-in).
  --pilot N          Process N groups at the top order, print measured rate
                     + projection, then exit.
  --dry-run          Print space table (nonabelian counts per order) and exit.
  --workers N        Spawn N worker subprocesses (default 1).
  --shard I/N        Run shard I of N (0-indexed, for worker dispatch).
  --budget-ms MS     Per-pair orbital computation budget in milliseconds
                     (default 30000). Pairs exceeding the budget emit
                     SKIPPED_BUDGET instead of stalling.

Output: Scratch/GroupSieve/forge/out/gelfand/<name>.shard<I>of<N>.jsonl

Space projections (--dry-run):

  Orders 2..127:  ~1,800 nonabelian groups, ~39,000 pairs, ~4.5 min/core.
  Orders 128..255: adds ~5,600 nonabelian groups (2,313 at order 128,
                   ~1,400 at order 192), with larger subgroup lattices.
  Order 256:       56,092 groups (all 2-groups); gated behind --include-256.

USAGE:
  cd .../Scratch/GroupSieve/forge
  sage gelfand.sage -- --toy
  sage gelfand.sage -- --dry-run
  sage gelfand.sage -- --dry-run --order-max 511 --include-256
  sage gelfand.sage -- --pilot 20 --workers 1
  sage gelfand.sage -- --workers 4
  sage gelfand.sage -- --shard 0/4
"""

import argparse
import json
import os
import sys
import time
from math import floor, sqrt
from pathlib import Path

# forgelib is a plain .py in the same directory
sys.path.insert(0, str(Path(__file__).resolve().parent))
import forgelib

REPO_ROOT = Path("/home/exedev/p/proofs")
FORGE_OUT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "forge" / "out" / "gelfand"

FORGE_OUT_DIR.mkdir(parents=True, exist_ok=True)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

ORDER_MIN_DEFAULT = 2
ORDER_MAX_DEFAULT = 255
TOY_ORDER_MAX = 24

# Per-pair orbital computation budget (ms).  The O(r^3) partners /
# triangle_count loops are acceptable for r <= a few hundred, but a
# pathological pair could stall.  Pairs exceeding the budget emit
# SKIPPED_BUDGET.
DEFAULT_BUDGET_MS = 30000

# Chunk size for work units — at this scale (order, group) is already
# fine-grained; chunk_size controls how many group indices per unit.
CHUNK_SIZE = 200

# Measured baseline: prototype did orders 2..127 at ~145 pairs/s/core
# (39,358 records / 270s).  Conservative estimate for orders up to 255.
RATE_PAIRS_PER_S = 100.0


# ---------------------------------------------------------------------------
# Abelian counting (partition formula, no enumeration)
# ---------------------------------------------------------------------------

def count_abelian(order):
    """Number of abelian groups of a given order: prod p(a_i) over the
    prime factorization."""
    c = 1
    for _, a in factor(order):
        c *= number_of_partitions(a)
    return int(c)


# ---------------------------------------------------------------------------
# Core pipeline: Gelfand check
# ---------------------------------------------------------------------------

def is_gelfand(G, H, ct, irrs):
    """
    Check if (G, H) is a Gelfand pair, reusing a precomputed character
    table and irreducible characters of G.

    Returns (True, multiplicities) or (False, None).
    multiplicities = sorted list of degrees of irreps appearing in 1_H^G.
    """
    triv_H = libgap.TrivialCharacter(H)
    ind = libgap.InducedClassFunction(triv_H, G)
    appearing_degrees = []
    for chi in irrs:
        sp = int(libgap.ScalarProduct(ct, ind, chi))
        if sp > 1:
            return False, None
        if sp == 1:
            appearing_degrees.append(int(chi.DegreeOfCharacter()))
    return True, sorted(appearing_degrees)


# ---------------------------------------------------------------------------
# Core pipeline: orbital computation with flat array + budget
# ---------------------------------------------------------------------------

def compute_scheme_data(G, H, N, budget_ms):
    """
    Compute the Schurian association scheme data for (G, H).

    Uses FactorCosetAction for the permutation representation, then
    computes orbitals (G-orbits on [N]x[N]) via libgap.Orbits with
    OnTuples. Intersection numbers computed pointwise from orbital
    membership.

    Uses a flat N*N int array instead of a dict for pair->orbital lookup.

    Returns (data_dict, None) on success, or (None, reason_str) on budget
    exceeded or error.
    """
    t_start = time.time()
    budget_s = budget_ms / 1000.0
    N = int(N)

    # Permutation representation on G/H
    action = libgap.FactorCosetAction(G, H)
    perm_G = action.Image()

    # Orbitals = orbits of perm_G on [N] x [N] under OnTuples
    pts = libgap.eval("[1..%d]" % N)
    orbitals = libgap.Orbits(perm_G, libgap.Cartesian(pts, pts),
                             libgap.eval("OnTuples"))
    r = int(len(orbitals))

    # Budget check after orbital computation (the GAP-side heavy lift)
    if time.time() - t_start > budget_s:
        return None, "budget_exceeded_orbital"

    # Build pair -> orbital index: flat array indexed as (x-1)*N + (y-1)
    pair_to_orbital = [0] * (N * N)
    for idx, orb in enumerate(orbitals):
        for pair in orb:
            x, y = int(pair[0]), int(pair[1])
            pair_to_orbital[(x - 1) * N + (y - 1)] = idx

    # Identify diagonal orbital
    diag_idx = pair_to_orbital[0]  # (1,1) -> index (0)*N+(0)

    # Compute duals: R_{i*} = {(y,x) : (x,y) in R_i}
    dual = [0] * r
    for i in range(r):
        rep = orbitals[i][0]
        x, y = int(rep[0]), int(rep[1])
        dual[i] = pair_to_orbital[(y - 1) * N + (x - 1)]

    # Is symmetric? (all R_i = R_{i*})
    is_symmetric = all(dual[i] == i for i in range(r))

    # Valencies: v_i = |orbital_i| / N for non-diagonal orbitals
    valencies = []
    for i in range(r):
        if i == diag_idx:
            continue
        v_i = int(len(orbitals[i])) // N
        valencies.append(v_i)

    # Budget check before intersection numbers
    if time.time() - t_start > budget_s:
        return None, "budget_exceeded_pre_pijk"

    # Intersection numbers p^k_{i,j}
    # p^k_{i,j} = |{z in [N] : (x,z) in R_i and (z,y) in R_j}| for (x,y) in R_k
    p_ijk = [[[0] * r for _ in range(r)] for _ in range(r)]
    for k in range(r):
        rep = orbitals[k][0]
        x, y = int(rep[0]), int(rep[1])
        x_off = (x - 1) * N
        y_off_base = y - 1
        for z in range(N):
            i_idx = pair_to_orbital[x_off + z]
            j_idx = pair_to_orbital[z * N + y_off_base]
            p_ijk[i_idx][j_idx][k] += 1

    # Budget check before O(r^3) loops
    if time.time() - t_start > budget_s:
        return None, "budget_exceeded_pre_partners"

    # Partners: partners(j) = |{(i,k) : p^{k*}_{i,j} > 0}|
    partners = []
    for j in range(r):
        count = 0
        for i in range(r):
            for k in range(r):
                k_star = dual[k]
                if p_ijk[i][j][k_star] > 0:
                    count += 1
        partners.append(count)

    # Budget check before triangle count
    if time.time() - t_start > budget_s:
        # We got partners but not triangle_count — still useful, emit partial
        return None, "budget_exceeded_pre_triangle"

    # Triangle count: |{(i,j,k) : p^{k*}_{i,j} > 0}|
    tri_count = 0
    for i in range(r):
        for j in range(r):
            for k in range(r):
                k_star = dual[k]
                if p_ijk[i][j][k_star] > 0:
                    tri_count += 1

    return {
        "r": r,
        "is_symmetric": is_symmetric,
        "valencies": valencies,
        "partners": partners,
        "triangle_count": tri_count,
    }, None


# ---------------------------------------------------------------------------
# Verdict cascade (spec Section 3)
# ---------------------------------------------------------------------------

def compute_verdict(N, r, is_thin, G_abelian, H_normal, quotient_abelian, partners):
    """
    Apply the verdict cascade from Cc2-ccsieve-spec.md Section 3.
    Returns (verdict, nc4_bound, cap_eff, nc1_pass, nc2_pass).
    """
    N = int(N)
    r = int(r)

    # 1. TRIVIAL_SMALL
    if N <= 2 or r <= 3:
        return "TRIVIAL_SMALL", 0, 0, False, False

    # 2. TRIVIAL_ABELIAN_G (defensive; outer loop skips abelian G)
    if G_abelian:
        return "TRIVIAL_ABELIAN_G", 0, 0, False, False

    # 3. TRIVIAL_ABELIAN_QUOTIENT: H normal and G/H abelian
    if H_normal and quotient_abelian:
        return "TRIVIAL_ABELIAN_QUOTIENT", 0, 0, False, False

    # 4. TRIVIAL_THIN: rank = N (H is normal => thin)
    if is_thin:
        return "TRIVIAL_THIN", 0, 0, False, False

    # 5. REJECT_RANK: r < 4
    if r < 4:
        return "REJECT_RANK", 0, 0, False, False

    # Compute capacity quantities
    nc4_bound = int(floor(sqrt(r)))

    # cap_eff = max { n <= floor(sqrt(r)) : |{j : partners(j) >= n}| >= n^2 }
    cap_eff = 0
    for n_val in range(nc4_bound, 1, -1):
        eligible = sum(1 for pj in partners if pj >= n_val)
        if eligible >= n_val * n_val:
            cap_eff = n_val
            break

    nc1_pass = (r >= cap_eff * cap_eff) if cap_eff > 0 else False
    nc2_pass = (cap_eff >= 2)

    # 6. REJECT_TRIANGLE: cap_eff < 2 while r >= 4
    if cap_eff < 2:
        return "REJECT_TRIANGLE", nc4_bound, cap_eff, nc1_pass, nc2_pass

    # 7. KEEP
    return "KEEP", nc4_bound, cap_eff, nc1_pass, nc2_pass


# ---------------------------------------------------------------------------
# H_id: guarded IdSmallGroup
# ---------------------------------------------------------------------------

def safe_h_id(H):
    """Return [h_order, index] or [h_order, None] if IdSmallGroup fails."""
    h_order = int(H.Size())
    try:
        sid = libgap.IdSmallGroup(H)
        return [h_order, int(sid[1])]
    except Exception:
        return [h_order, None]


# ---------------------------------------------------------------------------
# Process one group: all (G, H) pairs for a fixed G
# ---------------------------------------------------------------------------

def process_group(order, gidx, budget_ms):
    """Process all Gelfand pairs (G, H) for SmallGroup(order, gidx).

    Returns a list of output records (possibly empty).
    """
    records = []
    G = libgap.SmallGroup(order, gidx)

    # Skip abelian G
    if libgap.IsAbelian(G):
        return records

    # Precompute character table + Irr ONCE per G (fixes defect 1)
    ct = libgap.CharacterTable(G)
    irrs = ct.Irr()

    # Get conjugacy classes of subgroups
    cc = libgap.ConjugacyClassesSubgroups(G)

    for h_class in range(int(len(cc))):
        H = cc[h_class].Representative()
        h_order = int(H.Size())

        # Skip (G, G): trivial, N=1, r=1
        if h_order == int(order):
            continue

        # Skip (G, 1): Gelfand iff G abelian; G nonabelian => not Gelfand
        if h_order == 1:
            continue

        N = int(order) // h_order

        # Quick classification: is H normal?
        H_normal = bool(libgap.IsNormal(G, H))
        quotient_abelian = False

        if H_normal:
            Q = G.FactorGroup(H)
            quotient_abelian = bool(libgap.IsAbelian(Q))

        h_id = safe_h_id(H)

        # For N <= 2, the scheme is trivially small regardless.
        # Still verify Gelfand for completeness.
        if N <= 2:
            is_gelf, mults = is_gelfand(G, H, ct, irrs)
            if not is_gelf:
                continue
            rec = {
                "id": [int(order), int(gidx), h_class],
                "G_id": [int(order), int(gidx)],
                "H_id": h_id,
                "H_class": h_class,
                "N": N,
                "r": N,
                "is_symmetric": True,
                "multiplicities": mults,
                "valencies": [],
                "triangle_count": 0,
                "partners": [],
                "nc4_bound": 0,
                "cap_eff": 0,
                "nc1_pass": False,
                "nc2_pass": False,
                "is_thin": True,
                "verdict": "TRIVIAL_SMALL",
            }
            records.append(rec)
            continue

        # Check Gelfand property via induced character
        is_gelf, mults = is_gelfand(G, H, ct, irrs)
        if not is_gelf:
            continue

        # Normal H => thin scheme (rank = N = [G:H]).
        # Classify without computing full orbital structure.
        if H_normal:
            r = N
            verdict, nc4_bound, cap_eff, nc1_pass, nc2_pass = compute_verdict(
                N, r, True, False, True, quotient_abelian, [])
            rec = {
                "id": [int(order), int(gidx), h_class],
                "G_id": [int(order), int(gidx)],
                "H_id": h_id,
                "H_class": h_class,
                "N": N,
                "r": r,
                "is_symmetric": True,
                "multiplicities": mults,
                "valencies": [],
                "triangle_count": 0,
                "partners": [],
                "nc4_bound": nc4_bound,
                "cap_eff": cap_eff,
                "nc1_pass": nc1_pass,
                "nc2_pass": nc2_pass,
                "is_thin": True,
                "verdict": verdict,
            }
            records.append(rec)
            continue

        # Non-normal H: compute full scheme data (orbitals,
        # intersection numbers, partners, triangle counts).
        scheme, skip_reason = compute_scheme_data(G, H, N, budget_ms)

        if scheme is None:
            # Budget exceeded — emit explicit SKIPPED_BUDGET record
            rec = {
                "id": [int(order), int(gidx), h_class],
                "G_id": [int(order), int(gidx)],
                "H_id": h_id,
                "H_class": h_class,
                "N": N,
                "multiplicities": mults,
                "verdict": "SKIPPED_BUDGET",
                "skip_reason": skip_reason,
            }
            records.append(rec)
            continue

        r = scheme["r"]
        is_thin = (r == N)

        verdict, nc4_bound, cap_eff, nc1_pass, nc2_pass = compute_verdict(
            N, r, is_thin, False, False, False, scheme["partners"])

        rec = {
            "id": [int(order), int(gidx), h_class],
            "G_id": [int(order), int(gidx)],
            "H_id": h_id,
            "H_class": h_class,
            "N": N,
            "r": r,
            "is_symmetric": scheme["is_symmetric"],
            "multiplicities": mults,
            "valencies": scheme["valencies"],
            "triangle_count": scheme["triangle_count"],
            "partners": scheme["partners"],
            "nc4_bound": nc4_bound,
            "cap_eff": cap_eff,
            "nc1_pass": nc1_pass,
            "nc2_pass": nc2_pass,
            "is_thin": is_thin,
            "verdict": verdict,
        }
        records.append(rec)

    return records


# ---------------------------------------------------------------------------
# Shard sweep: process one deterministic slice of work units
# ---------------------------------------------------------------------------

def shard_sweep(shard_i, shard_n, start_order, end_order, out_dir, tag,
                budget_ms):
    """Run one shard's deterministic slice of the Gelfand-pair sweep."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_file = out_dir / forgelib.shard_filename("gelfand", shard_i, shard_n)

    # Build work units for all orders in range
    orders_and_counts = []
    for order in range(int(start_order), int(end_order) + 1):
        n_groups = int(libgap.NumberSmallGroups(order))
        orders_and_counts.append((order, n_groups))

    all_units = forgelib.make_work_units(orders_and_counts, CHUNK_SIZE)
    # Round-robin striping
    my_units = all_units[shard_i::shard_n]

    print("%sGelfand sweep: %d work units (of %d total), orders %d..%d" %
          (tag, len(my_units), len(all_units), start_order, end_order),
          flush=True)

    # Load done ids from ALL shard files.
    # id key is [order, gidx, h_class] — resume at (G, H_class) granularity.
    done_ids = forgelib.load_done_ids(str(out_dir), "gelfand*.jsonl")
    print("%sResume: %d done ids" % (tag, len(done_ids)), flush=True)

    t_start = time.time()
    total_pairs = 0
    total_keep = 0
    total_errors = 0

    with open(out_file, "a") as out_fh:
        for ui, unit in enumerate(my_units):
            order = unit["order"]
            for idx in range(unit["idx_start"], unit["idx_end"] + 1):
                try:
                    recs = process_group(order, idx, budget_ms)
                    for rec in recs:
                        rid = tuple(rec["id"])
                        if rid in done_ids:
                            continue
                        out_fh.write(forgelib.dump_jsonl(rec) + "\n")
                        total_pairs += 1
                        if rec.get("verdict") == "KEEP":
                            total_keep += 1
                except KeyboardInterrupt:
                    out_fh.flush()
                    print("%sInterrupted at [%d,%d]; shard checkpointed." %
                          (tag, order, idx), flush=True)
                    sys.exit(130)
                except Exception as e:
                    err_rec = {
                        "id": [int(order), idx, -1],
                        "G_id": [int(order), idx],
                        "verdict": "ERROR",
                        "error": str(e),
                    }
                    out_fh.write(forgelib.dump_jsonl(err_rec) + "\n")
                    print("%sERROR [%d,%d]: %s" % (tag, order, idx, e),
                          file=sys.stderr, flush=True)
                    total_errors += 1

            out_fh.flush()

            elapsed_total = time.time() - t_start
            if (ui + 1) % 5 == 0 or ui == len(my_units) - 1:
                print(forgelib.progress_line(
                    unit["unit_id"], ui + 1, len(my_units), elapsed_total,
                    prefix=tag), flush=True)

    elapsed = time.time() - t_start
    print("%sShard sweep done: %d pairs emitted (%d KEEP), %d errors, %.1fs" %
          (tag, total_pairs, total_keep, total_errors, elapsed), flush=True)


# ---------------------------------------------------------------------------
# Pilot mode
# ---------------------------------------------------------------------------

def run_pilot(n_pilot, order_max, out_dir, tag, budget_ms):
    """Process n_pilot groups at the top order, print rate + projection."""
    order = int(order_max)
    n_groups = int(libgap.NumberSmallGroups(order))
    n_abelian = count_abelian(order)
    n_nonabelian = n_groups - n_abelian

    print("%sPILOT: order %d, %d groups (%d nonabelian), sampling %d" %
          (tag, order, n_groups, n_nonabelian, n_pilot), flush=True)

    t_start = time.time()
    n_processed = 0
    n_pairs = 0

    for idx in range(1, n_groups + 1):
        if n_processed >= int(n_pilot):
            break
        try:
            G = libgap.SmallGroup(order, idx)
            if bool(libgap.IsAbelian(G)):
                continue
            recs = process_group(order, idx, budget_ms)
            n_pairs += len(recs)
            n_processed += 1
        except KeyboardInterrupt:
            break
        except Exception as e:
            print("%sPILOT ERROR [%d,%d]: %s" % (tag, order, idx, e),
                  file=sys.stderr, flush=True)
            n_processed += 1

    elapsed = time.time() - t_start
    rate_groups = n_processed / elapsed if elapsed > 0 else 0
    rate_pairs = n_pairs / elapsed if elapsed > 0 else 0

    print("%sPILOT RESULT: %d groups -> %d pairs in %.1fs (%.1f groups/s, "
          "%.1f pairs/s)" % (tag, n_processed, n_pairs, elapsed,
                             rate_groups, rate_pairs), flush=True)

    remaining = n_nonabelian - n_processed
    if rate_groups > 0:
        proj_s = remaining / rate_groups
        print("%sPROJECTION: remaining %d nonabelian at %.1f groups/s -> "
              "%.0fs (~%.1f hours) single-core" %
              (tag, remaining, rate_groups, proj_s, proj_s / 3600), flush=True)
    print(flush=True)


# ---------------------------------------------------------------------------
# Toy mode
# ---------------------------------------------------------------------------

def run_toy_mode(out_dir, budget_ms):
    """Orders 2..24, single-process.  Exercises shard/checkpoint/resume."""
    print("=== TOY MODE ===", flush=True)
    print("Orders 2..%d, single-process." % TOY_ORDER_MAX, flush=True)
    print(flush=True)

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    tag = "[toy] "

    shard_sweep(0, 1, ORDER_MIN_DEFAULT, TOY_ORDER_MAX, str(out_dir), tag,
                budget_ms)

    # Quick summary
    done = forgelib.load_done_ids(str(out_dir), "gelfand*.jsonl")
    print(flush=True)
    print("%sToy complete: %d records." % (tag, len(done)), flush=True)


# ---------------------------------------------------------------------------
# Dry-run: space table
# ---------------------------------------------------------------------------

def dry_run(args):
    """Print nonabelian group counts per order and projections."""
    print("=== DRY RUN: Gelfand-pair screen ===", flush=True)
    print(flush=True)

    total_nonabelian = 0
    big_orders = []

    print("  Order | Total | Abelian | Nonabelian", flush=True)
    print("  ------|-------|---------|----------", flush=True)

    for order in range(args.order_min, args.order_max + 1):
        n_groups = int(libgap.NumberSmallGroups(order))
        n_abelian = count_abelian(order)
        n_nonabelian = n_groups - n_abelian
        total_nonabelian += n_nonabelian
        if n_nonabelian >= 100:
            big_orders.append((order, n_groups, n_nonabelian))
        # Print aggregated: every order with nonabelian groups, or sparse
        if n_nonabelian > 0 and (n_nonabelian >= 50 or order <= 48 or order % 32 == 0):
            print("  %5d | %5d | %7d | %10d" %
                  (order, n_groups, n_abelian, n_nonabelian), flush=True)

    print(flush=True)
    print("  Total nonabelian groups: %d" % total_nonabelian, flush=True)
    print("  Estimated pairs (30x nonabelian): ~%d" % (total_nonabelian * 30),
          flush=True)
    print(flush=True)

    if big_orders:
        print("  Orders with >= 100 nonabelian groups:", flush=True)
        for order, ntot, nna in big_orders:
            print("    order %d: %d nonabelian (of %d total)" %
                  (order, nna, ntot), flush=True)

    print(flush=True)
    n_workers = max(args.workers, 1)
    est_pairs = total_nonabelian * 30
    print(forgelib.dry_run_table(
        est_pairs, RATE_PAIRS_PER_S,
        sorted(set([1, 4, 8, 16, n_workers])),
        "Gelfand-pair screen (estimated pairs)"), flush=True)
    print(flush=True)
    print("  Use --pilot N to measure actual rate before committing.",
          flush=True)

    if args.order_max < 256:
        print(flush=True)
        print("  Order 256 (56,092 groups) not included.  Use "
              "--order-max 511 --include-256 to see projections.", flush=True)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv):
    parser = argparse.ArgumentParser(
        description="Gelfand-pair screen — forge-grade cascade (Fg4)")
    parser.add_argument("--toy", action="store_true",
                        help="toy mode: orders 2..%d, single-process" % TOY_ORDER_MAX)
    parser.add_argument("--dry-run", action="store_true",
                        help="print space table and exit; no compute")
    parser.add_argument("--pilot", type=int, default=0, metavar="N",
                        help="process N groups at top order, print rate + projection")
    parser.add_argument("--order-min", type=int, default=ORDER_MIN_DEFAULT)
    parser.add_argument("--order-max", type=int, default=ORDER_MAX_DEFAULT)
    parser.add_argument("--include-256", action="store_true",
                        help="allow order 256 (56,092 groups; explicit opt-in)")
    parser.add_argument("--workers", type=int, default=1,
                        help="spawn N single-core worker subprocesses (default 1)")
    parser.add_argument("--shard", default=None, metavar="I/N",
                        help="run the I-th of N deterministic slices (0-indexed)")
    parser.add_argument("--out-dir", default=str(FORGE_OUT_DIR),
                        help="output directory for shard files")
    parser.add_argument("--budget-ms", type=int, default=DEFAULT_BUDGET_MS,
                        help="per-pair orbital computation budget in ms (default %d)"
                        % DEFAULT_BUDGET_MS)
    args = parser.parse_args(argv)

    # Gate order 256
    if args.order_max >= 256 and not args.include_256 and not args.dry_run:
        # Only gate actual compute; dry-run is allowed to show projections.
        # Check if order 256 is actually in the range.
        if args.order_max >= 256 and args.order_min <= 256:
            print("ERROR: order 256 has 56,092 groups.  Pass --include-256 "
                  "to include it, or use --order-max 255.", flush=True)
            sys.exit(1)

    # --- Dry run ---
    if args.dry_run:
        dry_run(args)
        return

    # --- Toy mode ---
    if args.toy:
        run_toy_mode(args.out_dir, args.budget_ms)
        return

    # --- Pilot mode ---
    if args.pilot > 0:
        run_pilot(args.pilot, args.order_max, args.out_dir, "",
                  args.budget_ms)
        return

    # --- Worker-pool dispatch ---
    if args.workers > 1 and args.shard is None:
        extra = [
            "--out-dir", args.out_dir,
            "--order-min", str(args.order_min),
            "--order-max", str(args.order_max),
            "--budget-ms", str(args.budget_ms),
        ]
        if args.include_256:
            extra.append("--include-256")

        n_workers = min(args.workers, 224)
        pool = forgelib.WorkerPool(
            script=str(Path(__file__).resolve()),
            n_workers=n_workers,
            extra_args=extra,
        )
        print("Launching %d workers for orders %d..%d..." %
              (n_workers, args.order_min, args.order_max), flush=True)
        rc = pool.run()
        if rc != 0 and rc != 130:
            print("Workers exited with code %d" % rc, flush=True)
        sys.exit(rc)

    # --- Single-shard execution ---
    shard_i, shard_n = 0, 1
    if args.shard:
        shard_i, shard_n = (int(x) for x in args.shard.split("/"))
        if not (0 <= shard_i < shard_n):
            parser.error("--shard %s: need 0 <= I < N" % args.shard)
    tag = "[shard %d/%d] " % (shard_i, shard_n) if shard_n > 1 else ""

    shard_sweep(shard_i, shard_n, args.order_min, args.order_max,
                str(args.out_dir), tag, args.budget_ms)


# The sage CLI executes .sage files inside sage_globals(), not
# under __name__ == "__main__" — an if-guard would silently skip.
# Strip the "--" separator that `sage script.sage -- --flags` requires.
main([a for a in sys.argv[1:] if a != "--"])
