"""
gelfand.sage — Gelfand-pair screen for commutative Schurian association schemes.

Enumerates pairs (G, H) with G nonabelian from SmallGroups orders 2-127,
H over conjugacy classes of subgroups; keeps Gelfand pairs (permutation
character multiplicity-free); computes per-pair scheme quantities and
tier predicates from Cc2-ccsieve-spec.md; emits JSONL.

Spec: .tasks/f5exp/docs/Cc2-ccsieve-spec.md (rev2)
Campaign: f5exp / Im7.

USAGE (USER-run only, per sieve policy):
  cd /home/exedev/p/proofs/Scratch/GroupSieve && sage gelfand.sage

  sage gelfand.sage -- --resume
      Resume from checkpoint.

  sage gelfand.sage -- --order-min 48 --order-max 96
      Restrict order range.

  sage gelfand.sage -- --dry-run
      Print space stats and exit.
"""

import json
import os
import sys
import time
from math import floor, sqrt
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT = Path("/home/exedev/p/proofs")
SIEVE_DIR = REPO_ROOT / "Scratch" / "GroupSieve"
CHECKPOINT_DIR = SIEVE_DIR / "checkpoints"
CHECKPOINT_FILE = CHECKPOINT_DIR / "gelfand_progress.jsonl"
OUTPUT_FILE = SIEVE_DIR / "gelfand-screen.jsonl"

ORDER_MIN = 2
ORDER_MAX = 127
RESUME = False
DRY_RUN = False

# Parse arguments (preparse-safe, no argparse in .sage files with sage preparser).
args = sys.argv[1:]
i = 0
while i < len(args):
    if args[i] == "--resume":
        RESUME = True
        i += 1
    elif args[i] == "--dry-run":
        DRY_RUN = True
        i += 1
    elif args[i] == "--order-min" and i + 1 < len(args):
        ORDER_MIN = int(args[i + 1])
        i += 2
    elif args[i] == "--order-max" and i + 1 < len(args):
        ORDER_MAX = int(args[i + 1])
        i += 2
    else:
        i += 1


# ---------------------------------------------------------------------------
# JSON serialization helper (Sage preparser converts literals to Integer/RR)
# ---------------------------------------------------------------------------

def sanitize(obj):
    """Recursively convert Sage Integer/RR types to native Python for JSON."""
    if isinstance(obj, dict):
        return {k: sanitize(v) for k, v in obj.items()}
    elif isinstance(obj, (list, tuple)):
        return [sanitize(x) for x in obj]
    elif isinstance(obj, bool):
        return obj
    elif hasattr(obj, "__index__"):
        return int(obj)
    elif isinstance(obj, float):
        return obj
    elif isinstance(obj, str):
        return obj
    # Catch Sage RealDoubleElement and similar
    try:
        return float(obj)
    except (TypeError, ValueError):
        return str(obj)


def dump_json(rec):
    """Serialize a record to compact JSON, handling Sage types."""
    return json.dumps(sanitize(rec), separators=(",", ":"))


# ---------------------------------------------------------------------------
# Resume / checkpoint
# ---------------------------------------------------------------------------

def load_done_orders():
    """Load set of completed orders from the checkpoint file."""
    done = set()
    if CHECKPOINT_FILE.exists():
        with open(CHECKPOINT_FILE) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    if rec.get("type") == "order_complete":
                        done.add(rec["order"])
                except (json.JSONDecodeError, KeyError):
                    pass
    return done


def checkpoint_order_complete(fh, order, n_pairs, elapsed):
    """Write a checkpoint marker for a completed order."""
    rec = {
        "type": "order_complete",
        "order": int(order),
        "n_pairs": int(n_pairs),
        "elapsed_s": round(float(elapsed), 2),
    }
    fh.write(dump_json(rec) + "\n")
    fh.flush()


# ---------------------------------------------------------------------------
# Core pipeline
# ---------------------------------------------------------------------------

def is_gelfand(G, H):
    """
    Check if (G, H) is a Gelfand pair.
    Returns (True, multiplicities) or (False, None).
    multiplicities = sorted list of degrees of irreps appearing in 1_H^G.
    """
    ct = libgap.CharacterTable(G)
    irrs = ct.Irr()
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


def compute_scheme_data(G, H, N):
    """
    Compute the Schurian association scheme data for (G, H).

    Uses FactorCosetAction for the permutation representation, then
    computes orbitals (G-orbits on [N]x[N]) via libgap.Orbits with
    OnTuples. Intersection numbers computed pointwise from orbital
    membership in O(r * N) time.

    Returns dict with rank, valencies, intersection numbers, partners, etc.
    """
    # Permutation representation on G/H
    action = libgap.FactorCosetAction(G, H)
    perm_G = action.Image()

    # Orbitals = orbits of perm_G on [N] x [N] under OnTuples
    pts = libgap.eval("[1..%d]" % int(N))
    orbitals = libgap.Orbits(perm_G, libgap.Cartesian(pts, pts),
                             libgap.eval("OnTuples"))
    r = int(len(orbitals))

    # Build pair -> orbital index lookup
    pair_to_orbital = {}
    for idx, orb in enumerate(orbitals):
        for pair in orb:
            pair_to_orbital[(int(pair[0]), int(pair[1]))] = idx

    # Identify diagonal orbital
    diag_idx = pair_to_orbital[(1, 1)]

    # Compute duals: R_{i*} = {(y,x) : (x,y) in R_i}
    dual = [0] * r
    for i in range(r):
        rep = orbitals[i][0]
        x, y = int(rep[0]), int(rep[1])
        dual[i] = pair_to_orbital[(y, x)]

    # Is symmetric? (all R_i = R_{i*})
    is_symmetric = all(dual[i] == i for i in range(r))

    # Valencies: v_i = |orbital_i| / N for non-diagonal orbitals
    valencies = []
    for i in range(r):
        if i == diag_idx:
            continue
        v_i = int(len(orbitals[i])) // int(N)
        valencies.append(v_i)

    # Intersection numbers p^k_{i,j}
    # p^k_{i,j} = |{z in [N] : (x,z) in R_i and (z,y) in R_j}| for (x,y) in R_k
    p_ijk = [[[0] * r for _ in range(r)] for _ in range(r)]
    for k in range(r):
        rep = orbitals[k][0]
        x, y = int(rep[0]), int(rep[1])
        for z in range(1, int(N) + 1):
            i_idx = pair_to_orbital[(x, z)]
            j_idx = pair_to_orbital[(z, y)]
            p_ijk[i_idx][j_idx][k] += 1

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
    }


def compute_verdict(N, r, is_thin, G_abelian, H_normal, quotient_abelian, partners):
    """
    Apply the verdict cascade from spec Section 3.
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
# Main loop
# ---------------------------------------------------------------------------

def main():
    print("=== Gelfand-Pair Screen (orders %d-%d) ===" % (int(ORDER_MIN), int(ORDER_MAX)),
          flush=True)

    if DRY_RUN:
        # Count nonabelian groups in range
        total_groups = 0
        nonabelian_groups = 0
        for order in range(int(ORDER_MIN), int(ORDER_MAX) + 1):
            n_groups = int(libgap.NumberSmallGroups(order))
            total_groups += n_groups
            for gidx in range(1, n_groups + 1):
                G = libgap.SmallGroup(order, gidx)
                if not libgap.IsAbelian(G):
                    nonabelian_groups += 1
        print("  Total groups: %d" % total_groups, flush=True)
        print("  Nonabelian groups: %d" % nonabelian_groups, flush=True)
        print("  Estimated pairs (30x nonabelian): ~%d" % (nonabelian_groups * 30),
              flush=True)
        return

    # Resume state
    done_orders = set()
    if RESUME:
        done_orders = load_done_orders()
        print("  Resuming: %d orders already done" % len(done_orders), flush=True)

    # Open output and checkpoint files
    out_mode = "a" if RESUME else "w"
    out_fh = open(OUTPUT_FILE, out_mode)
    ckpt_fh = open(CHECKPOINT_FILE, "a" if RESUME else "w")

    t_global_start = time.time()
    total_pairs_emitted = 0
    total_gelfand = 0
    total_keep = 0

    for order in range(int(ORDER_MIN), int(ORDER_MAX) + 1):
        if order in done_orders:
            continue

        t_order_start = time.time()
        n_groups = int(libgap.NumberSmallGroups(order))
        n_pairs_this_order = 0

        for gidx in range(1, n_groups + 1):
            G = libgap.SmallGroup(order, gidx)

            # Skip abelian G (spec Section 5A: thin schemes subject to
            # cap-set barrier, not worth screening for Conjecture 5.7)
            if libgap.IsAbelian(G):
                continue

            # Get conjugacy classes of subgroups
            cc = libgap.ConjugacyClassesSubgroups(G)

            for h_class in range(int(len(cc))):
                H = cc[h_class].Representative()
                h_order = int(H.Size())

                # Skip (G, G): trivial, N=1, r=1
                if h_order == order:
                    continue

                # Skip (G, 1): Gelfand iff G abelian; G nonabelian => not Gelfand
                if h_order == 1:
                    continue

                N = order // h_order

                # Quick classification: is H normal?
                H_normal = bool(libgap.IsNormal(G, H))
                quotient_abelian = False

                if H_normal:
                    Q = G.FactorGroup(H)
                    quotient_abelian = bool(libgap.IsAbelian(Q))

                # For N <= 2, the scheme is trivially small regardless.
                # Still verify Gelfand for completeness.
                if N <= 2:
                    is_gelf, mults = is_gelfand(G, H)
                    if not is_gelf:
                        continue
                    total_gelfand += 1
                    rec = {
                        "G_id": [order, gidx],
                        "H_id": [h_order, int(libgap.IdSmallGroup(H)[1])],
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
                    out_fh.write(dump_json(rec) + "\n")
                    n_pairs_this_order += 1
                    total_pairs_emitted += 1
                    continue

                # Check Gelfand property via induced character
                is_gelf, mults = is_gelfand(G, H)
                if not is_gelf:
                    continue
                total_gelfand += 1

                # Normal H => thin scheme (rank = N = [G:H]).
                # Classify without computing full orbital structure.
                if H_normal:
                    r = N
                    verdict, nc4_bound, cap_eff, nc1_pass, nc2_pass = compute_verdict(
                        N, r, True, False, True, quotient_abelian, [])
                    rec = {
                        "G_id": [order, gidx],
                        "H_id": [h_order, int(libgap.IdSmallGroup(H)[1])],
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
                    out_fh.write(dump_json(rec) + "\n")
                    n_pairs_this_order += 1
                    total_pairs_emitted += 1
                    if verdict == "KEEP":
                        total_keep += 1
                    continue

                # Non-normal H: compute full scheme data (orbitals,
                # intersection numbers, partners, triangle counts).
                scheme = compute_scheme_data(G, H, N)
                r = scheme["r"]
                is_thin = (r == N)

                verdict, nc4_bound, cap_eff, nc1_pass, nc2_pass = compute_verdict(
                    N, r, is_thin, False, False, False, scheme["partners"])

                if verdict == "KEEP":
                    total_keep += 1

                rec = {
                    "G_id": [order, gidx],
                    "H_id": [h_order, int(libgap.IdSmallGroup(H)[1])],
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
                out_fh.write(dump_json(rec) + "\n")
                n_pairs_this_order += 1
                total_pairs_emitted += 1

        # Order complete
        order_elapsed = time.time() - t_order_start
        checkpoint_order_complete(ckpt_fh, order, n_pairs_this_order, order_elapsed)

        # Progress print every order
        total_elapsed = time.time() - t_global_start
        print("  order %d: %d groups, %d Gelfand pairs (%.1fs) | "
              "total: %d pairs, %d KEEP, %.0fs elapsed" %
              (order, n_groups, n_pairs_this_order, order_elapsed,
               total_pairs_emitted, total_keep, total_elapsed),
              flush=True)

    out_fh.close()
    ckpt_fh.close()

    total_elapsed = time.time() - t_global_start
    print("", flush=True)
    print("=== Complete ===", flush=True)
    print("  Total Gelfand pairs found: %d" % total_gelfand, flush=True)
    print("  Total records emitted: %d" % total_pairs_emitted, flush=True)
    print("  KEEP verdicts: %d" % total_keep, flush=True)
    print("  Wall time: %.1f minutes" % (total_elapsed / 60.0), flush=True)
    print("  Output: %s" % OUTPUT_FILE, flush=True)


main()
