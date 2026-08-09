"""
cascade.sage — Forge-grade TPP group sieve cascade.

Rewrite of groupsieve.sage for parallel forge execution.  Uses
forge/forgelib.py for worker pool, sharded JSONL, resume, progress,
and Sage-type JSON sanitization.

Library survey (GAP SmallGroups / libgap, mandatory per sieve-spec v1.2):

  (a) Precomputed attributes for library-level filtering:
      - AllSmallGroups(n, IsAbelian, false) returns nonabelian groups
        directly (no instantiate-then-skip). The ids-only variant
        AllSmallGroups(n, IsAbelian, false, IdSmallGroup) is faster
        when only ids are needed.
      - NumberSmallGroups(n) returns the total count per order.
      - Abelian counts per order: prod p(a_i) over prime factorization
        (partition formula, no GAP call needed).

  (b) Per-invariant API functions:
      - CharacterDegrees(G): [[degree, multiplicity], ...] integer pairs.
        NEVER iterate Irr() — libgap is 0-based, chi[1] is the second
        conjugacy-class value (cyclotomic), not the degree. This bug
        caused a 53% crash rate in the first sweep.
      - NilpotencyClassOfGroup(G): integer, only valid if IsNilpotent.
      - MaximalSubgroupClassReps(G): for p-group abelian-index-p test.
      - MaximalNormalSubgroups(G): for non-p-group T3b test.
      - DirectFactorsOfGroup(G): for T3c product decomposition.
      - IdSmallGroup(G): [order, idx] identification.

  (c) Space size distribution:
      - Orders 2..511: 92,803 groups total (incl. abelian).
      - Order 256 alone: 56,092 groups (all 2-groups).
      - Order 512: 10,494,213 groups (all 2-groups) — stratum B.
      - OEIS A060689 for nonabelian counts.
      - Every group of order 2^k is a 2-group.

Modes:
  --toy            Harness + orders 2..24 + 20-id stratum-B sample (seconds).
  (default)        Stratum A: orders 2..511, all nonabelian.
  --stratum-b      Stratum B: order 512 sample or full census.
  --dry-run        Print projections per --workers, no compute.
  --harness-only   Run falsifiability harness and exit.
  --summary-only   Regenerate summary from checkpoints/shards.

Output: Scratch/GroupSieve/forge/out/cascade/<name>.shard<I>of<N>.jsonl
Legacy: Scratch/GroupSieve/checkpoints/order_N.jsonl (importable as done).

T3c product-decomposition tier is conjecture-gated behind
T3C_CONJECTURE=1 (Pf3 is still open); the unconditional bound
rho_0(AxH) <= |A|^2 rho_0(H) is always sound. Both paths and their
provenance labels are preserved.

USAGE:
  sage cascade.sage -- --harness-only
  sage cascade.sage -- --toy
  sage cascade.sage -- --dry-run --workers 128
  sage cascade.sage -- --workers 4
  sage cascade.sage -- --shard 0/4
  sage cascade.sage -- --stratum-b --pilot 200
  sage cascade.sage -- --stratum-b --target 10000 --workers 128
  sage cascade.sage -- --stratum-b --full --workers 224
  sage cascade.sage -- --summary-only
"""

import argparse
import json
import os
import random
import re
import sys
import time
from pathlib import Path

# forgelib is a plain .py in the same directory
sys.path.insert(0, str(Path(__file__).resolve().parent))
import forgelib

REPO_ROOT = Path("/home/exedev/p/proofs")
DOCS_DIR = REPO_ROOT / ".tasks" / "f5exp" / "docs"
LEGACY_CHECKPOINT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "checkpoints"
FORGE_OUT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "forge" / "out" / "cascade"
SUMMARY_FILE = DOCS_DIR / "sieve-summary.md"

FORGE_OUT_DIR.mkdir(parents=True, exist_ok=True)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

STRATUM_A_START = 2
STRATUM_A_END = 511

STRATUM_B_ORDER = 512
STRATUM_B_POPULATION = 10494213
STRATUM_B_SEED = 20260711
STRATUM_B_DEFAULT_TARGET = 10000

# Measured pilot rate (stratum-b-pilot200.log): ~55 groups/s/core.
STRATUM_B_RATE = 55.0
# Stratum-A rate: ~200 groups/s/core (small orders fast, 256 slower).
STRATUM_A_RATE = 200.0

# Chunk size for work units (order 256 = 56,092 -> ~28 chunks).
CHUNK_SIZE = 2000

# T3c conjecture toggle (Pf3 abelian-factor conjecture).
T3C_CONJECTURE_ENABLED = os.environ.get("T3C_CONJECTURE", "0") == "1"


# ---------------------------------------------------------------------------
# Tier predicates — the ONLY copy; harness and sweep both use these.
# ---------------------------------------------------------------------------

def compute_character_degrees(G):
    """Character degrees of G as a set of Python ints, via GAP
    CharacterDegrees() (pairs [degree, multiplicity], 0-indexed here)."""
    degrees = set()
    for pair in G.CharacterDegrees():
        degrees.add(int(pair[0]))
    return degrees


def smallest_nonlinear_irrep_dim(cd_set):
    """n(G) = min{dim pi : dim pi > 1}, or None if abelian. [BCGPU Def 3.1]"""
    dims_gt1 = [d for d in cd_set if d > 1]
    if not dims_gt1:
        return None
    return min(dims_gt1)


def p_group_prime(G):
    """Return p if G is a p-group, else None."""
    order_val = int(G.Order())
    if order_val == 1:
        return None
    f = factor(order_val)
    if len(f) == 1:
        return int(f[0][0])
    return None


def nilpotency_class_or_none(G):
    if G.IsNilpotentGroup():
        return int(G.NilpotencyClassOfGroup())
    return None


def has_abelian_subgroup_index_p(G):
    """p-group G: abelian subgroup of index p (maximal subgroup reps).
    [T3a: Murthy25 Cor 4.3(2); prime-index subgroups of p-groups are
    automatically normal.]"""
    for H in G.MaximalSubgroupClassReps():
        if H.IsAbelian():
            return True
    return False


def abelian_normal_subgroup_prime_index(G, order_G):
    """Non-p-group G: abelian normal subgroup of prime index.
    Returns (True, p) or (False, None). [T3b: Murthy25 Thm 4.1]"""
    for H in G.MaximalNormalSubgroups():
        idx = order_G // int(H.Size())
        if is_prime(idx) and H.IsAbelian():
            return True, int(idx)
    return False, None


def abelian_direct_factor(G):
    """Detect a nontrivial abelian direct factor of G via GAP
    DirectFactorsOfGroup. Returns (abelian_order, complement_id) or
    (None, None). complement_id is [order, idx] if IdSmallGroup resolves.
    Cost: one GAP DirectFactorsOfGroup call (cheap at sieve scale)."""
    df = libgap.DirectFactorsOfGroup(G)
    if len(df) <= 1:
        return None, None
    abelian_factors = []
    nonabelian_factors = []
    for f in df:
        f_order = int(f.Size())
        if libgap.IsAbelian(f):
            abelian_factors.append((f_order, f))
        else:
            nonabelian_factors.append((f_order, f))
    if not abelian_factors:
        return None, None
    ab_order = 1
    for (sz, _) in abelian_factors:
        ab_order *= sz
    if not nonabelian_factors:
        return None, None
    if len(nonabelian_factors) == 1:
        comp_order, comp = nonabelian_factors[0]
        try:
            sid = [int(x) for x in libgap.IdSmallGroup(comp)]
            return int(ab_order), sid
        except Exception:
            return int(ab_order), [int(comp_order), None]
    else:
        comp_order = 1
        for (sz, _) in nonabelian_factors:
            comp_order *= sz
        try:
            prod = nonabelian_factors[0][1]
            for (_, f) in nonabelian_factors[1:]:
                prod = libgap.DirectProduct(prod, f)
            sid = [int(x) for x in libgap.IdSmallGroup(prod)]
            return int(ab_order), sid
        except Exception:
            return int(ab_order), [int(comp_order), None]


# ---------------------------------------------------------------------------
# Tier cascade
# ---------------------------------------------------------------------------

def classify_group(order_val, idx):
    """Classify nonabelian SmallGroup(order_val, idx); returns the
    per-group record (all values JSON-safe Python types)."""
    G = libgap.SmallGroup(order_val, idx)
    order_G = int(order_val)
    z_order = int(G.Centre().Size())
    gz_index = order_G // z_order
    Gp = G.DerivedSubgroup()
    Gp_size = int(Gp.Size())
    Gp_cyclic = bool(Gp.IsCyclic())
    nil_class = nilpotency_class_or_none(G)
    p = p_group_prime(G)

    rec = {
        "id": [order_G, int(idx)],
        "order": order_G,
        "nil_class": nil_class,
        "center_order": z_order,
        "gz_index": gz_index,
        "derived_order": Gp_size,
        "derived_cyclic": Gp_cyclic,
        "p_group": p,
        "tier": None,
        "action": None,
        "flags": [],
        "ceilings": {},
    }

    # T0: abelian => rho_0 = 1 [Murthy26 Thm 2.3 / CU03 Lemma 3.1]
    if G.IsAbelian():
        rec["tier"] = "T0"
        rec["action"] = "REJECT"
        return rec

    # T1a: p-group with |G| <= p^4 => rho_0 = 1 [Murthy26 Prop 2.14]
    if p is not None and order_G <= p**4:
        rec["tier"] = "T1a"
        rec["action"] = "REJECT"
        return rec

    # T1b: class-2 p-group with cd(G) = {1, p} => rho_0 = 1
    # [Murthy26 Thm 6.1; hypothesis is class-2 p-group, not arbitrary G]
    cd = None
    if p is not None and nil_class == 2:
        cd = compute_character_degrees(G)
        rec["cd"] = sorted(cd)
        if cd == {1, int(p)}:
            rec["tier"] = "T1b"
            rec["action"] = "REJECT"
            return rec

    # (No T2a: provably shadowed by T1b — Isaacs Cor 2.30 gives
    # chi(1)^2 <= |G:Z(G)| for every finite group, so under T2a's
    # hypothesis every degree lies in {1, p} and T1b already rejected.
    # T2a fired zero times across 63,988 records for this reason.)

    # T3a: p-group with abelian subgroup of index p => rho_0 = 1
    # [Murthy25 Cor 4.3(2)]
    if p is not None and has_abelian_subgroup_index_p(G):
        rec["tier"] = "T3a"
        rec["action"] = "REJECT"
        return rec

    # T3b: non-p-group with abelian normal subgroup of prime index p
    # => rho_0 <= p^2/(2p-1) [Murthy25 Thm 4.1]; if additionally
    # (2p-1) nmid |G| => rho_0 <= p/2 [Murthy25 Cor 4.3(1)].
    if p is None:
        has_ans, ans_p = abelian_normal_subgroup_prime_index(G, order_G)
        if has_ans:
            cap_val = QQ(ans_p**2) / QQ(2 * ans_p - 1)
            tighter = order_G % (2 * ans_p - 1) != 0
            cap_val_tight = QQ(ans_p) / QQ(2)

            if tighter and cap_val_tight <= 1:
                rec["tier"] = "T3b"
                rec["action"] = "REJECT"
                rec["flags"].append("p=%d, (2p-1)=%d nmid |G|=%d, cap=p/2=%s"
                                    % (ans_p, 2 * ans_p - 1, order_G, float(cap_val_tight)))
                return rec
            elif cap_val <= 1:
                rec["tier"] = "T3b"
                rec["action"] = "REJECT"
                rec["flags"].append("p=%d, cap=p^2/(2p-1)=%s <= 1" % (ans_p, float(cap_val)))
                return rec
            else:
                final_cap = float(cap_val_tight) if tighter else float(cap_val)
                rec["tier"] = "T3b"
                rec["action"] = "CAP(%s)" % final_cap
                rec["ceilings"]["T3b"] = final_cap
                rec["flags"].append("p=%d" % ans_p)
                # fall through to collect packing ceilings

    # T3c: product decomposition — G = A x H with A abelian, H nonabelian.
    # Conjecture (Pf3): rho_0(G) = rho_0(H).
    # Unconditional (Pf3 section 6 item 3): rho_0(G) <= |A|^2 * rho_0(H).
    # Provenance: Pf3-abelian-factor.md + computational sweep (Im6).
    ab_order, comp_id = abelian_direct_factor(G)
    if ab_order is not None and comp_id is not None and comp_id[1] is not None:
        comp_rec = classify_group(comp_id[0], comp_id[1])
        comp_action = comp_rec.get("action", "")
        comp_ceiling = comp_rec.get("ceiling")

        rec["flags"].append("T3c:A=%d,H=[%d,%d]" % (ab_order, comp_id[0], comp_id[1]))
        rec["t3c_complement"] = comp_id
        rec["t3c_abelian_order"] = int(ab_order)
        rec["t3c_complement_action"] = str(comp_action)

        # --- Conjecture-gated prune (equality): default OFF ---
        if T3C_CONJECTURE_ENABLED:
            if comp_action == "REJECT":
                rec["tier"] = "T3c"
                rec["action"] = "REJECT"
                rec["flags"].append("T3c_conjecture_gated")
                rec["t3c_provenance"] = "Pf3 conjecture + computational sweep"
                return rec
            elif "CAP" in str(comp_action) and comp_ceiling is not None:
                rec["ceilings"]["T3c_conj"] = float(comp_ceiling)
                rec["flags"].append("T3c_conjecture_gated")
                rec["t3c_provenance"] = "Pf3 conjecture + computational sweep"

        # --- Unconditional bound: rho_0(G) <= |A|^2 * rho_0(H) ---
        if comp_action == "REJECT":
            uncond_ceil_reject = float(ab_order ** 2)
            rec["ceilings"]["T3c_uncond"] = uncond_ceil_reject
            if uncond_ceil_reject <= 1:
                rec["tier"] = "T3c"
                rec["action"] = "REJECT"
                rec["t3c_provenance"] = "Pf3 unconditional bound"
                return rec
        elif comp_ceiling is not None:
            uncond_ceil = float(ab_order ** 2) * float(comp_ceiling)
            rec["ceilings"]["T3c_uncond"] = uncond_ceil

    # T1c: nonabelian p-group with cyclic G' of order p => rho_0 <= p
    # [Murthy26 Thm 4.1] CAP(p), never REJECT — extraspecial groups
    # achieve rho_0 = p > 1.
    if p is not None and Gp_cyclic and Gp_size == p:
        rec["tier"] = "T1c"
        rec["action"] = "CAP(%d)" % p
        rec["ceilings"]["T1c"] = float(p)

    # T2b: packing ceilings for everything still alive.
    # [BCGPU Thm 3.2: rho_0 <= sqrt(|G|/n(G)) + 1;
    #  BCGPU Cor 3.8: rho_0 <= sqrt(|G:Z(G)|).
    #  The family-level barrier (BCGPU Cor 3.3) MUST NOT hard-reject
    #  individual groups.]
    if cd is None:
        cd = compute_character_degrees(G)
        rec["cd"] = sorted(cd)

    n_G = smallest_nonlinear_irrep_dim(cd)
    rec["n_G"] = n_G

    if n_G is not None:
        rec["ceilings"]["subset_packing"] = float(RR(sqrt(order_G / n_G)) + 1)

    subgroup_ceil = float(RR(sqrt(gz_index)))
    rec["ceilings"]["subgroup_packing"] = subgroup_ceil

    if nil_class == 2:
        rec["ceilings"]["class2_strict"] = subgroup_ceil
        rec["flags"].append("class2_strict_ineq")

    if rec["tier"] is None:
        rec["tier"] = "T2b"
        rec["action"] = "SURVIVE"

    rec["ceiling"] = min(rec["ceilings"].values())
    return rec


# ---------------------------------------------------------------------------
# Falsifiability harness — tier membership is asserted, not just action.
# ---------------------------------------------------------------------------

ANCHORS_REJECT = [
    ((8, 3), ("T1a", "T3a")),     # D8
    ((8, 4), ("T1a", "T3a")),     # Q8
    ((16, 3), ("T1a", "T3a")),
    ((16, 4), ("T1a", "T3a")),
    ((16, 6), ("T1a", "T3a")),
    ((16, 11), ("T1a", "T3a")),
    ((16, 12), ("T1a", "T3a")),
    ((16, 13), ("T1a", "T3a")),
    ((27, 3), ("T1a", "T1b", "T3a")),
    ((27, 4), ("T1a", "T1b", "T3a")),
]

ANCHORS_REJECT_OR_CAP = [
    ((24, 10), "T3b"),
    ((24, 11), "T3b"),
]

ANCHORS_T3C_CONJECTURE_REJECT = [
    ((24, 10), "T3c"),
    ((24, 11), "T3c"),
]

ANCHORS_MUST_NOT_REJECT = [
    ((32, 49), "CAP"),
    ((64, 226), "SURVIVE"),
    ((128, 1135), "SURVIVE"),
    ((128, 2194), "SURVIVE"),
]

ANCHORS_DIHEDRAL = [
    ((12, 4), "CAP", "T3b"),
    ((10, 1), "REJECT", "T3b"),
]


def run_anchor_harness():
    """Returns (passed, n_assertions, failures)."""
    failures = []
    n_assert = 0

    def check(cond, ok_msg, fail_msg):
        nonlocal n_assert
        n_assert += 1
        if cond:
            print("  %s -- OK" % ok_msg, flush=True)
        else:
            failures.append(fail_msg)
            print("  FAIL: %s" % fail_msg, flush=True)

    print("=== Falsifiability Harness ===", flush=True)

    print("--- REJECT anchors (action and tier both asserted) ---", flush=True)
    for (o, i), tiers in ANCHORS_REJECT:
        rec = classify_group(o, i)
        check(rec["action"] == "REJECT" and rec["tier"] in tiers,
              "[%d,%d]: %s REJECT" % (o, i, rec["tier"]),
              "[%d,%d]: expected REJECT at tier in %s, got tier=%s action=%s"
              % (o, i, "/".join(tiers), rec["tier"], rec["action"]))

    print("--- REJECT-or-CAP anchors (known rho_0=1, cascade limited) ---", flush=True)
    if T3C_CONJECTURE_ENABLED:
        print("  (T3C_CONJECTURE=1: expecting T3c REJECT for [24,10]/[24,11])", flush=True)
        for (o, i), tier in ANCHORS_T3C_CONJECTURE_REJECT:
            rec = classify_group(o, i)
            ok = rec["tier"] == tier and rec["action"] == "REJECT"
            check(ok,
                  "[%d,%d]: %s REJECT (conjecture-gated)" % (o, i, rec["tier"]),
                  "[%d,%d]: expected %s REJECT (conjecture ON), got tier=%s action=%s"
                  % (o, i, tier, rec["tier"], rec["action"]))
    else:
        for (o, i), tier in ANCHORS_REJECT_OR_CAP:
            rec = classify_group(o, i)
            ok = rec["tier"] == tier and (rec["action"] == "REJECT" or "CAP" in str(rec["action"]))
            check(ok,
                  "[%d,%d]: %s %s (conservative bound)" % (o, i, rec["tier"], rec["action"]),
                  "[%d,%d]: expected %s REJECT/CAP, got tier=%s action=%s"
                  % (o, i, tier, rec["tier"], rec["action"]))

    print("--- MUST-NOT-REJECT anchors (known rho_0 > 1) ---", flush=True)
    for (o, i), pattern in ANCHORS_MUST_NOT_REJECT:
        rec = classify_group(o, i)
        ok = rec["action"] != "REJECT" and pattern in str(rec["action"])
        check(ok,
              "[%d,%d]: %s %s" % (o, i, rec["tier"], rec["action"]),
              "[%d,%d]: expected %s (never REJECT), got tier=%s action=%s"
              % (o, i, pattern, rec["tier"], rec["action"]))

    print("--- Dihedral family anchors ---", flush=True)
    for (o, i), pattern, tier in ANCHORS_DIHEDRAL:
        rec = classify_group(o, i)
        ok = rec["tier"] == tier and pattern in str(rec["action"])
        check(ok,
              "[%d,%d]: %s %s" % (o, i, rec["tier"], rec["action"]),
              "[%d,%d]: expected %s %s, got tier=%s action=%s"
              % (o, i, tier, pattern, rec["tier"], rec["action"]))

    print("--- [32,49] ceiling consistency ---", flush=True)
    rec = classify_group(32, 49)
    sp = rec["ceilings"].get("subgroup_packing")
    check(sp is not None and abs(sp - 4.0) < 0.01,
          "[32,49]: subgroup_packing = %s = sqrt(16)" % sp,
          "[32,49]: expected subgroup_packing ~ 4, got %s" % sp)
    c2 = rec["ceilings"].get("class2_strict")
    check(c2 is not None and sp is not None and abs(c2 - sp) < 0.001,
          "[32,49]: class2_strict = subgroup_packing = %s" % c2,
          "[32,49]: class2_strict (%s) != subgroup_packing (%s)" % (c2, sp))

    print(flush=True)
    if failures:
        print("HARNESS FAILED: %d/%d assertions broken:" % (len(failures), n_assert), flush=True)
        for f in failures:
            print("  - %s" % f, flush=True)
        return False, n_assert, failures
    print("HARNESS PASSED: %d/%d assertions." % (n_assert, n_assert), flush=True)
    return True, n_assert, []


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
# Shard sweep: process one deterministic slice of work units
# ---------------------------------------------------------------------------

def process_chunk(order, idx_start, idx_end, done_ids, out_fh, tag):
    """Process nonabelian groups in SmallGroup(order, idx_start..idx_end).
    Returns (n_processed, n_errors, interrupted)."""
    n_processed = 0
    n_errors = 0
    interrupted = False

    for idx in range(int(idx_start), int(idx_end) + 1):
        gid = (int(order), idx)
        if gid in done_ids:
            continue
        try:
            G = libgap.SmallGroup(order, idx)
            if bool(G.IsAbelian()):
                continue
            rec = classify_group(order, idx)
            out_fh.write(forgelib.dump_jsonl(rec) + "\n")
            n_processed += 1
        except KeyboardInterrupt:
            interrupted = True
            break
        except Exception as e:
            err_rec = {
                "id": [int(order), idx],
                "order": int(order),
                "tier": "ERROR",
                "action": "SKIP",
                "error": str(e),
            }
            out_fh.write(forgelib.dump_jsonl(err_rec) + "\n")
            print("%sERROR [%d,%d]: %s" % (tag, order, idx, e),
                  file=sys.stderr, flush=True)
            n_errors += 1
            n_processed += 1

    return n_processed, n_errors, interrupted


def shard_sweep(shard_i, shard_n, start_order, end_order, out_dir, tag):
    """Run one shard's deterministic slice of the stratum-A sweep."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_file = out_dir / forgelib.shard_filename("cascade", shard_i, shard_n)

    # Build work units for all orders in range
    orders_and_counts = []
    for order in range(int(start_order), int(end_order) + 1):
        n_groups = int(libgap.NumberSmallGroups(order))
        orders_and_counts.append((order, n_groups))

    all_units = forgelib.make_work_units(orders_and_counts, CHUNK_SIZE)
    # Round-robin striping
    my_units = all_units[shard_i::shard_n]

    print("%sStratum A sweep: %d work units (of %d total)" %
          (tag, len(my_units), len(all_units)), flush=True)

    # Load done ids from ALL shard files + legacy checkpoints
    done_ids = forgelib.load_done_ids(str(out_dir), "cascade*.jsonl")
    legacy_done = forgelib.load_legacy_done_ids(str(LEGACY_CHECKPOINT_DIR))
    done_ids |= legacy_done
    print("%sResume: %d done ids (forge: %d, legacy: %d)" %
          (tag, len(done_ids), len(done_ids) - len(legacy_done), len(legacy_done)),
          flush=True)

    t_start = time.time()
    total_processed = 0
    total_errors = 0

    with open(out_file, "a") as out_fh:
        for ui, unit in enumerate(my_units):
            t_unit = time.time()
            n_proc, n_err, interrupted = process_chunk(
                unit["order"], unit["idx_start"], unit["idx_end"],
                done_ids, out_fh, tag)
            total_processed += n_proc
            total_errors += n_err
            out_fh.flush()

            elapsed_total = time.time() - t_start
            if (ui + 1) % 5 == 0 or interrupted:
                print(forgelib.progress_line(
                    unit["unit_id"], ui + 1, len(my_units), elapsed_total,
                    prefix=tag), flush=True)

            if interrupted:
                print("%sInterrupted at unit %s; shard checkpointed." %
                      (tag, unit["unit_id"]), flush=True)
                sys.exit(130)

    elapsed = time.time() - t_start
    print("%sShard sweep done: %d processed, %d errors, %.1fs" %
          (tag, total_processed, total_errors, elapsed), flush=True)


# ---------------------------------------------------------------------------
# Stratum B
# ---------------------------------------------------------------------------

def stratum_b_generate_sample(target):
    """Generate the fixed-seed sample of ``target`` ids from 1..POPULATION."""
    rng = random.Random(int(STRATUM_B_SEED))
    return rng.sample(range(1, STRATUM_B_POPULATION + 1), int(target))


def shard_stratum_b(shard_i, shard_n, target, pilot, full_mode, out_dir, tag):
    """Run one shard's slice of the stratum-B sweep."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    base_name = "stratum_b"
    out_file = out_dir / forgelib.shard_filename(base_name, shard_i, shard_n)

    if full_mode:
        # Full census: all 10,494,213 groups, chunked.
        all_units = forgelib.make_work_units(
            [(STRATUM_B_ORDER, STRATUM_B_POPULATION)], CHUNK_SIZE)
        my_units = all_units[shard_i::shard_n]
        print("%sStratum B FULL: %d work units (of %d total)" %
              (tag, len(my_units), len(all_units)), flush=True)
    else:
        # Sample mode: generate sample, stripe across shards.
        sample = stratum_b_generate_sample(target)
        effective = sample[:int(pilot)] if pilot else sample
        # Stripe sample ids across shards
        my_ids = effective[shard_i::shard_n]
        print("%sStratum B sample: %d ids in this shard (of %d effective)" %
              (tag, len(my_ids), len(effective)), flush=True)

    # Load done ids
    done_ids = forgelib.load_done_ids(str(out_dir), "stratum_b*.jsonl")
    # Also check legacy stratum-B checkpoint
    legacy_sb = LEGACY_CHECKPOINT_DIR / "stratum_b_512.jsonl"
    if legacy_sb.exists():
        legacy_sb_done = set()
        with open(legacy_sb) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    if rec.get("type"):
                        continue
                    gid = rec.get("id")
                    if gid:
                        legacy_sb_done.add(tuple(gid))
                except (json.JSONDecodeError, TypeError):
                    continue
        done_ids |= legacy_sb_done

    print("%sResume: %d done ids" % (tag, len(done_ids)), flush=True)

    t_start = time.time()
    total_processed = 0
    total_errors = 0

    with open(out_file, "a") as out_fh:
        if full_mode:
            # Chunk-based full sweep
            for ui, unit in enumerate(my_units):
                for idx in range(unit["idx_start"], unit["idx_end"] + 1):
                    gid = (STRATUM_B_ORDER, idx)
                    if gid in done_ids:
                        continue
                    try:
                        G = libgap.SmallGroup(STRATUM_B_ORDER, idx)
                        if bool(G.IsAbelian()):
                            continue
                        rec = classify_group(STRATUM_B_ORDER, idx)
                        out_fh.write(forgelib.dump_jsonl(rec) + "\n")
                        total_processed += 1
                    except KeyboardInterrupt:
                        out_fh.flush()
                        print("%sInterrupted; shard checkpointed." % tag, flush=True)
                        sys.exit(130)
                    except Exception as e:
                        err_rec = {
                            "id": [STRATUM_B_ORDER, idx],
                            "order": STRATUM_B_ORDER,
                            "tier": "ERROR",
                            "action": "SKIP",
                            "error": str(e),
                        }
                        out_fh.write(forgelib.dump_jsonl(err_rec) + "\n")
                        print("%sERROR [512,%d]: %s" % (tag, idx, e),
                              file=sys.stderr, flush=True)
                        total_errors += 1
                        total_processed += 1

                out_fh.flush()
                elapsed = time.time() - t_start
                if (ui + 1) % 10 == 0:
                    print(forgelib.progress_line(
                        unit["unit_id"], ui + 1, len(my_units), elapsed,
                        prefix=tag), flush=True)
        else:
            # Sample-based sweep
            for i, sid in enumerate(my_ids):
                gid = (STRATUM_B_ORDER, int(sid))
                if gid in done_ids:
                    continue
                try:
                    G = libgap.SmallGroup(STRATUM_B_ORDER, sid)
                    if bool(G.IsAbelian()):
                        rec = {
                            "id": [STRATUM_B_ORDER, int(sid)],
                            "order": STRATUM_B_ORDER,
                            "tier": "T0",
                            "action": "REJECT",
                        }
                    else:
                        rec = classify_group(STRATUM_B_ORDER, sid)
                    out_fh.write(forgelib.dump_jsonl(rec) + "\n")
                    total_processed += 1
                except KeyboardInterrupt:
                    out_fh.flush()
                    print("%sInterrupted; shard checkpointed." % tag, flush=True)
                    sys.exit(130)
                except Exception as e:
                    err_rec = {
                        "id": [STRATUM_B_ORDER, int(sid)],
                        "order": STRATUM_B_ORDER,
                        "tier": "ERROR",
                        "action": "SKIP",
                        "error": str(e),
                    }
                    out_fh.write(forgelib.dump_jsonl(err_rec) + "\n")
                    print("%sERROR [512,%d]: %s" % (tag, sid, e),
                          file=sys.stderr, flush=True)
                    total_errors += 1
                    total_processed += 1

                if (i + 1) % 100 == 0:
                    out_fh.flush()
                    elapsed = time.time() - t_start
                    print(forgelib.progress_line(
                        "sample", i + 1, len(my_ids), elapsed,
                        prefix=tag), flush=True)

    elapsed = time.time() - t_start
    print("%sStratum B shard done: %d processed, %d errors, %.1fs" %
          (tag, total_processed, total_errors, elapsed), flush=True)

    if pilot and total_processed > 0:
        rate = total_processed / elapsed if elapsed > 0 else 0
        full_remaining = int(target) - total_processed
        if rate > 0:
            proj_s = full_remaining / rate
            print("  PILOT PROJECTION: full sample (%d remaining) at %.1f/s: "
                  "~%.0fs (~%.1f hours)" % (full_remaining, rate, proj_s, proj_s / 3600),
                  flush=True)


# ---------------------------------------------------------------------------
# Toy mode
# ---------------------------------------------------------------------------

def run_toy_mode(out_dir):
    """Harness + orders 2..24 + 20-id stratum-B sample, 2 workers.
    Exercises: sharding, checkpoint, resume, summary."""
    print("=== TOY MODE ===", flush=True)
    print("Orders 2..24, 2 workers, 20-id stratum-B sample.", flush=True)
    print(flush=True)

    passed, n_assert, _ = run_anchor_harness()
    if not passed:
        print("STOPPING: fix the cascade before sweeping.", flush=True)
        sys.exit(1)

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    tag = "[toy] "

    # Stratum A: orders 2..24, single-process (fast enough)
    shard_sweep(0, 1, 2, 24, str(out_dir), tag)

    # Stratum B: 20-id sample, single-process
    print(flush=True)
    print("%sToy stratum-B: 20-id sample" % tag, flush=True)
    shard_stratum_b(0, 1, 20, 0, False, str(out_dir), tag)

    # Print quick summary
    print(flush=True)
    done_a = forgelib.load_done_ids(str(out_dir), "cascade*.jsonl")
    done_b = forgelib.load_done_ids(str(out_dir), "stratum_b*.jsonl")
    print("%sToy complete: %d stratum-A records, %d stratum-B records." %
          (tag, len(done_a), len(done_b)), flush=True)


# ---------------------------------------------------------------------------
# Summary generator
# ---------------------------------------------------------------------------

def load_all_records(start_order, end_order, out_dir):
    """Load all cascade records from forge shards + legacy checkpoints."""
    all_records = []

    # Forge shard records
    out_path = Path(out_dir)
    for path in sorted(out_path.glob("cascade*.jsonl")):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    if rec.get("type"):
                        continue
                    all_records.append(rec)
                except (json.JSONDecodeError, TypeError):
                    continue

    # Legacy checkpoint records
    seen_ids = set(tuple(r["id"]) for r in all_records if "id" in r)
    for order in range(int(start_order), int(end_order) + 1):
        path = LEGACY_CHECKPOINT_DIR / ("order_%d.jsonl" % order)
        if not path.exists():
            continue
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    if rec.get("type"):
                        continue
                    gid = rec.get("id")
                    if gid and tuple(gid) not in seen_ids:
                        all_records.append(rec)
                        seen_ids.add(tuple(gid))
                except (json.JSONDecodeError, TypeError):
                    continue

    return all_records


def generate_summary(start_order, end_order, out_dir):
    """Generate sieve-summary.md from all available data sources."""
    all_records = load_all_records(start_order, end_order, out_dir)

    total_groups = 0
    abelian_total = 0
    for order in range(int(start_order), int(end_order) + 1):
        n = int(libgap.NumberSmallGroups(order))
        total_groups += n
        abelian_total += count_abelian(order)

    n_orders = int(end_order) - int(start_order) + 1
    expected_nonabelian = total_groups - abelian_total

    tier_counts = {}
    action_counts = {"REJECT": 0, "CAP": 0, "SURVIVE": 0, "ERROR": 0}
    for rec in all_records:
        tier = rec.get("tier", "UNKNOWN")
        tier_counts[tier] = tier_counts.get(tier, 0) + 1
        action = str(rec.get("action", ""))
        if action == "REJECT":
            action_counts["REJECT"] += 1
        elif action == "SURVIVE":
            action_counts["SURVIVE"] += 1
        elif "CAP" in action:
            action_counts["CAP"] += 1
        else:
            action_counts["ERROR"] += 1

    survivors = [r for r in all_records if r.get("action") == "SURVIVE"]
    capped = [r for r in all_records if "CAP" in str(r.get("action", ""))]

    # Determine coverage gaps
    all_ids = set(tuple(r["id"]) for r in all_records if "id" in r)
    incomplete_orders = []
    for order in range(int(start_order), int(end_order) + 1):
        n = int(libgap.NumberSmallGroups(order))
        n_abelian = count_abelian(order)
        n_nonabelian = n - n_abelian
        n_have = sum(1 for gid in all_ids if gid[0] == order)
        if n_have < n_nonabelian:
            incomplete_orders.append((order, n_have, n_nonabelian))

    with open(SUMMARY_FILE, "w") as f:
        f.write("# TPP Group Sieve Summary\n\n")
        f.write("Generated by `Scratch/GroupSieve/forge/cascade.sage` on %s.\n\n"
                % time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime()))
        f.write("## Coverage — stratum A, orders %d..%d\n\n" % (start_order, end_order))
        f.write("- Orders: %d\n" % n_orders)
        f.write("- Total groups in range: %d (abelian: %d, nonabelian: %d)\n"
                % (total_groups, abelian_total, expected_nonabelian))
        f.write("- Nonabelian records held: %d of %d expected (%.1f%%)\n"
                % (len(all_records), expected_nonabelian,
                   100.0 * len(all_records) / expected_nonabelian if expected_nonabelian else 0.0))
        if incomplete_orders:
            f.write("\n**Incomplete orders** (aggregate claims over the range are\n")
            f.write("unsound until these close):\n\n")
            for order, have, need in incomplete_orders:
                f.write("- order %d: %d of %d nonabelian\n" % (order, have, need))
        else:
            f.write("\nAll orders in range are complete.\n")

        f.write("\n### Per-tier counts (nonabelian, processed population only)\n\n")
        f.write("| Tier | Count | Description |\n")
        f.write("|------|-------|-------------|\n")
        f.write("| T0 | %d | Abelian, counted analytically (rho_0 = 1) "
                "[Murthy26 Thm 2.3 / CU03 Lem 3.1] |\n" % abelian_total)
        descs = {
            "T1a": "p-group |G| <= p^4 [Murthy26 Prop 2.14]",
            "T1b": "Class-2 p-group, cd={1,p} [Murthy26 Thm 6.1]",
            "T3a": "p-group, abelian subgroup index p [Murthy25 Cor 4.3(2)]",
            "T3b": "Abelian normal subgroup prime index [Murthy25 Thm 4.1]",
            "T3c": "Product decomp A x H, conjecture-gated [Pf3 + sweep]",
            "T1c": "p-group, cyclic G' order p, CAP(p) [Murthy26 Thm 4.1]",
            "T2b": "Survivors with packing ceilings [BCGPU Thm 3.2, Cor 3.8]",
            "ERROR": "Per-group classification errors",
        }
        for tier in ["T1a", "T1b", "T3a", "T3b", "T3c", "T1c", "T2b", "ERROR"]:
            f.write("| %s | %d | %s |\n" % (tier, tier_counts.get(tier, 0), descs[tier]))
        f.write("\nT2a is absent by design: provably shadowed by T1b "
                "(Isaacs Cor 2.30); it fired 0 times in all prior data.\n")

        f.write("\n### Action summary\n\n")
        f.write("| Action | Count |\n|--------|-------|\n")
        for k in ["REJECT", "CAP", "SURVIVE", "ERROR"]:
            f.write("| %s | %d |\n" % (k, action_counts[k]))

        f.write("\n### Survivors: %d\n\n" % len(survivors))
        if survivors:
            survivors_sorted = sorted(survivors,
                                      key=lambda r: float(r.get("ceiling") or 0.0),
                                      reverse=True)
            f.write("Top 20 by ceiling, descending (high ceiling = least "
                    "constrained, not \"promising\"):\n\n")
            f.write("| Group | Order | n(G) | |G:Z| | Ceiling | Nil class |\n")
            f.write("|-------|-------|------|-------|---------|-----------|\n")
            for r in survivors_sorted[:20]:
                gid = r["id"]
                f.write("| [%d,%d] | %d | %s | %s | %.4g | %s |\n"
                        % (gid[0], gid[1], r.get("order", 0), r.get("n_G", "?"),
                           r.get("gz_index", "?"), float(r.get("ceiling") or 0.0),
                           r.get("nil_class", "?")))

        f.write("\n### Capped groups: %d\n\n" % len(capped))

        f.write("### Known cascade gaps\n\n")
        f.write("1. [24,10] (C3xD8) and [24,11] (C3xQ8) have known rho_0 = 1 but\n")
        f.write("   the cascade can only certify CAP(4/3) via T3b: p = 2 and\n")
        f.write("   (2p-1) = 3 divides 24, so Murthy25 Cor 4.3(1) is inapplicable.\n")
        f.write("   A product-decomposition tier would close this.\n")
        f.write("2. Ceilings are upper bounds (necessary-condition screens): a\n")
        f.write("   high ceiling means \"not yet excluded\", never \"promising\".\n")

        f.write("\n### Downstream artifacts\n\n")
        f.write("- Tier-4 ranking and anchor validation: "
                "`.tasks/f5exp/docs/Im3-ranking.md` "
                "(program: `cmd/tier4rank/`, features: `forge/features.sage`)\n")
        f.write("- Survivor census (direct factors, ES types, T3b rationals): "
                "`survivors-census*.jsonl` via `census.sage`; early analysis "
                "in `.tasks/f5exp/docs/orch-Cj-census-early.md`\n")

    return SUMMARY_FILE


# ---------------------------------------------------------------------------
# Dry-run
# ---------------------------------------------------------------------------

def dry_run(args):
    """Print space sizes and runtime projections."""
    n_workers = max(args.workers, 1)

    print("=== DRY RUN ===", flush=True)

    if args.stratum_b:
        if args.full:
            space = STRATUM_B_POPULATION
            label = "Stratum B FULL (order 512, all %d groups)" % space
        else:
            space = int(args.pilot) if args.pilot else int(args.target)
            label = "Stratum B sample (%d ids)" % space
        print(forgelib.dry_run_table(
            space, STRATUM_B_RATE,
            [1, 4, 16, 64, 128, 224, n_workers] if n_workers not in [1, 4, 16, 64, 128, 224] else [1, 4, 16, 64, 128, 224],
            label), flush=True)
        print(flush=True)
        print("  Memory: ~1-2 GiB per GAP worker. Cap workers at "
              "min(nproc, floor(RAM_GiB / 2)).", flush=True)
    else:
        # Count nonabelian groups for the order range
        total_nonabelian = 0
        for order in range(args.start, args.end + 1):
            n = int(libgap.NumberSmallGroups(order))
            total_nonabelian += n - count_abelian(order)

        # Load done ids to show remaining
        done_ids = forgelib.load_done_ids(str(FORGE_OUT_DIR), "cascade*.jsonl")
        legacy_done = forgelib.load_legacy_done_ids(str(LEGACY_CHECKPOINT_DIR))
        all_done = done_ids | legacy_done
        remaining = total_nonabelian - len(all_done)

        print("  Stratum A: orders %d..%d" % (args.start, args.end), flush=True)
        print("  Total nonabelian: %d" % total_nonabelian, flush=True)
        print("  Already done: %d (forge: %d, legacy: %d)" %
              (len(all_done), len(done_ids), len(legacy_done)), flush=True)
        print("  Remaining: %d" % max(remaining, 0), flush=True)
        print(flush=True)

        effective_space = max(remaining, 0) if remaining > 0 else total_nonabelian
        print(forgelib.dry_run_table(
            effective_space, STRATUM_A_RATE,
            [1, 4, 16, 64, 128, 224, n_workers] if n_workers not in [1, 4, 16, 64, 128, 224] else [1, 4, 16, 64, 128, 224],
            "Stratum A (remaining)"), flush=True)

    print(flush=True)
    print("  Default workers: min(nproc, 224). Each GAP worker uses ~1-2 GiB.",
          flush=True)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv):
    parser = argparse.ArgumentParser(
        description="TPP group sieve — forge-grade cascade")
    parser.add_argument("--harness-only", action="store_true",
                        help="run the falsifiability harness and exit")
    parser.add_argument("--summary-only", action="store_true",
                        help="regenerate the summary from all data sources; no compute")
    parser.add_argument("--toy", action="store_true",
                        help="toy mode: harness + orders 2..24 + 20-id stratum-B sample")
    parser.add_argument("--dry-run", action="store_true",
                        help="print space sizes and runtime projections; no compute")
    parser.add_argument("--start", type=int, default=STRATUM_A_START)
    parser.add_argument("--end", type=int, default=STRATUM_A_END)
    parser.add_argument("--workers", type=int, default=1,
                        help="spawn N single-core worker subprocesses (default 1)")
    parser.add_argument("--shard", default=None, metavar="I/N",
                        help="run the I-th of N deterministic slices (0-indexed)")
    parser.add_argument("--out-dir", default=str(FORGE_OUT_DIR),
                        help="output directory for shard files")
    # Stratum-B flags
    parser.add_argument("--stratum-b", action="store_true",
                        help="run the stratum-B sweep (order 512)")
    parser.add_argument("--target", type=int, default=STRATUM_B_DEFAULT_TARGET,
                        help="stratum-B sample size (default %d)" % STRATUM_B_DEFAULT_TARGET)
    parser.add_argument("--pilot", type=int, default=0,
                        help="stratum-B pilot batch size (for projection); 0 = full")
    parser.add_argument("--full", action="store_true",
                        help="stratum-B complete census (all %d groups)" % STRATUM_B_POPULATION)
    args = parser.parse_args(argv)

    # --- Dry run ---
    if args.dry_run:
        dry_run(args)
        return

    # --- Summary only ---
    if args.summary_only:
        path = generate_summary(args.start, args.end, args.out_dir)
        print("Summary: %s" % path, flush=True)
        return

    # --- Harness only ---
    if args.harness_only:
        passed, n_assert, _ = run_anchor_harness()
        if not passed:
            sys.exit(1)
        return

    # --- Toy mode ---
    if args.toy:
        run_toy_mode(args.out_dir)
        return

    # --- Worker-pool dispatch ---
    if args.workers > 1 and args.shard is None:
        extra = []
        extra.extend(["--out-dir", args.out_dir])
        if args.stratum_b:
            extra.append("--stratum-b")
            extra.extend(["--target", str(args.target)])
            if args.pilot:
                extra.extend(["--pilot", str(args.pilot)])
            if args.full:
                extra.append("--full")
        else:
            extra.extend(["--start", str(args.start)])
            extra.extend(["--end", str(args.end)])

        # Cap workers at min(requested, 224) — memory headroom
        n_workers = min(args.workers, 224)
        pool = forgelib.WorkerPool(
            script=str(Path(__file__).resolve()),
            n_workers=n_workers,
            extra_args=extra,
        )
        print("Launching %d workers..." % n_workers, flush=True)
        rc = pool.run()
        if rc != 0 and rc != 130:
            print("Workers exited with code %d" % rc, flush=True)
        # Generate summary after workers finish
        path = generate_summary(args.start, args.end, args.out_dir)
        print("Summary: %s" % path, flush=True)
        sys.exit(rc)

    # --- Single-shard execution ---
    shard_i, shard_n = 0, 1
    if args.shard:
        shard_i, shard_n = (int(x) for x in args.shard.split("/"))
        if not (0 <= shard_i < shard_n):
            parser.error("--shard %s: need 0 <= I < N" % args.shard)
    tag = "[shard %d/%d] " % (shard_i, shard_n) if shard_n > 1 else ""

    # Pre-sweep harness gate (only shard 0 runs it to avoid N x harness)
    if shard_i == 0:
        passed, n_assert, _ = run_anchor_harness()
        if not passed:
            print("STOPPING: fix the cascade before sweeping.", flush=True)
            sys.exit(1)

    if args.stratum_b:
        shard_stratum_b(shard_i, shard_n, args.target, args.pilot,
                        args.full, args.out_dir, tag)
    else:
        shard_sweep(shard_i, shard_n, args.start, args.end,
                    args.out_dir, tag)

    # Shard 0 generates the summary
    if shard_i == 0 and shard_n == 1:
        path = generate_summary(args.start, args.end, args.out_dir)
        print("Summary: %s" % path, flush=True)


# The sage CLI executes .sage files inside sage_globals(), not
# under __name__ == "__main__" — an if-guard would silently skip.
# Strip the "--" separator that `sage script.sage -- --flags` requires.
main([a for a in sys.argv[1:] if a != "--"])
