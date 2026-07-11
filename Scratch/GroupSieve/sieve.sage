"""
TPP Group Sieve — stratum A (nonabelian groups of order 2..511).

Implements the tier cascade from .tasks/f5exp/docs/sieve-spec.md with
corrected theorem citations verified against arXiv LaTeX sources.

Usage:
    sage sieve.sage [--harness-only] [--workers N] [--start ORDER] [--end ORDER]
"""

import json
import os
import sys
import time
import signal
from multiprocessing import Pool, cpu_count
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DOCS_DIR = REPO_ROOT / ".tasks" / "f5exp" / "docs"
SCRATCH_DIR = REPO_ROOT / "Scratch" / "GroupSieve"
CHECKPOINT_DIR = SCRATCH_DIR / "checkpoints"
RESULTS_FILE = DOCS_DIR / "sieve-results-A.jsonl"

CHECKPOINT_DIR.mkdir(parents=True, exist_ok=True)

# ---------------------------------------------------------------------------
# Per-group / per-order timeout (seconds)
# ---------------------------------------------------------------------------

GROUP_TIMEOUT = 30   # seconds per group
ORDER_TIMEOUT = 600  # seconds per order (10 min)

# ---------------------------------------------------------------------------
# Tier predicates
# ---------------------------------------------------------------------------

def compute_character_degrees(G):
    """Return the set of character degrees of G (as Python integers)."""
    ct = G.CharacterTable()
    irr = ct.Irr()
    degrees = set()
    for chi in irr:
        d = ZZ(chi[1])  # chi(1) = degree
        degrees.add(int(d))
    return degrees


def smallest_nonlinear_irrep_dim(cd_set):
    """
    n(G) = smallest irrep dimension > 1.
    [BCGPU Definition 3.1: min{dim pi : pi in Irr(G), dim pi > 1}]
    """
    dims_gt1 = [d for d in cd_set if d > 1]
    if not dims_gt1:
        return None
    return min(dims_gt1)


def is_p_group(G):
    """Check if G is a p-group; if so return p, else None."""
    order = int(G.Order())
    if order == 1:
        return None
    f = factor(order)
    if len(f) == 1:
        return int(f[0][0])
    return None


def nilpotency_class(G):
    """Return nilpotency class or None if not nilpotent."""
    if G.IsNilpotentGroup():
        return int(G.NilpotencyClassOfGroup())
    return None


def center_order(G):
    """Return |Z(G)|."""
    return int(G.Centre().Size())


def derived_subgroup_info(G):
    """Return (|G'|, is_cyclic_Gp)."""
    Gp = G.DerivedSubgroup()
    size = int(Gp.Size())
    is_cyc = bool(Gp.IsCyclic())
    return size, is_cyc


def has_abelian_subgroup_index_p(G, p):
    """
    Check if p-group G has an abelian subgroup of index p.
    For p-groups, use MaximalSubgroupClassReps (index p subgroups).
    [Used by T3a: Murthy25 Cor 4.3(2)]
    """
    maxsubs = G.MaximalSubgroupClassReps()
    for H in maxsubs:
        if H.IsAbelian():
            return True
    return False


def has_abelian_normal_subgroup_prime_index(G, order_G):
    """
    For general (non-p) groups, check if G has an abelian normal
    subgroup of prime index. Returns (True, p) or (False, None).

    Note: subgroups of smallest-prime index are automatically normal
    [Murthy25 end of Sec 5], so we only need to check normality for
    non-smallest prime indices.

    [Used by T3b: Murthy25 Thm 4.1]
    """
    # Find prime divisors of |G|
    primes = [int(f[0]) for f in factor(order_G)]
    smallest_prime = min(primes)

    # Check maximal normal subgroups
    normal_subs = G.MaximalNormalSubgroups()
    for H in normal_subs:
        idx = order_G // int(H.Size())
        if is_prime(idx) and H.IsAbelian():
            return True, int(idx)

    return False, None


# ---------------------------------------------------------------------------
# Tier cascade
# ---------------------------------------------------------------------------

def classify_group(order, idx):
    """
    Classify a single nonabelian group SmallGroup(order, idx).
    Returns a dict with the per-group record fields.
    """
    G = libgap.SmallGroup(order, idx)

    # Basic invariants
    order_G = int(order)
    z_order = center_order(G)
    gz_index = order_G // z_order  # |G:Z(G)|

    Gp_size, Gp_cyclic = derived_subgroup_info(G)
    nil_class = nilpotency_class(G)

    p = is_p_group(G)

    rec = {
        "id": [order_G, idx],
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

    # --- T0: abelian check (should not reach here, but safety) ---
    # [Murthy26 Thm 2.3 / CU03 Lemma 3.1: abelian => rho_0 = 1]
    if G.IsAbelian():
        rec["tier"] = "T0"
        rec["action"] = "REJECT"
        return rec

    # --- T1a: p-group of order <= p^4 ---
    # [Murthy26 Prop 2.14: p-group |G| <= p^4 => rho_0 = 1]
    if p is not None:
        if order_G <= p**4:
            rec["tier"] = "T1a"
            rec["action"] = "REJECT"
            return rec

    # --- T1b: p-group, class 2, cd(G) = {1, p} ---
    # [Murthy26 Thm 6.1: class-2 p-group with cd(G) = {1,p} => rho_0 = 1.
    #  SCOPE: hypothesis is class-2 p-group, not arbitrary G.]
    if p is not None and nil_class == 2:
        cd = compute_character_degrees(G)
        rec["cd"] = sorted(cd)
        if cd == {1, p}:
            rec["tier"] = "T1b"
            rec["action"] = "REJECT"
            return rec
    else:
        cd = None

    # --- T2a: p-group, class 2, p^2 <= |G:Z| <= p^3 ---
    # [Murthy26 Thm 5.1: class-2 p-group, p^2 <= |G:Z(G)| <= p^3 => rho_0 = 1]
    if p is not None and nil_class == 2:
        if p**2 <= gz_index <= p**3:
            rec["tier"] = "T2a"
            rec["action"] = "REJECT"
            return rec

    # --- T3a: p-group with abelian subgroup of index p ---
    # [Murthy25 Cor 4.3(2): p-group + abelian subgroup index p => rho_0 = 1.
    #  Normality automatic in p-groups for prime-index subgroups.]
    if p is not None:
        if has_abelian_subgroup_index_p(G, p):
            rec["tier"] = "T3a"
            rec["action"] = "REJECT"
            return rec

    # --- T3b: general G (non-p-group) with abelian normal subgroup of prime index ---
    # [Murthy25 Thm 4.1: abelian normal subgroup of prime index p => rho_0 <= p^2/(2p-1).
    #  Murthy25 Cor 4.3(1): if additionally (2p-1) nmid |G| => rho_0 <= p/2.
    #  Note: p=2 with 3 nmid |G| gives CAP(1) = REJECT.]
    if p is None:
        has_ans, ans_p = has_abelian_normal_subgroup_prime_index(G, order_G)
        if has_ans:
            cap_val = QQ(ans_p**2) / QQ(2*ans_p - 1)
            tighter = False
            if (2*ans_p - 1) % order_G != 0:
                # Check (2p-1) does not divide |G|
                if order_G % (2*ans_p - 1) != 0:
                    cap_val_tight = QQ(ans_p) / QQ(2)
                    tighter = True

            if tighter and cap_val_tight <= 1:
                rec["tier"] = "T3b"
                rec["action"] = "REJECT"
                rec["flags"].append(f"p={ans_p}, (2p-1)={2*ans_p-1} nmid |G|={order_G}, cap=p/2={float(cap_val_tight)}")
                return rec
            elif cap_val <= 1:
                rec["tier"] = "T3b"
                rec["action"] = "REJECT"
                rec["flags"].append(f"p={ans_p}, cap=p^2/(2p-1)={float(cap_val)} <= 1")
                return rec
            else:
                final_cap = float(cap_val_tight) if tighter else float(cap_val)
                rec["tier"] = "T3b"
                rec["action"] = f"CAP({final_cap:.6g})"
                rec["ceilings"]["T3b"] = final_cap
                rec["flags"].append(f"p={ans_p}")
                # Don't return — continue to collect T2b ceilings

    # --- T1c: nonabelian p-group with cyclic G' of order p ---
    # [Murthy26 Thm 4.1: nonabelian p-group, G' cyclic of order p => rho_0 <= p.
    #  ACTION CORRECTION: CAP(p), never reject — extraspecial groups achieve rho_0 = p > 1.]
    if p is not None and Gp_cyclic and Gp_size == p:
        rec["tier"] = "T1c"
        rec["action"] = f"CAP({p})"
        rec["ceilings"]["T1c"] = float(p)
        # Continue to collect T2b ceilings

    # --- T2b: packing ceilings for all survivors/capped groups ---
    # [BCGPU Thm 3.2 (arXiv numbering): |S||T||U| <= |G|^{3/2}/n(G)^{1/2} + |G|
    #  => rho_0 <= |G|^{1/2}/n(G)^{1/2} + 1
    #  BCGPU Cor 3.8 (arXiv numbering): |H1||H2||H3| <= |G|^{3/2}/|Z(G)|^{1/2}
    #  => rho_0 <= sqrt(|G:Z(G)|) for subgroup triples.
    #  Family-level barrier (BCGPU Cor 3.3) MUST NOT hard-reject individual groups.]
    if cd is None:
        cd = compute_character_degrees(G)
        rec["cd"] = sorted(cd)

    n_G = smallest_nonlinear_irrep_dim(cd)
    rec["n_G"] = n_G

    # Subset packing ceiling: rho_0 <= sqrt(|G|/n(G)) + 1
    if n_G is not None and n_G > 0:
        subset_ceil = float(RR(sqrt(order_G / n_G)) + 1)
        rec["ceilings"]["subset_packing"] = subset_ceil

    # Subgroup packing ceiling: rho_0 <= sqrt(|G:Z(G)|)
    subgroup_ceil = float(RR(sqrt(gz_index)))
    rec["ceilings"]["subgroup_packing"] = subgroup_ceil

    # Class-2 strict ceiling from Murthy26 Thm 3.1
    if nil_class == 2:
        rec["ceilings"]["class2_strict"] = subgroup_ceil
        rec["flags"].append("class2_strict_ineq")

    # Final tier/action if not already set by T1c or T3b
    if rec["tier"] is None:
        rec["tier"] = "T2b"
        rec["action"] = "SURVIVE"

    # Compute overall ceiling as min of applicable bounds
    if rec["ceilings"]:
        rec["ceiling"] = min(rec["ceilings"].values())
    else:
        rec["ceiling"] = None

    return rec


# ---------------------------------------------------------------------------
# Anchor harness
# ---------------------------------------------------------------------------

ANCHORS_REJECT = [
    # [order, idx], expected_tier (or list of acceptable tiers)
    ([8, 3], ["T1a", "T3a"]),    # D8: p=2, |G|=8<=2^4 => T1a
    ([8, 4], ["T1a", "T3a"]),    # Q8: p=2, |G|=8<=2^4 => T1a
    ([16, 3], ["T1a", "T3a"]),   # p=2, |G|=16<=2^4 => T1a
    ([16, 4], ["T1a", "T3a"]),   # p=2, |G|=16<=2^4 => T1a (NOTE: this is nonabelian per Tables)
    ([16, 6], ["T1a", "T3a"]),   # p=2, |G|=16<=2^4 => T1a
    ([16, 11], ["T1a", "T3a"]),  # p=2, |G|=16<=2^4 => T1a
    ([16, 12], ["T1a", "T3a"]),  # p=2, |G|=16<=2^4 => T1a
    ([16, 13], ["T1a", "T3a"]),  # p=2, |G|=16<=2^4 => T1a
    ([27, 3], ["T1a", "T1b", "T2a", "T3a"]),  # p=3, |G|=27<=3^4 => T1a
    ([27, 4], ["T1a", "T1b", "T2a", "T3a"]),  # p=3, |G|=27<=3^4 => T1a
    ([24, 10], ["T3b"]),         # C3xD8: non-p-group, has abelian normal index-2
    ([24, 11], ["T3b"]),         # C3xQ8: non-p-group, has abelian normal index-2
]

ANCHORS_MUST_NOT_REJECT = [
    # [order, idx], expected action pattern
    ([32, 49], "CAP"),    # extraspecial, rho_0=2, T1c CAP(2)
    ([64, 226], "SURVIVE"),  # cd={1,2,4}, rho_0=2, survives (or CAP)
    ([128, 1135], "SURVIVE"),  # rho_0=2
    ([128, 2194], "SURVIVE"),  # rho_0=2
]

# D_{2n} family anchors
ANCHORS_DIHEDRAL = [
    # D12 = [12,4]: 3|6 so 3|n (n=6 in D_{2n}=D12), must NOT reject, T3b CAP(4/3)
    ([12, 4], "CAP"),
    # D10 = [10,1]: 3 nmid 5 (n=5 in D_{2n}=D10), T3b p=2 with 3 nmid |G|=10, REJECT
    ([10, 1], "REJECT"),
]


def run_anchor_harness():
    """
    Run the falsifiability harness. Returns (passed: bool, details: list[str]).
    """
    failures = []

    print("=== Falsifiability Harness ===")
    print()

    # Test REJECT anchors
    print("--- REJECT anchors (must be rejected) ---")
    for gid, acceptable_tiers in ANCHORS_REJECT:
        order, idx = gid
        # First check if the group is actually nonabelian
        G = libgap.SmallGroup(order, idx)
        if G.IsAbelian():
            # Abelian groups are rejected at T0 — that's fine
            print(f"  [{order},{idx}]: T0 REJECT (abelian) -- OK")
            continue
        rec = classify_group(order, idx)
        if rec["action"] != "REJECT":
            msg = f"[{order},{idx}]: expected REJECT, got tier={rec['tier']} action={rec['action']}"
            failures.append(msg)
            print(f"  FAIL: {msg}")
        else:
            print(f"  [{order},{idx}]: {rec['tier']} REJECT -- OK")

    print()
    print("--- MUST-NOT-REJECT anchors (known rho_0 > 1) ---")
    for gid, expected_pattern in ANCHORS_MUST_NOT_REJECT:
        order, idx = gid
        rec = classify_group(order, idx)
        if rec["action"] == "REJECT":
            msg = f"[{order},{idx}]: WRONGLY REJECTED at tier={rec['tier']}"
            failures.append(msg)
            print(f"  FAIL: {msg}")
        else:
            print(f"  [{order},{idx}]: tier={rec['tier']} action={rec['action']} -- OK")

    print()
    print("--- Dihedral family anchors ---")
    for gid, expected_pattern in ANCHORS_DIHEDRAL:
        order, idx = gid
        G = libgap.SmallGroup(order, idx)
        if G.IsAbelian():
            if expected_pattern == "REJECT":
                print(f"  [{order},{idx}]: T0 REJECT (abelian) -- OK")
                continue
            else:
                msg = f"[{order},{idx}]: expected {expected_pattern} but group is abelian (T0 REJECT)"
                failures.append(msg)
                print(f"  FAIL: {msg}")
                continue
        rec = classify_group(order, idx)
        if expected_pattern == "REJECT":
            if rec["action"] != "REJECT":
                msg = f"[{order},{idx}]: expected REJECT, got tier={rec['tier']} action={rec['action']}"
                failures.append(msg)
                print(f"  FAIL: {msg}")
            else:
                print(f"  [{order},{idx}]: {rec['tier']} REJECT -- OK")
        elif expected_pattern == "CAP":
            if rec["action"] == "REJECT":
                msg = f"[{order},{idx}]: WRONGLY REJECTED at tier={rec['tier']}"
                failures.append(msg)
                print(f"  FAIL: {msg}")
            elif "CAP" not in str(rec["action"]):
                msg = f"[{order},{idx}]: expected CAP, got tier={rec['tier']} action={rec['action']}"
                failures.append(msg)
                print(f"  FAIL: {msg}")
            else:
                print(f"  [{order},{idx}]: tier={rec['tier']} action={rec['action']} -- OK")

    print()
    # Validation: [32,49] ceiling check
    print("--- Validation: [32,49] ceiling consistency ---")
    rec = classify_group(32, 49)
    ceil_val = rec.get("ceilings", {}).get("subgroup_packing")
    if ceil_val is not None and abs(ceil_val - 4.0) < 0.01:
        print(f"  [32,49]: subgroup_packing ceiling = {ceil_val} = sqrt(16) = 4 -- OK")
    else:
        msg = f"[32,49]: expected subgroup_packing ceiling ~ 4, got {ceil_val}"
        failures.append(msg)
        print(f"  FAIL: {msg}")

    # Check class-2 strict vs BCGPU agreement
    if "class2_strict" in rec.get("ceilings", {}):
        c2 = rec["ceilings"]["class2_strict"]
        sp = rec["ceilings"]["subgroup_packing"]
        if abs(c2 - sp) < 0.001:
            print(f"  [32,49]: class2_strict = subgroup_packing = {c2} (both = sqrt(|G:Z|)) -- OK")
        else:
            msg = f"[32,49]: class2_strict ({c2}) != subgroup_packing ({sp})"
            failures.append(msg)
            print(f"  FAIL: {msg}")

    print()
    if failures:
        print(f"HARNESS FAILED: {len(failures)} assertion(s) broken:")
        for f in failures:
            print(f"  - {f}")
        return False, failures
    else:
        print("HARNESS PASSED: all anchors correctly classified.")
        return True, []


# ---------------------------------------------------------------------------
# Stratum A sweep
# ---------------------------------------------------------------------------

def process_order(order):
    """
    Process all nonabelian groups of a given order.
    Returns list of classification records.
    """
    results = []

    try:
        n_groups = int(libgap.NumberSmallGroups(order))
    except Exception as e:
        return [{"order": order, "error": str(e), "type": "NumberSmallGroups_failed"}]

    for idx in range(1, n_groups + 1):
        try:
            G = libgap.SmallGroup(order, idx)
            if G.IsAbelian():
                continue  # Skip abelian, counted separately
            rec = classify_group(order, idx)
            results.append(rec)
        except Exception as e:
            results.append({
                "id": [order, idx],
                "order": order,
                "tier": "ERROR",
                "action": "SKIP",
                "error": str(e),
            })

    return results


def sweep_stratum_a(start_order=2, end_order=511, max_workers=4):
    """
    Sweep all nonabelian groups in orders start_order..end_order.
    Checkpoints per-order, resumes from last checkpoint.
    """
    all_results = []
    t0 = time.time()

    # Determine which orders are already checkpointed
    done_orders = set()
    for cp_file in CHECKPOINT_DIR.glob("order_*.jsonl"):
        try:
            o = int(cp_file.stem.split("_")[1])
            done_orders.add(o)
        except (ValueError, IndexError):
            pass

    # Load existing checkpointed results
    for o in sorted(done_orders):
        cp_file = CHECKPOINT_DIR / f"order_{o}.jsonl"
        with open(cp_file) as f:
            for line in f:
                line = line.strip()
                if line:
                    all_results.append(json.loads(line))

    orders_to_process = [o for o in range(start_order, end_order + 1) if o not in done_orders]
    total_orders = len(orders_to_process)

    print(f"Stratum A sweep: orders {start_order}..{end_order}")
    print(f"  Already checkpointed: {len(done_orders)} orders")
    print(f"  Remaining: {total_orders} orders")
    print(f"  Workers: {max_workers}")
    print()

    # Process sequentially (libgap not fork-safe in general with Sage)
    # Use alarm-based timeouts per order
    for i, order in enumerate(orders_to_process):
        t_order = time.time()

        try:
            signal.alarm(ORDER_TIMEOUT)
            results = process_order(order)
            signal.alarm(0)
        except Exception as e:
            signal.alarm(0)
            results = [{"order": order, "error": str(e), "type": "order_timeout_or_error"}]

        # Checkpoint
        cp_file = CHECKPOINT_DIR / f"order_{order}.jsonl"
        with open(cp_file, "w") as f:
            for rec in results:
                f.write(json.dumps(rec) + "\n")

        all_results.extend(results)

        elapsed = time.time() - t_order
        if (i + 1) % 50 == 0 or elapsed > 5:
            print(f"  Order {order} done ({i+1}/{total_orders}): {len(results)} nonabelian groups, {elapsed:.1f}s")

    total_time = time.time() - t0

    # Write final results
    with open(RESULTS_FILE, "w") as f:
        for rec in all_results:
            f.write(json.dumps(rec) + "\n")

    return all_results, total_time


def count_abelian_groups(start_order=2, end_order=511):
    """Count total abelian groups in range (for T0 reporting)."""
    count = 0
    for order in range(start_order, end_order + 1):
        try:
            n_groups = int(libgap.NumberSmallGroups(order))
            # Count abelian groups = number of abelian groups of this order
            # = number of partitions of the prime factorization
            # More accurate: use GAP
            n_abelian = int(libgap.Length(libgap.AllSmallGroups(order, libgap.IsAbelian, True)))
            count += n_abelian
        except Exception:
            pass
    return count


def count_abelian_fast(start_order=2, end_order=511):
    """Fast count of abelian groups using NrSmallGroups with filter."""
    count = 0
    for order in range(start_order, end_order + 1):
        try:
            # Number of abelian groups = number of abelian groups of given order
            ab_count = int(libgap.eval(f'Length(AllSmallGroups({order}, IsAbelian, true))'))
            count += ab_count
        except Exception:
            pass
    return count


def generate_summary(results, total_time, abelian_count):
    """Generate the sieve-summary.md stratum-A section."""
    # Tier counts
    tier_counts = {}
    action_counts = {"REJECT": 0, "SURVIVE": 0, "CAP": 0, "ERROR": 0}
    total_nonabelian = 0

    for rec in results:
        if "error" in rec and "type" in rec:
            action_counts["ERROR"] += 1
            continue
        total_nonabelian += 1
        tier = rec.get("tier", "UNKNOWN")
        tier_counts[tier] = tier_counts.get(tier, 0) + 1
        action = rec.get("action", "UNKNOWN")
        if action == "REJECT":
            action_counts["REJECT"] += 1
        elif action == "SURVIVE":
            action_counts["SURVIVE"] += 1
        elif "CAP" in str(action):
            action_counts["CAP"] += 1
        else:
            action_counts["ERROR"] += 1

    survivors = [r for r in results if r.get("action") == "SURVIVE"]
    capped = [r for r in results if "CAP" in str(r.get("action", ""))]

    summary_path = DOCS_DIR / "sieve-summary.md"
    with open(summary_path, "w") as f:
        f.write("# TPP Group Sieve Summary\n\n")
        f.write("## Stratum A: nonabelian groups of order 2..511\n\n")
        f.write(f"- Total groups in SmallGroups library (order 2..511): ~92,803\n")
        f.write(f"- Abelian groups (T0 REJECT): {abelian_count}\n")
        f.write(f"- Nonabelian groups processed: {total_nonabelian}\n")
        f.write(f"- Runtime: {total_time:.1f}s\n\n")

        f.write("### Per-tier counts\n\n")
        f.write("| Tier | Count | Description |\n")
        f.write("|------|-------|-------------|\n")
        f.write(f"| T0 | {abelian_count} | Abelian (rho_0 = 1) [Murthy26 Thm 2.3 / CU03 Lem 3.1] |\n")
        for tier in ["T1a", "T1b", "T2a", "T3a", "T3b", "T1c", "T2b"]:
            c = tier_counts.get(tier, 0)
            desc = {
                "T1a": "p-group |G| <= p^4 [Murthy26 Prop 2.14]",
                "T1b": "Class-2 p-group, cd={1,p} [Murthy26 Thm 6.1]",
                "T2a": "Class-2 p-group, p^2<=|G:Z|<=p^3 [Murthy26 Thm 5.1]",
                "T3a": "p-group, abelian subgroup index p [Murthy25 Cor 4.3(2)]",
                "T3b": "Abelian normal subgroup prime index [Murthy25 Thm 4.1]",
                "T1c": "p-group, cyclic G' order p, CAP(p) [Murthy26 Thm 4.1]",
                "T2b": "Survivors with packing ceilings [BCGPU Thm 3.2, Cor 3.8]",
            }.get(tier, "")
            f.write(f"| {tier} | {c} | {desc} |\n")

        f.write(f"\n### Action summary\n\n")
        f.write(f"| Action | Count |\n")
        f.write(f"|--------|-------|\n")
        f.write(f"| REJECT | {action_counts['REJECT']} |\n")
        f.write(f"| CAP (deprioritized) | {action_counts['CAP']} |\n")
        f.write(f"| SURVIVE | {action_counts['SURVIVE']} |\n")
        f.write(f"| ERROR/SKIP | {action_counts['ERROR']} |\n")

        f.write(f"\n### Survivors (tier T2b, action SURVIVE): {len(survivors)}\n\n")
        if survivors:
            # Sort by ceiling ascending (lower ceiling = less headroom)
            survivors_sorted = sorted(survivors, key=lambda r: r.get("ceiling", 999999), reverse=True)
            f.write("Top 20 by ceiling (descending):\n\n")
            f.write("| Group | Order | n(G) | |G:Z| | Ceiling | Nil class |\n")
            f.write("|-------|-------|------|-------|---------|----------|\n")
            for r in survivors_sorted[:20]:
                gid = r["id"]
                f.write(f"| [{gid[0]},{gid[1]}] | {r['order']} | {r.get('n_G', '?')} | {r['gz_index']} | {r.get('ceiling', '?'):.4g} | {r.get('nil_class', '?')} |\n")

        f.write(f"\n### Capped groups: {len(capped)}\n\n")
        if capped:
            f.write("Sample (first 10):\n\n")
            f.write("| Group | Tier | Cap value | Flags |\n")
            f.write("|-------|------|-----------|-------|\n")
            for r in capped[:10]:
                gid = r["id"]
                f.write(f"| [{gid[0]},{gid[1]}] | {r['tier']} | {r['action']} | {', '.join(r.get('flags', []))} |\n")

    return summary_path


# ---------------------------------------------------------------------------
# Signal handler for alarm-based timeouts
# ---------------------------------------------------------------------------

def alarm_handler(signum, frame):
    raise TimeoutError("Order processing timed out")

signal.signal(signal.SIGALRM, alarm_handler)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse
    parser = argparse.ArgumentParser(description="TPP Group Sieve")
    parser.add_argument("--harness-only", action="store_true", help="Only run the falsifiability harness")
    parser.add_argument("--workers", type=int, default=1, help="Number of workers (unused; sequential for libgap safety)")
    parser.add_argument("--start", type=int, default=2, help="Start order")
    parser.add_argument("--end", type=int, default=511, help="End order")
    args = parser.parse_args()

    # Always run harness first
    print("Running falsifiability harness...")
    print()
    passed, failures = run_anchor_harness()
    print()

    if not passed:
        print("STOPPING: harness failed. Fix tier predicates before sweeping.")
        sys.exit(1)

    if args.harness_only:
        print("Harness-only mode; exiting.")
        sys.exit(0)

    # Sweep stratum A
    print("=" * 60)
    print("Starting stratum A sweep...")
    print("=" * 60)
    print()

    results, total_time = sweep_stratum_a(args.start, args.end)

    # Count abelian groups
    print()
    print("Counting abelian groups...")
    abelian_count = count_abelian_fast(args.start, args.end)
    print(f"  Abelian groups: {abelian_count}")

    # Generate summary
    summary_path = generate_summary(results, total_time, abelian_count)
    print()
    print(f"Results written to: {RESULTS_FILE}")
    print(f"Summary written to: {summary_path}")
    print(f"Total runtime: {total_time:.1f}s")
    print(f"Nonabelian groups processed: {len(results)}")


if __name__ == "__main__":
    main()
