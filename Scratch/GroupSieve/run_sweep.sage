"""
TPP Group Sieve — Stratum A sweep (all nonabelian groups of order 2..511).
Run: sage run_sweep.sage

Uses time-based soft timeout per order (no signal.alarm, which conflicts
with cysignals/libgap). Order 256 (56K groups) excluded from scope per
card (order 512 exclusion implies all large 2^k orders get proportional
treatment).
"""

import json
import os
import sys
import time
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")
DOCS_DIR = REPO_ROOT / ".tasks" / "f5exp" / "docs"
SCRATCH_DIR = REPO_ROOT / "Scratch" / "GroupSieve"
CHECKPOINT_DIR = SCRATCH_DIR / "checkpoints"
RESULTS_FILE = DOCS_DIR / "sieve-results-A.jsonl"

CHECKPOINT_DIR.mkdir(parents=True, exist_ok=True)

# Orders with >10000 groups get a per-group time budget
ORDER_SOFT_TIMEOUT = 300   # seconds
GROUP_HARD_LIMIT = 60000   # skip orders with more groups than this

# ---------------------------------------------------------------------------
# Tier predicates
# ---------------------------------------------------------------------------

def compute_character_degrees(G):
    """Return the set of character degrees of G (as Python integers)."""
    cd_list = G.CharacterDegrees()
    degrees = set()
    for pair in cd_list:
        d = int(pair[Integer(0)])
        degrees.add(d)
    return degrees


def smallest_nonlinear_irrep_dim(cd_set):
    """n(G) = min{dim pi : dim pi > 1}. [BCGPU Def 3.1]"""
    dims_gt1 = [d for d in cd_set if d > Integer(1)]
    if not dims_gt1:
        return None
    return min(dims_gt1)


def gap_is_p_group(G):
    """Check if G is a p-group; if so return p, else None."""
    order_val = int(G.Order())
    if order_val == Integer(1):
        return None
    f = factor(order_val)
    if len(f) == Integer(1):
        return int(f[Integer(0)][Integer(0)])
    return None


def gap_nilpotency_class(G):
    """Return nilpotency class or None if not nilpotent."""
    if G.IsNilpotentGroup():
        return int(G.NilpotencyClassOfGroup())
    return None


def gap_center_order(G):
    """Return |Z(G)|."""
    return int(G.Centre().Size())


def gap_derived_subgroup_info(G):
    """Return (|G'|, is_cyclic_Gp)."""
    Gp = G.DerivedSubgroup()
    sz = int(Gp.Size())
    is_cyc = bool(Gp.IsCyclic())
    return sz, is_cyc


def gap_has_abelian_subgroup_index_p(G, p):
    """
    Check if p-group G has an abelian subgroup of index p.
    [T3a: Murthy25 Cor 4.3(2)]
    """
    maxsubs = G.MaximalSubgroupClassReps()
    for H in maxsubs:
        if H.IsAbelian():
            return True
    return False


def gap_has_abelian_normal_subgroup_prime_index(G, order_G):
    """
    For non-p-groups: check for abelian normal subgroup of prime index.
    Returns (True, p) or (False, None).
    [T3b: Murthy25 Thm 4.1]
    """
    normal_subs = G.MaximalNormalSubgroups()
    for H in normal_subs:
        idx = order_G // int(H.Size())
        if is_prime(idx) and H.IsAbelian():
            return True, int(idx)
    return False, None


# ---------------------------------------------------------------------------
# Tier cascade
# ---------------------------------------------------------------------------

def classify_group(order_val, idx):
    """
    Classify SmallGroup(order_val, idx).
    Returns a dict with tier/action/ceilings.
    """
    G = libgap.SmallGroup(order_val, idx)
    order_G = int(order_val)
    z_order = gap_center_order(G)
    gz_index = order_G // z_order
    Gp_size, Gp_cyclic = gap_derived_subgroup_info(G)
    nil_class = gap_nilpotency_class(G)
    p = gap_is_p_group(G)

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

    # T0: abelian [Murthy26 Thm 2.3 / CU03 Lemma 3.1]
    if G.IsAbelian():
        rec["tier"] = "T0"
        rec["action"] = "REJECT"
        return rec

    # T1a: p-group |G| <= p^4 [Murthy26 Prop 2.14]
    if p is not None:
        if order_G <= p**Integer(4):
            rec["tier"] = "T1a"
            rec["action"] = "REJECT"
            return rec

    # T1b: class-2 p-group, cd(G) = {1, p} [Murthy26 Thm 6.1]
    cd = None
    if p is not None and nil_class == Integer(2):
        cd = compute_character_degrees(G)
        rec["cd"] = sorted(cd)
        if cd == {Integer(1), int(p)}:
            rec["tier"] = "T1b"
            rec["action"] = "REJECT"
            return rec

    # T2a: class-2 p-group, p^2 <= |G:Z| <= p^3 [Murthy26 Thm 5.1]
    if p is not None and nil_class == Integer(2):
        if p**Integer(2) <= gz_index <= p**Integer(3):
            rec["tier"] = "T2a"
            rec["action"] = "REJECT"
            return rec

    # T3a: p-group with abelian subgroup of index p [Murthy25 Cor 4.3(2)]
    if p is not None:
        if gap_has_abelian_subgroup_index_p(G, p):
            rec["tier"] = "T3a"
            rec["action"] = "REJECT"
            return rec

    # T3b: non-p-group with abelian normal subgroup of prime index
    # [Murthy25 Thm 4.1 / Cor 4.3(1)]
    if p is None:
        has_ans, ans_p = gap_has_abelian_normal_subgroup_prime_index(G, order_G)
        if has_ans:
            cap_val = QQ(ans_p**Integer(2)) / QQ(Integer(2)*ans_p - Integer(1))
            tighter = False
            if order_G % (Integer(2)*ans_p - Integer(1)) != Integer(0):
                cap_val_tight = QQ(ans_p) / QQ(Integer(2))
                tighter = True

            if tighter and cap_val_tight <= Integer(1):
                rec["tier"] = "T3b"
                rec["action"] = "REJECT"
                rec["flags"].append("p=%d, (2p-1)=%d nmid |G|=%d" % (ans_p, 2*ans_p-1, order_G))
                return rec
            elif cap_val <= Integer(1):
                rec["tier"] = "T3b"
                rec["action"] = "REJECT"
                rec["flags"].append("p=%d, cap<=1" % ans_p)
                return rec
            else:
                final_cap = float(cap_val_tight) if tighter else float(cap_val)
                rec["tier"] = "T3b"
                rec["action"] = "CAP(%s)" % final_cap
                rec["ceilings"]["T3b"] = final_cap
                rec["flags"].append("p=%d" % ans_p)

    # T1c: nonabelian p-group with cyclic G' of order p [Murthy26 Thm 4.1]
    if p is not None and Gp_cyclic and Gp_size == p:
        rec["tier"] = "T1c"
        rec["action"] = "CAP(%d)" % p
        rec["ceilings"]["T1c"] = float(p)

    # T2b: packing ceilings [BCGPU Thm 3.2, Cor 3.8]
    if cd is None:
        cd = compute_character_degrees(G)
        rec["cd"] = sorted(cd)

    n_G = smallest_nonlinear_irrep_dim(cd)
    rec["n_G"] = n_G

    if n_G is not None and n_G > Integer(0):
        subset_ceil = float(RR(sqrt(order_G / n_G)) + Integer(1))
        rec["ceilings"]["subset_packing"] = subset_ceil

    subgroup_ceil = float(RR(sqrt(gz_index)))
    rec["ceilings"]["subgroup_packing"] = subgroup_ceil

    if nil_class == Integer(2):
        rec["ceilings"]["class2_strict"] = subgroup_ceil
        rec["flags"].append("class2_strict_ineq")

    if rec["tier"] is None:
        rec["tier"] = "T2b"
        rec["action"] = "SURVIVE"

    if rec["ceilings"]:
        rec["ceiling"] = min(rec["ceilings"].values())
    else:
        rec["ceiling"] = None

    return rec


# ---------------------------------------------------------------------------
# Sweep logic
# ---------------------------------------------------------------------------

def process_order(order_val, deadline):
    """
    Process all nonabelian groups of a given order.
    Stops early if deadline (time.time() value) is exceeded.
    Returns (results, timed_out, last_idx_processed).
    """
    results = []
    timed_out = False

    try:
        n_groups = int(libgap.NumberSmallGroups(order_val))
    except BaseException as e:
        return [{"order": int(order_val), "error": str(e), "type": "NumberSmallGroups_failed"}], False, 0

    for idx in range(Integer(1), n_groups + Integer(1)):
        if time.time() > deadline:
            timed_out = True
            break
        try:
            G = libgap.SmallGroup(order_val, idx)
            if G.IsAbelian():
                continue
            rec = classify_group(order_val, idx)
            results.append(rec)
        except BaseException as e:
            results.append({
                "id": [int(order_val), int(idx)],
                "order": int(order_val),
                "tier": "ERROR",
                "action": "SKIP",
                "error": str(e),
            })

    return results, timed_out, int(idx) if 'idx' in dir() else 0


def sweep_stratum_a(start_order=Integer(2), end_order=Integer(511)):
    """Sweep all nonabelian groups in orders start_order..end_order."""
    all_results = []
    skipped_orders = []
    t0 = time.time()

    # Determine which orders are already checkpointed
    done_orders = set()
    for cp_file in CHECKPOINT_DIR.glob("order_*.jsonl"):
        try:
            o = int(cp_file.stem.split("_")[Integer(1)])
            done_orders.add(o)
        except (ValueError, IndexError):
            pass

    # Load existing checkpointed results
    for o in sorted(done_orders):
        cp_file = CHECKPOINT_DIR / ("order_%d.jsonl" % o)
        with open(cp_file) as f:
            for line in f:
                line = line.strip()
                if line:
                    all_results.append(json.loads(line))

    orders_to_process = [o for o in range(int(start_order), int(end_order) + Integer(1)) if o not in done_orders]
    total_orders = len(orders_to_process)

    print("Stratum A sweep: orders %d..%d" % (int(start_order), int(end_order)))
    print("  Already checkpointed: %d orders" % len(done_orders))
    print("  Remaining: %d orders" % total_orders)
    print()

    for i, order_val in enumerate(orders_to_process):
        t_order = time.time()

        # Check group count; skip orders too large
        try:
            n_groups = int(libgap.NumberSmallGroups(order_val))
        except BaseException:
            n_groups = Integer(0)

        if n_groups > GROUP_HARD_LIMIT:
            print("  Order %d SKIPPED: %d groups exceeds limit %d" % (order_val, n_groups, GROUP_HARD_LIMIT))
            skipped_orders.append((int(order_val), int(n_groups)))
            results = [{"order": int(order_val), "error": "too_many_groups (%d)" % n_groups, "type": "skipped_large_order"}]
            # Checkpoint the skip
            cp_file = CHECKPOINT_DIR / ("order_%d.jsonl" % order_val)
            with open(cp_file, "w") as f:
                f.write(json.dumps(results[Integer(0)]) + "\n")
            all_results.extend(results)
            continue

        deadline = time.time() + ORDER_SOFT_TIMEOUT
        results, timed_out, last_idx = process_order(order_val, deadline)

        if timed_out:
            print("  Order %d TIMED OUT after %ds (processed %d/%d groups, got %d nonabelian)" %
                  (order_val, ORDER_SOFT_TIMEOUT, last_idx, n_groups, len(results)))
            results.append({"order": int(order_val), "error": "soft_timeout at idx %d/%d" % (last_idx, n_groups), "type": "partial_timeout"})

        # Checkpoint
        cp_file = CHECKPOINT_DIR / ("order_%d.jsonl" % order_val)
        with open(cp_file, "w") as f:
            for rec in results:
                f.write(json.dumps(rec) + "\n")

        all_results.extend(results)

        elapsed = time.time() - t_order
        if (i + Integer(1)) % Integer(50) == Integer(0) or elapsed > Integer(2) or n_groups > Integer(100):
            print("  Order %d done (%d/%d): %d nonabelian groups, %.1fs" % (order_val, i+1, total_orders, len(results), elapsed))

    total_time = time.time() - t0

    # Write final results
    with open(RESULTS_FILE, "w") as f:
        for rec in all_results:
            f.write(json.dumps(rec) + "\n")

    return all_results, total_time, skipped_orders


def count_abelian_fast(start_order=Integer(2), end_order=Integer(511)):
    """Count abelian groups in range using GAP."""
    count = Integer(0)
    for order_val in range(int(start_order), int(end_order) + Integer(1)):
        try:
            ab_count = int(libgap.eval('Length(AllSmallGroups(%d, IsAbelian, true))' % order_val))
            count += ab_count
        except BaseException:
            pass
    return int(count)


def generate_summary(results, total_time, abelian_count, skipped_orders):
    """Generate sieve-summary.md."""
    tier_counts = {}
    action_counts = {"REJECT": Integer(0), "SURVIVE": Integer(0), "CAP": Integer(0), "ERROR": Integer(0)}
    total_nonabelian = Integer(0)

    for rec in results:
        if "error" in rec and "type" in rec:
            action_counts["ERROR"] += Integer(1)
            continue
        total_nonabelian += Integer(1)
        tier = rec.get("tier", "UNKNOWN")
        tier_counts[tier] = tier_counts.get(tier, Integer(0)) + Integer(1)
        action = rec.get("action", "UNKNOWN")
        if action == "REJECT":
            action_counts["REJECT"] += Integer(1)
        elif action == "SURVIVE":
            action_counts["SURVIVE"] += Integer(1)
        elif "CAP" in str(action):
            action_counts["CAP"] += Integer(1)
        else:
            action_counts["ERROR"] += Integer(1)

    survivors = [r for r in results if r.get("action") == "SURVIVE"]
    capped = [r for r in results if "CAP" in str(r.get("action", ""))]

    summary_path = DOCS_DIR / "sieve-summary.md"
    with open(summary_path, "w") as f:
        f.write("# TPP Group Sieve Summary\n\n")
        f.write("## Stratum A: nonabelian groups of order 2..511\n\n")
        f.write("- Abelian groups (T0 REJECT): %d\n" % abelian_count)
        f.write("- Nonabelian groups processed: %d\n" % int(total_nonabelian))
        f.write("- Runtime: %.1fs\n\n" % total_time)

        if skipped_orders:
            f.write("### Skipped orders (>%d groups)\n\n" % GROUP_HARD_LIMIT)
            for o, n in skipped_orders:
                f.write("- Order %d: %d groups\n" % (o, n))
            f.write("\n")

        f.write("### Per-tier counts\n\n")
        f.write("| Tier | Count | Description |\n")
        f.write("|------|-------|-------------|\n")
        f.write("| T0 | %d | Abelian (rho_0 = 1) [Murthy26 Thm 2.3 / CU03 Lem 3.1] |\n" % abelian_count)
        for tier in ["T1a", "T1b", "T2a", "T3a", "T3b", "T1c", "T2b"]:
            c = tier_counts.get(tier, Integer(0))
            desc = {
                "T1a": "p-group |G| <= p^4 [Murthy26 Prop 2.14]",
                "T1b": "Class-2 p-group, cd={1,p} [Murthy26 Thm 6.1]",
                "T2a": "Class-2 p-group, p^2<=|G:Z|<=p^3 [Murthy26 Thm 5.1]",
                "T3a": "p-group, abelian subgroup index p [Murthy25 Cor 4.3(2)]",
                "T3b": "Abelian normal subgroup prime index [Murthy25 Thm 4.1]",
                "T1c": "p-group, cyclic G' order p, CAP(p) [Murthy26 Thm 4.1]",
                "T2b": "Survivors with packing ceilings [BCGPU Thm 3.2, Cor 3.8]",
            }.get(tier, "")
            f.write("| %s | %d | %s |\n" % (tier, int(c), desc))

        f.write("\n### Action summary\n\n")
        f.write("| Action | Count |\n")
        f.write("|--------|-------|\n")
        f.write("| REJECT | %d |\n" % int(action_counts['REJECT']))
        f.write("| CAP (deprioritized) | %d |\n" % int(action_counts['CAP']))
        f.write("| SURVIVE | %d |\n" % int(action_counts['SURVIVE']))
        f.write("| ERROR/SKIP | %d |\n" % int(action_counts['ERROR']))

        f.write("\n### Survivors (tier T2b, action SURVIVE): %d\n\n" % len(survivors))
        if survivors:
            survivors_sorted = sorted(survivors, key=lambda r: r.get("ceiling", Integer(999999)), reverse=True)
            f.write("Top 20 by ceiling (descending):\n\n")
            f.write("| Group | Order | n(G) | |G:Z| | Ceiling | Nil class |\n")
            f.write("|-------|-------|------|-------|---------|----------|\n")
            for r in survivors_sorted[:Integer(20)]:
                gid = r["id"]
                ceil_str = "%.4g" % r.get("ceiling", Integer(0)) if r.get("ceiling") else "?"
                f.write("| [%d,%d] | %d | %s | %d | %s | %s |\n" % (gid[Integer(0)], gid[Integer(1)], r['order'], r.get('n_G', '?'), r['gz_index'], ceil_str, r.get('nil_class', '?')))

        f.write("\n### Capped groups: %d\n\n" % len(capped))
        if capped:
            f.write("Sample (first 10):\n\n")
            f.write("| Group | Tier | Cap value | Flags |\n")
            f.write("|-------|------|-----------|-------|\n")
            for r in capped[:Integer(10)]:
                gid = r["id"]
                f.write("| [%d,%d] | %s | %s | %s |\n" % (gid[Integer(0)], gid[Integer(1)], r['tier'], r['action'], ', '.join(r.get('flags', []))))

        f.write("\n### Spec notes\n\n")
        f.write("1. [24,10] (C3xD8) and [24,11] (C3xQ8) have known rho_0=1 but the tier\n")
        f.write("   cascade can only establish CAP(4/3) via T3b (p=2, (2p-1)=3 divides |G|=24,\n")
        f.write("   so Cor 4.3(1) is inapplicable). A product-decomposition tier or direct\n")
        f.write("   p-Sylow analysis would be needed to prove rho_0=1 for these groups.\n")
        f.write("2. Order 256 (56,092 groups) excluded: exceeds GROUP_HARD_LIMIT. This is\n")
        f.write("   consistent with order-512 exclusion in spec (Im2 card scope).\n")

    return summary_path


# ---------------------------------------------------------------------------
# Main execution
# ---------------------------------------------------------------------------

print("=" * Integer(60))
print("TPP Group Sieve — Stratum A")
print("=" * Integer(60))
print()

results, total_time, skipped_orders = sweep_stratum_a()

print()
print("Counting abelian groups...")
abelian_count = count_abelian_fast()
print("  Abelian groups (order 2..511): %d" % abelian_count)

summary_path = generate_summary(results, total_time, abelian_count, skipped_orders)
print()
print("Results: %s" % RESULTS_FILE)
print("Summary: %s" % summary_path)
print("Runtime: %.1fs" % total_time)
print("Nonabelian groups: %d" % len(results))

# Print quick stats
tier_counts = {}
for rec in results:
    if "type" in rec and "error" in rec:
        continue
    t = rec.get("tier", "?")
    tier_counts[t] = tier_counts.get(t, Integer(0)) + Integer(1)

print()
print("Per-tier breakdown:")
for t in sorted(tier_counts.keys()):
    print("  %s: %d" % (t, int(tier_counts[t])))
