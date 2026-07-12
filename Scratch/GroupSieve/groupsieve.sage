"""
groupsieve.sage — TPP group sieve, single-source consolidated version.

Supersedes and retires sieve.sage, run_sweep.sage, and run_harness.sage
(2026-07-11): one copy of the tier cascade serves both the
falsifiability harness and the sweep, so a passing harness always
certifies exactly the code that produces the data.

Fixes carried in from the consolidation review:

- Character degrees come from GAP CharacterDegrees(). The retired
  sieve.sage read ZZ(chi[1]) assuming GAP's 1-based indexing, but
  libgap in Sage is 0-based: chi[1] is the character value at the
  second conjugacy class (cyclotomic in general), not the degree.
- The T3b tightening test is |G| % (2p-1) != 0 — the correct
  direction of "(2p-1) does not divide |G|".
- T2a (Murthy26 Thm 5.1: class-2 p-group, p^2 <= |G:Z| <= p^3) is
  intentionally absent. Isaacs Cor 2.30 gives chi(1)^2 <= |G:Z(G)|
  for every finite group, so under T2a's hypothesis every degree
  lies in {1, p} (p-group degrees are p-powers), cd(G) = {1, p},
  and T1b — same guard, earlier in the cascade — has already
  rejected the group. T2a fired zero times across 63,988 records
  for exactly this reason.
- No signal.alarm (conflicts with cysignals): soft deadline checks
  between groups instead. A single pathological group can overrun
  the deadline; per-group cost is small at these orders.
- The per-group handler catches Exception only. Ctrl-C checkpoints
  the current order as partial and exits cleanly with code 130.
- A checkpoint file no longer means "order done". Every order
  carries an explicit order_complete / order_partial control record
  and partial orders resume from the last processed index. Legacy
  checkpoints (group records only) are treated as complete; legacy
  partial_timeout sentinels are parsed for their resume index.
- Abelian groups are counted by the partition formula
  prod p(a_i) over |G| = prod p_i^a_i — no enumeration.
- The summary reports per-order coverage honestly; no hardcoded
  totals, and no dead "hard limit" mechanism.

USAGE — run by the USER, never by agents (system.md sieve policy).
The sage CLI wrapper needs `--` before script flags:

  sage groupsieve.sage -- --harness-only
      ~22 assertions over anchor groups; a few seconds.

  sage groupsieve.sage
      Resume the stratum-A sweep (orders 2..511). With the existing
      checkpoints only orders 256 and 384 are incomplete (~24.3k
      groups remaining, ~98% at order 256). Expect hours of wall
      clock for order 256; the run is resumable and Ctrl-C-safe, so
      it can be done in sessions.

  sage groupsieve.sage -- --order-timeout 0
      No per-order deadline: run each pending order to completion.

  sage groupsieve.sage -- --budget-min 30
      Stop cleanly (checkpointing) after ~30 minutes of wall clock.

  sage groupsieve.sage -- --summary-only
      Regenerate the summary from checkpoints without computing.

Space size: 92,803 groups of order 2..511; 56,092 at order 256 alone.
Checkpoints: Scratch/GroupSieve/checkpoints/order_N.jsonl
Summary:     .tasks/f5exp/docs/sieve-summary.md
Spec:        .tasks/f5exp/docs/sieve-spec.md
"""

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")
DOCS_DIR = REPO_ROOT / ".tasks" / "f5exp" / "docs"
CHECKPOINT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "checkpoints"
SUMMARY_FILE = DOCS_DIR / "sieve-summary.md"

CHECKPOINT_DIR.mkdir(parents=True, exist_ok=True)


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

    # (No T2a: provably shadowed by T1b — see module docstring.)

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
        # Murthy26 Thm 3.1: strict inequality for class 2
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
    # (order, idx), acceptable tiers
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

# [24,10] C3xD8 and [24,11] C3xQ8: known rho_0 = 1, but no tier can
# prove it — T3b with p=2 has (2p-1)=3 | 24, so Cor 4.3(1) is
# inapplicable and CAP(4/3) is the best available. A product-
# decomposition tier would close this (Im4 card).
ANCHORS_REJECT_OR_CAP = [
    ((24, 10), "T3b"),
    ((24, 11), "T3b"),
]

ANCHORS_MUST_NOT_REJECT = [
    # (order, idx), expected action pattern
    ((32, 49), "CAP"),        # extraspecial 2^5, rho_0 = 2, T1c CAP(2)
    ((64, 226), "SURVIVE"),   # cd = {1,2,4}, rho_0 = 2
    ((128, 1135), "SURVIVE"), # rho_0 = 2
    ((128, 2194), "SURVIVE"), # rho_0 = 2
]

ANCHORS_DIHEDRAL = [
    # (order, idx), expected action, required tier
    ((12, 4), "CAP", "T3b"),    # D12: 3 | 12, tight cap inapplicable, CAP(4/3)
    ((10, 1), "REJECT", "T3b"), # D10: 3 nmid 10, cap p/2 = 1, REJECT
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
# Checkpoints
# ---------------------------------------------------------------------------

def checkpoint_path(order):
    return CHECKPOINT_DIR / ("order_%d.jsonl" % order)


def load_checkpoint(order):
    """Returns (group_records, status, resume_idx).

    status: "complete" | "partial" | "absent".
    Control records carry a "type" key; group records never do.
    Legacy files with only group records are complete (the old sweep
    wrote checkpoints only after finishing an order, except for the
    partial_timeout sentinels, which are parsed here)."""
    path = checkpoint_path(order)
    if not path.exists():
        return [], "absent", 1

    records = []
    status = None
    resume_idx = 1
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            t = rec.get("type")
            if t is None:
                records.append(rec)
            elif t == "order_complete":
                status = "complete"
            elif t == "order_partial":
                status = "partial"
                resume_idx = int(rec["last_idx"]) + 1
            elif t == "partial_timeout":
                # legacy sentinel: "soft_timeout at idx K/M", K unprocessed
                status = "partial"
                m = re.search(r"idx (\d+)/", str(rec.get("error", "")))
                resume_idx = int(m.group(1)) if m else 1
            else:
                # legacy error control record (e.g. NumberSmallGroups_failed)
                status = "partial"
                resume_idx = 1
    if status is None:
        status = "complete"
    return records, status, resume_idx


def write_checkpoint(order, records, complete, last_done, n_groups):
    """Atomic rewrite: group records then one control record."""
    path = checkpoint_path(order)
    tmp = path.with_suffix(".jsonl.tmp")
    control = {
        "type": "order_complete" if complete else "order_partial",
        "order": int(order),
        "last_idx": int(last_done),
        "n_groups": int(n_groups),
    }
    with open(tmp, "w") as f:
        for rec in records:
            f.write(json.dumps(rec) + "\n")
        f.write(json.dumps(control) + "\n")
    os.replace(tmp, path)


# ---------------------------------------------------------------------------
# Sweep
# ---------------------------------------------------------------------------

def process_order(order, prior_records, start_idx, deadline):
    """Process nonabelian groups of one order from start_idx.
    Returns (records, complete, last_done, interrupted, n_groups)."""
    records = list(prior_records)
    seen = set()
    for r in records:
        rid = r.get("id")
        if rid:
            seen.add((int(rid[0]), int(rid[1])))

    n_groups = int(libgap.NumberSmallGroups(order))
    last_done = int(start_idx) - 1
    interrupted = False

    idx = int(start_idx)
    while idx <= n_groups:
        if deadline is not None and time.time() > deadline:
            break
        if (int(order), idx) in seen:
            last_done = idx
            idx += 1
            continue
        try:
            G = libgap.SmallGroup(order, idx)
            if not bool(G.IsAbelian()):
                records.append(classify_group(order, idx))
        except KeyboardInterrupt:
            interrupted = True
            break
        except Exception as e:
            records.append({
                "id": [int(order), idx],
                "order": int(order),
                "tier": "ERROR",
                "action": "SKIP",
                "error": str(e),
            })
        last_done = idx
        if n_groups > 2000 and idx % 2000 == 0:
            print("    order %d: %d/%d groups" % (order, idx, n_groups), flush=True)
        idx += 1

    complete = last_done >= n_groups
    return records, complete, last_done, interrupted, n_groups


def sweep(start_order, end_order, order_timeout, budget_min):
    t0 = time.time()
    global_deadline = t0 + budget_min * 60 if budget_min else None

    pending = []
    for order in range(int(start_order), int(end_order) + 1):
        records, status, resume_idx = load_checkpoint(order)
        if status != "complete":
            pending.append((order, records, resume_idx))

    print("Sweep orders %d..%d: %d pending order(s)" %
          (start_order, end_order, len(pending)), flush=True)
    for order, records, resume_idx in pending[:20]:
        print("  order %d: resume at idx %d (%d records held)" %
              (order, resume_idx, len(records)), flush=True)
    print(flush=True)

    for order, prior, resume_idx in pending:
        if global_deadline is not None and time.time() > global_deadline:
            print("Budget exhausted; stopping before order %d." % order, flush=True)
            break

        deadlines = []
        if order_timeout:
            deadlines.append(time.time() + order_timeout)
        if global_deadline is not None:
            deadlines.append(global_deadline)
        deadline = min(deadlines) if deadlines else None

        t1 = time.time()
        records, complete, last_done, interrupted, n_groups = \
            process_order(order, prior, resume_idx, deadline)
        write_checkpoint(order, records, complete, last_done, n_groups)

        state = "complete" if complete else ("interrupted" if interrupted else "partial")
        print("  order %d %s: idx %d/%d, %d nonabelian records, %.1fs" %
              (order, state, last_done, n_groups, len(records), time.time() - t1),
              flush=True)

        if interrupted:
            print("Interrupted — order %d checkpointed at idx %d; rerun to resume."
                  % (order, last_done), flush=True)
            sys.exit(130)

    print("Sweep pass done in %.1fs." % (time.time() - t0), flush=True)


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

def count_abelian(order):
    """Number of abelian groups of a given order: prod p(a_i) over the
    prime factorization — no enumeration."""
    c = 1
    for _, a in factor(order):
        c *= number_of_partitions(a)
    return int(c)


def generate_summary(start_order, end_order):
    total_groups = 0
    abelian_total = 0
    all_records = []
    incomplete = []       # (order, last_idx, n_groups)
    complete_orders = 0

    for order in range(int(start_order), int(end_order) + 1):
        n = int(libgap.NumberSmallGroups(order))
        total_groups += n
        abelian_total += count_abelian(order)
        records, status, resume_idx = load_checkpoint(order)
        all_records.extend(records)
        if status == "complete":
            complete_orders += 1
        else:
            last = resume_idx - 1 if status == "partial" else 0
            incomplete.append((order, last, n))

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

    with open(SUMMARY_FILE, "w") as f:
        f.write("# TPP Group Sieve Summary\n\n")
        f.write("Generated by `Scratch/GroupSieve/groupsieve.sage` on %s.\n\n"
                % time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime()))
        f.write("## Coverage — stratum A, orders %d..%d\n\n" % (start_order, end_order))
        f.write("- Orders complete: %d/%d\n" % (complete_orders, n_orders))
        f.write("- Total groups in range: %d (abelian: %d, nonabelian: %d)\n"
                % (total_groups, abelian_total, expected_nonabelian))
        f.write("- Nonabelian records held: %d of %d expected (%.1f%%)\n"
                % (len(all_records), expected_nonabelian,
                   100.0 * len(all_records) / expected_nonabelian if expected_nonabelian else 0.0))
        if incomplete:
            f.write("\n**Incomplete orders** (aggregate claims over the range are\n")
            f.write("unsound until these close):\n\n")
            for order, last, n in incomplete:
                f.write("- order %d: processed through idx %d of %d\n" % (order, last, n))
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
            "T1c": "p-group, cyclic G' order p, CAP(p) [Murthy26 Thm 4.1]",
            "T2b": "Survivors with packing ceilings [BCGPU Thm 3.2, Cor 3.8]",
            "ERROR": "Per-group classification errors",
        }
        for tier in ["T1a", "T1b", "T3a", "T3b", "T1c", "T2b", "ERROR"]:
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

    return SUMMARY_FILE


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv):
    parser = argparse.ArgumentParser(description="TPP group sieve (consolidated)")
    parser.add_argument("--harness-only", action="store_true",
                        help="run the falsifiability harness and exit")
    parser.add_argument("--summary-only", action="store_true",
                        help="regenerate the summary from checkpoints; no compute")
    parser.add_argument("--start", type=int, default=2)
    parser.add_argument("--end", type=int, default=511)
    parser.add_argument("--order-timeout", type=int, default=300,
                        help="soft seconds per order, 0 = none (default 300)")
    parser.add_argument("--budget-min", type=int, default=0,
                        help="overall wall-clock budget in minutes, 0 = none")
    args = parser.parse_args(argv)

    if args.summary_only:
        path = generate_summary(args.start, args.end)
        print("Summary: %s" % path, flush=True)
        return

    passed, n_assert, _ = run_anchor_harness()
    if not passed:
        print("STOPPING: fix the cascade before sweeping.", flush=True)
        sys.exit(1)
    if args.harness_only:
        return

    print(flush=True)
    sweep(args.start, args.end, args.order_timeout, args.budget_min)
    path = generate_summary(args.start, args.end)
    print("Summary: %s" % path, flush=True)


# The sage.cli runner executes this file inside sage_globals(), not
# under __name__ == "__main__" — an if-guard would silently skip
# main(). It also forwards the literal "--" separator that
# `sage groupsieve.sage -- --flags` requires; strip it here.
main([a for a in sys.argv[1:] if a != "--"])
