"""
tier4.sage — Tier-4 feature extraction for top-N sieve survivors.

Extracts normalizer quality (snr), minimal proper-subgroup index (m(G)),
and extraspecial type for ranking candidates. Reads the checkpoint data
to identify top-N survivors by ceiling, then probes each via GAP.

USER-RUN ONLY (system.md sieve policy). Resumable via checkpoint file.

USAGE:
  sage tier4.sage
      Default: top 50 survivors by ceiling.

  sage tier4.sage -- --top 100
      Top 100 survivors.

  sage tier4.sage -- --timeout 120
      Per-group timeout in seconds (default 60).

  sage tier4.sage -- --resume
      Resume from existing tier4-features.jsonl checkpoint.
"""
import json
import os
import sys
import time
from pathlib import Path

# Parse arguments manually (preparse-safe).
TOP_N = 50
PER_GROUP_TIMEOUT = 60
RESUME = False

args = sys.argv[1:]
i = 0
while i < len(args):
    if args[i] == "--top" and i + 1 < len(args):
        TOP_N = int(args[i + 1])
        i += 2
    elif args[i] == "--timeout" and i + 1 < len(args):
        PER_GROUP_TIMEOUT = int(args[i + 1])
        i += 2
    elif args[i] == "--resume":
        RESUME = True
        i += 1
    else:
        i += 1

CHECKPOINT_DIR = Path("checkpoints")
OUTPUT_FILE = Path("tier4-features.jsonl")


def load_survivors_ranked(top_n):
    """Load survivors from checkpoints, rank by ceiling desc, return top N."""
    survivors = []
    for f in sorted(CHECKPOINT_DIR.glob("order_*.jsonl")):
        with open(f) as fh:
            for line in fh:
                line = line.strip()
                if not line or "order_complete" in line or "order_partial" in line:
                    continue
                rec = json.loads(line)
                if rec.get("action", "").startswith("REJECT") or rec.get("action") == "ERROR":
                    continue
                ceiling = rec.get("ceiling", 0)
                if ceiling > 0:
                    survivors.append(rec)
    # Sort by ceiling descending, then order ascending for stability.
    survivors.sort(key=lambda r: (-r["ceiling"], r["order"], r["id"][1]))
    return survivors[:top_n]


def load_completed_ids():
    """Load IDs already in the output checkpoint."""
    done = set()
    if OUTPUT_FILE.exists():
        with open(OUTPUT_FILE) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    done.add(tuple(rec["id"]))
                except (json.JSONDecodeError, KeyError):
                    pass
    return done


def snr_quality(G, order_G, timeout_sec):
    """
    Self-normalizing ratio: min |N_G(H)| / |H| over conjugacy classes
    of proper nontrivial subgroups H. Lower snr = H is closer to
    self-normalizing = better for TPP construction (BCGPU Thm 3.6).

    Returns (snr_value, timed_out).
    """
    import signal

    best_snr = None
    timed_out = False
    start = time.time()

    try:
        # Get conjugacy classes of subgroups (GAP).
        cc = G.conjugacy_classes_subgroups()
        for cls in cc:
            if time.time() - start > timeout_sec:
                timed_out = True
                break
            # conjugacy_classes_subgroups() yields representative
            # subgroups directly; indexing one grabs its identity element
            H = cls
            h_order = H.order()
            if h_order == Integer(1) or h_order == order_G:
                continue
            N_H = G.normalizer(H)
            ratio = QQ(N_H.order()) / QQ(h_order)
            if best_snr is None or ratio < best_snr:
                best_snr = ratio
    except Exception as e:
        print("    snr error: %s" % e, flush=True)
        timed_out = True

    return (float(best_snr) if best_snr is not None else None, timed_out)


def minimal_proper_subgroup_index(G, order_G, timeout_sec):
    """
    m(G) = minimal index [G:H] over proper nontrivial subgroups H.
    This is the quasirandomness-adjacent parameter (probe-quasirandomness-verdict.md).

    Returns (m_value, timed_out).
    """
    start = time.time()
    best_m = None
    timed_out = False

    try:
        cc = G.conjugacy_classes_subgroups()
        for cls in cc:
            if time.time() - start > timeout_sec:
                timed_out = True
                break
            # conjugacy_classes_subgroups() yields representative
            # subgroups directly; indexing one grabs its identity element
            H = cls
            h_order = H.order()
            if h_order == Integer(1) or h_order == order_G:
                continue
            idx = order_G // h_order
            if best_m is None or idx < best_m:
                best_m = idx
        # Also check maximal subgroups for minimum index.
    except Exception as e:
        print("    m(G) error: %s" % e, flush=True)
        timed_out = True

    return (int(best_m) if best_m is not None else None, timed_out)


def extraspecial_type_check(G, order_G, p_group):
    """
    For extraspecial p-groups: determine + or - type.
    Returns "+", "-", or None if not extraspecial.
    """
    if p_group is None:
        return None
    p = p_group
    # Extraspecial: |G| = p^(1+2n), |Z(G)| = p, G' = Z(G) = Phi(G).
    Z = G.center()
    if Z.order() != p:
        return None
    G_derived = G.derived_subgroup()
    if G_derived.order() != p:
        return None
    if not Z.is_isomorphic(G_derived):
        return None
    # G is extraspecial. Determine type by exponent.
    # Type +: exponent p (for p odd) or exponent 4 and extra (for p=2, D8-central-products)
    # Type -: exponent p^2 (for p odd) or exponent 4 with Q8 factor (for p=2)
    exp_G = G.exponent()
    if p == Integer(2):
        # For 2-groups: ES+ = central product of D8's, exponent 4 but
        # contains element of order 4 in the center? No, center is C2.
        # Actually: ES+(2^(1+2n)) has all elements of order <= 4 and
        # for n=2 (order 32): [32,49] is D8*D8 (type +), [32,50] is D8*Q8 (type -)
        # Distinguish by number of elements of order 2 vs 4:
        # Type + has more involutions.
        # Safest: check if the group has a faithful irrep of degree p^n
        # and compare structure. For p=2, use the Arf invariant.
        # Simpler: type + iff the group has exponent 4 and
        # |{g : g^2 = 1}| = 2^(n+1) + 2^n - 1 (more involutions).
        # For order 2^(1+2n): count involutions.
        n_involutions = sum(Integer(1) for g in G if g.order() == Integer(2))
        n = (order_G.valuation(Integer(2)) - Integer(1)) // Integer(2)
        # ES+: 2^(2n) + 2^n - 1 involutions (including identity? no)
        # ES-: 2^(2n) - 2^n - 1 involutions
        # Standard: ES+(2^(1+2n)) has 2^(2n-1) + 2^(n-1) elements of order 2.
        # Actually just compare: + type has more involutions than - type.
        # For n=2 (order 32): ES+ has 2^3+2^2-1 = 11 involutions? Let's not
        # over-engineer: just check if G is isomorphic to the library group.
        # Use a simpler criterion: type + iff G has a subgroup isomorphic to D8^n.
        # Simplest practical test: compare GAP ID.
        gap_id = G.gap().IdSmallGroup()
        gap_id_tuple = (int(gap_id[Integer(1)]), int(gap_id[Integer(2)]))
        # Known extraspecial IDs:
        # Order 8: [8,3]=D8(+), [8,4]=Q8(-)
        # Order 32: [32,49]=ES+, [32,50]=ES-
        # Order 128: [128,928]=ES+, [128,929]=ES- (verify)
        # General rule: for each order p^(1+2n), ES+ is the one with
        # larger number of involutions.
        # Since we have the GAP ID we can look up empirically, but for
        # a safe general method: count involutions, more = +.
        if p == Integer(2) and n >= Integer(1):
            # For order 2^(1+2n): ES+ has 2^(2n-1)+2^(n-1) involutions
            expected_plus = Integer(2)**(Integer(2)*n-Integer(1)) + Integer(2)**(n-Integer(1))
            if n_involutions >= expected_plus:
                return "+"
            else:
                return "-"
    else:
        # Odd p: ES+ has exponent p, ES- has exponent p^2.
        if exp_G == p:
            return "+"
        elif exp_G == p**Integer(2):
            return "-"
    return None


def main():
    print("=== Tier-4 Feature Extraction ===", flush=True)
    print("  top_n=%d, per_group_timeout=%ds" % (TOP_N, PER_GROUP_TIMEOUT), flush=True)
    print(flush=True)

    # Load and rank survivors.
    print("[1/4] Loading checkpoint survivors...", flush=True)
    survivors = load_survivors_ranked(TOP_N)
    print("  Selected %d survivors for feature extraction" % len(survivors), flush=True)
    if not survivors:
        print("ERROR: no survivors found in checkpoints/", flush=True)
        sys.exit(1)

    # Load completed IDs for resume.
    done_ids = set()
    if RESUME and OUTPUT_FILE.exists():
        done_ids = load_completed_ids()
        print("  Resuming: %d groups already done" % len(done_ids), flush=True)

    # Process each survivor.
    print("[2/4] Extracting features...", flush=True)
    n_done = 0
    n_timeout = 0
    n_total = len(survivors)

    out_fh = open(OUTPUT_FILE, "a" if RESUME else "w")

    for idx, rec in enumerate(survivors):
        gid = tuple(rec["id"])
        if gid in done_ids:
            n_done += 1
            continue

        order_val = rec["order"]
        gap_idx = rec["id"][1]
        print("  [%d/%d] [%d,%d] (ceiling=%.4f) ..." %
              (idx + 1, n_total, order_val, gap_idx, rec["ceiling"]),
              end="", flush=True)

        t0 = time.time()

        # Construct the group via in-process libgap: the pexpect `gap`
        # interface needs a standalone gap binary this env lacks.
        H_pc = libgap.SmallGroup(order_val, gap_idx)
        P = libgap.Image(libgap.IsomorphismPermGroup(H_pc))
        G = PermutationGroup(gap_group=P)
        order_G = Integer(order_val)
        p_group_val = rec.get("p_group")

        # Feature: snr (normalizer quality).
        snr_val, snr_timeout = snr_quality(G, order_G, PER_GROUP_TIMEOUT)

        # Feature: m(G) (minimal proper-subgroup index).
        m_val, m_timeout = minimal_proper_subgroup_index(G, order_G, PER_GROUP_TIMEOUT)

        # Feature: extraspecial type (for p-groups with cyclic derived of order p).
        es_type = None
        if p_group_val is not None and rec.get("derived_cyclic") and rec.get("derived_order") == p_group_val:
            es_type = extraspecial_type_check(G, order_G, Integer(p_group_val))

        elapsed = time.time() - t0
        timed_out = snr_timeout or m_timeout
        if timed_out:
            n_timeout += 1

        # Build output record.
        out_rec = {
            "id": rec["id"],
            "order": order_val,
            "tier": rec["tier"],
            "ceiling": rec["ceiling"],
            "n_G": rec.get("n_G"),
            "cd": rec.get("cd"),
            "snr": (float(snr_val) if snr_val is not None else None),
            "m_G": (int(m_val) if m_val is not None else None),
            "extraspecial_type": es_type,
            "snr_timeout": snr_timeout,
            "m_timeout": m_timeout,
            # Sage's global round() returns RDF, which json.dumps rejects
            "elapsed_s": float(round(elapsed, 2)),
        }

        out_fh.write(json.dumps(out_rec) + "\n")
        out_fh.flush()
        n_done += 1

        status = " TIMEOUT" if timed_out else ""
        print(" snr=%s m=%s es=%s (%.1fs)%s" %
              (("%.3f" % snr_val if snr_val is not None else "?"),
               (str(m_val) if m_val is not None else "?"),
               (es_type if es_type else "-"),
               elapsed, status), flush=True)

    out_fh.close()

    # Summary.
    print(flush=True)
    print("[3/4] Feature extraction complete.", flush=True)
    print("  Groups processed: %d/%d" % (n_done, n_total), flush=True)
    print("  Timeouts: %d" % n_timeout, flush=True)
    print("  Output: %s" % OUTPUT_FILE, flush=True)
    print(flush=True)
    print("[4/4] Done.", flush=True)


main()
