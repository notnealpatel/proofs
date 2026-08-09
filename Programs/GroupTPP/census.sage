"""
census.sage — Survivor census for TPP group sieve data.

For every SURVIVE and CAP record in the checkpoint data, computes:
  1. Whether G has a nontrivial abelian direct factor
     (via GAP DirectFactorsOfGroup).
  2. The nonabelian complement's SmallGroup id, when the group
     decomposes and IdSmallGroup is cheap (order in SmallGroups library).
  3. Extraspecial +/- type for T1c groups (cyclic G' order p, CAP(p)).
  4. T3b caps re-emitted as exact rational p^2/k where k is the
     integer subgroup index (the Murthy25 quantization).

Output: Scratch/GroupSieve/survivors-census*.jsonl
  One JSON record per group, checkpointed and resumable. Parallel runs
  write one file per shard; downstream readers must glob the pattern.
  Resume unions done-ids across all shard files, so re-sharding
  (e.g. 4 workers here, 256 shards on the cluster) is safe.

USAGE (USER-run only, per system.md sieve policy):
  sage census.sage -- --dry-run     # record count and projected runtime
  sage census.sage -- --workers 4   # 4 single-core shard subprocesses
  sage census.sage -- --shard 2/4   # one deterministic slice (cluster mode)
  sage census.sage                  # single core

Population: 88185 records (84681 SURVIVE + 3504 CAP).
Estimated cost: ~0.15s/group average for DirectFactorsOfGroup on p-groups,
cheaper for non-p-groups. Projected wall time: 2-4 hours.
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")
CHECKPOINT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "checkpoints"
OUTPUT_FILE = REPO_ROOT / "Scratch" / "GroupSieve" / "survivors-census.jsonl"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def load_targets():
    """Load all SURVIVE and CAP records from checkpoints, sorted by id."""
    targets = []
    for fname in sorted(CHECKPOINT_DIR.iterdir()):
        if not fname.name.startswith("order_") or not fname.suffix == ".jsonl":
            continue
        with open(fname) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                if rec.get("type"):
                    continue
                action = rec.get("action", "")
                if action == "SURVIVE" or action.startswith("CAP"):
                    targets.append(rec)
    targets.sort(key=lambda r: r["id"])
    return targets


def load_done_ids():
    """Load ids already processed from every census shard file (resume)."""
    done = set()
    for path in sorted(OUTPUT_FILE.parent.glob("survivors-census*.jsonl")):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    gid = rec.get("id")
                    if gid:
                        done.add(tuple(gid))
                except (json.JSONDecodeError, TypeError):
                    continue
    return done


def extraspecial_type(G, p, order):
    """
    Determine extraspecial +/- type for a p-group G.

    Extra-special means |Z(G)| = p, G' = Z(G), G/Z(G) elementary abelian.
    Returns "+", "-", or None if not extra-special.

    For p odd: exponent p => +, exponent p^2 => -.
    For p = 2, order 2^(2n+1):
      + type has 2^(2n) + 2^n - 1 involutions
      - type has 2^(2n) - 2^n - 1 involutions
    """
    Z = libgap.Center(G)
    if int(Z.Size()) != p:
        return None
    if not libgap.IsElementaryAbelian(G.FactorGroup(Z)):
        return None
    D = libgap.DerivedSubgroup(G)
    if D != Z:
        return None
    # Confirmed extra-special
    if p != 2:
        exp = int(libgap.Exponent(G))
        return "+" if exp == p else "-"
    else:
        # p = 2, order = 2^(2n+1)
        # Find n: order = 2^(2n+1) => 2n+1 = log2(order)
        import math
        k = int(math.log2(order))  # k = 2n+1
        n = (k - 1) // 2
        # Count involutions
        num_inv = sum(1 for g in G.Elements() if int(g.Order()) == 2)
        plus_inv = 2**(2*n) + 2**n - 1
        minus_inv = 2**(2*n) - 2**n - 1
        if num_inv == plus_inv:
            return "+"
        elif num_inv == minus_inv:
            return "-"
        else:
            return None  # shouldn't happen for true extra-special


def t3b_exact_rational(rec):
    """
    For T3b CAP records, extract the exact rational p^2/k.

    The action field is "CAP(float)" and the T3b ceiling is in ceilings.
    The cap value = p^2/k where k = |H : S0 T0 U0| is an integer.
    Since p is in the flags as "p=N", we can recover k = p^2 / cap_value.
    """
    flags = rec.get("flags", [])
    p = None
    for f in flags:
        if f.startswith("p="):
            p = int(f[2:])
            break
    if p is None:
        return None, None, None
    cap_val = rec["ceilings"].get("T3b")
    if cap_val is None:
        return p, None, None
    # k = p^2 / cap_val; should be integer
    from fractions import Fraction
    # cap_val is p^2/k stored as float; recover k
    k_approx = int(p) * int(p) / cap_val
    k = int(round(k_approx))
    # Verify
    exact = Fraction(int(p) * int(p), k)
    if abs(float(exact) - cap_val) < 1e-10:
        return p, k, f"{p}^2/{k}"
    else:
        return p, None, None


def process_group(rec):
    """Process one SURVIVE or CAP record; returns census dict."""
    gid = rec["id"]
    order = rec["order"]
    tier = rec["tier"]
    action = rec["action"]

    result = {
        "id": gid,
        "order": order,
        "tier": tier,
        "action": action,
    }

    # Load the group from GAP
    G = libgap.SmallGroup(order, gid[1])

    # 1. Direct factor decomposition
    df = libgap.DirectFactorsOfGroup(G)
    n_factors = len(df)
    result["n_direct_factors"] = n_factors

    if n_factors > 1:
        abelian_factors = []
        nonabelian_factors = []
        for f in df:
            f_order = int(f.Size())
            if libgap.IsAbelian(f):
                abelian_factors.append(f_order)
            else:
                # Try to identify via SmallGroup id
                try:
                    # cast: IdSmallGroup yields GapElement_Integer,
                    # which json.dumps rejects
                    sid = [int(x) for x in libgap.IdSmallGroup(f)]
                    nonabelian_factors.append(sid)
                except Exception:
                    nonabelian_factors.append([f_order, "?"])

        result["has_abelian_factor"] = len(abelian_factors) > 0
        if abelian_factors:
            result["abelian_factor_orders"] = sorted(abelian_factors)
        if nonabelian_factors:
            result["nonabelian_complements"] = nonabelian_factors
    else:
        result["has_abelian_factor"] = False

    # 3. Extra-special type for T1c groups
    if tier == "T1c":
        p_group = rec.get("p_group")
        if p_group:
            es_type = extraspecial_type(G, p_group, order)
            if es_type:
                result["extraspecial_type"] = es_type

    # 4. T3b exact rational
    if tier == "T3b" and action.startswith("CAP"):
        p, k, rational = t3b_exact_rational(rec)
        if rational:
            result["t3b_p"] = p
            result["t3b_k"] = k
            result["t3b_cap_rational"] = rational

    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run_workers(n_workers, limit):
    """Spawn one single-core shard subprocess per worker and wait."""
    import subprocess
    script = str(REPO_ROOT / "Scratch" / "GroupSieve" / "census.sage")
    procs = []
    for i in range(n_workers):
        cmd = ["sage", script, "--", f"--shard={i}/{n_workers}"]
        if limit:
            cmd.append(f"--limit={limit}")
        procs.append(subprocess.Popen(cmd))
    rc = 0
    try:
        for p in procs:
            rc |= p.wait()
    except KeyboardInterrupt:
        # Ctrl-C hits the whole process group; each worker checkpoints
        # itself — just wait for them to finish writing.
        print("\nInterrupt — waiting for workers to checkpoint...", flush=True)
        for p in procs:
            p.wait()
        rc = 1
    return rc


def main(argv):
    parser = argparse.ArgumentParser(description="TPP survivor census")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print stats and projected runtime, then exit")
    parser.add_argument("--workers", type=int, default=1,
                        help="Spawn N single-core shard subprocesses")
    parser.add_argument("--shard", default=None, metavar="I/N",
                        help="Process the I-th of N deterministic slices")
    parser.add_argument("--limit", type=int, default=0,
                        help="Stop after this many groups (0 = no limit)")
    args = parser.parse_args(argv)

    if args.workers > 1 and not args.dry_run:
        if args.shard:
            parser.error("--workers and --shard are mutually exclusive")
        return run_workers(args.workers, args.limit)

    shard_i, shard_n = 0, 1
    if args.shard:
        shard_i, shard_n = (int(x) for x in args.shard.split("/"))
        if not 0 <= shard_i < shard_n:
            parser.error(f"--shard {args.shard}: need 0 <= I < N")
    tag = f"[shard {shard_i}/{shard_n}] " if shard_n > 1 else ""
    out_file = (OUTPUT_FILE if shard_n == 1 else OUTPUT_FILE.with_name(
        f"survivors-census.shard{shard_i}of{shard_n}.jsonl"))

    print(f"{tag}Loading target records (SURVIVE + CAP)...", flush=True)
    targets = load_targets()
    n_total = len(targets)
    # Round-robin striping over the id-sorted list: interleaving spreads
    # the order-correlated cost evenly across shards.
    targets = targets[shard_i::shard_n]
    print(f"{tag}Targets in this shard: {len(targets)} of {n_total} total",
          flush=True)

    if args.dry_run:
        n_cores = max(args.workers, 1)
        per_core = n_total / n_cores
        print(f"\nProjected runtime at 0.15s/group: "
              f"{per_core * 0.15 / 3600:.1f} hours on {n_cores} core(s)")
        print(f"Projected runtime at 0.25s/group: "
              f"{per_core * 0.25 / 3600:.1f} hours on {n_cores} core(s)")
        return

    done_ids = load_done_ids()
    n_done = len(done_ids)
    remaining = [r for r in targets if tuple(r["id"]) not in done_ids]
    if args.limit:
        remaining = remaining[:args.limit]
    n_remaining = len(remaining)

    print(f"{tag}Already done (all shard files): {n_done}", flush=True)
    print(f"{tag}Remaining in this shard: {n_remaining}", flush=True)

    if n_remaining == 0:
        print(f"{tag}Nothing to do — shard complete.", flush=True)
        return

    # Runtime projection
    est_per_group = 0.15  # seconds, conservative average
    est_hours = n_remaining * est_per_group / 3600
    print(f"{tag}Estimated runtime: {est_hours:.1f} hours "
          f"(at {float(est_per_group):.2f}s/group average)", flush=True)
    print(f"{tag}Output: {out_file}", flush=True)

    # Process with progress
    t_start = time.time()
    n_processed = 0
    n_with_abelian_factor = 0
    errors = 0

    with open(out_file, "a") as out:
        for i, rec in enumerate(remaining):
            try:
                result = process_group(rec)
                out.write(json.dumps(result, separators=(",", ":")) + "\n")
                if (i + 1) % 100 == 0:
                    out.flush()
                n_processed += 1
                if result.get("has_abelian_factor"):
                    n_with_abelian_factor += 1
            except KeyboardInterrupt:
                print(f"\n{tag}Interrupted after {n_processed} groups.",
                      flush=True)
                break
            except Exception as e:
                errors += 1
                err_rec = {"id": rec["id"], "error": str(e)}
                out.write(json.dumps(err_rec, separators=(",", ":")) + "\n")
                if errors <= 5:
                    print(f"  {tag}ERROR on {rec['id']}: {e}", flush=True)

            # Progress every 500 groups
            if (i + 1) % 500 == 0:
                elapsed = time.time() - t_start
                rate = (i + 1) / elapsed
                eta = (n_remaining - i - 1) / rate
                print(f"  {tag}[{i+1}/{n_remaining}] "
                      f"{rate:.1f} groups/s, "
                      f"ETA {eta/60:.0f}min, "
                      f"abelian-factor: {n_with_abelian_factor}",
                      flush=True)

    elapsed = time.time() - t_start
    print(f"\n{tag}Done: {n_processed} processed, {errors} errors, "
          f"{elapsed/60:.1f} min elapsed.", flush=True)
    print(f"{tag}Groups with abelian direct factor: {n_with_abelian_factor} "
          f"({float(100*n_with_abelian_factor/max(n_processed,1)):.1f}%)",
          flush=True)


# sage's script loader does not execute .sage files
# under __name__ == "__main__" — an if-guard would silently skip
main([a for a in sys.argv[1:] if a != "--"])
