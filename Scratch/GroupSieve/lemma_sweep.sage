"""
lemma_sweep.sage — Lemma M / Lemma D kill-test sweep over SmallGroups.

Exhaustive verification of the Pf3 abelian-factor conjecture
(rho_0(A x G) = rho_0(G)) by testing Lemma M (the equivalent algebraic
statement) and Lemma D (the distributed-shrink certificate) on every
nonabelian group at orders <= 64 plus all sieve survivors at orders
96 and 128.

A SINGLE VIOLATION kills the conjecture — surface immediately.

This wraps the probe logic from .tasks/f5exp/docs/pf3-probes/
{lemmaM2.sage, lemmaD.sage}, refactored for parallel batch execution
with checkpoint/resume.

USAGE (USER-run only, per system.md sieve policy):
  sage lemma_sweep.sage -- --dry-run            # space stats + projection
  sage lemma_sweep.sage                         # single core, resume
  sage lemma_sweep.sage -- --shard 0/4          # deterministic slice
  sage lemma_sweep.sage -- --shard 0/4 --lemma-d  # also run Lemma D
  sage lemma_sweep.sage -- --limit 10           # process at most 10

Space: 469 nonabelian groups at orders 2..64, plus ~2135 sieve
survivors at orders 96 and 128 = ~2604 targets total.
Projected runtime: ~2-6 hours single-core (dominated by order-64
groups and order-128 survivors with large subgroup lattices).
Output: Scratch/GroupSieve/lemma-sweep-results.jsonl (or per-shard).
Provenance: Pf3 (.tasks/f5exp/docs/Pf3-abelian-factor.md) + Im6.
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")
CHECKPOINT_DIR = REPO_ROOT / "Scratch" / "GroupSieve" / "checkpoints"
OUTPUT_FILE = REPO_ROOT / "Scratch" / "GroupSieve" / "lemma-sweep-results.jsonl"

# ---------------------------------------------------------------------------
# Target population
# ---------------------------------------------------------------------------

def load_targets():
    """Build the ordered target list: all nonabelian groups order 2..64,
    plus SURVIVE/CAP records from orders 96 and 128."""
    from sage.all import libgap

    targets = []

    # Part 1: all nonabelian groups at orders 2..64
    for order in range(2, 65):
        n_groups = int(libgap.NumberSmallGroups(order))
        for idx in range(1, n_groups + 1):
            G = libgap.SmallGroup(order, idx)
            if not bool(G.IsAbelian()):
                targets.append([order, idx])

    # Part 2: sieve survivors at orders 96 and 128
    for order in [96, 128]:
        path = CHECKPOINT_DIR / ("order_%d.jsonl" % order)
        if not path.exists():
            continue
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                if rec.get("type"):
                    continue
                action = rec.get("action", "")
                if action == "SURVIVE" or "CAP" in action:
                    gid = rec["id"]
                    targets.append([int(gid[0]), int(gid[1])])

    # Sort deterministically by (order, idx)
    targets.sort()
    return targets


def load_done_ids(out_file):
    """Load ids already processed from all shard files (resume)."""
    done = set()
    parent = out_file.parent
    base = "lemma-sweep-results"
    for path in sorted(parent.glob(base + "*.jsonl")):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    gid = rec.get("group_id")
                    if gid:
                        done.add(tuple(gid))
                except (json.JSONDecodeError, TypeError):
                    continue
    return done


# ---------------------------------------------------------------------------
# Lemma M probe (from pf3-probes/lemmaM2.sage, refactored as function)
# ---------------------------------------------------------------------------

def probe_lemma_m(order, idx):
    """Run the Lemma M check for SmallGroup(order, idx).
    Returns dict with results. A violation dict has n_violations > 0."""
    from sage.all import libgap

    G = libgap.SmallGroup(order, idx)
    G = libgap.Image(libgap.IsomorphismPermGroup(G))
    e1 = libgap.One(G)
    nG = int(libgap.Size(G))

    subs = []
    for c in libgap.ConjugacyClassesSubgroups(G):
        for H in libgap.AsList(c):
            subs.append(H)
    n = len(subs)
    sizes = [int(libgap.Size(H)) for H in subs]
    elts = [list(libgap.Elements(H)) for H in subs]
    eltstr = [set(str(x) for x in E) for E in elts]

    # beta_0
    def is_tpp(iS, iT, iU):
        Us = eltstr[iU]
        for x in elts[iS]:
            for y in elts[iT]:
                if str((x * y) ** -1) in Us and not (x == e1 and y == e1):
                    return False
        return True

    beta0 = 0
    for iS in range(n):
        for iT in range(n):
            if sizes[iS] * sizes[iT] > nG:
                continue
            for iU in range(n):
                p = sizes[iS] * sizes[iT] * sizes[iU]
                if p <= beta0:
                    continue
                if is_tpp(iS, iT, iU):
                    beta0 = p

    # Abelianization data
    abdata = []
    for i, H in enumerate(subs):
        D = libgap.DerivedSubgroup(H)
        q = libgap.NaturalHomomorphismByNormalSubgroup(H, D)
        F = libgap.Image(q)
        libgap.IsAbelian(F)
        invs = tuple(int(v) for v in libgap.AbelianInvariants(F))
        vec = {}
        if len(invs) == 0:
            for x in elts[i]:
                vec[str(x)] = ()
        else:
            for x in elts[i]:
                img = libgap.Image(q, x)
                ex = libgap.IndependentGeneratorExponents(F, img)
                vec[str(x)] = tuple(int(t) for t in ex)
        abdata.append({"dsize": int(libgap.Size(D)), "invs": invs, "vec": vec})

    # Lattice cache (local to this call)
    lat_cache = {}

    def lattice(invs):
        if invs in lat_cache:
            return lat_cache[invs]
        if len(invs) == 0:
            lat_cache[invs] = (None, [], [(1, frozenset(["<identity>"]))])
            return lat_cache[invs]
        A = libgap.AbelianGroup(list(invs))
        gens = list(libgap.GeneratorsOfGroup(A))
        out = []
        for c in libgap.ConjugacyClassesSubgroups(A):
            Sg = libgap.Representative(c)
            out.append((int(libgap.Size(Sg)),
                        frozenset(str(x) for x in libgap.Elements(Sg))))
        lat_cache[invs] = (A, gens, out)
        return lat_cache[invs]

    def to_elt_str(gens, A, v):
        if A is None:
            return "<identity>"
        g = libgap.One(A)
        for gen, e in zip(gens, v):
            if e:
                g = g * gen ** int(e)
        return str(g)

    viol = []
    checked = 0
    skipped_dead = 0
    for iS in range(n):
        dS = abdata[iS]
        for iT in range(n):
            dT = abdata[iT]
            for iU in range(n):
                if sizes[iS] * sizes[iT] * sizes[iU] <= beta0:
                    continue
                dU = abdata[iU]
                dprod = dS["dsize"] * dT["dsize"] * dU["dsize"]
                invs = dS["invs"] + dT["invs"] + dU["invs"]
                A, gens, lat = lattice(invs)
                Us = eltstr[iU]
                nbar = set()
                dead = False
                for x in elts[iS]:
                    sv = dS["vec"][str(x)]
                    for y in elts[iT]:
                        z = (x * y) ** -1
                        kz = str(z)
                        if kz in Us:
                            if x == e1 and y == e1:
                                continue
                            v = sv + dT["vec"][str(y)] + dU["vec"][kz]
                            if all(t == 0 for t in v):
                                dead = True
                                break
                            nbar.add(to_elt_str(gens, A, v))
                    if dead:
                        break
                if dead:
                    skipped_dead += 1
                    continue
                checked += 1
                for (sz, els) in lat:
                    tot = sz * dprod
                    if tot <= beta0:
                        continue
                    if not (nbar & els):
                        viol.append({
                            "S": int(iS), "T": int(iT), "U": int(iU),
                            "sizes": [int(sizes[iS]), int(sizes[iT]), int(sizes[iU])],
                            "sigma_size": int(tot),
                        })

    return {
        "beta0": int(beta0),
        "n_subgroups": int(n),
        "checked": int(checked),
        "dead": int(skipped_dead),
        "n_violations": int(len(viol)),
        "violations": viol[:5],
    }


# ---------------------------------------------------------------------------
# Lemma D probe (from pf3-probes/lemmaD.sage, refactored as function)
# ---------------------------------------------------------------------------

def probe_lemma_d(order, idx):
    """Run the Lemma D check for SmallGroup(order, idx).
    Returns dict with results. A failure means Lemma D fails for that config."""
    from sage.all import libgap

    G = libgap.SmallGroup(order, idx)
    G = libgap.Image(libgap.IsomorphismPermGroup(G))
    e1 = libgap.One(G)
    nG = int(libgap.Size(G))

    subs = []
    for c in libgap.ConjugacyClassesSubgroups(G):
        for H in libgap.AsList(c):
            subs.append(H)
    n = len(subs)
    sizes = [int(libgap.Size(H)) for H in subs]
    elts = [list(libgap.Elements(H)) for H in subs]
    eltstr = [set(str(x) for x in E) for E in elts]
    subidx = {}
    for i in range(n):
        subidx[frozenset(eltstr[i])] = i
    subsubs = []
    for i, H in enumerate(subs):
        L = []
        for c in libgap.ConjugacyClassesSubgroups(H):
            for K in libgap.AsList(c):
                L.append(subidx[frozenset(str(x) for x in libgap.Elements(K))])
        L = sorted(set(L), key=lambda j: -sizes[j])
        subsubs.append(L)

    tpp_cache = {}

    def is_tpp(iS, iT, iU):
        Us = eltstr[iU]
        for x in elts[iS]:
            for y in elts[iT]:
                if str((x * y) ** -1) in Us and not (x == e1 and y == e1):
                    return False
        return True

    def is_tpp_c(iS, iT, iU):
        key = (iS, iT, iU)
        if key not in tpp_cache:
            tpp_cache[key] = is_tpp(iS, iT, iU)
        return tpp_cache[key]

    beta0 = 0
    for iS in range(n):
        for iT in range(n):
            if sizes[iS] * sizes[iT] > nG:
                continue
            for iU in range(n):
                p = sizes[iS] * sizes[iT] * sizes[iU]
                if p > beta0 and is_tpp_c(iS, iT, iU):
                    beta0 = p

    def max_inside(iS, iT, iU, need):
        best = 0
        for jS in subsubs[iS]:
            if sizes[jS] * sizes[iT] * sizes[iU] <= best:
                break
            for jT in subsubs[iT]:
                if sizes[jS] * sizes[jT] * sizes[iU] <= best:
                    break
                for jU in subsubs[iU]:
                    p = sizes[jS] * sizes[jT] * sizes[jU]
                    if p <= best:
                        break
                    if is_tpp_c(jS, jT, jU):
                        best = p
                        if best >= need:
                            return best
        return best

    abdata = []
    for i, H in enumerate(subs):
        D = libgap.DerivedSubgroup(H)
        q = libgap.NaturalHomomorphismByNormalSubgroup(H, D)
        F = libgap.Image(q)
        libgap.IsAbelian(F)
        invs = tuple(int(v) for v in libgap.AbelianInvariants(F))
        vec = {}
        if len(invs) == 0:
            for x in elts[i]:
                vec[str(x)] = ()
        else:
            for x in elts[i]:
                ex = libgap.IndependentGeneratorExponents(F, libgap.Image(q, x))
                vec[str(x)] = tuple(int(t) for t in ex)
        abdata.append({"dsize": int(libgap.Size(D)), "invs": invs, "vec": vec})

    lat_cache = {}

    def lattice(invs):
        if invs in lat_cache:
            return lat_cache[invs]
        if len(invs) == 0:
            lat_cache[invs] = (None, [], [(1, frozenset(["<identity>"]))])
            return lat_cache[invs]
        A = libgap.AbelianGroup(list(invs))
        gens = list(libgap.GeneratorsOfGroup(A))
        out = []
        for c in libgap.ConjugacyClassesSubgroups(A):
            Sg = libgap.Representative(c)
            out.append((int(libgap.Size(Sg)),
                        frozenset(str(x) for x in libgap.Elements(Sg))))
        lat_cache[invs] = (A, gens, out)
        return lat_cache[invs]

    def to_elt_str(gens, A, v):
        if A is None:
            return "<identity>"
        g = libgap.One(A)
        for gen, e in zip(gens, v):
            if e:
                g = g * gen ** int(e)
        return str(g)

    fails = []
    nch = 0
    for iS in range(n):
        dS = abdata[iS]
        for iT in range(n):
            dT = abdata[iT]
            for iU in range(n):
                dU = abdata[iU]
                dprod = dS["dsize"] * dT["dsize"] * dU["dsize"]
                invs = dS["invs"] + dT["invs"] + dU["invs"]
                A, gens, lat = lattice(invs)
                Us = eltstr[iU]
                nbar = set()
                dead = False
                for x in elts[iS]:
                    sv = dS["vec"][str(x)]
                    for y in elts[iT]:
                        z = (x * y) ** -1
                        kz = str(z)
                        if kz in Us:
                            if x == e1 and y == e1:
                                continue
                            v = sv + dT["vec"][str(y)] + dU["vec"][kz]
                            if all(t == 0 for t in v):
                                dead = True
                                break
                            nbar.add(to_elt_str(gens, A, v))
                    if dead:
                        break
                if dead:
                    continue
                maxsig = 0
                for (sz, els) in lat:
                    tot = sz * dprod
                    if tot > maxsig and not (nbar & els):
                        maxsig = tot
                if maxsig <= 1:
                    continue
                nch += 1
                wit = max_inside(iS, iT, iU, maxsig)
                if wit < maxsig:
                    fails.append({
                        "members": [int(sizes[iS]), int(sizes[iT]), int(sizes[iU])],
                        "max_eligible_sigma": int(maxsig),
                        "best_inside_witness": int(wit),
                    })

    return {
        "beta0": int(beta0),
        "n_checked": int(nch),
        "n_D_failures": int(len(fails)),
        "D_failures": fails[:5],
    }


# ---------------------------------------------------------------------------
# Main sweep driver
# ---------------------------------------------------------------------------

def main(argv):
    parser = argparse.ArgumentParser(
        description="Lemma M / Lemma D kill-test sweep (Pf3 conjecture)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print space stats and projected runtime, then exit")
    parser.add_argument("--shard", default=None, metavar="I/N",
                        help="Process the I-th of N deterministic slices (0-indexed)")
    parser.add_argument("--lemma-d", action="store_true",
                        help="Also run Lemma D probe (slower; default: Lemma M only)")
    parser.add_argument("--limit", type=int, default=0,
                        help="Stop after this many groups (0 = no limit)")
    args = parser.parse_args(argv)

    shard_i, shard_n = 0, 1
    if args.shard:
        shard_i, shard_n = (int(x) for x in args.shard.split("/"))
        if not (0 <= shard_i < shard_n):
            parser.error("--shard %s: need 0 <= I < N" % args.shard)
    tag = "[shard %d/%d] " % (shard_i, shard_n) if shard_n > 1 else ""
    out_file = (OUTPUT_FILE if shard_n == 1 else OUTPUT_FILE.with_name(
        "lemma-sweep-results.shard%dof%d.jsonl" % (shard_i, shard_n)))

    print("%sLoading target population..." % tag, flush=True)
    targets = load_targets()
    n_total = len(targets)

    # Round-robin striping (same as census.sage)
    targets = targets[shard_i::shard_n]
    print("%sTargets in this shard: %d of %d total" % (tag, len(targets), n_total),
          flush=True)

    if args.dry_run:
        print("\nSpace: %d nonabelian groups" % n_total)
        # Breakdown
        n_le64 = sum(1 for t in load_targets() if t[0] <= 64)
        n_96 = sum(1 for t in load_targets() if t[0] == 96)
        n_128 = sum(1 for t in load_targets() if t[0] == 128)
        print("  Orders 2..64: %d" % n_le64)
        print("  Order 96 survivors: %d" % n_96)
        print("  Order 128 survivors: %d" % n_128)
        # Runtime projection: ~3s average per group (dominanted by order-64/128)
        est_s = n_total * 3.0 / shard_n
        print("\nProjected runtime (Lemma M only): ~%.0f min on %d shard(s)"
              % (est_s / 60, shard_n))
        if args.lemma_d:
            print("  With --lemma-d: ~%.0f min (2-3x overhead)" % (est_s * 2.5 / 60))
        return

    done_ids = load_done_ids(out_file)
    remaining = [t for t in targets if tuple(t) not in done_ids]
    if args.limit:
        remaining = remaining[:args.limit]
    n_remaining = len(remaining)

    print("%sAlready done (all shard files): %d" % (tag, len(done_ids)), flush=True)
    print("%sRemaining in this shard: %d" % (tag, n_remaining), flush=True)

    if n_remaining == 0:
        print("%sNothing to do — shard complete." % tag, flush=True)
        return

    est_s = n_remaining * 3.0
    print("%sEstimated runtime: ~%.0f min (Lemma M)" % (tag, est_s / 60), flush=True)
    print("%sOutput: %s" % (tag, out_file), flush=True)
    print("%sMode: Lemma M%s" % (tag, " + Lemma D" if args.lemma_d else " only"),
          flush=True)
    print(flush=True)

    t_start = time.time()
    n_processed = 0
    n_violations = 0
    n_d_failures = 0

    with open(out_file, "a") as out:
        for i, gid in enumerate(remaining):
            order, idx = gid
            t_group = time.time()
            try:
                m_result = probe_lemma_m(order, idx)
                result = {
                    "group_id": [int(order), int(idx)],
                    "order": int(order),
                    "lemma_m": m_result,
                }

                if m_result["n_violations"] > 0:
                    n_violations += m_result["n_violations"]
                    result["VIOLATION"] = True
                    # SURFACE IMMEDIATELY
                    print("\n!!! VIOLATION at [%d,%d] !!!" % (order, idx), flush=True)
                    print("  %s" % json.dumps(m_result["violations"][:3]), flush=True)

                if args.lemma_d:
                    d_result = probe_lemma_d(order, idx)
                    result["lemma_d"] = d_result
                    if d_result["n_D_failures"] > 0:
                        n_d_failures += d_result["n_D_failures"]
                        result["D_FAILURE"] = True
                        print("\n!!! Lemma D failure at [%d,%d] !!!" % (order, idx),
                              flush=True)
                        print("  %s" % json.dumps(d_result["D_failures"][:3]),
                              flush=True)

                result["elapsed_s"] = float("%.2f" % (time.time() - t_group))
                out.write(json.dumps(result, separators=(",", ":")) + "\n")
                n_processed += 1

            except KeyboardInterrupt:
                print("\n%sInterrupted after %d groups." % (tag, n_processed),
                      flush=True)
                break
            except Exception as e:
                err_rec = {
                    "group_id": [int(order), int(idx)],
                    "order": int(order),
                    "error": str(e),
                }
                out.write(json.dumps(err_rec, separators=(",", ":")) + "\n")
                n_processed += 1
                print("  %sERROR on [%d,%d]: %s" % (tag, order, idx, e), flush=True)

            # Progress every 20 groups
            if (i + 1) % 20 == 0:
                elapsed = time.time() - t_start
                rate = (i + 1) / elapsed
                eta = (n_remaining - i - 1) / rate
                print("  %s[%d/%d] %.2f groups/s, ETA %.0fmin, "
                      "violations=%d, D_fails=%d"
                      % (tag, i + 1, n_remaining, rate, eta / 60,
                         n_violations, n_d_failures),
                      flush=True)

            # Flush after each group (critical: violations must persist)
            out.flush()

    elapsed = time.time() - t_start
    print("\n%sDone: %d processed, %.1f min elapsed." % (tag, n_processed, elapsed / 60),
          flush=True)
    print("%sLemma M violations: %d" % (tag, n_violations), flush=True)
    if args.lemma_d:
        print("%sLemma D failures: %d" % (tag, n_d_failures), flush=True)
    if n_violations > 0:
        print("\n*** CONJECTURE KILLED — violations found. See output. ***", flush=True)
    else:
        print("%sNo violations — conjecture survives this sweep." % tag, flush=True)


main([a for a in sys.argv[1:] if a != "--"])
