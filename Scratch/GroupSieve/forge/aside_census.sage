# aside_census.sage — A-side census: max eligible |Sigma| over
# covering configurations in a target group G with kernel B = C_p.
#
# Campaign: Pl15 (abelian direct factor conjecture — large-group probing)
# Spec: .tasks/f5exp/docs/Pl15-aside-spec.md
#
# SCOPE CAVEAT (binding, from spec section 2.2):
#   This census measures A_{C_p} := max eligible |Sigma| over B = C_p
#   configurations only.  Composite B is excluded BY CAMPAIGN SCOPE,
#   not by theorem.  A zero-margin result (A_{C_p} = beta_0(G)) certifies
#   A_{C_p} = beta_0(G) for p in {2,3}, NOT max over all abelian B.
#   The full-B certification requires a separate composite-B census or
#   a correct general lemma, neither of which exists today.
#
# PRUNING ASSUMPTIONS (numbered per spec section 1.1, all EXACT):
#
#   1. Junction concentration — case-alpha reduction (Pf3 3.iii).
#      For B = C_p: at most one pairwise intersection of members is
#      nontrivial, and if one is, EVERY nontrivial collision is of the
#      junction form (1, w, w^{-1}).  Since delta_TU is injective on
#      W ~ C_p, one member's kernel shrink is an honest TPP triple of
#      size |Pi|/p = |Sigma|.  DONE.  So Lemma M for B = C_p reduces
#      to CASE ALPHA: S' ∩ T' = S' ∩ U' = T' ∩ U' = 1.
#      Semantics preserved: EXACT.
#
#   2. Pairwise-trivial junction subgroups (Pf3 3.ii).
#      For B = C_p, subsumed by Assumption 1 (no separate pruning step).
#
#   3. Covering requirement (Pf3 section 2, Lemma P).
#      Lemma P reduces Lemma M to covering configurations.  For
#      B = C_p, case alpha: k := |{X : f_X != 0}| >= 2.
#      Semantics preserved: EXACT.
#
#   4. Lambda-shrink for unblocked members (Pf3 section 3).
#      If some member X has a character lambda with lambda(x_c) != 0
#      for every nontrivial collision c, then (ker lambda in slot X,
#      other two full) is honest of size |Sigma|.  The census reports
#      only fully-blocked configs (all three members blocked).
#      Semantics preserved: EXACT.
#
# Usage:
#   sage aside_census.sage -- --target "AlternatingGroup(5)" --threshold 108 --primes 2,3
#   sage aside_census.sage -- --target "SymmetricGroup(4)" --primes 2 --mode census
#   sage aside_census.sage -- --target "AlternatingGroup(5)" --threshold 108 --mode hunt
#
# Output: JSONL to stdout (one record per eligible fully-blocked config,
#         plus a summary record per (target, p)).

import json
import os
import sys
import time
import itertools
import argparse

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from forgelib import sanitize, dump_jsonl

from sage.all import libgap, GF, matrix


def jdumps(obj):
    """JSON-serialize with Sage type sanitization."""
    return dump_jsonl(obj)


# ---------------------------------------------------------------------------
# Argument parsing (strip Sage's '--' from argv)
# ---------------------------------------------------------------------------

def parse_args():
    argv = [a for a in sys.argv[1:] if a != "--"]
    parser = argparse.ArgumentParser(description="A-side census")
    parser.add_argument("--target", required=True,
                        help="GAP constructor string, e.g. AlternatingGroup(5)")
    parser.add_argument("--threshold", type=int, default=0,
                        help="beta_0(G); configs with |Sigma| <= threshold are skipped in shape filter")
    parser.add_argument("--primes", default="2,3",
                        help="Comma-separated primes for B = C_p")
    parser.add_argument("--mode", choices=["census", "hunt"], default="census",
                        help="census = exhaustive; hunt = stop at first |Sigma| > threshold")
    parser.add_argument("--raw", action="store_true",
                        help="Raw mode: skip pruning assumptions 1,3 (for calibration vs blockedscan)")
    return parser.parse_args(argv)


# ---------------------------------------------------------------------------
# Group construction
# ---------------------------------------------------------------------------

def make_group(target_str):
    """Construct a GAP group from a string like 'AlternatingGroup(5)'."""
    return libgap.eval(target_str)


# ---------------------------------------------------------------------------
# Character data for a subgroup (mod-p abelianization)
# ---------------------------------------------------------------------------

def compute_char_data(H, p):
    """Compute F_p character data for H.

    Returns dict with:
      "dim":     dimension of H^ab tensor F_p
      "vecs":    list of F_p-vectors, one per element of H (same order as Elements(H))
      "elems":   list of GAP elements of H
      "kernels": list of frozensets of element indices (one per distinct nontrivial kernel)
    """
    D = libgap.DerivedSubgroup(H)
    q = libgap.NaturalHomomorphismByNormalSubgroup(H, D)
    F = libgap.Image(q)
    libgap.IsAbelian(F)
    invs = [int(v) for v in libgap.AbelianInvariants(F)]
    slots = [j for j, d in enumerate(invs) if d % p == 0]
    dim = len(slots)
    elems = list(libgap.Elements(H))
    vecs = []
    for x in elems:
        if not invs:
            vecs.append(())
            continue
        img = libgap.Image(q, x)
        ex = [int(t) for t in libgap.IndependentGeneratorExponents(F, img)]
        vecs.append(tuple(ex[j] % p for j in slots))

    # Enumerate all distinct nontrivial kernels
    kernels = set()
    for lam in itertools.product(range(p), repeat=dim):
        if not any(lam):
            continue
        ker = frozenset(i for i, v in enumerate(vecs)
                        if sum(a * b for a, b in zip(lam, v)) % p == 0)
        kernels.add(ker)
    kernels = list(kernels)
    return {"dim": dim, "vecs": vecs, "elems": elems, "kernels": kernels}


# ---------------------------------------------------------------------------
# Blockedness check (Assumption 4)
# ---------------------------------------------------------------------------

def consistent_ones(vs, p):
    """Does there exist lambda in F_p^dim with <lambda, v> = 1 (mod p)
    for all v in vs?  Returns True iff such lambda exists (member UNBLOCKED).
    Rouché-Capelli: solvable iff rank(A) == rank(A|1)."""
    if not vs:
        return True
    d = len(vs[0])
    if d == 0:
        return False
    Fp = GF(p)
    A = matrix(Fp, vs)
    Ab = A.augment(matrix(Fp, [[1]] * len(vs)))
    return A.rank() == Ab.rank()


def member_blocked(vecs, coll_indices, p):
    """Is member X blocked?  Blocked iff no lambda with lambda(x_c)=1
    for every collision c."""
    vs = [vecs[i] for i in coll_indices]
    return not consistent_ones(vs, p)


# ---------------------------------------------------------------------------
# Raw exhaustive census (blockedscan-compatible, for S_4 calibration)
# ---------------------------------------------------------------------------

def run_raw_census(G, target_name, p):
    """Exhaustive enumeration matching blockedscan.sage: all ordered triples
    of subgroups (sizes >= 2), all character triples with k >= 1.
    Returns (n_eligible, n_blocked)."""
    t0 = time.time()
    e1 = libgap.One(G)

    # Collect all subgroups
    subs = []
    for c in libgap.ConjugacyClassesSubgroups(G):
        for H in libgap.AsList(c):
            subs.append(H)
    n = len(subs)
    sizes = [int(libgap.Size(H)) for H in subs]
    print("RAW census: %d subgroups, p=%d" % (n, p), flush=True)

    # Precompute element lists and char data
    elts = [list(libgap.Elements(H)) for H in subs]
    keys = [{str(x): i for i, x in enumerate(E)} for E in elts]
    cds = [compute_char_data(H, p) for H in subs]

    n_eligible = 0
    n_blocked = 0
    last_progress = time.time()

    for iS in range(n):
        if sizes[iS] < 2:
            continue
        dS = cds[iS]
        for iT in range(n):
            if sizes[iT] < 2:
                continue
            dT = cds[iT]
            for iU in range(n):
                if sizes[iU] < 2:
                    continue
                dU = cds[iU]

                # Collision list
                colls = []
                for a, x in enumerate(elts[iS]):
                    for b, y in enumerate(elts[iT]):
                        z = (x * y) ** (-1)
                        kz = keys[iU].get(str(z))
                        if kz is not None:
                            if x == e1 and y == e1 and z == e1:
                                continue
                            colls.append((a, b, kz))
                if not colls:
                    continue

                # Character triple enumeration (k >= 1: not all zero)
                for lamS in itertools.product(range(p), repeat=dS["dim"]):
                    for lamT in itertools.product(range(p), repeat=dT["dim"]):
                        for lamU in itertools.product(range(p), repeat=dU["dim"]):
                            if not any(lamS) and not any(lamT) and not any(lamU):
                                continue
                            ok = True
                            for (a, b, c) in colls:
                                psi = (sum(x * y for x, y in zip(lamS, dS["vecs"][a]))
                                       + sum(x * y for x, y in zip(lamT, dT["vecs"][b]))
                                       + sum(x * y for x, y in zip(lamU, dU["vecs"][c]))) % p
                                if psi == 0:
                                    ok = False
                                    break
                            if not ok:
                                continue
                            n_eligible += 1
                            bS = member_blocked(dS["vecs"], [a for (a, _, _) in colls], p)
                            if not bS:
                                continue
                            bT = member_blocked(dT["vecs"], [b for (_, b, _) in colls], p)
                            if not bT:
                                continue
                            bU = member_blocked(dU["vecs"], [c for (_, _, c) in colls], p)
                            if not bU:
                                continue
                            n_blocked += 1

                now = time.time()
                if now - last_progress >= 15:
                    print("RAW progress: iS=%d/%d eligible=%d blocked=%d elapsed=%.1fs"
                          % (iS, n, n_eligible, n_blocked, now - t0), flush=True)
                    last_progress = now

    elapsed = time.time() - t0
    result = {"type": "raw_summary", "target": target_name, "p": int(p),
              "n_subs": int(n), "eligible": int(n_eligible), "blocked": int(n_blocked),
              "elapsed_seconds": float(elapsed)}
    print(jdumps(result), flush=True)
    return n_eligible, n_blocked


# ---------------------------------------------------------------------------
# Subgroup lattice
# ---------------------------------------------------------------------------

def build_lattice(G):
    """Build subgroup conjugacy class list with copies."""
    nG = int(libgap.Size(G))
    classes = []
    for c in libgap.ConjugacyClassesSubgroups(G):
        rep = libgap.Representative(c)
        order = int(libgap.Size(rep))
        N = libgap.Normalizer(G, rep)
        copies = [libgap.ConjugateSubgroup(rep, rc)
                  for rc in libgap.RightTransversal(G, N)]
        sd = str(libgap.StructureDescription(rep))
        classes.append({
            "rep": rep, "copies": copies, "order": order,
            "sd": sd, "n_copies": len(copies),
        })
    return classes, nG


def twistable_indices(classes, p):
    """Indices of classes admitting a C_p quotient."""
    result = []
    for i, cl in enumerate(classes):
        if cl["order"] < p or cl["order"] % p != 0:
            continue
        n_chars = 0
        for K in libgap.NormalSubgroups(cl["rep"]):
            if int(libgap.Size(K)) * p == cl["order"]:
                n_chars += 1
        if n_chars > 0:
            cl["n_p_chars"] = n_chars
            result.append(i)
    return result


# ---------------------------------------------------------------------------
# Forced-intersection cache
# ---------------------------------------------------------------------------

def build_fi_cache(classes, nG):
    """For each pair of class indices (i,j), i<=j, check whether any
    pair of copies has trivial intersection."""
    cache = {}
    t0 = time.time()
    for i in range(len(classes)):
        for j in range(i, len(classes)):
            if classes[i]["order"] * classes[j]["order"] > nG:
                cache[(i, j)] = False
                continue
            found = False
            for Hi in classes[i]["copies"]:
                for Hj in classes[j]["copies"]:
                    if int(libgap.Size(libgap.Intersection(Hi, Hj))) == 1:
                        found = True
                        break
                if found:
                    break
            cache[(i, j)] = found
    print("FORCED-INTERSECTION cache: %d pairs in %.1fs" % (len(cache), time.time() - t0),
          flush=True)
    return cache


def fi_possible(cache, i, j):
    key = (min(i, j), max(i, j))
    return cache.get(key, False)


# ---------------------------------------------------------------------------
# Shape enumeration (spec 1.2 step 1)
# ---------------------------------------------------------------------------

def enumerate_shapes(classes, twist_idx, p, threshold, nG):
    """Enumerate (iA, iB, iC, k, sigma) shapes above threshold.
    k=3: all three in twist_idx.
    k=2: exactly two in twist_idx (the third is any class, untwisted)."""
    shapes = []
    twist_set = set(twist_idx)
    n_classes = len(classes)

    # Assumption 1: pairwise product bound s*t <= |G| (case alpha)
    # Assumption 3: k >= 2

    # k=3: all twisted
    for a in range(len(twist_idx)):
        iA = twist_idx[a]
        sA = classes[iA]["order"]
        for b in range(a, len(twist_idx)):
            iB = twist_idx[b]
            sB = classes[iB]["order"]
            if sA * sB > nG:
                continue
            for c in range(b, len(twist_idx)):
                iC = twist_idx[c]
                sC = classes[iC]["order"]
                if sA * sC > nG or sB * sC > nG:
                    continue
                sigma = sA * sB * sC // p
                if sigma >= threshold:
                    shapes.append((iA, iB, iC, 3, sigma))

    # k=2: two twisted (iA, iB), one untwisted (iC = any class)
    # The untwisted member has f=0.
    for a in range(len(twist_idx)):
        iA = twist_idx[a]
        sA = classes[iA]["order"]
        for b in range(a, len(twist_idx)):
            iB = twist_idx[b]
            sB = classes[iB]["order"]
            if sA * sB > nG:
                continue
            for iC in range(n_classes):
                sC = classes[iC]["order"]
                if sA * sC > nG or sB * sC > nG:
                    continue
                sigma = sA * sB * sC // p
                if sigma <= threshold:
                    continue
                shapes.append((iA, iB, iC, 2, sigma))

    # Deduplicate: a k=2 shape (iA, iB, iC) where iC is twistable
    # is distinct from a k=3 shape (iA, iB, iC) because k=2 has f_C=0.
    # Both are valid and must be checked.

    # Sort by sigma descending (for hunt mode)
    shapes.sort(key=lambda s: -s[4])
    return shapes


# ---------------------------------------------------------------------------
# Census pipeline per (target, p)
# ---------------------------------------------------------------------------

def run_pipeline(G, classes, fi_cache, nG, target_name, p, threshold, mode):
    """Run the census pipeline for one prime."""
    tp_start = time.time()
    e1 = libgap.One(G)

    twist_idx = twistable_indices(classes, p)
    print("Twistable (p=%d): %s"
          % (p, [(i, classes[i]["order"], classes[i]["sd"],
                  classes[i].get("n_p_chars", 0)) for i in twist_idx]),
          flush=True)

    if len(twist_idx) < 2:
        print("Fewer than 2 twistable classes for p=%d; skip." % p, flush=True)
        return {"type": "summary", "target": target_name, "p": p,
                "max_sigma": 0, "configs_eligible": 0, "configs_blocked": 0,
                "semantics": "exact" if mode == "census" else "lower_bound",
                "beta0": threshold, "margin": -threshold if threshold else None,
                "elapsed_seconds": time.time() - tp_start}

    # Shape enumeration
    # Assumption 1: case-alpha pairwise bound s*t <= |G|
    # Assumption 3: k >= 2
    shapes = enumerate_shapes(classes, twist_idx, p, threshold, nG)
    print("Shapes above threshold: %d" % len(shapes), flush=True)

    max_sigma = 0       # max |Sigma| among fully-blocked eligible configs
    max_elig_sigma = 0  # max |Sigma| among all eligible configs (diagnostic)
    total_frames = 0
    total_eligible = 0
    total_blocked = 0
    shapes_done = 0
    last_progress = time.time()
    kill_hit = None

    for si, (iA, iB, iC, k, sigma) in enumerate(shapes):
        shape_t0 = time.time()

        # Forced-intersection filter (Assumption 1)
        if not fi_possible(fi_cache, iA, iB):
            shapes_done += 1
            continue
        if not fi_possible(fi_cache, iA, iC):
            shapes_done += 1
            continue
        if not fi_possible(fi_cache, iB, iC):
            shapes_done += 1
            continue

        # Determine twisted slots
        if k == 3:
            twisted = ('S', 'T', 'U')
        else:
            twisted = ('S', 'T')  # iC is untwisted

        # Frame enumeration: fix one copy of S (WLOG), iterate T, U copies
        # Assumption 1: all pairwise intersections trivial
        S0 = classes[iA]["copies"][0]
        S0_elems = list(libgap.Elements(S0))
        S0_set = set(str(x) for x in S0_elems)
        S0_eidx = {str(x): i for i, x in enumerate(S0_elems)}

        shape_frames = 0
        shape_eligible = 0
        shape_blocked = 0

        for T in classes[iB]["copies"]:
            T_elems = list(libgap.Elements(T))
            T_set = set(str(x) for x in T_elems)
            # Assumption 1: S' ∩ T' = 1
            if len(S0_set & T_set) > 1:
                continue
            T_eidx = {str(x): i for i, x in enumerate(T_elems)}

            for U in classes[iC]["copies"]:
                U_elems = list(libgap.Elements(U))
                U_set = set(str(x) for x in U_elems)
                # Assumption 1: S' ∩ U' = 1, T' ∩ U' = 1
                if len(S0_set & U_set) > 1:
                    continue
                if len(T_set & U_set) > 1:
                    continue

                # Covering check: <S', T', U'> = G
                gen = libgap.Subgroup(G,
                    list(libgap.GeneratorsOfGroup(S0)) +
                    list(libgap.GeneratorsOfGroup(T)) +
                    list(libgap.GeneratorsOfGroup(U)))
                if int(libgap.Size(gen)) != nG:
                    continue

                shape_frames += 1
                total_frames += 1

                # Compute char data for these specific copies
                cd_S = compute_char_data(S0, p)
                cd_T = compute_char_data(T, p)
                cd_U = compute_char_data(U, p)

                # Collision enumeration: xyz=1, x in S', y in T', z in U'
                U_eidx = {str(x): i for i, x in enumerate(U_elems)}
                colls = []
                for iT_idx, y in enumerate(T_elems):
                    for iU_idx, z in enumerate(U_elems):
                        x = (y * z) ** (-1)
                        iS_idx = S0_eidx.get(str(x))
                        if iS_idx is not None:
                            if x == e1 and y == e1 and z == e1:
                                continue
                            colls.append((iS_idx, iT_idx, iU_idx))

                if not colls:
                    continue

                # Character enumeration and eligibility check
                # For twisted slots: enumerate nontrivial lambda in F_p^dim
                # For untwisted slot: lambda = 0 (f=0)
                def get_lambdas(cd, is_twisted):
                    if not is_twisted:
                        return [tuple(0 for _ in range(cd["dim"]))]
                    result = []
                    for lam in itertools.product(range(p), repeat=cd["dim"]):
                        if any(lam):
                            result.append(lam)
                    return result

                lams_S = get_lambdas(cd_S, 'S' in twisted)
                lams_T = get_lambdas(cd_T, 'T' in twisted)
                lams_U = get_lambdas(cd_U, 'U' in twisted)

                for lamS in lams_S:
                    for lamT in lams_T:
                        for lamU in lams_U:
                            # Eligibility: psi != 0 for all collisions
                            ok = True
                            for (a, b, c) in colls:
                                fS_val = sum(x * y for x, y in zip(lamS, cd_S["vecs"][a])) % p
                                fT_val = sum(x * y for x, y in zip(lamT, cd_T["vecs"][b])) % p
                                fU_val = sum(x * y for x, y in zip(lamU, cd_U["vecs"][c])) % p
                                psi = (fS_val + fT_val + fU_val) % p
                                if psi == 0:
                                    ok = False
                                    break
                            if not ok:
                                continue

                            shape_eligible += 1
                            total_eligible += 1
                            if sigma > max_elig_sigma:
                                max_elig_sigma = sigma

                            # Blockedness check (Assumption 4)
                            bS = member_blocked(cd_S["vecs"],
                                                [a for (a, _, _) in colls], p)
                            bT = member_blocked(cd_T["vecs"],
                                                [b for (_, b, _) in colls], p)
                            bU = member_blocked(cd_U["vecs"],
                                                [c for (_, _, c) in colls], p)

                            if bS and bT and bU:
                                shape_blocked += 1
                                total_blocked += 1
                                if sigma > max_sigma:
                                    max_sigma = sigma

                                rec = {
                                    "type": "config",
                                    "target": target_name, "p": p,
                                    "shape": [classes[iA]["order"],
                                              classes[iB]["order"],
                                              classes[iC]["order"]],
                                    "shape_sd": [classes[iA]["sd"],
                                                 classes[iB]["sd"],
                                                 classes[iC]["sd"]],
                                    "sigma": sigma, "k": k,
                                    "ncolls": len(colls),
                                    "blocked": [bS, bT, bU],
                                    "S_gens": str(list(libgap.GeneratorsOfGroup(S0))),
                                    "T_gens": str(list(libgap.GeneratorsOfGroup(T))),
                                    "U_gens": str(list(libgap.GeneratorsOfGroup(U))),
                                    "semantics": "exact" if mode == "census" else "lower_bound",
                                }
                                print(jdumps(rec), flush=True)

                                if threshold > 0 and sigma > threshold:
                                    print("*** KILL CANDIDATE: |Sigma|=%d > beta_0=%d ***"
                                          % (sigma, threshold), flush=True)
                                    kill_hit = rec
                                    if mode == "hunt":
                                        break
                            if kill_hit and mode == "hunt":
                                break
                        if kill_hit and mode == "hunt":
                            break
                    if kill_hit and mode == "hunt":
                        break
                if kill_hit and mode == "hunt":
                    break
            if kill_hit and mode == "hunt":
                break

        shapes_done += 1
        now = time.time()
        if now - last_progress >= 5 or shape_eligible > 0 or kill_hit:
            print("SHAPE (%d,%d,%d) p=%d k=%d |Sigma|=%d: frames=%d eligible=%d blocked=%d max_sigma=%d elapsed=%.1fs [%d/%d shapes]"
                  % (classes[iA]["order"], classes[iB]["order"], classes[iC]["order"],
                     p, k, sigma, shape_frames, shape_eligible, shape_blocked,
                     max_sigma, now - shape_t0, si + 1, len(shapes)),
                  flush=True)
            last_progress = now

        if kill_hit and mode == "hunt":
            break

    tp_elapsed = time.time() - tp_start
    margin = max_sigma - threshold if threshold > 0 else None
    summary = {
        "type": "summary", "target": target_name, "p": p,
        "max_sigma_blocked": max_sigma,
        "max_sigma_eligible": max_elig_sigma,
        "shapes_checked": shapes_done,
        "shapes_total": len(shapes),
        "frames_checked": total_frames,
        "configs_eligible": total_eligible,
        "configs_blocked": total_blocked,
        "semantics": ("exact" if mode == "census" and not kill_hit
                      else "lower_bound"),
        "beta0": threshold,
        "margin": margin,
        "elapsed_seconds": tp_elapsed,
    }
    if kill_hit:
        summary["kill"] = True
    print(jdumps(summary), flush=True)
    print("\n--- p=%d DONE: max_blocked_sigma=%d max_elig_sigma=%d eligible=%d blocked=%d margin=%s elapsed=%.1fs ---"
          % (p, max_sigma, max_elig_sigma, total_eligible, total_blocked, margin, tp_elapsed),
          flush=True)
    return summary


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    args = parse_args()
    primes = [int(x) for x in args.primes.split(",")]
    G = make_group(args.target)
    nG = int(libgap.Size(G))
    target_name = args.target

    print("TARGET %s |G|=%d threshold=%d mode=%s primes=%s raw=%s"
          % (target_name, nG, args.threshold, args.mode, primes, args.raw),
          flush=True)

    if args.raw:
        for p in primes:
            run_raw_census(G, target_name, p)
        return

    # Build lattice and forced-intersection cache
    print("Building subgroup lattice...", flush=True)
    classes, nG = build_lattice(G)
    n_subs = sum(cl["n_copies"] for cl in classes)
    print("Lattice: %d classes, %d subgroups" % (len(classes), n_subs), flush=True)

    fi_cache = build_fi_cache(classes, nG)

    results = []
    for p in primes:
        print("\n=== PRIME p=%d ===" % p, flush=True)
        r = run_pipeline(G, classes, fi_cache, nG, target_name, p,
                         args.threshold, args.mode)
        results.append(r)

    total_elapsed = sum(r.get("elapsed_seconds", 0) for r in results)
    print("\nTOTAL elapsed: %.1fs" % total_elapsed, flush=True)


main()
