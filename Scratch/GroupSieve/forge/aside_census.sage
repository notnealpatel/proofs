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
import sys
import time
import itertools
import argparse

from sage.all import libgap, GF, matrix


# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

def parse_args():
    parser = argparse.ArgumentParser(description="A-side census")
    parser.add_argument("--target", required=True,
                        help="GAP constructor string, e.g. AlternatingGroup(5)")
    parser.add_argument("--threshold", type=int, default=0,
                        help="beta_0(G); configs with |Sigma| <= threshold are skipped")
    parser.add_argument("--primes", default="2,3",
                        help="Comma-separated primes for B = C_p")
    parser.add_argument("--mode", choices=["census", "hunt"], default="census",
                        help="census = exhaustive; hunt = stop at first |Sigma| > threshold")
    return parser.parse_args()


# ---------------------------------------------------------------------------
# Group construction
# ---------------------------------------------------------------------------

def make_group(target_str):
    """Construct a GAP group from a string like 'AlternatingGroup(5)'."""
    G = libgap.eval(target_str)
    return G


# ---------------------------------------------------------------------------
# Subgroup lattice and metadata
# ---------------------------------------------------------------------------

def build_lattice(G):
    """Return list of (class_rep, copies_list, order, sd, n_idx_p_subs)
    for each conjugacy class of subgroups."""
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
            "rep": rep,
            "copies": copies,
            "order": order,
            "sd": sd,
            "n_copies": len(copies),
        })
    return classes, nG


def twistable_classes(classes, p):
    """Return indices of classes whose members admit a C_p quotient
    (have a normal subgroup of index p).  Also annotate each class
    with the number of distinct C_p characters."""
    result = []
    for i, cl in enumerate(classes):
        H = cl["rep"]
        order = cl["order"]
        if order < p:
            continue
        if order % p != 0:
            continue
        # Count normal subgroups of index p
        n_chars = 0
        for K in libgap.NormalSubgroups(H):
            if int(libgap.Size(K)) * p == order:
                n_chars += 1
        if n_chars > 0:
            cl["n_p_chars"] = n_chars
            result.append(i)
    return result


def all_class_sizes(classes):
    """Return sorted list of unique orders."""
    return sorted(set(cl["order"] for cl in classes))


# ---------------------------------------------------------------------------
# Character data for a subgroup (mod-p abelianization)
# ---------------------------------------------------------------------------

def char_data_p2(H):
    """Compute F_2 character data for H (p=2).
    Returns: {"dim": d, "vecs": [tuple_per_element], "kernels": [frozenset_of_element_indices]}
    where element indices are positions in list(Elements(H))."""
    D = libgap.DerivedSubgroup(H)
    q = libgap.NaturalHomomorphismByNormalSubgroup(H, D)
    F = libgap.Image(q)
    libgap.IsAbelian(F)
    invs = [int(v) for v in libgap.AbelianInvariants(F)]
    slots = [j for j, d in enumerate(invs) if d % 2 == 0]
    dim = len(slots)
    elems = list(libgap.Elements(H))
    vecs = []
    for x in elems:
        if len(invs) == 0:
            vecs.append(())
            continue
        img = libgap.Image(q, x)
        ex = [int(t) for t in libgap.IndependentGeneratorExponents(F, img)]
        vecs.append(tuple(ex[j] % 2 for j in slots))
    # Enumerate all nontrivial characters (nonzero lambda in F_2^dim)
    kernels = []
    for lam in itertools.product([0, 1], repeat=dim):
        if not any(lam):
            continue
        ker = frozenset(i for i, v in enumerate(vecs)
                        if sum(a * b for a, b in zip(lam, v)) % 2 == 0)
        kernels.append(ker)
    # Deduplicate kernels
    kernels = list(set(kernels))
    return {"dim": dim, "vecs": vecs, "elems": elems, "kernels": kernels}


def char_data_p3(H):
    """Compute F_3 character data for H (p=3).
    Returns same schema as char_data_p2 but for p=3 characters."""
    D = libgap.DerivedSubgroup(H)
    q = libgap.NaturalHomomorphismByNormalSubgroup(H, D)
    F = libgap.Image(q)
    libgap.IsAbelian(F)
    invs = [int(v) for v in libgap.AbelianInvariants(F)]
    slots = [j for j, d in enumerate(invs) if d % 3 == 0]
    dim = len(slots)
    elems = list(libgap.Elements(H))
    vecs = []
    for x in elems:
        if len(invs) == 0:
            vecs.append(())
            continue
        img = libgap.Image(q, x)
        ex = [int(t) for t in libgap.IndependentGeneratorExponents(F, img)]
        vecs.append(tuple(ex[j] % 3 for j in slots))
    # Enumerate all nontrivial characters (nonzero lambda in F_3^dim)
    kernels = []
    for lam in itertools.product(range(3), repeat=dim):
        if not any(lam):
            continue
        ker = frozenset(i for i, v in enumerate(vecs)
                        if sum(a * b for a, b in zip(lam, v)) % 3 == 0)
        kernels.append(ker)
    kernels = list(set(kernels))
    return {"dim": dim, "vecs": vecs, "elems": elems, "kernels": kernels}


def char_data(H, p):
    if p == 2:
        return char_data_p2(H)
    elif p == 3:
        return char_data_p3(H)
    else:
        raise ValueError("unsupported prime %d" % p)


# ---------------------------------------------------------------------------
# Blockedness check (Assumption 4)
# ---------------------------------------------------------------------------

def consistent_ones_p(vs, p):
    """Check if there exists lambda in F_p^dim with <lambda, v> = 1 (mod p)
    for all v in vs.  Returns True if such lambda exists (member is unblocked).
    For p=2: rank(A) == rank(A|1) over GF(2).
    For p=3: rank(A) == rank(A|1) over GF(3)."""
    if not vs:
        return True  # no collisions => trivially unblocked
    d = len(vs[0])
    if d == 0:
        return False  # only zero character; can never satisfy <lam,v>=1
    Fp = GF(p)
    A = matrix(Fp, vs)
    ones = matrix(Fp, [[1]] * len(vs))
    Ab = A.augment(ones)
    return A.rank() == Ab.rank()


def is_blocked(member_vecs, collision_component_indices, p):
    """A member X is blocked iff no character lambda of X has
    lambda(x_c) = 1 for every collision c.  Equivalently, the
    F_p system {<lam, vec(x_c)> = 1} is inconsistent."""
    vs = [member_vecs[i] for i in collision_component_indices]
    return not consistent_ones_p(vs, p)


# ---------------------------------------------------------------------------
# Forced-intersection cache
# ---------------------------------------------------------------------------

def build_forced_intersection_cache(classes, nG):
    """For each pair of class indices (i, j) with i <= j, determine whether
    any pairwise-trivial pair of copies exists.  Returns dict (i,j) -> bool."""
    cache = {}
    n = len(classes)
    t0 = time.time()
    for i in range(n):
        for j in range(i, n):
            ci = classes[i]
            cj = classes[j]
            if ci["order"] * cj["order"] > nG:
                cache[(i, j)] = False
                continue
            found = False
            # Check all pairs of copies
            for Hi in ci["copies"]:
                for Hj in cj["copies"]:
                    inter = libgap.Intersection(Hi, Hj)
                    if int(libgap.Size(inter)) == 1:
                        found = True
                        break
                if found:
                    break
            cache[(i, j)] = found
    elapsed = time.time() - t0
    print("FORCED-INTERSECTION cache built: %d pairs in %.1fs" % (len(cache), elapsed),
          flush=True)
    return cache


def pair_trivial_possible(cache, i, j):
    """Can classes i and j have a pairwise-trivial pair?"""
    key = (min(i, j), max(i, j))
    return cache.get(key, False)


# ---------------------------------------------------------------------------
# Shape enumeration (spec section 1.2, step 1)
# ---------------------------------------------------------------------------

def enumerate_shapes(classes, twist_idx, all_sizes_idx, p, threshold, nG):
    """Enumerate shapes (iS, iT, iU) with |Sigma| > threshold.
    For k=3: all three indices in twist_idx.
    For k=2: exactly two in twist_idx, third can be any class."""
    shapes = []

    # Assumption 3: k >= 2 characters must be nontrivial.
    # k=3: all three members are twisted.
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
                if sigma > threshold:
                    shapes.append((iA, iB, iC, 3, sigma))

    # k=2: exactly two twisted, one untwisted (f=0 slot).
    # The untwisted member can be any subgroup class.
    for a in range(len(twist_idx)):
        iA = twist_idx[a]
        sA = classes[iA]["order"]
        for b in range(a, len(twist_idx)):
            iB = twist_idx[b]
            sB = classes[iB]["order"]
            if sA * sB > nG:
                continue
            # Third (untwisted) slot: any class
            for iC in range(len(classes)):
                if iC in (iA, iB):
                    # same class is ok (distinct copies), but handle via k=3 above
                    # only skip if iC is a twist class already handled
                    pass
                sC = classes[iC]["order"]
                if sA * sC > nG or sB * sC > nG:
                    continue
                sigma = sA * sB * sC // p
                if sigma <= threshold:
                    continue
                # Ensure this isn't a duplicate of a k=3 shape
                triple = tuple(sorted([iA, iB, iC]))
                if iC in twist_idx:
                    # This would be a k=3 shape, already enumerated above
                    # Only count it as k=2 if iC is NOT in twist_idx
                    # Actually, k=2 means we specifically set f_C=0.
                    # So even if iC is twistable, we can have k=2 with f_C=0.
                    # But the k=3 enumeration already covers (iA,iB,iC) with all three twisted.
                    # k=2 with iC twistable but f_C=0 is a DIFFERENT character assignment.
                    pass
                shapes.append((iA, iB, iC, 2, sigma))

    # Sort by sigma descending (for hunt mode: find biggest first)
    shapes.sort(key=lambda s: -s[4])
    return shapes


# ---------------------------------------------------------------------------
# Frame enumeration (spec section 1.2, step 3)
# ---------------------------------------------------------------------------

def enumerate_frames(classes, iS, iT, iU, fi_cache):
    """Enumerate covering pairwise-trivial triples of actual subgroup copies.
    Assumption 1: S' ∩ T' = S' ∩ U' = T' ∩ U' = 1 (case alpha)."""
    # Check forced-intersection first
    if not pair_trivial_possible(fi_cache, iS, iT):
        return []
    if not pair_trivial_possible(fi_cache, iS, iU):
        return []
    if not pair_trivial_possible(fi_cache, iT, iU):
        return []

    frames = []
    cS = classes[iS]
    cT = classes[iT]
    cU = classes[iU]

    # Fix one copy of S (WLOG by conjugation)
    S0 = cS["copies"][0]
    S0_set = set(libgap.Elements(S0))

    for T in cT["copies"]:
        T_set = set(libgap.Elements(T))
        # Assumption 1: S' ∩ T' = 1
        if len(S0_set & T_set) > 1:
            continue
        for U in cU["copies"]:
            U_set = set(libgap.Elements(U))
            # Assumption 1: S' ∩ U' = 1, T' ∩ U' = 1
            if len(S0_set & U_set) > 1:
                continue
            if len(T_set & U_set) > 1:
                continue
            # Covering: <S', T', U'> = G
            gen = libgap.Subgroup(classes[0]["copies"][0].Parent(),
                                  list(libgap.GeneratorsOfGroup(S0)) +
                                  list(libgap.GeneratorsOfGroup(T)) +
                                  list(libgap.GeneratorsOfGroup(U)))
            if int(libgap.Size(gen)) != int(libgap.Size(S0.Parent())):
                continue
            frames.append((S0, T, U))
    return frames


# ---------------------------------------------------------------------------
# Collision enumeration and eligibility check (spec section 1.2, steps 4-5)
# ---------------------------------------------------------------------------

def compute_collisions(S_elems, T_elems, U_keys, e1):
    """Compute collision list: (iS, iT, iU) indices where xyz=1,
    x in S', y in T', z in U', not all identity.
    x = (y*z)^{-1}.  We iterate over (y, z) pairs."""
    colls = []
    S_set = {str(x): i for i, x in enumerate(S_elems)}
    for iT, y in enumerate(T_elems):
        for iU, z in enumerate(U_keys):
            x = (y * z[1]) ** (-1)
            xs = str(x)
            iS = S_set.get(xs)
            if iS is not None:
                if x == e1 and y == e1 and z[1] == e1:
                    continue
                colls.append((iS, iT, iU))
    return colls


def check_eligibility_and_blockedness(colls, cd_S, cd_T, cd_U,
                                       k, twisted_slots, p):
    """For each character triple with the given k-structure, check
    eligibility (psi != 0 for all collisions) and blockedness.

    twisted_slots: set of slot names ('S','T','U') that carry nontrivial chars.
    For k=3: {'S','T','U'}.
    For k=2: two of the three.

    Returns list of eligible fully-blocked configs."""

    results = []
    n_eligible = 0

    # Character enumeration per spec section 1.2 step 4
    # For each twisted slot, enumerate nontrivial characters (kernel sets).
    # For untwisted slot, the character is the zero map.
    def slot_chars(cd, slot_name):
        if slot_name not in twisted_slots:
            # Untwisted: f = 0, kernel = all elements
            return [frozenset(range(len(cd["elems"])))]
        return cd["kernels"]

    S_chars = slot_chars(cd_S, 'S')
    T_chars = slot_chars(cd_T, 'T')
    U_chars = slot_chars(cd_U, 'U')

    for kerS in S_chars:
        for kerT in T_chars:
            for kerU in U_chars:
                # Assumption 3: k >= 2 nontrivial characters
                # Already enforced by construction.

                # Eligibility check (spec step 5):
                # For each collision, psi = f_S(x) + f_T(y) + f_U(z) mod p
                # where f_X(x) = 0 if x in ker, else some nonzero value.
                # For B = C_p, f_X maps to {0, 1, ..., p-1}.
                # The character value for x not in ker is determined by
                # which coset x lies in.  For p=2, it's simply 0/1.
                # For p=3, we need actual coset values.
                #
                # Simpler approach for eligibility: psi != 0 means
                # NOT ALL of (f_S(x), f_T(y), f_U(z)) sum to 0 mod p.
                # For p=2: psi = (0 if x in kerS else 1) + (0 if y in kerT else 1)
                #          + (0 if z in kerU else 1) mod 2.
                # For p=3: we need the actual F_3 character values.

                ok = True
                for (iS, iT, iU) in colls:
                    if p == 2:
                        psi = ((0 if iS in kerS else 1) +
                               (0 if iT in kerT else 1) +
                               (0 if iU in kerU else 1)) % 2
                    elif p == 3:
                        # For p=3, use the vec representation.
                        # The character value is sum(lam_j * vec_j) mod 3.
                        # But we stored kernels as frozensets, not actual
                        # character vectors.  We need the character values.
                        # Use the vecs directly.
                        vS = cd_S["vecs"][iS]
                        vT = cd_T["vecs"][iT]
                        vU = cd_U["vecs"][iU]
                        # For untwisted slot, value is 0 regardless.
                        fS_val = 0 if iS in kerS else None
                        fT_val = 0 if iT in kerT else None
                        fU_val = 0 if iU in kerU else None
                        # We need the actual character value, not just in/out of kernel.
                        # Abandon the kernel approach for p=3; use char vectors below.
                        psi = -1  # sentinel
                    else:
                        psi = -1
                    if p == 2:
                        if psi == 0:
                            ok = False
                            break

                if p == 3:
                    # For p=3, we need to re-check using explicit character vectors.
                    # This is handled in the p=3 path below.
                    pass
                elif not ok:
                    continue
                else:
                    n_eligible += 1
                    # Blockedness check (Assumption 4)
                    bS = is_blocked(cd_S["vecs"], [iS for (iS, _, _) in colls], p)
                    bT = is_blocked(cd_T["vecs"], [iT for (_, iT, _) in colls], p)
                    bU = is_blocked(cd_U["vecs"], [iU for (_, _, iU) in colls], p)
                    results.append({
                        "n_eligible": 1,
                        "blocked": [bS, bT, bU],
                        "all_blocked": bS and bT and bU,
                        "ncolls": len(colls),
                    })
                    continue

    return results, n_eligible


# ---------------------------------------------------------------------------
# p=3 eligibility path using explicit character vectors
# ---------------------------------------------------------------------------

def check_eligibility_blockedness_p3(colls, cd_S, cd_T, cd_U,
                                      k, twisted_slots):
    """p=3 path: enumerate character triples as vectors in F_3^dim,
    compute psi as sum of character values mod 3."""
    results = []
    n_eligible = 0
    p = 3

    def slot_lambdas(cd, slot_name):
        """Return list of (lambda_vec,) for enumeration.
        Untwisted: [(0,...,0)].
        Twisted: all nonzero vectors in F_3^dim."""
        dim = cd["dim"]
        if slot_name not in twisted_slots:
            return [tuple(0 for _ in range(dim))]
        # All nonzero vectors in F_3^dim
        nontrivial = []
        for lam in itertools.product(range(3), repeat=dim):
            if any(lam):
                nontrivial.append(lam)
        return nontrivial

    S_lams = slot_lambdas(cd_S, 'S')
    T_lams = slot_lambdas(cd_T, 'T')
    U_lams = slot_lambdas(cd_U, 'U')

    for lamS in S_lams:
        for lamT in T_lams:
            for lamU in U_lams:
                ok = True
                for (iS, iT, iU) in colls:
                    vS = cd_S["vecs"][iS]
                    vT = cd_T["vecs"][iT]
                    vU = cd_U["vecs"][iU]
                    fS_val = sum(a * b for a, b in zip(lamS, vS)) % 3
                    fT_val = sum(a * b for a, b in zip(lamT, vT)) % 3
                    fU_val = sum(a * b for a, b in zip(lamU, vU)) % 3
                    psi = (fS_val + fT_val + fU_val) % 3
                    if psi == 0:
                        ok = False
                        break
                if not ok:
                    continue
                n_eligible += 1

                # Blockedness check
                bS = is_blocked(cd_S["vecs"], [iS for (iS, _, _) in colls], p)
                bT = is_blocked(cd_T["vecs"], [iT for (_, iT, _) in colls], p)
                bU = is_blocked(cd_U["vecs"], [iU for (_, _, iU) in colls], p)
                results.append({
                    "n_eligible": 1,
                    "blocked": [bS, bT, bU],
                    "all_blocked": bS and bT and bU,
                    "ncolls": len(colls),
                })
    return results, n_eligible


# ---------------------------------------------------------------------------
# Main census loop
# ---------------------------------------------------------------------------

def run_census(G, target_name, primes, threshold, mode):
    """Run the A-side census for one target group G."""

    t_start = time.time()
    nG = int(libgap.Size(G))
    e1 = libgap.One(G)
    print("TARGET %s |G|=%d threshold=%d mode=%s primes=%s"
          % (target_name, nG, threshold, mode, primes), flush=True)

    # Build subgroup lattice
    print("Building subgroup lattice...", flush=True)
    classes, nG = build_lattice(G)
    n_subs = sum(cl["n_copies"] for cl in classes)
    print("Lattice: %d classes, %d subgroups" % (len(classes), n_subs), flush=True)

    # Build forced-intersection cache
    fi_cache = build_forced_intersection_cache(classes, nG)

    all_results = []

    for p in primes:
        tp_start = time.time()
        print("\n=== PRIME p=%d ===" % p, flush=True)

        # Identify twistable classes
        twist_idx = twistable_classes(classes, p)
        twist_sizes = [(i, classes[i]["order"], classes[i]["sd"],
                        classes[i].get("n_p_chars", 0))
                       for i in twist_idx]
        print("Twistable classes (p=%d): %s" % (p, twist_sizes), flush=True)

        if len(twist_idx) < 2:
            print("Fewer than 2 twistable classes for p=%d; skip." % p, flush=True)
            continue

        # Shape enumeration (spec section 1.2, step 1)
        # Assumption 1: case-alpha => pairwise product bound s*t <= |G|
        # Assumption 3: k >= 2
        shapes = enumerate_shapes(classes, twist_idx, list(range(len(classes))),
                                  p, threshold, nG)
        print("Shapes above threshold: %d" % len(shapes), flush=True)

        max_sigma = 0
        total_frames = 0
        total_eligible = 0
        total_blocked = 0
        shapes_checked = 0
        last_progress = time.time()

        for si, (iA, iB, iC, k, sigma) in enumerate(shapes):
            shape_t0 = time.time()

            # Forced-intersection filter (spec step 2)
            # Already checked inside enumerate_frames, but pre-check here
            # to avoid expensive frame enumeration.
            skip = False
            pairs_to_check = [(iA, iB), (iA, iC), (iB, iC)]
            for (x, y) in pairs_to_check:
                if not pair_trivial_possible(fi_cache, x, y):
                    skip = True
                    break
            if skip:
                shapes_checked += 1
                now = time.time()
                if now - last_progress >= 30:
                    print("SHAPE (%d,%d,%d) p=%d k=%d: KILLED by forced-intersection [%d/%d shapes]"
                          % (classes[iA]["order"], classes[iB]["order"], classes[iC]["order"],
                             p, k, si + 1, len(shapes)), flush=True)
                    last_progress = now
                continue

            # Determine twisted slots
            if k == 3:
                twisted_slots = {'S', 'T', 'U'}
            else:
                # k=2: iA and iB are twisted, iC is untwisted
                twisted_slots = {'S', 'T'}

            # Frame enumeration (spec step 3)
            frames = enumerate_frames(classes, iA, iB, iC, fi_cache)

            shape_eligible = 0
            shape_blocked = 0

            for (S, T, U) in frames:
                total_frames += 1

                # Compute character data for this frame's actual subgroup copies
                cd_S = char_data(S, p)
                cd_T = char_data(T, p)
                cd_U = char_data(U, p)

                # Collision enumeration
                S_elems = cd_S["elems"]
                T_elems = cd_T["elems"]
                U_elems_with_idx = list(enumerate(cd_U["elems"]))
                U_keys = [(i, e) for i, e in U_elems_with_idx]

                colls = compute_collisions(S_elems, T_elems, U_keys, e1)

                if not colls:
                    # No nontrivial collisions: honest triple, not interesting
                    # (every character triple is eligible but no member is blocked)
                    continue

                # Check eligibility and blockedness (spec steps 5-6)
                if p == 2:
                    results, n_elig = check_eligibility_and_blockedness(
                        colls, cd_S, cd_T, cd_U, k, twisted_slots, p)
                else:
                    results, n_elig = check_eligibility_blockedness_p3(
                        colls, cd_S, cd_T, cd_U, k, twisted_slots)

                shape_eligible += n_elig
                total_eligible += n_elig

                for r in results:
                    if r["all_blocked"]:
                        shape_blocked += 1
                        total_blocked += 1
                        if sigma > max_sigma:
                            max_sigma = sigma

                        # Emit config record
                        rec = {
                            "type": "config",
                            "target": target_name,
                            "p": p,
                            "shape": [classes[iA]["order"], classes[iB]["order"],
                                      classes[iC]["order"]],
                            "shape_sd": [classes[iA]["sd"], classes[iB]["sd"],
                                         classes[iC]["sd"]],
                            "sigma": sigma,
                            "k": k,
                            "ncolls": r["ncolls"],
                            "blocked": r["blocked"],
                            "semantics": "exact" if mode == "census" else "lower_bound",
                        }
                        print(json.dumps(rec), flush=True)

                        # KILL check
                        if sigma > threshold and threshold > 0:
                            print("*** KILL CANDIDATE: |Sigma|=%d > beta_0=%d ***"
                                  % (sigma, threshold), flush=True)
                            if mode == "hunt":
                                print("HUNT mode: stopping at first |Sigma| > threshold.",
                                      flush=True)
                                # Emit summary and return
                                summary = {
                                    "type": "summary",
                                    "target": target_name,
                                    "p": p,
                                    "max_sigma": max_sigma,
                                    "shapes_checked": shapes_checked,
                                    "frames_checked": total_frames,
                                    "configs_eligible": total_eligible,
                                    "configs_blocked": total_blocked,
                                    "semantics": "lower_bound",
                                    "beta0": threshold,
                                    "margin": max_sigma - threshold,
                                    "elapsed_seconds": time.time() - tp_start,
                                }
                                print(json.dumps(summary), flush=True)
                                return [summary]

            shapes_checked += 1
            now = time.time()
            if now - last_progress >= 5 or shape_eligible > 0:
                print("SHAPE (%d,%d,%d) p=%d k=%d |Sigma|=%d: frames=%d eligible=%d blocked=%d max_sigma=%d elapsed=%.1fs [%d/%d shapes]"
                      % (classes[iA]["order"], classes[iB]["order"], classes[iC]["order"],
                         p, k, sigma, len(frames), shape_eligible, shape_blocked,
                         max_sigma, now - shape_t0, si + 1, len(shapes)),
                      flush=True)
                last_progress = now

        # Emit summary for this prime
        tp_elapsed = time.time() - tp_start
        margin = max_sigma - threshold if threshold > 0 else None
        summary = {
            "type": "summary",
            "target": target_name,
            "p": p,
            "max_sigma": max_sigma,
            "shapes_checked": shapes_checked,
            "frames_checked": total_frames,
            "configs_eligible": total_eligible,
            "configs_blocked": total_blocked,
            "semantics": "exact" if mode == "census" else "lower_bound",
            "beta0": threshold,
            "margin": margin,
            "elapsed_seconds": tp_elapsed,
        }
        print(json.dumps(summary), flush=True)
        all_results.append(summary)

        print("\n--- p=%d DONE: max_sigma=%d eligible=%d blocked=%d margin=%s elapsed=%.1fs ---"
              % (p, max_sigma, total_eligible, total_blocked, margin, tp_elapsed),
              flush=True)

    total_elapsed = time.time() - t_start
    print("\nTOTAL elapsed: %.1fs" % total_elapsed, flush=True)
    return all_results


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    args = parse_args()
    primes = [int(x) for x in args.primes.split(",")]
    G = make_group(args.target)
    target_name = args.target
    run_census(G, target_name, primes, args.threshold, args.mode)


if __name__ == "__main__":
    main()
