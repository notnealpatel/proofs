"""
rho0.sage — Exact subgroup TPP ratio engine.

Computes rho_0(G) = beta_0(G)/|G| (Murthy convention, arXiv:2602.15796
Sec 1, eqs 2.5-2.6) for a manifest of target groups. Serves both:
  - Pf3 kill-test: abelian-direct-factor conjecture rho_0(AxG)=rho_0(G)
  - Qr1 lamplighter analysis: C2 wr Cn, n=3..6

USER-run program (system.md sieve policy). Never run by agents.

USAGE:
  sage rho0.sage -- [--resume] [--per-target-timeout 3600]

Space size: per target, the search explores all triples of conjugacy class
representatives of subgroups, then for promising triples expands conjugacy
orbits for pair-compatibility. For order-24 groups: ~12 conjugacy classes,
~150 triples to test. For order-384 (C2 wr C6): ~hundreds of classes;
the per-target timeout caps worst-case wall clock.

Projected runtimes (single-threaded, conservative):
  - Regression anchors (5 targets, order <= 64): < 5 minutes total
  - Kill-test controls (order <= 32): < 10 minutes total
  - Kill-test products AxG (order <= 128): < 2 hours total
  - Lamplighters n=3 (order 24): < 1 minute
  - Lamplighters n=4 (order 64): < 30 minutes
  - Lamplighters n=5 (order 160): hours, likely needs timeout
  - Lamplighters n=6 (order 384): many hours, likely needs timeout
  - D8xD8 (order 64): < 30 minutes
  - C2x[32,49], C3x[32,49] (order 64, 96): < 1 hour each
  Total: expect 4-8 hours to completion with per-target timeout of 3600s;
  the order-160/384 lamplighters may report partial results.

Checkpoints: Scratch/GroupSieve/rho0-results.jsonl (append-mode, one
record per completed or timed-out target; resumable via --resume).
Progress: prints at least every 60s showing current target and search state.

Library survey (GAP subgroup-lattice primitives):
  - ConjugacyClassesSubgroups(G): returns conjugacy classes of all
    subgroups of G. Each class has .Representative() and .AsList()
    (all conjugates). Cost: polynomial in |G| via cyclic extension
    algorithm (Cannon/Holt/Hulpke). For |G|=384, typically seconds.
  - LatticeSubgroups(G): more expensive (computes full inclusion
    relations). NOT needed here — we only need the classes.
  - WreathProduct(A, B): requires at least one arg to be a permutation
    group (IsPermGroup). Use CyclicGroup(IsPermGroup, n).
  - DirectProduct(A, B): works on any group type.
  - Elements(H): enumerate all elements of a subgroup.
  - Intersection(H, K): subgroup intersection.
  - Size(H): order of H.
  Cost profile: ConjugacyClassesSubgroups dominates; for order 384,
  expect 1-10s per call. The TPP triple-test is O(|S||T||U|) per
  candidate, dominated by element enumeration.

Pruning theory (citations from reading-papers-1to4.md):
  - Neumann Obs 3.1: |S|(|T|+|U|-1) <= |G| for any TPP triple.
    Equivalent: |S||T||U| <= |G| * |S| / (|T|+|U|-1). Prunes
    triples where the product cannot exceed current best.
  - Murthy26 Prop 2.19(2): in a non-trivial triple (|S||T||U| > |G|),
    all members are non-normal; no member contains G'; for class-2
    groups, no member contains Z(G).
  - Subgroup TPP test: for subgroups S,T,U, TPP holds iff
    for all s in S, t in T, u in U: stu = 1 => s=t=u=1.
    Equivalently: S cap TU = {1} (where TU = {tu : t in T, u in U}).
  - Conjugacy reduction: rho_0 is invariant under replacing (S,T,U)
    by (S^g, T^h, U^k) for any g,h,k in G — so we search over class
    representatives and only expand conjugates for pair-compatibility.
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

REPO_ROOT = Path("/home/exedev/p/proofs")
RESULTS_FILE = REPO_ROOT / "Scratch" / "GroupSieve" / "rho0-results.jsonl"

# ---------------------------------------------------------------------------
# Manifest (ordered small/cheap first, large/expensive last)
# ---------------------------------------------------------------------------

def build_manifest():
    """Build the ordered target manifest. Returns list of dicts with keys:
    id, description, constructor (a callable returning a GAP group),
    expected_rho0 (if known, else None), category."""

    targets = []

    # --- Category 1: Regression anchors (known rho_0) ---
    anchors = [
        ([24, 10], 1, "C3xD8"),
        ([24, 11], 1, "C3xQ8"),
        ([32, 49], 2, "ExSp(2,5)+"),
        ([32, 50], 1, "ExSp(2,5)-"),
        ([64, 226], 2, "D8:D8"),
    ]
    for (o, i), rho, desc in anchors:
        targets.append({
            "id": "%d_%d" % (o, i),
            "description": "[%d,%d] %s" % (o, i, desc),
            "constructor": ("SmallGroup", o, i),
            "expected_rho0": str(rho),
            "category": "regression_anchor",
        })

    # --- Category 2: Kill-test controls (bare G, order <= 32) ---
    # Nonabelian G with known rho_0 from Hedtke-Murthy tables
    controls = [
        ([8, 3], 1, "D8"),
        ([8, 4], 1, "Q8"),
        ([12, 4], "4/3", "D12"),
        ([16, 3], 1, "C4^2:C2 a"),
        ([16, 4], 1, "C4^2:C2 b"),
        ([16, 6], 1, "C8:C2"),
        ([16, 11], 1, "C2xD8"),
        ([16, 12], 1, "C2xQ8"),
        ([16, 13], 1, "(C4xC2):C2"),
        ([27, 3], 1, "(C3xC3):C3"),
        ([27, 4], 1, "C9:C3"),
        ([32, 49], 2, "ExSp(2,5)+"),
        ([32, 50], 1, "ExSp(2,5)-"),
    ]
    for (o, i), rho, desc in controls:
        targets.append({
            "id": "ctrl_%d_%d" % (o, i),
            "description": "control [%d,%d] %s" % (o, i, desc),
            "constructor": ("SmallGroup", o, i),
            "expected_rho0": str(rho),
            "category": "kill_test_control",
        })

    # --- Category 3: Kill-test products AxG ---
    # A in {C2, C3, C4, C2xC2} crossed with nonabelian G of order <= 32
    # that have known rho_0
    abelian_factors = [
        ("C2", 2),
        ("C3", 3),
        ("C4", 4),
        ("C2xC2", 4),
    ]
    nonabelian_with_rho0 = [
        ([8, 3], 1, "D8"),
        ([8, 4], 1, "Q8"),
        ([12, 4], "4/3", "D12"),
        ([16, 3], 1, "C4^2:C2 a"),
        ([16, 6], 1, "C8:C2"),
        ([16, 11], 1, "C2xD8"),
        ([16, 12], 1, "C2xQ8"),
        ([16, 13], 1, "(C4xC2):C2"),
        ([27, 3], 1, "(C3xC3):C3"),
        ([27, 4], 1, "C9:C3"),
        ([32, 49], 2, "ExSp(2,5)+"),
        ([32, 50], 1, "ExSp(2,5)-"),
    ]
    for a_name, a_order in abelian_factors:
        for (o, i), rho, desc in nonabelian_with_rho0:
            prod_order = a_order * o
            # Skip if product order exceeds a reasonable threshold for exhaustive search
            if prod_order > 192:
                continue
            targets.append({
                "id": "prod_%s_%d_%d" % (a_name, o, i),
                "description": "%s x [%d,%d] %s (order %d)" % (a_name, o, i, desc, prod_order),
                "constructor": ("DirectProduct", a_name, a_order, o, i),
                "expected_rho0": str(rho),
                "category": "kill_test_product",
            })

    # Specific products mentioned in the card
    extra_products = [
        ("D8xD8", "DirectProductSmall", 8, 3, 8, 3, 2, "D8xD8 (order 64)"),
        ("C2x32_49", "DirectProduct", "C2", 2, 32, 49, 2, "C2x[32,49] (order 64)"),
        ("C3x32_49", "DirectProduct", "C3", 3, 32, 49, 2, "C3x[32,49] (order 96)"),
    ]
    for eid, *rest in extra_products:
        if eid == "D8xD8":
            targets.append({
                "id": "D8xD8",
                "description": "D8xD8 (order 64)",
                "constructor": ("DirectProductSmall", 8, 3, 8, 3),
                "expected_rho0": "2",
                "category": "kill_test_product",
            })
        elif eid == "C2x32_49":
            targets.append({
                "id": "C2x32_49",
                "description": "C2x[32,49] (order 64)",
                "constructor": ("DirectProduct", "C2", 2, 32, 49),
                "expected_rho0": "2",
                "category": "kill_test_product",
            })
        elif eid == "C3x32_49":
            targets.append({
                "id": "C3x32_49",
                "description": "C3x[32,49] (order 96)",
                "constructor": ("DirectProduct", "C3", 3, 32, 49),
                "expected_rho0": "2",
                "category": "kill_test_product",
            })

    # --- Category 4: Lamplighters C2 wr Cn ---
    for n in [3, 4, 5, 6]:
        order = (2**n) * n
        targets.append({
            "id": "lamp_C2wrC%d" % n,
            "description": "C2 wr C%d (order %d)" % (n, order),
            "constructor": ("WreathProduct", 2, n),
            "expected_rho0": None,
            "category": "lamplighter",
        })

    return targets


# ---------------------------------------------------------------------------
# Group construction from manifest spec
# ---------------------------------------------------------------------------

def construct_group(spec):
    """Construct a GAP group from a manifest constructor spec."""
    kind = spec[0]
    if kind == "SmallGroup":
        return libgap.SmallGroup(spec[1], spec[2])
    elif kind == "DirectProduct":
        # ("DirectProduct", a_name, a_order, o, i)
        a_name, a_order, o, i = spec[1], spec[2], spec[3], spec[4]
        if a_name == "C2":
            A = libgap.CyclicGroup(2)
        elif a_name == "C3":
            A = libgap.CyclicGroup(3)
        elif a_name == "C4":
            A = libgap.CyclicGroup(4)
        elif a_name == "C2xC2":
            A = libgap.DirectProduct(libgap.CyclicGroup(2), libgap.CyclicGroup(2))
        else:
            raise ValueError("Unknown abelian factor: %s" % a_name)
        G = libgap.SmallGroup(o, i)
        return libgap.DirectProduct(A, G)
    elif kind == "DirectProductSmall":
        # ("DirectProductSmall", o1, i1, o2, i2)
        G1 = libgap.SmallGroup(spec[1], spec[2])
        G2 = libgap.SmallGroup(spec[3], spec[4])
        return libgap.DirectProduct(G1, G2)
    elif kind == "WreathProduct":
        # ("WreathProduct", base_order, top_order)
        base = libgap.CyclicGroup(libgap.IsPermGroup, spec[1])
        top = libgap.CyclicGroup(libgap.IsPermGroup, spec[2])
        return libgap.WreathProduct(base, top)
    else:
        raise ValueError("Unknown constructor kind: %s" % kind)


# ---------------------------------------------------------------------------
# TPP search engine
# ---------------------------------------------------------------------------

def compute_rho0(G, order_G, timeout_deadline, progress_cb):
    """Compute exact rho_0(G) by exhaustive subgroup triple search.

    Returns (rho0_exact: Rational or None, best_triple_type: tuple or None,
             search_stats: dict, timed_out: bool).

    Strategy:
    1. Compute conjugacy classes of subgroups.
    2. For each ordered triple of class representatives (S_rep, T_rep, U_rep):
       a. Prune by Neumann: |S||T||U| must exceed current best.
       b. Prune non-normal members when seeking non-trivial triples.
       c. Test TPP on representatives.
       d. If TPP holds on reps, record as candidate; also test all
          conjugates in the respective classes for better triples.
    3. Return the maximum |S||T||U|/|G| found.

    The conjugacy-reduction argument: if (S,T,U) is a TPP triple then
    so is (S^g, T^h, U^k) for any g,h,k, with the same product |S||T||U|.
    So the maximum over ALL triples equals the maximum over triples drawn
    from class representatives — but we must test ALL combinations of
    one representative per class (not all conjugates), since the TPP
    property is NOT conjugation-invariant for mixed triples.
    """

    t_start = time.time()
    last_progress = t_start

    # Get conjugacy classes
    classes = G.ConjugacyClassesSubgroups().AsList()
    n_classes = len(classes)

    # Precompute class info: representative, order, elements, is_normal
    class_info = []
    for cl in classes:
        rep = cl[0] if hasattr(cl, '__getitem__') else cl
        # cl is a ConjugacyClassSubgroups object in GAP
        # Actually classes is a list of ConjugacyClassSubgroups
        pass

    # Re-approach: use the standard GAP interface
    conj_classes = G.ConjugacyClassesSubgroups()
    class_data = []
    for cl in conj_classes:
        rep = cl.Representative()
        h_order = int(rep.Size())
        class_data.append({
            "rep": rep,
            "order": h_order,
            "class": cl,
        })

    n_classes = len(class_data)
    # Sort by order for pruning efficiency
    class_data.sort(key=lambda x: x["order"])

    stats = {
        "n_conjugacy_classes": n_classes,
        "n_triples_tested": 0,
        "n_triples_pruned_neumann": 0,
        "n_triples_pruned_normal": 0,
        "n_tpp_checks": 0,
    }

    one = G.Identity()
    best_product = int(order_G)  # trivial triple gives |G|*1*1 = |G|
    best_triple_orders = (order_G, 1, 1)
    timed_out = False

    # Precompute: which classes have normal representatives?
    # (All conjugates of a normal subgroup are the same subgroup, so
    # a normal subgroup's class has size 1.)
    for cd in class_data:
        cd["is_normal"] = bool(libgap.IsNormal(G, cd["rep"]))

    # Precompute derived subgroup and center for pruning
    Gp = G.DerivedSubgroup()
    Z = G.Centre()
    nil_class = None
    if G.IsNilpotentGroup():
        nil_class = int(G.NilpotencyClassOfGroup())

    def tpp_holds(S, T, U):
        """Test if subgroups S, T, U satisfy TPP: stu=1 => s=t=u=1."""
        stats["n_tpp_checks"] += 1
        # Compute TU = {tu : t in T, u in U} as a set of GAP elements
        T_elts = T.Elements().AsList()
        U_elts = U.Elements().AsList()
        S_elts = S.Elements().AsList()

        # Build the set TU
        TU_set = set()
        for t in T_elts:
            for u in U_elts:
                TU_set.add(t * u)

        # Check S ∩ TU = {1}: for each s in S\{1}, check if s^{-1} is NOT in TU
        # Actually: stu = 1 means s = (tu)^{-1}, so s in S ∩ (TU)^{-1}\{1} violates TPP
        # Correction: stu = 1 => u = (st)^{-1} = t^{-1} s^{-1}
        # More directly: stu = 1 => s^{-1} = tu
        # So TPP fails iff there exist s!=1 in S, t in T, u in U with s^{-1} = tu
        # i.e., S^{-1} ∩ TU contains a non-identity element
        # Wait, need to be more careful. stu=1 means s = (tu)^{-1} = u^{-1} t^{-1}
        # No: stu = 1 => s^{-1} = tu (multiply both sides on left by s^{-1})
        # So: for subgroups, TPP holds iff:
        #   for all nontrivial s in S: s^{-1} not in TU
        #   AND for all nontrivial t in T: t^{-1} not in SU
        #   ... no, that's the wrong decomposition.
        #
        # Actually the FULL condition is: stu = 1 => s=t=u=1.
        # stu = 1 means s^{-1} = tu. So if s^{-1} is in TU for some s != 1,
        # then there exist t in T, u in U with stu = 1 and s != 1. TPP fails.
        #
        # But we also need: even if s = 1, we need tu = 1 => t = u = 1.
        # i.e., T ∩ U^{-1} = {1}, which for subgroups means T ∩ U = {1}.
        #
        # So full TPP for subgroups is equivalent to:
        #   (a) T ∩ U = {1}
        #   (b) For all s in S, s != 1: s^{-1} not in TU
        #       i.e., S^{-1} ∩ TU = {1}
        #       i.e., S ∩ TU = {1} (since S is a subgroup, S^{-1} = S)
        #
        # Wait: S is a subgroup so S^{-1} = S. Therefore:
        # TPP <=> S ∩ TU = {1} AND T ∩ U = {1}
        #
        # Hmm, let me re-derive. stu = 1. Then:
        # - s = (tu)^{-1} = u^{-1} t^{-1}. Since S is a group, s in S.
        #   So s^{-1} = tu in TU. Since S is a subgroup, s^{-1} in S.
        #   So s^{-1} in S ∩ TU.
        # If s != 1 then s^{-1} != 1 and we have a nontrivial element in S ∩ TU.
        #
        # Conversely if x in S ∩ TU, x != 1, then x = tu for some t in T, u in U,
        # and x in S, so x * t * u^{-1}... no wait. x = tu and x in S means
        # set s = x^{-1}, then s * t * u... no.
        #
        # Let me just use the brute force definition: check all triples.

        for s in S_elts:
            for t in T_elts:
                for u in U_elts:
                    if s * t * u == one:
                        if not (s == one and t == one and u == one):
                            return False
        return True

    def tpp_holds_fast(S, T, U):
        r"""Faster TPP check using set intersection.

        For subgroups S, T, U: TPP holds iff S ∩ TU = T ∩ U = {1}.
        Proof: stu = 1 => s = (tu)^{-1}. If s != 1 then (tu)^{-1} != 1,
        and s in S, (tu)^{-1} = s in S. Also tu = s^{-1} in S (subgroup).
        So tu in S ∩ TU... Actually let me use the correct formulation:

        stu = 1 <=> s^{-1} = tu.
        Since S is a subgroup: s^{-1} in S.
        So: TPP fails iff there exist s in S\{1}, t in T, u in U with s^{-1} = tu.
        i.e., S\{1} ∩ TU is nonempty (using S = S^{-1} for subgroups).
        Plus the case s=1: tu=1, t=u^{-1}, so T ∩ U^{-1} = T ∩ U (subgroups) must be {1}.

        Full condition: S ∩ TU = {1} (this includes the T ∩ U = {1} case
        since if t in T ∩ U\{1} then 1 * t * t^{-1} = 1 with 1 in S, t!=1,
        which... wait that has s=1, so we need t=u=1 too. So T ∩ U = {1}
        is a separate condition? No:

        If t0 in T ∩ U, t0 != 1: set u0 = t0^{-1} in U (subgroup), then
        1 * t0 * t0^{-1} = 1 with s=1, t=t0!=1. TPP fails.
        So T ∩ U != {1} => TPP fails.

        If x in S ∩ TU, x != 1: x = tu for some t,u. Set s = x^{-1} in S
        (subgroup). Then s * t * u = x^{-1} * x = 1 with s = x^{-1} != 1.
        TPP fails.

        Conversely if TPP fails: s*t*u=1 with (s,t,u) != (1,1,1).
        Case s != 1: s^{-1} = tu in TU, and s^{-1} in S. So s^{-1} in S ∩ TU\{1}.
        Case s = 1: tu = 1 with (t,u) != (1,1). Then t = u^{-1} in T ∩ U\{1}.
          But 1 in S and tu = 1 means 1 is in S ∩ TU? 1 = 1*1 in TU always.
          We need S ∩ TU = {1}... but 1 is always in both. So the condition
          should be S ∩ TU ⊆ {1}... which is S ∩ TU = {1} (meaning only
          the identity).
          If s=1, tu=1, t!=1: then u=t^{-1}, so 1 = t*t^{-1} in TU (always there).
          s^{-1} = 1 = tu... so 1 in TU always. We want: the only element
          of S that equals some product tu is the identity (with t=1,u=1).

        OK let me state it cleanly:
        TPP <=> for all (s,t,u) in SxTxU: stu=1 => s=t=u=1.
        <=> {s^{-1} : s in S} ∩ {tu : t in T, u in U} = {1}
        <=> S ∩ TU = {1}  (since S^{-1} = S for subgroups, and we mean
            the only common element is the identity 1 = 1*1 in TU).

        Actually 1 in S always, and 1 = 1*1 in TU always, so S ∩ TU always
        contains {1}. The TPP condition is S ∩ TU = {1}.

        Wait but we also need: when s=1, t*u=1 means only t=u=1.
        If S ∩ TU = {1}: can 1 = tu with t!=1? Then tu in TU and
        we'd need to check if 1 is the only element in S ∩ TU... but
        1 in S always, and if tu = 1 with t!=1 then 1 in TU via that product.
        But 1 is already in S ∩ TU (it's always there). So S ∩ TU = {1}
        does NOT rule out tu=1 with t!=1.

        Let me reconsider. S ∩ TU = {1} means: the ONLY element that is both
        in S and expressible as tu (for t in T, u in U) is the identity.
        But 1 = 1*1 is always such an element. If there exists t0 != 1 in T
        with t0^{-1} in U, then t0 * t0^{-1} = 1 in TU. So 1 in TU via
        the trivial product AND via (t0, t0^{-1}). This doesn't add a new
        element to S ∩ TU — 1 is still 1.

        So S ∩ TU = {1} means {1} is the only common element.
        Now: stu = 1 with s in S means s^{-1} = tu in TU. Since S subgroup,
        s^{-1} in S. So s^{-1} in S ∩ TU = {1}, hence s^{-1} = 1, s = 1.
        Then tu = 1. If T ∩ U = {1} (as subgroups), then... wait, tu=1
        means t = u^{-1}, so t in T and t in U^{-1} = U (subgroup), so
        t in T ∩ U. If T ∩ U = {1} then t = 1, hence u = 1.

        So: TPP <=> S ∩ TU = {1} AND T ∩ U = {1}.

        But actually: S ∩ TU = {1} already implies T ∩ U = {1}!
        Proof: if t in T ∩ U, t != 1, then t = t * 1 in TU (with the
        element t from T and identity 1 from U). Also t in... wait, t in U
        means... no. TU = {t'u' : t' in T, u' in U}. So t = t * 1 in TU
        (since 1 in U). And t in T. But we need t in S for it to violate
        S ∩ TU = {1}. t might not be in S.

        So no, S ∩ TU = {1} does NOT imply T ∩ U = {1} in general.

        Correct full condition: TPP <=> S ∩ TU = {1} AND T ∩ U = {1}.
        Hmm actually let me re-examine.

        stu = 1, s=1: then tu = 1, u = t^{-1} in U, so t in T and t^{-1} in U.
        Since U is a subgroup, t^{-1} in U means t in U. So t in T ∩ U.
        For TPP we need t = 1 (hence u = 1). So need T ∩ U = {1}.

        stu = 1, s!=1: s^{-1} = tu in TU. s^{-1} in S (subgroup). So
        s^{-1} in S ∩ TU. For TPP we need s^{-1} = 1, contradiction s!=1.
        So need (S\{1}) ∩ TU^{-1}... no.
        We need: no s^{-1} != 1 is in TU. I.e., (S\{1}) ∩ TU = empty.
        Since 1 in S and 1 in TU, S ∩ TU contains 1 always.
        The condition is: S ∩ TU = {1} (nothing beyond the identity).

        So FULL TPP: S ∩ TU = {1} AND T ∩ U = {1}.

        Wait, but if S ∩ TU = {1}, does that already ensure the s=1 case?
        When s = 1: stu = tu = 1 means u = t^{-1}. The triple is (1, t, t^{-1}).
        s = 1 is fine. For TPP we need t = 1 too.
        The condition S ∩ TU = {1} says: the only element in S that equals
        some tu is identity. s = 1 is already in S ∩ TU (via 1 = 1*1).
        Even if t != 1 and u = t^{-1} != 1: tu = 1, and 1 in S. So 1 in
        S ∩ TU — but we already knew that. S ∩ TU = {1} is satisfied even
        if T ∩ U != {1}, because the "violating" products tu = 1 still
        only give element 1 in TU (which is in S ∩ TU = {1}).

        So S ∩ TU = {1} does NOT exclude the case s=1, t!=1, u=t^{-1}.
        The issue is that 1 in S ∩ TU is always true, and we declared
        S ∩ TU = {1} meaning it's the ONLY element there. But the TPP
        violation (1, t, t^{-1}) has s = 1, which IS in S ∩ TU... and the
        condition S ∩ TU = {1} is satisfied. But TPP is violated!

        OK so the correct formulation must be:
        TPP <=> S ∩ TU = {1} AND T ∩ U = {1}.
        Or equivalently: use the full brute force.

        Actually, I think I was overcomplicating. Let me just use the O(|S||T||U|)
        brute force which is clearly correct, and optimize with early exit.
        For groups of order up to ~400, this is fine.
        """
        stats["n_tpp_checks"] += 1
        S_elts = list(S.Elements().AsList())
        T_elts = list(T.Elements().AsList())
        U_elts = list(U.Elements().AsList())

        for s in S_elts:
            for t in T_elts:
                st = s * t
                for u in U_elts:
                    if st * u == one:
                        if not (s == one and t == one and u == one):
                            return False
        return True

    # Enumerate ordered triples of class reps in descending-product order
    # WITHOUT materializing them: the full list is O(n_classes^3) and hit
    # 19 GB / OOM on C4 x [32,49] (order 128). Subgroup orders divide |G|,
    # so bucket classes by order, sort the few hundred order-triples, and
    # stream index-triples lazily; iteration order (non-increasing product)
    # and the early-break prune are preserved exactly.
    import itertools
    from collections import defaultdict
    by_order = defaultdict(list)
    for i, ci in enumerate(class_data):
        by_order[int(ci["order"])].append(i)
    order_triples = []
    for oS in by_order:
        for oT in by_order:
            for oU in by_order:
                prod = oS * oT * oU
                if prod <= order_G:  # Only interesting if ratio > 1
                    continue
                # Neumann Obs 3.1 depends only on member orders: prune
                # whole buckets here, not per-candidate (554M candidate
                # iterations collapsed to the few surviving buckets)
                if oS * (oT + oU - 1) > order_G:
                    continue
                if oT * (oS + oU - 1) > order_G:
                    continue
                if oU * (oS + oT - 1) > order_G:
                    continue
                order_triples.append((prod, oS, oT, oU))
    order_triples.sort(reverse=True)  # Largest product first

    def _iter_candidates():
        for prod, oS, oT, oU in order_triples:
            for i, j, k in itertools.product(
                    by_order[oS], by_order[oT], by_order[oU]):
                yield (prod, i, j, k)

    candidates = _iter_candidates()
    n_candidates = sum(
        len(by_order[oS]) * len(by_order[oT]) * len(by_order[oU])
        for _, oS, oT, oU in order_triples)
    tested = 0
    pruned_neumann = 0

    for idx_cand, (prod, i, j, k) in enumerate(candidates):
        # Check timeout
        now = time.time()
        if timeout_deadline and now > timeout_deadline:
            timed_out = True
            break

        # Progress callback
        if now - last_progress > 60:
            progress_cb("  [%s] testing candidate %d/%d, best=%s, tpp_checks=%d" %
                        (time.strftime("%H:%M:%S"), idx_cand, n_candidates,
                         str(QQ(best_product) / order_G), stats["n_tpp_checks"]))
            last_progress = now

        # Neumann pruning: can this triple beat current best?
        if prod <= best_product:
            pruned_neumann += 1
            # Since candidates are sorted descending, all remaining are worse
            break

        ci = class_data[i]
        cj = class_data[j]
        ck = class_data[k]

        # Neumann Obs 3.1: |S|(|T|+|U|-1) <= |G|
        s_ord, t_ord, u_ord = ci["order"], cj["order"], ck["order"]
        if s_ord * (t_ord + u_ord - 1) > order_G:
            stats["n_triples_pruned_neumann"] += 1
            continue
        if t_ord * (s_ord + u_ord - 1) > order_G:
            stats["n_triples_pruned_neumann"] += 1
            continue
        if u_ord * (s_ord + t_ord - 1) > order_G:
            stats["n_triples_pruned_neumann"] += 1
            continue

        # Murthy pruning: in a non-trivial triple (prod > |G|), all members
        # are non-normal.
        if ci["is_normal"] or cj["is_normal"] or ck["is_normal"]:
            stats["n_triples_pruned_normal"] += 1
            continue

        # Test TPP on class representatives
        stats["n_triples_tested"] += 1
        S_rep = ci["rep"]
        T_rep = cj["rep"]
        U_rep = ck["rep"]

        if tpp_holds_fast(S_rep, T_rep, U_rep):
            if prod > best_product:
                best_product = prod
                best_triple_orders = (s_ord, t_ord, u_ord)

        # Also try conjugates of T and U with the same S representative
        # (since TPP is NOT preserved under independent conjugation of members,
        # but rho_0 searches over all subgroups, not just representatives)
        # For efficiency: only expand conjugates for promising size combinations
        if prod > best_product or prod > order_G:
            # Get all conjugates in each class
            T_conjugates = cj["class"].AsList()
            U_conjugates = ck["class"].AsList()
            S_conjugates = ci["class"].AsList()
            # Test a sample: S_rep with all T_conj, U_conj
            for T_conj in T_conjugates:
                for U_conj in U_conjugates:
                    if timeout_deadline and time.time() > timeout_deadline:
                        timed_out = True
                        break
                    stats["n_tpp_checks"] += 1
                    if tpp_holds_fast(S_rep, T_conj, U_conj):
                        if prod > best_product:
                            best_product = prod
                            best_triple_orders = (s_ord, t_ord, u_ord)
                            break  # Found one, that's enough for this prod level
                if timed_out or best_product >= prod:
                    break
            if timed_out:
                break
            # If we haven't found it yet, try different S conjugates too
            if best_product < prod:
                for S_conj in S_conjugates:
                    if S_conj == S_rep:
                        continue
                    for T_conj in T_conjugates:
                        for U_conj in U_conjugates:
                            if timeout_deadline and time.time() > timeout_deadline:
                                timed_out = True
                                break
                            stats["n_tpp_checks"] += 1
                            if tpp_holds_fast(S_conj, T_conj, U_conj):
                                if prod > best_product:
                                    best_product = prod
                                    best_triple_orders = (s_ord, t_ord, u_ord)
                                    break
                        if timed_out or best_product >= prod:
                            break
                    if timed_out or best_product >= prod:
                        break

    rho0 = QQ(best_product) / QQ(order_G)
    stats["n_triples_pruned_neumann"] += pruned_neumann
    stats["best_product"] = int(best_product)

    return rho0, best_triple_orders, stats, timed_out


# ---------------------------------------------------------------------------
# Main loop with checkpointing
# ---------------------------------------------------------------------------

def load_completed_ids():
    """Load IDs of already-completed targets from the results file."""
    completed = set()
    if RESULTS_FILE.exists():
        with open(RESULTS_FILE) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                    completed.add(rec.get("id", ""))
                except json.JSONDecodeError:
                    pass
    return completed


def append_result(record):
    """Append one JSONL record to the results file."""
    with open(RESULTS_FILE, "a") as f:
        f.write(json.dumps(record) + "\n")


def main(argv):
    parser = argparse.ArgumentParser(
        description="Exact subgroup TPP ratio engine (rho_0)")
    parser.add_argument("--resume", action="store_true",
                        help="skip targets already in the results file")
    parser.add_argument("--per-target-timeout", type=int, default=3600,
                        help="seconds per target (default 3600)")
    parser.add_argument("--target-id", type=str, default=None,
                        help="run only a specific target by ID")
    args = parser.parse_args(argv)

    manifest = build_manifest()
    completed = load_completed_ids() if args.resume else set()

    if args.target_id:
        manifest = [t for t in manifest if t["id"] == args.target_id]
        if not manifest:
            print("ERROR: target '%s' not found in manifest." % args.target_id, flush=True)
            sys.exit(1)

    print("=" * 70, flush=True)
    print("rho0.sage — Exact subgroup TPP ratio engine", flush=True)
    print("Targets: %d total, %d already done, %d to run" %
          (len(manifest), len(completed),
           len([t for t in manifest if t["id"] not in completed])), flush=True)
    print("Per-target timeout: %ds" % args.per_target_timeout, flush=True)
    print("Results file: %s" % RESULTS_FILE, flush=True)
    print("=" * 70, flush=True)
    print(flush=True)

    for i, target in enumerate(manifest):
        tid = target["id"]
        if tid in completed:
            continue

        print("[%d/%d] %s" % (i + 1, len(manifest), target["description"]), flush=True)
        t0 = time.time()
        deadline = t0 + args.per_target_timeout

        def progress_cb(msg):
            print(msg, flush=True)

        try:
            G = construct_group(target["constructor"])
            order_G = int(G.Order())
            print("  Order: %d" % order_G, flush=True)

            rho0, triple_type, stats, timed_out = compute_rho0(
                G, order_G, deadline, progress_cb)

            elapsed = time.time() - t0
            record = {
                "id": tid,
                "description": target["description"],
                "order": int(order_G),
                "rho0_exact": str(rho0),
                "rho0_float": float(float(rho0)),
                "achieving_triple_type": [int(x) for x in triple_type] if triple_type else None,
                "expected_rho0": target.get("expected_rho0"),
                "category": target["category"],
                "search_stats": {k: int(v) if isinstance(v, (int, Integer)) else v
                                 for k, v in stats.items()},
                "runtime_seconds": float(round(elapsed, 1)),
                "timed_out": timed_out,
            }

            append_result(record)
            completed.add(tid)

            status = "TIMEOUT (partial)" if timed_out else "DONE"
            match_str = ""
            if target.get("expected_rho0") is not None:
                expected = QQ(target["expected_rho0"])
                match_str = " [MATCH]" if rho0 == expected else " [MISMATCH expected=%s]" % expected
            print("  %s: rho_0 = %s (%.6f), triple type %s, %.1fs%s" %
                  (status, rho0, float(rho0), triple_type, elapsed, match_str), flush=True)
            print(flush=True)

        except KeyboardInterrupt:
            print("\nInterrupted at target '%s'. Results saved up to previous target." % tid,
                  flush=True)
            sys.exit(130)
        except Exception as e:
            elapsed = time.time() - t0
            record = {
                "id": tid,
                "description": target["description"],
                "order": None,
                "rho0_exact": None,
                "rho0_float": None,
                "achieving_triple_type": None,
                "expected_rho0": target.get("expected_rho0"),
                "category": target["category"],
                "search_stats": {},
                "runtime_seconds": round(elapsed, 1),
                "timed_out": False,
                "error": str(e),
            }
            append_result(record)
            completed.add(tid)
            print("  ERROR: %s (%.1fs)" % (e, elapsed), flush=True)
            print(flush=True)

    print("=" * 70, flush=True)
    print("All targets processed. Results: %s" % RESULTS_FILE, flush=True)
    print("=" * 70, flush=True)


# Entry point (same pattern as groupsieve.sage — sage runs in exec context)
main([a for a in sys.argv[1:] if a != "--"])
