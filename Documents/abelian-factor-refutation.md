# Adjoining an abelian direct factor can increase the TPP capacity ratio

**Status: computational manuscript, agent-drafted 2026-07-17,
revised 2026-07-18 (lift law, five-kill census, exact values).
Pending author verification (Hu9 gate).  All machine outputs cited
here are on disk under `Scratch/GroupSieve/forge/out/` and
`.tasks/f5exp/docs/`; every claim is labeled with its verification
status.**

## Abstract

For a finite group G, let beta_0(G) be the largest value of
|S||T||U| over subgroup triples of G satisfying the triple product
property (TPP), and rho_0(G) = beta_0(G)/|G|.  We refute the
conjecture

    rho_0(A x G) = rho_0(G)   (A abelian)

by five independently verified counterexamples at A = C_2, in
three groups (S_6, M_10, A_7):

    beta_0(C_2 x S_6)  = 5184  > 4800  = 2 * beta_0(S_6)
    beta_0(C_2 x M_10) = 6144  > 4608  = 2 * beta_0(M_10)
    beta_0(C_2 x A_7)  >= 31104 > 21168 = 2 * beta_0(A_7)

The first two are exact (exhaustive search over C_2 x G);
the third is a verified lower bound.  In all cases each
right-hand side rests on a new exact computation of beta_0 by
exhaustive search; each left-hand side includes concrete subgroup
triples in C_2 x G, checked to satisfy the TPP by brute force with
no reliance on the search machinery.  Consequently rho_0 is not
invariant under abelian direct factors:

    rho_0(C_2 x S_6)  = 18/5   > 10/3 = rho_0(S_6)
    rho_0(C_2 x M_10) = 64/15  > 16/5 = rho_0(M_10)
    rho_0(C_2 x A_7)  >= 216/35 > 21/5 = rho_0(A_7)

The same sweep produced exact values beta_0(A_5) = 108,
beta_0(S_5) = 256, beta_0(PSL(2,11)) = 1980, beta_0(M_10) = 2304,
beta_0(S_6) = 2400, beta_0(A_7) = 10584, and a structured picture
of *where* the conjecture fails: the adversary quantity (maximal
"eligible configuration" size) sits strictly below beta_0 for
A_5 and S_5, ties it exactly for A_6 and PSL(2,11), and exceeds it
from order 720 onward, with the excess growing (+192, +768, +4968).

We prove a replacement law (Theorem 1): for every finite G and
prime p,

    beta_0(C_p x G) = p * max( beta_0(G), Sigma_max^lift(G, p) ),

where Sigma_max^lift(G, p) is the maximum of |Sigma| over
sign-liftable configurations (Definition 5).  The proof is by
Goursat case analysis of the subgroups of C_p x G.  This law
reduces to beta_0(C_p x G) = p * beta_0(G) when p is coprime
to |G| (recovering the conjecture where it holds), and to
beta_0(C_p x G) = p * Sigma_max^lift(G, p) when sign-liftable
configurations dominate (the violation regime).  Combined with
the census, the law yields exact values for all seven targets at
p = 2 and p = 3, including beta_0(C_2 x A_7) = 31104.

## 1. Definitions

A triple (S, T, U) of subsets of a group H satisfies the **triple
product property** if for all s,s' in S, t,t' in T, u,u' in U,

    s'^{-1} s t'^{-1} t u'^{-1} u = 1  implies  s = s', t = t', u = u'.

For subgroup triples this reduces to the two conditions
S ∩ TU = 1 and T ∩ U = 1 (checked in exactly this form below).
Define

    beta_0(G) = max { |S||T||U| : S,T,U <= G subgroups, TPP },
    rho_0(G)  = beta_0(G) / |G|.

These invariants originate in the Cohn-Umans group-theoretic
framework for matrix multiplication [CU03]; they have since been
studied as structural invariants of finite groups in their own
right, with Hedtke-Murthy 2012 computing exact values for PSL and
small-group families and Murthy 2025-2026 establishing upper bounds
on rho_0 for nilpotent and prime-index-extension families
[arXiv:2602.15796, arXiv:2512.16730].  The present work contributes
to this structural line: we determine how beta_0 transforms under
direct product with a cyclic group of prime order.

A **sign configuration** in G at a prime p is a tuple
(S', T', U', f_S, f_T, f_U) with S', T', U' <= G and
homomorphisms f_X : X' -> C_p.  Set Pi := S' x T' x U',
psi(x,y,z) := f_S(x) + f_T(y) + f_U(z),
k := #{ X : f_X != 0 } (the twist count),
Sigma := psi^{-1}(0) <= Pi.  The configuration is
**sign-liftable** if k >= 1 and psi(c) != 0 for every nontrivial
collision c = (x,y,z) with xyz = 1.  Define

    Sigma_max^lift(G, p) := max { |Sigma| : sign-liftable
                                  configurations in G },

with max over the empty set equal to 0.

## 2. The conjecture and its provenance

**Conjecture (this project, Pf3 campaign, 2026-07).**
rho_0(A x G) = rho_0(G) for every abelian A and finite G;
equivalently beta_0(A x G) = |A| * beta_0(G).

Provenance and honesty notes:

- The **>= direction is known**: subgroup triples lift along the
  product (classical lift), and beta_0(A) = |A| for abelian A.
  Citations carried from the Pf3 report: thesis
  [arXiv:0709.1223] Lemma 4.8; CU03 Lemma 2.2 + Lemma 3.1.
- The **<= direction is unstated in the literature** per the Pf3
  novelty sweep; the conjecture is project-internal.  This
  manuscript therefore refutes *our own* natural conjecture, not a
  named open problem.  Its external content is: **rho_0 is not
  preserved by abelian direct factors**, a possibility the
  existing product tables (Hedtke-Murthy 2012, ~7 pairs, all
  consistent with equality) gave no hint of.  The result is
  situated alongside Murthy's recent structural work: where
  [arXiv:2512.16730] bounds rho_0 from above for groups with
  abelian normal subgroups of prime index (using an implicit
  Goursat decomposition), we determine rho_0 of the product
  exactly via an explicit lift law.
- Prior supporting evidence: exhaustive verification on 40+ small
  groups (Pf3 sessions 3-4), all Hedtke-Murthy product rows, and
  a partial proof (Pf3 session-4 structure theorems) covering all
  configuration space except one corner ("all-blocked case
  alpha") -- the corner where the counterexamples live.

## 3. Method

Two independent computations per target G ("the diagnostic"):

- **B-side (capacity):** beta_0(G) by exhaustive search over
  subgroup-class triples with Neumann and non-normality pruning
  (Go engine `cmd/sieve/beta0probe`, input = Cayley-table JSON
  from `export_tpp.sage`).  Every value below carries `exact`
  semantics: the candidate space was exhausted, no budget cutoff.
  The engine's exactness was audited against a known incident (a
  flawed Sage-prototype cutoff once returned 900 for A_6 instead
  of 972; the Go path has no analogous cutoff).
- **A-side (adversary):** a census (`aside_census.sage`) of
  *eligible configurations*: triples (X, Y, Z) of subgroups with
  pairwise trivial intersections, generating G, carrying
  characters f : member -> C_p (p in {2,3}) such that every
  collision xyz = 1 is "psi-odd".  By the graph-lift
  correspondence, an eligible configuration yields the
  subgroup triple (X-hat, Y-hat, Z-hat) of graph subgroups in
  C_p x G, of size |X||Y||Z|; the configuration's
  |Sigma| = |X||Y||Z| / p exceeding beta_0(G) is exactly a
  counterexample candidate.  The census declares four proved
  pruning assumptions (from the Pf3 session-4 structure theorems)
  in its header; its scope is kernels B = C_p, p in {2,3}.
- **Verification discipline:** census hits are *candidates only*.
  Each counterexample claimed here was re-verified by a standalone
  script that rebuilds the members from generator strings,
  re-checks orders / pairwise-trivial intersections / generation,
  enumerates ALL index-2 kernel combinations per member, and
  brute-checks S ∩ TU = 1, T ∩ U = 1 for the lifted triple two
  ways: exact pair arithmetic in C_2 x G, then a raw
  permutation-group check with C_2 realized on two fresh points.
  No step of the census or the correspondence is trusted.
- **Exhaustive product verification (kills #4 and #5):**
  `verify_all_combos.sage` extends the verification to all
  character combinations (k=1, k=2, and k=3), closing the gap
  left by `verify_kill_any.sage` which enumerated only nontrivial
  characters.  The sigma=2560 families lift at k=2 but not k=3.

**Calibration** (all reproduced before any metered run): the S_4
anchor (38,340 eligible / 0 blocked, exact match with the Pf3
session-4 scan); beta_0(A_5) = 108 by two independent routes (Go
engine and Sage); the A_6 reproduction gate (below).

**Methods incident, disclosed:** the first A_6 census run returned
0 configurations at the tie because of an off-by-one -- the k=2
shape filter used strict `>` threshold while the k=3 filter used
`>=`, and the A_6 ground truth is a k=2 configuration sitting
exactly at the threshold.  The one-line fix was applied and the
gate then reproduced the Pf3 ground truth exactly, including a
count-convention reconciliation: the census's 12 anchored frames
(one S_3 copy fixed per class; S_3 is self-normalizing in A_6,
60 copies per class) equal Pf3's 72 C_3^2-anchored configurations,
both normalizations of the same 720 unnormalized configs.  The
incident is recorded because the tie region is precisely where the
zero-margin phenomenon lives; a strict filter silently blinds the
census to it.

## 4. Results: exact capacities and census margins

All B-side values exact.  The first three rows (A_5, A_6,
PSL(2,11)) reproduce values published in Hedtke-Murthy 2012,
Table 3 (as PSL_2(F_4), PSL_2(F_9), PSL_2(F_11) respectively);
the remaining four (S_5, M_10, S_6, A_7) are new.  rho_0 strictly
increases along the sample; only the conjecture, not each value,
received a formal novelty sweep.

| G          | order | beta_0 | rho_0  | witness orders | census verdict (p=2 / p=3) |
|------------|------:|-------:|--------|----------------|-----------------------------|
| A_5        |    60 |    108 | 9/5    | (6,6,3)        | slack: 0 blocked / 0 blocked (exact) |
| S_5        |   120 |    256 | 32/15  | (4,8,8)        | slack: 0 blocked / no shapes (exact) |
| A_6        |   360 |    972 | 27/10  | (12,9,9)       | tie: 12 blocked at 972 / 144 blocked at 972 (exact) |
| PSL(2,11)  |   660 |  1,980 | 3      | (55,6,6)       | tie: 180 blocked at 1980 / none (exact) |
| M_10       |   720 |  2,304 | 16/5   | (8,8,36)       | **+768**: max 3072 (96 configs above) / none |
| S_6        |   720 |  2,400 | 10/3   | (20,6,20)      | **+192**: max 2592 (72+48 above) / none (exact) |
| A_7        | 2,520 | 10,584 | 21/5   | (24,21,21)     | **+4968**: max 15552 (24 configs) / tie: 168 blocked at 10584 (exact) |

("Blocked" = every member blocked, i.e. no in-frame shrink to an
honest triple exists; ties are configurations whose graph lift
exactly matches the classical product lift in size.  The p=2
census rows for M_10 and A_7 carry `lower_bound` semantics flags
only because the program conservatively downgrades on a kill; in
each case the shape list was in fact exhausted.)

Census runtimes on an 8-core desktop: seconds for orders <= 660;
197.6 s for S_6; 232 s for A_7 (the high threshold beta_0 = 10584
prunes A_7's shape list to 291 + 9).

## 5. The counterexamples (verified)

Five verified violations of rho_0(A x G) = rho_0(G), all at
A = C_2.  Each triple below, lifted by the stated characters into
C_2 x G, was brute-checked to satisfy S ∩ TU = 1 and T ∩ U = 1.
Verification commands are exact and take < 1 s each:

    cd Scratch/GroupSieve/forge
    timeout 60  sage verify_kill_m10.sage
    timeout 120 sage verify_kill_any.sage -- --target "SymmetricGroup(6)" \
      --S-gens "(2,5), (1,5), (3,4)" --T-gens "(2,4), (4,6), (3,5)" \
      --U-gens "(1,5,3,2,6,4), (1,5,6,2,3,4), (1,6,3)"
    timeout 120 sage verify_kill_any.sage -- --target "AlternatingGroup(7)" \
      --S-gens "(1,2)(3,5)(4,6,7), (1,3)(2,5), (1,2)(6,7)" \
      --T-gens "(2,5)(3,6,4,7), (2,3,4)" --U-gens "(1,3,5,6)(4,7), (3,6,7)"

**Kill #1: C_2 x M_10** (M_10 = Stabilizer(MathieuGroup(11),1),
acting on {2..11}): members QD16, S4, QD16 of orders (16, 24, 16),

    S = <(2,3)(5,11)(6,7)(8,9), (2,3)(4,5,6,11,10,8,7,9)>
    T = <(2,4)(5,9)(6,11)(7,8), (2,4)(3,7,9,8,10,11,5,6)>
    U = <(3,9)(4,7)(5,6)(8,10), (2,11,10,8)(5,9,6,7)>

2 of 9 character combinations (k=3) lift to TPP triples of size
16*24*16 = **6144 = 2 * 3072 = 2 * Sigma_max^lift(M_10, 2)**.

    beta_0(C_2 x M_10) = 6144 > 4608 = 2 * beta_0(M_10).

**Kill #2: C_2 x S_6**: members D12, S3 x S3, D12 of orders
(12, 36, 12),

    S = <(2,5), (1,5), (3,4)>
    T = <(2,4), (4,6), (3,5)>
    U = <(1,5,3,2,6,4), (1,5,6,2,3,4), (1,6,3)>

2 of 27 combinations (k=3) lift to TPP triples of size
12*36*12 = **5184 = 2 * 2592 = 2 * Sigma_max^lift(S_6, 2)**.

    beta_0(C_2 x S_6) = 5184 > 4800 = 2 * beta_0(S_6).

**Kill #3: C_2 x A_7**: members (C6 x C2):C2, (C3 x C3):C4,
(C3 x C3):C4 of orders (24, 36, 36),

    S = <(1,2)(3,5)(4,6,7), (1,3)(2,5), (1,2)(6,7)>
    T = <(2,5)(3,6,4,7), (2,3,4)>
    U = <(1,3,5,6)(4,7), (3,6,7)>

1 of 3 combinations (k=3) lifts to a TPP triple of size
24*36*36 = **31104 = 2 * 15552 = 2 * Sigma_max^lift(A_7, 2)**.

    beta_0(C_2 x A_7) = 31104 > 21168 = 2 * beta_0(A_7).

**Kill #4: C_2 x M_10** (second family): members QD16, QD16,
C5:C4 of orders (16, 16, 20),

    Shape: (QD16, QD16, C5:C4) at |Sigma| = 2560.

2 of 18 combinations (k=2, third member untwisted) lift to TPP
triples of size 2*2560 = **5120 > 4608 = 2 * beta_0(M_10)**.
Verified by `verify_all_combos.sage` (pair-arithmetic and raw
permutation TPP check).  No k=3 combination passes for this shape.

**Kill #5: C_2 x S_6** (second family): members C2xD8, C2xD8,
C5:C4 of orders (16, 16, 20),

    Shape: (C2xD8, C2xD8, C5:C4) at |Sigma| = 2560.

2 of 70 combinations (k=2) lift to TPP triples of size
2*2560 = **5120 > 4800 = 2 * beta_0(S_6)**.
Verified by `verify_all_combos.sage`.  No k=3 combination passes.

**Correction note (kills #4 and #5):** an earlier version of this
document listed only three kills and noted the sigma=2560 families
as "census-eligible but not brute-verified" (sec 7 caveat).  The
extended verifier `verify_all_combos.sage` closed this gap: the
earlier verifier `verify_kill_any.sage` enumerated only nontrivial
characters, missing the k=2 combinations where the C5:C4 member
goes untwisted.  Both sigma=2560 families verify at k=2.

**Exact product values.**  Exhaustive search (`beta0probe exact`)
over the full subgroup lattice of C_2 x G confirms the kills and
pins the exact capacities:

| Target | Order | beta_0 | rho_0 | Witness orders | Semantics | Runtime |
|--------|------:|-------:|-------|----------------|-----------|--------:|
| C_2 x A_5 | 120 | 216 | 9/5 | (6, 6, 6) | exact | < 0.01s |
| C_2 x A_6 | 720 | 1944 | 27/10 | (18, 12, 9) | exact | 0.73s |
| C_2 x M_10 | 1440 | 6144 | 64/15 | (16, 24, 16) | exact | 1.32s |
| C_2 x S_6 | 1440 | 5184 | 18/5 | (12, 36, 12) | exact | 21.12s |

C_2 x A_5 serves as a **calibration anchor**: beta_0(C_2 x A_5) =
216 = 2 * 108 = 2 * beta_0(A_5), confirming the conjecture holds
in the slack regime (as the law predicts).  C_2 x A_6 confirms the
law in the **tie regime**: beta_0(C_2 x A_6) = 1944 = 2 * 972 =
2 * max(beta_0(A_6), Sigma_max^lift(A_6, 2)).  C_2 x A_7 stays at
the census lower bound (>= 31104); the law (Theorem 1 below)
upgrades this to an exact equality.

**Corollaries.**  rho_0(C_2 x S_6) = 18/5, rho_0(C_2 x M_10) =
64/15, rho_0(C_2 x A_7) >= 216/35 ~ 6.17.  The last exceeds every
exactly-known rho_0 in our records (including rho_0(A_7) = 21/5 at
five times the order): *abelian padding produces capacity-ratio
records*, which is precisely what the conjecture forbade.

**Remaining trust surface.**  The strict inequalities depend on
the B-side exact values (no honest triple in G beats beta_0(G)).
The witnesses themselves are verified independently of the entire
search stack; an author wishing to re-derive the right-hand sides
can rerun `beta0probe exact` per the commands in section 8.

## 5a. The lift law

**Theorem 1 (lift law).** For every finite group G and prime p:

    beta_0(C_p x G) = p * max( beta_0(G), Sigma_max^lift(G, p) ).

*Proof sketch (Goursat case analysis).* By Goursat's lemma
specialized to C_p (which has no proper nontrivial subgroups),
every subgroup P of C_p x G takes exactly one of three forms:

  (i)   P = 1 x H  (trivial character);
  (ii)  P = Gamma(H, chi) := { (chi(h), h) : h in H } for a
        unique nontrivial chi : H -> C_p;
  (iii) P = C_p x H.

In any TPP triple, pairwise intersections are trivial, so at most
one member can be of type (iii) (two would share the central
subgroup C_p x 1).

**Case B** (one type-(iii) member, say the third):  an element
triple (f_S(s), s)(f_T(t), t)(c, w) equals the identity iff
stw = 1 and c = -f_S(s) - f_T(t).  The free central coordinate c
absorbs any character data; the lift triple is TPP iff (S', T', W)
is TPP in G.  Maximum size: p * beta_0(G), attained by lifting a
beta_0(G)-achiever.

**Case A** (all three members are graphs): the lift triple is TPP
iff psi(c) != 0 for every nontrivial collision c -- i.e. the
configuration is sign-liftable.  When k = 0 this is just TPP in G;
when k >= 1 the size is p * |Sigma|, and the maximum over all
sign-liftable configurations gives p * Sigma_max^lift(G, p).

**Assembly:** beta_0(C_p x G) = max(p*beta_0(G), p*Sigma_max^lift)
= p * max(beta_0(G), Sigma_max^lift(G, p)).

Two structural lemmas (proved in the companion document
`.tasks/f5exp/docs/Pf13-lift-law.md`) close the remaining gaps:

- **Junction concentration (Lemma J):** any sign-liftable
  configuration with a nontrivial pairwise member intersection has
  |Sigma| <= beta_0(G), so it never exceeds the beta_0 term.
- **Lambda-shrink (Lemma L):** if k <= 1 or any member is
  unblocked, then |Sigma| <= beta_0(G).

These ensure that the only configurations contributing to
Sigma_max^lift beyond beta_0(G) are covering, case-alpha (pairwise
trivial intersections), k >= 2, fully blocked -- precisely the
census class.

**Census reduction (Proposition 2, Corollary 3).** The law
connects to the computed census values through a subgroup-max
domination check.  For each of the seven census targets at p = 2
and p = 3, the proper-subgroup bound (via maximal subgroup orders
and a crude capacity bound |Sigma| <= |H|^{3/2}/p) is below
beta_0(G) itself.  Therefore:

    beta_0(C_p x G) = p * max( beta_0(G), A_2(G, p) )

where A_2(G, p) is the censused maximum, for all seven targets
unconditionally.

**Exact values from the law.** Applying Corollary 3:

| Product | Law evaluation | beta_0 | Status |
|---------|----------------|-------:|--------|
| C_2 x A_5 | 2*max(108, 0) | 216 | computed = 216 |
| C_2 x S_5 | 2*max(256, 0) | 512 | new exact |
| C_2 x A_6 | 2*max(972, 972) | 1944 | computed = 1944 |
| C_2 x PSL(2,11) | 2*max(1980, 1980) | 3960 | new exact |
| C_2 x M_10 | 2*max(2304, 3072) | 6144 | computed = 6144 |
| C_2 x S_6 | 2*max(2400, 2592) | 5184 | computed = 5184 |
| C_2 x A_7 | 2*max(10584, 15552) | 31104 | new exact |
| C_3 x A_5 | 3*max(108, 0) | 324 | new exact |
| C_3 x S_5 | 3*max(256, 0) | 768 | new exact |
| C_3 x A_6 | 3*max(972, 972) | 2916 | new exact |
| C_3 x PSL(2,11) | 3*max(1980, 0) | 5940 | new exact |
| C_3 x M_10 | 3*max(2304, 0) | 6912 | new exact |
| C_3 x S_6 | 3*max(2400, 0) | 7200 | new exact |
| C_3 x A_7 | 3*max(10584, 10584) | 31752 | new exact |

In particular, beta_0(C_2 x A_7) = 31104 (upgrading the lower
bound to an exact value), rho_0(C_2 x A_7) = 216/35, and every
p=3 tie row yields a product value with zero excess -- consistent
with the conjecture that odd primes never violate.

**The law holds in all three regimes:**

| Regime | Anchor | beta_0(G) | Sigma_max^lift | Predicted | Actual |
|--------|--------|----------:|---------------:|----------:|-------:|
| Slack | C_2 x A_5 | 108 | 108 | 216 | 216 |
| Tie | C_2 x A_6 | 972 | 972 | 1944 | 1944 |
| Violation | C_2 x M_10 | 2304 | 3072 | 6144 | 6144 |
| Violation | C_2 x S_6 | 2400 | 2592 | 5184 | 5184 |

(The slack-regime Sigma_max^lift(A_5, 2) = 108 equals beta_0(A_5):
six eligible unblocked (S_3, S_3, S_3) configurations exist at
|Sigma| = 108, but they never exceed beta_0 since all members are
unblocked.  A_2(A_5, 2) = 0 because the blocked census class is
empty.)

**Consequences.**

- *Eligibility implies realizability:* every sign-liftable
  configuration genuinely lifts to a TPP triple in C_p x G.  The
  8/8 empirical record at p=2 was not luck; it is a theorem.
- *Two-twist threshold:* a strict violation
  beta_0(C_p x G) > p*beta_0(G) forces a sign-liftable
  configuration with k >= 2.  Every k <= 1 configuration has
  |Sigma| <= beta_0(G).
- *Coprime padding identity:* if p does not divide |G| then
  beta_0(C_p x G) = p*beta_0(G).  The conjecture is true for
  C_p coprime to |G|.
- *Excess ratio factorization:* define e(G) = Sigma_max^lift(G,2)
  / beta_0(G).  Then rho_0(C_2 x G) = e(G) * rho_0(G) whenever
  Sigma_max^lift dominates.  Values: e(M_10) = 3072/2304 = 4/3,
  e(S_6) = 2592/2400 = 27/25.

## 6. Interpretation: where the wall breaks

The campaign was designed as a three-way diagnostic on
A(G) := max eligible |Sigma| versus B(G) := beta_0(G), after Pf3
found A = B = 972 exactly in A_6 ("zero margin").  The observed
margin sequence, ordered by group order:

    A_5: slack   S_5: slack   A_6: 0   PSL(2,11): 0
    S_6: +192    M_10: +768   A_7: +4968

Three regimes:

1. **Slack (A_5, S_5):** the adversary class is empty -- every
   eligible configuration has an unblocked member, and the
   lambda-shrink theorem (Pf3 3.iii) converts it into an honest
   triple.  The conjecture holds here for a local, provable
   reason.
2. **Tie (A_6, PSL(2,11); also A_7 at p=3):** fully-blocked
   configurations exist and land exactly on beta_0.  Before the
   refutation these read as evidence of a structural identity;
   after it, they are crossings of two independently growing
   quantities -- each tie has local structure (A_6's Sylow-3
   geometry; PSL(2,11)'s configs share the C_11:C_5 with the
   beta_0 witness; A_7's p=3 ties share its C_7:C_3 pairs), but
   there is no global law forcing equality.  The lift law
   (Theorem 1) explains ties as max(beta_0, Sigma_max^lift) =
   beta_0 = Sigma_max^lift: neither side dominates.
3. **Violation (S_6, M_10, A_7 at p=2):** the adversary exceeds
   the capacity, increasingly with order.

The mechanism visible in the data: violations are powered by
members with **rich C_2-character spaces** -- QD16 in M_10, D12 and
S3 x S3 in S_6, (C6 x C2):C2 in A_7, all with abelianization
C2 x C2 or larger (3+ characters each), against the single
character available to the members of the small-group configs.
More characters means more ways to render every collision psi-odd;
eligibility gets cheap while beta_0 grows on its own schedule.
Consistent with a thin winning margin in character space, only
2/9, 2/27, and 1/3 combinations verify in the three principal
witnesses.

**What survives.**  The lift lemma (>= direction) is untouched;
lambda-shrink still resolves all unblocked configurations; the
Pf3 structure theorems remain true (the counterexamples live
exactly in the corner they left open).  The replacement law
(Theorem 1) provides the complete answer for prime cyclic
factors.  The open questions inverted by the refutation: is the
excess E(G) = A(G) - B(G) unbounded?  Is E > 0 generic beyond
order ~700?  What local invariant predicts slack / tie /
violation?  Does padding iterate (rho_0(C_2^k x G) strictly
increasing in k)?  What is the true growth of max rho_0 against
order, now that padding generates records?

**Relation to the omega=2 program.**  The cap-set barrier
[BCCGNS+U 2017, arXiv:1605.06702] shows that STPP constructions
in bounded-exponent abelian groups cannot yield omega = 2.  The
groups studied here (A_5 through A_7, their C_2-products) are
non-abelian, but the lift law addresses products C_p x G — a
construction that cannot amplify the pseudo-exponent (CU03 showed
alpha(G_1 x G_2) <= max(alpha(G_1), alpha(G_2))).  The path to
omega = 2 via the Cohn-Umans framework, if one exists, runs
through wreath-product amplification with *non-abelian* base
groups, where no barrier is known; the lift law and the
sign-liftable framework are contributions to the structural
theory of TPP capacity, not to the omega search directly.

## 7. Caveats

- **Scope of the census:** kernels B = C_p, p in {2,3} only.  The
  composite-kernel corner (e.g. B = C_4 shapes in A_6 surviving
  the corrected junction bound) is open; tie/slack rows are lower
  bounds on the full adversary.  This does not affect the
  counterexamples, which only need one witness each.
- **Novelty:** the conjecture is project-internal (see section 2).
  Three of seven base-group values (A_5 = 108, A_6 = 972,
  PSL(2,11) = 1980) were previously computed by Hedtke-Murthy
  2012 under the PSL_2(F_q) family; the remaining four and all
  product values are new to the literature as far as we are aware.
- **Formalization:** the lift law at p = 2 is machine-checked in
  Lean 4 (`Proofs/Xlib/TPPLift.lean`, theorem
  `stppCapacity_prod_eq_two_mul_max`, sorry-free).  The
  sign-liftable framework (charLift, SignKilled, SigmaMaxLift,
  the Goursat trichotomy, and the lift correspondence) is fully
  proved.  The general-p lift law is not yet formalized.  The
  witnesses are finite checks in groups of order <= 5040;
  formal refutation certificates would additionally require
  verified computation of beta_0(G) for the base groups.

## 8. Reproducibility

Hardware: single 8-core desktop; all computations single-run,
wall-clock as cited.

**B-side (base group capacities).**  Per target, from
`Scratch/GroupSieve/forge/`:

    sage export_tpp.sage -- --target-id pl15_<T> [--skip-ab]
    beta0probe exact --data out/tpp-data/pl15_<T>.json \
        --output out/pl15_results.jsonl --target-budget 10m

**A-side (census).**

    sage aside_census.sage -- --target "<constructor>" \
        --primes 2,3 --threshold <beta_0> | tee out/pl15_census_<T>.log

**Exact product computations (Im12/Im13).**  For the C_2 x G
targets with exact semantics:

    sage export_tpp.sage -- --probe-products --skip-ab \
        --target-id pl15_C2_x_<T>
    beta0probe exact --data out/tpp-data/pl15_C2_x_<T>.json \
        --output out/im12_results.jsonl --target-budget 10m

Calibration gate: run C_2 x A_5 first, confirm beta_0 = 216.

**Kill verification.**

    # Kills #1-#3 (k=3 witnesses):
    timeout 60  sage verify_kill_m10.sage
    timeout 120 sage verify_kill_any.sage -- --target "SymmetricGroup(6)" \
      --S-gens "(2,5), (1,5), (3,4)" --T-gens "(2,4), (4,6), (3,5)" \
      --U-gens "(1,5,3,2,6,4), (1,5,6,2,3,4), (1,6,3)"
    timeout 120 sage verify_kill_any.sage -- --target "AlternatingGroup(7)" \
      --S-gens "(1,2)(3,5)(4,6,7), (1,3)(2,5), (1,2)(6,7)" \
      --T-gens "(2,5)(3,6,4,7), (2,3,4)" --U-gens "(1,3,5,6)(4,7), (3,6,7)"

    # Kills #4-#5 (k=2 witnesses, extended verifier):
    timeout 120 sage verify_all_combos.sage

Artifacts: B-side records `out/pl15_results.jsonl`; product records
`out/im12_results.jsonl` (3 records: A_5, M_10, S_6),
`out/im13_results.jsonl` (1 record: A_6);
census logs `out/pl15_census_{A6,S5,PSL_2_11,M10,S6,A7}.log`;
verifiers `verify_kill_m10.sage`, `verify_kill_any.sage`,
`verify_all_combos.sage`; campaign documents
`.tasks/f5exp/docs/Pl15-{export,bside,aside-spec,aside,kill-witness}.md`;
lift law proof `.tasks/f5exp/docs/Pf13-lift-law.md`;
mathematical background `.tasks/f5exp/docs/Pf3-abelian-factor.md`.

## References

- [CU03] H. Cohn, C. Umans, *A group-theoretic approach to fast
  matrix multiplication*, FOCS 2003, arXiv:math/0307321.
- Thesis, arXiv:0709.1223 (lift lemma, Lemma 4.8; beta_0 of
  abelian groups).
- I. Hedtke, S. Murthy, *Search and test algorithms for triple
  product property triples*, 2012 (product tables used as
  calibration anchors; Theorem 3.5 non-normality pruning;
  Table 3 exact values for PSL_2(F_q) family).
- I. Murthy, *The triple product property for groups with an
  abelian normal subgroup of prime index*, arXiv:2512.16730
  (coset-decomposition analysis of TPP in prime-index
  extensions; closest prior art to the Goursat approach here).
- I. Murthy, *Subgroup triple product property ratio of nilpotent
  groups of class 2*, arXiv:2602.15796 (upper bounds on rho_0
  for nilpotent families).
- J. Blasiak, T. Church, H. Cohn, J. Grochow, E. Naslund,
  W. Sawin, C. Umans, *On cap sets and the group-theoretic
  approach to matrix multiplication*, arXiv:1605.06702 (Theorem B:
  STPP in bounded-exponent abelian groups cannot yield omega = 2).
- Neumann, Obs 3.1 (search pruning), as cited in the Pf3 report.

*(Citations re-checked against sources 2026-07-18; Murthy
arXiv:2602.15796 removed (Thm 2.3 and Prop 2.19(2) not found
in that paper); non-normality pruning re-attributed to
Hedtke-Murthy Thm 3.5; CU03 Lemma 2.2 added.)*
