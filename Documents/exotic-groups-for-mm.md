# Exotic Groups for Better Matrix Multiplication

## Definitions

*This is a section that should be re-homed.*

### Upper Bound

Let `G_{TPP}` denote an exotic, non-abelian
group that satisfies TPP, where "exotic" is
taken to mean:

* (possibly) of not Lie type
* (possibly) of passing the TPP filter

### Lower Bound

> Let `S \in VP` denote that "Hilbert-scheme
> search as a proof technique."

Corrective framing from LLM; to be verified:

```
▎ Does there exist a VP-computable polynomial family {D_n} such that D_n(c_ijk) = 0 iff the
▎ Hilbert-scheme smoothability search passes for the tensor with entries c_ijk?

So a more precise definition would be:

▎ Let S ∈ VP denote that the boolean output of the smoothability-based border apolarity test is
▎ decided by a polynomial family in VP — i.e., the test's pass/fail locus is cut out by
▎ polynomial-size arithmetic circuits.

The Chevalley result (from the flash agent earlier) tells us the pass/fail locus IS Zariski-closed
— polynomials cutting it out exist. The VP question is whether those polynomials have small
circuits.
```

## P, NP, and... VP?

## Bottom Up: Big Omega

### Case Study: `M_3`

## Naively probing the lower bound

┌───────────────────────┬───────┬───────────────┐
│         Group         │ Order │     Card      │
├───────────────────────┼───────┼───────────────┤
│ S₄                    │ 24    │ Or2, Oe1, Os1 │
├───────────────────────┼───────┼───────────────┤
│ A₄                    │ 12    │ Oe1           │
├───────────────────────┼───────┼───────────────┤
│ O (octahedral)        │ 24    │ Oe1           │
├───────────────────────┼───────┼───────────────┤
│ A₅                    │ 60    │ Oe1           │
├───────────────────────┼───────┼───────────────┤
│ PSL(2,7)              │ 168   │ Oe1, Od2      │
├───────────────────────┼───────┼───────────────┤
│ Hessian/ST25          │ 648   │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ Valentiner 3.A₆       │ 1080  │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ C₇:C₃                 │ 21    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ Heisenberg (C₃×C₃):C₃ │ 27    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ C₉:C₃                 │ 27    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ C₁₃:C₃                │ 39    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ C₇:C₉                 │ 63    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ (C₃×C₃×C₃):C₃         │ 81    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ (C₉×C₃):C₃            │ 81    │ Od2           │
├───────────────────────┼───────┼───────────────┤
│ C₂₇:C₃                │ 81    │ Od2           │
└───────────────────────┴───────┴───────────────┘

## Top Down: Big O

## Measurements of Abelian-ness

### Commutativity Degree

### Center Ratio

### Derived Length

### Nilpotency Class

## TPP Filtering of Non-Abelian Groups

The following pseudocode was generated after
several agents synthesized the approaches in
the following papers:

- [arXiv:1411.0848](https://arxiv.org/abs/1411.0848) — Eberhard, commuting probabilities of finite groups
- [arXiv:1009.5526](https://arxiv.org/abs/1009.5526) — Nath, commutativity degree survey
- [arXiv:1605.04829](https://arxiv.org/abs/1605.04829) — Cox, lamplighter groups and commutativity
- [arXiv:2605.02071](https://arxiv.org/abs/2605.02071) — Levit-Shwartz, higher commutativity spectrum
- [arXiv:2112.08681](https://arxiv.org/abs/2112.08681) — Burness-Guralnick-Moretó-Navarro, p-element commuting
- [arXiv:1011.2083](https://arxiv.org/abs/1011.2083) — Yadav, central quotient vs commutator subgroup
- [arXiv:1204.4641](https://arxiv.org/abs/1204.4641) — Kurdachenko-Shumyatsky, ranks of central factor
- [arXiv:2410.23034](https://arxiv.org/abs/2410.23034) — Guo, conjugacy ratio of abelian-by-cyclic groups
- [arXiv:1802.02194](https://arxiv.org/abs/1802.02194) — Burness-Liebeck-Shalev, length and depth of finite groups
- [arXiv:2411.18534](https://arxiv.org/abs/2411.18534) — Sabatini, stabilizers in permutation groups
- [arXiv:2509.17780](https://arxiv.org/abs/2509.17780) — Beike, p-groups with derived length 3
- [arXiv:1212.3113](https://arxiv.org/abs/1212.3113) — Burde, derived length and nildecomposable Lie algebras
- [arXiv:2602.15796](https://arxiv.org/abs/2602.15796) — Murthy, TPP for nilpotent groups of class 2
- [arXiv:2401.04277](https://arxiv.org/abs/2401.04277) — Moubarak, classification of free and free-like nilpotent groups
- [arXiv:2511.19494](https://arxiv.org/abs/2511.19494) — Dong-Fan-Zhong-Qiu, generating nilpotent groups
- [arXiv:math/0606605](https://arxiv.org/abs/math/0606605) — Aviño-Diaz, nilpotency class algorithm
- [arXiv:2512.16730](https://arxiv.org/abs/2512.16730) — Murthy, TPP for abelian-normal-subgroup-of-prime-index
- [arXiv:2204.03826](https://arxiv.org/abs/2204.03826) — Blasiak-Cohn-Grochow-Pratt-Umans, matrix multiplication via matrix groups

```
SCREEN_TPP_CANDIDATES(groups):
  survivors = []

  for G in groups:
      # === TIER 0: TRIVIAL REJECT ===

      if is_abelian(G):
          continue  # ρ₀ = ρ = 1 (Cohn-Umans Lemma 3.1)

      # === TIER 1: HARD REJECTS (cheap, from character table) ===

      # Reject 1: small p-group
      if is_p_group(G) and order(G) ≤ p⁴:
          continue  # ρ₀ = 1 (Murthy Prop 1.19)

      # Reject 2: character degrees = {1, p}
      if char_degrees(G) == {1, p}:
          continue  # ρ₀ = 1 (Murthy Thm 6.1)

      # Reject 3 (soft): cyclic commutator of order p
      if is_cyclic(derived_subgroup(G)) and order(derived_subgroup(G)) == p:
          deprioritize(G)  # ρ₀ ≤ p (Murthy Thm 4.1)
          continue

      # === TIER 2a: CENTER/INDEX REJECTS ===

      ci = central_index(G)          # |G:Z(G)|
      zs = center_size(G)            # |Z(G)|

      # Class-2 p-group with small central index
      if is_nilpotent_class2(G) and p² ≤ ci ≤ p³:
          continue  # ρ₀ = 1 (Murthy Thm 5.1)

      # === TIER 2b: ASYMPTOTIC PACKING BARRIERS (BCGPU) ===

      ng = min_nontrivial_irrep(G)   # n(G) — second-smallest irrep dim

      # n(G) growing as any positive power of |G| kills the packing bound.
      # For a family G_i: n(G_i) ≥ Ω(|G_i|^δ) for ANY fixed δ > 0
      # ⟹ |S||T||U| ≤ |G|^{3/2 - δ/2} + |G|, falls short of |G|^{3/2}.
      # (BCGPU Thm 3.3 / Cor 1.6)
      # For individual groups, flag when n(G)/log|G| is large relative
      # to known survivors (calibrate against Hedtke-Murthy ρ₀ > 1 examples).

      # Center barrier: |Z(G)| = Ω(|G|^δ) kills packing (BCGPU Cor 3.6)
      # Subgroup bound: |H₁||H₂||H₃| ≤ |G|^{3/2} / |Z(G)|^{1/2}

      # === TIER 3: SUBGROUP LATTICE REJECTS ===

      # Abelian normal subgroup of prime index p
      if has_abelian_normal_subgroup_of_prime_index(G):
          continue  # ρ₀ ≤ p²/(2p−1) (Murthy 2025 Thm 4.1)
                     # p-group case: ρ₀ = 1 (Murthy 2025 Cor 4.3)

      # === TIER 4: CAPACITY RANKING (survivors only) ===

      # Murthy ceiling: ρ₀(G) < √|G:Z(G)| for class-2 nilpotent
      ceiling = sqrt(ci)

      # Normalizer quality (BCGPU Thm 3.4):
      # |H₁||H₂||H₃| ≤ |G|^{3/2} / (s₁s₂s₃)^{1/4}
      # where sᵢ = |N(Hᵢ)|/|Hᵢ|. Self-normalizing (sᵢ = 1) is optimal.
      snr = best_self_normalizing_ratio(G)

      score = ceiling / snr  # high ceiling + near-self-normalizing = best

      survivors.append((G, score))

  return sorted(survivors, key=score, descending=True)
```

---

# mostly generated garbage that is somewhat helpful for planning

No matrix-of-linear-forms trick can prove
R̲(M₃) > 14 — yet CHL proves R̲(M₃) ≥ 17 because
the (111) test checks smoothability, which is
invisible to linear forms.

>> What are matrix-of-linear-forms tricks? Do
   they only matter for lower bound attacks?

>> What type of class of things does (111) belong?

>> Does proof of `R̲(M₃) ≥ 17` generalize into any
   usable Lean statements?

---

EGOW — Efremenko, Garg, Oliveira, Wigderson (arXiv:1710.09502). Proved unconditional limits on
rank-based methods (flattenings). The cactus barrier is the geometric explanation of why their
barrier holds.

FSV — Forbes, Shpilka, Volk (arXiv:1701.05328). Defined the algebraic natural proofs barrier: if
PIT derandomizes, no VP-computable polynomial can distinguish hard polynomials from VP.

GKSS — Grochow, Kumar, Saks, Saraf (arXiv:1701.01717). Independent, concurrent result to FSV —
same barrier from a different angle (meta-polynomials).

Cactus barrier — unconditional, geometric. Linear rank methods (flattenings/minors) can't prove
border rank > 6m−4 because the cactus variety fills the ambient space at that level. Named after
Buczyński's 2026 paper (arXiv:2602.11309) that gave the geometric explanation, building on EGOW.

Algebraic natural proofs barrier — conditional on PIT derandomization. Any efficiently computable
(VP) polynomial equation that vanishes on low-complexity polynomials also vanishes on most
polynomials — so it can't be a useful distinguisher. The arithmetic-circuit analog of
Razborov-Rudich natural proofs from boolean complexity.

---

Razborov-Rudich natural proofs (1997): In boolean complexity, a "natural proof" is a circuit lower
bound strategy that works by finding a property that (1) hard functions have and (2) random
functions don't — a "distinguisher." Razborov-Rudich showed that if one-way functions exist, no
such natural proof can separate P from NP, because a useful distinguisher would break
pseudorandomness. The algebraic natural proofs barrier (FSV/GKSS) is the same idea lifted to
arithmetic circuits: a VP-computable polynomial that vanishes on VP can't be a useful
distinguisher, conditional on PIT.

Arithmetic circuit: A DAG of + and × gates over a field k, with inputs being variables x₁,...,xₙ
or constants from k. It computes a polynomial. Size = number of gates. The determinant of an n×n
matrix is computable by a circuit of size poly(n). VP = the class of polynomial families
computable by poly-size circuits.

Border apolarity: A lower bound technique for border rank. Given a tensor T, its apolar ideal
Ann(T) is the set of "differential operators" that kill T. Border apolarity enumerates candidate
ideals I ⊆ Ann(T) with prescribed length r and tests whether any of them could witness a
border-rank-r decomposition. If none pass, R̲(T) > r. CHL's version adds the smoothability
requirement and the (210)/(120)/(111) rank filters.

The (111) test: The final and most powerful filter in CHL's pipeline. After a candidate ideal
passes the (210) and (120) tests (which check rank conditions on two of the three "directions" of
the tensor), the (111) test checks all three directions simultaneously. Concretely: does a certain
combined multiplication map have codimension ≥ r? It's called "(111)" because it uses degree 1 in
each of the three factor spaces (A, B, C). This is the step that requires smoothability and is
the mechanism that breaks the cactus barrier.

bcr(M₃) ≤ 14 < 17:
- bcr(M₃) ≤ 14: the border cactus rank of the 3×3 matrix multiplication tensor is at most 14.
Every 3×3×3 tensor has cactus rank ≤ 14 (Buczyński: the cactus variety fills the ambient space at
6(3)−4 = 14; Bernardi-Blekherman-Galazka: cr ≤ 2·C(7,1) = 14).
- 17 ≤ R̲(M₃): the border rank of M₃ is at least 17 (CHL's theorem, the result the campaign
reproduces).
- The gap 14 < 17 means M₃'s border decompositions must use non-smoothable limiting schemes at
length 14, but border rank requires smoothable ones — so you need more terms. The (111) test
detects this gap because it enforces smoothability. Linear rank methods cannot, because they can't
distinguish smooth from non-smooth schemes.

---

The following was in the context of using
smaller groups to blow up to larger groups
that might yield more interesting structures
to evaluate and generalize?

"Independent value of TPP upward inheritance"

```
Positive theorem: dead end. Wreath products already ARE the "grow it" theory — capacity multiplies
under wreath/direct powers. A general embedding bound would be weaker than what exists, and
barrier results (Blasiak-Cohn) constrain capacity so sharply that any true f(ρ₀, [H:G]) is
essentially trivial.

Negative characterization: the real value. A theorem stating when and why embedding fails to
preserve capacity would explain why wreath products are special. That's citable in the
Hedtke-Murthy / Blasiak-Cohn line.

Recommended first step: compute ρ₀ for small groups and their overgroups using Sager/GAP. Will
likely kill the positive theorem in an afternoon and surface the negative one.
```

---


This is not totally correct, but it
is a good depiction of what to look
at next given my personal notes are
more complete and more correct:

```
●   BINI (1979): the foundation
    ═══════════════════════════
    r
    Σ  aᵢ(ε) ⊗ bᵢ(ε) ⊗ cᵢ(ε)  =  εʰ·T  +  O(εʰ⁺¹)
    i=1

    "How few ε-polynomial sticks can sum to T
     at the εʰ coefficient?"
    Answer = border rank R̲(T).
    This is the OBJECT. Everything branches from it.

            ┌─────────────────────────────────┐
            │          BORDER RANK            │
            │     R̲(T) = min r such that      │
            │     the ε-equation has a        │
            │     solution                    │
            └───────────┬─────────────────────┘
                        │
            ┌───────────┴───────────┐
            │                       │
      UPPER BOUNDS              LOWER BOUNDS
      "find solutions"          "prove no solution exists"
            │                       │
            │                       │
    ┌───────┴────────┐      ┌──────┴───────────┐
    │                │      │                  │
    ORBITS          TPP     EQUATIONS      APOLARITY
    (Grochow-       (Cohn-  (flattenings,  (CHL border
     Moore)          Umans)  Koszul)        apolarity)
    │                │      │                  │
    │                │      │                  │
    ▼                ▼      ▼                  ▼

    Construct r     Embed    Write poly      Search Hilbert
    sticks via      M_n in   D(c_ijk)       scheme for
    group orbit     C[G]     that vanishes   smoothable ideal
    of a seed       via TPP  on σ_r          in Ann(T)
    │                │      │                  │
    │                │      │                  │
    STRASSEN M₂     ω BOUNDS BARRIERED        R̲(M₃) ≥ 17
    = 1 seed +      ω ≤ 2.37  cactus:6m-4     │
    S₃ orbit        (CW/laser) nat proofs:VP  BREAKS BARRIERS
    = 7 sticks      abelian    GCT:mult       bcr(M₃)≤14 < 17
    (optimal)       groups                     │
    │               KILLED                     smoothability
    │               │                          = non-VP (HMPW)
    M₃: S₄ orbit   need NON-                  = non-natural
    = 25 sticks     ABELIAN                    (CHL remark)
    (not optimal,   groups
    Laderman=23)    │
    │               THE SEARCH
    │               ┌──────────────────┐
    │               │ 15 non-abelian   │
    └───────────────│ groups tested    │
      same groups,  │ for lower bounds │
      different     │ (Or2/Oe1/Od2)    │
      question      │                  │
                    │ REPURPOSE for    │
                    │ upper bounds:    │
                    │ TPP pre-filter + │
                    │ Aut(G) pruning + │
                    │ capacity ranking │
                    └──────────────────┘
                             │
                    ┌────────┴────────┐
                    │   THE 2×2       │
                    │                 │
                    │  S ∈ VP?  G_TPP?│
                    │  (row)    (col) │
                    │                 │
                    │ bottom-right =  │
                    │ where history   │
                    │ gets made       │
                    └─────────────────┘
```

This is a slightly better version but
still kinda wrong at the bottom TWO QUESTIONS:

```
●   BORDER RANK (the object both sides argue about)
    ═══════════════════════════════════════════════
    Defined by Bini (1979). Two equivalent faces:

    ┌──────────────────────┐    ┌──────────────────────┐
    │    ALGEBRAIC FACE    │ ≡  │    GEOMETRIC FACE    │
    │                      │    │                      │
    │  r                   │    │                      │
    │  Σ aᵢ(ε)⊗bᵢ(ε)⊗cᵢ(ε) │    │  T ∈ σ_r(Seg) ?      │
    │  = εʰ·T + O(εʰ⁺¹)    │    │  (Zariski closure    │
    │                      │    │   of rank-≤r set)    │
    │  "can I BUILD it?"   │    │  "does T LIVE here?" │
    └──────────┬───────────┘    └──────────┬───────────┘
               │                           │
       UPPER BOUNDS                 LOWER BOUNDS
       (construct solutions)        (prove impossibility)
               │                           │
       ┌───────┴────────┐          ┌───────┴────────────┐
       │                │          │                    │
     ORBITS            TPP       EQUATIONS          APOLARITY
     (Grochow-Moore)   (Cohn-Umans)  (flattenings)  (CHL)
       │                │          │                    │
       │                │          │                    │
     pick seed,       embed M_n   write poly D        search Hilbert
     let group         in C[G]    that vanishes        scheme for
     generate          via subset  on σ_r              smoothable
     the sticks        triples                         ideal ⊆ Ann(T)
       │                │          │                    │
       │                │          │                    │
     SPECIFIC r        ω BOUNDS    BARRIERED            BARRIER-
     for fixed n       for all n   ┌─────────┐         BREAKING
       │                │          │cactus   │          │
     M₂: S₃→7✓        ω ≤ 2.37     │nat proof│     R̲(M₃) ≥ 17
     M₃: S₄→25        (CW+laser)   │GCT mult │     bcr≤14 < 17
     M₄: A₅→61         │           └─────────┘     smoothability
       │                │               │          = non-VP (HMPW)
     suboptimal        need             │          = non-natural
     for n>2           NON-ABELIAN      all three      (Bini remark
       │               groups           block at       in CHL)
       │                │               n² floor
       │                │                              │
       │          THE GAP                              │
       │          no group found                       │
       │          beyond wreath                  only known method
       │          products                       past the barriers
       │                │                              │
       └────────────────┴──────────────────────────────┘
                        │
                THE CAMPAIGN'S 15
                NON-ABELIAN GROUPS
                ┌────────────────────────────────────┐
                │ tested for LOWER bounds (Or2/Oe1)  │
                │ → ALL-INFEASIBLE for rank decomp   │
                │                                    │
                │ untested for UPPER bounds (TPP)    │
                │ → pre-filter designed, ready to    │
                │   search with Aut(G) pruning       │
                └────────────────┬───────────────────┘
                                 │
                        THE TWO QUESTIONS
                  ┌──────────────┴──────────────┐
                  │                             │
            Is S ∈ VP?                   Does G_TPP exist?
            (smoothability               (non-abelian group
             class of proofs              achieving ω = 2)
             non-VP under
             robustness—HMPW)            open, searchable
                  │                             │
                  │         ┌───────────────────┘
                  │         │
                  ▼         ▼
           ┌──────────────────────┐
           │     BOTTOM RIGHT     │
           │                      │
           │  S not VP (proven    │
           │  under robustness)   │
           │         +            │
           │  no G_TPP found      │
           │         =            │
           │  lower bounds can    │
           │  scale, upper bound  │
           │  program stuck       │
           │         =            │
           │  ω > 2 is provable   │
           └──────────────────────┘
```
