import Xlib.TPP
import Xlib.CharDegrees

/-!
# Cohn–Umans Theorem 4.1: the capacity bound on `ω`

This file formalizes the central theorem of the Cohn–Umans group-theoretic
approach to fast matrix multiplication [math/0307321, `theorem:bound`,
CU.tex:603–609]: the **pseudo-exponent capacity bound**

  `|G|^{ω/α(G)} ≤ Σᵢ dᵢ^ω`,

equivalently, writing `β(G) = |S|·|T|·|U|` for an optimal TPP triple (so that
`β(G) = |G|^{3/α(G)}`),

  `β(G)^{ω/3} ≤ Σᵢ dᵢ^ω = D_ω(G)`.

This is *the* edge crossing from group theory to complexity theory: it converts
"`G` has a good TPP triple (large `β(G)`)" into "`ω ≤ X`".

## The two foundational debts

This is a **sorry-skeleton**: the *type-level statements* are the deliverable.
Two distinct foundations are missing from Mathlib and are isolated here:

1. **The matrix-multiplication exponent `ω` itself** (`matrixExponent`). Its
   genuine definition is the infimum of feasible exponents of bilinear matrix
   multiplication, which requires *tensor rank / bilinear complexity* — entirely
   **absent from Mathlib**. We introduce `ω` and its two elementary bounds
   `2 ≤ ω ≤ 3` as **axioms** (`matrixExponent`, `two_le_matrixExponent`,
   `matrixExponent_le_three`) — the standard, importable, `#print axioms`-auditable
   idiom for a constant not yet definable but reasoned about via stated bounds. A
   future task landing bilinear complexity replaces these three axioms.

2. **The proof of Theorem 4.1.** Its proof (CU.tex:621–666) embeds an
   `⟨n,m,p⟩` matrix product into `ℂ[G]`, transports through the *indexed*
   Wedderburn decomposition (the `Pf4` debt, `Xlib.CharDegrees.charDegrees`),
   and invokes the tensor-rank inequalities `(n'm'p')^{ω/3} ≤ R(⟨n',m',p'⟩)`
   and `R(⟨k,k,k⟩) ≤ C k^{ω+ε}` (Bürgisser–Clausen–Shokrollahi 15.5/15.1) — none
   of which exist in Mathlib. The statement is `sorry`d.

Everything *between* these debts is built on the (`sorry`-free) TPP/character-
degree API of `Xlib.TPP` and `Xlib.CharDegrees` and **proved here in full**: the
abelian case `α(G) = 3` (`pseudoExponent_eq_three_of_commGroup`), the
equivalence of the `β`- and pseudo-exponent forms of Theorem 4.1
(`card_rpow_le_charDegreeSumReal` derives from `capacity_rpow_le_charDegreeSumReal`
via the identity `β(G) = |G|^{3/α(G)}`), the `D₃` certificate
(`betaExceedsD3_certifies_subcubic` derives from Theorem 4.1), and the `D₃`
threshold equivalence (`subcubic_certificate_iff`). The only remaining `sorry`s
are Theorem 4.1 itself (debt 2) and the universal lower bound `α(G) > 2`.

## Main definitions

* `Xlib.CUCapacity.matrixExponent` — `ω`, the exponent of matrix multiplication.
  **Foundation axiom #1** (tensor rank absent from Mathlib).
* `Xlib.CUCapacity.pseudoExponent` — `α(G) = 3·log|G| / log β(G)`, the
  Cohn–Umans pseudo-exponent (`theorem:bound` preamble, CU.tex:460–467).
* `Xlib.CUCapacity.BetaExceedsD3` — the `D₃` threshold predicate
  `D₃(G) < β(G)` (CU Question `fundamentalq`, CU.tex:774–781). **Correct as
  stated, but currently junk-valued**: its `D₃(G)` side is computed from the
  `sorry`d `Xlib.CharDegrees.charDegrees`, so its truth value is undetermined
  until that upstream `sorry` lands.

## Main results

* `Xlib.CUCapacity.capacity_rpow_le_charDegreeSumReal` — **(`sorry`, debt 2)** CU
  Theorem 4.1 in `β`-form: `β(G)^{ω/3} ≤ D_ω(G)`.
* `Xlib.CUCapacity.card_rpow_le_charDegreeSumReal` — **(proved from the `β`-form)**
  the equivalent pseudo-exponent form `|G|^{ω/α(G)} ≤ D_ω(G)`.
* `Xlib.CUCapacity.card_rpow_three_div_pseudoExponent` — **(proved,
  `sorry`-free)** the identity `β(G) = |G|^{3/α(G)}` (the bridge between the two
  forms), via `Real.rpow_logb`.
* `Xlib.CUCapacity.pseudoExponent_eq_three_of_commGroup` — **(proved,
  `sorry`-free)** `α(G) = 3` for a nontrivial commutative `G` (the abelian
  barrier, via `Xlib.TPP.tppCapacity_eq_card`).
* `Xlib.CUCapacity.two_lt_pseudoExponent` — **(`sorry`)** `α(G) > 2` for every
  nontrivial finite `G` (CU pseudo-exponent lemma, CU.tex:478–500).
* `Xlib.CUCapacity.betaExceedsD3_certifies_subcubic` — **(proved from Theorem
  4.1)** the `D₃` certificate: `D₃(G) < β(G) ⟹ ω < 3` (a single group certifies
  `ω < 3`). Correct as stated, but **conditional on the `charDegrees` `sorry`**
  through its junk-valued hypothesis `BetaExceedsD3 G`; the inherited debt is the
  Theorem 4.1 `sorry` *and* the `charDegrees` `sorry`.
* `Xlib.CUCapacity.subcubic_certificate_iff` — **(proved, `sorry`-free body)** a
  *trivial arithmetic unfolding*: the Theorem 4.1 expression evaluated at exponent
  `3` is violated iff `D₃(G) < β(G)`. This is `not_le` after `3/3 = 1` and
  `rpow_one` — it restates `BetaExceedsD3` in negated-bound shape and is **not**
  the substantive "rules out `ω = 3`" equivalence (which would require Theorem 4.1,
  debt 2); it makes no claim about `ω`. Its `sorryAx` dependency is inherited
  *only* from the upstream `charDegrees` debt.

## References

* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, [arXiv:math/0307321] (`theorem:bound`, CU.tex:603–609;
  pseudo-exponent definition CU.tex:460–467; `α > 2` and `α = 3` for abelian
  CU.tex:478–500; the `D₃` threshold question `fundamentalq` CU.tex:774–781).
* P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity Theory*
  (Prop. 15.1, 15.5: the tensor-rank facts the proof of Theorem 4.1 needs).
-/

open scoped BigOperators

namespace Xlib.CUCapacity

open Xlib.TPP Xlib.CharDegrees

/-! ### The matrix-multiplication exponent `ω` (foundation axiom #1)

`ω` is **not definable in current Mathlib** — its genuine definition is the
infimum of feasible exponents of bilinear matrix multiplication, requiring
*tensor rank / bilinear complexity* which Mathlib lacks entirely. Rather than a
`noncomputable def … := sorry` (which would poison `ω` with the `sorryAx`
dependency and force every bound to be a `sorry` as well), we introduce `ω` and
its two elementary bounds as **axioms**: this is the standard idiom for "a
constant we cannot yet define but must reason about with stated bounds", keeps
the constant importable with no `sorry` noise, makes the bounds first-class
facts downstream, and is cleanly auditable via `#print axioms`. A future task
landing bilinear complexity replaces these three axioms with a genuine `def` and
two theorems. -/

/-- **The exponent of matrix multiplication** `ω`.

`ω` is the infimum of all `c` such that two `n × n` matrices can be multiplied
with `O(n^{c+ε})` arithmetic operations for every `ε > 0`; equivalently the
infimum of feasible exponents of the matrix-multiplication tensor `⟨n,n,n⟩`.

**Foundation axiom** (tensor rank / bilinear complexity absent from Mathlib).
This is the single real constant the capacity bound (`theorem:bound`) compares
against; downstream files (`Xlib.STPPWreath`, the `Dᵣ` sieve) reference it by
this name. -/
axiom matrixExponent : ℝ

@[inherit_doc] scoped notation "ω" => matrixExponent

/-- **`2 ≤ ω`.** Multiplying two `n × n` matrices must read all `2n²` input
entries, so the exponent is at least `2`. Elementary mathematically, but
unprovable without the bilinear-complexity foundation that *defines* `ω`;
recorded as a **foundation axiom** so downstream files consume it by name. -/
axiom two_le_matrixExponent : 2 ≤ ω

/-- **`ω ≤ 3`.** Schoolbook matrix multiplication uses `O(n³)` operations, so the
exponent is at most `3`. A **foundation axiom** (same foundation as
`two_le_matrixExponent`). -/
axiom matrixExponent_le_three : ω ≤ 3

/-- `0 ≤ ω`, an immediate consequence of `2 ≤ ω`; convenient for the `rpow`
positivity side-conditions in the capacity bound. -/
theorem matrixExponent_nonneg : 0 ≤ ω :=
  le_trans (by norm_num) two_le_matrixExponent

/-! ### The Cohn–Umans pseudo-exponent `α(G)` -/

/-- **The Cohn–Umans pseudo-exponent** `α(G)` [math/0307321, CU.tex:460–467].

By definition `α(G)` is the minimum of `3·log|G| / log(nmp)` over all TPP triples
realizing `⟨n,m,p⟩` with `nmp > 1`. Since `3·log|G| / log(nmp)` is *decreasing*
in `nmp` (for `|G| ≥ 1`), the minimum is attained at the **maximal** `nmp`, which
is exactly the TPP capacity `β(G) = tppCapacity G`. Hence the closed form used
here:

  `α(G) = 3·log|G| / log β(G)`.

This is `noncomputable` (real `log` and `tppCapacity` are). For the trivial group
Cohn–Umans set `α = 3` by convention; here `tppCapacity = |G| = 1` gives
`log 1 = 0` and the expression is the junk value `0/0 = 0`, so all theorems below
carry a `Nontrivial G` hypothesis (equivalently `2 ≤ |G|`), matching the paper's
"non-trivial finite group". -/
noncomputable def pseudoExponent (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] : ℝ :=
  3 * Real.log (Fintype.card G) / Real.log (tppCapacity G)

/-! ### The abelian barrier: `α(G) = 3` for commutative `G` (proved) -/

/-- **The abelian pseudo-exponent barrier:** for a *nontrivial* commutative
finite group, `α(G) = 3` [math/0307321, CU.tex:497–499].

This is the base negative result of the whole program: abelian groups cannot
beat `ω = 3`. The proof chains the abelian capacity barrier
`Xlib.TPP.tppCapacity_eq_card` (`β(G) = |G|`) with `log|G| ≠ 0` (from `|G| ≥ 2`),
collapsing `3·log|G| / log|G|` to `3`. Commutativity enters *only* through
`tppCapacity_eq_card`; everything else is real-arithmetic. -/
theorem pseudoExponent_eq_three_of_commGroup {H : Type*} [CommGroup H] [Fintype H]
    [DecidableEq H] [Nontrivial H] : pseudoExponent H = 3 := by
  have hcard : (1 : ℕ) < Fintype.card H := Fintype.one_lt_card
  have hlog_pos : 0 < Real.log (Fintype.card H) := by
    apply Real.log_pos
    exact_mod_cast hcard
  have hlog_ne : Real.log (Fintype.card H) ≠ 0 := ne_of_gt hlog_pos
  rw [pseudoExponent, tppCapacity_eq_card, mul_div_assoc, div_self hlog_ne, mul_one]

/-! ### Pairwise product bounds for the universal lower bound

The lower bound `α(G) > 2` (below) rests on the three *pairwise* product bounds
of Cohn–Umans [math/0307321, CU.tex:487–494]: a TPP triple `(S, T, U)` satisfies
`|S|·|T| ≤ |G|`, with strict inequality unless `|U| = 1`. We package both into a
single inequality `|S|·|T| + |U| ≤ |G| + 1` (`pairSumBound`): the injective
product map `(x, y) ↦ x·y⁻¹` embeds `S ×ˢ T` into `G` with image disjoint from
the translate `s₀·(Q(U) \ {1})·t₀⁻¹` of the punctured left quotient set, which
has `≥ |U| - 1` elements. Since `TripleProductProperty` is the *left*-quotient
convention while CU use the right, the two permutation helpers `tpp_perm_swap23`
and `tpp_perm_rotate` supply the cyclic/reflected orderings needed to apply the
`(S, T)` bound to the `(S, U)` and `(T, U)` pairs. -/

section PairwiseBounds

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
/-- **Permutation invariance (transpose the last two):** the (left) TPP is
symmetric under swapping `T` and `U`. Proved through the quotient-set
characterization `tripleProductProperty_iff_leftQuot`: a relation
`q₁ q₂ q₃ = 1` with `q₂ ∈ Q(U)`, `q₃ ∈ Q(T)` inverts and cyclically rotates to
`q₁⁻¹ q₃⁻¹ q₂⁻¹ = 1` in the `(S, T, U)` order, where the original TPP applies. -/
theorem tpp_perm_swap23 {S T U : Finset G} (h : TripleProductProperty S T U) :
    TripleProductProperty S U T := by
  rw [tripleProductProperty_iff_leftQuot] at h ⊢
  intro q₁ hq₁ q₂ hq₂ q₃ hq₃ heq
  have hcyc : q₂ * q₃ * q₁ = 1 := by
    calc q₂ * q₃ * q₁ = q₁⁻¹ * (q₁ * q₂ * q₃) * q₁ := by group
      _ = q₁⁻¹ * 1 * q₁ := by rw [heq]
      _ = 1 := by group
  have hkey : q₁⁻¹ * q₃⁻¹ * q₂⁻¹ = 1 := by
    calc q₁⁻¹ * q₃⁻¹ * q₂⁻¹ = (q₂ * q₃ * q₁)⁻¹ := by group
      _ = (1 : G)⁻¹ := by rw [hcyc]
      _ = 1 := inv_one
  obtain ⟨e1, e3, e2⟩ := h q₁⁻¹ (inv_mem_leftQuot hq₁) q₃⁻¹ (inv_mem_leftQuot hq₃)
    q₂⁻¹ (inv_mem_leftQuot hq₂) hkey
  exact ⟨inv_eq_one.mp e1, inv_eq_one.mp e2, inv_eq_one.mp e3⟩

omit [Fintype G] in
/-- **Permutation invariance (cyclic rotation):** the (left) TPP is symmetric
under the cyclic rotation `(S, T, U) ↦ (T, U, S)`. A relation `q₁ q₂ q₃ = 1`
with `q₁ ∈ Q(T)`, `q₂ ∈ Q(U)`, `q₃ ∈ Q(S)` rotates to `q₃ q₁ q₂ = 1` in the
`(S, T, U)` order, where the original TPP applies. -/
theorem tpp_perm_rotate {S T U : Finset G} (h : TripleProductProperty S T U) :
    TripleProductProperty T U S := by
  rw [tripleProductProperty_iff_leftQuot] at h ⊢
  intro q₁ hq₁ q₂ hq₂ q₃ hq₃ heq
  have hcyc : q₃ * q₁ * q₂ = 1 := by
    calc q₃ * q₁ * q₂ = (q₁ * q₂)⁻¹ * (q₁ * q₂ * q₃) * (q₁ * q₂) := by group
      _ = (q₁ * q₂)⁻¹ * 1 * (q₁ * q₂) := by rw [heq]
      _ = 1 := by group
  obtain ⟨e3, e1, e2⟩ := h q₃ hq₃ q₁ hq₁ q₂ hq₂ hcyc
  exact ⟨e1, e2, e3⟩

/-- **The pairwise sum-product bound** [math/0307321, CU.tex:487–494]: for a TPP
triple `(S, T, U)` of nonempty finsets, `|S|·|T| + |U| ≤ |G| + 1`.

The product map `f(x, y) = x·y⁻¹` is injective on `S ×ˢ T` (if `x₁ y₁⁻¹ = x₂ y₂⁻¹`
then `x₂⁻¹ x₁ = y₂⁻¹ y₁ ∈ Q(S) ∩ Q(T) = {1}` by `leftQuot_inter_ST`), so its
image `Im` has `|S|·|T|` elements. Choosing base points `s₀ ∈ S`, `t₀ ∈ T`, the
translate `W = s₀·(Q(U) \ {1})·t₀⁻¹` has `|Q(U)| - 1 ≥ |U| - 1` elements and is
disjoint from `Im`: a common element yields `q₁ q₂ q⁻¹ = 1` with
`q₁ = s₀⁻¹ x ∈ Q(S)`, `q₂ = y⁻¹ t₀ ∈ Q(T)`, `q ∈ Q(U) \ {1}`, contradicting the
TPP via `tripleProductProperty_iff_leftQuot`. Disjoint union in `G` gives the
bound. Taking `|U| ≥ 1` recovers `|S|·|T| ≤ |G|`; `|U| ≥ 2` makes it strict. -/
theorem pairSumBound {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    S.card * T.card + U.card ≤ Fintype.card G + 1 := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨t₀, ht₀⟩ := hT
  -- the injective product image `Im = { x * y⁻¹ : x ∈ S, y ∈ T }`
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2⁻¹) (↑(S ×ˢ T) : Set (G × G)) := by
    intro a ha b hb hab
    obtain ⟨x, y⟩ := a
    obtain ⟨x', y'⟩ := b
    rw [Finset.mem_coe, Finset.mem_product] at ha hb
    simp only at hab
    have hq : x'⁻¹ * x = y'⁻¹ * y := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y⁻¹) * y := by group
        _ = x'⁻¹ * (x' * y'⁻¹) * y := by rw [hab]
        _ = y'⁻¹ * y := by group
    have hmem : x'⁻¹ * x ∈ leftQuot S ∩ leftQuot T := Finset.mem_inter.mpr
      ⟨mem_leftQuot.mpr ⟨x, ha.1, x', hb.1, rfl⟩,
       by rw [hq]; exact mem_leftQuot.mpr ⟨y, ha.2, y', hb.2, rfl⟩⟩
    rw [leftQuot_inter_ST h ⟨s₀, hs₀⟩ ⟨t₀, ht₀⟩ hU, Finset.mem_singleton] at hmem
    have hxx : x = x' := (inv_mul_eq_one.mp hmem).symm
    have hyy : y = y' := (inv_mul_eq_one.mp (hq.symm.trans hmem)).symm
    simp only [Prod.mk.injEq]
    exact ⟨hxx, hyy⟩
  have hIm_card : ((S ×ˢ T).image (fun p : G × G => p.1 * p.2⁻¹)).card
      = S.card * T.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
  -- the disjoint translate `W = s₀ * (Q(U) \ {1}) * t₀⁻¹`
  have hg_inj : Function.Injective (fun q : G => s₀ * q * t₀⁻¹) := by
    intro a b hab
    simp only at hab
    exact mul_left_cancel (mul_right_cancel hab)
  have hW_card : (((leftQuot U).erase 1).image (fun q : G => s₀ * q * t₀⁻¹)).card
      = ((leftQuot U).erase 1).card := Finset.card_image_of_injective _ hg_inj
  have hdisj : Disjoint ((S ×ˢ T).image (fun p : G × G => p.1 * p.2⁻¹))
      (((leftQuot U).erase 1).image (fun q : G => s₀ * q * t₀⁻¹)) := by
    rw [Finset.disjoint_left]
    intro w hwIm hwW
    rw [Finset.mem_image] at hwIm hwW
    obtain ⟨⟨x, y⟩, hxy, hw1⟩ := hwIm
    rw [Finset.mem_product] at hxy
    simp only at hw1
    obtain ⟨q, hqE, hw2⟩ := hwW
    rw [Finset.mem_erase] at hqE
    obtain ⟨hqne, hqU⟩ := hqE
    have hq1 : s₀⁻¹ * x ∈ leftQuot S := mem_leftQuot.mpr ⟨x, hxy.1, s₀, hs₀, rfl⟩
    have hq2 : y⁻¹ * t₀ ∈ leftQuot T := mem_leftQuot.mpr ⟨t₀, ht₀, y, hxy.2, rfl⟩
    have hq3 : q⁻¹ ∈ leftQuot U := inv_mem_leftQuot hqU
    have hxyq : x * y⁻¹ = s₀ * q * t₀⁻¹ := by rw [hw1, ← hw2]
    have hprod12 : (s₀⁻¹ * x) * (y⁻¹ * t₀) = q := by
      calc (s₀⁻¹ * x) * (y⁻¹ * t₀) = s₀⁻¹ * (x * y⁻¹) * t₀ := by group
        _ = s₀⁻¹ * (s₀ * q * t₀⁻¹) * t₀ := by rw [hxyq]
        _ = q := by group
    have hprod : (s₀⁻¹ * x) * (y⁻¹ * t₀) * q⁻¹ = 1 := by rw [hprod12]; group
    obtain ⟨_, _, hq3eq⟩ := (tripleProductProperty_iff_leftQuot.mp h)
      (s₀⁻¹ * x) hq1 (y⁻¹ * t₀) hq2 q⁻¹ hq3 hprod
    exact hqne (inv_eq_one.mp hq3eq)
  -- counting: the disjoint union sits inside `G`
  have hunion : (((S ×ˢ T).image (fun p : G × G => p.1 * p.2⁻¹)) ∪
      (((leftQuot U).erase 1).image (fun q : G => s₀ * q * t₀⁻¹))).card
      ≤ Fintype.card G := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdisj, hIm_card, hW_card] at hunion
  have hUcard : ((leftQuot U).erase 1).card + 1 = (leftQuot U).card :=
    Finset.card_erase_add_one (one_mem_leftQuot hU)
  have hUge : U.card ≤ (leftQuot U).card := card_le_card_leftQuot hU
  omega

end PairwiseBounds

/-! ### The universal lower bound: `α(G) > 2` (proved) -/

/-- **The universal pseudo-exponent lower bound:** every nontrivial finite group
has `α(G) > 2` [math/0307321, CU.tex:478–500].

CU proof: let `(S, T, U)` be a TPP triple *realizing* `β(G) = tppCapacity G`, so
`β(G) = |S|·|T|·|U|` and, `G` being nontrivial, `β(G) ≥ |G| ≥ 2 > 1`. The three
pairwise sum-product bounds (`pairSumBound`, applied through the permutation
helpers `tpp_perm_swap23`/`tpp_perm_rotate` to reach the `(S,U)` and `(T,U)`
pairs) give `|S|·|T| + |U| ≤ |G| + 1` and cyclically. Since `β(G) > 1` at least
one of `|S|, |T|, |U|` is `≥ 2`, making the corresponding pairwise product bound
*strict*; multiplying the three (via `(|S||T||U|)² = (|S||T|)(|S||U|)(|T||U|)`)
yields the strict cube inequality `β(G)² < |G|³` in `ℕ`. Casting to `ℝ` and
applying `log`-monotonicity (`Real.log_lt_log`, `Real.log_pow`) converts
`β(G)² < |G|³` to `2·log β(G) < 3·log|G|`, i.e. `2 < 3·log|G| / log β(G) = α(G)`
(`lt_div_iff₀`, using `log β(G) > 0`). -/
theorem two_lt_pseudoExponent (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] [Nontrivial G] :
    2 < pseudoExponent G := by
  classical
  -- A TPP triple `(S, T, U)` realizing the capacity `β(G) = |S|·|T|·|U|`.
  have hne : (tppTriples G).Nonempty :=
    ⟨(Finset.univ, {1}, {1}), mem_tppTriples.mpr tpp_trivial⟩
  obtain ⟨p, hpmem, hpsup⟩ :=
    Finset.exists_mem_eq_sup (tppTriples G) hne
      (fun p => p.1.card * p.2.1.card * p.2.2.card)
  obtain ⟨S, T, U⟩ := p
  have hTPP : TripleProductProperty S T U := mem_tppTriples.mp hpmem
  have hβeq : tppCapacity G = S.card * T.card * U.card := hpsup
  have hN1 : 1 < Fintype.card G := Fintype.one_lt_card
  have hβN : Fintype.card G ≤ tppCapacity G := card_le_tppCapacity
  have hβ1 : 1 < S.card * T.card * U.card := by rw [← hβeq]; omega
  -- All three sets are nonempty (else the product would be `0`).
  have hpos : S.card ≠ 0 ∧ T.card ≠ 0 ∧ U.card ≠ 0 := by
    have hne0 : S.card * T.card * U.card ≠ 0 := by omega
    rw [mul_ne_zero_iff, mul_ne_zero_iff] at hne0
    exact ⟨hne0.1.1, hne0.1.2, hne0.2⟩
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hpos.1)
  have hT : T.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hpos.2.1)
  have hU : U.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hpos.2.2)
  -- The three pairwise sum-product bounds.
  have hb1 := pairSumBound hTPP hS hT hU
  have hb2 := pairSumBound (tpp_perm_swap23 hTPP) hS hU hT
  have hb3 := pairSumBound (tpp_perm_rotate hTPP) hT hU hS
  set a := S.card with ha_def
  set b := T.card with hb_def
  set c := U.card with hc_def
  have ha : 0 < a := Nat.pos_of_ne_zero hpos.1
  have hb : 0 < b := Nat.pos_of_ne_zero hpos.2.1
  have hc : 0 < c := Nat.pos_of_ne_zero hpos.2.2
  -- Product bounds `|Sᵢ|·|Sⱼ| ≤ |G|`, and at least one is strict.
  have pab : a * b ≤ Fintype.card G := by omega
  have pac : a * c ≤ Fintype.card G := by omega
  have pbc : b * c ≤ Fintype.card G := by omega
  have hsome : 2 ≤ a ∨ 2 ≤ b ∨ 2 ≤ c := by
    by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨hca, hcb, hcc⟩ := hcon
    have hae : a = 1 := by omega
    have hbe : b = 1 := by omega
    have hce : c = 1 := by omega
    rw [hae, hbe, hce] at hβ1
    omega
  -- `(|S||T||U|)² = (|S||T|)(|S||U|)(|T||U|) < |G|³`.
  have cube_lt : ∀ x y z : ℕ, x ≤ Fintype.card G → y ≤ Fintype.card G →
      z < Fintype.card G → x * y * z < Fintype.card G ^ 3 := by
    intro x y z hx hy hz
    have hNpos : 0 < Fintype.card G := by omega
    calc x * y * z ≤ Fintype.card G * Fintype.card G * z :=
          Nat.mul_le_mul (Nat.mul_le_mul hx hy) (le_refl _)
      _ < Fintype.card G * Fintype.card G * Fintype.card G :=
          mul_lt_mul_of_pos_left hz (Nat.mul_pos hNpos hNpos)
      _ = Fintype.card G ^ 3 := by ring
  have hcube : (a * b * c) ^ 2 < Fintype.card G ^ 3 := by
    rcases hsome with h2 | h2 | h2
    · rw [show (a * b * c) ^ 2 = a * b * (a * c) * (b * c) by ring]
      exact cube_lt _ _ _ pab pac (by omega)
    · rw [show (a * b * c) ^ 2 = a * b * (b * c) * (a * c) by ring]
      exact cube_lt _ _ _ pab pbc (by omega)
    · rw [show (a * b * c) ^ 2 = a * c * (b * c) * (a * b) by ring]
      exact cube_lt _ _ _ pac pbc (by omega)
  have hβcube : tppCapacity G ^ 2 < Fintype.card G ^ 3 := by rw [hβeq]; exact hcube
  -- Convert to the `log` form: `2·log β < 3·log|G|`, hence `2 < α(G)`.
  have hβR : (1 : ℝ) < (tppCapacity G : ℝ) := by
    have : 1 < tppCapacity G := lt_of_lt_of_le hN1 hβN
    exact_mod_cast this
  have hlogβ : 0 < Real.log (tppCapacity G) := Real.log_pos hβR
  have hβpos : (0 : ℝ) < (tppCapacity G : ℝ) := lt_trans one_pos hβR
  rw [pseudoExponent, lt_div_iff₀ hlogβ]
  have e1 : (2 : ℝ) * Real.log (tppCapacity G) = Real.log ((tppCapacity G : ℝ) ^ 2) := by
    rw [Real.log_pow]; norm_num
  have e2 : (3 : ℝ) * Real.log (Fintype.card G) = Real.log ((Fintype.card G : ℝ) ^ 3) := by
    rw [Real.log_pow]; norm_num
  rw [e1, e2]
  apply Real.log_lt_log (pow_pos hβpos 2)
  exact_mod_cast hβcube

/-! ### Cohn–Umans Theorem 4.1 (sorry) -/

/-- **Cohn–Umans Theorem 4.1, `β`-form** [math/0307321, `theorem:bound`,
CU.tex:603–609].

If `G` has TPP capacity `β(G) = tppCapacity G` and complex irreducible character
degrees `{dᵢ}`, then

  `β(G)^{ω/3} ≤ Σᵢ dᵢ^ω = D_ω(G)`.

This is the form the program actually uses: a single group with large `β(G)`
and small `D_ω(G)` bounds `ω`. (It is equivalent to the pseudo-exponent form
`card_rpow_le_charDegreeSumReal` via `β(G) = |G|^{3/α(G)}`.)

**Proof debt** (CU.tex:621–666): embed an `⟨n,m,p⟩` product with `nmp = β(G)`
into `ℂ[G]`, transport through the indexed Wedderburn decomposition to
`⊕ᵢ ⟨dᵢ,dᵢ,dᵢ⟩`, then apply the tensor-rank facts `(nmp)^{ω/3} ≤ R(⟨n,m,p⟩)`
and `R(⟨k,k,k⟩) ≤ C k^{ω+ε}` (Bürgisser–Clausen–Shokrollahi 15.5/15.1), take
the `ℓ`-th tensor power, `ℓ`-th root, `ℓ → ∞`, and `ε → 0` by continuity. None
of tensor rank, bilinear complexity, or the indexed Wedderburn layer is in
Mathlib. `sorry`. -/
theorem capacity_rpow_le_charDegreeSumReal (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] :
    (tppCapacity G : ℝ) ^ (ω / 3) ≤ charDegreeSumReal G ω :=
  sorry

/-- `0 < β(G)`: the TPP capacity of a (nonempty, finite) group is positive, since
`|G| ≤ β(G)` and `|G| ≥ 1`. A positivity side-condition for the `rpow` algebra
linking the two forms of Theorem 4.1. -/
theorem tppCapacity_pos (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    0 < tppCapacity G :=
  lt_of_lt_of_le Fintype.card_pos card_le_tppCapacity

/-- **The pseudo-exponent identity** `β(G) = |G|^{3/α(G)}` for a nontrivial
finite group [math/0307321, CU.tex:471–476]. This is the algebraic heart of the
equivalence between the two forms of Theorem 4.1: since
`α(G) = 3·log|G| / log β(G)`, we have `3/α(G) = log β(G)/log|G| = logb_{|G|} β(G)`,
so `|G|^{3/α(G)} = β(G)` by `Real.rpow_logb`. (Needs `|G| ≥ 2`, i.e.
`Nontrivial G`, so that `log|G| ≠ 0` and `|G| ≠ 1`.) -/
theorem card_rpow_three_div_pseudoExponent (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] [Nontrivial G] :
    (Fintype.card G : ℝ) ^ (3 / pseudoExponent G) = (tppCapacity G : ℝ) := by
  have hcard : (1 : ℕ) < Fintype.card G := Fintype.one_lt_card
  have hcardR : (1 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hcard
  have hβpos : (0 : ℝ) < (tppCapacity G : ℝ) := by exact_mod_cast tppCapacity_pos G
  -- rewrite the exponent `3 / α(G)` as `logb |G| β(G) = log β(G) / log |G|`
  have hexp : (3 : ℝ) / pseudoExponent G
      = Real.logb (Fintype.card G) (tppCapacity G) := by
    rw [pseudoExponent, Real.logb]
    have hlogN : Real.log (Fintype.card G) ≠ 0 := (Real.log_pos hcardR).ne'
    field_simp
  rw [hexp, Real.rpow_logb (lt_trans one_pos hcardR) hcardR.ne' hβpos]

/-- **Cohn–Umans Theorem 4.1, pseudo-exponent form** [math/0307321,
`theorem:bound`, CU.tex:603–609]: `|G|^{ω/α(G)} ≤ D_ω(G)`.

This is the statement exactly as printed in the paper, and it is **derived here
in full** from the `β`-form (`capacity_rpow_le_charDegreeSumReal`) via the
identity `β(G) = |G|^{3/α(G)}` (`card_rpow_three_div_pseudoExponent`): writing
`ω/α = (ω/3)·(3/α)`, `rpow_mul` gives
`|G|^{ω/α} = (|G|^{3/α})^{ω/3} = β(G)^{ω/3}`, and the `β`-form bounds the
right-hand side. It therefore carries no `sorry` of its own — only the inherited
debt of Theorem 4.1. -/
theorem card_rpow_le_charDegreeSumReal (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] [Nontrivial G] :
    (Fintype.card G : ℝ) ^ (ω / pseudoExponent G) ≤ charDegreeSumReal G ω := by
  have hcardNonneg : (0 : ℝ) ≤ (Fintype.card G : ℝ) := Nat.cast_nonneg _
  -- `|G|^{ω/α} = (|G|^{3/α})^{ω/3} = β(G)^{ω/3}`
  have hsplit : (Fintype.card G : ℝ) ^ (ω / pseudoExponent G)
      = (tppCapacity G : ℝ) ^ (ω / 3) := by
    rw [show ω / pseudoExponent G = (3 / pseudoExponent G) * (ω / 3) by ring,
      Real.rpow_mul hcardNonneg, card_rpow_three_div_pseudoExponent G]
  rw [hsplit]
  exact capacity_rpow_le_charDegreeSumReal G

/-! ### The `D₃` threshold certificate (sorry)

CU.tex:749–769 and Question `fundamentalq` (CU.tex:774–781). With the full set
of character degrees in hand, there is a *single arithmetic condition* deciding
whether Theorem 4.1 for `G` yields any nontrivial bound on `ω` (i.e. rules out
`ω = 3`): the condition is `|G|^{3/α(G)} > Σᵢ dᵢ³`, i.e. `β(G) > D₃(G)`.

CU remark (CU.tex:766–768): the inequality of Theorem 4.1 "gives no information
about `ω` in the interval `[2,3]` unless it rules out `ω = 3`, which is
equivalent to the above stated condition." No group meeting it is known
(`fundamentalq` is open). -/

/-- **The `D₃` threshold predicate** `D₃(G) < β(G)` [math/0307321, Question
`fundamentalq`, CU.tex:774–781]. A group `G` satisfies `BetaExceedsD3 G` exactly
when its TPP capacity strictly exceeds the cubic character-degree sum
`D₃(G) = Σᵢ dᵢ³`. This is the (open) condition under which a single group
certifies `ω < 3`.

**⚠ Conditional on the `charDegrees` `sorry` (`Xlib.CharDegrees.charDegrees`).**
This predicate is the *mathematically correct* statement of the `D₃` threshold
condition, but its **truth value is currently undetermined**: the left-hand side
`charDegreeSum G 3 = Σᵢ dᵢ³` is computed from `Xlib.CharDegrees.charDegrees`,
whose body is `sorry` (the indexed-Wedderburn debt — no canonical enumeration of
irreps in Mathlib). So `BetaExceedsD3 G` asserts a property of an **unresolved
(junk) definition**: the `β(G) = tppCapacity G` side is fully defined and
`sorry`-free, but the `D₃(G)` side is junk until that one upstream `sorry` is
discharged. Both the predicate and the theorem `betaExceedsD3_certifies_subcubic`
that consumes it are *correct as stated* and become meaningful verbatim once the
indexed Wedderburn layer lands; nothing about them needs to change at that point.

Concretely, `#print axioms BetaExceedsD3` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`: the `sorryAx` here enters
**solely** through `charDegrees` (via `charDegreeSum`); no `matrixExponent` family
axiom appears, since the predicate does not mention `ω`. -/
def BetaExceedsD3 (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Prop :=
  (charDegreeSum G 3 : ℝ) < (tppCapacity G : ℝ)

/-- **The `D₃` certificate** [math/0307321, CU.tex:766–768]: if `G`'s TPP
capacity strictly exceeds its cubic character-degree sum, `D₃(G) < β(G)`, then
the matrix-multiplication exponent is strictly subcubic, `ω < 3`.

This is the precise sense in which "a single group certifies `ω < 3`", and it is
**proved here in full from Theorem 4.1** (`capacity_rpow_le_charDegreeSumReal`)
together with `matrixExponent_le_three` — it carries *no* `sorry` of its own,
only the inherited debts of those two. The argument is the boundary evaluation,
not the general convexity step: were `ω = 3`, Theorem 4.1 would read
`β(G)^{3/3} = β(G) ≤ charDegreeSumReal G 3 = D₃(G)` (via `Real.rpow_one` and
`Xlib.CharDegrees.charDegreeSumReal_natCast`), contradicting `D₃(G) < β(G)`;
hence `ω ≠ 3`, and `ω ≤ 3` then forces `ω < 3`.

**⚠ Conditional on the `charDegrees` `sorry`, via the hypothesis `BetaExceedsD3`.**
The theorem is a *correct* statement and its tactic body is `sorry`-free, but the
hypothesis `h : BetaExceedsD3 G` is the junk-valued predicate above (its `D₃(G)`
side is computed from the `sorry`d `Xlib.CharDegrees.charDegrees`). So this is a
correct implication *out of* a currently-undetermined antecedent: it is not
vacuously discharged, and it becomes verbatim-meaningful — with no change to the
statement — once the indexed Wedderburn `sorry` is discharged.

The inherited debt chain is therefore **two `sorry`s plus two axioms**:
(1) Theorem 4.1 `capacity_rpow_le_charDegreeSumReal` is itself `sorry`d
(tensor-rank debt 2); (2) the hypothesis `BetaExceedsD3 G` drags in the
`charDegrees` `sorry` through `charDegreeSum`/`charDegreeSumReal_natCast`; plus
the two foundation axioms `matrixExponent` (`ω` exists) and
`matrixExponent_le_three` (`ω ≤ 3`). Concretely,
`#print axioms betaExceedsD3_certifies_subcubic` reports
`[propext, sorryAx, Classical.choice, Quot.sound, matrixExponent,
matrixExponent_le_three]`. Note `two_le_matrixExponent` does **not** appear (the
boundary argument uses only the upper bound `ω ≤ 3`), and the single `sorryAx`
entry collapses both independent `sorry` sources — debt 2 and the `charDegrees`
debt — into one axiom name. -/
theorem betaExceedsD3_certifies_subcubic (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] (h : BetaExceedsD3 G) :
    ω < 3 := by
  refine lt_of_le_of_ne matrixExponent_le_three ?_
  intro heq
  -- Theorem 4.1 at the actual `ω`, then specialize to the impossible `ω = 3`.
  have hbound := capacity_rpow_le_charDegreeSumReal G
  rw [heq] at hbound
  have hbridge : charDegreeSumReal G (3 : ℝ) = (charDegreeSum G 3 : ℝ) := by
    have := charDegreeSumReal_natCast G 3
    rwa [Nat.cast_ofNat] at this
  rw [hbridge] at hbound
  -- `β^(3/3) = β`, so the bound becomes `β ≤ D₃`, contradicting `D₃ < β`.
  have hexp : ((3 : ℝ) / 3) = (1 : ℝ) := by norm_num
  rw [hexp, Real.rpow_one] at hbound
  exact absurd hbound (not_le.mpr h)

/-- **Arithmetic unfolding of the `D₃` threshold shape** [math/0307321,
CU.tex:766–768]: the Theorem 4.1 expression, evaluated at exponent `3`, is
*violated* for `G` (`¬ (β(G)^{3/3} ≤ D₃(G))`) if and only if `BetaExceedsD3 G`
(i.e. `D₃(G) < β(G)`).

**This theorem is fully proved (`sorry`-free body) and is mathematically
trivial — it is an arithmetic unfolding, not a substantive equivalence.** It does
*not* capture any nontrivial content of CU's "equivalent to the above stated
condition"; that equivalence is real only because Theorem 4.1 holds (debt 2,
`capacity_rpow_le_charDegreeSumReal`), which this statement neither invokes nor
needs. All this says is that the two *literal expressions* coincide: after
collapsing the exponent `3/3 = 1` (so `β^{3/3} = β` by `Real.rpow_one`) and
bridging `charDegreeSumReal G 3 = (charDegreeSum G 3 : ℝ)`
(`Xlib.CharDegrees.charDegreeSumReal_natCast`), the goal is exactly
`¬ (β ≤ D₃) ↔ D₃ < β`, which is `not_le`. In short it restates `BetaExceedsD3`
in the "negated-bound" shape; it makes no claim about `ω` at all.

Axiom footprint accordingly: `#print axioms subcubic_certificate_iff` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`. The lone `sorryAx` enters
**only** through the upstream `charDegrees` `sorry` (via `charDegreeSum` on both
sides of the iff); crucially **no** `matrixExponent` family axiom appears —
unlike `betaExceedsD3_certifies_subcubic`, this statement never mentions `ω`, so
it does not even depend on the existence of the exponent, only on the still-junk
`charDegrees`. -/
theorem subcubic_certificate_iff (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] :
    ¬ ((tppCapacity G : ℝ) ^ ((3 : ℝ) / 3) ≤ charDegreeSumReal G 3)
      ↔ BetaExceedsD3 G := by
  have hbridge : charDegreeSumReal G (3 : ℝ) = (charDegreeSum G 3 : ℝ) := by
    have := charDegreeSumReal_natCast G 3
    rwa [Nat.cast_ofNat] at this
  have hexp : ((3 : ℝ) / 3) = (1 : ℝ) := by norm_num
  rw [BetaExceedsD3, hbridge, hexp, Real.rpow_one, not_le]

end Xlib.CUCapacity
