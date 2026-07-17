import Xlib.TPP
import Xlib.CharDegrees
import Xlib.CharDegreesMul
import Xlib.TPPProd
import Proofs.BilinearComplexity.Omega
import Proofs.BilinearComplexity.Complexify
import Proofs.BilinearComplexity.GroupTensorWedderburn

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

## The foundational debts — all discharged

Historically this file was a sorry-skeleton with two isolated foundational
debts; both are now discharged and **the file is `sorry`-free**:

1. ~~**The matrix-multiplication exponent `ω` itself.**~~ **Discharged.** The
   exponent `ω` is now defined as `BilinearComplexity.omega := sInf omegaSet`
   (the infimum of admissible exponents of the matrix-multiplication tensor),
   with its two elementary bounds `2 ≤ ω` and `ω ≤ 3` proved from the
   sorry-free tensor-rank calculus (`Proofs/BilinearComplexity/Omega.lean`).
   The local alias `matrixExponent := BilinearComplexity.omega` and scoped
   notation `ω` are retained for downstream compatibility.

2. ~~**The proof of Theorem 4.1.**~~ **Discharged.** The proof (CU.tex:621–666)
   is assembled in the `CohnUmansChain` section below from the delivered
   planks: the Cohn–Umans/Murthy TPP embedding
   (`Proofs.BilinearComplexity.GroupTensor`), TPP product closure
   (`Xlib.TPPProd`), Wedderburn transport of the group-tensor rank
   (`Proofs.BilinearComplexity.GroupTensorWedderburn`), multiplicativity of
   the character-degree power sum (`Xlib.CharDegreesMul`), and the two
   tensor-rank facts `n^ω ≤ R_ℂ⟨n,n,n⟩` and `R_ℂ⟨k,k,k⟩ ≤ C·k^{ω+ε}`
   (Bürgisser–Clausen–Shokrollahi 15.5/15.1;
   `Proofs.BilinearComplexity.Complexify` / `Omega.lean` §4).

Everything else is built on the (`sorry`-free) TPP/character-degree API of
`Xlib.TPP` and `Xlib.CharDegrees` and **proved here in full**: the abelian
case `α(G) = 3` (`pseudoExponent_eq_three_of_commGroup`), the universal lower
bound `α(G) > 2` (`two_lt_pseudoExponent`), the equivalence of the `β`- and
pseudo-exponent forms of Theorem 4.1 (`card_rpow_le_charDegreeSumReal`
derives from `capacity_rpow_le_charDegreeSumReal` via the identity
`β(G) = |G|^{3/α(G)}`), the `D₃` certificate
(`betaExceedsD3_certifies_subcubic` derives from Theorem 4.1), and the `D₃`
threshold equivalence (`subcubic_certificate_iff`).

## Main definitions

* `Xlib.CUCapacity.matrixExponent` — `ω`, the exponent of matrix multiplication.
  Alias for `BilinearComplexity.omega` (discharged foundation).
* `Xlib.CUCapacity.pseudoExponent` — `α(G) = 3·log|G| / log β(G)`, the
  Cohn–Umans pseudo-exponent (`theorem:bound` preamble, CU.tex:460–467).
* `Xlib.CUCapacity.BetaExceedsD3` — the `D₃` threshold predicate
  `D₃(G) < β(G)` (CU Question `fundamentalq`, CU.tex:774–781). Fully defined:
  both sides are `sorry`-free (`Xlib.CharDegrees.charDegrees` landed with the
  `Wd` campaign).

## Main results

* `Xlib.CUCapacity.capacity_rpow_le_charDegreeSumReal` — **(proved,
  `sorry`-free)** CU Theorem 4.1 in `β`-form: `β(G)^{ω/3} ≤ D_ω(G)`.
* `Xlib.CUCapacity.card_rpow_le_charDegreeSumReal` — **(proved from the `β`-form)**
  the equivalent pseudo-exponent form `|G|^{ω/α(G)} ≤ D_ω(G)`.
* `Xlib.CUCapacity.card_rpow_three_div_pseudoExponent` — **(proved,
  `sorry`-free)** the identity `β(G) = |G|^{3/α(G)}` (the bridge between the two
  forms), via `Real.rpow_logb`.
* `Xlib.CUCapacity.pseudoExponent_eq_three_of_commGroup` — **(proved,
  `sorry`-free)** `α(G) = 3` for a nontrivial commutative `G` (the abelian
  barrier, via `Xlib.TPP.tppCapacity_eq_card`).
* `Xlib.CUCapacity.two_lt_pseudoExponent` — **(proved, `sorry`-free)**
  `α(G) > 2` for every nontrivial finite `G` (CU pseudo-exponent lemma,
  CU.tex:478–500).
* `Xlib.CUCapacity.betaExceedsD3_certifies_subcubic` — **(proved from Theorem
  4.1, `sorry`-free)** the `D₃` certificate: `D₃(G) < β(G) ⟹ ω < 3` (a single
  group certifies `ω < 3`).
* `Xlib.CUCapacity.subcubic_certificate_iff` — **(proved, `sorry`-free)** a
  *trivial arithmetic unfolding*: the Theorem 4.1 expression evaluated at exponent
  `3` is violated iff `D₃(G) < β(G)`. This is `not_le` after `3/3 = 1` and
  `rpow_one` — it restates `BetaExceedsD3` in negated-bound shape and makes no
  claim about `ω` (the substantive "rules out `ω = 3`" implication is
  `betaExceedsD3_certifies_subcubic`).

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

/-! ### The matrix-multiplication exponent `ω` (discharged foundation)

`ω` is defined as `BilinearComplexity.omega := sInf omegaSet` in
`Proofs/BilinearComplexity/Omega.lean`, with `2 ≤ ω` and `ω ≤ 3` proved from
the sorry-free tensor-rank calculus (flattening lower bound and cubic upper
bound). The local alias `matrixExponent` and scoped notation `ω` are retained
for downstream compatibility (`Xlib.STPPWreath`, the `Dᵣ` sieve). -/

/-- **The exponent of matrix multiplication** `ω`.

`ω` is the infimum of all `c` such that two `n × n` matrices can be multiplied
with `O(n^{c+ε})` arithmetic operations for every `ε > 0`; equivalently the
infimum of feasible exponents of the matrix-multiplication tensor `⟨n,n,n⟩`.

Defined as `BilinearComplexity.omega := sInf omegaSet` on top of the sorry-free
tensor-rank calculus. This is the single real constant the capacity bound
(`theorem:bound`) compares against; downstream files (`Xlib.STPPWreath`, the
`Dᵣ` sieve) reference it by this name. -/
noncomputable def matrixExponent : ℝ := BilinearComplexity.omega

@[inherit_doc] scoped notation "ω" => matrixExponent

/-- **`2 ≤ ω`.** Multiplying two `n × n` matrices must read all `2n²` input
entries, so the exponent is at least `2`. Proved from the flattening lower bound
`n² ≤ R⟨n,n,n⟩` via `BilinearComplexity.two_le_omega`. -/
theorem two_le_matrixExponent : 2 ≤ ω := BilinearComplexity.two_le_omega

/-- **`ω ≤ 3`.** Schoolbook matrix multiplication uses `O(n³)` operations, so the
exponent is at most `3`. Proved from the cubic upper bound `R⟨n,n,n⟩ ≤ n³` via
`BilinearComplexity.omega_le_three`. -/
theorem matrixExponent_le_three : ω ≤ 3 := BilinearComplexity.omega_le_three

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

/-! ### The Cohn–Umans chain: analytic and combinatorial glue

The proof of Theorem 4.1 below composes the delivered planks
(`Proofs.BilinearComplexity.{GroupTensor, GroupTensorWedderburn, Complexify,
Omega}`, `Xlib.TPPProd`, `Xlib.CharDegreesMul`) through the per-triple chain:
for a TPP triple `(S, T, U)` with `N = |S|·|T|·|U| ≥ 2`, every `ℓ ≥ 1` and
`ε > 0` (writing `s_ε := charDegreeSumReal G (ω+ε)`),

  `N^{ℓω} ≤ R_ℂ⟨N^ℓ,N^ℓ,N^ℓ⟩`                            (`rpow_omega_le_rank_complex`)
  `      ≤ R_ℂ⟨|S|^ℓ,|T|^ℓ,|U|^ℓ⟩³`                       (symmetrization, below)
  `      ≤ R_ℂ(mulTensor ℂ (Fin ℓ → G))³`                 (TPP power triple + Murthy 4.13)
  `      ≤ (Σ_{d ∈ charDegrees (Fin ℓ → G)} R_ℂ⟨d,d,d⟩)³` (Wedderburn transport)
  `      ≤ (C · s_ε^ℓ)³`                                  (BCS 15.1 + degree multiplicativity),

whence `(N^ω)^ℓ ≤ C³ · (s_ε³)^ℓ`; the geometric-growth helper absorbs `C³`
(`ℓ → ∞`), a cube root gives `N^{ω/3} ≤ s_ε`, and `ε := 1/ℓ → 0⁺` converges
`s_ε → s_0` through the elementary bound `s_ε ≤ |G|^ε · s_0` (every degree is
at most `|G|`, since `d ≤ d² ≤ Σᵢ dᵢ² = |G|`). -/

section CohnUmansChain

open BilinearComplexity Xlib.CharDegreesMul
open scoped Pointwise

/-- Unfolding of `charDegreeSumReal` with the coercion normalized to a plain
`Multiset.map` over `ℕ` (the definition's `(d : ℝ)` cast elaborates as the
monadic container cast; see the note in `Xlib.CharDegreesMul`). -/
private theorem charDegreeSumReal_eq_map_sum (G : Type*) [Group G] [Fintype G]
    (x : ℝ) :
    charDegreeSumReal G x
      = ((charDegrees G).map (fun d : ℕ => (d : ℝ) ^ x)).sum := by
  unfold charDegreeSumReal
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton,
    Multiset.map_map]
  rfl

/-- `1 ≤ D_x(G)` for `x ≥ 0`: the degree multiset is nonempty (else
`Σᵢ dᵢ² = |G| ≥ 1` would fail) and each entry contributes `dᵢˣ ≥ 1`. -/
private theorem one_le_charDegreeSumReal (G : Type*) [Group G] [Fintype G]
    {x : ℝ} (hx : 0 ≤ x) : 1 ≤ charDegreeSumReal G x := by
  have hne : charDegrees G ≠ 0 := by
    intro h0
    have h2 := charDegreeSum_two G
    unfold charDegreeSum at h2
    rw [h0, Multiset.map_zero, Multiset.sum_zero] at h2
    have hpos := Fintype.card_pos (α := G)
    omega
  obtain ⟨d, hd⟩ := Multiset.exists_mem_of_ne_zero hne
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast one_le_of_mem_charDegrees hd
  rw [charDegreeSumReal_eq_map_sum]
  calc (1 : ℝ) ≤ (d : ℝ) ^ x := Real.one_le_rpow hd1R hx
    _ ≤ ((charDegrees G).map (fun m : ℕ => (m : ℝ) ^ x)).sum := by
        refine Multiset.single_le_sum (fun y hy => ?_) _
          (Multiset.mem_map_of_mem _ hd)
        obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hy
        exact Real.rpow_nonneg (Nat.cast_nonneg m) x

/-- **The `ε`-shift bound** `D_{x+ε}(G) ≤ |G|^ε · D_x(G)` for `ε ≥ 0`:
entrywise `d^{x+ε} = d^x · d^ε ≤ d^x · |G|^ε`, using `1 ≤ d ≤ |G|`
(`d ≤ d² ≤ Σᵢ dᵢ² = |G|`, `charDegreeSum_two`). This elementary bound
replaces the continuity argument for the `ε → 0⁺` limit of Theorem 4.1. -/
private theorem charDegreeSumReal_add_le (G : Type*) [Group G] [Fintype G]
    (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    charDegreeSumReal G (x + ε)
      ≤ (Fintype.card G : ℝ) ^ ε * charDegreeSumReal G x := by
  rw [charDegreeSumReal_eq_map_sum, charDegreeSumReal_eq_map_sum,
    ← Multiset.sum_map_mul_left]
  refine Multiset.sum_map_le_sum_map _ _ fun d hd => ?_
  have hd1 : 1 ≤ d := one_le_of_mem_charDegrees hd
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd0R : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos hd1R
  have hdG : d ≤ Fintype.card G := by
    have h2 : d ^ 2 ≤ ((charDegrees G).map (fun m => m ^ 2)).sum :=
      Multiset.single_le_sum (fun y _ => Nat.zero_le y) _
        (Multiset.mem_map_of_mem _ hd)
    have hsum : ((charDegrees G).map (fun m => m ^ 2)).sum = Fintype.card G :=
      charDegreeSum_two G
    exact le_trans (le_self_pow hd1 two_ne_zero) (le_trans h2 hsum.le)
  have hdGR : (d : ℝ) ≤ (Fintype.card G : ℝ) := by exact_mod_cast hdG
  calc (d : ℝ) ^ (x + ε) = (d : ℝ) ^ x * (d : ℝ) ^ ε := Real.rpow_add hd0R x ε
    _ ≤ (d : ℝ) ^ x * (Fintype.card G : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd0R.le hdGR hε)
          (Real.rpow_nonneg (Nat.cast_nonneg d) x)
    _ = (Fintype.card G : ℝ) ^ ε * (d : ℝ) ^ x := mul_comm _ _

/-- **Geometric-growth constant absorption** (the `ℓ`-th root / `ℓ → ∞` step
of Theorem 4.1, in Archimedean form): if `x^ℓ ≤ K · y^ℓ` for all `ℓ ≥ 1` with
`y ≥ 0`, then `x ≤ y` — otherwise `(x/y)^ℓ` eventually exceeds `K`. -/
private theorem le_of_pow_le_const_mul_pow {x y K : ℝ} (hy : 0 ≤ y)
    (h : ∀ ℓ : ℕ, 1 ≤ ℓ → x ^ ℓ ≤ K * y ^ ℓ) : x ≤ y := by
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · have h1 := h 1 le_rfl
    rw [← hy0] at h1 ⊢
    simpa using h1
  · by_contra hcon
    rw [not_le] at hcon
    have hr : 1 < x / y := (one_lt_div hy0).mpr hcon
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt K hr
    have hj' : K < (x / y) ^ (j + 1) :=
      lt_of_lt_of_le hj (pow_le_pow_right₀ hr.le (Nat.le_succ j))
    have hle := h (j + 1) (Nat.le_add_left 1 j)
    have hyp : (0 : ℝ) < y ^ (j + 1) := pow_pos hy0 _
    have hK : (x / y) ^ (j + 1) ≤ K := by
      rw [div_pow, div_le_iff₀ hyp]
      exact hle
    linarith

/-- **Root convergence** (the `ε → 0⁺` step of Theorem 4.1, along the
diagonal `ε := 1/ℓ`): if `x ≤ B^{1/ℓ} · s` for all `ℓ ≥ 1` with `B > 0`,
then `x ≤ s`, since `B^{1/ℓ} → B⁰ = 1`. -/
private theorem le_of_forall_rpow_one_div_mul {x s B : ℝ} (hB : 0 < B)
    (h : ∀ ℓ : ℕ, 1 ≤ ℓ → x ≤ B ^ (1 / (ℓ : ℝ)) * s) : x ≤ s := by
  have h0 : Filter.Tendsto (fun ℓ : ℕ => B ^ (1 / (ℓ : ℝ))) Filter.atTop
      (nhds (B ^ (0 : ℝ))) :=
    Filter.Tendsto.rpow tendsto_const_nhds tendsto_one_div_atTop_nhds_zero_nat
      (Or.inl hB.ne')
  rw [Real.rpow_zero] at h0
  have htend : Filter.Tendsto (fun ℓ : ℕ => B ^ (1 / (ℓ : ℝ)) * s) Filter.atTop
      (nhds s) := by
    have hmul := h0.mul_const s
    rwa [one_mul] at hmul
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with ℓ hℓ using h ℓ hℓ

/-- **Symmetrization** (the cubic reduction inside BCS Prop. 15.5):
`R⟨abc,abc,abc⟩ ≤ R⟨a,b,c⟩³`. The Kronecker square/cube
`⟨a,b,c⟩ ⊗ ⟨b,c,a⟩ ⊗ ⟨c,a,b⟩` is `⟨abc,abc,abc⟩` up to reindexing
(`rank_matMulTensor_mul_le`), and the three cyclic rotations share one rank
(`rank_matMulTensor_cyc`). -/
private theorem rank_matMulTensor_cube_le (k : Type*) [CommSemiring k]
    (a b c : ℕ) :
    rank (matMulTensor k (a * b * c) (a * b * c) (a * b * c))
      ≤ rank (matMulTensor k a b c) ^ 3 := by
  have h1 : rank (matMulTensor k (a * b) (b * c) (c * a))
      ≤ rank (matMulTensor k a b c) * rank (matMulTensor k b c a) :=
    rank_matMulTensor_mul_le k a b c b c a
  have h2 : rank (matMulTensor k (a * b * c) (b * c * a) (c * a * b))
      ≤ rank (matMulTensor k (a * b) (b * c) (c * a))
          * rank (matMulTensor k c a b) :=
    rank_matMulTensor_mul_le k (a * b) (b * c) (c * a) c a b
  rw [show b * c * a = a * b * c from by ring,
    show c * a * b = a * b * c from by ring] at h2
  rw [← rank_matMulTensor_cyc k a b c] at h1
  rw [← rank_matMulTensor_cyc k b c a, ← rank_matMulTensor_cyc k a b c] at h2
  calc rank (matMulTensor k (a * b * c) (a * b * c) (a * b * c))
      ≤ rank (matMulTensor k (a * b) (b * c) (c * a))
          * rank (matMulTensor k a b c) := h2
    _ ≤ rank (matMulTensor k a b c) * rank (matMulTensor k a b c)
          * rank (matMulTensor k a b c) := Nat.mul_le_mul h1 le_rfl
    _ = rank (matMulTensor k a b c) ^ 3 := by ring

/-- **Murthy 4.13 across the TPP convention bridge**: a left-quotient TPP
triple `(S, T, U)` embeds `⟨|S|,|T|,|U|⟩` into the group tensor. The inversion
bridge `tripleProductProperty_iff_inv` supplies the right-quotient
`DihedralTPP.IsTPP` for `(S⁻¹, T⁻¹, U⁻¹)` (definitionally
`TripleProductPropertyR`), whose cardinalities agree with `(S, T, U)`. -/
private theorem rank_matMulTensor_le_rank_mulTensor {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) :
    rank (matMulTensor ℂ S.card T.card U.card) ≤ rank (mulTensor ℂ G) := by
  have hIs : DihedralTPP.IsTPP S⁻¹ T⁻¹ U⁻¹ := tripleProductProperty_iff_inv.mp h
  rw [← Finset.card_inv S, ← Finset.card_inv T, ← Finset.card_inv U]
  exact rank_matMulTensor_le_of_isTPP (k := ℂ) hIs

/-- **The per-`(ℓ, ε)` chain of Theorem 4.1**: for a TPP triple with
`N = |S|·|T|·|U| ≥ 2` and a BCS 15.1 constant `C` for slack `ε`,

  `(N^ω)^ℓ ≤ C³ · (D_{ω+ε}(G)³)^ℓ`   for every `ℓ ≥ 1`.

Chain: `ω` lower bound at `N^ℓ` (over ℂ), symmetrization to
`R_ℂ⟨|S|^ℓ,|T|^ℓ,|U|^ℓ⟩³`, TPP power-triple embedding into
`mulTensor ℂ (Fin ℓ → G)`, Wedderburn transport to the degree multiset of the
power group, the per-degree bound `R_ℂ⟨d,d,d⟩ ≤ C·d^{ω+ε}`, and
multiplicativity `D_{ω+ε}(G^ℓ) = D_{ω+ε}(G)^ℓ`. -/
private theorem pow_omega_pow_le_of_tpp {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {S T U : Finset G} (h : TripleProductProperty S T U)
    (hN : 2 ≤ S.card * T.card * U.card) {ε C : ℝ}
    (hC : ∀ k : ℕ, 1 ≤ k → (rank (matMulTensor ℂ k k k) : ℝ)
      ≤ C * (k : ℝ) ^ (BilinearComplexity.omega + ε))
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (((S.card * T.card * U.card : ℕ) : ℝ) ^ BilinearComplexity.omega) ^ ℓ
      ≤ C ^ 3 * (charDegreeSumReal G (BilinearComplexity.omega + ε) ^ 3) ^ ℓ := by
  set N : ℕ := S.card * T.card * U.card with hNdef
  have hNℓ : 2 ≤ N ^ ℓ :=
    le_trans hN (by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ ℓ := Nat.pow_le_pow_right (by omega) hℓ)
  -- (1) the `ω` lower bound at dimension `N^ℓ`
  have h1 : ((N ^ ℓ : ℕ) : ℝ) ^ BilinearComplexity.omega
      ≤ (rank (matMulTensor ℂ (N ^ ℓ) (N ^ ℓ) (N ^ ℓ)) : ℝ) :=
    rpow_omega_le_rank_complex hNℓ
  -- (2) symmetrization to the rectangular power triple
  have h2 : rank (matMulTensor ℂ (N ^ ℓ) (N ^ ℓ) (N ^ ℓ))
      ≤ rank (matMulTensor ℂ (S.card ^ ℓ) (T.card ^ ℓ) (U.card ^ ℓ)) ^ 3 := by
    have hsplit : N ^ ℓ = S.card ^ ℓ * T.card ^ ℓ * U.card ^ ℓ := by
      rw [hNdef, mul_pow, mul_pow]
    rw [hsplit]
    exact rank_matMulTensor_cube_le ℂ _ _ _
  -- (3) the TPP power triple embeds into the power-group tensor
  have h3 : rank (matMulTensor ℂ (S.card ^ ℓ) (T.card ^ ℓ) (U.card ^ ℓ))
      ≤ rank (mulTensor ℂ (Fin ℓ → G)) := by
    have hb := rank_matMulTensor_le_rank_mulTensor (h.piFinset ℓ)
    rwa [card_piFinset_const_eq S ℓ, card_piFinset_const_eq T ℓ,
      card_piFinset_const_eq U ℓ] at hb
  -- (4) Wedderburn transport
  have h4 : rank (mulTensor ℂ (Fin ℓ → G))
      ≤ ((charDegrees (Fin ℓ → G)).map
          (fun d => rank (matMulTensor ℂ d d d))).sum :=
    rank_mulTensor_le_sum_charDegrees (Fin ℓ → G)
  -- (5) per-degree BCS 15.1 bound and degree multiplicativity
  have h5 : ((((charDegrees (Fin ℓ → G)).map
        (fun d => rank (matMulTensor ℂ d d d))).sum : ℕ) : ℝ)
      ≤ C * charDegreeSumReal G (BilinearComplexity.omega + ε) ^ ℓ := by
    have hcast : ((((charDegrees (Fin ℓ → G)).map
          (fun d => rank (matMulTensor ℂ d d d))).sum : ℕ) : ℝ)
        = ((charDegrees (Fin ℓ → G)).map
            (fun d : ℕ => (rank (matMulTensor ℂ d d d) : ℝ))).sum := by
      rw [Nat.cast_multiset_sum, Multiset.map_map]
      rfl
    rw [hcast]
    calc ((charDegrees (Fin ℓ → G)).map
          (fun d : ℕ => (rank (matMulTensor ℂ d d d) : ℝ))).sum
        ≤ ((charDegrees (Fin ℓ → G)).map
            (fun d : ℕ => C * (d : ℝ) ^ (BilinearComplexity.omega + ε))).sum :=
          Multiset.sum_map_le_sum_map _ _
            (fun d hd => hC d (one_le_of_mem_charDegrees hd))
      _ = C * ((charDegrees (Fin ℓ → G)).map
            (fun d : ℕ => (d : ℝ) ^ (BilinearComplexity.omega + ε))).sum :=
          Multiset.sum_map_mul_left
      _ = C * charDegreeSumReal (Fin ℓ → G) (BilinearComplexity.omega + ε) := by
          rw [charDegreeSumReal_eq_map_sum]
      _ = C * charDegreeSumReal G (BilinearComplexity.omega + ε) ^ ℓ := by
          rw [charDegreeSumReal_pi_fin]
  -- assemble, cube, and collapse the powers
  have h6 : (rank (matMulTensor ℂ (S.card ^ ℓ) (T.card ^ ℓ) (U.card ^ ℓ)) : ℝ)
      ≤ C * charDegreeSumReal G (BilinearComplexity.omega + ε) ^ ℓ := by
    refine le_trans ?_ h5
    exact_mod_cast le_trans h3 h4
  calc (((N : ℕ) : ℝ) ^ BilinearComplexity.omega) ^ ℓ
      = ((N ^ ℓ : ℕ) : ℝ) ^ BilinearComplexity.omega := by
        rw [Nat.cast_pow,
          ← Real.rpow_natCast_mul (Nat.cast_nonneg N) ℓ BilinearComplexity.omega,
          ← Real.rpow_mul_natCast (Nat.cast_nonneg N) BilinearComplexity.omega ℓ,
          mul_comm]
    _ ≤ (rank (matMulTensor ℂ (N ^ ℓ) (N ^ ℓ) (N ^ ℓ)) : ℝ) := h1
    _ ≤ (rank (matMulTensor ℂ (S.card ^ ℓ) (T.card ^ ℓ) (U.card ^ ℓ)) : ℝ) ^ 3 := by
        exact_mod_cast h2
    _ ≤ (C * charDegreeSumReal G (BilinearComplexity.omega + ε) ^ ℓ) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h6 3
    _ = C ^ 3 * (charDegreeSumReal G (BilinearComplexity.omega + ε) ^ 3) ^ ℓ := by
        rw [mul_pow, pow_right_comm]

/-- **The per-`ε` capacity bound**: for a TPP triple with
`N = |S|·|T|·|U| ≥ 2` and every `ε > 0`, `N^{ω/3} ≤ D_{ω+ε}(G)`. Extract the
BCS 15.1 constant (`exists_rank_le_rpow_complex`), run the per-`(ℓ, ε)` chain,
absorb the constant by geometric growth, and take the cube root. -/
private theorem rpow_le_charDegreeSumReal_add {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {S T U : Finset G} (h : TripleProductProperty S T U)
    (hN : 2 ≤ S.card * T.card * U.card) {ε : ℝ} (hε : 0 < ε) :
    ((S.card * T.card * U.card : ℕ) : ℝ) ^ (BilinearComplexity.omega / 3)
      ≤ charDegreeSumReal G (BilinearComplexity.omega + ε) := by
  obtain ⟨C, -, hC⟩ := exists_rank_le_rpow_complex ε hε
  have homega0 : (0 : ℝ) ≤ BilinearComplexity.omega :=
    le_trans (by norm_num) two_le_omega
  have hs1 : (1 : ℝ) ≤ charDegreeSumReal G (BilinearComplexity.omega + ε) :=
    one_le_charDegreeSumReal G (by linarith)
  have hs0 : (0 : ℝ) ≤ charDegreeSumReal G (BilinearComplexity.omega + ε) :=
    le_trans zero_le_one hs1
  have hcube_id : (((S.card * T.card * U.card : ℕ) : ℝ)
        ^ (BilinearComplexity.omega / 3)) ^ 3
      = ((S.card * T.card * U.card : ℕ) : ℝ) ^ BilinearComplexity.omega := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)
      (BilinearComplexity.omega / 3) 3]
    congr 1
    push_cast
    ring
  have hA : (((S.card * T.card * U.card : ℕ) : ℝ)
        ^ (BilinearComplexity.omega / 3)) ^ 3
      ≤ charDegreeSumReal G (BilinearComplexity.omega + ε) ^ 3 := by
    refine le_of_pow_le_const_mul_pow (K := C ^ 3) (pow_nonneg hs0 3)
      fun ℓ hℓ => ?_
    rw [hcube_id]
    exact pow_omega_pow_le_of_tpp h hN hC hℓ
  exact le_of_pow_le_pow_left₀ (by norm_num) hs0 hA

end CohnUmansChain

/-! ### Cohn–Umans Theorem 4.1 (proved) -/

/-- **Cohn–Umans Theorem 4.1, `β`-form** [math/0307321, `theorem:bound`,
CU.tex:603–609].

If `G` has TPP capacity `β(G) = tppCapacity G` and complex irreducible character
degrees `{dᵢ}`, then

  `β(G)^{ω/3} ≤ Σᵢ dᵢ^ω = D_ω(G)`.

This is the form the program actually uses: a single group with large `β(G)`
and small `D_ω(G)` bounds `ω`. (It is equivalent to the pseudo-exponent form
`card_rpow_le_charDegreeSumReal` via `β(G) = |G|^{3/α(G)}`.)

**Proof** (CU.tex:621–666, assembled from the `CohnUmansChain` section): the
capacity is attained by a TPP triple `(S, T, U)` with `N = |S|·|T|·|U|`
(`Finset.exists_mem_eq_sup`). If `N ≤ 1` the bound reads `1 ≤ D_ω(G)`
(`one_le_charDegreeSumReal`). For `N ≥ 2`, the per-`(ℓ, ε)` chain gives
`(N^ω)^ℓ ≤ C³·(D_{ω+ε}(G)³)^ℓ`; letting `ℓ → ∞` absorbs `C³`
(`le_of_pow_le_const_mul_pow`), a cube root gives `N^{ω/3} ≤ D_{ω+ε}(G)`,
and `ε := 1/ℓ → 0⁺` closes via `D_{ω+ε}(G) ≤ |G|^ε·D_ω(G)`
(`charDegreeSumReal_add_le`, `le_of_forall_rpow_one_div_mul`). -/
theorem capacity_rpow_le_charDegreeSumReal (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] :
    (tppCapacity G : ℝ) ^ (ω / 3) ≤ charDegreeSumReal G ω := by
  show (tppCapacity G : ℝ) ^ (BilinearComplexity.omega / 3)
      ≤ charDegreeSumReal G BilinearComplexity.omega
  have homega0 : (0 : ℝ) ≤ BilinearComplexity.omega :=
    le_trans (by norm_num) BilinearComplexity.two_le_omega
  -- the capacity is attained by a TPP triple
  have hne : (tppTriples G).Nonempty :=
    ⟨(Finset.univ, {1}, {1}), mem_tppTriples.mpr tpp_trivial⟩
  obtain ⟨p, hpmem, hpsup⟩ :=
    Finset.exists_mem_eq_sup (tppTriples G) hne
      (fun p => p.1.card * p.2.1.card * p.2.2.card)
  obtain ⟨S, T, U⟩ := p
  have hTPP : TripleProductProperty S T U := mem_tppTriples.mp hpmem
  have hβeq : tppCapacity G = S.card * T.card * U.card := hpsup
  rw [hβeq]
  rcases le_or_gt (S.card * T.card * U.card) 1 with hN1 | hN2
  · -- degenerate maximizer (`N ≤ 1`, i.e. the trivial group): `1 ≤ D_ω(G)`
    have hle1 : ((S.card * T.card * U.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hN1
    exact le_trans
      (Real.rpow_le_one (Nat.cast_nonneg _) hle1
        (div_nonneg homega0 (by norm_num)))
      (one_le_charDegreeSumReal G homega0)
  · -- `N ≥ 2`: the `ε := 1/ℓ` diagonal against root convergence
    refine le_of_forall_rpow_one_div_mul (B := (Fintype.card G : ℝ))
      (by exact_mod_cast Fintype.card_pos) fun ℓ hℓ => ?_
    have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hℓ
    have hεpos : (0 : ℝ) < 1 / (ℓ : ℝ) := one_div_pos.mpr hℓR
    exact le_trans (rpow_le_charDegreeSumReal_add hTPP hN2 hεpos)
      (charDegreeSumReal_add_le G BilinearComplexity.omega hεpos.le)

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
right-hand side. With Theorem 4.1 now proved, this form is `sorry`-free
end-to-end. -/
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

/-! ### The `D₃` threshold certificate (proved)

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

Fully defined and `sorry`-free: the `D₃(G) = charDegreeSum G 3` side is
computed from the canonical `Xlib.CharDegrees.charDegrees` (the indexed
Wedderburn layer, landed with the `Wd` campaign), and the
`β(G) = tppCapacity G` side is the `sorry`-free TPP capacity. Concretely,
`#print axioms BetaExceedsD3` reports exactly
`[propext, Classical.choice, Quot.sound]`. -/
def BetaExceedsD3 (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Prop :=
  (charDegreeSum G 3 : ℝ) < (tppCapacity G : ℝ)

/-- **The `D₃` certificate** [math/0307321, CU.tex:766–768]: if `G`'s TPP
capacity strictly exceeds its cubic character-degree sum, `D₃(G) < β(G)`, then
the matrix-multiplication exponent is strictly subcubic, `ω < 3`.

This is the precise sense in which "a single group certifies `ω < 3`", and it is
**proved here in full from Theorem 4.1** (`capacity_rpow_le_charDegreeSumReal`)
together with `matrixExponent_le_three`. The argument is the boundary evaluation,
not the general convexity step: were `ω = 3`, Theorem 4.1 would read
`β(G)^{3/3} = β(G) ≤ charDegreeSumReal G 3 = D₃(G)` (via `Real.rpow_one` and
`Xlib.CharDegrees.charDegreeSumReal_natCast`), contradicting `D₃(G) < β(G)`;
hence `ω ≠ 3`, and `ω ≤ 3` then forces `ω < 3`.

Proved end-to-end with no remaining debt: Theorem 4.1
(`capacity_rpow_le_charDegreeSumReal`) and the `charDegrees` foundation are
both `sorry`-free, so `#print axioms betaExceedsD3_certifies_subcubic` reports
exactly `[propext, Classical.choice, Quot.sound]`. -/
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
condition"; that equivalence is real only because Theorem 4.1 holds
(`capacity_rpow_le_charDegreeSumReal`, now proved), which this statement
neither invokes nor needs. All this says is that the two *literal expressions*
coincide: after
collapsing the exponent `3/3 = 1` (so `β^{3/3} = β` by `Real.rpow_one`) and
bridging `charDegreeSumReal G 3 = (charDegreeSum G 3 : ℝ)`
(`Xlib.CharDegrees.charDegreeSumReal_natCast`), the goal is exactly
`¬ (β ≤ D₃) ↔ D₃ < β`, which is `not_le`. In short it restates `BetaExceedsD3`
in the "negated-bound" shape; it makes no claim about `ω` at all.

Axiom footprint: `#print axioms subcubic_certificate_iff` reports exactly
`[propext, Classical.choice, Quot.sound]` — this statement never mentions `ω`,
so it does not even depend on the existence of the exponent. -/
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
