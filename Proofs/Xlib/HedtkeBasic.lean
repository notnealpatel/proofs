import Mathlib
import Xlib.TPP

/-!
# Translating a TPP triple to a basic one

This file formalizes the **"WLOG basic" reduction** for Triple Product Property
triples: *any* TPP triple can be left-translated, factor by factor, to a
**basic** TPP triple (one containing the identity in each set), and the
translation preserves the three cardinalities.

This is the reduction remarked on by Hedtke–Murthy
[arXiv:1104.5097, just after Lemma `lemm:Neumann`, "Note that any TPP triple
can be translated to a basic TPP triple"], resting on the
**translation-invariance** of the TPP, originally Neumann's Observation 2.1
[ibid., Lemma `lemm:Neumann`]: if `(S, T, U)` is a TPP triple then so is
`(dSa, dTb, dUc)`.

The TPP in `Xlib.TPP` is the *left-quotient* form
`s'⁻¹ s · t'⁻¹ t · u'⁻¹ u = 1 → s = s' ∧ t = t' ∧ u = u'`
(matching Murthy / Wikipedia). For this convention the invariant translations
are exactly the **left** translations `S ↦ d • S`, acting independently on each
factor: a left translate has the *same* left-quotient set as the original,
because `(d s')⁻¹ (d s) = s'⁻¹ s`. (Neumann's right translates `S ↦ S a`
conjugate the right-quotient set, the convention used in [1104.5097].) No
commutativity and no finiteness are needed.

This reduction is *why* `Xlib.TPP.inter_ST_eq_one_of_basic` and its siblings —
the basic-triple pairwise-intersection equalities `S ∩ T = T ∩ U = S ∩ U = 1` —
are not a loss of generality: they apply to the translated representative of
*every* TPP triple, which has the same cardinalities, hence the same
`|S| · |T| · |U|`.

## Main definitions

* `Xlib.HedtkeBasic.IsBasic` — `(S, T, U)` is *basic* when `1 ∈ S ∩ T ∩ U`.

## Main results

* `Xlib.TPP.TripleProductProperty.smul` — **translation invariance**: if
  `(S, T, U)` has the TPP then so does `(d • S, e • T, f • U)` for any
  `d e f : G`.
* `Xlib.HedtkeBasic.exists_basic_of_tpp` — **Hedtke's WLOG-basic reduction**:
  every TPP triple of nonempty sets left-translates to a *basic* TPP triple
  with the same three cardinalities (hence the same product `|S|·|T|·|U|`).

## References

* J. Hedtke, I. Murthy (notation), *Search and test algorithms for Triple
  Product Property triples*, [arXiv:1104.5097]; the translation remark follows
  Lemma `lemm:Neumann` (P. Neumann, Observation 2.1).
* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, [arXiv:math/0307321].
-/

open scoped Pointwise

namespace Xlib.TPP

variable {G : Type*} [Group G]

/-- **Translation invariance of the TPP** (Neumann's Observation 2.1,
Hedtke–Murthy [arXiv:1104.5097, Lemma `lemm:Neumann`], adapted to the
left-quotient convention).

If `(S, T, U)` has the Triple Product Property, then so does the factorwise
**left**-translate `(d • S, e • T, f • U)` for *any* `d e f : G`. The proof is a
pure cancellation: writing each translated element as `d * a` (`a` in the
original set), every left quotient `(d a')⁻¹ (d a)` collapses to `a'⁻¹ a`, so
the TPP hypothesis on the translate is *literally* the TPP hypothesis on the
original. No commutativity or finiteness is used. -/
theorem TripleProductProperty.smul [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (d e f : G) :
    TripleProductProperty (d • S) (e • T) (f • U) := by
  intro s hs s' hs' t ht t' ht' u hu u' hu' heq
  rw [Finset.mem_smul_finset] at hs hs' ht ht' hu hu'
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨a', ha', rfl⟩ := hs'
  obtain ⟨b, hb, rfl⟩ := ht
  obtain ⟨b', hb', rfl⟩ := ht'
  obtain ⟨c, hc, rfl⟩ := hu
  obtain ⟨c', hc', rfl⟩ := hu'
  -- The translated hypothesis collapses to the original left-quotient equation,
  -- since each left quotient `(d a')⁻¹ (d a)` cancels the translation to `a'⁻¹ a`.
  simp only [smul_eq_mul] at heq
  have hquot : a'⁻¹ * a * b'⁻¹ * b * c'⁻¹ * c = 1 := by
    rw [← heq]; group
  obtain ⟨hsa, hsb, hsc⟩ := h a ha a' ha' b hb b' hb' c hc c' hc' hquot
  exact ⟨by rw [hsa], by rw [hsb], by rw [hsc]⟩

/-! ### The basic-triple reduction -/

end Xlib.TPP

namespace Xlib.HedtkeBasic

variable {G : Type*} [Group G]

open Xlib.TPP

/-- A triple `(S, T, U)` of subsets is **basic** (Hedtke–Murthy
[arXiv:1104.5097, Def. "basic TPP triple", after P. Neumann]) when the identity
lies in all three: `1 ∈ S`, `1 ∈ T`, `1 ∈ U` (i.e. `1 ∈ S ∩ T ∩ U`). -/
def IsBasic (S T U : Finset G) : Prop :=
  (1 : G) ∈ S ∧ (1 : G) ∈ T ∧ (1 : G) ∈ U

/-- **Hedtke's WLOG-basic reduction** [arXiv:1104.5097, the remark following
Lemma `lemm:Neumann`]: every TPP triple of nonempty sets can be left-translated,
factor by factor, to a **basic** TPP triple with the *same* three
cardinalities.

Concretely, choosing `s₀ ∈ S`, `t₀ ∈ T`, `u₀ ∈ U`, the translate
`(s₀⁻¹ • S, t₀⁻¹ • T, u₀⁻¹ • U)` has the TPP (translation invariance), contains
the identity in each set (since `s₀⁻¹ • s₀ = 1`, etc.), and preserves
cardinalities (left translation is a bijection). This is why the basic-triple
intersection identities `S ∩ T = T ∩ U = S ∩ U = 1`
(`Xlib.TPP.inter_ST_eq_one_of_basic`) lose no generality. -/
theorem exists_basic_of_tpp [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) :
    ∃ S' T' U' : Finset G,
      TripleProductProperty S' T' U' ∧ IsBasic S' T' U' ∧
        S'.card = S.card ∧ T'.card = T.card ∧ U'.card = U.card := by
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨t₀, ht₀⟩ := hT
  obtain ⟨u₀, hu₀⟩ := hU
  refine ⟨s₀⁻¹ • S, t₀⁻¹ • T, u₀⁻¹ • U, h.smul s₀⁻¹ t₀⁻¹ u₀⁻¹, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_smul_finset.mpr ⟨s₀, hs₀, by simp⟩
    · exact Finset.mem_smul_finset.mpr ⟨t₀, ht₀, by simp⟩
    · exact Finset.mem_smul_finset.mpr ⟨u₀, hu₀, by simp⟩
  · exact Finset.card_smul_finset _ _
  · exact Finset.card_smul_finset _ _
  · exact Finset.card_smul_finset _ _

/-- **The payoff of the WLOG-basic reduction.** Combining
`exists_basic_of_tpp` with the basic-triple intersection identities
`Xlib.TPP.inter_ST_eq_one_of_basic` (and its `TU` / `SU` siblings), *every* TPP
triple of nonempty sets left-translates to a TPP triple whose three pairwise
intersections are each exactly the trivial subgroup `{1}`, with the same three
cardinalities.

This is Hedtke–Murthy's Observation `ob:Intersec`
[arXiv:1104.5097, "It is sufficient to search TPP triples with
`S ∩ T = T ∩ U = S ∩ U = 1`"]: the intersection equalities `(***)`, which a
priori require a *basic* triple, in fact constrain a representative of every TPP
triple, so they may be assumed without loss of generality. -/
theorem exists_pairwise_inter_one_of_tpp [DecidableEq G] {S T U : Finset G}
    (h : TripleProductProperty S T U) (hS : S.Nonempty) (hT : T.Nonempty)
    (hU : U.Nonempty) :
    ∃ S' T' U' : Finset G,
      TripleProductProperty S' T' U' ∧
        S' ∩ T' = {1} ∧ T' ∩ U' = {1} ∧ S' ∩ U' = {1} ∧
          S'.card = S.card ∧ T'.card = T.card ∧ U'.card = U.card := by
  obtain ⟨S', T', U', hTPP', ⟨h1S, h1T, h1U⟩, hcS, hcT, hcU⟩ :=
    exists_basic_of_tpp h hS hT hU
  exact ⟨S', T', U', hTPP',
    inter_ST_eq_one_of_basic hTPP' h1S h1T h1U,
    inter_TU_eq_one_of_basic hTPP' h1S h1T h1U,
    inter_SU_eq_one_of_basic hTPP' h1S h1T h1U,
    hcS, hcT, hcU⟩

end Xlib.HedtkeBasic
