/- Existing STPP capacity admissions and their dependent specialization, relocated unchanged.
The direct-sum tensor/Schönhage assembly remains unpaid; the one-shot wreath
factorial bound does not discharge it. -/
import GroupTPP.STPPWreath

/-!
# Retired implementation card: CKSU STPP and wreath inequalities

These are published results from Cohn–Kleinberg–Szegedy–Umans,
arXiv:math/0511460, not open mathematical conjectures. Only the central
simultaneous-TPP capacity and wreath-specialization portions belong to this
archive. The chart-USP construction and `ω < 2.41` derivation remain separate
in `Formalize/GroupTPP-Barriers-Lie-ChartUSP.md`.

Production retains the right-quotient, cyclic `SimultaneousTPP` convention,
direct-product closure, wreath embeddings, character-degree bounds and
asymptotic witness families. The general capacity theorem below uses `[Group G]`;
the hypothesis-factored wreath skeleton and its dependent commutative
specialization use `[CommGroup G]`, with their displayed finiteness/decidability
hypotheses unchanged. The skeleton is admitted, not proved; the commutative
theorem inherits `sorryAx` despite its independently proved input planks.
The missing direct-sum tensor/Schönhage asymptotic sum inequality and
multinomial/wreath amplification must be formalized and their downstream
consumers audited. The one-shot factorial estimate and proved constructions
or convergence statements do not discharge those central inequalities.
Retirement completes a faithful admission boundary, not the published proof.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.STPPWreath

open GroupTPP.TPP GroupTPP.CUCapacity GroupTPP.CharDegrees

variable {G : Type*} [Group G]

/-! ### The STPP capacity inequality (CKSU `theorem:asi`, `sorry`)

The multi-triple analogue of `GroupTPP.CUCapacity.capacity_rpow_le_charDegreeSumReal`
(CU Theorem 4.1). Whereas the single-triple bound reads
`(|S|·|T|·|U|)^{ω/3} ≤ D_ω(G)`, the STPP packs `n` independent triples into one
group-algebra multiplication, giving a *sum* on the left. -/

/-- **CKSU Theorem `theorem:asi`** [math/0511460]: the **STPP capacity
inequality**. If the `n` triples `(A i, B i, C i)` of a finite group `G` satisfy
the STPP, then

  `∑ᵢ (|A i| · |B i| · |C i|)^{ω/3} ≤ D_ω(G) = ∑ₖ dₖ^ω`.

This is the multi-triple version of CU Theorem 4.1
(`GroupTPP.CUCapacity.capacity_rpow_le_charDegreeSumReal`). For abelian `G` the
right-hand side collapses to `|G|` (`GroupTPP.CharDegrees.charDegreeSum_two`), the
form used in the `ω < 2.93` example.

**Proof route** (Pl21, Clifford campaign): the general-`G` form requires
Clifford theory for the wreath character-degree bound and the corrected
`SimultaneousTPP` definition (Df1). The hypothesis-factored skeleton
(`stpp_capacity_le_of_wreath`) is also admitted below. The abelian instance
(`stpp_capacity_le_comm`) is derived from it and therefore also depends on
`sorryAx`; neither is an independent proof of the capacity inequality. -/
theorem stpp_capacity_le {n : ℕ} [Fintype G] [DecidableEq G]
    (A B C : Fin n → Finset G) (h : SimultaneousTPP A B C) :
    ∑ i, ((A i).card * (B i).card * (C i).card : ℝ) ^ (ω / 3)
      ≤ charDegreeSumReal G ω :=
  sorry

/-! ### The STPP capacity inequality — hypothesis-factored skeleton and CommGroup instance

The hypothesis-factored skeleton `stpp_capacity_le_of_wreath` (Hu8-1c / Hu10-B)
takes the two generality-varying planks — the n!-carrier TPP lift and the wreath
D_ω bound — as explicit hypotheses. The CommGroup instance
`stpp_capacity_le_comm` instantiates them with the sorry-free abelian planks. -/

/-- **CKSU `theorem:asi`, hypothesis-factored skeleton** (Hu8-1c / Hu10-B).
See the docstring on `stpp_capacity_le` for the full mathematical statement.

**Hypotheses (the two generality-varying planks):**
* `htpp` — the n!-carrier TPP lift (shape of `stpp_to_tpp_wreath_card`).
* `hbound` — the wreath D_ω bound (shape of `wreath_charDegree_bound`).

**Blocker:** the multinomial assembly — producing the hypothesis of
`sum_le_of_multinomial_prod_pow_le` from the wreath capacity chain. -/
theorem stpp_capacity_le_of_wreath
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {n : ℕ} (A B C : Fin n → Finset G) (h : SimultaneousTPP A B C)
    (htpp : ∀ (ℓ : ℕ) (m : ℕ) (A' B' C' : Fin m → Finset (Fin ℓ → G)),
      SimultaneousTPP A' B' C' →
      ∃ S T U : Finset (ImprimitiveWreathProduct (Fin ℓ → G) m),
        TripleProductProperty S T U
        ∧ S.card = m.factorial * ∏ i, (A' i).card
        ∧ T.card = m.factorial * ∏ i, (B' i).card
        ∧ U.card = m.factorial * ∏ i, (C' i).card)
    (hbound : ∀ (ℓ m : ℕ),
      charDegreeSumReal (ImprimitiveWreathProduct (Fin ℓ → G) m) ω
        ≤ (Nat.factorial m : ℝ) ^ (ω - 1)
          * (charDegreeSumReal (Fin ℓ → G) ω) ^ m) :
    ∑ i, ((A i).card * (B i).card * (C i).card : ℝ) ^ (ω / 3)
      ≤ charDegreeSumReal G ω := by
  sorry

/-- **`[CommGroup G]` instance of the STPP capacity inequality** (Hu8-1c /
Hu10-B): instantiation of `stpp_capacity_le_of_wreath` with the sorry-free
abelian planks `stpp_to_tpp_wreath_card` and `wreath_charDegree_bound`. -/
theorem stpp_capacity_le_comm
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {n : ℕ} (A B C : Fin n → Finset G) (h : SimultaneousTPP A B C) :
    ∑ i, ((A i).card * (B i).card * (C i).card : ℝ) ^ (ω / 3)
      ≤ charDegreeSumReal G ω := by
  apply stpp_capacity_le_of_wreath A B C h
  · intro ℓ m A' B' C' hstpp
    exact stpp_to_tpp_wreath_card A' B' C' hstpp
  · intro ℓ m
    exact wreath_charDegree_bound m

end GroupTPP.STPPWreath
