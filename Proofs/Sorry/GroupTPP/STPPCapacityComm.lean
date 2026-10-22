import Sorry.GroupTPP.STPPEqualVolume
import GroupTPP.FactorialAmplification
import GroupTPP.STPPTypeCount
import GroupTPP.GeomArithInequality

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.STPPWreath

open GroupTPP.TPP GroupTPP.CUCapacity GroupTPP.CharDegrees

/-- **CKSU `theorem:asi`, hypothesis-factored skeleton** (Hu8-1c / Hu10-B).
The STPP capacity inequality bounds the sum of the triple volumes raised to
`ω / 3` by the character-degree sum of the ambient group.

**Hypotheses (the two generality-varying planks):**
* `htpp` — the n!-carrier TPP lift (shape of `stpp_to_tpp_wreath_card`).
* `hbound` — the wreath D_ω bound (shape of `wreath_charDegree_bound`).

**Proof:** prescribed-type label words are counted by the multinomial and
retain their labels even when product sets coincide. All-powers factorial
amplification gives the exact multinomial hypothesis of
`sum_le_of_multinomial_prod_pow_le`, including zero volumes and empty words. -/
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
  classical
  let v : Fin n → ℕ := fun i => (A i).card * (B i).card * (C i).card
  have hD1 : 1 ≤ charDegreeSumReal G ω := by
    rw [GroupTPP.CharDegreesComm.charDegreeSumReal_of_commGroup]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)
  have hD : 0 ≤ charDegreeSumReal G ω := le_trans (by norm_num) hD1
  apply GroupTPP.GeomArithInequality.sum_le_of_multinomial_prod_pow_le hD
  intro N μ hsum
  let X := {f : Fin N → Fin n //
    ∀ i, (Finset.univ.filter (fun j => f j = i)).card = μ i}
  let M := Nat.multinomial Finset.univ μ
  have hcard : Fintype.card X = M := TypeCount.card_words n N μ hsum
  have hm : 1 ≤ M := Nat.multinomial_pos Finset.univ μ
  let e : Fin M ≃ X := (Fintype.equivOfCardEq (by simpa using hcard.symm))
  let Φ : Fin M → Fin N → Fin n := fun p => (e p).val
  have hΦ : Function.Injective Φ := by
    intro p q hpq
    apply e.injective
    exact Subtype.ext hpq
  let V : ℕ := ∏ i, v i ^ μ i
  have hV : ∀ p, ∏ j : Fin N,
      (A (Φ p j)).card * (B (Φ p j)).card * (C (Φ p j)).card = V := by
    intro p
    exact TypeCount.prod_word n N μ (e p) v
  have hscalar : (M : ℝ) * (V : ℝ) ^ (ω / 3) ≤ (charDegreeSumReal G ω) ^ N :=
    mul_le_of_factorial_amplification M hm _ _ (by positivity)
      (pow_nonneg hD N) (fun t ht =>
        stpp_equal_volume_factorial_chain A B C h htpp hbound N M hm Φ hΦ V hV t ht)
  have hregroup : (V : ℝ) ^ (ω / 3) =
      ∏ i, ((v i : ℝ) ^ (ω / 3)) ^ μ i := by
    simp only [V, Nat.cast_prod, Nat.cast_pow]
    rw [← Real.finsetProd_rpow]
    · apply Finset.prod_congr rfl
      intro i hi
      exact (Real.rpow_pow_comm (by positivity) (ω / 3) (μ i)).symm
    · intro i hi
      positivity
  rw [hregroup] at hscalar
  simpa only [M, v, Nat.cast_mul] using hscalar

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

-- A concrete nonempty, nontrivial model jointly realizes the STPP and both
-- displayed wreath premises; its volume sum is one and its ambient degree sum two.
example : (1 : ℝ) ≤ charDegreeSumReal (Multiplicative (ZMod 2)) ω := by
  let A : Fin 1 → Finset (Multiplicative (ZMod 2)) := fun _ => {1}
  have h : SimultaneousTPP A A A := by
    constructor
    · intro i
      simp [A, TripleProductPropertyR]
    · intro i j k a ha a' ha' b hb b' hb' c hc c' hc' heq
      exact ⟨Subsingleton.elim i j, Subsingleton.elim j k⟩
  have hcapacity := stpp_capacity_le_of_wreath A A A h
    (fun ℓ m A' B' C' hs => stpp_to_tpp_wreath_card A' B' C' hs)
    (fun ℓ m => wreath_charDegree_bound (H := Fin ℓ → Multiplicative (ZMod 2)) m)
  simpa [A] using hcapacity

end GroupTPP.STPPWreath
