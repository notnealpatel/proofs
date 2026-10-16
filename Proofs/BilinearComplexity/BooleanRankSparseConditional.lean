import BilinearComplexity.BooleanRankSparseMoment
import BilinearComplexity.BooleanRankCounting

set_option autoImplicit false

open scoped BigOperators
namespace BilinearComplexity.BooleanRankSparseConditional
open BilinearComplexity.BooleanRankProbability
open BilinearComplexity.BooleanRankSparseMoment

/-- An exact OR representation covers the target by selected rows contained in
it, so the target cardinality is bounded by the total contained-row size. -/
theorem card_le_contained_sum {m n : ℕ} (A : BoolMatrix m n)
    (S : Finset (Fin n)) (T : Finset (Fin m))
    (h : rowsSum A T = fun c => if c ∈ S then 1 else 0) :
    S.card ≤ ∑ i : Fin m, if ∀ c, A i c = 1 → c ∈ S then
      (Finset.univ.filter fun c => A i c = 1).card else 0 := by
  classical
  let R := fun i : Fin m => Finset.univ.filter fun c => A i c = 1
  have hselected : ∀ i ∈ T, ∀ c, A i c = 1 → c ∈ S := by
    intro i hi c hic
    have hc : rowsSum A T c = 1 :=
      (BoolSemiring.sum_eq_one_iff T _).mpr ⟨i, hi, hic⟩
    rw [h] at hc
    by_contra hnot
    simp [hnot] at hc
  have hcover : S ⊆ T.biUnion R := by
    intro c hc
    have hone : rowsSum A T c = 1 := by simp [h, hc]
    obtain ⟨i, hi, hic⟩ := (BoolSemiring.sum_eq_one_iff T _).mp hone
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [R, hic]⟩
  calc
    S.card ≤ (T.biUnion R).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ T, (R i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ T, if ∀ c, A i c = 1 → c ∈ S then (R i).card else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (hselected i hi)]
    _ ≤ ∑ i : Fin m, if ∀ c, A i c = 1 → c ∈ S then (R i).card else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      intro i hi hnot
      exact Nat.zero_le _

/-- The exact matrix moment factors as the product of the exact row moments. -/
theorem matrix_contained_moment (m n : ℕ) (S : Finset (Fin n)) (p z : ℝ) :
    (∑ A : BoolMatrix m n, matrixWeight p A *
      z ^ (∑ i : Fin m, if ∀ c, A i c = 1 → c ∈ S then
        (Finset.univ.filter fun c => A i c = 1).card else 0)) =
      (1 - (1 - p) ^ (n - S.card) +
        (1 - p) ^ (n - S.card) * ((1 - p) + p * z) ^ S.card) ^ m := by
  classical
  simp_rw [← Finset.prod_pow_eq_pow_sum, matrixWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (x : Fin n → BoolSemiring) =>
    (∏ j, entryWeight p (x j)) * z ^ (if ∀ c, x c = 1 → c ∈ S then
      (Finset.univ.filter fun c => x c = 1).card else 0))]
  simp only [support_conditioned_moment, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A finite exponential bound for the actual event that some set of displayed
rows has OR equal to the indicator of `S`, including the empty witness. -/
theorem or_representation_mass_le (m n : ℕ) (S : Finset (Fin n))
    (p z : ℝ) (hp : 0 < p) (hp1 : p < 1) (hz : 1 ≤ z) :
    z ^ S.card * (∑ A : BoolMatrix m n,
      if ∃ T : Finset (Fin m), rowsSum A T = (fun c => if c ∈ S then 1 else 0)
      then matrixWeight p A else 0) ≤
      (1 - (1 - p) ^ (n - S.card) +
        (1 - p) ^ (n - S.card) * ((1 - p) + p * z) ^ S.card) ^ m := by
  classical
  rw [Finset.mul_sum, ← matrix_contained_moment m n S p z]
  apply Finset.sum_le_sum
  intro A hA
  have hw : 0 ≤ matrixWeight p A := matrixWeight_nonneg p hp hp1 A
  split_ifs with hevent
  · obtain ⟨T, hT⟩ := hevent
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hz (card_le_contained_sum A S T hT)) hw).trans_eq
      (mul_comm _ _)
  · simpa using mul_nonneg hw (pow_nonneg (le_trans (by norm_num) hz) _)

example : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧ (1 : ℝ) ≤ 2 ∧
    rowsSum (fun _ _ => 1 : BoolMatrix 1 1) {0} =
      (fun c => if c ∈ ({0} : Finset (Fin 1)) then 1 else 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  funext c
  have hc : c = 0 := Subsingleton.elim c 0
  simp [rowsSum, hc]

example : Nonempty (BoolMatrix 0 0) ∧ Nonempty (BoolMatrix 2 3) ∧
    Nonempty (Finset (Fin 0)) := ⟨⟨0⟩, ⟨0⟩, ⟨∅⟩⟩

end BilinearComplexity.BooleanRankSparseConditional
