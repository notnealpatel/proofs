import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators symmDiff Classical

namespace LittlewoodOfford

private theorem sum_indicator {α : Type*} [Fintype α]
    (S : Finset α) (a : α → ℝ) :
    (∑ i : α, if i ∈ S then a i else 0) = ∑ i ∈ S, a i := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- Flipping membership at the negative weights converts a subset sum into an
absolute-weight subset sum, with a constant translation. -/
theorem sum_abs_symmDiff_negatives {α : Type*} [Fintype α]
    (a : α → ℝ) (S : Finset α) :
    (∑ i ∈ S ∆ (Finset.univ.filter fun i => a i < 0), |a i|) =
      (∑ i ∈ S, a i) - ∑ i ∈ Finset.univ.filter (fun i => a i < 0), a i := by
  classical
  rw [← sum_indicator (S ∆ (Finset.univ.filter fun i => a i < 0)) (fun i => |a i|),
    ← sum_indicator S a,
    ← sum_indicator (Finset.univ.filter fun i => a i < 0) a,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hneg : a i < 0 <;> by_cases hS : i ∈ S
  · simp [Finset.mem_symmDiff, hS, hneg]
  · simp [Finset.mem_symmDiff, hS, hneg, abs_of_neg hneg]
  · simp [Finset.mem_symmDiff, hS, hneg, abs_of_nonneg (le_of_not_gt hneg)]
  · simp [Finset.mem_symmDiff, hS, hneg]

private theorem interval_antichain {α : Type*} [Fintype α]
    (b : α → ℝ) (d t : ℝ) (hd : 0 < d) (hb : ∀ i, d ≤ b i) :
    IsAntichain (· ⊆ ·) {S : Finset α | t ≤ ∑ i ∈ S, b i ∧
      (∑ i ∈ S, b i) < t + d} := by
  intro S hS T hT hne hST
  have hTS : ¬ T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
  have hi : i ∈ T \ S := Finset.mem_sdiff.mpr ⟨hiT, hiS⟩
  have hsingle : ({i} : Finset α) ⊆ T \ S := Finset.singleton_subset_iff.mpr hi
  have hsum : b i ≤ ∑ j ∈ T \ S, b j := by
    simpa using Finset.sum_le_sum_of_subset_of_nonneg hsingle
      (fun j _ _ => le_trans (le_of_lt hd) (hb j))
  have hsplit := Finset.sum_sdiff (f := b) hST
  have hgap : d + (∑ j ∈ S, b j) ≤ ∑ j ∈ T, b j := by
    linarith [hb i]
  linarith [hS.1, hT.2]

/-- The classical real Littlewood–Offord bound for half-open subset-sum intervals.
Weights may repeat and may be negative; the empty index type is allowed.
This is the subset-sum variant of Erdős (1945), Theorem 1,
DOI 10.1090/S0002-9904-1945-08454-7, not a novelty claim. -/
theorem subset_sum_interval_card_le_choose {α : Type*} [Fintype α]
    (a : α → ℝ) (d t : ℝ) (hd : 0 < d) (ha : ∀ i, d ≤ |a i|) :
    ((Finset.univ : Finset (Finset α)).filter
      (fun S => t ≤ ∑ i ∈ S, a i ∧ (∑ i ∈ S, a i) < t + d)).card ≤
      (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
  let N := Finset.univ.filter (fun i => a i < 0)
  let F := (Finset.univ : Finset (Finset α)).filter
    (fun S => t ≤ ∑ i ∈ S, a i ∧ (∑ i ∈ S, a i) < t + d)
  let flip : Finset α → Finset α := fun S => S ∆ N
  have hinj : Function.Injective flip := by
    intro S T h
    have heq := congrArg (fun U => U ∆ N) h
    simpa only [flip, symmDiff_symmDiff_cancel_right] using heq
  have himage : IsAntichain (· ⊆ ·) (F.image flip : Set (Finset α)) := by
    have hanti := interval_antichain (fun i => |a i|) d
      (t - ∑ i ∈ N, a i) hd ha
    apply hanti.subset
    intro U hU
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
    have hmem := (Finset.mem_filter.mp hS).2
    change t - (∑ i ∈ N, a i) ≤ (∑ i ∈ flip S, |a i|) ∧
      (∑ i ∈ flip S, |a i|) < t - (∑ i ∈ N, a i) + d
    have heq : (∑ i ∈ flip S, |a i|) =
        (∑ i ∈ S, a i) - ∑ i ∈ N, a i := sum_abs_symmDiff_negatives a S
    rw [heq]
    constructor <;> linarith [hmem.1, hmem.2]
  have hbound := himage.sperner
  rw [Finset.card_image_of_injective F hinj] at hbound
  exact hbound

example : (0 : ℝ) < 1 ∧ (∀ _i : Fin 0, (1 : ℝ) ≤ |(-1 : ℝ)|) ∧
    ((Finset.univ : Finset (Finset (Fin 0))).filter
      (fun S => (0 : ℝ) ≤ ∑ _i ∈ S, (-1 : ℝ) ∧
        (∑ _i ∈ S, (-1 : ℝ)) < 0 + 1)).card ≤ 1 := by
  refine ⟨by norm_num, by intro i; norm_num, ?_⟩
  simpa using subset_sum_interval_card_le_choose (fun _ : Fin 0 => (-1 : ℝ))
    1 0 (by norm_num) (by intro i; norm_num)

example : (0 : ℝ) < 1 ∧ (∀ _i : Fin 2, (1 : ℝ) ≤ |(-1 : ℝ)|) ∧
    ((Finset.univ : Finset (Finset (Fin 2))).filter
      (fun S => (-1 : ℝ) ≤ ∑ _i ∈ S, (-1 : ℝ) ∧
        (∑ _i ∈ S, (-1 : ℝ)) < -1 + 1)).card ≤ 2 := by
  refine ⟨by norm_num, by intro i; norm_num, ?_⟩
  simpa using subset_sum_interval_card_le_choose (fun _ : Fin 2 => (-1 : ℝ))
    1 (-1) (by norm_num) (by intro i; norm_num)

end LittlewoodOfford
