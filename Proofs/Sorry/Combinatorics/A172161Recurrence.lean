import Sorry.Combinatorics.GreedyCWAsymptotic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit false

namespace Candidates.A172161

/-- The offset-1 recurrence sequence, with an unused zero at index 0.
The guarded recursive calls have the same values as the sum over all indices below n. -/
def a172161 : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | n + 5 => (∑ i ∈ Finset.range (n + 5),
      if _h : i < n + 5 then a172161 i else 0) / 2 + 1
termination_by n => n

example : a172161 0 = 0 := by rw [a172161]
example : a172161 1 = 0 := by rw [a172161]
example : a172161 2 = 1 := by rw [a172161]
example : a172161 3 = 2 := by rw [a172161]
example : a172161 4 = 3 := by rw [a172161]

/-- Unfolding the defining recurrence, not a proof of greedy semantics. -/
theorem cwGreedy_eq_recurrence (n : ℕ) (hn : 4 < n) :
    a172161 n = (∑ i ∈ Finset.range n, a172161 i) / 2 + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
  rw [a172161]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- The recurrence sequence equals the actual least-admissible greedy sequence
at every index, including the unused index 0. -/
theorem a172161_eq_greedyA (n : ℕ) : a172161 n = GreedyCW.greedyA n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 4 < n
    · rw [cwGreedy_eq_recurrence n hn, GreedyCW.greedyA_recurrence n hn]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      exact ih i (Finset.mem_range.mp hi)
    · interval_cases n <;>
        simp [a172161, GreedyCW.greedyA_three, GreedyCW.greedyA_four]

/-- McEachen's positive quotient limit transferred from the greedy semantics. -/
theorem mcEachen_growth :
    ∃ k : ℝ, 0 < k ∧
      Filter.Tendsto (fun n : ℕ => (a172161 n : ℝ) / (3 / 2 : ℝ) ^ n)
        Filter.atTop (nhds k) := by
  simpa only [a172161_eq_greedyA] using GreedyCW.mcEachen_growth

/-- The positive finite quotient limit gives two-sided big-O growth. -/
theorem a172161_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (a172161 n : ℝ))
      (fun n : ℕ => (3 / 2 : ℝ) ^ n) := by
  obtain ⟨k, hk, hlim⟩ := mcEachen_growth
  exact (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hlim (ne_of_gt hk)).symm

/-- Partial sums of the recurrence sequence. -/
def cwSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a172161 i

/-- Partial sums agree with the semantic partial sums. -/
theorem cwSum_eq_sumA (n : ℕ) : cwSum n = GreedyCW.sumA n := by
  simp [cwSum, GreedyCW.sumA, a172161_eq_greedyA]

example : cwSum 0 = 0 := by simp [cwSum]
example : cwSum 5 = 6 := by rw [cwSum_eq_sumA, GreedyCW.sumA_five]
example : 4 < (5 : ℕ) := by decide
example : (Finset.range 5).Nonempty := ⟨0, by decide⟩

/-- Every recurrence term after the base prefix is at most its preceding sum. -/
theorem a172161_le_cwSum (n : ℕ) (hn : 4 < n) : a172161 n ≤ cwSum n := by
  have hmono : cwSum 5 ≤ cwSum n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro i hi hnmem
    exact Nat.zero_le _
  have hfive : cwSum 5 = 6 := by rw [cwSum_eq_sumA, GreedyCW.sumA_five]
  rw [cwGreedy_eq_recurrence n hn]
  change cwSum n / 2 + 1 ≤ cwSum n
  omega

/-- After the base prefix, partial sums obey the floor recurrence. -/
theorem cwSum_succ (n : ℕ) (hn : 4 < n) : cwSum (n + 1) = 3 * cwSum n / 2 + 1 := by
  rw [cwSum_eq_sumA, cwSum_eq_sumA, GreedyCW.sumA_succ_of_ge n (by omega)]
  omega

end Candidates.A172161
