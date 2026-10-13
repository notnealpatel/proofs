import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E673

/-- The increasing list of divisors of `n`. -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- `G n`: the sum of ratios of consecutive divisors,
    `∑_{i < τ(n)−1} d_i / d_{i+1} : ℚ`, via `zipWith` on the sorted
    divisor list and its tail. -/
def G (n : ℕ) : ℚ :=
  (List.zipWith (fun a b => (a : ℚ) / b) (divisorList n)
    (divisorList n).tail).sum

private theorem divisors_twelve : (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by
  decide

private theorem divisors_seven : (7 : ℕ).divisors = {1, 7} := by
  decide

private theorem divisorList_twelve : divisorList 12 = [1, 2, 3, 4, 6, 12] := by
  rw [divisorList, divisors_twelve]
  change ([1, 2, 3, 4, 6, 12] : List ℕ).toFinset.sort (· ≤ ·) = _
  exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

private theorem divisorList_seven : divisorList 7 = [1, 7] := by
  rw [divisorList, divisors_seven]
  change ([1, 7] : List ℕ).toFinset.sort (· ≤ ·) = _
  exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)

/-- Ground truth: the consecutive divisor ratios of 12 sum to 37/12. -/
example : G 12 = 37 / 12 := by
  rw [G, divisorList_twelve]
  norm_num [List.zipWith_cons_cons, List.sum_cons]

/-- Ground truth: the prime 7 has one ratio, and 1 has none. -/
example : G 7 = 1 / 7 ∧ G 1 = 0 := by
  constructor
  · rw [G, divisorList_seven]
    norm_num
  · simp [G, divisorList]

/-- The live entry's literal `m = 1` lower bound fails at `n = 7`. -/
example : ¬(((7 / 1).divisors.card : ℚ) / 1 ≤ G 7) := by
  norm_num [G, divisorList_seven, divisors_seven]

private theorem adjacent_nonneg (l : List ℕ) :
    0 ≤ (List.zipWith (fun a b => (a : ℚ) / b) l l.tail).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.tail_cons] at ih
      exact add_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)) ih

private theorem adjacent_le_length (l : List ℕ) (h : l.Pairwise (· ≤ ·)) :
    (List.zipWith (fun a b => (a : ℚ) / b) l l.tail).sum ≤
      ((l.length - 1 : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have hab : a ≤ b := h.rel_head (by simp)
      have htail : (b :: l).Pairwise (· ≤ ·) := h.of_cons
      have hratio : (a : ℚ) / b ≤ 1 := by
        by_cases hb : b = 0
        · simp [hb]
        · have hbpos : (0 : ℚ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
          exact (div_le_one hbpos).2 (by exact_mod_cast hab)
      have hsum := add_le_add hratio (ih htail)
      simpa [List.length_cons, Nat.add_sub_cancel, Nat.cast_add, add_comm] using hsum

/-- Every consecutive divisor ratio is nonnegative, including the empty sum at zero. -/
theorem G_nonneg (n : ℕ) : 0 ≤ G n := adjacent_nonneg (divisorList n)

/-- There are at most `τ(n) - 1` consecutive ratios, each at most one. -/
theorem G_le_tau_sub_one (n : ℕ) : G n ≤ ((n.divisors.card - 1 : ℕ) : ℚ) := by
  have h := adjacent_le_length (divisorList n) (Finset.pairwise_sort _ _)
  simpa [G, divisorList] using h

/-- The sum of consecutive divisor ratios is at most the number of divisors. -/
theorem G_le_tau (n : ℕ) (hn : 1 ≤ n) : G n ≤ n.divisors.card := by
  exact (G_le_tau_sub_one n).trans (by exact_mod_cast Nat.sub_le n.divisors.card 1)

example : 1 ≤ (12 : ℕ) := by decide
example : G 0 = 0 := by simp [G, divisorList]

end ErdosCandidates.E673
