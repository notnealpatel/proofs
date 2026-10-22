/-
# A327138: refutation of Kimberling's decimal bounds

OEIS A327138 (entry by Clark Kimberling, 2019-08-23) consists of integers
`k` satisfying `cos(2k) < cos(2k+2)`. The entry conjectures
`2.07 < nπ-a(n) < 3.08` for `n ≥ 1`.

Here `a(1) = 2` and `π-2 < 2.07` refute the lower bound. The first five
terms are proved from the predicate; no density or sister-sequence
formula is asserted as an additional formal result.

`IsTerm` is defined on `ℕ`; `0` is not a term. The source offset is 1,
so `a n = Nat.nth IsTerm (n-1)` and `a 0` is irrelevant to the conjecture.
The sum-to-product identity gives `IsTerm k ↔ sin(2k+1) < 0`; bounds on `π`
locate the small terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A327138Refutation

open Real

/-- The defining condition of A327138: `k` is a term iff `cos(2k) < cos(2k+2)`. -/
def IsTerm (k : ℕ) : Prop := Real.cos (2 * k) < Real.cos (2 * k + 2)

/-- The `n`-th term `a(n)` of A327138 (offset `1`): the `(n-1)`-st natural number
`k` (counting from `0`) with `cos(2k) < cos(2k+2)`.  The value at `n = 0` is junk. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-! ### The sign criterion -/

/-- Sum-to-product: `cos(2k) < cos(2k+2)` iff `sin(2k+1) < 0`. -/
theorem isTerm_iff_sin_neg (k : ℕ) : IsTerm k ↔ Real.sin (2 * k + 1) < 0 := by
  have h := Real.cos_sub_cos (2 * (k : ℝ)) (2 * k + 2)
  rw [show (2 * (k : ℝ) + (2 * k + 2)) / 2 = 2 * k + 1 by ring,
    show (2 * (k : ℝ) - (2 * k + 2)) / 2 = -1 by ring, Real.sin_neg] at h
  have hs1 : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])
  unfold IsTerm
  constructor
  · intro hk
    by_contra hc
    nlinarith [not_lt.mp hc]
  · intro hk
    nlinarith

/-- If `(2m+1)π < 2k+1 < (2m+2)π` then `k` is a term. -/
theorem isTerm_of_band (k m : ℕ) (h1 : (2 * m + 1) * π < 2 * k + 1)
    (h2 : (2 * k + 1 : ℝ) < (2 * m + 2) * π) : IsTerm k := by
  rw [isTerm_iff_sin_neg, ← Real.sin_sub_nat_mul_two_pi _ (m + 1)]
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> push_cast <;> linarith

/-- If `2mπ < 2k+1 < (2m+1)π` then `k` is not a term. -/
theorem not_isTerm_of_band (k m : ℕ) (h1 : 2 * m * π < 2 * k + 1)
    (h2 : (2 * k + 1 : ℝ) < (2 * m + 1) * π) : ¬ IsTerm k := by
  rw [isTerm_iff_sin_neg, not_lt, ← Real.sin_sub_nat_mul_two_pi _ m]
  exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le

/-! ### Examples against the OEIS DATA line -/

/-- Among `k < 13`, the terms are exactly `2, 5, 8, 11, 12`. -/
theorem isTerm_iff_of_lt_thirteen (k : ℕ) (hk : k < 13) :
    IsTerm k ↔ k ∈ ({2, 5, 8, 11, 12} : Finset ℕ) := by
  have lo := Real.pi_gt_d2
  have hi := Real.pi_lt_d2
  interval_cases k
  · simpa using not_isTerm_of_band 0 0 (by norm_num) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 1 0 (by norm_num) (by norm_num; linarith)
  · simpa using isTerm_of_band 2 0 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 3 1 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 4 1 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using isTerm_of_band 5 1 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 6 2 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 7 2 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using isTerm_of_band 8 2 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 9 3 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using not_isTerm_of_band 10 3 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using isTerm_of_band 11 3 (by norm_num; linarith) (by norm_num; linarith)
  · simpa using isTerm_of_band 12 3 (by norm_num; linarith) (by norm_num; linarith)

/-- The first five terms: `a(1), …, a(5) = 2, 5, 8, 11, 12`. -/
theorem a_one_to_five : a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 8 ∧ a 4 = 11 ∧ a 5 = 12 := by
  classical
  have t : ∀ k < 13, IsTerm k ↔ k ∈ ({2, 5, 8, 11, 12} : Finset ℕ) :=
    isTerm_iff_of_lt_thirteen
  have h0 : ¬ IsTerm 0 := by simpa using t 0 (by norm_num)
  have h1 : ¬ IsTerm 1 := by simpa using t 1 (by norm_num)
  have h2 : IsTerm 2 := by simpa using t 2 (by norm_num)
  have h3 : ¬ IsTerm 3 := by simpa using t 3 (by norm_num)
  have h4 : ¬ IsTerm 4 := by simpa using t 4 (by norm_num)
  have h5 : IsTerm 5 := by simpa using t 5 (by norm_num)
  have h6 : ¬ IsTerm 6 := by simpa using t 6 (by norm_num)
  have h7 : ¬ IsTerm 7 := by simpa using t 7 (by norm_num)
  have h8 : IsTerm 8 := by simpa using t 8 (by norm_num)
  have h9 : ¬ IsTerm 9 := by simpa using t 9 (by norm_num)
  have h10 : ¬ IsTerm 10 := by simpa using t 10 (by norm_num)
  have h11 : IsTerm 11 := by simpa using t 11 (by norm_num)
  have h12 : IsTerm 12 := by simpa using t 12 (by norm_num)
  have c2 : Nat.count IsTerm 2 = 0 := by simp [Nat.count_succ, h0, h1]
  have c5 : Nat.count IsTerm 5 = 1 := by simp [Nat.count_succ, h0, h1, h2, h3, h4]
  have c8 : Nat.count IsTerm 8 = 2 := by
    simp [Nat.count_succ, h0, h1, h2, h3, h4, h5, h6, h7]
  have c11 : Nat.count IsTerm 11 = 3 := by
    simp [Nat.count_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  have c12 : Nat.count IsTerm 12 = 4 := by
    simp [Nat.count_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [a, c2] using Nat.nth_count h2
  · simpa [a, c5] using Nat.nth_count h5
  · simpa [a, c8] using Nat.nth_count h8
  · simpa [a, c11] using Nat.nth_count h11
  · simpa [a, c12] using Nat.nth_count h12

/-! ### The conjecture -/

/-- The conjecture in Kimberling's OEIS A327138 entry (2019-08-23):
for every `n ≥ 1`, `2.07 < n·π-a(n) < 3.08`, with subtraction in `ℝ`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → (2.07 : ℝ) < n * π - a n ∧ (n : ℝ) * π - a n < 3.08

/-! ### The refutation -/

/-- Kimberling's conjecture for A327138 is false at `n = 1`, where
`a(1) = 2` and `π - 2 < 1.15 < 2.07`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨hlo, -⟩ := h 1 le_rfl
  have ha1 : a 1 = 2 := a_one_to_five.1
  rw [ha1] at hlo
  push_cast at hlo
  linarith [Real.pi_lt_d2]

end Candidates.A327138Refutation
