/-
# A073023 — Cloitre: `Sum_{k=1..n} a(k) > n^(3/2)` for `n > 100` is false

Benoit Cloitre's conjecture in OEIS A073023 (2002), where `a(n)` counts
`1 ≤ x ≤ n` satisfying `n^x ≡ 1 (mod x)`.

For `S(n) = Σ_{k=1}^n a(k)`, `S(102) = 1025` and
`1025^2 = 1050625 < 1061208 = 102^3`, refuting `n^(3/2) < S(n)` for `100 < n`.
No assertion about a corrected eventual threshold is proved here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A073023Refutation

/-- A073023: `a n` is the number of `x` with `1 ≤ x ≤ n` and `n ^ x ≡ 1 (mod x)`.
For `x = 1` the congruence holds trivially, matching the PARI program
`(n^i-1)%i == 0`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun x => n ^ x ≡ 1 [MOD x])).card

/-- Examples: `a 1, …, a 88` agree with all 88 terms of the OEIS DATA line. -/
example : (List.range 88).map (fun i => a (i + 1)) =
    [1, 1, 2, 2, 3, 2, 5, 2, 4, 3, 7, 2, 8, 2, 6, 5, 7, 2, 11, 2, 8, 5, 11, 2,
     12, 3, 9, 4, 14, 2, 18, 2, 7, 6, 12, 5, 16, 2, 10, 6, 19, 2, 22, 2, 9, 9,
     16, 2, 19, 3, 13, 6, 18, 2, 20, 5, 14, 7, 21, 2, 28, 2, 10, 9, 17, 5, 29,
     2, 17, 6, 31, 2, 23, 2, 10, 9, 23, 5, 32, 2, 16, 5, 26, 2, 28, 6, 14, 9] := by
  decide +kernel

/-- Cloitre's conjecture (OEIS A073023, 2002): for `n > 100`,
`n^(3/2) < Σ_{k=1}^n a(k)`. The power is `Real.rpow` at a positive base. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 100 < n → (n : ℝ) ^ ((3 : ℝ) / 2) < ∑ k ∈ Finset.Icc 1 n, (a k : ℝ)

/-- The partial sum at the witness: `Sum_{k=1..102} a(k) = 1025`
(kernel computation of 5253 modular congruences). -/
theorem sum_a_Icc_102 : ∑ k ∈ Finset.Icc 1 102, a k = 1025 := by
  decide +kernel

/-- Squaring the real power: `(102 ^ (3/2)) ^ 2 = 102 ^ 3`. -/
theorem rpow_three_halves_102_sq :
    ((102 : ℝ) ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = 102 ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- At `n = 102` the partial sum lies strictly below `n^(3/2)`:
`1025 < 102^(3/2)` because `1025^2 = 1050625 < 1061208 = 102^3`. -/
theorem sum_a_Icc_102_lt_rpow :
    ∑ k ∈ Finset.Icc 1 102, (a k : ℝ) < (102 : ℝ) ^ ((3 : ℝ) / 2) := by
  have hcast : ∑ k ∈ Finset.Icc 1 102, (a k : ℝ) = 1025 := by
    rw [← Nat.cast_sum, sum_a_Icc_102]
    norm_num
  have hnonneg : (0 : ℝ) ≤ (102 : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hsq : (1025 : ℝ) ^ (2 : ℕ) < ((102 : ℝ) ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) := by
    rw [rpow_three_halves_102_sq]
    norm_num
  rw [hcast]
  exact lt_of_pow_lt_pow_left₀ 2 hnonneg hsq

/-- **Refutation of Cloitre's conjecture.**  The counterexample is `n = 102`:
`Sum_{k=1..102} a(k) = 1025` and `1025^2 < 102^3`, so the sum is below
`102^(3/2)`.  No corrected eventual threshold is proved here. -/
theorem cloitre_conjecture_false : ¬ Conjecture := by
  intro hconj
  have h102 := hconj 102 (by norm_num)
  push_cast at h102
  exact lt_asymm h102 sum_a_Icc_102_lt_rpow

end Candidates.A073023Refutation
