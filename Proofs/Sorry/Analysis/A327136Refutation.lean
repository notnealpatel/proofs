/-
# A327136 — Kimberling's window conjecture for the `sin(2k)` local minima (refuted)

## OEIS source (`oeis show A327136`, live entry checked 2026-10-21)

```
A327136   Numbers k such that sin(2k) > sin(2k+2) < sin(2k+4).
OFFSET:   1,2
TERMS:    1,4,8,11,14,17,20,23,26,30,33,36,39,42,45,48,52,55,58,61,64,67,
          70,74,77,80,83,86,89,92,96,99,102,105,108,111,114,118,121,124,...
COMMENT:  The sequences A026317, A327136, A327137 partition the nonnegative
          integers.
COMMENT:  Conjecture:  1.285 < n*Pi - a(n) < 1.286 for n >= 1.
AUTHOR:   _Clark Kimberling_, Aug 23 2019
MATHEMATICA: Select[t, f[#] > f[# + 1] < f[# + 2] &] with f[x_] := Sin[2 x]
```

No later comment or `%E` line retracts or corrects the conjecture.

## Status

This module **refutes** the conjecture as stated.  It already fails at
`n = 1`: `a(1) = 1` and `1 * Pi - 1 = 2.14159... > 1.286`.  (Over
`n = 1..637` checked at 200-bit precision, `n*Pi - a(n)` never lies in the
window `(1.285, 1.286)` at all; it ranges over `(1.2918..., 2.2831...)`.)

The window the author presumably intended is `1.285 < n*Pi - a(n) < 2.286`,
i.e. a window of width one.  The exact form, proved below as
`a327136_window`, is `Pi/4 + 1/2 < n*Pi - a(n) < Pi/4 + 3/2`
(`= 1.2853... , 2.2853...`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A327136Refutation

open Real

/-! ## Definitions -/

/-- Membership in A327136: `k` is a natural number with
`sin(2k) > sin(2k+2) < sin(2k+4)` (OEIS NAME line). -/
def IsMember (k : ℕ) : Prop :=
  Real.sin (2 * k + 2) < Real.sin (2 * k) ∧ Real.sin (2 * k + 2) < Real.sin (2 * k + 4)

/-- `a n` is the `n`-th term of A327136 (offset `1`): the `(n-1)`-st member
in increasing order, zero-indexed by `Nat.nth`.  The value at `n = 0` is
outside the OEIS index range and is never used by the conjecture below. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsMember (n - 1)

/-! ## Elementary sine facts used by the ground-truth checks -/

lemma sin_two_pos : 0 < Real.sin 2 :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_d4])

lemma sin_four_lt_sin_six : Real.sin 4 < Real.sin 6 := by
  have h4 : Real.sin 4 = Real.sin (π - 4) := (Real.sin_pi_sub 4).symm
  have h6 : Real.sin 6 = Real.sin (6 - 2 * π) := (Real.sin_sub_two_pi 6).symm
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  rw [h4, h6]
  apply Real.strictMonoOn_sin
  · constructor <;> linarith
  · constructor <;> linarith
  · linarith

lemma sin_six_neg : Real.sin 6 < 0 := by
  have h6 : Real.sin 6 = Real.sin (6 - 2 * π) := (Real.sin_sub_two_pi 6).symm
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  rw [h6]
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)

lemma sin_four_neg : Real.sin 4 < 0 := sin_four_lt_sin_six.trans sin_six_neg

lemma sin_eight_pos : 0 < Real.sin 8 := by
  have h8 : Real.sin 8 = Real.sin (8 - 2 * π) := (Real.sin_sub_two_pi 8).symm
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  rw [h8]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

lemma sin_ten_lt_sin_twelve : Real.sin 10 < Real.sin 12 := by
  have h10 : Real.sin 10 = Real.sin (3 * π - 10) := by
    rw [← Real.sin_pi_sub, ← Real.sin_sub_two_pi (3 * π - 10)]
    congr 1
    ring
  have h12 : Real.sin 12 = Real.sin (12 - 4 * π) := by
    rw [← Real.sin_sub_two_pi 12, ← Real.sin_sub_two_pi (12 - 2 * π)]
    congr 1
    ring
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  rw [h10, h12]
  apply Real.strictMonoOn_sin
  · constructor <;> linarith
  · constructor <;> linarith
  · linarith

lemma sin_ten_neg : Real.sin 10 < 0 := by
  have h10 : Real.sin 10 = Real.sin (10 - 4 * π) := by
    rw [← Real.sin_sub_two_pi 10, ← Real.sin_sub_two_pi (10 - 2 * π)]
    congr 1
    ring
  have hlo := Real.pi_gt_d4
  have hhi := Real.pi_lt_d4
  rw [h10]
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)

/-! ## Ground truth against the DATA line `1, 4, 8, ...` -/

lemma not_isMember_zero : ¬ IsMember 0 := by
  rintro ⟨h, -⟩
  norm_num at h
  linarith [sin_two_pos]

lemma isMember_one : IsMember 1 := by
  refine ⟨?_, ?_⟩ <;> norm_num
  · linarith [sin_two_pos, sin_four_neg]
  · exact sin_four_lt_sin_six

lemma not_isMember_two : ¬ IsMember 2 := by
  rintro ⟨h, -⟩
  norm_num at h
  linarith [sin_four_lt_sin_six]

lemma not_isMember_three : ¬ IsMember 3 := by
  rintro ⟨h, -⟩
  norm_num at h
  linarith [sin_six_neg, sin_eight_pos]

lemma isMember_four : IsMember 4 := by
  refine ⟨?_, ?_⟩ <;> norm_num
  · linarith [sin_ten_neg, sin_eight_pos]
  · exact sin_ten_lt_sin_twelve

/-- `a(1) = 1`, the first DATA term. -/
theorem a_one : a 1 = 1 := by
  classical
  have hcount : Nat.count IsMember 1 = 0 := by
    simp [Nat.count_succ, not_isMember_zero]
  have h := Nat.nth_count isMember_one
  rw [hcount] at h
  simpa [a] using h

/-- `a(2) = 4`, the second DATA term. -/
theorem a_two : a 2 = 4 := by
  classical
  have hcount : Nat.count IsMember 4 = 1 := by
    simp [Nat.count_succ, not_isMember_zero, isMember_one, not_isMember_two,
      not_isMember_three]
  have h := Nat.nth_count isMember_four
  rw [hcount] at h
  simpa [a] using h

/-! ## The conjecture and its refutation -/

/-- **Kimberling's conjecture (A327136, Aug 23 2019).**
Verbatim: "Conjecture:  1.285 < n*Pi - a(n) < 1.286 for n >= 1." -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → (1.285 : ℝ) < n * π - a n ∧ (n : ℝ) * π - a n < 1.286

/-- **The conjecture is false.**  Counterexample `n = 1`: `a(1) = 1` and
`1 * Pi - 1 = 2.14159... ≥ 1.286`.  The author presumably intended the
width-one window `1.285 < n*Pi - a(n) < 2.286`; see `a327136_window`. -/
theorem a327136_conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨-, hupper⟩ := h 1 le_rfl
  rw [a_one] at hupper
  norm_num at hupper
  linarith [Real.pi_gt_d4]

end Candidates.A327136Refutation
