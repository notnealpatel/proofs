/-
# A131418: a digit-sum divisibility condition

OEIS A131418, Harvey P. Dale (Mar 28 2019).
Every natural `n` satisfying `s(n) = s(n+s(n))`, where `s` is decimal digit
sum, is divisible by `9`. This follows from `s(n) ≡ n (mod 9)`.
Only this necessary condition is asserted, not its converse.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A131418BaseDigitSum

/-- The base-10 digit sum `s(n)` (`Sum_digits(n)` in the entry). -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- Membership in A131418: `s(n) = s(n + s(n))`, with `n ≥ 0` (all of `ℕ`). -/
def IsA131418 (n : ℕ) : Prop := digitSum n = digitSum (n + digitSum n)

instance : DecidablePred IsA131418 := fun n => by
  unfold IsA131418
  infer_instance

/-! ## Examples against the DATA line -/

example : digitSum 639 = 18 := by decide

/-- The listed terms below `100` are exactly `0, 9, …, 81`. -/
example : (List.range 100).filter (fun n => decide (IsA131418 n)) =
    [0, 9, 18, 27, 36, 45, 54, 63, 72, 81] := by decide

example : IsA131418 108 ∧ IsA131418 279 ∧ IsA131418 639 ∧ ¬ IsA131418 99 := by
  decide

/-! ## The conjecture -/

/-- Casting out nines: `s(n) ≡ n (mod 9)`. -/
theorem digitSum_modEq (n : ℕ) : digitSum n ≡ n [MOD 9] :=
  (Nat.modEq_nine_digits_sum n).symm

/-- **Dale's conjecture (A131418, Harvey P. Dale, Mar 28 2019), proved.**

Verbatim: "Conjecture: all terms are divisible by 9."  That is: every `n ≥ 0`
with `s(n) = s(n + s(n))`, where `s` is the base-10 digit sum, satisfies
`9 ∣ n`. -/
theorem nine_dvd_of_isA131418 (n : ℕ) (h : IsA131418 n) : 9 ∣ n := by
  -- `s(n + s(n)) ≡ n + s(n) ≡ n + n (mod 9)` and `s(n) ≡ n (mod 9)`.
  have hleft : digitSum n ≡ n [MOD 9] := digitSum_modEq n
  have hright : digitSum (n + digitSum n) ≡ n + n [MOD 9] :=
    (digitSum_modEq (n + digitSum n)).trans (Nat.ModEq.add_left n hleft)
  have hcong : n + 0 ≡ n + n [MOD 9] := by
    rw [Nat.add_zero]
    exact hleft.symm.trans (h ▸ hright)
  have hzero : 0 ≡ n [MOD 9] := Nat.ModEq.add_left_cancel' n hcong
  exact (Nat.modEq_zero_iff_dvd.mp hzero.symm)

/-- Non-vacuity: the hypothesis is satisfied by a nonzero term (`108`). -/
example : IsA131418 108 ∧ 9 ∣ 108 := ⟨by decide, nine_dvd_of_isA131418 108 (by decide)⟩

end Candidates.A131418BaseDigitSum
