import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace Erdos175.A046098.Residual

/-- The sum of the first `fuel` base-`p` digits, computed by structural recursion.
The correctness theorem below assumes `1 < p` and enough fuel. -/
def digitSum (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => n % p + digitSum p fuel (n / p)

example : digitSum 7 18 40 = 10 := by decide
example : digitSum 7 0 40 = 0 := rfl
example : 1 < 7 ∧ (40 : ℕ) < 7 ^ 18 := by decide

/-- Zero has truncated digit sum zero at every fuel. -/
@[simp] theorem digitSum_zero (p fuel : ℕ) : digitSum p fuel 0 = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [digitSum, ih]

/-- With enough fuel and a genuine positional base, the structurally recursive
sum agrees with the sum of Mathlib's digits. -/
theorem digitSum_eq_sum_digits {p fuel n : ℕ} (hp : 1 < p) (hn : n < p ^ fuel) :
    digitSum p fuel n = (Nat.digits p n).sum := by
  induction fuel generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp [digitSum]
  | succ fuel ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hdiv : n / p < p ^ fuel := by
        apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
        simpa only [pow_succ] using hn
      rw [digitSum, Nat.digits_def' hp hn0, List.sum_cons, ih hdiv]

example : (⟨3, by decide⟩ : Fin 31).val = 3 ∧ 3 ≤ (3 : ℕ) := by decide
example : (2 : ℕ) ^ 31 < 3 ^ 21 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked carry certificates for exponents `3` through `30`. The
witness is `5` at exponent `6`, `7` at exponent `8`, and `3` otherwise.
Twenty-one digits suffice for all the inputs, which are at most `2^31`.
This finite computation is isolated from the downstream Kummer bridge. -/
theorem witness_digitSum_certificate : ∀ k : Fin 31, 3 ≤ k.val →
    let p := if k.val = 6 then 5 else if k.val = 8 then 7 else 3
    p.Prime ∧
      digitSum p 21 (2 ^ (k.val + 1)) + 2 * (p - 1) ≤
        2 * digitSum p 21 (2 ^ k.val) := by
  decide

end Erdos175.A046098.Residual
