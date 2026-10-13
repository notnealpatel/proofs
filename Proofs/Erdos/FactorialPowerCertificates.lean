import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false

namespace ErdosCandidates.E405

/-- `(p−1)! + a^(p−1) = p^k` with `p` an odd prime and positive `a, k`.
The prime guard ensures `1 ≤ p`, so `p - 1` is the intended predecessor;
the positivity guards exclude zero base and exponent from the solution domain. -/
def IsSolution (p a k : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ 1 ≤ a ∧ 1 ≤ k ∧
    (p - 1).factorial + a ^ (p - 1) = p ^ k

example : IsSolution 3 1 1 := by unfold IsSolution; decide
example : ¬ IsSolution 2 1 1 := by unfold IsSolution; decide
example : ¬ IsSolution 3 0 1 := by unfold IsSolution; decide
example : ¬ IsSolution 3 1 0 := by unfold IsSolution; decide

/-- The triples `(3,1,1)`, `(3,5,3)`, and `(5,1,2)` satisfy the guarded
factorial-power equation. This certificate makes no completeness claim. -/
theorem cert_solutions :
    IsSolution 3 1 1 ∧ IsSolution 3 5 3 ∧ IsSolution 5 1 2 := by
  unfold IsSolution
  decide

/-- At `p = 2`, the equation holds for `a = 2^k - 1` and every positive `k`.
This is an identity family, not an `IsSolution` claim or an infinitude theorem. -/
theorem p2_family : ∀ k : ℕ, 1 ≤ k →
    (2 - 1).factorial + (2 ^ k - 1) ^ (2 - 1) = 2 ^ k := by
  intro k _hk
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  simpa only [Nat.reduceSub, Nat.factorial_one, pow_one] using Nat.add_sub_of_le hpow

example : 1 ≤ (1 : ℕ) ∧
    (2 - 1).factorial + (2 ^ 1 - 1) ^ (2 - 1) = 2 ^ 1 := by decide

/-- The side calculation `720 + 64 = 28²` is a square, but `(7,2,2)`
does not satisfy the guarded factorial-power equation. -/
theorem side_square_and_not_solution :
    720 + 64 = 28 ^ 2 ∧ ¬ IsSolution 7 2 2 := by
  unfold IsSolution
  decide

end ErdosCandidates.E405
