import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

namespace Erdos727

/-- At `n = 208`, the square of `(n + 2)!` divides `(2n)!`. -/
theorem k2_witness_exists : ∃ n : ℕ, (n + 2).factorial ^ 2 ∣ (2*n).factorial := by
  refine ⟨208, ?_⟩
  set_option maxRecDepth 4096 in
    decide

end Erdos727
