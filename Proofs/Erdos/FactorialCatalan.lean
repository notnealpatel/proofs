import Mathlib.Combinatorics.Enumerative.Catalan.Basic

set_option autoImplicit false

namespace Erdos727

/-- The square of `(n + 1)!` divides `(2 * n)!` exactly when `n + 1` divides the
`n`th Catalan number. -/
theorem sq_dvd_iff_dvd_catalan (n : ℕ) :
    (n + 1).factorial ^ 2 ∣ (2 * n).factorial ↔ (n + 1) ∣ catalan n := by
  have hchoose : n ≤ 2 * n := by omega
  have hsub : 2 * n - n = n := by omega
  have hcentral : n.centralBinom * n.factorial * n.factorial =
      (2 * n).factorial := by
    simpa only [Nat.centralBinom, hsub] using
      (Nat.choose_mul_factorial_mul_factorial hchoose)
  have htotal : (2 * n).factorial =
      catalan n * ((n + 1) * n.factorial * n.factorial) := by
    rw [← hcentral, ← succ_mul_catalan_eq_centralBinom]
    ac_rfl
  have hsquare : (n + 1).factorial ^ 2 =
      (n + 1) * ((n + 1) * n.factorial * n.factorial) := by
    rw [Nat.factorial_succ, pow_two]
    ac_rfl
  have hfactor : 0 < (n + 1) * n.factorial * n.factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos n) (Nat.factorial_pos n))
      (Nat.factorial_pos n)
  rw [hsquare, htotal]
  exact Nat.mul_dvd_mul_iff_right hfactor

/-- The square of `6!` divides `10!`, with quotient `7`. -/
theorem factorial_six_sq_dvd_factorial_ten :
    (Nat.factorial 6) ^ 2 ∣ Nat.factorial 10 := by
  refine ⟨7, ?_⟩
  decide

example : (0 + 1).factorial ^ 2 ∣ (2 * 0).factorial ∧
    (0 + 1) ∣ catalan 0 := by simp

example : 0 < (0 + 1) * Nat.factorial 0 * Nat.factorial 0 := by decide

end Erdos727
