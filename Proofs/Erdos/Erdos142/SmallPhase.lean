/-
  Erdős Problem #142 — selecting a small step for one additive phase.

  Dirichlet approximation supplies a positive denominator `d ≤ Q`.  Integer
  periodicity of the complex exponential then makes the phase at `d` lie
  within `2 * π / Q` of one.  The additional hypothesis `Q * K ≤ N`
  ensures that this same step satisfies the size condition `d * K ≤ N`
  required by `PhasePartition`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos142

/-- Dirichlet approximation with a positive natural denominator at most `Q`
and an integer numerator, in the weaker `1 / Q` form convenient for phases. -/
theorem exists_nat_abs_mul_sub_int_le (θ : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ d : ℕ, 0 < d ∧ d ≤ Q ∧
      ∃ a : ℤ, |(d : ℝ) * θ - (a : ℝ)| ≤ 1 / (Q : ℝ) := by
  obtain ⟨d, hd, hdQ, happ⟩ := Real.exists_nat_abs_mul_sub_round_le θ hQ
  refine ⟨d, hd, hdQ, round ((d : ℝ) * θ), happ.trans ?_⟩
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Q)
  norm_num

/-- If `Q * K ≤ N`, a single real additive phase has a positive step `d ≤ Q`
which also satisfies `d * K ≤ N` and whose value is within `2 * π / Q` of one. -/
theorem exists_small_phase_step (θ : ℝ) {Q K N : ℕ} (hQ : 0 < Q)
    (hQK : Q * K ≤ N) :
    ∃ d : ℕ, 0 < d ∧ d ≤ Q ∧ d * K ≤ N ∧
      ‖Complex.exp (2 * Real.pi * Complex.I * θ * d) - 1‖ ≤
        2 * Real.pi / (Q : ℝ) := by
  obtain ⟨d, hd, hdQ, a, ha⟩ := exists_nat_abs_mul_sub_int_le θ hQ
  refine ⟨d, hd, hdQ, (Nat.mul_le_mul_right K hdQ).trans hQK, ?_⟩
  have hphase :
      Complex.exp (2 * Real.pi * Complex.I * θ * d) =
        Complex.exp (Complex.I * (2 * Real.pi * ((d : ℝ) * θ - (a : ℝ)))) := by
    calc
      Complex.exp (2 * Real.pi * Complex.I * θ * d) =
          Complex.exp
            (Complex.I * (2 * Real.pi * ((d : ℝ) * θ - (a : ℝ))) +
              (a : ℂ) * (2 * Real.pi * Complex.I)) := by
                congr 1
                push_cast
                ring
      _ = Complex.exp (Complex.I * (2 * Real.pi * ((d : ℝ) * θ - (a : ℝ)))) *
          Complex.exp ((a : ℂ) * (2 * Real.pi * Complex.I)) := Complex.exp_add _ _
      _ = Complex.exp (Complex.I * (2 * Real.pi * ((d : ℝ) * θ - (a : ℝ)))) := by
        rw [Complex.exp_int_mul_two_pi_mul_I]
        simp only [mul_one]
  rw [hphase]
  calc
    ‖Complex.exp (Complex.I * (2 * Real.pi * ((d : ℝ) * θ - (a : ℝ)))) - 1‖ ≤
        ‖2 * Real.pi * ((d : ℝ) * θ - (a : ℝ))‖ := by
      have harg :
          Complex.I * (2 * Real.pi * ((d : ℝ) * θ - (a : ℝ))) =
            Complex.I * ((2 * Real.pi * ((d : ℝ) * θ - (a : ℝ)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |(d : ℝ) * θ - (a : ℝ)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
    _ ≤ 2 * Real.pi * (1 / (Q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num) Real.pi_pos.le)
    _ = 2 * Real.pi / (Q : ℝ) := by ring

/-- The selection hypotheses are jointly satisfiable for the boundary example
`θ = 1 / 2`, `Q = 4`, `K = 2`, and `N = Q * K`. -/
example :
    ∃ d : ℕ, 0 < d ∧ d ≤ 4 ∧ d * 2 ≤ 8 ∧
      ‖Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ) * d) - 1‖ ≤
        2 * Real.pi / (4 : ℝ) := by
  exact exists_small_phase_step (1 / 2 : ℝ) (by norm_num) (by norm_num)

#check @Real.exists_nat_abs_mul_sub_round_le
#check @exists_nat_abs_mul_sub_int_le
#check @exists_small_phase_step

#print axioms exists_nat_abs_mul_sub_int_le
#print axioms exists_small_phase_step

end Erdos142
