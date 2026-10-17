import NumberComplexity.AdditionChainStability
import NumberComplexity.AdditionChainDefectWellOrder

set_option autoImplicit false

namespace NumberComplexity

/-- The real base-two logarithm is a lower bound for the shortest chain length
of every positive integer. -/
theorem logb_two_le_l (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n : ℝ) ≤ (l n : ℝ) := by
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ l n := by
    exact_mod_cast le_two_pow_l n hn
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hn) (by positivity : (0 : ℝ) < 2 ^ l n)).2 hpow
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] using hlog

/-- An actual addition-chain defect is nonnegative on positive integers. -/
theorem additionChainDefect_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ additionChainDefect n := by
  exact sub_nonneg.mpr (logb_two_le_l n hn)

/-- A positive integer of actual addition-chain defect less than one is stable
under every number of doublings, including zero doublings. -/
theorem l_two_pow_mul_eq_of_defect_lt_one (n : ℕ) (hn : 0 < n)
    (hdef : additionChainDefect n < 1) :
    ∀ k : ℕ, l (2 ^ k * n) = l n + k := by
  have hupper (k : ℕ) : l (2 ^ k * n) ≤ l n + k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hnorm : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
      rw [hnorm]
      exact (l_two_mul_le (2 ^ k * n)).trans (by omega)
  intro k
  have hpos : 0 < 2 ^ k * n := Nat.mul_pos (Nat.two_pow_pos k) hn
  have hlog : Real.logb 2 ((2 ^ k * n : ℕ) : ℝ) =
      (k : ℝ) + Real.logb 2 (n : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Real.logb_mul (by positivity) (by exact_mod_cast (Nat.ne_of_gt hn)),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hlower := logb_two_le_l (2 ^ k * n) hpos
  rw [hlog] at hlower
  have hstrict : (l n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
    unfold additionChainDefect at hdef
    linarith
  apply Nat.le_antisymm (hupper k)
  by_contra hnot
  have hdrop : l (2 ^ k * n) + 1 ≤ l n + k := by omega
  have hdrop_real : (l (2 ^ k * n) : ℝ) + 1 ≤ (l n : ℝ) + (k : ℝ) := by
    exact_mod_cast hdrop
  linarith

example : 0 < (1 : ℕ) ∧ additionChainDefect 1 < 1 ∧
    ∀ k : ℕ, l (2 ^ k * 1) = l 1 + k := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [additionChainDefect, l_one]
  · intro k
    simp [l_two_pow]

example (n : ℕ) : l (2 ^ 0 * n) = l n + 0 := by simp

end NumberComplexity
