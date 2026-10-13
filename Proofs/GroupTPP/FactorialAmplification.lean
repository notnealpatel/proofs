import Mathlib.Analysis.SpecialFunctions.Stirling

set_option autoImplicit false

namespace GroupTPP.STPPWreath

/-- Factorial amplification: if every positive tensor power satisfies the
factorial-weighted scalar capacity bound, then the number of summands times
its scalar volume is at most the capacity. -/
theorem mul_le_of_factorial_amplification (m : ℕ) (hm : 1 ≤ m)
    (x d : ℝ) (hx : 0 ≤ x) (hd : 0 ≤ d)
    (h : ∀ t : ℕ, 1 ≤ t →
      (Nat.factorial (m ^ t) : ℝ) * x ^ (t * m ^ t) ≤ d ^ (t * m ^ t)) :
    (m : ℝ) * x ≤ d := by
  have hgeom : ∀ t : ℕ, 1 ≤ t →
      ((m : ℝ) * x) ^ t ≤ Real.exp 1 * d ^ t := by
    intro t ht
    let k := m ^ t
    have hk : 1 ≤ k := one_le_pow₀ hm
    have hk0 : k ≠ 0 := by omega
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
      have harg : (1 : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by
        nlinarith [Real.two_le_pi, mul_nonneg (sub_nonneg.mpr Real.two_le_pi)
          (sub_nonneg.mpr hkR)]
      simpa using Real.sqrt_le_sqrt harg
    have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
      calc
        ((k : ℝ) / Real.exp 1) ^ k
            ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k :=
          le_mul_of_one_le_left (by positivity) hsqrt
        _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k
    have hp : (((m : ℝ) * x) ^ t / Real.exp 1) ^ k ≤ (d ^ t) ^ k := by
      calc
        (((m : ℝ) * x) ^ t / Real.exp 1) ^ k
            = ((k : ℝ) / Real.exp 1) ^ k * x ^ (t * k) := by
          dsimp [k]
          push_cast
          rw [mul_pow, mul_div_right_comm, mul_pow, pow_mul]
        _ ≤ (Nat.factorial k : ℝ) * x ^ (t * k) :=
          mul_le_mul_of_nonneg_right hfac (pow_nonneg hx _)
        _ ≤ d ^ (t * k) := h t ht
        _ = (d ^ t) ^ k := pow_mul d t k
    have hroot : ((m : ℝ) * x) ^ t / Real.exp 1 ≤ d ^ t :=
      le_of_pow_le_pow_left₀ hk0 (pow_nonneg hd _) hp
    have hscaled := (div_le_iff₀ he).mp hroot
    simpa only [mul_comm] using hscaled
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · have h1 := hgeom 1 le_rfl
    rw [← hd0] at h1 ⊢
    simpa using h1
  · by_contra hcon
    have hstrict : d < (m : ℝ) * x := lt_of_not_ge hcon
    have hr : 1 < ((m : ℝ) * x) / d := (one_lt_div hdpos).mpr hstrict
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (Real.exp 1) hr
    have hj' : Real.exp 1 < (((m : ℝ) * x) / d) ^ (j + 1) :=
      lt_of_lt_of_le hj (pow_le_pow_right₀ hr.le (Nat.le_succ j))
    have hle := hgeom (j + 1) (Nat.le_add_left 1 j)
    have hdp : 0 < d ^ (j + 1) := pow_pos hdpos _
    have hK : (((m : ℝ) * x) / d) ^ (j + 1) ≤ Real.exp 1 := by
      rw [div_pow, div_le_iff₀ hdp]
      exact hle
    exact (not_le_of_gt hj') hK

-- A jointly satisfiable boundary model: one summand of unit volume and capacity.
example : (1 : ℕ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧
    (∀ t : ℕ, 1 ≤ t →
      (Nat.factorial (1 ^ t) : ℝ) * (1 : ℝ) ^ (t * 1 ^ t) ≤
        (1 : ℝ) ^ (t * 1 ^ t)) := by
  simp

end GroupTPP.STPPWreath
