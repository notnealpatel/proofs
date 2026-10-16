import Combinatorics.PermutationEndpointProfileAlgebra

set_option autoImplicit false

namespace PermutationEndpointProfile

/-- Multiplication of two unit-interval quantities adds their absolute errors. -/
theorem abs_mul_sub_mul_unit (A B X Y : ℝ)
    (hA : 0 ≤ A ∧ A ≤ 1) (hY : 0 ≤ Y ∧ Y ≤ 1) :
    |A * B - X * Y| ≤ |B - Y| + |A - X| := by
  calc
    _ = |A * (B - Y) + (A - X) * Y| := by congr 1; ring
    _ ≤ |A * (B - Y)| + |(A - X) * Y| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA.1, abs_of_nonneg hY.1]
      apply add_le_add <;> nlinarith [abs_nonneg (B - Y), abs_nonneg (A - X)]

/-- Positive normalization preserves the unit interval for descending products. -/
theorem descFactorial_div_pow_mem_unit (m k n : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    0 ≤ (m.descFactorial k : ℝ) / (n : ℝ)^k ∧
      (m.descFactorial k : ℝ) / (n : ℝ)^k ≤ 1 := by
  rw [descFactorial_div_pow_eq_prod]
  exact ⟨Finset.prod_nonneg (fun i _ => (scaled_nat_sub_mem_unit m i n hn hm).1),
    Finset.prod_le_one (fun i _ => (scaled_nat_sub_mem_unit m i n hn hm).1)
      (fun i _ => (scaled_nat_sub_mem_unit m i n hn hm).2)⟩

/-- The three numerator blocks have the uniform sharp quadratic approximation;
zero populations and populations smaller than the ranks are included. -/
theorem three_block_scaled_error (m₀ m₁ m₂ r q h s n : ℕ)
    (hn : 0 < n) (hm₀ : m₀ ≤ n) (hm₁ : m₁ + 1 ≤ n) (hm₂ : m₂ + 1 ≤ n)
    (hrs : r + q + h = s) :
    |((m₀.descFactorial r : ℝ) / (n : ℝ)^r) *
        ((m₁.descFactorial q : ℝ) / (n : ℝ)^q) *
        ((m₂.descFactorial h : ℝ) / (n : ℝ)^h) -
      ((m₀ : ℝ)/n)^r * (((m₁ : ℝ)+1)/n)^q * (((m₂ : ℝ)+1)/n)^h| ≤
      (s : ℝ) * ((s : ℝ) + 1) / (2 * n) := by
  let A : ℝ := (m₀.descFactorial r : ℝ) / (n : ℝ)^r
  let B : ℝ := (m₁.descFactorial q : ℝ) / (n : ℝ)^q
  let C : ℝ := (m₂.descFactorial h : ℝ) / (n : ℝ)^h
  let X : ℝ := ((m₀ : ℝ)/n)^r
  let Y : ℝ := (((m₁ : ℝ)+1)/n)^q
  let Z : ℝ := (((m₂ : ℝ)+1)/n)^h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA := descFactorial_div_pow_mem_unit m₀ r n hn hm₀
  have hB := descFactorial_div_pow_mem_unit m₁ q n hn (by omega)
  have hC := descFactorial_div_pow_mem_unit m₂ h n hn (by omega)
  have hY : 0 ≤ Y ∧ Y ≤ 1 := by
    dsimp [Y]
    exact ⟨by positivity, pow_le_one₀ (by positivity)
      ((div_le_one hnR).mpr (by exact_mod_cast hm₁))⟩
  have hZ : 0 ≤ Z ∧ Z ≤ 1 := by
    dsimp [Z]
    exact ⟨by positivity, pow_le_one₀ (by positivity)
      ((div_le_one hnR).mpr (by exact_mod_cast hm₂))⟩
  have hAB : 0 ≤ A * B ∧ A * B ≤ 1 :=
    ⟨mul_nonneg hA.1 hB.1, by nlinarith [mul_nonneg (sub_nonneg.mpr hA.2) hB.1]⟩
  have he₀ := descFactorial_div_pow_shift_error m₀ 0 r n hn (by omega)
  have he₁ := descFactorial_div_pow_shift_error m₁ 1 q n hn hm₁
  have he₂ := descFactorial_div_pow_shift_error m₂ 1 h n hn hm₂
  norm_num only [Nat.cast_zero, Nat.cast_one, add_zero, mul_zero] at he₀ he₁ he₂
  have hsum : (r : ℝ) + q + h = s := by exact_mod_cast hrs
  have hquad : (r : ℝ) * ((r : ℝ) - 1) +
      (q : ℝ) * ((q : ℝ) - 1 + 2 * 1) +
      (h : ℝ) * ((h : ℝ) - 1 + 2 * 1) ≤ (s : ℝ) * ((s : ℝ) + 1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
      mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (Nat.cast_nonneg h : (0 : ℝ) ≤ h),
      mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  calc
    _ ≤ |C - Z| + (|B - Y| + |A - X|) :=
      (abs_mul_sub_mul_unit (A*B) C (X*Y) Z hAB hZ).trans
        (add_le_add le_rfl (abs_mul_sub_mul_unit A B X Y hA hY))
    _ ≤ (h : ℝ) * ((h : ℝ)-1+2*1)/(2*n) +
        ((q : ℝ) * ((q : ℝ)-1+2*1)/(2*n) +
          (r : ℝ) * ((r : ℝ)-1)/(2*n)) := by
      simpa only [mul_one] using add_le_add he₂ (add_le_add he₁ he₀)
    _ ≤ _ := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Dividing by a denominator within its explicit error of one costs at most
twice the sum of numerator and denominator errors when that denominator is at
least one half. -/
theorem normalized_error (A U d E D : ℝ) (hd : 1 / 2 ≤ d)
    (hU : 0 ≤ U ∧ U ≤ 1) (hA : |A-U| ≤ E) (hD : |d-1| ≤ D) :
    |A/d-U| ≤ 2*(E+D) := by
  have hd0 : 0 < d := by linarith
  have hE : 0 ≤ E := (abs_nonneg _).trans hA
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hnum : |A - U*d| ≤ E+D := by
    calc
      _ = |(A-U)+U*(1-d)| := by congr 1; ring
      _ ≤ |A-U| + |U*(1-d)| := abs_add_le _ _
      _ ≤ E+D := by
        rw [abs_mul, abs_of_nonneg hU.1, abs_sub_comm 1 d]
        have hu : U * |d-1| ≤ |d-1| := by nlinarith [abs_nonneg (d-1)]
        linarith
  have hid : A/d-U = (A-U*d)/d := by field_simp
  rw [hid, abs_div, abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  nlinarith

/-- Three scaled descending numerator blocks divided by the scaled kernel
denominator approximate the continuous monomial with the uniform `2s(s+2)/n`
error. Factorial weights, which can only improve it, are handled downstream. -/
theorem three_block_normalized_error (m₀ m₁ m₂ r q h s n : ℕ)
    (hn : 2 ≤ n) (hs : s ≤ n - 2) (hlarge : s * (s + 3) ≤ n)
    (hm₀ : m₀ ≤ n) (hm₁ : m₁ + 1 ≤ n) (hm₂ : m₂ + 1 ≤ n)
    (hrs : r + q + h = s) :
    |(((m₀.descFactorial r : ℝ) / (n : ℝ)^r) *
        ((m₁.descFactorial q : ℝ) / (n : ℝ)^q) *
        ((m₂.descFactorial h : ℝ) / (n : ℝ)^h)) /
        (((n - 2).descFactorial s : ℝ) / (n : ℝ)^s) -
      ((m₀ : ℝ)/n)^r * (((m₁ : ℝ)+1)/n)^q * (((m₂ : ℝ)+1)/n)^h| ≤
      2 * (s : ℝ) * ((s : ℝ)+2) / n := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hU₀ : 0 ≤ ((m₀ : ℝ)/n)^r ∧ ((m₀ : ℝ)/n)^r ≤ 1 :=
    ⟨by positivity, pow_le_one₀ (by positivity)
      ((div_le_one hnR).mpr (by exact_mod_cast hm₀))⟩
  have hU₁ : 0 ≤ (((m₁ : ℝ)+1)/n)^q ∧ (((m₁ : ℝ)+1)/n)^q ≤ 1 :=
    ⟨by positivity, pow_le_one₀ (by positivity)
      ((div_le_one hnR).mpr (by exact_mod_cast hm₁))⟩
  have hU₂ : 0 ≤ (((m₂ : ℝ)+1)/n)^h ∧ (((m₂ : ℝ)+1)/n)^h ≤ 1 :=
    ⟨by positivity, pow_le_one₀ (by positivity)
      ((div_le_one hnR).mpr (by exact_mod_cast hm₂))⟩
  have hp₀₁ : ((m₀ : ℝ)/n)^r * (((m₁ : ℝ)+1)/n)^q ≤ 1 := by
    nlinarith [mul_nonneg hU₀.1 (sub_nonneg.mpr hU₁.2)]
  have hp : ((m₀ : ℝ)/n)^r * (((m₁ : ℝ)+1)/n)^q * (((m₂ : ℝ)+1)/n)^h ≤ 1 := by
    nlinarith [mul_nonneg (mul_nonneg hU₀.1 hU₁.1) (sub_nonneg.mpr hU₂.2)]
  have he := normalized_error _ _ _ _ _ (denominator_scaled_half_le s n hn hs hlarge)
    ⟨by positivity, hp⟩
    (three_block_scaled_error m₀ m₁ m₂ r q h s n hn0 hm₀ hm₁ hm₂ hrs)
    (denominator_scaled_bounds s n hn hs).2.2
  convert he using 1 <;> ring

end PermutationEndpointProfile
