import Combinatorics.PermutationEndpointProfileTail
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false

namespace PermutationEndpointProfile

/-- Products of factors in the unit interval are stable with the sum of the
individual absolute errors, independently of the number of factors. -/
theorem abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hpg : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg (fun i hi => (hgs i hi).1)
    have hpg1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one
      (fun i hi => (hgs i hi).1) (fun i hi => (hgs i hi).2)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
      _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
          |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ ≤ |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| + |f a - g a| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfa.1, abs_of_nonneg hpg]
        apply add_le_add
        · nlinarith [abs_nonneg ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)]
        · nlinarith [abs_nonneg (f a - g a)]
      _ ≤ _ := by linarith [ih hfs hgs]

/-- Truncated natural subtraction has the required factor error even when the
population is smaller than the descending-factor index. -/
theorem scaled_nat_sub_error (m i n : ℕ) (hn : 0 < n) :
    |((m - i : ℕ) : ℝ) / n - (m : ℝ) / n| ≤ (i : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sub_div, abs_div, abs_of_pos hnR]
  apply div_le_div_of_nonneg_right _ hnR.le
  by_cases hi : i ≤ m
  · rw [Nat.cast_sub hi]
    simp
  · have hmi : m ≤ i := by omega
    rw [Nat.sub_eq_zero_of_le hmi, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg m)]
    exact_mod_cast hmi

/-- Every scaled descending factor lies in the unit interval when the original
population is at most the positive normalization size. -/
theorem scaled_nat_sub_mem_unit (m i n : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    0 ≤ ((m - i : ℕ) : ℝ) / n ∧ ((m - i : ℕ) : ℝ) / n ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_one hnR).mpr
    exact_mod_cast (le_trans (Nat.sub_le m i) hm)

/-- A scaled natural descending factorial is the product of the genuinely
truncated scaled factors, without assuming the population exceeds the degree. -/
theorem descFactorial_div_pow_eq_prod (m s n : ℕ) :
    (m.descFactorial s : ℝ) / (n : ℝ) ^ s =
      ∏ i ∈ Finset.range s, ((m - i : ℕ) : ℝ) / n := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]
  simp

/-- Uniform descending-product approximation, valid even for degrees above the
population. This coarse quadratic bound avoids all unguarded natural casts. -/
theorem descFactorial_div_pow_error (m s n : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    |(m.descFactorial s : ℝ) / (n : ℝ) ^ s - ((m : ℝ) / n) ^ s| ≤
      (s : ℝ) ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (m : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hm)
  rw [descFactorial_div_pow_eq_prod]
  have he := abs_prod_sub_prod_le_sum (Finset.range s)
    (fun i => ((m - i : ℕ) : ℝ) / n) (fun _ => (m : ℝ) / n)
    (fun i _ => scaled_nat_sub_mem_unit m i n hn hm)
    (fun _ _ => ⟨by positivity, hmR⟩)
  simp only [Finset.prod_const, Finset.card_range] at he
  calc
    _ ≤ ∑ i ∈ Finset.range s, |((m - i : ℕ) : ℝ) / n - (m : ℝ) / n| := he
    _ ≤ ∑ i ∈ Finset.range s, (s : ℝ) / n := by
      apply Finset.sum_le_sum
      intro i hi
      exact (scaled_nat_sub_error m i n hn).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hi).le) hnR.le)
    _ = _ := by simp [pow_two, mul_div_assoc]

/-- Gauss' sum in real arithmetic, including the zero boundary. -/
theorem sum_range_cast (s : ℕ) :
    (∑ i ∈ Finset.range s, (i : ℝ)) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Shifted-population descending products approximate powers uniformly in the
population, with the sharp quadratic sum of factor errors. -/
theorem descFactorial_div_pow_shift_error (m c s n : ℕ) (hn : 0 < n)
    (hm : m + c ≤ n) :
    |(m.descFactorial s : ℝ) / (n : ℝ) ^ s - (((m : ℝ) + c) / n) ^ s| ≤
      (s : ℝ) * ((s : ℝ) - 1 + 2 * c) / (2 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : ((m : ℝ) + c) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hm)
  have hfactor (i : ℕ) :
      |((m - i : ℕ) : ℝ) / n - ((m : ℝ) + c) / n| ≤ ((i : ℝ) + c) / n := by
    calc
      _ = |(((m - i : ℕ) : ℝ) / n - (m : ℝ) / n) + (-(c : ℝ) / n)| := by
        congr 1
        ring
      _ ≤ |((m - i : ℕ) : ℝ) / n - (m : ℝ) / n| + |-(c : ℝ) / n| := abs_add_le _ _
      _ ≤ (i : ℝ) / n + (c : ℝ) / n := by
        rw [neg_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (c : ℝ) / n)]
        exact add_le_add (scaled_nat_sub_error m i n hn) le_rfl
      _ = _ := by ring
  rw [descFactorial_div_pow_eq_prod]
  have he := abs_prod_sub_prod_le_sum (Finset.range s)
    (fun i => ((m - i : ℕ) : ℝ) / n) (fun _ => ((m : ℝ) + c) / n)
    (fun i _ => scaled_nat_sub_mem_unit m i n hn (by omega))
    (fun _ _ => ⟨by positivity, hmR⟩)
  simp only [Finset.prod_const, Finset.card_range] at he
  calc
    _ ≤ ∑ i ∈ Finset.range s, |((m - i : ℕ) : ℝ) / n - ((m : ℝ) + c) / n| := he
    _ ≤ ∑ i ∈ Finset.range s, ((i : ℝ) + c) / n :=
      Finset.sum_le_sum (fun i _ => hfactor i)
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, sum_range_cast]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The normalized actual kernel denominator stays in the unit interval and
within its explicit factorial-product error of one. -/
theorem denominator_scaled_bounds (s n : ℕ) (hn : 2 ≤ n) (hs : s ≤ n - 2) :
    let d := ((n - 2).descFactorial s : ℝ) / (n : ℝ) ^ s
    0 ≤ d ∧ d ≤ 1 ∧ |d - 1| ≤ (s : ℝ) * ((s : ℝ) + 3) / (2 * n) := by
  dsimp only
  have hn0 : 0 < n := by omega
  have he := descFactorial_div_pow_shift_error (n - 2) 2 s n hn0 (by omega)
  have hnsub : ((n - 2 : ℕ) : ℝ) + 2 = n := by
    rw [Nat.cast_sub hn]
    norm_num
  norm_num only [Nat.cast_ofNat] at he
  rw [hnsub, div_self (by positivity : (n : ℝ) ≠ 0), one_pow] at he
  refine ⟨by positivity, ?_, ?_⟩
  · rw [descFactorial_div_pow_eq_prod]
    exact Finset.prod_le_one
      (fun i _ => (scaled_nat_sub_mem_unit (n - 2) i n hn0 (by omega)).1)
      (fun i _ => (scaled_nat_sub_mem_unit (n - 2) i n hn0 (by omega)).2)
  · convert he using 1 <;> ring

/-- Above the explicit quadratic threshold the normalized denominator is at least
one half, uniformly in the prescribed endpoint labels. -/
theorem denominator_scaled_half_le (s n : ℕ) (hn : 2 ≤ n)
    (hs : s ≤ n - 2) (hlarge : s * (s + 3) ≤ n) :
    (1 : ℝ) / 2 ≤ ((n - 2).descFactorial s : ℝ) / (n : ℝ) ^ s := by
  have he := (denominator_scaled_bounds s n hn hs).2.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlargeR : (s : ℝ) * ((s : ℝ) + 3) ≤ n := by exact_mod_cast hlarge
  have herr : (s : ℝ) * ((s : ℝ) + 3) / (2 * n) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith
  have hlo := (abs_le.mp (he.trans herr)).1
  linarith

end PermutationEndpointProfile
