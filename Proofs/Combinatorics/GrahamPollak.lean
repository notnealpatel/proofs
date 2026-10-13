import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace ErdosCandidates.E482

/-- The Graham–Pollak sequence with the unused zero index. -/
noncomputable def gp : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => ⌊Real.sqrt 2 * (gp n + 1 / 2)⌋₊

/-- Binary digits of square root two, starting with the integer-part bit. -/
noncomputable def sqrtTwoDigit (n : ℕ) : ℤ :=
  ⌊Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 1)⌋ -
    2 * ⌊Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 2)⌋

example : gp 0 = 0 := rfl
example : gp 1 = 1 := rfl
example : sqrtTwoDigit 1 = ⌊Real.sqrt 2⌋ - 2 * ⌊Real.sqrt 2 / 2⌋ := by
  norm_num [sqrtTwoDigit, zpow_neg, mul_one_div]

private lemma sqrt_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 ∧
    (Real.sqrt 2) ^ 2 = 2 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  constructor
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact Real.sq_sqrt (by norm_num)

/-- Odd-state floor form in the paired recurrence. -/
noncomputable def gpA (m : ℕ) : ℕ := m + ⌊(m : ℝ) / Real.sqrt 2⌋₊
/-- Even-state floor form in the paired recurrence. -/
noncomputable def gpB (m : ℕ) : ℕ := m + ⌊Real.sqrt 2 * m⌋₊

example : gpA 0 = 0 := by simp [gpA]
example : gpB 0 = 0 := by simp [gpB]

/-- The first paired transition: T(A(m)) = B(m). The half-threshold
of the fractional part of m/√2 agrees exactly with that of √2 m. -/
theorem gpA_step (m : ℕ) :
    ⌊Real.sqrt 2 * ((gpA m : ℝ) + 1 / 2)⌋₊ = gpB m := by
  obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds
  let s := Real.sqrt 2
  have hs : 0 < s := by dsimp [s]; linarith
  let q : ℕ := ⌊(m : ℝ) / s⌋₊
  let r : ℝ := (m : ℝ) / s - q
  have hnon : 0 ≤ (m : ℝ) / s := div_nonneg (Nat.cast_nonneg m) hs.le
  have hq : (q : ℝ) ≤ (m : ℝ) / s := Nat.floor_le hnon
  have hq' : (m : ℝ) / s < q + 1 := Nat.lt_floor_add_one _
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hm : (m : ℝ) = s * (q + r) := by dsimp [r]; field_simp; ring
  have hsquare : s * s = 2 := by dsimp [s]; nlinarith [hsq]
  have hsm : s * m = 2 * (q : ℝ) + 2 * r := by rw [hm]; nlinarith [hsquare]
  have hsq' : s * q = m - s * r := by nlinarith [hm]
  have harg : s * ((gpA m : ℝ) + 1 / 2) =
      (m : ℝ) + 2 * q + (2 - s) * r + s / 2 := by
    simp only [gpA, Nat.cast_add]
    change s * ((m : ℝ) + q + 1 / 2) = _
    nlinarith [hsm, hsq']
  have harg0 : 0 ≤ s * ((gpA m : ℝ) + 1 / 2) :=
    mul_nonneg hs.le (by positivity)
  by_cases hr : r < 1 / 2
  · have hp : ⌊s * m⌋₊ = 2 * q := (Nat.floor_eq_iff (by positivity)).2 (by
      constructor <;> push_cast <;> nlinarith [hsm])
    change ⌊s * ((gpA m : ℝ) + 1 / 2)⌋₊ = m + ⌊s * m⌋₊
    rw [hp]
    apply (Nat.floor_eq_iff harg0).2
    constructor <;> push_cast <;> nlinarith [harg, mul_pos (show 0 < 2 - s by dsimp [s]; linarith) (show 0 < 1 / 2 - r by linarith)]
  · have hp : ⌊s * m⌋₊ = 2 * q + 1 := (Nat.floor_eq_iff (by positivity)).2 (by
      constructor <;> push_cast <;> nlinarith [hsm])
    change ⌊s * ((gpA m : ℝ) + 1 / 2)⌋₊ = m + ⌊s * m⌋₊
    rw [hp]
    apply (Nat.floor_eq_iff harg0).2
    constructor <;> push_cast <;>
      nlinarith [harg, mul_nonneg (show 0 ≤ 2 - s by dsimp [s]; linarith) (show 0 ≤ r - 1 / 2 by linarith),
        mul_pos (show 0 < 2 - s by dsimp [s]; linarith) (show 0 < 1 - r by linarith)]

/-- The second paired transition: T(B(m)) = A(2m); its residual
√2/2 − (√2−1) frac(√2 m) lies strictly between zero and one. -/
theorem gpB_step (m : ℕ) :
    ⌊Real.sqrt 2 * ((gpB m : ℝ) + 1 / 2)⌋₊ = gpA (2 * m) := by
  obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds
  let s := Real.sqrt 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hsquare : s * s = 2 := by dsimp [s]; nlinarith [hsq]
  have hdiv : (2 * m : ℝ) / s = s * m := by
    apply (div_eq_iff hs.ne').2
    nlinarith [hsquare]
  let p : ℕ := ⌊s * m⌋₊
  let t : ℝ := s * m - p
  have hp : (p : ℝ) ≤ s * m := Nat.floor_le (by positivity)
  have hp' : s * m < p + 1 := Nat.lt_floor_add_one _
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hsm : s * m = p + t := by dsimp [t]; ring
  have hsp : s * p = 2 * m - s * t := by nlinarith [hsquare, hsm]
  have harg : s * ((gpB m : ℝ) + 1 / 2) =
      2 * m + p + s / 2 - (s - 1) * t := by
    simp only [gpB, Nat.cast_add]
    change s * ((m : ℝ) + p + 1 / 2) = _
    nlinarith [hsm, hsp]
  change ⌊s * ((gpB m : ℝ) + 1 / 2)⌋₊ = 2 * m + ⌊((2 * m : ℕ) : ℝ) / s⌋₊
  push_cast
  rw [hdiv]
  change _ = 2 * m + p
  apply (Nat.floor_eq_iff (mul_nonneg hs.le (by positivity))).2
  constructor <;> push_cast <;>
    nlinarith [harg, mul_nonneg (show 0 ≤ s - 1 by dsimp [s]; linarith) ht0,
      mul_pos (show 0 < s - 1 by dsimp [s]; linarith) (show 0 < 1 - t by linarith)]

/-- The initial odd state is A(1)=1. -/
theorem gpA_one : gpA 1 = 1 := by
  obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds
  have hf : ⌊(1 : ℝ) / Real.sqrt 2⌋₊ = 0 := by
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor
    · norm_num
    · simp only [Nat.cast_zero, zero_add]
      exact (div_lt_one (by positivity)).2 hs1
  unfold gpA
  norm_num only [Nat.cast_one]
  rw [hf]

private lemma gp_succ (k : ℕ) (hk : 1 ≤ k) :
    gp (k + 1) = ⌊Real.sqrt 2 * ((gp k : ℝ) + 1 / 2)⌋₊ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [gp]
  omega

/-- Paired closed forms at powers of two, starting at index one. -/
theorem gp_pair (n : ℕ) :
    gp (2 * n + 1) = gpA (2 ^ n) ∧ gp (2 * n + 2) = gpB (2 ^ n) := by
  induction n with
  | zero =>
    constructor
    · simpa only [Nat.mul_zero, zero_add, pow_zero, gp] using gpA_one.symm
    · rw [show 2 * 0 + 2 = 1 + 1 by omega, gp_succ 1 (by omega)]
      simpa only [pow_zero, gpA_one, gp] using gpA_step 1
  | succ n ih =>
    have hodd : gp (2 * (n + 1) + 1) = gpA (2 ^ (n + 1)) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
        gp_succ _ (by omega), ih.2, gpB_step]
      congr 1
      rw [pow_succ]
      omega
    constructor
    · exact hodd
    · rw [show 2 * (n + 1) + 2 = (2 * (n + 1) + 1) + 1 by omega,
        gp_succ _ (by omega), hodd, gpA_step]

private lemma div_sqrt_two (x : ℝ) : x / Real.sqrt 2 = Real.sqrt 2 * x / 2 := by
  obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds
  apply (div_eq_iff (show Real.sqrt 2 ≠ 0 by linarith)).2
  calc
    x = x * (Real.sqrt 2 * Real.sqrt 2) / 2 := by
      rw [← pow_two, hsq]; ring
    _ = Real.sqrt 2 * x / 2 * Real.sqrt 2 := by ring
private lemma power_shift (n : ℕ) :
    (2 : ℝ) ^ ((n : ℤ) - 1) = (2 : ℝ) ^ n / 2 := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_one]

/-- The odd-index formula in integer-floor form, including n=0. -/
theorem gp_odd (n : ℕ) : (gp (2 * n + 1) : ℤ) =
    (2 : ℤ) ^ n + ⌊Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 1)⌋ := by
  rw [(gp_pair n).1, gpA, Nat.cast_add, Nat.cast_pow,
    Int.natCast_floor_eq_floor (by positivity)]
  congr 1
  congr 1
  rw [Nat.cast_pow, Nat.cast_ofNat, div_sqrt_two, power_shift]
  ring

/-- The recurrence difference is the binary digit, with subtraction in ℤ. -/
theorem graham_pollak_identity (n : ℕ) (hn : 1 ≤ n) :
    (gp (2 * n + 1) : ℤ) - 2 * (gp (2 * n - 1) : ℤ) = sqrtTwoDigit n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, gp_odd, gp_odd]
  have he : ((k + 1 : ℕ) : ℤ) - 2 = (k : ℤ) - 1 := by omega
  simp only [sqrtTwoDigit, he, pow_succ]
  ring

private lemma floor_double (x : ℝ) : ⌊2 * x⌋ - 2 * ⌊x⌋ = 0 ∨
    ⌊2 * x⌋ - 2 * ⌊x⌋ = 1 := by
  have hlo : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := Int.le_floor.mpr (by
    push_cast
    linarith [Int.floor_le x])
  have hhi : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := Int.floor_lt.mpr (by
    push_cast
    linarith [Int.lt_floor_add_one x])
  omega

/-- Every extracted digit is zero or one. Fractional-part bracketing
suffices; irrationality is not needed. -/
theorem sqrtTwoDigit_binary (n : ℕ) (_hn : 1 ≤ n) :
    sqrtTwoDigit n = 0 ∨ sqrtTwoDigit n = 1 := by
  have he : (n : ℤ) - 1 = ((n : ℤ) - 2) + 1 := by omega
  have hx : Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 1) =
      2 * (Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 2)) := by
    rw [he, zpow_add₀ (by norm_num), zpow_one]
    ring
  simpa only [sqrtTwoDigit, hx] using
    floor_double (Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 2))

private lemma weight_pow (n : ℕ) :
    (2 : ℝ) ^ (1 - (n : ℤ)) = 2 / (2 : ℝ) ^ n := by
  rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]

private lemma floor_initial : ⌊Real.sqrt 2 / 2⌋ = (0 : ℤ) := by
  obtain ⟨hs1, hs2, hsq⟩ := sqrt_bounds
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num <;> linarith

/-- The partial digit sum telescopes to the scaled floor, including N=0. -/
theorem sqrtTwoDigit_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (sqrtTwoDigit n : ℝ) * (2 : ℝ) ^ (1 - (n : ℤ))) =
    (⌊Real.sqrt 2 * (2 : ℝ) ^ ((N : ℤ) - 1)⌋ : ℝ) *
      (2 : ℝ) ^ (1 - (N : ℤ)) := by
  induction N with
  | zero => norm_num [mul_one_div, floor_initial]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have he : ((N + 1 : ℕ) : ℤ) - 2 = (N : ℤ) - 1 := by omega
    simp only [sqrtTwoDigit, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, he]
    rw [weight_pow, weight_pow, pow_succ]
    field_simp
    ring

/-- The floor approximation error lies in [0, 2·(1/2)^N). -/
theorem sqrtTwoDigit_sum_error (N : ℕ) :
    0 ≤ Real.sqrt 2 - (∑ n ∈ Finset.Icc 1 N,
      (sqrtTwoDigit n : ℝ) * (2 : ℝ) ^ (1 - (n : ℤ))) ∧
    Real.sqrt 2 - (∑ n ∈ Finset.Icc 1 N,
      (sqrtTwoDigit n : ℝ) * (2 : ℝ) ^ (1 - (n : ℤ))) <
      2 * (1 / 2 : ℝ) ^ N := by
  rw [sqrtTwoDigit_sum, weight_pow, power_shift]
  let x := Real.sqrt 2 * ((2 : ℝ) ^ N / 2)
  have hw : 0 < 2 / (2 : ℝ) ^ N := by positivity
  have he : x * (2 / (2 : ℝ) ^ N) = Real.sqrt 2 := by
    dsimp [x]
    field_simp
  have hweight : 2 * (1 / 2 : ℝ) ^ N = 2 / (2 : ℝ) ^ N := by
    rw [div_pow, one_pow]; ring
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le x) hw.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one x) hw
  change 0 ≤ Real.sqrt 2 - (⌊x⌋ : ℝ) * (2 / (2 : ℝ) ^ N) ∧
    Real.sqrt 2 - (⌊x⌋ : ℝ) * (2 / (2 : ℝ) ^ N) < _
  rw [hweight]
  constructor <;> nlinarith [he]

/-- The binary digit partial sums converge to square root two. -/
theorem sqrtTwoDigit_tendsto :
    Filter.Tendsto
      (fun N => ∑ n ∈ Finset.Icc 1 N,
        (sqrtTwoDigit n : ℝ) * (2 : ℝ) ^ (1 - (n : ℤ)))
      Filter.atTop (nhds (Real.sqrt 2)) := by
  have hw : Filter.Tendsto (fun N : ℕ => 2 * (1 / 2 : ℝ) ^ N)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  have herr := squeeze_zero (fun N => (sqrtTwoDigit_sum_error N).1)
    (fun N => (sqrtTwoDigit_sum_error N).2.le) hw
  have hlim := (tendsto_const_nhds (x := Real.sqrt 2)
    (f := Filter.atTop (α := ℕ))).sub herr
  simpa using hlim

/-- The even-index formula in integer-floor form. -/
theorem gp_even (n : ℕ) : (gp (2 * n + 2) : ℤ) =
    (2 : ℤ) ^ n + ⌊Real.sqrt 2 * (2 : ℝ) ^ n⌋ := by
  rw [(gp_pair n).2, gpB, Nat.cast_add, Nat.cast_pow,
    Int.natCast_floor_eq_floor (by positivity)]
  norm_cast

private lemma sqrt_tight : (14142 / 10000 : ℝ) < Real.sqrt 2 ∧
    Real.sqrt 2 < (14143 / 10000 : ℝ) := by
  constructor
  · apply (Real.lt_sqrt (by norm_num)).2
    norm_num
  · apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num

private lemma sqrt_floors : ⌊Real.sqrt 2⌋ = (1 : ℤ) ∧
    ⌊Real.sqrt 2 * 2⌋ = (2 : ℤ) ∧ ⌊Real.sqrt 2 * 4⌋ = (5 : ℤ) ∧
    ⌊Real.sqrt 2 * 8⌋ = (11 : ℤ) ∧ ⌊Real.sqrt 2 * 16⌋ = (22 : ℤ) ∧
    ⌊Real.sqrt 2 * 32⌋ = (45 : ℤ) := by
  obtain ⟨hlo, hhi⟩ := sqrt_tight
  repeat' constructor
  all_goals apply Int.floor_eq_iff.mpr
  all_goals constructor <;> norm_num <;> linarith

/-- The first six bits, checked by rational bracketing of square root two. -/
theorem sqrtTwoDigit_first_six : sqrtTwoDigit 1 = 1 ∧ sqrtTwoDigit 2 = 0 ∧
    sqrtTwoDigit 3 = 1 ∧ sqrtTwoDigit 4 = 1 ∧ sqrtTwoDigit 5 = 0 ∧
    sqrtTwoDigit 6 = 1 := by
  obtain ⟨h1, h2, h4, h8, h16, h32⟩ := sqrt_floors
  norm_num [sqrtTwoDigit, zpow_neg, mul_one_div, floor_initial, h1, h2, h4, h8, h16, h32]

/-- The first nine recurrence values, obtained from the paired forms. -/
theorem gp_first_nine : gp 2 = 2 ∧ gp 3 = 3 ∧ gp 4 = 4 ∧ gp 5 = 6 ∧
    gp 6 = 9 ∧ gp 7 = 13 ∧ gp 8 = 19 ∧ gp 9 = 27 := by
  obtain ⟨h1, h2, h4, h8, h16, h32⟩ := sqrt_floors
  have ho1 := gp_odd 1
  have ho2 := gp_odd 2
  have ho3 := gp_odd 3
  have ho4 := gp_odd 4
  have he0 := gp_even 0
  have he1 := gp_even 1
  have he2 := gp_even 2
  have he3 := gp_even 3
  norm_num [h1, h2, h4, h8, h16] at ho1 ho2 ho3 ho4 he0 he1 he2 he3
  omega

example : 1 ≤ (1 : ℕ) ∧
    (gp 3 : ℤ) - 2 * (gp 1 : ℤ) = sqrtTwoDigit 1 :=
  ⟨by decide, graham_pollak_identity 1 (by decide)⟩

end ErdosCandidates.E482
