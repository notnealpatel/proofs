import Combinatorics.AffineRetainedVariance
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace AffineRetainedFourier

variable {p : ℕ} [Fact p.Prime]

/-- Normalized Fourier coefficient of the indicator of `C`, with negative sign. -/
def hatC (C : Finset (ZMod p)) (k : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ x ∈ C, ZMod.stdAddChar (-(k * x))

/-- Positive-sign exponential sum of the window. -/
def DJ (J : Finset (ZMod p)) (t : ZMod p) : ℂ :=
  ∑ j ∈ J, ZMod.stdAddChar (t * j)

/-- Total Fourier weight away from zero. -/
def L (C : Finset (ZMod p)) : ℝ :=
  ∑ k ∈ AffineRetainedVariance.directions (ZMod p), ‖hatC C k‖

/-- Actual translation-averaged centered fourth moment. -/
def F4 (C J : Finset (ZMod p)) (a : ZMod p) : ℝ :=
  (∑ b : ZMod p,
    (AffineRetainedVariance.Y C J a b - AffineRetainedVariance.mean C J) ^ 4) / (p : ℝ)

example (k : ZMod p) : hatC ∅ k = 0 := by simp [hatC]
example (J : Finset (ZMod p)) : DJ J 0 = J.card := by simp [DJ]
example : L (∅ : Finset (ZMod p)) = 0 := by simp [L, hatC]
example (a : ZMod p) : F4 ∅ ∅ a = 0 := by
  simp [F4, AffineRetainedVariance.Y, AffineRetainedVariance.mean]

/-- Orthogonality of the actual standard additive character. -/
theorem orthogonality (u : ZMod p) :
    (∑ t : ZMod p, ZMod.stdAddChar (t * u)) = if u = 0 then (p : ℂ) else 0 := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [if_neg hu]
    simpa only [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hu)

/-- The coefficient at zero is the density of the set. -/
theorem hatC_zero (C : Finset (ZMod p)) :
    hatC C 0 = (C.card : ℂ) / p := by
  simp [hatC, div_eq_mul_inv, mul_comm]

/-- Fourier inversion for the real indicator, cast to the complex numbers. -/
theorem indicator_inversion (C : Finset (ZMod p)) (x : ZMod p) :
    (AffineRetainedVariance.indicator C x : ℂ) =
      ∑ k : ZMod p, hatC C k * ZMod.stdAddChar (k * x) := by
  let f : ZMod p → ℂ := fun y ↦ if y ∈ C then 1 else 0
  have hf (k : ZMod p) :
      ZMod.dft f k = ∑ y ∈ C, ZMod.stdAddChar (-(k * y)) := by
    simp [ZMod.dft_apply, f, smul_eq_mul, mul_comm]
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, hf] at hinv
  rw [Finset.mul_sum] at hinv
  simp only [AffineRetainedVariance.indicator, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero]
  simpa [f, hatC, mul_comm, mul_left_comm,
    mul_assoc] using hinv.symm

/-- Fourier inversion of the centered affine count, with the zero frequency removed. -/
theorem centered_inversion (C J : Finset (ZMod p)) (a b : ZMod p) :
    ((AffineRetainedVariance.Y C J a b - AffineRetainedVariance.mean C J : ℝ) : ℂ) =
      ∑ k ∈ AffineRetainedVariance.directions (ZMod p),
        hatC C k * DJ J (a * k) * ZMod.stdAddChar (k * b) := by
  have hfull : (AffineRetainedVariance.Y C J a b : ℂ) =
      ∑ k : ZMod p, hatC C k * DJ J (a * k) * ZMod.stdAddChar (k * b) := by
    simp only [AffineRetainedVariance.Y, Complex.ofReal_sum, indicator_inversion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [DJ, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_add, AddChar.map_add_eq_mul]
    rw [show k * (a * j) = a * k * j by ring]
    ring
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun k : ZMod p ↦ hatC C k * DJ J (a * k) * ZMod.stdAddChar (k * b))
    (Finset.mem_univ 0)
  have hzero : hatC C 0 * DJ J (a * 0) * ZMod.stdAddChar (0 * b) =
      (AffineRetainedVariance.mean C J : ℂ) := by
    simp [hatC_zero, DJ, AffineRetainedVariance.mean, div_eq_mul_inv,
      mul_assoc, mul_comm]
  rw [hzero, ← hfull] at hsplit
  rw [Complex.ofReal_sub]
  exact eq_sub_of_add_eq hsplit |>.symm

/-- Squared complex modulus expanded as the product with its conjugate. -/
theorem DJ_norm_sq (J : Finset (ZMod p)) (t : ZMod p) :
    ((‖DJ J t‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ J, ∑ l ∈ J, ZMod.stdAddChar (t * (j - l)) := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [DJ, map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The full Fourier energy of the actual window sum. -/
theorem DJ_energy (J : Finset (ZMod p)) :
    ∑ t : ZMod p, ‖DJ J t‖ ^ 2 = (p : ℝ) * J.card := by
  have hc : ((∑ t : ZMod p, ‖DJ J t‖ ^ 2 : ℝ) : ℂ) = (p : ℂ) * J.card := by
    simp only [Complex.ofReal_sum, DJ_norm_sq]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ), orthogonality, sub_eq_zero]
    simp [mul_comm]
  exact_mod_cast hc

/-- Exact window energy over nonzero directions for every nonzero frequency. -/
theorem DJ_nonzero_energy (J : Finset (ZMod p)) (k : ZMod p) (hk : k ≠ 0) :
    (∑ a ∈ AffineRetainedVariance.directions (ZMod p), ‖DJ J (a * k)‖ ^ 2) =
      (J.card : ℝ) * ((p : ℝ) - J.card) := by
  have hfull : (∑ a : ZMod p, ‖DJ J (a * k)‖ ^ 2) = (p : ℝ) * J.card := by
    calc
      _ = ∑ t : ZMod p, ‖DJ J t‖ ^ 2 :=
        Equiv.sum_comp (Equiv.mulRight₀ k hk) (fun t ↦ ‖DJ J t‖ ^ 2)
      _ = _ := DJ_energy J
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun a : ZMod p ↦ ‖DJ J (a * k)‖ ^ 2) (Finset.mem_univ 0)
  rw [hfull] at hsplit
  have hzero : ‖DJ J (0 * k)‖ ^ 2 = (J.card : ℝ) ^ 2 := by
    simp [DJ]
  rw [hzero] at hsplit
  change (∑ a ∈ Finset.univ.erase 0, ‖DJ J (a * k)‖ ^ 2) = _
  nlinarith [hsplit]

/-- Triangle inequality for the actual centered affine count. -/
theorem centered_abs_le (C J : Finset (ZMod p)) (a b : ZMod p) :
    |AffineRetainedVariance.Y C J a b - AffineRetainedVariance.mean C J| ≤
      ∑ k ∈ AffineRetainedVariance.directions (ZMod p), ‖hatC C k‖ * ‖DJ J (a * k)‖ := by
  have hnorm := norm_sum_le (AffineRetainedVariance.directions (ZMod p))
    (fun k ↦ hatC C k * DJ J (a * k) * ZMod.stdAddChar (k * b))
  rw [← centered_inversion] at hnorm
  simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
    ZMod.stdAddChar_apply, Circle.norm_coe, mul_one] using hnorm

/-- A uniform pointwise square bound converts the second moment into the fourth. -/
theorem F4_le_S (C J : Finset (ZMod p)) (a : ZMod p) :
    F4 C J a ≤ AffineRetainedVariance.S C J a *
      (∑ k ∈ AffineRetainedVariance.directions (ZMod p),
        ‖hatC C k‖ * ‖DJ J (a * k)‖) ^ 2 := by
  let B : ℝ := ∑ k ∈ AffineRetainedVariance.directions (ZMod p),
    ‖hatC C k‖ * ‖DJ J (a * k)‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k hk ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hpoint (b : ZMod p) :
      (AffineRetainedVariance.Y C J a b - AffineRetainedVariance.mean C J) ^ 4 ≤
        (AffineRetainedVariance.Y C J a b - AffineRetainedVariance.mean C J) ^ 2 * B ^ 2 := by
    let f := AffineRetainedVariance.Y C J a b - AffineRetainedVariance.mean C J
    have habs : |f| ≤ B := centered_abs_le C J a b
    have hsquare : f ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg f) hB).mpr habs
    calc
      f ^ 4 = f ^ 2 * f ^ 2 := by ring
      _ ≤ f ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hsquare (sq_nonneg f)
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  simpa only [F4, AffineRetainedVariance.S, ZMod.card, ← Finset.sum_mul,
    div_mul_eq_mul_div] using div_le_div_of_nonneg_right (Finset.sum_le_sum (fun b hb ↦ hpoint b)) hp

/-- The actual retained fourth moment is bounded by the squared Fourier weight,
with no Fourier or energy hypotheses. -/
theorem retained_fourth_mean_le (C J : Finset (ZMod p))
    (hp : 3 ≤ p) (hq : 1 ≤ J.card)
    (hm : 2 * (C.card : ℝ) = (p : ℝ) + 1) :
    (∑ a ∈ AffineRetainedVariance.retained C J, F4 C J a) /
      ((AffineRetainedVariance.retained C J).card : ℝ) ≤
        (J.card : ℝ) ^ 2 * L C ^ 2 := by
  apply AffineRetainedVariance.half_interval_fourth_mean_le C J
    (AffineRetainedVariance.directions (ZMod p)) (fun k ↦ ‖hatC C k‖)
    (fun a k ↦ ‖DJ J (a * k)‖) (F4 C J) (L C)
    (by simpa using hp) hq (by simpa using hm)
    (fun k hk ↦ norm_nonneg _) ?_ (fun a ha ↦ F4_le_S C J a) (le_refl _)
  intro k hk
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
  simpa using (DJ_nonzero_energy J k hk0).le

example : 3 ≤ (3 : ℕ) ∧ 1 ≤ ({0} : Finset (ZMod 3)).card ∧
    2 * (({0, 1} : Finset (ZMod 3)).card : ℝ) = (3 : ℝ) + 1 := by
  norm_num

example : (AffineRetainedVariance.retained ({0, 1} : Finset (ZMod 3)) {0}).Nonempty :=
  AffineRetainedVariance.retained_nonempty _ _

example : (∑ a ∈ AffineRetainedVariance.retained ({0, 1} : Finset (ZMod 3)) {0},
    F4 {0, 1} {0} a) /
      ((AffineRetainedVariance.retained ({0, 1} : Finset (ZMod 3)) {0}).card : ℝ) ≤
        L ({0, 1} : Finset (ZMod 3)) ^ 2 := by
  simpa using retained_fourth_mean_le ({0, 1} : Finset (ZMod 3)) {0}
    (by norm_num) (by norm_num) (by norm_num)

end AffineRetainedFourier
