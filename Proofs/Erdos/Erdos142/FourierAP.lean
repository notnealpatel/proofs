/-
  Erdős Problem #142 — finite Fourier analysis of cyclic three-term progressions.

  Mathlib's `ZMod.dft` uses counting measure and the negative exponential sign.
  This file gives it an explicit unnormalized name, proves the exact trilinear
  identity for three-term progressions, and derives mixed Fourier/L2 bounds.
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators ComplexConjugate ZMod
open Finset

namespace Erdos142

/-- The unnormalized discrete Fourier transform on `ZMod p`; explicitly,
`unnormalizedDFT f r = ∑ x, stdAddChar (-(x*r)) * f x`. -/
noncomputable def unnormalizedDFT (p : ℕ) [NeZero p]
    (f : ZMod p → ℂ) : ZMod p → ℂ :=
  ZMod.dft f

/-- The cyclic, ordered three-term-progression trilinear sum. -/
noncomputable def threeAPSum (p : ℕ) [NeZero p]
    (u v w : ZMod p → ℂ) : ℂ :=
  ∑ x : ZMod p, ∑ d : ZMod p, u x * v (x + d) * w (x + 2 * d)

/-- The named Fourier transform is exactly Mathlib's counting-measure DFT,
including its negative sign convention. -/
theorem unnormalizedDFT_apply (p : ℕ) [NeZero p] (f : ZMod p → ℂ) (r : ZMod p) :
    unnormalizedDFT p f r =
      ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x := by
  simp only [unnormalizedDFT, ZMod.dft_apply, smul_eq_mul]

/-- The zero-frequency coefficient is the unnormalized sum of the function. -/
theorem unnormalizedDFT_zero (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    unnormalizedDFT p f 0 = ∑ x : ZMod p, f x := by
  exact ZMod.dft_apply_zero f

/-- Orthogonality of the standard additive characters on `ZMod p`. -/
theorem sum_stdAddChar_mul (p : ℕ) [NeZero p] (a : ZMod p) :
    ∑ r : ZMod p, ZMod.stdAddChar (a * r) = if a = 0 then (p : ℂ) else 0 := by
  split_ifs with ha
  · rw [ha]
    simp only [zero_mul, AddChar.map_zero_eq_one, sum_const, card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ha)

/-- The Fourier transform at zero agrees with the ordinary finite sum. -/
theorem sum_unnormalizedDFT_zero (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    ∑ x : ZMod p, f x = unnormalizedDFT p f 0 := by
  exact (unnormalizedDFT_zero p f).symm

set_option maxHeartbeats 800000 in
/-- Bilinear Parseval identity for the unnormalized transform. -/
theorem sum_conj_unnormalizedDFT_mul (p : ℕ) [NeZero p]
    (f g : ZMod p → ℂ) :
    (∑ r : ZMod p, star (unnormalizedDFT p f r) * unnormalizedDFT p g r) =
      (p : ℂ) * ∑ x : ZMod p, star (f x) * g x := by
  have hstar (r : ZMod p) :
      star (unnormalizedDFT p f r) =
        ∑ x : ZMod p, star (ZMod.stdAddChar (-(x * r)) * f x) := by
    rw [unnormalizedDFT_apply]
    exact map_sum (starRingEnd ℂ) _ Finset.univ
  have hterm (a b r : ZMod p) :
      star (ZMod.stdAddChar (-(a * r)) * f a) *
          (ZMod.stdAddChar (-(b * r)) * g b) =
        star (f a) * g b * ZMod.stdAddChar ((a - b) * r) := by
    rw [star_mul,
      AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (a * r)]
    change star (f a) * star (star (ZMod.stdAddChar (a * r))) *
      (ZMod.stdAddChar (-(b * r)) * g b) = _
    rw [star_star]
    have hchar : ZMod.stdAddChar (a * r) *
        ZMod.stdAddChar (-(b * r)) = ZMod.stdAddChar ((a - b) * r) := by
      rw [← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    rw [← hchar]
    ring
  rw [show (∑ r : ZMod p,
      star (unnormalizedDFT p f r) * unnormalizedDFT p g r) =
      ∑ r : ZMod p, ∑ b : ZMod p, ∑ a : ZMod p,
        star (ZMod.stdAddChar (-(a * r)) * f a) *
          (ZMod.stdAddChar (-(b * r)) * g b) by
        apply sum_congr rfl
        intro r _
        rw [hstar, unnormalizedDFT_apply]
        simp only [sum_mul, mul_sum]]
  calc
    (∑ r : ZMod p, ∑ b : ZMod p, ∑ a : ZMod p,
        star (ZMod.stdAddChar (-(a * r)) * f a) *
          (ZMod.stdAddChar (-(b * r)) * g b)) =
      ∑ b : ZMod p, ∑ r : ZMod p, ∑ a : ZMod p,
        star (ZMod.stdAddChar (-(a * r)) * f a) *
          (ZMod.stdAddChar (-(b * r)) * g b) :=
      Finset.sum_comm
    _ = ∑ b : ZMod p, ∑ a : ZMod p, ∑ r : ZMod p,
        star (ZMod.stdAddChar (-(a * r)) * f a) *
          (ZMod.stdAddChar (-(b * r)) * g b) := by
      apply sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a : ZMod p, ∑ b : ZMod p, ∑ r : ZMod p,
        star (ZMod.stdAddChar (-(a * r)) * f a) *
          (ZMod.stdAddChar (-(b * r)) * g b) :=
      Finset.sum_comm
    _ = ∑ a : ZMod p, ∑ b : ZMod p,
        star (f a) * g b *
          (∑ r : ZMod p, ZMod.stdAddChar ((a - b) * r)) := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      exact hterm a b r
    _ = ∑ a : ZMod p, (p : ℂ) * (star (f a) * g a) := by
      simp_rw [sum_stdAddChar_mul]
      have hzero (a b : ZMod p) : a - b = 0 ↔ b = a :=
        sub_eq_zero.trans eq_comm
      simp_rw [hzero]
      simp only [sum_ite_eq', mem_univ, if_true, mul_ite, mul_zero]
      apply sum_congr rfl
      intro a _
      ring
    _ = (p : ℂ) * ∑ a : ZMod p, star (f a) * g a := by
      rw [mul_sum]

/-- Parseval's identity for the unnormalized DFT in squared-norm form. -/
theorem sum_sq_norm_unnormalizedDFT (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖unnormalizedDFT p f r‖ ^ 2) =
      (p : ℝ) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  have hcomplex := sum_conj_unnormalizedDFT_mul p f f
  change (∑ r : ZMod p, (starRingEnd ℂ) (unnormalizedDFT p f r) *
      unnormalizedDFT p f r) =
    (p : ℂ) * ∑ x : ZMod p, (starRingEnd ℂ) (f x) * f x at hcomplex
  have hnormSq :
      (∑ r : ZMod p, (Complex.normSq (unnormalizedDFT p f r) : ℂ)) =
        (p : ℂ) * ∑ x : ZMod p, (Complex.normSq (f x) : ℂ) := by
    simpa only [Complex.normSq_eq_conj_mul_self] using hcomplex
  have hre := congrArg Complex.re hnormSq
  simpa only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul,
    sub_zero, Complex.normSq_eq_norm_sq, sum_const_zero] using hre

/-- Multiplication by `-2` permutes the frequencies when the modulus is odd. -/
theorem sum_sq_norm_unnormalizedDFT_neg_two (p : ℕ) [NeZero p]
    (hp : Odd p) (f : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖unnormalizedDFT p f (-2 * r)‖ ^ 2) =
      ∑ r : ZMod p, ‖unnormalizedDFT p f r‖ ^ 2 := by
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime 2 hp.coprime_two_left
  let e : ZMod p ≃ ZMod p := u.mulLeft.trans (Equiv.neg (ZMod p))
  apply Fintype.sum_equiv e
  intro r
  simp only [e, u, Equiv.trans_apply, Equiv.neg_apply, Units.mulLeft_apply,
    ZMod.coe_unitOfCoprime]
  norm_num

set_option maxHeartbeats 800000 in
/-- Exact Fourier formula for the cyclic three-term-progression trilinear sum.
The factor `p⁻¹` is the only normalization, since all three transforms are
unnormalized. -/
theorem threeAPSum_eq_fourier (p : ℕ) [NeZero p] (u v w : ZMod p → ℂ) :
    threeAPSum p u v w = (p : ℂ)⁻¹ *
      ∑ r : ZMod p,
        unnormalizedDFT p u r * unnormalizedDFT p v (-2 * r) *
          unnormalizedDFT p w r := by
  have hp : (p : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne p
  have hexpand :
      (∑ r : ZMod p,
        unnormalizedDFT p u r * unnormalizedDFT p v (-2 * r) *
          unnormalizedDFT p w r) =
      ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p,
        u c * v b * w a *
          (∑ r : ZMod p, ZMod.stdAddChar ((-c + 2 * b - a) * r)) := by
    simp only [unnormalizedDFT_apply, sum_mul, mul_sum]
    rw [sum_comm]
    congr 1 with a
    rw [sum_comm]
    congr 1 with b
    rw [sum_comm]
    congr 1 with c
    apply sum_congr rfl
    intro r _
    simp only [neg_mul, mul_neg, neg_neg]
    have hchar :
        ZMod.stdAddChar (-(c * r)) * ZMod.stdAddChar (b * (2 * r)) *
            ZMod.stdAddChar (-(a * r)) =
          ZMod.stdAddChar ((-c + 2 * b - a) * r) := by
      rw [← ZMod.stdAddChar.map_add_eq_mul,
        ← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    rw [← hchar]
    ring
  rw [hexpand]
  simp_rw [sum_stdAddChar_mul]
  simp only [mul_ite, mul_zero]
  rw [← div_eq_inv_mul]
  apply (eq_div_iff hp).2
  simp only [threeAPSum]
  have hrel (a b c : ZMod p) : -c + 2 * b - a = 0 ↔ c = 2 * b - a := by
    constructor <;> intro h
    · linear_combination -h
    · rw [h]
      ring
  simp_rw [hrel]
  simp only [sum_ite_eq', mem_univ, if_true, sum_mul]
  let e : (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) :=
    { toFun := fun q => (q.1 + 2 * q.2, q.1 + q.2)
      invFun := fun q => (2 * q.2 - q.1, q.1 - q.2)
      left_inv := by
        intro q
        apply Prod.ext <;> dsimp only
        · ring
        · ring
      right_inv := by
        intro q
        apply Prod.ext <;> dsimp only
        · ring
        · ring }
  calc
    (∑ x : ZMod p, ∑ d : ZMod p,
        u x * v (x + d) * w (x + 2 * d) * (p : ℂ)) =
        ∑ q : ZMod p × ZMod p,
          u q.1 * v (q.1 + q.2) * w (q.1 + 2 * q.2) * (p : ℂ) :=
      by
        simpa only [mul_comm (2 : ZMod p)] using
          (Fintype.sum_prod_type (fun q : ZMod p × ZMod p =>
            u q.1 * v (q.1 + q.2) * w (q.1 + 2 * q.2) * (p : ℂ))).symm
    _ = ∑ q : ZMod p × ZMod p,
          u (2 * q.2 - q.1) * v q.2 * w q.1 * (p : ℂ) := by
      apply Fintype.sum_equiv e
      intro q
      rcases q with ⟨x, d⟩
      change u x * v (x + d) * w (x + 2 * d) * (p : ℂ) =
        u (2 * (x + d) - (x + 2 * d)) * v (x + d) * w (x + 2 * d) * (p : ℂ)
      congr 1
      ring
    _ = ∑ a : ZMod p, ∑ b : ZMod p,
          u (2 * b - a) * v b * w a * (p : ℂ) :=
      Fintype.sum_prod_type (fun q : ZMod p × ZMod p =>
        u (2 * q.2 - q.1) * v q.2 * w q.1 * (p : ℂ))

/-- A mixed Fourier `L∞-L1` estimate obtained from the exact trilinear
identity. This form does not require `2` to be invertible. -/
theorem norm_threeAPSum_le_of_fourier_bound (p : ℕ) [NeZero p]
    (u v w : ZMod p → ℂ) (M : ℝ)
    (hu : ∀ r : ZMod p, ‖unnormalizedDFT p u r‖ ≤ M) :
    ‖threeAPSum p u v w‖ ≤ (p : ℝ)⁻¹ *
      (M * ∑ r : ZMod p,
        ‖unnormalizedDFT p v (-2 * r)‖ * ‖unnormalizedDFT p w r‖) := by
  rw [threeAPSum_eq_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∑ r : ZMod p,
        unnormalizedDFT p u r * unnormalizedDFT p v (-2 * r) *
          unnormalizedDFT p w r‖ ≤
      ∑ r : ZMod p, ‖unnormalizedDFT p u r *
        unnormalizedDFT p v (-2 * r) * unnormalizedDFT p w r‖ :=
      norm_sum_le _ _
    _ = ∑ r : ZMod p, ‖unnormalizedDFT p u r‖ *
        (‖unnormalizedDFT p v (-2 * r)‖ *
          ‖unnormalizedDFT p w r‖) := by
      apply sum_congr rfl
      intro r _
      rw [norm_mul, norm_mul]
      ring
    _ ≤ ∑ r : ZMod p, M *
        (‖unnormalizedDFT p v (-2 * r)‖ *
          ‖unnormalizedDFT p w r‖) := by
      apply sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right (hu r) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = M * ∑ r : ZMod p,
        ‖unnormalizedDFT p v (-2 * r)‖ * ‖unnormalizedDFT p w r‖ := by
      rw [mul_sum]

/-- The mixed Fourier `L∞-L2-L2` estimate. The displayed square sums
are in frequency space; a spatial form follows after Parseval. -/
theorem norm_threeAPSum_le_sqrt_of_fourier_bound (p : ℕ) [NeZero p]
    (u v w : ZMod p → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ r : ZMod p, ‖unnormalizedDFT p u r‖ ≤ M) :
    ‖threeAPSum p u v w‖ ≤ (p : ℝ)⁻¹ * M *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p v (-2 * r)‖ ^ 2) *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) := by
  have hcs :
      (∑ r : ZMod p,
        ‖unnormalizedDFT p v (-2 * r)‖ * ‖unnormalizedDFT p w r‖) ≤
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p v (-2 * r)‖ ^ 2) *
          Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) := by
    simpa only using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod p))
        (fun r => ‖unnormalizedDFT p v (-2 * r)‖)
        (fun r => ‖unnormalizedDFT p w r‖))
  calc
    ‖threeAPSum p u v w‖ ≤ (p : ℝ)⁻¹ *
        (M * ∑ r : ZMod p,
          ‖unnormalizedDFT p v (-2 * r)‖ * ‖unnormalizedDFT p w r‖) :=
      norm_threeAPSum_le_of_fourier_bound p u v w M hu
    _ ≤ (p : ℝ)⁻¹ * (M *
        (Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p v (-2 * r)‖ ^ 2) *
          Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs hM) (by positivity)
    _ = (p : ℝ)⁻¹ * M *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p v (-2 * r)‖ ^ 2) *
          Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) := by ring

/-- Reversing a progression exchanges its two endpoint functions. -/
theorem threeAPSum_swap_ends (p : ℕ) [NeZero p] (u v w : ZMod p → ℂ) :
    threeAPSum p u v w = threeAPSum p w v u := by
  rw [threeAPSum_eq_fourier, threeAPSum_eq_fourier]
  congr 1
  apply sum_congr rfl
  intro r _
  ring

/-- The spatial `L∞-L2-L2` estimate with the Fourier bound in the first
position. Oddness is used only to permute the middle frequencies by `-2`. -/
theorem norm_threeAPSum_le_spatial_of_first_fourier_bound (p : ℕ) [NeZero p]
    (hp : Odd p) (u v w : ZMod p → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ r : ZMod p, ‖unnormalizedDFT p u r‖ ≤ M) :
    ‖threeAPSum p u v w‖ ≤
      M * Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2) := by
  have hpNat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpNat
  calc
    ‖threeAPSum p u v w‖ ≤ (p : ℝ)⁻¹ * M *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p v (-2 * r)‖ ^ 2) *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) :=
      norm_threeAPSum_le_sqrt_of_fourier_bound p u v w M hM hu
    _ = (p : ℝ)⁻¹ * M *
        Real.sqrt ((p : ℝ) * ∑ x : ZMod p, ‖v x‖ ^ 2) *
        Real.sqrt ((p : ℝ) * ∑ x : ZMod p, ‖w x‖ ^ 2) := by
      rw [sum_sq_norm_unnormalizedDFT_neg_two p hp v,
        sum_sq_norm_unnormalizedDFT p v, sum_sq_norm_unnormalizedDFT p w]
    _ = M * Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2) := by
      rw [Real.sqrt_mul hpReal.le, Real.sqrt_mul hpReal.le]
      have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
        Real.mul_self_sqrt hpReal.le
      calc
        (p : ℝ)⁻¹ * M *
            (Real.sqrt (p : ℝ) * Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2)) *
            (Real.sqrt (p : ℝ) * Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2)) =
          ((p : ℝ)⁻¹ * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ))) * M *
            Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2) *
            Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2) := by ring
        _ = _ := by rw [hsqrt, inv_mul_cancel₀ hpReal.ne']; ring

/-- The spatial `L2-L2-L∞` estimate with the Fourier bound in the last
position. Oddness is used to permute the middle frequencies by `-2`. -/
theorem norm_threeAPSum_le_spatial_of_last_fourier_bound (p : ℕ) [NeZero p]
    (hp : Odd p) (u v w : ZMod p → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ r : ZMod p, ‖unnormalizedDFT p w r‖ ≤ M) :
    ‖threeAPSum p u v w‖ ≤
      M * Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2) := by
  calc
    ‖threeAPSum p u v w‖ = ‖threeAPSum p w v u‖ := by
      rw [threeAPSum_swap_ends]
    _ ≤ M * Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2) :=
      norm_threeAPSum_le_spatial_of_first_fourier_bound p hp w v u M hM hw
    _ = M * Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖v x‖ ^ 2) := by ring

/-- The frequency `L2-L∞-L2` estimate, with the middle transform bounded. -/
theorem norm_threeAPSum_le_sqrt_of_middle_fourier_bound (p : ℕ) [NeZero p]
    (u v w : ZMod p → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ r : ZMod p, ‖unnormalizedDFT p v r‖ ≤ M) :
    ‖threeAPSum p u v w‖ ≤ (p : ℝ)⁻¹ * M *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p u r‖ ^ 2) *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) := by
  rw [threeAPSum_eq_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  rw [show (p : ℝ)⁻¹ * M *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p u r‖ ^ 2) *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) =
    (p : ℝ)⁻¹ * (M *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p u r‖ ^ 2) *
      Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∑ r : ZMod p, unnormalizedDFT p u r *
        unnormalizedDFT p v (-2 * r) * unnormalizedDFT p w r‖ ≤
      ∑ r : ZMod p, ‖unnormalizedDFT p u r‖ *
        (‖unnormalizedDFT p v (-2 * r)‖ * ‖unnormalizedDFT p w r‖) := by
      refine (norm_sum_le _ _).trans_eq ?_
      apply sum_congr rfl
      intro r _
      rw [norm_mul, norm_mul]
      ring
    _ ≤ ∑ r : ZMod p, ‖unnormalizedDFT p u r‖ *
        (M * ‖unnormalizedDFT p w r‖) := by
      apply sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hv (-2 * r)) (norm_nonneg _)) (norm_nonneg _)
    _ = M * ∑ r : ZMod p,
        ‖unnormalizedDFT p u r‖ * ‖unnormalizedDFT p w r‖ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    _ ≤ M * (Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p u r‖ ^ 2) *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      simpa only using
        (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod p))
          (fun r => ‖unnormalizedDFT p u r‖)
          (fun r => ‖unnormalizedDFT p w r‖))
    _ = M * Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p u r‖ ^ 2) *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) := by ring

/-- The spatial `L2-L∞-L2` estimate. It needs no oddness assumption because
both unbounded transforms occur at the same frequency `r`. -/
theorem norm_threeAPSum_le_spatial_of_middle_fourier_bound (p : ℕ) [NeZero p]
    (u v w : ZMod p → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ r : ZMod p, ‖unnormalizedDFT p v r‖ ≤ M) :
    ‖threeAPSum p u v w‖ ≤
      M * Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2) := by
  have hpNat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpNat
  calc
    ‖threeAPSum p u v w‖ ≤ (p : ℝ)⁻¹ * M *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p u r‖ ^ 2) *
        Real.sqrt (∑ r : ZMod p, ‖unnormalizedDFT p w r‖ ^ 2) :=
      norm_threeAPSum_le_sqrt_of_middle_fourier_bound p u v w M hM hv
    _ = (p : ℝ)⁻¹ * M *
        Real.sqrt ((p : ℝ) * ∑ x : ZMod p, ‖u x‖ ^ 2) *
        Real.sqrt ((p : ℝ) * ∑ x : ZMod p, ‖w x‖ ^ 2) := by
      rw [sum_sq_norm_unnormalizedDFT p u, sum_sq_norm_unnormalizedDFT p w]
    _ = M * Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2) := by
      rw [Real.sqrt_mul hpReal.le, Real.sqrt_mul hpReal.le]
      have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
        Real.mul_self_sqrt hpReal.le
      calc
        (p : ℝ)⁻¹ * M *
            (Real.sqrt (p : ℝ) * Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2)) *
            (Real.sqrt (p : ℝ) * Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2)) =
          ((p : ℝ)⁻¹ * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ))) * M *
            Real.sqrt (∑ x : ZMod p, ‖u x‖ ^ 2) *
            Real.sqrt (∑ x : ZMod p, ‖w x‖ ^ 2) := by ring
        _ = _ := by rw [hsqrt, inv_mul_cancel₀ hpReal.ne']; ring

/-- The exact three-term telescoping identity for two trilinear AP sums. -/
theorem threeAPSum_sub_threeAPSum (p : ℕ) [NeZero p]
    (u v w u' v' w' : ZMod p → ℂ) :
    threeAPSum p u v w - threeAPSum p u' v' w' =
      threeAPSum p (u - u') v w + threeAPSum p u' (v - v') w +
        threeAPSum p u' v' (w - w') := by
  simp only [threeAPSum, Pi.sub_apply, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro d _
  ring

/-- Ground truth: on `ZMod 3`, three constant-one functions count all nine
ordered pairs `(x,d)`. -/
example : threeAPSum 3 (fun _ => 1) (fun _ => 1) (fun _ => 1) = 9 := by
  simp only [threeAPSum, mul_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  norm_num

/-- Ground truth for the unnormalized convention: the constant-one function
on `ZMod 3` has zero-frequency coefficient three. -/
example : unnormalizedDFT 3 (fun _ => 1) 0 = 3 := by
  rw [unnormalizedDFT_zero]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  norm_num

#check @unnormalizedDFT
#check @threeAPSum
#check @threeAPSum_eq_fourier
#check @sum_unnormalizedDFT_zero
#check @sum_conj_unnormalizedDFT_mul
#check @sum_sq_norm_unnormalizedDFT
#check @sum_sq_norm_unnormalizedDFT_neg_two
#check @norm_threeAPSum_le_of_fourier_bound
#check @norm_threeAPSum_le_sqrt_of_fourier_bound
#check @norm_threeAPSum_le_spatial_of_first_fourier_bound
#check @norm_threeAPSum_le_spatial_of_middle_fourier_bound
#check @norm_threeAPSum_le_spatial_of_last_fourier_bound
#check @threeAPSum_sub_threeAPSum

#print axioms sum_unnormalizedDFT_zero
#print axioms sum_conj_unnormalizedDFT_mul
#print axioms sum_sq_norm_unnormalizedDFT
#print axioms sum_sq_norm_unnormalizedDFT_neg_two
#print axioms threeAPSum_eq_fourier
#print axioms norm_threeAPSum_le_of_fourier_bound
#print axioms norm_threeAPSum_le_sqrt_of_fourier_bound
#print axioms norm_threeAPSum_le_spatial_of_first_fourier_bound
#print axioms norm_threeAPSum_le_spatial_of_middle_fourier_bound
#print axioms norm_threeAPSum_le_spatial_of_last_fourier_bound
#print axioms threeAPSum_sub_threeAPSum

end Erdos142
