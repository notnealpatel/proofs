/-
  Erdős Problem #142 — leading constant and census-decay logarithm estimates.

  This module isolates the *scalar* asymptotics that an eventual EHPS-shaped
  lower bound consumes, on top of `TorusAsymptoticParameters`:

  * `torusLeadingConstant = 2·√(log(24/7))` is the leading constant of the
    boundary layer of the torus-radius asymptotics;
  * `torusEta δ = torusLeadingConstant·δ/4 + δ²/16` is the quadratic loss
    accumulated by a `δ`-defect.  For `δ > 0` it is positive, and for
    `0 < δ ≤ 1` it is at most `1` (so it is a *sub-unit* perturbation);
  * the exact square-completion identity
    `2·√(log(24/7) + torusEta δ) = torusLeadingConstant + δ/2` for `δ > 0`;
  * `census_log_bounds` controls the logarithm of the reciprocal census slack
    `1/b(e,q)` between the two explicit thresholds `1` and `log(24/7) + η`.

  Every declaration is proved from Mathlib primitives; there is no `sorry`, no
  new axiom, and no `unsafe`.
-/

import Erdos.Erdos142.TorusAsymptoticParameters

set_option autoImplicit false

namespace Erdos142

/-- The leading constant `2·√(log(24/7))` of the torus-radius asymptotics.
It is the factor multiplying the defect scale in the square-completion
identity `2·√(log(24/7) + torusEta δ) = torusLeadingConstant + δ/2`. -/
noncomputable def torusLeadingConstant : ℝ := 2 * Real.sqrt (Real.log (24 / 7))

/-- The quadratic loss `torusEta δ = torusLeadingConstant·δ/4 + δ²/16`
accumulated by a `δ`-defect in the torus-radius asymptotics. -/
noncomputable def torusEta (δ : ℝ) : ℝ := torusLeadingConstant * δ / 4 + δ ^ 2 / 16

/-- **Positivity of the leading constant.**  `24/7 > 1` gives `log(24/7) > 0`,
so its square root and twice it are positive. -/
lemma torusLeadingConstant_pos : 0 < torusLeadingConstant := by
  have hlog : 0 < Real.log (24 / 7) := Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt (Real.log (24 / 7)) := Real.sqrt_pos.mpr hlog
  rw [torusLeadingConstant]
  linarith

/-- **Square of the leading constant.**  `(2·√x)² = 4x` for `x = log(24/7)`. -/
lemma torusLeadingConstant_sq : torusLeadingConstant ^ 2 = 4 * Real.log (24 / 7) := by
  have hx0 : 0 ≤ Real.log (24 / 7) := Real.log_nonneg (by norm_num)
  rw [torusLeadingConstant, mul_pow, Real.sq_sqrt hx0]
  norm_num

/-- **Crude upper bound on the leading constant.**  `log(24/7) ≤ 17/7 ≤ 225/64`
(via `log x ≤ x - 1`), so `√(log(24/7)) ≤ 15/8` and
`torusLeadingConstant ≤ 15/4`. -/
lemma torusLeadingConstant_le : torusLeadingConstant ≤ 15 / 4 := by
  have hxle : Real.log (24 / 7) ≤ 225 / 64 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 24 / 7 by norm_num)
    have h2 : (24 : ℝ) / 7 - 1 = 17 / 7 := by norm_num
    have h3 : (17 : ℝ) / 7 ≤ 225 / 64 := by norm_num
    linarith
  have hs : Real.sqrt (Real.log (24 / 7)) ≤ 15 / 8 := by
    have h4 := Real.sqrt_le_sqrt hxle
    have h5 : Real.sqrt (225 / 64) = 15 / 8 := by
      rw [show (225 : ℝ) / 64 = (15 / 8) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 15 / 8)]
    linarith
  rw [torusLeadingConstant]
  linarith

/-- **Positivity of the quadratic loss.**  For `δ > 0`, the linear term
`torusLeadingConstant·δ/4` is already positive. -/
lemma torusEta_pos {δ : ℝ} (hδ : 0 < δ) : 0 < torusEta δ := by
  have hc : 0 < torusLeadingConstant := torusLeadingConstant_pos
  have h1 : 0 < torusLeadingConstant * δ / 4 := by positivity
  have h2 : 0 ≤ δ ^ 2 / 16 := by positivity
  rw [torusEta]
  linarith

/-- **Sub-unity bound on the quadratic loss.**  For `0 < δ ≤ 1`,
`torusLeadingConstant·δ/4 ≤ (15/4)/4 = 15/16` and `δ²/16 ≤ 1/16`, hence
`torusEta δ ≤ 1`. -/
lemma torusEta_le_one {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : torusEta δ ≤ 1 := by
  have hc0 : 0 ≤ torusLeadingConstant := torusLeadingConstant_pos.le
  have hcle : torusLeadingConstant ≤ 15 / 4 := torusLeadingConstant_le
  have h1 : torusLeadingConstant * δ / 4 ≤ 15 / 16 := by nlinarith
  have h2 : δ ^ 2 / 16 ≤ 1 / 16 := by nlinarith
  rw [torusEta]
  linarith

/-- **Square-completion identity.**  For `δ > 0`,
`2·√(log(24/7) + torusEta δ) = torusLeadingConstant + δ/2`.

Indeed `log(24/7) = torusLeadingConstant²/4`, so
`log(24/7) + torusEta δ = (torusLeadingConstant/2 + δ/4)²`, and the bracket is
nonnegative, so taking square roots gives the claim. -/
theorem two_mul_sqrt_log_add_torusEta {δ : ℝ} (hδ : 0 < δ) :
    2 * Real.sqrt (Real.log (24 / 7) + torusEta δ) = torusLeadingConstant + δ / 2 := by
  have hcsq : torusLeadingConstant ^ 2 = 4 * Real.log (24 / 7) := torusLeadingConstant_sq
  have hnonneg : 0 ≤ torusLeadingConstant / 2 + δ / 4 := by
    have := torusLeadingConstant_pos
    positivity
  have hsq : Real.log (24 / 7) + torusEta δ = (torusLeadingConstant / 2 + δ / 4) ^ 2 := by
    rw [torusEta]
    rw [show Real.log (24 / 7) = torusLeadingConstant ^ 2 / 4 by linarith]
    ring
  rw [hsq, Real.sqrt_sq hnonneg]
  ring

/-- **Census density lower bound.**  For `e ≥ 6`,
`rho e ≥ rho 6 = 2/9`, via the algebraic identity
`rho e - 2/9 = (e-6)(5e-6)/(72e²) ≥ 0`. -/
lemma rho_ge_two_ninths {e : ℝ} (he : 6 ≤ e) : (2 : ℝ) / 9 ≤ rho e := by
  have he0 : 0 < e := by linarith
  have hkey : rho e - 2 / 9 = (e - 6) * (5 * e - 6) / (72 * e ^ 2) := by
    rw [rho]
    field_simp
    ring
  have hnonneg : 0 ≤ (e - 6) * (5 * e - 6) / (72 * e ^ 2) := by
    apply div_nonneg
    · nlinarith
    · positivity
  linarith

/-- **Census density upper bound.**  For `e ≥ 1`,
`rho e ≤ 7/24`, since `7/24 - rho e = e⁻¹(1 - e⁻¹)/2 ≥ 0`. -/
lemma rho_le_seven_twentyfourths {e : ℝ} (he : 1 ≤ e) : rho e ≤ 7 / 24 := by
  have he0 : 0 < e := by linarith
  have hinv1 : e⁻¹ ≤ 1 := inv_le_one_of_one_le₀ he
  have hinv0 : 0 < e⁻¹ := inv_pos.mpr he0
  have hkey : 7 / 24 - rho e = e⁻¹ * (1 - e⁻¹) / 2 := by
    rw [rho]
    field_simp
    ring
  have hnonneg : 0 ≤ e⁻¹ * (1 - e⁻¹) / 2 := by
    apply div_nonneg
    · nlinarith
    · norm_num
  linarith

/-- **Positivity of the census density.**  Immediate from `rho e ≥ 2/9`. -/
lemma rho_pos {e : ℝ} (he : 6 ≤ e) : 0 < rho e := by
  have h := rho_ge_two_ninths he
  linarith

/-- **Reciprocal census density bound.**  For `e ≥ 6`,
`1/rho e ≤ (24/7)·(1 + 9/(4e))`.

Multiplying by `rho e > 0`, the claim is
`1 ≤ (24/7)·(1 + 9/(4e))·rho e`, whose difference from `1` equals the strictly
positive rational expression `(15e² - 60e + 108)/(28e³)`
(`= (15(e-2)² + 48)/(28e³)`). -/
lemma inv_rho_le_mul {e : ℝ} (he : 6 ≤ e) :
    1 / rho e ≤ (24 / 7) * (1 + 9 / (4 * e)) := by
  have he0 : 0 < e := by linarith
  have hrho : 0 < rho e := rho_pos he
  rw [div_le_iff₀ hrho]
  have hident : (24 / 7) * (1 + 9 / (4 * e)) * rho e - 1 =
      (15 * e ^ 2 - 60 * e + 108) / (28 * e ^ 3) := by
    rw [rho]
    field_simp
    ring
  have hpos : 0 < (15 * e ^ 2 - 60 * e + 108) / (28 * e ^ 3) := by
    apply div_pos
    · nlinarith [sq_nonneg (e - 2)]
    · positivity
  linarith

/-- **Census-decay logarithm bounds.**  Let `0 < η ≤ 1`, `6 ≤ e`, `18/η ≤ e`,
and let naturals `N < q` satisfy `58/η ≤ N`.  Then the census slack
`b(e,q) = rho(e) - 3/q` satisfies

* `0 < b(e,q)`;
* `1 ≤ log (1 / b(e,q))`;
* `log (1 / b(e,q)) ≤ log(24/7) + η`.

Writing `b(e,q) = rho(e)·(1 - x)` with `x = 3/(rho(e)·q)`, we have
`x ≤ 27/(2q) < 1/2`, and the estimates
`1/rho ≤ (24/7)(1 + 9/(4e))`, `log(1/(1-x)) ≤ 2x` give
`log(1/b) ≤ log(24/7) + 9/(4e) + 2x ≤ log(24/7) + η`,
using `9/(4e) ≤ η/8` (from `18/η ≤ e`) and `2x < 27η/58` (from `58/η < q`).
The lower bound uses `b < 7/24`, whence `1/b > 24/7 > 3 > exp 1`. -/
theorem census_log_bounds {e η : ℝ} {q N : ℕ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (he6 : 6 ≤ e) (he18 : 18 / η ≤ e)
    (hNq : N < q) (hN58 : 58 / η ≤ (N : ℝ)) :
    0 < b e q ∧ 1 ≤ Real.log (1 / b e q) ∧
      Real.log (1 / b e q) ≤ Real.log (24 / 7) + η := by
  have he0 : 0 < e := by
    have : 0 < 18 / η := by positivity
    linarith
  have hrho0 : 0 < rho e := rho_pos he6
  have hrho2n9 : (2 : ℝ) / 9 ≤ rho e := rho_ge_two_ninths he6
  have hNq' : (N : ℝ) < (q : ℝ) := by exact_mod_cast hNq
  have h58le : (58 : ℝ) ≤ 58 / η := by
    rw [le_div_iff₀ hη0]
    linarith
  have hNge58 : (58 : ℝ) ≤ (N : ℝ) := le_trans h58le hN58
  have hq58 : (58 : ℝ) < (q : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set x : ℝ := 3 / (rho e * (q : ℝ)) with hx_def
  have hx0 : 0 < x := by
    rw [hx_def]
    positivity
  have hx_le : x ≤ 27 / (2 * (q : ℝ)) := by
    rw [hx_def]
    have hb0 : 0 < (2 / 9) * (q : ℝ) := by positivity
    have hbc : (2 / 9) * (q : ℝ) ≤ rho e * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hrho2n9 hqpos.le
    have h1 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 3 by norm_num) hb0 hbc
    have h2 : 3 / ((2 / 9) * (q : ℝ)) = 27 / (2 * (q : ℝ)) := by
      field_simp
      ring
    rwa [h2] at h1
  have hx_lt_half : x < 1 / 2 := by
    have h1 : 27 / (2 * (q : ℝ)) < 27 / 116 := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))
        (by norm_num : (0 : ℝ) < 116)]
      nlinarith [hq58]
    have h2 : (27 : ℝ) / 116 < 1 / 2 := by norm_num
    linarith [hx_le, h1, h2]
  have h1mx_pos : 0 < 1 - x := by linarith
  have hb_eq : b e q = rho e * (1 - x) := by
    rw [b, hx_def]
    field_simp [ne_of_gt hrho0, ne_of_gt hqpos]
  have hbpos : 0 < b e q := by
    rw [hb_eq]
    exact mul_pos hrho0 h1mx_pos
  have hinv : 1 / (b e q) = (1 / rho e) * (1 / (1 - x)) := by
    rw [hb_eq]
    field_simp [ne_of_gt hrho0, ne_of_gt h1mx_pos]
  have hloginv : Real.log (1 / (b e q)) =
      Real.log (1 / rho e) + Real.log (1 / (1 - x)) := by
    have hp1 : 0 < 1 / rho e := div_pos one_pos hrho0
    have hp2 : 0 < 1 / (1 - x) := div_pos one_pos h1mx_pos
    rw [hinv, Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2)]
  -- upper bound on `log (1/rho)`
  have hA : Real.log (1 / rho e) ≤ Real.log (24 / 7) + 9 / (4 * e) := by
    have hle := inv_rho_le_mul he6
    have hp1 : 0 < 1 / rho e := div_pos one_pos hrho0
    have hp2 : 0 < 1 + 9 / (4 * e) := by positivity
    have hlog := Real.log_le_log hp1 hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hp2)] at hlog
    have hsub : Real.log (1 + 9 / (4 * e)) ≤ 9 / (4 * e) := by
      have := Real.log_le_sub_one_of_pos hp2
      linarith
    linarith
  -- upper bound on `log (1/(1-x))`
  have hB : Real.log (1 / (1 - x)) ≤ 2 * x := by
    have h3 := Real.log_le_sub_one_of_pos (div_pos one_pos h1mx_pos)
    have h4 : 1 / (1 - x) - 1 ≤ 2 * x := by
      have h5 : x / (1 - x) ≤ 2 * x := by
        rw [div_le_iff₀ h1mx_pos]
        nlinarith [hx0, hx_lt_half.le]
      have h6 : 1 / (1 - x) - 1 = x / (1 - x) := by
        field_simp
        ring
      linarith [h5, h6]
    linarith [h3, h4]
  -- the two parameter estimates
  have hsum : 9 / (4 * e) + 2 * x ≤ η := by
    have he_bd : 9 / (4 * e) ≤ η / 8 := by
      have h1 : 1 / e ≤ η / 18 := by
        have h := one_div_le_one_div_of_le (show (0 : ℝ) < 18 / η by positivity) he18
        have h2 : (1 : ℝ) / (18 / η) = η / 18 := by
          field_simp
        rwa [h2] at h
      have h2 : 9 / (4 * e) = (9 / 4) * (1 / e) := by ring
      rw [h2]
      have h3 : (9 / 4) * (1 / e) ≤ (9 / 4) * (η / 18) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h4 : (9 / 4) * (η / 18) = η / 8 := by ring
      linarith [h3, h4.le]
    have hx_bd : 2 * x < 27 * η / 58 := by
      have hqinv : 1 / (q : ℝ) < η / 58 := by
        have h58ltq : 58 / η < (q : ℝ) := by linarith
        have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 58 / η by positivity) h58ltq
        have h2 : (1 : ℝ) / (58 / η) = η / 58 := by
          field_simp
        rwa [h2] at h
      have h2x : 2 * x ≤ 27 / (q : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hx_le (show (0 : ℝ) ≤ 2 by norm_num)
        have h2 : 2 * (27 / (2 * (q : ℝ))) = 27 / (q : ℝ) := by
          field_simp
        linarith [h, h2.le]
      have h3 : 27 / (q : ℝ) < 27 * η / 58 := by
        have h4 : 27 / (q : ℝ) = 27 * (1 / (q : ℝ)) := by ring
        rw [h4]
        have h := mul_lt_mul_of_pos_left hqinv (show (0 : ℝ) < 27 by norm_num)
        have h5 : 27 * (η / 58) = 27 * η / 58 := by ring
        linarith [h, h5.le]
      linarith [h2x, h3]
    have htot : 9 / (4 * e) + 2 * x < η / 8 + 27 * η / 58 :=
      add_lt_add_of_le_of_lt he_bd hx_bd
    have hfin : η / 8 + 27 * η / 58 ≤ η := by nlinarith [hη0]
    linarith [htot, hfin]
  refine ⟨hbpos, ?_, ?_⟩
  · -- `1 ≤ log (1 / b)`
    have hb_lt : b e q < 7 / 24 := by
      have hrho_le : rho e ≤ 7 / 24 := rho_le_seven_twentyfourths (by linarith)
      have hpos3 : 0 < 3 / (q : ℝ) := by positivity
      rw [b]
      linarith
    have hinvlt : (24 : ℝ) / 7 < 1 / (b e q) := by
      have h := one_div_lt_one_div_of_lt hbpos hb_lt
      have h1 : (1 : ℝ) / (7 / 24) = 24 / 7 := by norm_num
      linarith [h, h1.le]
    have hexp : Real.exp 1 < 1 / (b e q) := by
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      have h4 : (3 : ℝ) < 24 / 7 := by norm_num
      linarith [h3, h4, hinvlt]
    have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at hlog
    linarith
  · calc Real.log (1 / (b e q)) = Real.log (1 / rho e) + Real.log (1 / (1 - x)) := hloginv
      _ ≤ (Real.log (24 / 7) + 9 / (4 * e)) + 2 * x := add_le_add hA hB
      _ ≤ Real.log (24 / 7) + η := by linarith [hsum]

-- Ground-truth checks.

/-- The leading constant is strictly positive. -/
example : 0 < torusLeadingConstant := torusLeadingConstant_pos

/-- The quadratic loss is positive at `δ = 1`. -/
example : 0 < torusEta 1 := torusEta_pos (by norm_num)

/-- The quadratic loss is at most `1` on `0 < δ ≤ 1`; the endpoint `δ = 1` is a
concrete check of the uniform bound. -/
example : torusEta 1 ≤ 1 := torusEta_le_one (by norm_num) (by norm_num)

/-- The square-completion identity at `δ = 1`. -/
example : 2 * Real.sqrt (Real.log (24 / 7) + torusEta 1) = torusLeadingConstant + 1 / 2 :=
  two_mul_sqrt_log_add_torusEta (by norm_num)

/-- Non-vacuity of `census_log_bounds`: `η = 1`, `e = 18`, `N = 64`, `q = 65`
satisfy every hypothesis jointly, so the three conclusions hold at an explicit
instance. -/
example : 0 < b 18 65 ∧ 1 ≤ Real.log (1 / b 18 65) ∧
    Real.log (1 / b 18 65) ≤ Real.log (24 / 7) + 1 :=
  census_log_bounds (η := 1) (e := 18) (q := 65) (N := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms torusLeadingConstant_pos
#print axioms torusLeadingConstant_sq
#print axioms torusLeadingConstant_le
#print axioms torusEta_pos
#print axioms torusEta_le_one
#print axioms two_mul_sqrt_log_add_torusEta
#print axioms rho_ge_two_ninths
#print axioms rho_le_seven_twentyfourths
#print axioms rho_pos
#print axioms inv_rho_le_mul
#print axioms census_log_bounds

end Erdos142