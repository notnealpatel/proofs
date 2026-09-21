/-
  Erdős Problem #142 — the sharpened finite-epsilon torus building block.

  This module is a parallel, additive companion to
  `Erdos.Erdos142.TorusBuildingBlock`.  It imports that module and leaves every
  definition and theorem there unchanged: in particular the accepted `9/5`
  weight chain, `torusF_threeAP`, and the coefficient-41 results that consume
  it are neither redefined nor touched.  Only a second weight and its
  polynomial kernels are added here.

  The improvement recorded is the coefficient pair `A = 69/8`, `B = 37/8`.
  Its two arithmetic certificates are

  * `A - B = 4`, which makes the far kernel tight (`A/2 = 2 + B/2`), and
  * `A * B - 4 * A - 2 * B + 4 = 9/64 > 0`, the numerator of four times the
    determinant of the close-branch endpoint quadratic.

  The geometry (`torusT`, `torusSum`, `torusG`, `torusT_coordinate_bounds`,
  `torusT_sum_bounds`, `torusG_bounds`, `torusG_ge_shift_sq`,
  `torus_endpoint_sum_large_of_first_sum_lt_one`, `torus_first_sum_ge_one_of_close`,
  `integer_wrap_cases`, `torus_wrap_sum_zero_or_one`,
  `torusG_eq_midpoint_of_integer_wrap`, `torusG_close_gap`,
  `unit_square_endpoint_distance_lt_two`) is reused verbatim from
  `TorusBuildingBlock`; only the weight and its polynomial kernels are new.
-/

import Erdos.Erdos142.TorusBuildingBlock

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- The sharpened finite-epsilon quadratic weight, with coefficients `69/8` and
`37/8`.  Its geometry is the unchanged `torusT` of `TorusBuildingBlock`. -/
noncomputable def torusFSharp (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (69 / 8) / ε ^ 2 * torusSum p ^ 2 + (37 / 8) * torusG p.1

/-- Ground truth for the sharpened weight at a branch-boundary point. -/
example : torusFSharp 1 ((1 / 2 : ℝ), 1 / 4) = 621 / 128 := by
  norm_num [torusFSharp, torusSum, torusG]

/-- Ground truth for the sharpened weight at a lattice point with `ε = 1`. -/
example : torusFSharp 1 ((0 : ℝ), 0) = 0 := by
  norm_num [torusFSharp, torusSum, torusG]

/-- The first arithmetic certificate: `A - B = 4` for `A = 69/8`, `B = 37/8`.
This is exactly the identity that makes the far polynomial kernel tight. -/
theorem torusSharp_coefficient_gap :
    (69 / 8 : ℝ) - 37 / 8 = 4 := by
  norm_num

/-- The second arithmetic certificate: `A * B - 4 * A - 2 * B + 4 = 9/64 > 0`
for `A = 69/8`, `B = 37/8`.  This is the numerator of four times the
determinant of the close-branch endpoint quadratic, so its positivity is the
positive-definiteness certificate for the close kernel. -/
theorem torusSharp_close_determinant :
    (69 / 8 : ℝ) * (37 / 8) - 4 * (69 / 8) - 2 * (37 / 8) + 4 = 9 / 64 := by
  norm_num

/-- Positivity of the close-branch determinant certificate. -/
theorem torusSharp_close_determinant_pos :
    0 < (69 / 8 : ℝ) * (37 / 8) - 4 * (69 / 8) - 2 * (37 / 8) + 4 := by
  rw [torusSharp_close_determinant]
  norm_num

/-- The coefficient-`69/8`/`37/8` far-branch polynomial kernel.  Its hypotheses
are exactly those of `torus_far_polynomial_kernel`, so it is the sharp analogue
of that lemma.  The proof is tight: `A/2 = 2 + B/2` is the certificate
`A - B = 4`. -/
theorem torusSharp_far_polynomial_kernel {ε sx sy sz gx gy gz u v : ℝ}
    (hε : 0 < ε)
    (hgap : ε ^ 2 / 2 ≤ sx ^ 2 + sz ^ 2 - 2 * sy ^ 2)
    (hgx : 0 ≤ gx) (hgz : 0 ≤ gz) (hgy : gy ≤ 1 / 4)
    (hdist : u ^ 2 + v ^ 2 < 2) :
    2 * ((69 / 8) / ε ^ 2 * sy ^ 2 + (37 / 8) * gy) + u ^ 2 + v ^ 2 ≤
      ((69 / 8) / ε ^ 2 * sx ^ 2 + (37 / 8) * gx) +
        ((69 / 8) / ε ^ 2 * sz ^ 2 + (37 / 8) * gz) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcoef : 0 ≤ (69 / 8) / ε ^ 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hgap hcoef
  have hcancel : ((69 / 8) / ε ^ 2) * (ε ^ 2 / 2) = (69 / 16 : ℝ) := by
    field_simp
    ring
  rw [hcancel] at hprod
  nlinarith

/-- Positive semidefiniteness of the close-branch endpoint quadratic for the
sharpened coefficients.  The explicit form is
`u^2 + v^2 ≤ (69/16) * (u+v)^2 + (37/16) * u^2`, i.e. the kernel with `A/2`,
`B/2` substituted; the identity `90 * (90*u^2 + 138*u*v + 53*v^2) =
(90*u + 69*v)^2 + 9*v^2` witnesses it, with `9 = AB - 4A - 2B + 4` up to the
factor four recorded in `torusSharp_close_determinant`. -/
theorem torusSharp_close_psd (u v : ℝ) :
    u ^ 2 + v ^ 2 ≤ 69 / 16 * (u + v) ^ 2 + 37 / 16 * u ^ 2 := by
  nlinarith [sq_nonneg (90 * u + 69 * v), sq_nonneg v]

/-- The coefficient-`69/8`/`37/8` close-branch polynomial kernel.  Its
hypotheses are exactly those of `torus_close_polynomial_kernel`, so it is the
sharp analogue of that lemma. -/
theorem torusSharp_close_polynomial_kernel {ε sx sy sz gx gy gz u v : ℝ}
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hsum : sx ^ 2 + sz ^ 2 - 2 * sy ^ 2 = (u + v) ^ 2 / 2)
    (hgap : u ^ 2 / 2 ≤ gx + gz - 2 * gy) :
    2 * ((69 / 8) / ε ^ 2 * sy ^ 2 + (37 / 8) * gy) + u ^ 2 + v ^ 2 ≤
      ((69 / 8) / ε ^ 2 * sx ^ 2 + (37 / 8) * gx) +
        ((69 / 8) / ε ^ 2 * sz ^ 2 + (37 / 8) * gz) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hεsqle : ε ^ 2 ≤ 1 := by nlinarith
  have hcoeff : (69 / 8 : ℝ) ≤ (69 / 8) / ε ^ 2 := by
    apply (le_div_iff₀ hεsq).2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u + v))
  have hpsd := torusSharp_close_psd u v
  nlinarith

/-- The sharpened finite-epsilon torus set with weight coefficients `69/8` and
`37/8` satisfies the required three-term-progression energy inequality.  This
is the exact analogue of `torusF_threeAP` on the unchanged `torusT` geometry. -/
theorem torusFSharp_threeAP {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {x y z : ℝ × ℝ} {w₁ w₂ : ℤ}
    (hx : torusT ε x) (hy : torusT ε y) (hz : torusT ε z)
    (hwrap₁ : x.1 + z.1 - 2 * y.1 = (w₁ : ℝ))
    (hwrap₂ : x.2 + z.2 - 2 * y.2 = (w₂ : ℝ)) :
    2 * torusFSharp ε y + (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2 ≤
      torusFSharp ε x + torusFSharp ε z := by
  have hwrapsum := torus_wrap_sum_zero_or_one hε hεle hx hy hz hwrap₁ hwrap₂
  have hsumEq :
      torusSum x + torusSum z - 2 * torusSum y = ((w₁ + w₂ : ℤ) : ℝ) := by
    rw [Int.cast_add]
    simp only [torusSum]
    linarith
  by_cases hclose : |torusSum x - torusSum z| < ε
  · rcases hwrapsum with hzero | hone
    · have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = 0 := by norm_num [hzero]
      rw [hcast] at hsumEq
      have hsumMid : torusSum y = (torusSum x + torusSum z) / 2 := by
        linarith
      have hsumGap :
          torusSum x ^ 2 + torusSum z ^ 2 - 2 * torusSum y ^ 2 =
            ((x.1 - z.1) + (x.2 - z.2)) ^ 2 / 2 := by
        rw [hsumMid]
        simp only [torusSum]
        ring
      have hgGap := torusG_close_gap hε hx hy hz hwrap₁ hclose
      have hεone : ε ≤ 1 := hεle.trans (by norm_num)
      exact torusSharp_close_polynomial_kernel hε hεone hsumGap hgGap
    · have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = 1 := by norm_num [hone]
      rw [hcast] at hsumEq
      have hsumGap :
          ε ^ 2 / 2 ≤ torusSum x ^ 2 + torusSum z ^ 2 -
            2 * torusSum y ^ 2 := by
        have hysum := (torusT_sum_bounds hε hy).1
        have hεsq : ε ^ 2 ≤ 1 := by nlinarith
        have hsq : 0 ≤ (torusSum x - torusSum z) ^ 2 := sq_nonneg _
        nlinarith
      have hxb := torusT_coordinate_bounds hx
      have hzb := torusT_coordinate_bounds hz
      have hgx := (torusG_bounds hxb.1 hxb.2.1).1
      have hgz := (torusG_bounds hzb.1 hzb.2.1).1
      have hyb := torusT_coordinate_bounds hy
      have hgy := (torusG_bounds hyb.1 hyb.2.1).2
      have hdist := unit_square_endpoint_distance_lt_two hxb hzb
      exact torusSharp_far_polynomial_kernel hε hsumGap hgx hgz hgy hdist
  · have hfar : ε ≤ |torusSum x - torusSum z| := le_of_not_gt hclose
    have hdiffsq : ε ^ 2 ≤ (torusSum x - torusSum z) ^ 2 := by
      have habsSq : ε ^ 2 ≤ |torusSum x - torusSum z| ^ 2 :=
        (sq_le_sq₀ hε.le (abs_nonneg _)).2 hfar
      simpa only [sq_abs] using habsSq
    rcases hwrapsum with hzero | hone
    · have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = 0 := by norm_num [hzero]
      rw [hcast] at hsumEq
      have hsumGap :
          ε ^ 2 / 2 ≤ torusSum x ^ 2 + torusSum z ^ 2 -
            2 * torusSum y ^ 2 := by
        have hsumMid : torusSum y = (torusSum x + torusSum z) / 2 := by
          linarith
        rw [hsumMid]
        nlinarith
      have hxb := torusT_coordinate_bounds hx
      have hzb := torusT_coordinate_bounds hz
      have hgx := (torusG_bounds hxb.1 hxb.2.1).1
      have hgz := (torusG_bounds hzb.1 hzb.2.1).1
      have hyb := torusT_coordinate_bounds hy
      have hgy := (torusG_bounds hyb.1 hyb.2.1).2
      have hdist := unit_square_endpoint_distance_lt_two hxb hzb
      exact torusSharp_far_polynomial_kernel hε hsumGap hgx hgz hgy hdist
    · have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = 1 := by norm_num [hone]
      rw [hcast] at hsumEq
      have hsumGap :
          ε ^ 2 / 2 ≤ torusSum x ^ 2 + torusSum z ^ 2 -
            2 * torusSum y ^ 2 := by
        have hysum := (torusT_sum_bounds hε hy).1
        have hεsq : ε ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (torusSum x - torusSum z)]
      have hxb := torusT_coordinate_bounds hx
      have hzb := torusT_coordinate_bounds hz
      have hgx := (torusG_bounds hxb.1 hxb.2.1).1
      have hgz := (torusG_bounds hzb.1 hzb.2.1).1
      have hyb := torusT_coordinate_bounds hy
      have hgy := (torusG_bounds hyb.1 hyb.2.1).2
      have hdist := unit_square_endpoint_distance_lt_two hxb hzb
      exact torusSharp_far_polynomial_kernel hε hsumGap hgx hgz hgy hdist

/-- Membership-dependent nonnegativity of the sharpened weight.  A point of
`torusT ε` has `torusSum p > 2/3 > 0` and `torusG p.1 ≥ 0`, so both terms are
nonnegative. -/
theorem torusFSharp_nonneg {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {p : ℝ × ℝ} (hp : torusT ε p) :
    0 ≤ torusFSharp ε p := by
  have hb := torusT_coordinate_bounds hp
  have hgnn := (torusG_bounds hb.1 hb.2.1).1
  have hsumLower := (torusT_sum_bounds hε hp).1
  have hsumnn : 0 ≤ torusSum p := by linarith
  have hcoef : 0 ≤ (69 / 8) / ε ^ 2 := by positivity
  have h1 : 0 ≤ (69 / 8) / ε ^ 2 * torusSum p ^ 2 :=
    mul_nonneg hcoef (sq_nonneg _)
  have h2 : 0 ≤ (37 / 8) * torusG p.1 := by positivity
  simp only [torusFSharp]
  linarith

/-- Membership-dependent strict positivity of the sharpened weight on `torusT ε`:
the sum coordinate exceeds `2/3` while the coefficient is positive. -/
theorem torusFSharp_pos {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {p : ℝ × ℝ} (hp : torusT ε p) :
    0 < torusFSharp ε p := by
  have hb := torusT_coordinate_bounds hp
  have hgnn := (torusG_bounds hb.1 hb.2.1).1
  have hsumLower := (torusT_sum_bounds hε hp).1
  have hsumPos : 0 < torusSum p := by linarith
  have hcoef : 0 < (69 / 8) / ε ^ 2 := by positivity
  have h1 : 0 < (69 / 8) / ε ^ 2 * torusSum p ^ 2 :=
    mul_pos hcoef (pow_pos hsumPos 2)
  have h2 : 0 ≤ (37 / 8) * torusG p.1 := by positivity
  simp only [torusFSharp]
  linarith

/-- Single-block upper bound for the sharpened weight.  With `C = 22393/1152`,
every point of `torusT ε` has `torusFSharp ε p ≤ C / ε^2`.  The proof uses
`torusSum p ≤ 3/2`, `torusG p.1 ≤ 1/4`, and `ε ≤ 1/6` (which under `0 < ε`
gives `ε^2 ≤ 1/36`), turning the `37/32` constant term into `(37/1152)/ε^2`. -/
theorem torusFSharp_le_block {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {p : ℝ × ℝ} (hp : torusT ε p) :
    torusFSharp ε p ≤ (22393 / 1152) / ε ^ 2 := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hεsqle : ε ^ 2 ≤ 1 / 36 := by nlinarith
  have hsumUpper := (torusT_sum_bounds hε hp).2
  have hsumle : torusSum p ≤ 3 / 2 := by linarith
  have hsumLower := (torusT_sum_bounds hε hp).1
  have hsumnn : 0 ≤ torusSum p := by linarith
  have hsqle : torusSum p ^ 2 ≤ 9 / 4 := by nlinarith
  have hb := torusT_coordinate_bounds hp
  have hgle : torusG p.1 ≤ 1 / 4 := (torusG_bounds hb.1 hb.2.1).2
  have hgnn : 0 ≤ torusG p.1 := (torusG_bounds hb.1 hb.2.1).1
  have hcoef : 0 ≤ (69 / 8) / ε ^ 2 := by positivity
  have h1 : (69 / 8) / ε ^ 2 * torusSum p ^ 2 ≤ (69 / 8) / ε ^ 2 * (9 / 4) :=
    mul_le_mul_of_nonneg_left hsqle hcoef
  have h2 : (37 / 8) * torusG p.1 ≤ (37 / 8) * (1 / 4) :=
    mul_le_mul_of_nonneg_left hgle (by norm_num)
  have h3 : (37 / 8 : ℝ) * (1 / 4) ≤ (37 / 1152) / ε ^ 2 := by
    rw [le_div_iff₀ hεsq]
    nlinarith
  have h4 : (69 / 8) / ε ^ 2 * (9 / 4) = (621 / 32) / ε ^ 2 := by
    ring_nf
  have h5 : (621 / 32 : ℝ) / ε ^ 2 + (37 / 1152) / ε ^ 2 =
      (22393 / 1152) / ε ^ 2 := by
    ring_nf
  simp only [torusFSharp]
  linarith

/-- Ground-truth instance of the single-block bound: at the branch-boundary
point `(1/2, 1/4)` with `ε = 1/6` one has `torusG (1/2) = 0`, so the point
value is `torusFSharp (1/6) ((1/2, 1/4)) = (69/8) * 36 * (9/16) = 5589/32`,
below the envelope `22393/1152 * 36`. -/
example : torusFSharp (1 / 6) ((1 / 2 : ℝ), 1 / 4) ≤
    (22393 / 1152) / (1 / 6) ^ 2 := by
  norm_num [torusFSharp, torusSum, torusG]

/-- The single-block constant is `C = (9/4) * (69/8) + (37/8)/144 = 22393/1152`. -/
theorem torusSharp_block_constant :
    (9 / 4 : ℝ) * (69 / 8) + (37 / 8) / 144 = 22393 / 1152 := by
  norm_num

/-- The doubled single-block constant stays below the integer slice coefficient
`39`: `2 * C = 22393/576 < 39`. -/
theorem torusSharp_double_constant_lt_thirtyNine :
    2 * ((9 / 4 : ℝ) * (69 / 8) + (37 / 8) / 144) < 39 := by
  rw [torusSharp_block_constant]
  norm_num

/-- Algebraic optimality lemma for the proof class.  For arbitrary reals `A`,
`B` with `0 ≤ B`, `4 ≤ A - B`, `0 ≤ A * B - 4 * A - 2 * B + 4`, and `2 ≤ A`,
one has `38 < 2 * ((9/4) * A + B/144)`.  Consequently the integer slice
coefficient `38` is impossible for any coefficient pair satisfying the two
arithmetic certificates of this proof class.

The hypotheses are satisfiable: `A = 69/8`, `B = 37/8` (see the `example`
below).  In fact the constraint set forces `A ≥ 5 + sqrt 13 > 76/9`, so
`2 * ((9/4) * A + B/144) > (9/2) * (76/9) = 38`. -/
theorem torusSharp_coefficient_optimality {A B : ℝ}
    (hB : 0 ≤ B) (hAB : 4 ≤ A - B)
    (hdet : 0 ≤ A * B - 4 * A - 2 * B + 4) (hA : 2 ≤ A) :
    38 < 2 * ((9 / 4) * A + B / 144) := by
  have hA2 : 2 < A := by
    rcases lt_or_eq_of_le hA with h | h
    · exact h
    · exfalso
      rw [← h] at hdet
      linarith
  have hBle : B ≤ A - 4 := by linarith
  have hA2nn : 0 ≤ A - 2 := by linarith
  have hkey : 0 ≤ A ^ 2 - 10 * A + 12 := by
    nlinarith [mul_le_mul_of_nonneg_right hBle hA2nn, hdet]
  have hA5 : 5 < A := by
    by_contra hnot
    have hle : A ≤ 5 := le_of_not_gt hnot
    have hprod : (A - 2) * (A - 8) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
  have hA76 : 76 / 9 < A := by
    by_contra hnot
    have hle : A ≤ 76 / 9 := le_of_not_gt hnot
    have h5nn : 0 ≤ A - 5 := by linarith
    have h5le : A - 5 ≤ 31 / 9 := by linarith
    have hsq : (A - 5) * (A - 5) ≤ (31 / 9) * (31 / 9) :=
      mul_le_mul h5le h5le h5nn (by norm_num)
    nlinarith
  have hBnn : 0 ≤ B / 72 := by linarith
  nlinarith

/-- Satisfiability of the optimality hypotheses: the concrete sharp pair
`A = 69/8`, `B = 37/8` lies in the constraint set, and the conclusion holds. -/
example : 38 < 2 * ((9 / 4 : ℝ) * (69 / 8) + (37 / 8) / 144) :=
  torusSharp_coefficient_optimality (by norm_num) (by norm_num)
    (by rw [torusSharp_close_determinant]; norm_num) (by norm_num)

#check @torusFSharp_threeAP
#check @torusSharp_far_polynomial_kernel
#check @torusSharp_close_polynomial_kernel
#check @torusFSharp_le_block
#check @torusSharp_coefficient_optimality

#print axioms torusFSharp_threeAP
#print axioms torusFSharp_nonneg
#print axioms torusFSharp_pos
#print axioms torusFSharp_le_block
#print axioms torusSharp_coefficient_optimality

end Erdos142