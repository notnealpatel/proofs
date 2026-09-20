/-
  Erdős Problem #142 — energy bounds for the finite-epsilon torus building block.

  This module formalizes the audited quantitative range of the weight `torusF`
  on the extended torus set `torusT ε`.  For `0 < ε ≤ 1/6` the weight is
  nonnegative and bounded above by `(2921/144)/ε²`.

  The constant is assembled exactly as audited:
  * the coordinate sum obeys `torusSum p ≤ 17/12 + ε/2 ≤ 3/2` (the last step
    uses `ε ≤ 1/6`), while its lower facet `2/3 < torusSum p` makes the square
    term's coefficient harmless;
  * the half-periodic quadratic obeys `torusG ≤ 1/4`;
  * the remaining constant `5/4` is charged as `5/4 ≤ (5/144)/ε²`, which is
    exactly the consequence of `ε² ≤ 1/36`.

  Consequently `9/ε² · (3/2)² + 5/4 = 81/(4ε²) + 5/4 ≤ (2921/144)/ε²`.

  A product-ready finite-slicing corollary bounds a `Fin k`-indexed family by
  `k` times the single-point constant.  No claim of mathematical novelty is
  made; the module only records the audited finite-epsilon inequalities.
-/

import Erdos.Erdos142.TorusBuildingBlock

set_option autoImplicit false

namespace Erdos142

/-- Joint satisfiability of the hypotheses: at `ε = 1/12` and a low-sum torus
point, `0 < ε`, `ε ≤ 1/6`, and `torusT ε p` all hold. -/
example : ∃ ε : ℝ, ∃ p : ℝ × ℝ, 0 < ε ∧ ε ≤ 1 / 6 ∧ torusT ε p :=
  ⟨1 / 12, ((1 / 2 : ℝ), 1 / 4), by norm_num, by norm_num, by
    left
    norm_num [torusT1, torusSum]⟩

/-- The audited constant is the sum `81/4 + 5/144 = 2921/144`. -/
example : (81 / 4 : ℝ) + 5 / 144 = 2921 / 144 := by norm_num

/-- On the extended torus set with `0 < ε`, the weight `torusF` is nonnegative.
Both the squared-sum term (coefficient `9/ε² ≥ 0`) and the half-periodic term
(`torusG ≥ 0`) are nonnegative. -/
theorem torusF_nonneg {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : torusT ε p) :
    0 ≤ torusF ε p := by
  have hb := torusT_coordinate_bounds hp
  have hg : 0 ≤ torusG p.1 := (torusG_bounds hb.1 hb.2.1).1
  have hcoef : 0 ≤ 9 / ε ^ 2 := by positivity
  have hs : 0 ≤ torusSum p ^ 2 := sq_nonneg _
  have hterm : 0 ≤ 9 / ε ^ 2 * torusSum p ^ 2 := mul_nonneg hcoef hs
  have hterm2 : 0 ≤ 5 * torusG p.1 := mul_nonneg (by norm_num) hg
  simp only [torusF]
  linarith

/-- The audited upper energy bound: for `0 < ε ≤ 1/6`, every point of the
extended torus set has `torusF ε p ≤ (2921/144)/ε²`. -/
theorem torusF_le {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6) {p : ℝ × ℝ}
    (hp : torusT ε p) :
    torusF ε p ≤ (2921 / 144 : ℝ) / ε ^ 2 := by
  have hb := torusT_coordinate_bounds hp
  have hsumB := torusT_sum_bounds hε hp
  have hsumLower : 0 ≤ torusSum p := by linarith [hsumB.1]
  have hsumUpper : torusSum p ≤ 3 / 2 := by linarith [hsumB.2]
  have hsq : torusSum p ^ 2 ≤ (9 / 4 : ℝ) := by
    have h := mul_self_le_mul_self hsumLower hsumUpper
    have h32 : (3 / 2 : ℝ) * (3 / 2) = 9 / 4 := by norm_num
    rw [h32] at h
    simpa only [pow_two] using h
  have hcoef : 0 ≤ 9 / ε ^ 2 := by positivity
  have hterm : 9 / ε ^ 2 * torusSum p ^ 2 ≤ 9 / ε ^ 2 * (9 / 4) :=
    mul_le_mul_of_nonneg_left hsq hcoef
  have hg : torusG p.1 ≤ 1 / 4 := (torusG_bounds hb.1 hb.2.1).2
  have hterm2 : 5 * torusG p.1 ≤ 5 / 4 := by linarith [hg]
  have hεsq : 0 < ε ^ 2 := by positivity
  have hεsqle : ε ^ 2 ≤ 1 / 36 := by nlinarith [hε, hεle]
  have hcharge : 5 / 4 ≤ (5 / 144 : ℝ) / ε ^ 2 := by
    rw [le_div_iff₀ hεsq]
    nlinarith [hεsqle]
  have hfinal : 9 / ε ^ 2 * (9 / 4) + (5 / 144 : ℝ) / ε ^ 2
      = (2921 / 144 : ℝ) / ε ^ 2 := by
    rw [div_mul_eq_mul_div, ← add_div]
    norm_num
  have hstep1 : 9 / ε ^ 2 * torusSum p ^ 2 + 5 * torusG p.1
      ≤ 9 / ε ^ 2 * (9 / 4) + 5 / 4 := add_le_add hterm hterm2
  have hstep2 : 9 / ε ^ 2 * (9 / 4) + 5 / 4
      ≤ 9 / ε ^ 2 * (9 / 4) + (5 / 144 : ℝ) / ε ^ 2 :=
    add_le_add_right hcharge _
  simp only [torusF]
  exact hstep1.trans (hstep2.trans (le_of_eq hfinal))

/-- Product-ready finite-slicing bound: a `Fin k`-indexed family of points of
the extended torus set has total weight at most `k` times the single-point
energy constant. -/
theorem torusF_sum_le {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {k : ℕ} {x : Fin k → ℝ × ℝ} (hx : ∀ i, torusT ε (x i)) :
    ∑ i : Fin k, torusF ε (x i) ≤ (k : ℝ) * ((2921 / 144 : ℝ) / ε ^ 2) := by
  calc ∑ i : Fin k, torusF ε (x i)
      ≤ ∑ _i : Fin k, (2921 / 144 : ℝ) / ε ^ 2 :=
        Finset.sum_le_sum (fun i _ => torusF_le hε hεle (hx i))
    _ = (k : ℝ) * ((2921 / 144 : ℝ) / ε ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The bound in the reciprocal form `(2921/144) * ε⁻²`, equivalent to the
division form used in `torusF_le`. -/
theorem torusF_le_inv {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6) {p : ℝ × ℝ}
    (hp : torusT ε p) :
    torusF ε p ≤ (2921 / 144 : ℝ) * ε⁻¹ ^ 2 := by
  have h := torusF_le hε hεle hp
  rw [div_eq_mul_inv] at h
  rw [inv_pow]
  exact h

#check @torusF_nonneg
#check @torusF_le
#check @torusF_sum_le
#print axioms torusF_nonneg
#print axioms torusF_le
#print axioms torusF_sum_le

end Erdos142