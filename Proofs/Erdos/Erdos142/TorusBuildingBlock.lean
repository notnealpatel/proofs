/-
  Erdős Problem #142 — a finite-epsilon torus building block.

  Provenance: Elsholtz–Hunter–Proske–Sauermann (EHPS), “Improving Behrend's
  construction”, arXiv:2406.12290v1, Proposition 2.2 and §5, Definition 5.1.
  The cited source uses upper facet `17/12` and weight coefficients `24, 6`.

  This module formally checks the subsequent finite-epsilon modifications
  with enlarged upper facet `17/12 + ε/2` and weight coefficients `9, 5`.
  These modifications were independently audited and are now formally
  verified here.  No claim of mathematical novelty or literature priority
  is made.  The module proves only the geometric and polynomial inequality;
  it makes no area, integration, or asymptotic-improvement claim.
-/

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- The sum of the two coordinates of a point in the torus square. -/
def torusSum (p : ℝ × ℝ) : ℝ := p.1 + p.2

/-- The half-periodic quadratic used in the torus building block. -/
noncomputable def torusG (a : ℝ) : ℝ :=
  if a < (1 / 2 : ℝ) then a ^ 2 else (a - 1 / 2) ^ 2

/-- The low-sum part of the extended finite-epsilon torus set. -/
def torusT1 (p : ℝ × ℝ) : Prop :=
  (1 / 2 : ℝ) ≤ p.1 ∧ p.1 < 1 ∧
    0 ≤ p.2 ∧ p.2 < 1 ∧
      (2 / 3 : ℝ) < torusSum p ∧ torusSum p ≤ 7 / 6

/-- The high-sum part below the horizontal half-coordinate facet. -/
def torusT2 (ε : ℝ) (p : ℝ × ℝ) : Prop :=
  (1 / 2 : ℝ) ≤ p.1 ∧ p.1 < 1 ∧
    0 ≤ p.2 ∧ p.2 < 1 / 2 ∧
      7 / 6 + ε ≤ torusSum p ∧ torusSum p ≤ 17 / 12 + ε / 2

/-- The high-sum part above the horizontal half-coordinate facet. -/
def torusT3 (ε : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ p.1 < 1 / 2 ∧
    (1 / 2 : ℝ) ≤ p.2 ∧ p.2 < 1 ∧
      7 / 6 + ε ≤ torusSum p ∧ torusSum p ≤ 17 / 12 + ε / 2 ∧
        3 / 2 + ε ≤ 2 * p.1 + p.2

/-- The extended finite-epsilon torus set `T1 ∪ T2 ∪ T3`. -/
def torusT (ε : ℝ) (p : ℝ × ℝ) : Prop :=
  torusT1 p ∨ torusT2 ε p ∨ torusT3 ε p

/-- The improved finite-epsilon quadratic weight, with coefficients nine and five. -/
noncomputable def torusF (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  9 / ε ^ 2 * torusSum p ^ 2 + 5 * torusG p.1

/-- Ground truth for the coordinate-sum definition. -/
example : torusSum ((1 / 2 : ℝ), 1 / 4) = 3 / 4 := by
  norm_num [torusSum]

/-- Ground truth on the lower half-open branch of `torusG`. -/
example : torusG (1 / 4) = (1 / 16 : ℝ) := by
  norm_num [torusG]

/-- Ground truth at the discontinuity: one half uses the upper branch. -/
example : torusG (1 / 2) = 0 := by
  norm_num [torusG]

/-- At epsilon `1/12`, all three pieces of the extended set are inhabited. -/
example :
    torusT1 ((1 / 2 : ℝ), 1 / 4) ∧
      torusT2 (1 / 12) ((5 / 6 : ℝ), 5 / 12) ∧
      torusT3 (1 / 12) ((1 / 3 : ℝ), 11 / 12) := by
  norm_num [torusT1, torusT2, torusT3, torusSum]

/-- A low-sum witness belongs to the union at epsilon `1/12`. -/
example : torusT (1 / 12) ((1 / 2 : ℝ), 1 / 4) := by
  left
  norm_num [torusT1, torusSum]

/-- Ground truth for the improved weight at a branch-boundary point. -/
example : torusF 1 ((1 / 2 : ℝ), 1 / 4) = 81 / 16 := by
  norm_num [torusF, torusSum, torusG]

/-- Every point of the extended torus set lies in the half-open unit square. -/
theorem torusT_coordinate_bounds {ε : ℝ} {p : ℝ × ℝ} (hp : torusT ε p) :
    0 ≤ p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 < 1 := by
  rcases hp with hp | hp | hp
  · exact ⟨hp.1.trans' (by norm_num), hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  · exact ⟨hp.1.trans' (by norm_num), hp.2.1, hp.2.2.1,
      hp.2.2.2.1.trans (by norm_num)⟩
  · exact ⟨hp.1, hp.2.1.trans (by norm_num),
      hp.2.2.1.trans' (by norm_num), hp.2.2.2.1⟩

/-- The sum coordinate of a torus point lies between the two outer facets. -/
theorem torusT_sum_bounds {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : torusT ε p) :
    (2 / 3 : ℝ) < torusSum p ∧ torusSum p ≤ 17 / 12 + ε / 2 := by
  rcases hp with hp | hp | hp
  · constructor
    · exact hp.2.2.2.2.1
    · exact hp.2.2.2.2.2.trans (by linarith)
  · constructor
    · linarith [hp.2.2.2.2.1]
    · exact hp.2.2.2.2.2
  · constructor
    · linarith [hp.2.2.2.2.1]
    · exact hp.2.2.2.2.2.1

/-- On a unit-square coordinate, `torusG` lies in the audited interval. -/
theorem torusG_bounds {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    0 ≤ torusG a ∧ torusG a ≤ 1 / 4 := by
  by_cases ha : a < (1 / 2 : ℝ)
  · simp only [torusG, if_pos ha]
    constructor
    · positivity
    · nlinarith [sq_nonneg a, mul_nonneg ha0 (sub_nonneg.mpr (le_of_lt ha))]
  · have hhalf : (1 / 2 : ℝ) ≤ a := le_of_not_gt ha
    simp only [torusG, if_neg ha]
    constructor
    · positivity
    · nlinarith [sq_nonneg (a - 1 / 2),
        mul_nonneg (sub_nonneg.mpr hhalf) (sub_nonneg.mpr (le_of_lt ha1))]

/-- On the extended torus set, `torusG a` dominates the upper-branch square. -/
theorem torusG_ge_shift_sq {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : torusT ε p) :
    (p.1 - 1 / 2) ^ 2 ≤ torusG p.1 := by
  rcases hp with hp | hp | hp
  · rw [torusG, if_neg (not_lt.mpr hp.1)]
  · rw [torusG, if_neg (not_lt.mpr hp.1)]
  · rw [torusG, if_pos hp.2.1]
    have ha : (1 / 4 : ℝ) < p.1 := by
      linarith [hp.2.2.2.1, hp.2.2.2.2.2.2]
    nlinarith

/-- If two endpoints have first-coordinate sum below one, their total
coordinate sums cross the strengthened `11/6 + ε` threshold. -/
theorem torus_endpoint_sum_large_of_first_sum_lt_one {ε : ℝ} (hε : 0 < ε)
    {x z : ℝ × ℝ} (hx : torusT ε x) (hz : torusT ε z)
    (hfirst : x.1 + z.1 < 1) :
    11 / 6 + ε < torusSum x + torusSum z := by
  simp only [torusSum] at *
  rcases hx with hx | hx | hx <;> rcases hz with hz | hz | hz <;>
    simp only [torusT1, torusT2, torusT3, torusSum] at hx hz <;> linarith

/-- Close endpoint sums cannot straddle the low and high sum bands; in the
mixed high-band case the slanted `T3` facet forces first-coordinate sum one. -/
theorem torus_first_sum_ge_one_of_close {ε : ℝ} {x z : ℝ × ℝ}
    (hx : torusT ε x) (hz : torusT ε z)
    (hclose : |torusSum x - torusSum z| < ε)
    (hhigh : (1 / 2 : ℝ) ≤ x.1 ∨ (1 / 2 : ℝ) ≤ z.1) :
    1 ≤ x.1 + z.1 := by
  simp only [torusSum] at *
  have hclose' := abs_lt.mp hclose
  rcases hx with hx | hx | hx <;> rcases hz with hz | hz | hz <;>
    simp only [torusT1, torusT2, torusT3, torusSum] at hx hz <;>
    rcases hhigh with hhigh | hhigh <;> linarith

/-- An integer wrap of three coordinates in `[0,1)` is `-1`, `0`, or `1`. -/
theorem integer_wrap_cases {a y c : ℝ} {w : ℤ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hwrap : a + c - 2 * y = (w : ℝ)) :
    w = -1 ∨ w = 0 ∨ w = 1 := by
  have hloR : (-2 : ℝ) < (w : ℝ) := by linarith
  have hhiR : (w : ℝ) < 2 := by linarith
  have hlo : (-2 : ℤ) < w := by exact_mod_cast hloR
  have hhi : w < (2 : ℤ) := by exact_mod_cast hhiR
  omega

/-- In the extended geometry, the sum of the two integer AP wraps is zero or
one.  The upper facet `17/12 + ε/2` is used sharply here. -/
theorem torus_wrap_sum_zero_or_one {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {x y z : ℝ × ℝ} {w₁ w₂ : ℤ}
    (hx : torusT ε x) (hy : torusT ε y) (hz : torusT ε z)
    (hwrap₁ : x.1 + z.1 - 2 * y.1 = (w₁ : ℝ))
    (hwrap₂ : x.2 + z.2 - 2 * y.2 = (w₂ : ℝ)) :
    w₁ + w₂ = 0 ∨ w₁ + w₂ = 1 := by
  have hxb := torusT_coordinate_bounds hx
  have hyb := torusT_coordinate_bounds hy
  have hzb := torusT_coordinate_bounds hz
  have hw₁ := integer_wrap_cases hxb.1 hxb.2.1 hyb.1 hyb.2.1
    hzb.1 hzb.2.1 hwrap₁
  have hw₂ := integer_wrap_cases hxb.2.2.1 hxb.2.2.2 hyb.2.2.1 hyb.2.2.2
    hzb.2.2.1 hzb.2.2.2 hwrap₂
  have hw₁lo : (-1 : ℤ) ≤ w₁ := by omega
  have hw₁hi : w₁ ≤ (1 : ℤ) := by omega
  have hw₂lo : (-1 : ℤ) ≤ w₂ := by omega
  have hw₂hi : w₂ ≤ (1 : ℤ) := by omega
  obtain ⟨hxsumLower, hxsumUpper⟩ := torusT_sum_bounds hε hx
  obtain ⟨hysumLower, hysumUpper⟩ := torusT_sum_bounds hε hy
  obtain ⟨hzsumLower, hzsumUpper⟩ := torusT_sum_bounds hε hz
  have hsumwrap :
      torusSum x + torusSum z - 2 * torusSum y = ((w₁ + w₂ : ℤ) : ℝ) := by
    rw [Int.cast_add]
    simp only [torusSum]
    linarith
  have hsumcases : w₁ + w₂ = -2 ∨ w₁ + w₂ = -1 ∨
      w₁ + w₂ = 0 ∨ w₁ + w₂ = 1 ∨ w₁ + w₂ = 2 := by
    omega
  rcases hsumcases with hminusTwo | hminusOne | hzero | hone | htwo
  · have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = -2 := by norm_num [hminusTwo]
    rw [hcast] at hsumwrap
    linarith
  · exfalso
    have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = -1 := by norm_num [hminusOne]
    rw [hcast] at hsumwrap
    by_cases hfirst : x.1 + z.1 < 1
    · have hlarge := torus_endpoint_sum_large_of_first_sum_lt_one hε hx hz hfirst
      linarith
    · have hfirst' : 1 ≤ x.1 + z.1 := le_of_not_gt hfirst
      have hw₁ne : w₁ ≠ -1 := by
        intro hw₁neg
        have hcast₁ : (w₁ : ℝ) = -1 := by norm_num [hw₁neg]
        rw [hcast₁] at hwrap₁
        linarith
      have hw₁zero : w₁ = 0 := by omega
      have hw₂neg : w₂ = -1 := by omega
      have hcast₁ : (w₁ : ℝ) = 0 := by norm_num [hw₁zero]
      have hcast₂ : (w₂ : ℝ) = -1 := by norm_num [hw₂neg]
      rw [hcast₁] at hwrap₁
      rw [hcast₂] at hwrap₂
      have hyfirst : (1 / 2 : ℝ) ≤ y.1 := by linarith
      have hysecond : (1 / 2 : ℝ) ≤ y.2 := by linarith
      rcases hy with hy | hy | hy
      · linarith [hy.2.2.2.2.2]
      · linarith [hy.2.2.2.1]
      · linarith [hy.2.1]
  · exact Or.inl hzero
  · exact Or.inr hone
  · have hcast : (((w₁ + w₂ : ℤ) : ℝ)) = 2 := by norm_num [htwo]
    rw [hcast] at hsumwrap
    linarith

/-- The half-periodic quadratic takes the same value at a midpoint and at any
unit-torus half-lift of that midpoint. -/
theorem torusG_eq_midpoint_of_integer_wrap {a y c : ℝ} {w : ℤ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hwrap : a + c - 2 * y = (w : ℝ)) :
    torusG y = torusG ((a + c) / 2) := by
  rcases integer_wrap_cases ha0 ha1 hy0 hy1 hc0 hc1 hwrap with
      hw | hw | hw
  · have hcast : (w : ℝ) = -1 := by norm_num [hw]
    rw [hcast] at hwrap
    have hmid : (a + c) / 2 < (1 / 2 : ℝ) := by linarith
    have hynot : ¬ y < (1 / 2 : ℝ) := by linarith
    simp only [torusG, if_neg hynot, if_pos hmid]
    nlinarith
  · have hcast : (w : ℝ) = 0 := by norm_num [hw]
    rw [hcast] at hwrap
    congr 1
    linarith
  · have hcast : (w : ℝ) = 1 := by norm_num [hw]
    rw [hcast] at hwrap
    have hmidnot : ¬ (a + c) / 2 < (1 / 2 : ℝ) := by
      apply not_lt.mpr
      linarith
    have hylt : y < (1 / 2 : ℝ) := by linarith
    simp only [torusG, if_pos hylt, if_neg hmidnot]
    nlinarith

/-- In the close-sum branch, the half-periodic quadratic supplies half the
first-coordinate endpoint square. -/
theorem torusG_close_gap {ε : ℝ} (hε : 0 < ε) {x y z : ℝ × ℝ} {w₁ : ℤ}
    (hx : torusT ε x) (hy : torusT ε y) (hz : torusT ε z)
    (hwrap₁ : x.1 + z.1 - 2 * y.1 = (w₁ : ℝ))
    (hclose : |torusSum x - torusSum z| < ε) :
    (x.1 - z.1) ^ 2 / 2 ≤ torusG x.1 + torusG z.1 - 2 * torusG y.1 := by
  have hxb := torusT_coordinate_bounds hx
  have hyb := torusT_coordinate_bounds hy
  have hzb := torusT_coordinate_bounds hz
  have hgmid := torusG_eq_midpoint_of_integer_wrap hxb.1 hxb.2.1
    hyb.1 hyb.2.1 hzb.1 hzb.2.1 hwrap₁
  rw [hgmid]
  by_cases hxhalf : x.1 < (1 / 2 : ℝ)
  · by_cases hzhalf : z.1 < (1 / 2 : ℝ)
    · have hmid : (x.1 + z.1) / 2 < (1 / 2 : ℝ) := by linarith
      simp only [torusG, if_pos hxhalf, if_pos hzhalf, if_pos hmid]
      ring_nf
      exact le_rfl
    · have hhigh : (1 / 2 : ℝ) ≤ x.1 ∨ (1 / 2 : ℝ) ≤ z.1 :=
        Or.inr (le_of_not_gt hzhalf)
      have hfirst := torus_first_sum_ge_one_of_close hx hz hclose hhigh
      have hmidnot : ¬ (x.1 + z.1) / 2 < (1 / 2 : ℝ) := by
        exact not_lt.mpr (by linarith)
      have hgx := torusG_ge_shift_sq hε hx
      have hgz := torusG_ge_shift_sq hε hz
      have hgmidBranch :
          torusG ((x.1 + z.1) / 2) = ((x.1 + z.1) / 2 - 1 / 2) ^ 2 := by
        simp only [torusG, if_neg hmidnot]
      rw [hgmidBranch]
      nlinarith
  · have hhigh : (1 / 2 : ℝ) ≤ x.1 ∨ (1 / 2 : ℝ) ≤ z.1 :=
      Or.inl (le_of_not_gt hxhalf)
    have hfirst := torus_first_sum_ge_one_of_close hx hz hclose hhigh
    have hmidnot : ¬ (x.1 + z.1) / 2 < (1 / 2 : ℝ) := by
      exact not_lt.mpr (by linarith)
    have hgx := torusG_ge_shift_sq hε hx
    have hgz := torusG_ge_shift_sq hε hz
    have hgmidBranch :
        torusG ((x.1 + z.1) / 2) = ((x.1 + z.1) / 2 - 1 / 2) ^ 2 := by
      simp only [torusG, if_neg hmidnot]
    rw [hgmidBranch]
    nlinarith

/-- A pointwise distance between two points of the half-open unit square has
squared Euclidean length strictly below two. -/
theorem unit_square_endpoint_distance_lt_two {x z : ℝ × ℝ}
    (hx : 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1)
    (hz : 0 ≤ z.1 ∧ z.1 < 1 ∧ 0 ≤ z.2 ∧ z.2 < 1) :
    (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2 < 2 := by
  have huLower : (-1 : ℝ) < x.1 - z.1 := by linarith
  have huUpper : x.1 - z.1 < 1 := by linarith
  have hvLower : (-1 : ℝ) < x.2 - z.2 := by linarith
  have hvUpper : x.2 - z.2 < 1 := by linarith
  have huAdd : 0 < 1 + (x.1 - z.1) := by linarith
  have hvAdd : 0 < 1 + (x.2 - z.2) := by linarith
  have huProd := mul_pos (sub_pos.mpr huUpper) huAdd
  have hvProd := mul_pos (sub_pos.mpr hvUpper) hvAdd
  nlinarith

/-- The coefficient-nine/five far-branch polynomial kernel. -/
theorem torus_far_polynomial_kernel {ε sx sy sz gx gy gz u v : ℝ}
    (hε : 0 < ε)
    (hgap : ε ^ 2 / 2 ≤ sx ^ 2 + sz ^ 2 - 2 * sy ^ 2)
    (hgx : 0 ≤ gx) (hgz : 0 ≤ gz) (hgy : gy ≤ 1 / 4)
    (hdist : u ^ 2 + v ^ 2 < 2) :
    2 * (9 / ε ^ 2 * sy ^ 2 + 5 * gy) + u ^ 2 + v ^ 2 ≤
      (9 / ε ^ 2 * sx ^ 2 + 5 * gx) +
        (9 / ε ^ 2 * sz ^ 2 + 5 * gz) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcoef : 0 ≤ 9 / ε ^ 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hgap hcoef
  have hcancel : (9 / ε ^ 2) * (ε ^ 2 / 2) = (9 / 2 : ℝ) := by
    field_simp
  rw [hcancel] at hprod
  nlinarith

/-- Positive semidefiniteness of the close-branch endpoint quadratic. -/
theorem torus_close_psd (u v : ℝ) :
    u ^ 2 + v ^ 2 ≤ 9 / 2 * (u + v) ^ 2 + 5 / 2 * u ^ 2 := by
  nlinarith [sq_nonneg (7 * v + 9 * u), sq_nonneg u]

/-- The coefficient-nine/five close-branch polynomial kernel.  Its explicit
`ε ≤ 1` hypothesis is necessary for this general sufficient statement. -/
theorem torus_close_polynomial_kernel {ε sx sy sz gx gy gz u v : ℝ}
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hsum : sx ^ 2 + sz ^ 2 - 2 * sy ^ 2 = (u + v) ^ 2 / 2)
    (hgap : u ^ 2 / 2 ≤ gx + gz - 2 * gy) :
    2 * (9 / ε ^ 2 * sy ^ 2 + 5 * gy) + u ^ 2 + v ^ 2 ≤
      (9 / ε ^ 2 * sx ^ 2 + 5 * gx) +
        (9 / ε ^ 2 * sz ^ 2 + 5 * gz) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hεsqle : ε ^ 2 ≤ 1 := by nlinarith
  have hcoeff : (9 : ℝ) ≤ 9 / ε ^ 2 := by
    apply (le_div_iff₀ hεsq).2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u + v))
  have hpsd := torus_close_psd u v
  nlinarith

/-- The extended finite-epsilon torus set with weight coefficients nine and
five satisfies the required three-term-progression energy inequality. -/
theorem torusF_threeAP {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {x y z : ℝ × ℝ} {w₁ w₂ : ℤ}
    (hx : torusT ε x) (hy : torusT ε y) (hz : torusT ε z)
    (hwrap₁ : x.1 + z.1 - 2 * y.1 = (w₁ : ℝ))
    (hwrap₂ : x.2 + z.2 - 2 * y.2 = (w₂ : ℝ)) :
    2 * torusF ε y + (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2 ≤
      torusF ε x + torusF ε z := by
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
      exact torus_close_polynomial_kernel hε hεone hsumGap hgGap
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
      exact torus_far_polynomial_kernel hε hsumGap hgx hgz hgy hdist
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
      exact torus_far_polynomial_kernel hε hsumGap hgx hgz hgy hdist
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
      exact torus_far_polynomial_kernel hε hsumGap hgx hgz hgy hdist

#check @torusF_threeAP
#print axioms torusF_threeAP

/-! ### Product/slice transfer of the torus building block

The building block `torusF_threeAP` is a pointwise statement about a single
pair of torus coordinates.  The EHPS construction (arXiv:2406.12290, proof of
Proposition 2.2 from Proposition 5.1) applies it independently in every block
of a product configuration and then sums.  The lemmas below perform exactly
that summation, without any area or measure bookkeeping: they consume
`torusF_threeAP` coordinatewise and expose the two conclusions the transfer
needs, namely the total squared endpoint separation and its per-coordinate
consequences. -/

/-- The squared Euclidean separation of two points of the unit torus square. -/
def torusSepSq (x z : ℝ × ℝ) : ℝ := (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2

/-- Ground truth: the squared separation of `(0,0)` and `(3,4)` is `25`. -/
example : torusSepSq ((0 : ℝ), 0) ((3 : ℝ), 4) = 25 := by
  norm_num [torusSepSq]

/-- Ground truth: the squared separation of `(1/2,0)` and `(0,0)` is `1/4`. -/
example : torusSepSq ((1 / 2 : ℝ), 0) ((0 : ℝ), 0) = 1 / 4 := by
  norm_num [torusSepSq]

/-- Squared torus separation is nonnegative. -/
theorem torusSepSq_nonneg (x z : ℝ × ℝ) : 0 ≤ torusSepSq x z := by
  simp only [torusSepSq]
  positivity

/-- The block weight deficit splits into the three block weight sums. -/
theorem torusF_sum_sub {ι : Type*} (s : Finset ι) (X Y Z : ι → ℝ × ℝ)
    (ε : ℝ) :
    ∑ i ∈ s, (torusF ε (X i) + torusF ε (Z i) - 2 * torusF ε (Y i)) =
      (∑ i ∈ s, torusF ε (X i)) + (∑ i ∈ s, torusF ε (Z i)) -
        2 * (∑ i ∈ s, torusF ε (Y i)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Summed torus energy.  Applying `torusF_threeAP` in every block and
summing over the block index set `s`, the total squared endpoint separation
is bounded by the total weight deficit. -/
theorem torusF_product_energy_le {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {ι : Type*} (s : Finset ι) (X Y Z : ι → ℝ × ℝ)
    (hX : ∀ i ∈ s, torusT ε (X i)) (hY : ∀ i ∈ s, torusT ε (Y i))
    (hZ : ∀ i ∈ s, torusT ε (Z i))
    (w₁ w₂ : ι → ℤ)
    (hw₁ : ∀ i ∈ s, (X i).1 + (Z i).1 - 2 * (Y i).1 = (w₁ i : ℝ))
    (hw₂ : ∀ i ∈ s, (X i).2 + (Z i).2 - 2 * (Y i).2 = (w₂ i : ℝ)) :
    ∑ i ∈ s, torusSepSq (X i) (Z i) ≤
      ∑ i ∈ s, (torusF ε (X i) + torusF ε (Z i) - 2 * torusF ε (Y i)) := by
  have hpoint : ∀ i ∈ s, 2 * torusF ε (Y i) + torusSepSq (X i) (Z i) ≤
      torusF ε (X i) + torusF ε (Z i) :=
    fun i hi => by
      have h := torusF_threeAP hε hεle (hX i hi) (hY i hi) (hZ i hi)
        (hw₁ i hi) (hw₂ i hi)
      simp only [torusSepSq]
      linarith
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hsplit := torusF_sum_sub s X Y Z ε
  have hsplit2 : ∑ i ∈ s, (torusF ε (X i) + torusF ε (Z i)) =
      (∑ i ∈ s, torusF ε (X i)) + (∑ i ∈ s, torusF ε (Z i)) := by
    rw [Finset.sum_add_distrib]
  linarith

/-- Half-open slice form of the summed torus energy.  If the three block
weight sums all lie in the same half-open interval `[L, L + Δ)`, then the
total squared endpoint separation is strictly below `2 * Δ`. -/
theorem torusF_product_slice_energy {ε L Δ : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ 1 / 6) {ι : Type*} (s : Finset ι) (X Y Z : ι → ℝ × ℝ)
    (hX : ∀ i ∈ s, torusT ε (X i)) (hY : ∀ i ∈ s, torusT ε (Y i))
    (hZ : ∀ i ∈ s, torusT ε (Z i))
    (w₁ w₂ : ι → ℤ)
    (hw₁ : ∀ i ∈ s, (X i).1 + (Z i).1 - 2 * (Y i).1 = (w₁ i : ℝ))
    (hw₂ : ∀ i ∈ s, (X i).2 + (Z i).2 - 2 * (Y i).2 = (w₂ i : ℝ))
    (hXband : L ≤ ∑ i ∈ s, torusF ε (X i) ∧
      ∑ i ∈ s, torusF ε (X i) < L + Δ)
    (hYband : L ≤ ∑ i ∈ s, torusF ε (Y i) ∧
      ∑ i ∈ s, torusF ε (Y i) < L + Δ)
    (hZband : L ≤ ∑ i ∈ s, torusF ε (Z i) ∧
      ∑ i ∈ s, torusF ε (Z i) < L + Δ) :
    ∑ i ∈ s, torusSepSq (X i) (Z i) < 2 * Δ := by
  have henergy := torusF_product_energy_le hε hεle s X Y Z hX hY hZ
    w₁ w₂ hw₁ hw₂
  have hsplit := torusF_sum_sub s X Y Z ε
  rw [hsplit] at henergy
  have hXhi := hXband.2
  have hZhi := hZband.2
  have hYlo := hYband.1
  nlinarith [henergy]

/-- Square-form endpoint separation.  Under the half-open slice hypotheses,
every coordinate of the endpoint difference has square strictly below
`2 * Δ`; this is the sqrt-free conclusion used by finite-grid transfers. -/
theorem torusF_product_slice_separation_sq {ε L Δ : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ 1 / 6) {ι : Type*} (s : Finset ι) (X Y Z : ι → ℝ × ℝ)
    (hX : ∀ i ∈ s, torusT ε (X i)) (hY : ∀ i ∈ s, torusT ε (Y i))
    (hZ : ∀ i ∈ s, torusT ε (Z i))
    (w₁ w₂ : ι → ℤ)
    (hw₁ : ∀ i ∈ s, (X i).1 + (Z i).1 - 2 * (Y i).1 = (w₁ i : ℝ))
    (hw₂ : ∀ i ∈ s, (X i).2 + (Z i).2 - 2 * (Y i).2 = (w₂ i : ℝ))
    (hXband : L ≤ ∑ i ∈ s, torusF ε (X i) ∧
      ∑ i ∈ s, torusF ε (X i) < L + Δ)
    (hYband : L ≤ ∑ i ∈ s, torusF ε (Y i) ∧
      ∑ i ∈ s, torusF ε (Y i) < L + Δ)
    (hZband : L ≤ ∑ i ∈ s, torusF ε (Z i) ∧
      ∑ i ∈ s, torusF ε (Z i) < L + Δ) :
    ∀ i ∈ s, ((X i).1 - (Z i).1) ^ 2 < 2 * Δ ∧
      ((X i).2 - (Z i).2) ^ 2 < 2 * Δ := by
  have henergy := torusF_product_slice_energy hε hεle s X Y Z hX hY hZ
    w₁ w₂ hw₁ hw₂ hXband hYband hZband
  simp only [torusSepSq] at henergy
  intro i hi
  have hle := Finset.single_le_sum
    (fun j _ => torusSepSq_nonneg (X j) (Z j)) hi
  simp only [torusSepSq] at hle
  constructor <;>
    nlinarith [sq_nonneg ((X i).1 - (Z i).1), sq_nonneg ((X i).2 - (Z i).2)]

/-- Absolute-value endpoint separation.  Under the half-open slice
hypotheses and `0 < Δ`, every coordinate of the endpoint difference is
strictly below `sqrt (2 * Δ)`.  With the paper's slice width `Δ = δ^2 / 2`
this is exactly the conclusion `|x_i - z_i| < δ`. -/
theorem torusF_product_slice_separation {ε L Δ : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ 1 / 6) (hΔ : 0 < Δ) {ι : Type*} (s : Finset ι)
    (X Y Z : ι → ℝ × ℝ)
    (hX : ∀ i ∈ s, torusT ε (X i)) (hY : ∀ i ∈ s, torusT ε (Y i))
    (hZ : ∀ i ∈ s, torusT ε (Z i))
    (w₁ w₂ : ι → ℤ)
    (hw₁ : ∀ i ∈ s, (X i).1 + (Z i).1 - 2 * (Y i).1 = (w₁ i : ℝ))
    (hw₂ : ∀ i ∈ s, (X i).2 + (Z i).2 - 2 * (Y i).2 = (w₂ i : ℝ))
    (hXband : L ≤ ∑ i ∈ s, torusF ε (X i) ∧
      ∑ i ∈ s, torusF ε (X i) < L + Δ)
    (hYband : L ≤ ∑ i ∈ s, torusF ε (Y i) ∧
      ∑ i ∈ s, torusF ε (Y i) < L + Δ)
    (hZband : L ≤ ∑ i ∈ s, torusF ε (Z i) ∧
      ∑ i ∈ s, torusF ε (Z i) < L + Δ) :
    ∀ i ∈ s, |(X i).1 - (Z i).1| < Real.sqrt (2 * Δ) ∧
      |(X i).2 - (Z i).2| < Real.sqrt (2 * Δ) := by
  have hsq := torusF_product_slice_separation_sq hε hεle s X Y Z hX hY hZ
    w₁ w₂ hw₁ hw₂ hXband hYband hZband
  have hpos : 0 < 2 * Δ := by linarith
  have hsqrtpos : 0 < Real.sqrt (2 * Δ) := Real.sqrt_pos.mpr hpos
  have hs : (Real.sqrt (2 * Δ)) ^ 2 = 2 * Δ := Real.sq_sqrt hpos.le
  intro i hi
  obtain ⟨h1, h2⟩ := hsq i hi
  constructor
  · have h1' : ((X i).1 - (Z i).1) ^ 2 < (Real.sqrt (2 * Δ)) ^ 2 := by
      rw [hs]
      exact h1
    have := (sq_lt_sq.mp h1')
    rwa [abs_of_pos hsqrtpos] at this
  · have h2' : ((X i).2 - (Z i).2) ^ 2 < (Real.sqrt (2 * Δ)) ^ 2 := by
      rw [hs]
      exact h2
    have := (sq_lt_sq.mp h2')
    rwa [abs_of_pos hsqrtpos] at this

#print axioms torusF_product_energy_le
#print axioms torusF_product_slice_energy
#print axioms torusF_product_slice_separation_sq
#print axioms torusF_product_slice_separation

end Erdos142
