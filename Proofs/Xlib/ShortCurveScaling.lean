import Mathlib
import Xlib.ShearAdditionEC

/-!
# Point-group isomorphism of short Weierstrass curves under unit scaling

For any field `F` and any unit `u ≠ 0`, the admissible change of variables
`(x, y) ↦ (u²x, u³y)` (Silverman, *The Arithmetic of Elliptic Curves*,
III §1 Table 3.1: `u ∈ F^×`, `r = s = t = 0`) carries the short Weierstrass
curve `y² = x³ + a₄x + a₆` onto `y² = x³ + (u⁴a₄)x + (u⁶a₆)` and induces an
**isomorphism of the affine point groups**:

* `scaleEquiv` — `(shortCurve F a₄ a₆).Point ≃+
  (shortCurve F (u⁴a₄) (u⁶a₆)).Point`, with **no characteristic assumption**.

## Mathlib gap

Mathlib's `WeierstrassCurve.VariableChange` acts on *curves* only: it
rescales the coefficients `aᵢ` and the standard quantities `b₂ … Δ, j`, but
provides no map of points. The only `AddEquiv`s in Mathlib's
`AlgebraicGeometry/EllipticCurve` directory are the coordinate-model
equivalences (affine ↔ Jacobian ↔ projective points of the *same* curve),
and the only point-level variable-change lemma is
`Affine.nonsingular_iff_variableChange`, which covers the pure translation
`u = 1, r = x, s = 0, t = y` used to recentre a point at the origin. The
point-group isomorphism induced by a variable change — the statement that
makes "isomorphic curves have isomorphic Mordell–Weil groups" usable — is
absent at every generality; this file provides the `u`-scaling case.

## Characteristic-freeness

Nonsingularity transfer is proved directly from the `Nonsingular`
definition: the curve equation and the two partial derivatives
`-(3x² + a₄)` and `2y` scale by `u⁶`, `u⁴`, `u³` respectively, so each is
zero iff its image is. No discriminant, no `IsElliptic`, no order, no
characteristic hypothesis. (A previous version of the congruent-number
corollary below routed nonsingularity through `IsElliptic` via `Δ ≠ 0`,
which silently needs `64 ≠ 0`, i.e. `char F ≠ 2`; the direct route shows
the hypothesis is not needed.)

## Corollaries: the congruent-number family

* `congrCurve n = shortCurve ℚ (-(n²)) 0` — the curve `y² = x³ - n²x`;
  `congrCurve_Δ : Δ = 64n⁶`; `congrCurve_isElliptic` for `n ≠ 0`.
* `congrCurveIso : (congrCurve n).Point ≃+ (congrCurve (4n)).Point` — the
  `u = 2` instance (`2⁴·(-(n²)) = -((4n)²)`, `2⁶·0 = 0`), i.e.
  `(x, y) ↦ (4x, 8y)`. The direct nonsingularity transfer removes the
  hypothesis `n ≠ 0` that the `IsElliptic` route required: the isomorphism
  holds for **all** `n : ℚ`, including the singular curve `y² = x³` at
  `n = 0` (Mathlib's group law lives on the nonsingular locus of an
  arbitrary Weierstrass cubic).

This is the algebraic core behind the OEIS A319510 empirical claim
(Aranda 2024) that the rank of `y² = x³ - n²x` is invariant under
`n ↦ 4n`: an `AddEquiv` of the point groups makes any functorial rank
surrogate invariant.

## Gaps to A319510

1. The OEIS sequence is indexed by `n : ℕ⁺`; here `n : ℚ` (now with no
   nonzeroness hypothesis). The intended reading `n : ℕ, n > 0` embeds via
   `(↑n : ℚ)`.
2. The rank definition (Mordell–Weil rank of `E(ℚ)`) is not formalised in
   Mathlib; the `AddEquiv` implies any functorial rank surrogate (e.g.
   `Module.rank` of the torsion-free quotient) is preserved.
3. The OEIS claim is marked "Empirical" and states `a(4n) = a(n)`; the
   general theorem `scaleEquiv` (specialised by `congrCurveIso`) proves the
   underlying group isomorphism that would make such an equality hold for
   any rank-like invariant.

## Open note

The Mathlib-PR-grade statement is the point-group isomorphism for a full
admissible change `VariableChange (u, r, s, t)` on a general Weierstrass
curve (all `aᵢ` nonzero); the group-law transfer there needs the general
`slope`/`addX`/`addY` covariance under translation and shear, not just the
diagonal scaling proved here. Done in `Xlib.VariableChangePointEquiv`
(`pointEquiv : (C • W).toAffine.Point ≃+ W.toAffine.Point`, char-free),
which recovers this file's `scaleEquiv` statement as `shortScaleEquiv`;
this file's `scaleEquiv` is kept as the standalone `r = s = t = 0` case.
-/

noncomputable section

namespace Xlib.ShortCurveScaling

open WeierstrassCurve.Affine
open Xlib.ShearAdditionEC (shortCurve shortCurve_a₁ shortCurve_a₂ shortCurve_a₃)

variable {F : Type*} [Field F]

/-! ## Short-curve coefficient and formula lemmas -/

@[simp] lemma shortCurve_a₄ (a₄ a₆ : F) : (shortCurve F a₄ a₆).a₄ = a₄ := rfl

@[simp] lemma shortCurve_a₆ (a₄ a₆ : F) : (shortCurve F a₄ a₆).a₆ = a₆ := rfl

@[simp] lemma shortCurve_negY (a₄ a₆ x y : F) :
    (shortCurve F a₄ a₆).negY x y = -y := by
  simp [negY]

lemma shortCurve_equation_iff {a₄ a₆ x y : F} :
    (shortCurve F a₄ a₆).Equation x y ↔ y ^ 2 = x ^ 3 + a₄ * x + a₆ := by
  rw [equation_iff]
  simp

/-- Nonsingularity on a short curve, characteristic-free: the equation
holds and one of the two partial derivatives `3x² + a₄`, `2y` is nonzero. -/
lemma shortCurve_nonsingular_iff {a₄ a₆ x y : F} :
    (shortCurve F a₄ a₆).Nonsingular x y ↔
      y ^ 2 = x ^ 3 + a₄ * x + a₆ ∧ (3 * x ^ 2 + a₄ ≠ 0 ∨ 2 * y ≠ 0) := by
  rw [nonsingular_iff', shortCurve_equation_iff]
  simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄]
  rw [show (0 * y - (3 * x ^ 2 + 2 * 0 * x + a₄) : F) = -(3 * x ^ 2 + a₄) by ring,
    show (2 * y + 0 * x + 0 : F) = 2 * y by ring, neg_ne_zero]

/-! ## Nonsingularity transfer

Both directions are direct: equation and partials scale by `u⁶`, `u⁴`,
`u³`. No discriminant, no characteristic assumption. -/

variable {a₄ a₆ u : F}

lemma nonsingular_scale (hu : u ≠ 0) {x y : F}
    (h : (shortCurve F a₄ a₆).Nonsingular x y) :
    (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  rw [shortCurve_nonsingular_iff] at h ⊢
  obtain ⟨heq, hd⟩ := h
  refine ⟨by linear_combination u ^ 6 * heq, ?_⟩
  rcases hd with h1 | h2
  · left
    rw [show (3 * (u ^ 2 * x) ^ 2 + u ^ 4 * a₄ : F) = u ^ 4 * (3 * x ^ 2 + a₄) by ring]
    exact mul_ne_zero (pow_ne_zero 4 hu) h1
  · right
    rw [show (2 * (u ^ 3 * y) : F) = u ^ 3 * (2 * y) by ring]
    exact mul_ne_zero (pow_ne_zero 3 hu) h2

lemma nonsingular_unscale (hu : u ≠ 0) {x y : F}
    (h : (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Nonsingular x y) :
    (shortCurve F a₄ a₆).Nonsingular (x / u ^ 2) (y / u ^ 3) := by
  rw [shortCurve_nonsingular_iff] at h ⊢
  obtain ⟨heq, hd⟩ := h
  refine ⟨?_, ?_⟩
  · field_simp
    linear_combination heq
  · rcases hd with h1 | h2
    · left
      intro hc
      apply h1
      rw [show (3 * x ^ 2 + u ^ 4 * a₄ : F) = u ^ 4 * (3 * (x / u ^ 2) ^ 2 + a₄) by
        field_simp, hc, mul_zero]
    · right
      intro hc
      apply h2
      rw [show (2 * y : F) = u ^ 3 * (2 * (y / u ^ 3)) by field_simp, hc, mul_zero]

/-! ## Covariance of the group-law formulas -/

section Formulas

lemma addX_scale (x₁ x₂ ℓ : F) :
    (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).addX (u ^ 2 * x₁) (u ^ 2 * x₂) (u * ℓ)
      = u ^ 2 * (shortCurve F a₄ a₆).addX x₁ x₂ ℓ := by
  simp only [addX, shortCurve_a₁, shortCurve_a₂]
  ring

lemma addY_scale (x₁ x₂ y₁ ℓ : F) :
    (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).addY
        (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u * ℓ)
      = u ^ 3 * (shortCurve F a₄ a₆).addY x₁ x₂ y₁ ℓ := by
  simp only [addY, negAddY, negY, addX, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃]
  ring

variable [DecidableEq F]

/-- The slope is covariant of weight `1` under `(x, y) ↦ (u²x, u³y)`, in
all three cases of its definition (secant, tangent, vertical — the latter
two including the degenerate denominators, since `Lean`'s `x / 0 = 0` is
scale-invariant). -/
lemma slope_scale (hu : u ≠ 0) (x₁ x₂ y₁ y₂ : F) :
    (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).slope
        (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂)
      = u * (shortCurve F a₄ a₆).slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = (shortCurve F a₄ a₆).negY x₁ y₂
    · have hy' : u ^ 3 * y₁ =
          (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).negY (u ^ 2 * x₁) (u ^ 3 * y₂) := by
        rw [shortCurve_negY] at hy ⊢
        rw [hy]; ring
      rw [slope_of_Y_eq rfl hy, slope_of_Y_eq rfl hy', mul_zero]
    · have hy' : u ^ 3 * y₁ ≠
          (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).negY (u ^ 2 * x₁) (u ^ 3 * y₂) := by
        rw [shortCurve_negY] at hy ⊢
        intro hc
        exact hy <| mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hc)
      rw [slope_of_Y_ne rfl hy, slope_of_Y_ne rfl hy']
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₄, shortCurve_negY,
        mul_zero, zero_mul, add_zero, sub_zero]
      rw [show (3 * (u ^ 2 * x₁) ^ 2 + u ^ 4 * a₄ : F)
            = u ^ 3 * (u * (3 * x₁ ^ 2 + a₄)) by ring,
        show (u ^ 3 * y₁ - -(u ^ 3 * y₁) : F) = u ^ 3 * (y₁ - -y₁) by ring,
        mul_div_mul_left _ _ (pow_ne_zero 3 hu), mul_div_assoc]
  · have hx' : u ^ 2 * x₁ ≠ u ^ 2 * x₂ :=
      fun hc => hx (mul_left_cancel₀ (pow_ne_zero 2 hu) hc)
    rw [slope_of_X_ne hx, slope_of_X_ne hx',
      show (u ^ 3 * y₁ - u ^ 3 * y₂ : F) = u ^ 2 * (u * (y₁ - y₂)) by ring,
      show (u ^ 2 * x₁ - u ^ 2 * x₂ : F) = u ^ 2 * (x₁ - x₂) by ring,
      mul_div_mul_left _ _ (pow_ne_zero 2 hu), mul_div_assoc]

end Formulas

/-! ## The point maps and the isomorphism -/

/-- The forward map `(x, y) ↦ (u²x, u³y)` on points. -/
def scalePoint (hu : u ≠ 0) :
    (shortCurve F a₄ a₆).Point → (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Point
  | .zero => .zero
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) (nonsingular_scale hu h)

/-- The inverse map `(x, y) ↦ (x/u², y/u³)` on points. -/
def unscalePoint (hu : u ≠ 0) :
    (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Point → (shortCurve F a₄ a₆).Point
  | .zero => .zero
  | .some x y h => .some (x / u ^ 2) (y / u ^ 3) (nonsingular_unscale hu h)

@[simp] lemma scalePoint_zero (hu : u ≠ 0) :
    scalePoint (a₄ := a₄) (a₆ := a₆) hu 0 = 0 := rfl

@[simp] lemma unscale_scale (hu : u ≠ 0) (P : (shortCurve F a₄ a₆).Point) :
    unscalePoint hu (scalePoint hu P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [scalePoint, unscalePoint]
    congr 1
    · exact mul_div_cancel_left₀ x (pow_ne_zero 2 hu)
    · exact mul_div_cancel_left₀ y (pow_ne_zero 3 hu)

@[simp] lemma scale_unscale (hu : u ≠ 0)
    (P : (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Point) :
    scalePoint hu (unscalePoint hu P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [unscalePoint, scalePoint]
    congr 1
    · exact mul_div_cancel₀ x (pow_ne_zero 2 hu)
    · exact mul_div_cancel₀ y (pow_ne_zero 3 hu)

variable [DecidableEq F]

lemma scalePoint_add (hu : u ≠ 0) (P Q : (shortCurve F a₄ a₆).Point) :
    scalePoint hu (P + Q) = scalePoint hu P + scalePoint hu Q := by
  cases P with
  | zero =>
    show scalePoint hu Q = .zero + scalePoint hu Q
    rw [← Point.zero_def, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show scalePoint hu (.some x₁ y₁ h₁) = scalePoint hu (.some x₁ y₁ h₁) + .zero
      rw [← Point.zero_def, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = (shortCurve F a₄ a₆).negY x₂ y₂
      · -- cancellation case: both sums are `0`
        obtain ⟨hx, hy⟩ := hxy
        rw [shortCurve_negY] at hy
        have hx' : u ^ 2 * x₁ = u ^ 2 * x₂ := by rw [hx]
        have hy' : u ^ 3 * y₁ =
            (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
          rw [shortCurve_negY, hy]; ring
        rw [Point.add_of_Y_eq hx (by rw [shortCurve_negY]; exact hy)]
        simp only [scalePoint]
        exact (Point.add_of_Y_eq hx' hy').symm
      · -- generic case: transport the addition formulas
        have hxy' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧ u ^ 3 * y₁ =
            (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
          rintro ⟨hx, hy⟩
          rw [shortCurve_negY] at hy
          refine hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) hx, ?_⟩
          rw [shortCurve_negY]
          exact mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hy)
        rw [Point.add_some hxy]
        simp only [scalePoint]
        rw [Point.add_some hxy']
        congr 1
        · rw [slope_scale hu, addX_scale]
        · rw [slope_scale hu, addY_scale]

/-- **Main theorem.** Over any field `F` (no characteristic assumption)
and for any `u ≠ 0`, the admissible change of variables
`(x, y) ↦ (u²x, u³y)` is an isomorphism of affine point groups
`y² = x³ + a₄x + a₆  ≃+  y² = x³ + (u⁴a₄)x + (u⁶a₆)`.

This is the point-level content of Silverman AEC III §1 Table 3.1 with
`r = s = t = 0`, which Mathlib's `WeierstrassCurve.VariableChange` (an
action on curves only) does not provide. -/
def scaleEquiv (a₄ a₆ : F) {u : F} (hu : u ≠ 0) :
    (shortCurve F a₄ a₆).Point ≃+ (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Point where
  toFun := scalePoint hu
  invFun := unscalePoint hu
  left_inv := unscale_scale hu
  right_inv := scale_unscale hu
  map_add' := scalePoint_add hu

/-! ## Corollaries: the congruent-number curve family -/

section CongruentNumber

/-- The congruent-number curve `E_n : y² = x³ - n²x` as a short
Weierstrass curve. -/
def congrCurve (n : ℚ) : WeierstrassCurve.Affine ℚ :=
  shortCurve ℚ (-(n ^ 2)) 0

@[simp] lemma congrCurve_a₁ (n : ℚ) : (congrCurve n).a₁ = 0 := rfl
@[simp] lemma congrCurve_a₂ (n : ℚ) : (congrCurve n).a₂ = 0 := rfl
@[simp] lemma congrCurve_a₃ (n : ℚ) : (congrCurve n).a₃ = 0 := rfl
@[simp] lemma congrCurve_a₄ (n : ℚ) : (congrCurve n).a₄ = -(n ^ 2) := rfl
@[simp] lemma congrCurve_a₆ (n : ℚ) : (congrCurve n).a₆ = 0 := rfl

@[simp] lemma congrCurve_negY (n x y : ℚ) : (congrCurve n).negY x y = -y :=
  shortCurve_negY _ _ x y

lemma congrCurve_Δ (n : ℚ) : (congrCurve n).Δ = 64 * n ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    congrCurve_a₁, congrCurve_a₂, congrCurve_a₃, congrCurve_a₄, congrCurve_a₆]
  ring

instance congrCurve_isElliptic {n : ℚ} (hn : n ≠ 0) : (congrCurve n).IsElliptic where
  isUnit := Ne.isUnit (by
    rw [congrCurve_Δ]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hn))

/-- Scaling `(a₄, a₆) = (-(n²), 0)` by `u = 2` lands exactly on the
congruent-number curve of parameter `4n`. -/
lemma shortCurve_scale_congrCurve (n : ℚ) :
    shortCurve ℚ ((2 : ℚ) ^ 4 * -(n ^ 2)) ((2 : ℚ) ^ 6 * 0) = congrCurve (4 * n) := by
  rw [show (2 : ℚ) ^ 4 * -(n ^ 2) = -((4 * n) ^ 2) by ring, mul_zero]
  rfl

/-- **Corollary.** `E_n ≃+ E_{4n}` for the congruent-number curve family:
the map `(x, y) ↦ (4x, 8y)` is an additive group isomorphism between the
affine point groups of `y² = x³ - n²x` and `y² = x³ - (4n)²x` — the
`u = 2` instance of `scaleEquiv`.

No hypothesis on `n`: the direct nonsingularity transfer eliminates the
`n ≠ 0` that the discriminant/`IsElliptic` route required, so this also
covers the singular curve `y² = x³` at `n = 0`. -/
def congrCurveIso (n : ℚ) :
    (congrCurve n).Point ≃+ (congrCurve (4 * n)).Point :=
  shortCurve_scale_congrCurve n ▸ scaleEquiv (-(n ^ 2)) 0 (two_ne_zero)

end CongruentNumber

end Xlib.ShortCurveScaling
