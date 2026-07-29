import Mathlib
import ShearEC.ShortCurveScaling

/-!
# Point-group isomorphism of Weierstrass curves under a full admissible change

For any field `F` and any admissible change of variables
`C = (u, r, s, t) : WeierstrassCurve.VariableChange F` (Silverman, *The
Arithmetic of Elliptic Curves*, III §1 Table 3.1), the substitution
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` carries the affine points of the
transformed curve `C • W` onto the affine points of `W` and induces an
**isomorphism of the affine point groups**:

* `pointEquiv W C : (C • W).toAffine.Point ≃+ W.toAffine.Point`, over any
  field, with **no characteristic assumption** and no nonsingularity
  hypothesis on the curve `W` itself (Mathlib's group law lives on the
  nonsingular locus of an arbitrary Weierstrass cubic).

The forward direction is deliberately the division-free substitution: it
maps points of the *transformed* curve `C • W` to points of the original
`W`, since Mathlib's `C • W` has coefficients `aᵢ' = u⁻ⁱ·(…)`.

## Mathlib gap

Mathlib's `WeierstrassCurve.VariableChange` acts on *curves* only
(`variableChange_a₁ … variableChange_j`); it provides no map of points.
The only point-level lemma is `Affine.nonsingular_iff_variableChange`
(the pure translation `u = 1, s = 0` used to recentre a point), and the
coordinate-model `AddEquiv`s (Jacobian/projective ↔ affine) are
same-curve only.  `ShearEC.ShortCurveScaling.scaleEquiv` covers the
`r = s = t = 0` diagonal-scaling case on short curves; this file proves
the general statement and recovers that one (`shortScaleEquiv`).

## Proof skeleton

Everything reduces to five *inverse coefficient relations*
`coeff_a₁ … coeff_a₆` (each `W.aᵢ` written in terms of `(C • W).aᵢ`,
obtained from `variableChange_aᵢ` by clearing the unit inverse once via
`Units.mul_inv`), after which every covariance identity is a polynomial
identity closed by `ring`:

* equation transfer: `W(φ(x,y)) = u⁶ · (C • W)(x,y)` (`equation_change`);
* nonsingularity transfer, direct from `nonsingular_iff'`: the partial
  derivatives transform *triangularly*, `∂ₓ ∘ φ = u⁴∂ₓ' - s·(u³∂ᵧ')` and
  `∂ᵧ ∘ φ = u³∂ᵧ'` — the disjunction of nonvanishing transfers by cases,
  with no discriminant and no characteristic hypothesis
  (`nonsingular_change_iff`);
* `negY`, `addX`, `addY` equivariance and the slope covariance
  `W.slope (φP) (φQ) = u · (C • W).slope P Q + s` (`slope_change`; unlike
  the `s = 0` case this needs the on-curve hypotheses, which rule out the
  degenerate vertical-tangent subcase via `Y_eq_of_Y_ne`).

All statements use a variable `W : WeierstrassCurve.Affine F`; since
`Affine F` and `toAffine` are reducible identity abbreviations, the
resulting `pointEquiv` definitionally has the advertised type
`(C • W).toAffine.Point ≃+ W.toAffine.Point` for `W : WeierstrassCurve F`.

## Functoriality API

`changeX_one`, `changeY_one`, `changeX_mul`, `changeY_mul` express
`φ₁ = id` and `φ_{C * C'} = φ_{C'} ∘ φ_C` at the coordinate level, and
`changePoint_one_some` / `changePoint_mul_some` lift them to point level
on `.some x y h`.  The transported statements
`pointEquiv W 1 = one_smul ▸ AddEquiv.refl _` are deliberately not
stated: the `▸`-cast on the *type* of the equiv makes them unusable;
the coordinate-level lemmas are the transport-free content.
-/

noncomputable section

namespace ShearEC.VariableChangePointEquiv

open WeierstrassCurve
open WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-! ## The forward substitution and its inverse -/

/-- The `X`-coordinate of the division-free substitution
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` from points of `C • W` to points
of `W`. -/
def changeX (C : VariableChange F) (x : F) : F :=
  (C.u : F) ^ 2 * x + C.r

/-- The `Y`-coordinate of the division-free substitution
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)`. -/
def changeY (C : VariableChange F) (x y : F) : F :=
  (C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t

/-- The `X`-coordinate of the inverse substitution
`(X, Y) ↦ ((X - r)/u², (Y - s(X - r) - t)/u³)`. -/
def invChangeX (C : VariableChange F) (x : F) : F :=
  (x - C.r) / (C.u : F) ^ 2

/-- The `Y`-coordinate of the inverse substitution. -/
def invChangeY (C : VariableChange F) (x y : F) : F :=
  (y - C.s * (x - C.r) - C.t) / (C.u : F) ^ 3

section RoundTrip

variable (C : VariableChange F)

@[simp] lemma changeX_invChangeX (x : F) : changeX C (invChangeX C x) = x := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [changeX, invChangeX]
  field_simp
  ring

@[simp] lemma changeY_invChangeY (x y : F) :
    changeY C (invChangeX C x) (invChangeY C x y) = y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [changeY, invChangeX, invChangeY]
  field_simp
  ring

@[simp] lemma invChangeX_changeX (x : F) : invChangeX C (changeX C x) = x := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [changeX, invChangeX]
  field_simp
  ring

@[simp] lemma invChangeY_changeY (x y : F) :
    invChangeY C (changeX C x) (changeY C x y) = y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [changeX, changeY, invChangeY]
  field_simp
  ring

end RoundTrip

/-! ## Inverse coefficient relations

Each original coefficient `W.aᵢ` in terms of the transformed ones,
derived from `variableChange_aᵢ` by clearing the unit inverse once via
`Units.mul_inv`.  These hold over any commutative ring; everything
downstream is `rw [coeff_*] … ring`. -/

variable (W : Affine F) (C : VariableChange F)

lemma coeff_a₁ : W.a₁ = (C.u : F) * (C • W).a₁ - 2 * C.s := by
  rw [variableChange_a₁]
  linear_combination (-(W.a₁ + 2 * C.s)) * C.u.mul_inv

lemma coeff_a₂ : W.a₂ = (C.u : F) ^ 2 * (C • W).a₂ + C.s * W.a₁ - 3 * C.r + C.s ^ 2 := by
  rw [variableChange_a₂]
  linear_combination (-(W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)) *
    pow_mul_pow_eq_one 2 C.u.mul_inv

lemma coeff_a₃ : W.a₃ = (C.u : F) ^ 3 * (C • W).a₃ - C.r * W.a₁ - 2 * C.t := by
  rw [variableChange_a₃]
  linear_combination (-(W.a₃ + C.r * W.a₁ + 2 * C.t)) * pow_mul_pow_eq_one 3 C.u.mul_inv

lemma coeff_a₄ : W.a₄ = (C.u : F) ^ 4 * (C • W).a₄ + C.s * W.a₃ - 2 * C.r * W.a₂
    + (C.t + C.r * C.s) * W.a₁ - 3 * C.r ^ 2 + 2 * C.s * C.t := by
  rw [variableChange_a₄]
  linear_combination (-(W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁
    + 3 * C.r ^ 2 - 2 * C.s * C.t)) * pow_mul_pow_eq_one 4 C.u.mul_inv

lemma coeff_a₆ : W.a₆ = (C.u : F) ^ 6 * (C • W).a₆ - C.r * W.a₄ - C.r ^ 2 * W.a₂
    - C.r ^ 3 + C.t * W.a₃ + C.t ^ 2 + C.r * C.t * W.a₁ := by
  rw [variableChange_a₆]
  linear_combination (-(W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
    - C.t ^ 2 - C.r * C.t * W.a₁)) * pow_mul_pow_eq_one 6 C.u.mul_inv

/-! ## Equation and nonsingularity transfer -/

/-- The Weierstrass polynomial of `W` at the substituted point is `u⁶`
times the Weierstrass polynomial of `C • W`. -/
lemma equation_change_key (x y : F) :
    changeY C x y ^ 2 + W.a₁ * changeX C x * changeY C x y + W.a₃ * changeY C x y
        - (changeX C x ^ 3 + W.a₂ * changeX C x ^ 2 + W.a₄ * changeX C x + W.a₆)
      = (C.u : F) ^ 6 * (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y
          - (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) := by
  rw [coeff_a₆ W C, coeff_a₄ W C, coeff_a₃ W C, coeff_a₂ W C, coeff_a₁ W C]
  simp only [changeX, changeY]
  ring

lemma equation_change (x y : F) :
    W.Equation (changeX C x) (changeY C x y) ↔ (C • W : Affine F).Equation x y := by
  rw [equation_iff', equation_iff', equation_change_key W C x y, mul_eq_zero]
  exact or_iff_right (pow_ne_zero 6 C.u.ne_zero)

/-- The `X`-partial transforms *triangularly*:
`∂ₓ ∘ φ = u⁴·∂ₓ' - s·(u³·∂ᵧ')` (shapes as in `nonsingular_iff'`). -/
lemma polynomialX_change_key (x y : F) :
    W.a₁ * changeY C x y - (3 * changeX C x ^ 2 + 2 * W.a₂ * changeX C x + W.a₄)
      = (C.u : F) ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄))
        - C.s * ((C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃)) := by
  rw [coeff_a₄ W C, coeff_a₃ W C, coeff_a₂ W C, coeff_a₁ W C]
  simp only [changeX, changeY]
  ring

/-- The `Y`-partial scales diagonally: `∂ᵧ ∘ φ = u³·∂ᵧ'`. -/
lemma polynomialY_change_key (x y : F) :
    2 * changeY C x y + W.a₁ * changeX C x + W.a₃
      = (C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  rw [coeff_a₃ W C, coeff_a₁ W C]
  simp only [changeX, changeY]
  ring

/-- Transfer of the nonvanishing disjunction along the triangular
transformation of the partials. -/
private lemma triangular_ne_iff {u s A B : F} (hu : u ≠ 0) :
    (u ^ 4 * A - s * (u ^ 3 * B) ≠ 0 ∨ u ^ 3 * B ≠ 0) ↔ (A ≠ 0 ∨ B ≠ 0) := by
  constructor
  · rintro (h | h)
    · by_cases hB : B = 0
      · exact .inl fun hA => h (by rw [hA, hB]; ring)
      · exact .inr hB
    · exact .inr fun hB => h (by rw [hB, mul_zero])
  · rintro (h | h)
    · by_cases hB : B = 0
      · left
        rw [hB, mul_zero, mul_zero, sub_zero]
        exact mul_ne_zero (pow_ne_zero 4 hu) h
      · exact .inr (mul_ne_zero (pow_ne_zero 3 hu) hB)
    · exact .inr (mul_ne_zero (pow_ne_zero 3 hu) h)

/-- **Nonsingularity transfer**, both directions, characteristic-free:
direct from `nonsingular_iff'`, with no discriminant and no
`IsElliptic`. -/
lemma nonsingular_change_iff (x y : F) :
    W.Nonsingular (changeX C x) (changeY C x y) ↔ (C • W : Affine F).Nonsingular x y := by
  rw [nonsingular_iff', nonsingular_iff', polynomialX_change_key W C x y,
    polynomialY_change_key W C x y]
  exact and_congr (equation_change W C x y) (triangular_ne_iff C.u.ne_zero)

lemma nonsingular_change {x y : F} (h : (C • W : Affine F).Nonsingular x y) :
    W.Nonsingular (changeX C x) (changeY C x y) :=
  (nonsingular_change_iff W C x y).mpr h

lemma nonsingular_invChange {x y : F} (h : W.Nonsingular x y) :
    (C • W : Affine F).Nonsingular (invChangeX C x) (invChangeY C x y) := by
  apply (nonsingular_change_iff W C _ _).mp
  rwa [changeX_invChangeX, changeY_invChangeY]

/-! ## Covariance of the group-law formulas -/

/-- `φ` commutes with negation:
`W.negY ∘ φ = φ ∘ ((C • W).negY)` in the `Y`-coordinate. -/
lemma negY_change (x y : F) :
    W.negY (changeX C x) (changeY C x y) = changeY C x ((C • W : Affine F).negY x y) := by
  simp only [negY, changeX, changeY]
  rw [coeff_a₃ W C, coeff_a₁ W C]
  ring

/-- The tangent-slope numerator at `φ(x, y)`: `N ∘ φ = u³·(u·N' + s·D')`
where `D' = y - (C • W).negY x y` is the transformed denominator. -/
lemma slope_num_change (x y : F) :
    3 * changeX C x ^ 2 + 2 * W.a₂ * changeX C x + W.a₄ - W.a₁ * changeY C x y
      = (C.u : F) ^ 3 * ((C.u : F) * (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄
            - (C • W).a₁ * y)
          + C.s * (y - (C • W : Affine F).negY x y)) := by
  simp only [negY, changeX, changeY]
  rw [coeff_a₄ W C, coeff_a₃ W C, coeff_a₂ W C, coeff_a₁ W C]
  ring

/-- The tangent-slope denominator at `φ(x, y)`: `D ∘ φ = u³·D'`. -/
lemma slope_den_change (x y : F) :
    changeY C x y - W.negY (changeX C x) (changeY C x y)
      = (C.u : F) ^ 3 * (y - (C • W : Affine F).negY x y) := by
  simp only [negY, changeX, changeY]
  rw [coeff_a₃ W C, coeff_a₁ W C]
  ring

lemma addX_change (x₁ x₂ ℓ : F) :
    W.addX (changeX C x₁) (changeX C x₂) ((C.u : F) * ℓ + C.s)
      = changeX C ((C • W : Affine F).addX x₁ x₂ ℓ) := by
  simp only [addX, changeX]
  rw [coeff_a₂ W C, coeff_a₁ W C]
  ring

lemma addY_change (x₁ x₂ y₁ ℓ : F) :
    W.addY (changeX C x₁) (changeX C x₂) (changeY C x₁ y₁) ((C.u : F) * ℓ + C.s)
      = changeY C ((C • W : Affine F).addX x₁ x₂ ℓ)
          ((C • W : Affine F).addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, negAddY, addX, negY, changeX, changeY]
  rw [coeff_a₃ W C, coeff_a₂ W C, coeff_a₁ W C]
  ring

section Slope

variable [DecidableEq F]

/-- **Slope covariance** of the full admissible change:
`W.slope (φP₁) (φP₂) = u · (C • W).slope P₁ P₂ + s`.

Unlike the `s = 0` scaling case this is *not* unconditional: in the
`Y_eq` branch both slopes are literally `0` by definition and the
relation would degenerate to `0 = s`.  The on-curve hypotheses `h₁ h₂`
kill the residual degenerate subcase (`x₁ = x₂`, `y₁ ≠ negY x₂ y₂`, yet
vertical tangent on both sides) via `Y_eq_of_Y_ne`. -/
lemma slope_change {x₁ x₂ y₁ y₂ : F} (h₁ : (C • W : Affine F).Equation x₁ y₁)
    (h₂ : (C • W : Affine F).Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W : Affine F).negY x₂ y₂)) :
    W.slope (changeX C x₁) (changeX C x₂) (changeY C x₁ y₁) (changeY C x₂ y₂)
      = (C.u : F) * (C • W : Affine F).slope x₁ x₂ y₁ y₂ + C.s := by
  by_cases hx : x₁ = x₂
  · -- tangent case: the equations force `y₁ = y₂`
    subst hx
    have hy : y₁ ≠ (C • W : Affine F).negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hy₂ : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hy₂
    have hy' : changeY C x₁ y₁ ≠ W.negY (changeX C x₁) (changeY C x₁ y₁) := by
      rw [negY_change]
      intro hc
      simp only [changeY] at hc
      exact hy (mul_left_cancel₀ (pow_ne_zero 3 C.u.ne_zero) (by linear_combination hc))
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, slope_num_change W C x₁ y₁,
      slope_den_change W C x₁ y₁, mul_div_mul_left _ _ (pow_ne_zero 3 C.u.ne_zero),
      add_div, mul_div_assoc, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hy)]
  · -- secant case
    have hx' : changeX C x₁ ≠ changeX C x₂ := fun hc => hx (by
      simp only [changeX] at hc
      exact mul_left_cancel₀ (pow_ne_zero 2 C.u.ne_zero) (by linear_combination hc))
    rw [slope_of_X_ne hx, slope_of_X_ne hx',
      show changeY C x₁ y₁ - changeY C x₂ y₂
          = (C.u : F) ^ 2 * ((C.u : F) * (y₁ - y₂) + C.s * (x₁ - x₂)) by
        simp only [changeY]; ring,
      show changeX C x₁ - changeX C x₂ = (C.u : F) ^ 2 * (x₁ - x₂) by
        simp only [changeX]; ring,
      mul_div_mul_left _ _ (pow_ne_zero 2 C.u.ne_zero), add_div, mul_div_assoc,
      mul_div_cancel_right₀ _ (sub_ne_zero.mpr hx)]

end Slope

/-! ## The point maps and the isomorphism -/

/-- The division-free forward map on points, from the transformed curve
to the original: `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def changePoint : (C • W : Affine F).Point → W.Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (nonsingular_change W C h)

/-- The inverse map on points:
`(x, y) ↦ ((x - r)/u², (y - s(x - r) - t)/u³)`. -/
def invChangePoint : W.Point → (C • W : Affine F).Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (nonsingular_invChange W C h)

@[simp] lemma changePoint_zero : changePoint W C .zero = .zero := rfl

@[simp] lemma changePoint_some {x y : F} (h : (C • W : Affine F).Nonsingular x y) :
    changePoint W C (.some x y h)
      = .some (changeX C x) (changeY C x y) (nonsingular_change W C h) := rfl

@[simp] lemma invChangePoint_changePoint (P : (C • W : Affine F).Point) :
    invChangePoint W C (changePoint W C P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [changePoint, invChangePoint]
    congr 1
    · exact invChangeX_changeX C x
    · exact invChangeY_changeY C x y

@[simp] lemma changePoint_invChangePoint (P : W.Point) :
    changePoint W C (invChangePoint W C P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [invChangePoint, changePoint]
    congr 1
    · exact changeX_invChangeX C x
    · exact changeY_invChangeY C x y

section Group

variable [DecidableEq F]

lemma changePoint_add (P Q : (C • W : Affine F).Point) :
    changePoint W C (P + Q) = changePoint W C P + changePoint W C Q := by
  cases P with
  | zero =>
    show changePoint W C Q = .zero + changePoint W C Q
    rw [← Point.zero_def, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show changePoint W C (.some x₁ y₁ h₁) = changePoint W C (.some x₁ y₁ h₁) + .zero
      rw [← Point.zero_def, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W : Affine F).negY x₂ y₂
      · -- cancellation case: both sums are `0`
        obtain ⟨hx, hy⟩ := hxy
        have hx' : changeX C x₁ = changeX C x₂ := by rw [hx]
        have hy' : changeY C x₁ y₁ = W.negY (changeX C x₂) (changeY C x₂ y₂) := by
          rw [negY_change, hy, hx]
        rw [Point.add_of_Y_eq hx hy]
        simp only [changePoint]
        exact (Point.add_of_Y_eq hx' hy').symm
      · -- generic case: transport the addition formulas
        have hxy' : ¬(changeX C x₁ = changeX C x₂ ∧
            changeY C x₁ y₁ = W.negY (changeX C x₂) (changeY C x₂ y₂)) := by
          rintro ⟨hx', hy'⟩
          have hx : x₁ = x₂ := by
            simp only [changeX] at hx'
            exact mul_left_cancel₀ (pow_ne_zero 2 C.u.ne_zero) (by linear_combination hx')
          refine hxy ⟨hx, ?_⟩
          rw [negY_change, hx] at hy'
          simp only [changeY] at hy'
          exact mul_left_cancel₀ (pow_ne_zero 3 C.u.ne_zero) (by linear_combination hy')
        rw [Point.add_some hxy]
        simp only [changePoint]
        rw [Point.add_some hxy']
        congr 1
        · rw [slope_change W C h₁.left h₂.left hxy, addX_change]
        · rw [slope_change W C h₁.left h₂.left hxy, addY_change]

/-- **Main theorem.** Over any field `F` (no characteristic assumption),
every admissible change of variables `C = (u, r, s, t)` induces an
isomorphism of affine point groups
`(C • W).toAffine.Point ≃+ W.toAffine.Point`, given on affine points by
the division-free substitution `(x, y) ↦ (u²x + r, u³y + u²sx + t)`.

This is the point-level content of Silverman AEC III §1 Table 3.1, which
Mathlib's `WeierstrassCurve.VariableChange` (an action on curves only)
does not provide; `ShearEC.ShortCurveScaling.scaleEquiv` is the
`r = s = t = 0` case. -/
def pointEquiv : (C • W : Affine F).Point ≃+ W.Point where
  toFun := changePoint W C
  invFun := invChangePoint W C
  left_inv := invChangePoint_changePoint W C
  right_inv := changePoint_invChangePoint W C
  map_add' := changePoint_add W C

@[simp] lemma pointEquiv_zero : pointEquiv W C .zero = .zero := rfl

@[simp] lemma pointEquiv_some {x y : F} (h : (C • W : Affine F).Nonsingular x y) :
    pointEquiv W C (.some x y h)
      = .some (changeX C x) (changeY C x y) (nonsingular_change W C h) := rfl

end Group

/-! ## Functoriality of the substitution -/

section Functoriality

@[simp] lemma changeX_one (x : F) : changeX (1 : VariableChange F) x = x := by
  simp [changeX, VariableChange.one_def]

@[simp] lemma changeY_one (x y : F) : changeY (1 : VariableChange F) x y = y := by
  simp [changeY, VariableChange.one_def]

/-- `φ_{C * C'} = φ_{C'} ∘ φ_C` in the `X`-coordinate (matching
`mul_smul : (C * C') • W = C • C' • W`). -/
lemma changeX_mul (C C' : VariableChange F) (x : F) :
    changeX (C * C') x = changeX C' (changeX C x) := by
  simp only [changeX, VariableChange.mul_def, Units.val_mul]
  ring

/-- `φ_{C * C'} = φ_{C'} ∘ φ_C` in the `Y`-coordinate. -/
lemma changeY_mul (C C' : VariableChange F) (x y : F) :
    changeY (C * C') x y = changeY C' (changeX C x) (changeY C x y) := by
  simp only [changeX, changeY, VariableChange.mul_def, Units.val_mul]
  ring

/-- `changePoint` at `C = 1` is the identity on coordinates. -/
lemma changePoint_one_some {x y : F}
    (h : ((1 : VariableChange F) • W : Affine F).Nonsingular x y) :
    changePoint W 1 (.some x y h) = .some x y (by rwa [one_smul] at h) := by
  simp only [changePoint]
  congr 1
  · exact changeX_one x
  · exact changeY_one x y

/-- `changePoint` at a product is the composite of the two
`changePoint`s, on `.some` points (the transport of the nonsingularity
proof along `mul_smul` lives in a proof position only). -/
lemma changePoint_mul_some (C C' : VariableChange F) {x y : F}
    (h : ((C * C') • W : Affine F).Nonsingular x y) :
    changePoint W (C * C') (.some x y h)
      = changePoint W C'
          (changePoint (C' • W) C (.some x y (by rwa [mul_smul] at h))) := by
  simp only [changePoint]
  congr 1
  · exact changeX_mul C C' x
  · exact changeY_mul C C' x y

end Functoriality

/-! ## Corollary: the unit-scaling case of `ShortCurveScaling` -/

section ShortCurve

open ShearEC.ShearAdditionEC (shortCurve)
open ShearEC.ShortCurveScaling (shortCurve_a₄ shortCurve_a₆)

/-- The unit-scaling change `⟨u, 0, 0, 0⟩` carries
`y² = x³ + u⁴a₄x + u⁶a₆` back to `y² = x³ + a₄x + a₆`. -/
lemma scale_smul_shortCurve (a₄ a₆ : F) {u : F} (hu : u ≠ 0) :
    (⟨Units.mk0 u hu, 0, 0, 0⟩ : VariableChange F)
        • shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)
      = shortCurve F a₄ a₆ := by
  have hu' : (u : F) ≠ 0 := hu
  ext <;>
    simp [variableChange_def, Units.val_inv_eq_inv_val, shortCurve] <;>
    field_simp

/-- Statement-level check: `pointEquiv` recovers the `u`-scaling
isomorphism `ShearEC.ShortCurveScaling.scaleEquiv`
`(shortCurve F a₄ a₆).Point ≃+ (shortCurve F (u⁴a₄) (u⁶a₆)).Point` as
the `C = ⟨u, 0, 0, 0⟩` special case. -/
def shortScaleEquiv [DecidableEq F] (a₄ a₆ : F) {u : F} (hu : u ≠ 0) :
    (shortCurve F a₄ a₆).Point ≃+ (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)).Point :=
  scale_smul_shortCurve a₄ a₆ hu ▸
    pointEquiv (shortCurve F (u ^ 4 * a₄) (u ^ 6 * a₆)) ⟨Units.mk0 u hu, 0, 0, 0⟩

end ShortCurve

end ShearEC.VariableChangePointEquiv
