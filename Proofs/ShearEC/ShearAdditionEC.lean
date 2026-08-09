import Mathlib
import ShearEC.ShearAddition
import ShearEC.ShearInversionLB

/-!
# Grounding the shear-addition map in Mathlib's Weierstrass group law

`ShearEC.ShearAddition` studies the "remaining transformation" of affine
elliptic-curve point addition once the slope is in hand:

  `(c, λ) ↦ (a - c, c·λ - b) = (X, Y)`, with `c = a - X`,

and proves reversibility/impossibility results about computing it with
multiply-add shears. This file closes the "are we lower-bounding the right
map?" gap: over any Weierstrass curve `W` with `a₁ = a₂ = a₃ = 0` (every
short curve `y² = x³ + a₄x + a₆`; secp256k1 is `a₄ = 0, a₆ = 7`), those
formulas are **provably the coordinates of Mathlib's verified group law** on
the chord locus `x₁ ≠ x₂`:

* `slope_eq`, `addX_eq`, `negY_eq`, `addY_eq` — Mathlib's `W.slope`,
  `W.addX`, `W.negY`, `W.addY` reduce to the classical
  `λ = (y - b)/(x - a)`, `X = λ² - a - x`, `-P = (a, -b)`,
  `Y = λ(a - X) - b`.
* `some_add_some` — `(a, b) + (x, y)` *is* `Point.some X Y _` with exactly
  those coordinates.
* `singleShear_computes_add` — the concrete one-shear circuit
  `ShearEC.ShearAddition.singleShear`, fed `(c, λ, 0)` with `c = a - W.addX …`,
  outputs Mathlib's `(W.addX …, W.addY …)` (plus the `λ`-garbage register).
* `c_eq_zero_iff_add_eq_neg` — the exceptional fibre of the impossibility
  argument is geometric: `c = 0 ↔ P + Q = -P`.
* `c_eq_zero_iff_eq_neg_two_smul` — via Mathlib's proven `AddCommGroup`
  structure: `c = 0 ↔ Q = -(2 • P)`.

Everything is stated for the chord case `a ≠ x` — exactly the domain of the
shear map; the tangent (doubling) case is a different formula and outside
this map's domain by design. Nothing below touches `a₄` or `a₆`.

Note: Mathlib has the *predicate* `WeierstrassCurve.IsShortNF` (`a₁ = a₂ =
a₃ = 0`, in `Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean`) with
simp lemmas for the standard quantities `b₂, …, Δ, j` — but no bridge from it
to the affine `slope`/`addX`/`addY`/`negY` formula API, no short-curve
constructor, and no secp256k1 instantiation; that bridge is what this file
provides (via explicit `a₁ = 0` … hypotheses, which `IsShortNF` supplies).
-/

namespace ShearEC.ShearAdditionEC

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} {a b x y : F}

section Formulas

/-- On the chord locus, Mathlib's slope is the classical `λ = (y - b)/(x - a)`
for `P = (a, b)`, `Q = (x, y)`. (Note Mathlib's argument order `x₁ x₂ y₁ y₂`.) -/
lemma slope_eq [DecidableEq F] (hx : a ≠ x) :
    W.slope a x b y = (y - b) / (x - a) := by
  rw [slope_of_X_ne hx, ← neg_sub y b, ← neg_sub x a, neg_div_neg_eq]

/-- `X = λ² - a - x` when `a₁ = a₂ = 0`. -/
lemma addX_eq (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (ℓ : F) :
    W.addX a x ℓ = ℓ ^ 2 - a - x := by
  simp only [addX, h1, h2]
  ring

/-- `-(a, b) = (a, -b)` when `a₁ = a₃ = 0`. -/
lemma negY_eq (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) : W.negY a b = -b := by
  simp only [negY, h1, h3]
  ring

/-- `Y = λ(a - X) - b` when `a₁ = a₃ = 0`. -/
lemma addY_eq (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (ℓ : F) :
    W.addY a x b ℓ = ℓ * (a - W.addX a x ℓ) - b := by
  simp only [addY, negAddY, negY, h1, h3]
  ring

/-- `Y = c·λ - b` where `c = a - X`: the second output of the shear-addition
map of `ShearEC.ShearAddition`. -/
lemma addY_eq_c_mul (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (ℓ : F) :
    W.addY a x b ℓ = (a - W.addX a x ℓ) * ℓ - b := by
  rw [addY_eq h1 h3 ℓ, mul_comm]

/-- **The one-shear circuit computes the verified group law.** Feeding the
concrete single-shear realisation `ShearEC.ShearAddition.singleShear` the chord
offset `c = a - W.addX …` and the slope `λ`, its first two registers hold
exactly Mathlib's `(W.addX …, W.addY …)` — and the third holds the
`λ`-garbage that `ShearEC.ShearAddition.ancilla_carries_lambda` proves is
unavoidable.

Input-model caveat: `c = a - W.addX … = 2a + x - λ²` is quadratic in `λ`, so
`(x, λ) ↦ (c, λ)` is not affine and forming `c` costs one further shear (the
`λ·λ` square); the one-shear count is specific to the c-given input model
(the lower bounds, which grant `c` for free, only get stronger). -/
theorem singleShear_computes_add (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (ℓ : F) :
    ShearEC.ShearAddition.singleShear a b (a - W.addX a x ℓ, ℓ, 0)
      = (W.addX a x ℓ, W.addY a x b ℓ, ℓ) := by
  rw [ShearEC.ShearAddition.singleShear_zero]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · show a - (a - W.addX a x ℓ) = W.addX a x ℓ
    ring
  · show (a - W.addX a x ℓ) * ℓ - b = W.addY a x b ℓ
    rw [addY_eq_c_mul h1 h3 ℓ]

end Formulas

section GroupLaw

variable [DecidableEq F]

/-- **The exact correspondence.** For `P = (a, b)`, `Q = (x, y)` with
`a ≠ x` on a curve with `a₁ = a₂ = a₃ = 0`, Mathlib's verified group law
lands on the classical chord coordinates `X = λ² - a - x`,
`Y = λ(a - X) - b`. The nonsingular witness of the target is an arbitrary
hypothesis: by proof irrelevance it does not matter, and it is inhabited by
`nonsingular_add`. -/
theorem some_add_some (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0)
    (hP : W.Nonsingular a b) (hQ : W.Nonsingular x y)
    (hx : a ≠ x) {ℓ X Y : F} (hl : ℓ = W.slope a x b y)
    (hX : X = ℓ ^ 2 - a - x) (hY : Y = ℓ * (a - X) - b)
    {hR : W.Nonsingular X Y} :
    Point.some a b hP + Point.some x y hQ = Point.some X Y hR := by
  rw [Point.add_of_X_ne hx]
  have hX' : W.addX a x (W.slope a x b y) = X := by
    rw [hX, hl, addX_eq h1 h2]
  have hY' : W.addY a x b (W.slope a x b y) = Y := by
    rw [hY, hX, hl, addY_eq h1 h3, addX_eq h1 h2]
  simp only [Point.some.injEq]
  exact ⟨hX', hY'⟩

/-- **The exceptional fibre is geometric.** The fibre `c = 0` on which the
shear-addition impossibility (`no_reversible_clean_shear_addition`) pivots
is exactly the locus where the verified group law gives `P + Q = -P`. -/
theorem c_eq_zero_iff_add_eq_neg (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (hP : W.Nonsingular a b) (hQ : W.Nonsingular x y) (hx : a ≠ x) :
    a - W.addX a x (W.slope a x b y) = 0
      ↔ Point.some a b hP + Point.some x y hQ = -Point.some a b hP := by
  rw [Point.add_of_X_ne hx, Point.neg_some, Point.some.injEq, sub_eq_zero]
  constructor
  · intro hc
    have hX : W.addX a x (W.slope a x b y) = a := hc.symm
    refine ⟨hX, ?_⟩
    rw [addY_eq h1 h3, negY_eq h1 h3, hX]
    ring
  · intro hc
    exact hc.1.symm

/-- **In the verified group: `c = 0 ↔ Q = -2P`.** Uses Mathlib's proven
associativity (`AddCommGroup W.Point`); this is the crisp geometric
description of the exceptional fibre. -/
theorem c_eq_zero_iff_eq_neg_two_smul (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (hP : W.Nonsingular a b) (hQ : W.Nonsingular x y) (hx : a ≠ x) :
    a - W.addX a x (W.slope a x b y) = 0
      ↔ Point.some x y hQ = -(2 • Point.some a b hP) := by
  rw [c_eq_zero_iff_add_eq_neg h1 h3 hP hQ hx]
  constructor
  · intro h
    have hz : 2 • Point.some a b hP + Point.some x y hQ = 0 := by
      rw [two_smul]
      calc Point.some a b hP + Point.some a b hP + Point.some x y hQ
          = Point.some a b hP + Point.some x y hQ + Point.some a b hP := by
            abel
        _ = -Point.some a b hP + Point.some a b hP := by rw [h]
        _ = 0 := neg_add_cancel _
    exact eq_neg_of_add_eq_zero_right hz
  · intro h
    rw [h, two_smul]
    abel

end GroupLaw

section ShortCurve

/-- The short Weierstrass curve `y² = x³ + a₄x + a₆` over any commutative
ring; all coefficient hypotheses above hold by `rfl`. secp256k1 is
`shortCurve _ 0 7` over `ZMod (2^256 - 2^32 - 977)`. -/
def shortCurve (R : Type*) [CommRing R] (a₄ a₆ : R) :
    WeierstrassCurve.Affine R :=
  ⟨0, 0, 0, a₄, a₆⟩

@[simp] lemma shortCurve_a₁ (a₄ a₆ : F) : (shortCurve F a₄ a₆).a₁ = 0 := rfl

@[simp] lemma shortCurve_a₂ (a₄ a₆ : F) : (shortCurve F a₄ a₆).a₂ = 0 := rfl

@[simp] lemma shortCurve_a₃ (a₄ a₆ : F) : (shortCurve F a₄ a₆).a₃ = 0 := rfl

/-- The correspondence, instantiated: on any short curve the verified group
law on the chord locus is exactly the `(X, Y) = (λ² - a - x, λ(a - X) - b)`
map whose shear complexity `ShearEC.ShearAddition` analyses. -/
theorem shortCurve_some_add_some [DecidableEq F] {a₄ a₆ : F}
    (hP : (shortCurve F a₄ a₆).Nonsingular a b)
    (hQ : (shortCurve F a₄ a₆).Nonsingular x y) (hx : a ≠ x)
    {ℓ X Y : F} (hl : ℓ = (shortCurve F a₄ a₆).slope a x b y)
    (hX : X = ℓ ^ 2 - a - x) (hY : Y = ℓ * (a - X) - b)
    {hR : (shortCurve F a₄ a₆).Nonsingular X Y} :
    Point.some a b hP + Point.some x y hQ = Point.some X Y hR :=
  some_add_some rfl rfl rfl hP hQ hx hl hX hY

end ShortCurve

section Secp256k1

open ShearEC.ShearInversionLB in
/-- **secp256k1** as a Weierstrass curve: `y² = x³ + 7` over
`F_p`, `p = 2^256 - 2^32 - 977`. -/
def secp256k1 : WeierstrassCurve.Affine (ZMod secp256k1P) :=
  shortCurve _ 0 7

open ShearEC.ShearInversionLB in
/-- **The secp256k1 payoff**: on the actual bitcoin curve, the group law on
the chord locus is exactly the `(X, Y) = (λ² - a - x, λ(a - X) - b)` map of
`ShearEC.ShearAddition` — so every reversibility/lower-bound statement about
that map is a statement about the real secp256k1 point addition. -/
theorem secp256k1_some_add_some [Fact (Nat.Prime secp256k1P)]
    {a b x y : ZMod secp256k1P}
    (hP : secp256k1.Nonsingular a b) (hQ : secp256k1.Nonsingular x y)
    (hx : a ≠ x) {ℓ X Y : ZMod secp256k1P} (hl : ℓ = secp256k1.slope a x b y)
    (hX : X = ℓ ^ 2 - a - x) (hY : Y = ℓ * (a - X) - b)
    {hR : secp256k1.Nonsingular X Y} :
    Point.some a b hP + Point.some x y hQ = Point.some X Y hR :=
  some_add_some rfl rfl rfl hP hQ hx hl hX hY

end Secp256k1

end ShearEC.ShearAdditionEC
