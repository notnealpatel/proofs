/-
# Alpöge's counterexample to the Jacobian Conjecture in dimension 3

## Source

arXiv 2610.24889v1, M. de Bondt, "Alpöge's counterexample to the JC,
Economic Stabilization, and Zhao's Vanishing Conjecture".
Retrieved 2026-10-21 (`fetch 2610.24889v1`, LaTeX source).
The map is due to L. Alpöge (X post, 20 July 2026), cited in the paper as
`alpoge2026`.

Where: Section 1 (Introduction), subsections "The Base Mapping and
Volume-Preserving Transformation" and "Numerical Collision Universality and
Parameterized Loci"; restated in Section 2, "The Initial Three-Dimensional
Mapping".

Verbatim (Section 1):

> we examine Alpöge's original three-dimensional counterexample
> `F : ℂ^3 → ℂ^3`, defined as:
> `F_1 = (1+x_1 x_2)^3 x_3 + x_2^2(1+x_1 x_2)(4+3x_1 x_2)`,
> `F_2 = x_2 + 3x_1(1+x_1 x_2)^2 x_3 + 3x_1 x_2^2(4+3x_1 x_2)`,
> `F_3 = 2x_1 - 3x_1^2 x_2 - x_1^3 x_3`.
> Expanding the determinant of its Jacobian yields `det 𝒥(F) = -2`.

> `G_1 = x_1 - 3x_1^2 x_2 - x_1^3 x_3`,
> `G_2 = 3v^2 x_1 x_3 + (9v^2 - 6v - 2)x_2`,
> `G_3 = v^3 x_3 + (6v^2 + 2v)x_2^2`, where `v = 1 + 2x_1 x_2`.

Verbatim (Section 2): "This mapping exhibits a non-injective collision where
two distinct pre-images map to an identical point in the target space:
`F(0,1,-8) = (0,1,0) = F(-1,1,4)`" (there `F` names the tweaked map `G`).

The Jacobian Conjecture `JC(n)` (Keller 1939) as stated in the paper: any
polynomial map `F : ℂ^n → ℂ^n` with `det 𝒥(F) ∈ ℂ^×` is globally invertible.

## Status

Proved (by explicit computation) in the paper and by Alpöge; this file is a
repo-local kernel-checked artifact of the known result.

## What is formalized

* `jacobian F` is the matrix `(∂ F_i / ∂ x_j)` built from `MvPolynomial.pderiv`;
  `JacobianConjecture R n` says every polynomial map `R^n → R^n` whose Jacobian
  determinant is a unit of `R[x_1, …, x_n]` is injective on `R`-points.
* `det_jacobian_G : det 𝒥(G) = 1` over every commutative ring.
* `G_eval_collision : G(0,1,-8) = G(-1,1,4)` over every commutative ring.
* `not_jacobianConjecture_three`: `JC(3)` fails over every nontrivial
  commutative ring (in particular over `ℂ`: `not_jacobianConjecture_three_complex`).
* For Alpöge's original map: `det_jacobian_alpogeF : det 𝒥(F) = -2` and
  `alpogeF_eval_collision : F(0,2,-16) = F(-1,2,8)`, giving a second refutation
  of `JC(3)` over every nontrivial commutative ring in which `2` is a unit.

Indices: the paper's `x_1, x_2, x_3` are `X 0, X 1, X 2` here.
-/
import Mathlib

set_option autoImplicit false

open MvPolynomial

namespace Candidates.AlpogeJacobianCounterexampleThree

/-! ## General definitions -/

section General

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The Jacobian matrix `(∂ F_i / ∂ x_j)_{i,j}` of a polynomial map
`F = (F_0, …, F_{n-1})` in the variables `x_0, …, x_{n-1}`. -/
noncomputable def jacobian (F : Fin n → MvPolynomial (Fin n) R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of fun i j => pderiv j (F i)

/-- The function `R^n → R^n` induced by a polynomial map `F`:
`x ↦ (F_0(x), …, F_{n-1}(x))`. -/
noncomputable def polyMap (F : Fin n → MvPolynomial (Fin n) R) : (Fin n → R) → Fin n → R :=
  fun x i => eval x (F i)

/-- A Keller map: a polynomial map whose Jacobian determinant is a unit of the
polynomial ring (over a field or a domain: a nonzero constant). -/
def IsKellerMap (F : Fin n → MvPolynomial (Fin n) R) : Prop :=
  IsUnit (jacobian F).det

variable (R n) in
/-- The Jacobian Conjecture `JC(n)` over `R`: every Keller map `R^n → R^n` is
injective. -/
def JacobianConjecture : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) R, IsKellerMap F → Function.Injective (polyMap F)

/-- The partial derivative of a numeral is zero. -/
theorem pderiv_ofNat {σ : Type*} (i : σ) (m : ℕ) [m.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat m : MvPolynomial σ R)) = 0 :=
  (pderiv i).map_natCast m

/-- Ground truth: the Jacobian of the identity map is the identity matrix. -/
example : jacobian (fun i : Fin 3 => (X i : MvPolynomial (Fin 3) ℤ)) = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [jacobian, pderiv_X]

/-- Ground truth: the identity map is a Keller map. -/
example : IsKellerMap (fun i : Fin 3 => (X i : MvPolynomial (Fin 3) ℤ)) := by
  have hJ : jacobian (fun i : Fin 3 => (X i : MvPolynomial (Fin 3) ℤ)) = 1 := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [jacobian, pderiv_X]
  simp [IsKellerMap, hJ]

/-- Ground truth: `polyMap` evaluates componentwise. -/
example : polyMap (fun i : Fin 2 => (X 0 * X 1 + C (i : ℤ) : MvPolynomial (Fin 2) ℤ)) ![2, 3]
    = ![6, 7] := by
  funext i
  fin_cases i <;> simp [polyMap]

/-- A Keller map with two distinct points sharing an image refutes `JC(n)`. -/
theorem not_jacobianConjecture_of_collision (F : Fin n → MvPolynomial (Fin n) R)
    (hF : IsKellerMap F) (a b : Fin n → R) (hab : a ≠ b) (hcol : polyMap F a = polyMap F b) :
    ¬ JacobianConjecture R n :=
  fun hJC => hab (hJC F hF hcol)

end General

/-! ## The normalized map `G` (det 𝒥 = 1) -/

section Normalized

variable (R : Type*) [CommRing R]

/-- `v = 1 + 2 x_1 x_2` (paper indexing). -/
noncomputable def v : MvPolynomial (Fin 3) R := 1 + 2 * X 0 * X 1

/-- de Bondt's volume-preserving normalization `G` of Alpöge's map:
`G = (x_1 - 3x_1^2 x_2 - x_1^3 x_3, 3v^2 x_1 x_3 + (9v^2 - 6v - 2)x_2,
v^3 x_3 + (6v^2 + 2v)x_2^2)` with `v = 1 + 2x_1x_2`. -/
noncomputable def G : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2,
    3 * v R ^ 2 * X 0 * X 2 + (9 * v R ^ 2 - 6 * v R - 2) * X 1,
    v R ^ 3 * X 2 + (6 * v R ^ 2 + 2 * v R) * X 1 ^ 2]

/-- The Jacobian matrix of `G`, entry by entry (cross-checked in Sage). -/
theorem jacobian_G : jacobian (G R) =
    !![1 - 6 * X 0 * X 1 - 3 * X 0 ^ 2 * X 2, -3 * X 0 ^ 2, -X 0 ^ 3;
      36 * X 0 ^ 2 * X 1 ^ 2 * X 2 + 72 * X 0 * X 1 ^ 3 + 24 * X 0 * X 1 * X 2 + 24 * X 1 ^ 2
        + 3 * X 2,
      24 * X 0 ^ 3 * X 1 * X 2 + 108 * X 0 ^ 2 * X 1 ^ 2 + 12 * X 0 ^ 2 * X 2 + 48 * X 0 * X 1 + 1,
      12 * X 0 ^ 3 * X 1 ^ 2 + 12 * X 0 ^ 2 * X 1 + 3 * X 0;
      24 * X 0 ^ 2 * X 1 ^ 3 * X 2 + 48 * X 0 * X 1 ^ 4 + 24 * X 0 * X 1 ^ 2 * X 2
        + 28 * X 1 ^ 3 + 6 * X 1 * X 2,
      24 * X 0 ^ 3 * X 1 ^ 2 * X 2 + 96 * X 0 ^ 2 * X 1 ^ 3 + 24 * X 0 ^ 2 * X 1 * X 2
        + 84 * X 0 * X 1 ^ 2 + 6 * X 0 * X 2 + 16 * X 1,
      8 * X 0 ^ 3 * X 1 ^ 3 + 12 * X 0 ^ 2 * X 1 ^ 2 + 6 * X 0 * X 1 + 1] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [jacobian, G, v, pderiv_X, pderiv_ofNat] <;> ring

/-- **de Bondt, Section 1.** The Jacobian determinant of `G` is exactly `1`, over
every commutative ring. -/
theorem det_jacobian_G : (jacobian (G R)).det = 1 := by
  rw [jacobian_G, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- `G` is a Keller map over every commutative ring. -/
theorem isKellerMap_G : IsKellerMap (G R) := by
  rw [IsKellerMap, det_jacobian_G]
  exact isUnit_one

/-- **de Bondt, Section 2.** `G(0,1,-8) = (0,1,0)`. -/
theorem polyMap_G_first : polyMap (G R) ![0, 1, -8] = ![0, 1, 0] := by
  funext i
  fin_cases i <;> simp [polyMap, G, v] <;> ring

/-- **de Bondt, Section 2.** `G(-1,1,4) = (0,1,0)`. -/
theorem polyMap_G_second : polyMap (G R) ![-1, 1, 4] = ![0, 1, 0] := by
  funext i
  fin_cases i <;> simp [polyMap, G, v] <;> ring

/-- **de Bondt, Section 2.** `G(0,1,-8) = G(-1,1,4)` over every commutative ring. -/
theorem G_eval_collision : polyMap (G R) ![0, 1, -8] = polyMap (G R) ![-1, 1, 4] := by
  rw [polyMap_G_first, polyMap_G_second]

/-- The two colliding points `(0,1,-8)` and `(-1,1,4)` are distinct in every
nontrivial ring (their first coordinates are `0 ≠ -1`). -/
theorem collision_points_ne [Nontrivial R] : (![0, 1, -8] : Fin 3 → R) ≠ ![-1, 1, 4] := by
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.cons_val_zero] at h0
  exact one_ne_zero (neg_eq_zero.mp h0.symm)

/-- **Alpöge (2026), via de Bondt's normalization.** The Jacobian Conjecture
`JC(3)` is false over every nontrivial commutative ring: `G` is a Keller map
(`det 𝒥(G) = 1`) with `G(0,1,-8) = G(-1,1,4)`. -/
theorem not_jacobianConjecture_three [Nontrivial R] : ¬ JacobianConjecture R 3 :=
  not_jacobianConjecture_of_collision (G R) (isKellerMap_G R) _ _ (collision_points_ne R)
    (G_eval_collision R)

/-- **Alpöge (2026).** The classical Jacobian Conjecture `JC(3)` over `ℂ` is false. -/
theorem not_jacobianConjecture_three_complex : ¬ JacobianConjecture ℂ 3 :=
  not_jacobianConjecture_three ℂ

end Normalized

/-! ## Alpöge's original map `F` (det 𝒥 = -2) -/

section Original

variable (R : Type*) [CommRing R]

/-- `w = 1 + x_1 x_2` (paper indexing). -/
noncomputable def w : MvPolynomial (Fin 3) R := 1 + X 0 * X 1

/-- Alpöge's map `F = ((1+x_1x_2)^3 x_3 + x_2^2(1+x_1x_2)(4+3x_1x_2),
x_2 + 3x_1(1+x_1x_2)^2 x_3 + 3x_1x_2^2(4+3x_1x_2), 2x_1 - 3x_1^2x_2 - x_1^3x_3)`. -/
noncomputable def alpogeF : Fin 3 → MvPolynomial (Fin 3) R :=
  ![w R ^ 3 * X 2 + X 1 ^ 2 * w R * (4 + 3 * X 0 * X 1),
    X 1 + 3 * X 0 * w R ^ 2 * X 2 + 3 * X 0 * X 1 ^ 2 * (4 + 3 * X 0 * X 1),
    2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]

/-- The Jacobian matrix of Alpöge's `F`, entry by entry (cross-checked in Sage). -/
theorem jacobian_alpogeF : jacobian (alpogeF R) =
    !![3 * X 0 ^ 2 * X 1 ^ 3 * X 2 + 6 * X 0 * X 1 ^ 4 + 6 * X 0 * X 1 ^ 2 * X 2 + 7 * X 1 ^ 3
        + 3 * X 1 * X 2,
      3 * X 0 ^ 3 * X 1 ^ 2 * X 2 + 12 * X 0 ^ 2 * X 1 ^ 3 + 6 * X 0 ^ 2 * X 1 * X 2
        + 21 * X 0 * X 1 ^ 2 + 3 * X 0 * X 2 + 8 * X 1,
      X 0 ^ 3 * X 1 ^ 3 + 3 * X 0 ^ 2 * X 1 ^ 2 + 3 * X 0 * X 1 + 1;
      9 * X 0 ^ 2 * X 1 ^ 2 * X 2 + 18 * X 0 * X 1 ^ 3 + 12 * X 0 * X 1 * X 2 + 12 * X 1 ^ 2
        + 3 * X 2,
      6 * X 0 ^ 3 * X 1 * X 2 + 27 * X 0 ^ 2 * X 1 ^ 2 + 6 * X 0 ^ 2 * X 2 + 24 * X 0 * X 1 + 1,
      3 * X 0 ^ 3 * X 1 ^ 2 + 6 * X 0 ^ 2 * X 1 + 3 * X 0;
      -3 * X 0 ^ 2 * X 2 - 6 * X 0 * X 1 + 2, -3 * X 0 ^ 2, -X 0 ^ 3] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [jacobian, alpogeF, w, pderiv_X, pderiv_ofNat] <;> ring

/-- **Alpöge / de Bondt, Section 1.** The Jacobian determinant of Alpöge's map
is `-2`, over every commutative ring. -/
theorem det_jacobian_alpogeF : (jacobian (alpogeF R)).det = -2 := by
  rw [jacobian_alpogeF, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- Alpöge's map collides: `F(0,2,-16) = F(-1,2,8) = (0,2,0)`. -/
theorem alpogeF_eval_collision :
    polyMap (alpogeF R) ![0, 2, -16] = polyMap (alpogeF R) ![-1, 2, 8] := by
  have h1 : polyMap (alpogeF R) ![0, 2, -16] = ![0, 2, 0] := by
    funext i
    fin_cases i <;> simp [polyMap, alpogeF, w]
    ring
  have h2 : polyMap (alpogeF R) ![-1, 2, 8] = ![0, 2, 0] := by
    funext i
    fin_cases i <;> simp [polyMap, alpogeF, w] <;> ring
  rw [h1, h2]

/-- **Alpöge (2026), original map.** Over every nontrivial commutative ring in
which `2` is a unit, Alpöge's `F` is a Keller map (`det 𝒥(F) = -2`) with
`F(0,2,-16) = F(-1,2,8)`, so `JC(3)` fails. -/
theorem not_jacobianConjecture_three_of_isUnit_two [Nontrivial R] (h2 : IsUnit (2 : R)) :
    ¬ JacobianConjecture R 3 := by
  have hKeller : IsKellerMap (alpogeF R) := by
    rw [IsKellerMap, det_jacobian_alpogeF]
    have hC : (-2 : MvPolynomial (Fin 3) R) = C (-2) := by rw [map_neg, map_ofNat]
    rw [hC]
    exact (h2.neg).map C
  have hne : (![0, 2, -16] : Fin 3 → R) ≠ ![-1, 2, 8] := by
    intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    exact one_ne_zero (neg_eq_zero.mp h0.symm)
  exact not_jacobianConjecture_of_collision (alpogeF R) hKeller _ _ hne
    (alpogeF_eval_collision R)

end Original

end Candidates.AlpogeJacobianCounterexampleThree
