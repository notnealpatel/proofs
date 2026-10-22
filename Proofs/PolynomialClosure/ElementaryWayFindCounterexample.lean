/-
# Non-injective Keller maps in dimension three

Arno van den Essen, "An elementary way to find a counterexample to the Jacobian
Conjecture", arXiv:2609.17795 (2026), Sections 3–5 and final remarks.

The paper's map is
`F = (u³z + y²p(u), xu²z + yq(u), x + x²y + x³z)`, where
`u = 1 - (2/3)xy`, `p(u) = -(2/3)u² - (2/9)u` and
`q(u) = u² - (2/3)u - 2/9`.
The integer-coefficient normal form `A` associated with Alpöge's map is

    A_1 = x^3y^3z + 3x^2y^4 + 3x^2y^2z + 7xy^3 + 3xyz + 4y^2 + z
    A_2 = 3x^3y^2z + 9x^2y^3 + 6x^2yz + 12xy^2 + 3xz + y
    A_3 = -x^3z - 3x^2y + 2x

This normal form is not printed in the paper. Its relation to `F` is established
here by `L₂ ∘ A ∘ L₁ = F`, with `L₁ = (x/2, -4y/3, -8z)` and
`L₂ = (-x/8, -y/12, z)`, over fields of characteristic different from `2, 3`.

Over every commutative ring, `det JA = -2` and
`A(1,0,2) = A(0,6,-142) = (2,6,0)`. Thus `A` is a non-injective Keller map
over nontrivial commutative rings in which `2` is a unit. Over fields of
characteristic different from `3`, `det JF = -1/9` and
`F(1,0,-1) = F(0,-9,71) = (-1,-1,0)`. Together these maps give failure of the
injectivity statement over every field, including characteristic `2`.

The polynomial-automorphism statement requires a two-sided polynomial inverse,
not merely a bijection on points. A polynomial left inverse implies injectivity,
so the collisions also rule out polynomial automorphisms. The complex-field
conclusion uses the usual nonzero-constant Jacobian hypothesis.

Rational polynomial identities use certificates in the ideal `(2s - 1, 3t - 1)`,
where `s = C (1/2)` and `t = C (1/3)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ElementaryWayFindCounterexample

open MvPolynomial

/-! ## Polynomial maps, Jacobians and the Jacobian Conjecture -/

/-- The Jacobian matrix `(∂F_i/∂x_j)` of a polynomial map
`F = (F_1, …, F_n) : R^n → R^n`. -/
noncomputable def jacobian {n : ℕ} {R : Type*} [CommRing R]
    (F : Fin n → MvPolynomial (Fin n) R) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of fun i j => pderiv j (F i)

/-- The function `R^n → R^n`, `v ↦ (F_1(v), …, F_n(v))`, induced by a polynomial
map `F`. -/
noncomputable def polyMap {n : ℕ} {R : Type*} [CommRing R]
    (F : Fin n → MvPolynomial (Fin n) R) : (Fin n → R) → (Fin n → R) :=
  fun v i => eval v (F i)

/-- `F` is a Keller map: its Jacobian determinant is a constant `C c` with `c`
a unit of `R` (over a field: a non-zero constant). -/
def IsKellerMap {n : ℕ} {R : Type*} [CommRing R] (F : Fin n → MvPolynomial (Fin n) R) : Prop :=
  ∃ c : R, IsUnit c ∧ (jacobian F).det = C c

/-- `F` is a polynomial automorphism: there is a polynomial map `G` with
`G ∘ F = id` and `F ∘ G = id` as polynomial maps (composition by `bind₁`). -/
def IsPolyAutomorphism {n : ℕ} {R : Type*} [CommRing R]
    (F : Fin n → MvPolynomial (Fin n) R) : Prop :=
  ∃ G : Fin n → MvPolynomial (Fin n) R,
    (∀ i, bind₁ F (G i) = X i) ∧ (∀ i, bind₁ G (F i) = X i)

/-- The Jacobian Conjecture in dimension `n` over `R`, injectivity form:
every Keller map `R^n → R^n` is injective. -/
def JacobianConjectureInj (n : ℕ) (R : Type*) [CommRing R] : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) R, IsKellerMap F → Function.Injective (polyMap F)

/-- The Jacobian Conjecture in dimension `n` over `R` (Keller 1939): every
Keller map `R^n → R^n` is a polynomial automorphism. -/
def JacobianConjecture (n : ℕ) (R : Type*) [CommRing R] : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) R, IsKellerMap F → IsPolyAutomorphism F

/-- Evaluating a composite `g ∘ F` (as `bind₁ F g`) at `v` is evaluating `g`
at `F(v)`. -/
theorem eval_bind₁_eq {σ τ R : Type*} [CommRing R] (v : σ → R) (F : τ → MvPolynomial σ R)
    (g : MvPolynomial τ R) : eval v (bind₁ F g) = eval (fun i => eval v (F i)) g :=
  eval₂Hom_bind₁ _ _ _ _

/-- A polynomial map with a polynomial left inverse is injective. -/
theorem injective_polyMap_of_leftInverse {n : ℕ} {R : Type*} [CommRing R]
    {F G : Fin n → MvPolynomial (Fin n) R} (hGF : ∀ i, bind₁ F (G i) = X i) :
    Function.Injective (polyMap F) := by
  intro v w hvw
  funext i
  have hv : eval v (bind₁ F (G i)) = v i := by rw [hGF i, eval_X]
  have hw : eval w (bind₁ F (G i)) = w i := by rw [hGF i, eval_X]
  rw [← hv, ← hw, eval_bind₁_eq, eval_bind₁_eq]
  exact congrArg (fun u => eval u (G i)) hvw

/-- The automorphism form of the Jacobian Conjecture implies the injectivity
form. -/
theorem jacobianConjectureInj_of_jacobianConjecture {n : ℕ} {R : Type*} [CommRing R]
    (h : JacobianConjecture n R) : JacobianConjectureInj n R := by
  intro F hF
  obtain ⟨G, hGF, -⟩ := h F hF
  exact injective_polyMap_of_leftInverse hGF

/-! ## Alpöge's map in integer-coefficient normal form -/

/-- Alpöge's counterexample `A = (A_1, A_2, A_3)` in integer-coefficient normal
form, over an arbitrary commutative ring `R` (variables `x = X 0`, `y = X 1`,
`z = X 2`). -/
noncomputable def alpoge (R : Type*) [CommRing R] : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 0 ^ 3 * X 1 ^ 3 * X 2 + 3 * X 0 ^ 2 * X 1 ^ 4 + 3 * X 0 ^ 2 * X 1 ^ 2 * X 2
      + 7 * X 0 * X 1 ^ 3 + 3 * X 0 * X 1 * X 2 + 4 * X 1 ^ 2 + X 2,
    3 * X 0 ^ 3 * X 1 ^ 2 * X 2 + 9 * X 0 ^ 2 * X 1 ^ 3 + 6 * X 0 ^ 2 * X 1 * X 2
      + 12 * X 0 * X 1 ^ 2 + 3 * X 0 * X 2 + X 1,
    -(X 0 ^ 3 * X 2) - 3 * X 0 ^ 2 * X 1 + 2 * X 0]

/-- `A(1, 1, 1) = (22, 34, -2)` over `ℤ`. -/
example : polyMap (alpoge ℤ) ![1, 1, 1] = ![22, 34, -2] := by
  funext i
  fin_cases i <;> norm_num [polyMap, alpoge, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- `A(1/2, 0, 8) = (8, 12, 0)` over `ℚ`. -/
example : polyMap (alpoge ℚ) ![1 / 2, 0, 8] = ![8, 12, 0] := by
  funext i
  fin_cases i <;> norm_num [polyMap, alpoge, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The integer polynomials `A_i` map to `alpoge R` under `ℤ → R`, so the
statements below are about one integer polynomial map read in every ring. -/
theorem map_alpoge (R : Type*) [CommRing R] (i : Fin 3) :
    map (Int.castRingHom R) (alpoge ℤ i) = alpoge R i := by
  fin_cases i <;> simp [alpoge]

/-- Partial derivatives kill numerals. -/
theorem pderiv_ofNat {σ R : Type*} [CommSemiring R] (i : σ) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat n : MvPolynomial σ R)) = 0 :=
  Derivation.map_natCast _ n

/-- Jacobian determinant of Alpöge's map: `det (∂A_i/∂x_j) = -2`, over every
commutative ring. -/
theorem alpoge_jacobian_det (R : Type*) [CommRing R] :
    (jacobian (alpoge R)).det = C (-2) := by
  simp only [jacobian, Matrix.det_fin_three, Matrix.of_apply, alpoge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_neg, map_sub, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X, smul_eq_mul,
    pderiv_ofNat, Pi.single_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero,
    Nat.add_one_sub_one, one_ne_zero, mul_one, nsmul_eq_mul, Nat.cast_ofNat, zero_add, pow_one,
    add_zero]
  rw [map_ofNat C 2]
  ring

/-- `A(1, 0, 2) = (2, 6, 0)`. -/
theorem polyMap_alpoge_one_zero_two (R : Type*) [CommRing R] :
    polyMap (alpoge R) ![1, 0, 2] = ![2, 6, 0] := by
  funext i
  fin_cases i <;> norm_num [polyMap, alpoge, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- `A(0, 6, -142) = (2, 6, 0)`. -/
theorem polyMap_alpoge_zero_six_neg (R : Type*) [CommRing R] :
    polyMap (alpoge R) ![0, 6, -142] = ![2, 6, 0] := by
  funext i
  fin_cases i <;> norm_num [polyMap, alpoge, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- Collision: `A(1, 0, 2) = A(0, 6, -142)`, over every commutative ring. -/
theorem polyMap_alpoge_collision (R : Type*) [CommRing R] :
    polyMap (alpoge R) ![1, 0, 2] = polyMap (alpoge R) ![0, 6, -142] := by
  rw [polyMap_alpoge_one_zero_two, polyMap_alpoge_zero_six_neg]

/-- Over a nontrivial commutative ring, Alpöge's map is not injective. -/
theorem not_injective_polyMap_alpoge (R : Type*) [CommRing R] [Nontrivial R] :
    ¬ Function.Injective (polyMap (alpoge R)) := by
  intro hinj
  have hpts := congrFun (hinj (polyMap_alpoge_collision R)) 0
  simp only [Fin.isValue, Matrix.cons_val_zero] at hpts
  exact one_ne_zero hpts

/-- Alpöge's map is a Keller map over every commutative ring in which `2` is a
unit. -/
theorem isKellerMap_alpoge (R : Type*) [CommRing R] (h2 : IsUnit (2 : R)) :
    IsKellerMap (alpoge R) :=
  ⟨-2, h2.neg, alpoge_jacobian_det R⟩

/-- Alpöge's map is not a polynomial automorphism over any nontrivial
commutative ring. -/
theorem not_isPolyAutomorphism_alpoge (R : Type*) [CommRing R] [Nontrivial R] :
    ¬ IsPolyAutomorphism (alpoge R) := by
  rintro ⟨G, hGF, -⟩
  exact not_injective_polyMap_alpoge R (injective_polyMap_of_leftInverse hGF)

/-! ## van den Essen's map `F` (Sections 3-5 of the paper) -/

section VanDenEssen

variable (K : Type*) [Field K]

/-- `u = 1 - (2/3) x y`. -/
noncomputable def vdeU : MvPolynomial (Fin 3) K := 1 - C (2 / 3) * X 0 * X 1

/-- `p(u) = -(2/3) u^2 - (2/9) u`. -/
noncomputable def vdeP (u : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  -C (2 / 3) * u ^ 2 - C (2 / 9) * u

/-- `q(u) = u^2 - (2/3) u - 2/9`. -/
noncomputable def vdeQ (u : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  u ^ 2 - C (2 / 3) * u - C (2 / 9)

/-- van den Essen's map `F = (u^3 z + y^2 p(u), x u^2 z + y q(u), x + x^2 y + x^3 z)`
(end of Section 5 of arXiv 2609.17795). -/
noncomputable def vanDenEssen : Fin 3 → MvPolynomial (Fin 3) K :=
  ![vdeU K ^ 3 * X 2 + X 1 ^ 2 * vdeP K (vdeU K),
    X 0 * vdeU K ^ 2 * X 2 + X 1 * vdeQ K (vdeU K),
    X 0 + X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2]

/-- `F` rewritten with the single constant `t = C (1/3)`: `2/3 = 2t`,
`2/9 = 2t^2`. -/
theorem vanDenEssen_eq :
    vanDenEssen K =
      ![(1 - 2 * C 3⁻¹ * X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (-(2 * C 3⁻¹) *
          (1 - 2 * C 3⁻¹ * X 0 * X 1) ^ 2 - 2 * C 3⁻¹ ^ 2 * (1 - 2 * C 3⁻¹ * X 0 * X 1)),
        X 0 * (1 - 2 * C 3⁻¹ * X 0 * X 1) ^ 2 * X 2 + X 1 * ((1 - 2 * C 3⁻¹ * X 0 * X 1) ^ 2 -
          2 * C 3⁻¹ * (1 - 2 * C 3⁻¹ * X 0 * X 1) - 2 * C 3⁻¹ ^ 2),
        X 0 + X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2] := by
  have h23 : (C (2 / 3 : K) : MvPolynomial (Fin 3) K) = 2 * C 3⁻¹ := by
    rw [div_eq_mul_inv, map_mul, map_ofNat]
  have h29 : (C (2 / 9 : K) : MvPolynomial (Fin 3) K) = 2 * C 3⁻¹ ^ 2 := by
    rw [← map_pow, ← map_ofNat C 2, ← map_mul, show (9 : K) = 3 ^ 2 by norm_num, div_eq_mul_inv,
      inv_pow]
  simp only [vanDenEssen, vdeU, vdeP, vdeQ, h23, h29]

/-- In characteristic `≠ 3`, `C (1/3)` is a right inverse of `3`. -/
theorem three_mul_C_inv_three {σ : Type*} (h3 : (3 : K) ≠ 0) :
    (3 : MvPolynomial σ K) * C 3⁻¹ = 1 := by
  rw [← map_ofNat C 3, ← map_mul, mul_inv_cancel₀ h3, map_one]

/-- Keller property of `F` (end of Section 5): `det JF = -1/9`, over every
field of characteristic `≠ 3`. -/
theorem vanDenEssen_jacobian_det (h3 : (3 : K) ≠ 0) :
    (jacobian (vanDenEssen K)).det = C (-1 / 9) := by
  have ht := three_mul_C_inv_three K (σ := Fin 3) h3
  have h19 : (C (-1 / 9 : K) : MvPolynomial (Fin 3) K) = -C 3⁻¹ ^ 2 := by
    rw [← map_pow, ← map_neg, show (9 : K) = 3 ^ 2 by norm_num, neg_div, one_div, inv_pow]
  rw [vanDenEssen_eq K, h19]
  simp only [jacobian, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_neg, map_sub, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X, smul_eq_mul,
    pderiv_ofNat, pderiv_C, Pi.single_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero,
    Nat.add_one_sub_one, one_ne_zero, mul_one, nsmul_eq_mul, Nat.cast_ofNat, zero_add, pow_one,
    add_zero, Derivation.map_one_eq_zero]
  set t : MvPolynomial (Fin 3) K := C 3⁻¹
  set x : MvPolynomial (Fin 3) K := X 0
  set y : MvPolynomial (Fin 3) K := X 1
  set z : MvPolynomial (Fin 3) K := X 2
  -- `det + t^2 = (3t - 1) · Q` with integer `Q`.
  linear_combination (32*t^4*x^6*y^4*z + 32*t^4*x^5*y^5 + 32*t^4*x^4*y^4 - 64*t^3*x^5*y^3*z - 64*t^3*x^4*y^4 - 8*t^4*x^3*y^3 + 8*t^3*x^4*y^2*z - 48*t^3*x^3*y^3 + 48*t^2*x^4*y^2*z + 48*t^2*x^3*y^3 + 8*t^3*x^2*y^2 - 8*t^2*x^3*y*z + 28*t^2*x^2*y^2 - 16*t*x^3*y*z - 16*t*x^2*y^2 - 4*t^2*x*y + 2*t*x^2*z - 8*t*x*y + 2*x^2*z + 2*x*y + t + 1) * ht

/-- `F(1, 0, -1) = (-1, -1, 0)` (at `x y = 0`, so `u = 1`). -/
theorem polyMap_vanDenEssen_one_zero_neg :
    polyMap (vanDenEssen K) ![1, 0, -1] = ![-1, -1, 0] := by
  funext i
  rw [polyMap, vanDenEssen_eq K]
  fin_cases i <;> simp

/-- `F(0, -9, 71) = (-1, -1, 0)` (characteristic `≠ 3`). -/
theorem polyMap_vanDenEssen_zero_neg_nine (h3 : (3 : K) ≠ 0) :
    polyMap (vanDenEssen K) ![0, -9, 71] = ![-1, -1, 0] := by
  funext i
  rw [polyMap, vanDenEssen_eq K]
  fin_cases i
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul, Fin.zero_eta,
      Matrix.cons_val_zero, map_add, map_mul, map_pow, map_sub, map_one, eval_ofNat, eval_C, eval_X,
      mul_zero, Matrix.cons_val_one, mul_neg, zero_mul, neg_zero, sub_zero, one_pow, Matrix.cons_val,
      one_mul, even_two, Even.neg_pow, map_neg, mul_one, inv_pow]
    field_simp
    ring
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_zero, map_add, map_mul, eval_X, map_pow, map_sub, map_one,
      eval_ofNat, eval_C, mul_zero, mul_neg, zero_mul, neg_zero, sub_zero, one_pow, mul_one,
      Matrix.cons_val, inv_pow, zero_add, neg_inj]
    field_simp
    ring
  · simp

/-- Over a field of characteristic `≠ 3`, `F` is a Keller map. -/
theorem isKellerMap_vanDenEssen (h3 : (3 : K) ≠ 0) : IsKellerMap (vanDenEssen K) := by
  refine ⟨-1 / 9, ?_, vanDenEssen_jacobian_det K h3⟩
  have h9 : (9 : K) ≠ 0 := by
    rw [show (9 : K) = 3 * 3 by norm_num]
    exact mul_ne_zero h3 h3
  exact (div_ne_zero (neg_ne_zero.mpr one_ne_zero) h9).isUnit

/-- `F` is not injective over a field of characteristic `≠ 3`. -/
theorem not_injective_polyMap_vanDenEssen (h3 : (3 : K) ≠ 0) :
    ¬ Function.Injective (polyMap (vanDenEssen K)) := by
  intro hinj
  have hpts := congrFun (hinj ((polyMap_vanDenEssen_one_zero_neg K).trans
    (polyMap_vanDenEssen_zero_neg_nine K h3).symm)) 0
  simp only [Fin.isValue, Matrix.cons_val_zero] at hpts
  exact one_ne_zero hpts

/-- `L_1 = (x/2, -4y/3, -8z)` from the paper's final remarks. -/
noncomputable def vdeL1 : Fin 3 → MvPolynomial (Fin 3) K :=
  ![C (1 / 2) * X 0, C (-4 / 3) * X 1, C (-8) * X 2]

/-- Final remark of the paper: `L_2 ∘ A ∘ L_1 = F` with
`L_1 = (x/2, -4y/3, -8z)` and `L_2 = (-x/8, -y/12, z)`, over every field of
characteristic `≠ 2, 3`.  Composition `A ∘ L_1` is `bind₁ L_1 A`. -/
theorem vanDenEssen_eq_L2_alpoge_L1 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    vanDenEssen K = ![C (-1 / 8) * bind₁ (vdeL1 K) (alpoge K 0),
      C (-1 / 12) * bind₁ (vdeL1 K) (alpoge K 1), bind₁ (vdeL1 K) (alpoge K 2)] := by
  have hs : (2 : MvPolynomial (Fin 3) K) * C 2⁻¹ = 1 := by
    rw [← map_ofNat C 2, ← map_mul, mul_inv_cancel₀ h2, map_one]
  have ht := three_mul_C_inv_three K (σ := Fin 3) h3
  have c1 : (C (1 / 2 : K) : MvPolynomial (Fin 3) K) = C 2⁻¹ := by rw [one_div]
  have c2 : (C (-4 / 3 : K) : MvPolynomial (Fin 3) K) = -(4 * C 3⁻¹) := by
    rw [← map_ofNat C 4, ← map_mul, ← map_neg, neg_div, div_eq_mul_inv]
  have c3 : (C (-8 : K) : MvPolynomial (Fin 3) K) = -8 := by rw [map_neg, map_ofNat]
  have c4 : (C (-1 / 8 : K) : MvPolynomial (Fin 3) K) = -(C 2⁻¹ ^ 3) := by
    rw [← map_pow, ← map_neg, show (8 : K) = 2 ^ 3 by norm_num, neg_div, one_div, inv_pow]
  have c5 : (C (-1 / 12 : K) : MvPolynomial (Fin 3) K) = -(C 2⁻¹ ^ 2 * C 3⁻¹) := by
    rw [← map_pow, ← map_mul, ← map_neg, show (12 : K) = 2 ^ 2 * 3 by norm_num, neg_div, one_div,
      mul_inv, inv_pow]
  rw [vanDenEssen_eq K]
  simp only [vdeL1, alpoge, c1, c2, c3, c4, c5, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_neg, map_sub, map_mul,
    map_pow, map_ofNat, bind₁_X_right, Fin.isValue]
  set s : MvPolynomial (Fin 3) K := C 2⁻¹
  set t : MvPolynomial (Fin 3) K := C 3⁻¹
  set x : MvPolynomial (Fin 3) K := X 0
  set y : MvPolynomial (Fin 3) K := X 1
  set z : MvPolynomial (Fin 3) K := X 2
  -- Each difference lies in the ideal `(2s - 1, 3t - 1)`.
  ext1 i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linear_combination (256*s^5*t^3*x^3*y^3*z + 128*s^4*t^3*x^3*y^3*z + 128*s^4*t^3*x^2*y^4 + 64*s^3*t^3*x^3*y^3*z + 64*s^3*t^3*x^2*y^4 + 32*s^2*t^3*x^3*y^3*z + 32*s^2*t^3*x^2*y^4 + 16*s*t^3*x^3*y^3*z - 224*s^3*t^3*x*y^3 + 16*s*t^3*x^2*y^4 - 64*s^4*t*x^2*y^2*z + 8*t^3*x^3*y^3*z - 112*s^2*t^3*x*y^3 + 8*t^3*x^2*y^4 - 32*s^3*t*x^2*y^2*z - 56*s*t^3*x*y^3 - 16*s^2*t*x^2*y^2*z - 28*t^3*x*y^3 - 8*s*t*x^2*y^2*z + 32*s^2*t^2*y^2 + 16*s^3*x*y*z - 4*t*x^2*y^2*z + 16*s*t^2*y^2 + 8*s^2*x*y*z + 8*t^2*y^2 + 4*s*x*y*z - 4*s^2*z + 2*x*y*z - 2*s*z - z) * hs + (256*s^5*t^3*x^2*y^4 - 128*s^5*t*x^2*y^2*z + 32*s^4*x*y*z - 8*t^2*x*y^3 + 4*t*x^2*y^2*z + 2*t*y^2 - 2*x*y*z) * ht
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination (-64*s^4*t^2*x^3*y^2*z - 32*s^3*t^2*x^3*y^2*z - 32*s^3*t^2*x^2*y^3 - 16*s^2*t^2*x^3*y^2*z - 16*s^2*t^2*x^2*y^3 - 8*s*t^2*x^3*y^2*z - 8*s*t^2*x^2*y^3 + 32*s^3*t*x^2*y*z - 4*t^2*x^3*y^2*z + 32*s^2*t^2*x*y^2 - 4*t^2*x^2*y^3 + 16*s^2*t*x^2*y*z + 16*s*t^2*x*y^2 + 8*s*t*x^2*y*z + 8*t^2*x*y^2 + 4*t*x^2*y*z - 2*s*t^2*y - 4*s^2*x*z - t^2*y - 2*s*x*z - x*z) * hs + (-128*s^5*t^2*x^3*y^2*z - 192*s^4*t^3*x^2*y^3 - 64*s^4*t^2*x^2*y^3 + 64*s^4*t*x^2*y*z + 64*s^3*t^2*x*y^2 - 8*s^3*x*z + 4*t*x*y^2 - t*y - y) * ht
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination (-4*s^2*x^3*z - 2*s*x^3*z - 2*s*x^2*y - x^3*z - x^2*y - x) * hs + (-4*s^2*x^2*y) * ht

end VanDenEssen

/-! ## Refutation of the Jacobian Conjecture in dimension three -/

/-- The three-dimensional Jacobian Conjecture is false (injectivity form),
over every nontrivial commutative ring in which `2` is a unit: Alpöge's map is
a Keller map with `det JA = -2` and `A(1,0,2) = A(0,6,-142)`.
Source: arXiv 2609.17795 (van den Essen), Alpöge's counterexample. -/
theorem jacobianConjectureInj_three_false (R : Type*) [CommRing R] [Nontrivial R]
    (h2 : IsUnit (2 : R)) : ¬ JacobianConjectureInj 3 R := fun h =>
  not_injective_polyMap_alpoge R (h (alpoge R) (isKellerMap_alpoge R h2))

/-- The three-dimensional Jacobian Conjecture is false (Keller's form:
Keller maps are polynomial automorphisms), over every nontrivial commutative
ring in which `2` is a unit.  Source: arXiv 2609.17795 (van den Essen). -/
theorem jacobianConjecture_three_false (R : Type*) [CommRing R] [Nontrivial R]
    (h2 : IsUnit (2 : R)) : ¬ JacobianConjecture 3 R := fun h =>
  jacobianConjectureInj_three_false R h2 (jacobianConjectureInj_of_jacobianConjecture h)

/-- The Jacobian Conjecture over `ℂ` fails in dimension three: there is a
polynomial map `ℂ^3 → ℂ^3` whose Jacobian determinant is a non-zero constant
and which is not injective (hence not invertible).
Source: arXiv 2609.17795 (van den Essen), Alpöge's counterexample. -/
theorem jacobianConjecture_complex_three_false :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) ℂ,
      (∃ c : ℂ, c ≠ 0 ∧ (jacobian F).det = C c) → Function.Injective (polyMap F) := by
  intro h
  refine not_injective_polyMap_alpoge ℂ (h (alpoge ℂ) ⟨-2, by norm_num, ?_⟩)
  exact alpoge_jacobian_det ℂ

/-- The three-dimensional Jacobian Conjecture fails over every field:
in characteristic `≠ 2` Alpöge's map `A` is a non-injective Keller map, and in
characteristic `2` (where `3 = 1 ≠ 0`) van den Essen's map `F` is one. -/
theorem jacobianConjectureInj_three_false_of_field (K : Type*) [Field K] :
    ¬ JacobianConjectureInj 3 K := by
  by_cases h2 : (2 : K) = 0
  · have h3 : (3 : K) ≠ 0 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
      exact one_ne_zero
    exact fun h => not_injective_polyMap_vanDenEssen K h3
      (h (vanDenEssen K) (isKellerMap_vanDenEssen K h3))
  · exact jacobianConjectureInj_three_false K (Ne.isUnit h2)

/-- The polynomial-automorphism statement fails over `ℚ`. -/
example : ¬ JacobianConjecture 3 ℚ := jacobianConjecture_three_false ℚ (by norm_num)

end Candidates.ElementaryWayFindCounterexample
