/-
# Casas-Alvero conjecture in degree at most 4 (characteristic zero)

## Source

arXiv:2608.14726, Mohammad F. Marashdeh, "A descent-set obstruction for the
Casas--Alvero conjecture", Section 1 (Introduction), Conjecture `conj:CA`
and the known-cases paragraph following it.  Recorded 2026-10-21.

Verbatim statement (Conjecture 1.1, `conj:CA`):

> Let $K$ be a field of characteristic $0$. Then there is no
> $\CA$-polynomial over $K$; equivalently, if $f\in K[x]$ is monic of
> degree $d$ and $\gcd\bigl(f,f^{(i)}\bigr)\neq 1$ for $i=1,\dots,d-1$,
> then $f=(x-\alpha)^{d}$ for some $\alpha\in K$.

The paper states that the conjecture "is trivial for $d\le2$", that
$\bad(3)=\{2\}$ and $\bad(4)=\{3,5,7\}$, and that the conjecture is known
for $d\le7$ by direct elimination (Diaz-Toca and Gonzalez-Vega 2006).

## Status

The conjecture is open in general.  The degree `d ≤ 4` case formalized here
is a known result (proved elsewhere: Diaz-Toca and Gonzalez-Vega 2006, and
elementary); it is not a new theorem of the source paper.

## Formalization

`gcd(f, f^(i)) ≠ 1` over the field `K` is rendered as
`¬ IsCoprime f (derivative^[i] f)`: in the Euclidean domain `K[X]` the
monic gcd is `1` exactly when the two polynomials are coprime.  The proof
passes to `AlgebraicClosure K`, where non-coprimality yields a common root,
translates the root of `f^(d-1)` to the origin, and eliminates.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.CasasAlveroDegreeFour

open Polynomial

/-! ## Definition layer -/

/-- The Casas-Alvero hypothesis on `f ∈ K[X]` of degree `d`: for every
`i ∈ {1, …, d - 1}` the polynomial `f` shares a non-constant common factor with
its `i`-th derivative, i.e. `gcd(f, f^(i)) ≠ 1`, i.e. `f` and `f^(i)` are not
coprime.  The range `1 ≤ i < d` avoids natural-number subtraction. -/
def SharesFactorWithDerivatives {K : Type*} [Field K] (f : K[X]) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i < f.natDegree → ¬ IsCoprime f (derivative^[i] f)

/-- Ground truth: `X ^ 4` satisfies the Casas-Alvero hypothesis over `ℚ`
(every derivative of order `1 ≤ i ≤ 3` is divisible by `X`). -/
example : SharesFactorWithDerivatives (X ^ 4 : ℚ[X]) := by
  intro i hi1 hi
  rw [natDegree_X_pow] at hi
  intro hcop
  have hXf : (X : ℚ[X]) ∣ X ^ 4 := dvd_pow_self X (by norm_num)
  have hXd : (X : ℚ[X]) ∣ derivative^[i] (X ^ 4) := by
    rw [iterate_derivative_X_pow_eq_C_mul]
    exact dvd_mul_of_dvd_right (dvd_pow_self X (by omega)) _
  exact not_isUnit_X (hcop.isUnit_of_dvd' hXf hXd)

/-- Ground truth: `X ^ 2 - 1` fails the Casas-Alvero hypothesis over `ℚ`,
since `-(X ^ 2 - 1) + (X / 2) * (2 X) = 1` makes it coprime to its derivative. -/
example : ¬ SharesFactorWithDerivatives (X ^ 2 - 1 : ℚ[X]) := by
  intro h
  have hdeg : (X ^ 2 - 1 : ℚ[X]).natDegree = 2 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  refine h 1 le_rfl (by rw [hdeg]; norm_num) ⟨-1, C (1 / 2) * X, ?_⟩
  have hder : derivative (X ^ 2 - 1 : ℚ[X]) = C 2 * X := by
    rw [derivative_sub, derivative_X_pow, derivative_one]
    norm_num
  have hC : C (1 / 2 : ℚ) * C 2 = 1 := by
    rw [← C_mul]
    norm_num
  rw [Function.iterate_one, hder]
  linear_combination X ^ 2 * hC

/-! ## Elimination in centred coordinates -/

/-- Degree-3 elimination: if `x ^ 3 + A x` has a root `v` that is also a root of
its derivative `3 x ^ 2 + A`, then `A = 0` (characteristic zero). -/
theorem centred_cubic_eq_zero {L : Type*} [Field L] [CharZero L] (A v : L)
    (h1 : 3 * v ^ 2 + A = 0) (hv : v ^ 3 + A * v = 0) : A = 0 := by
  have hA : A = -3 * v ^ 2 := by linear_combination h1
  subst hA
  have hv3 : (-2 : L) * v ^ 3 = 0 := by linear_combination hv
  have hv0 : v = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
    ((mul_eq_zero.mp hv3).resolve_left (by norm_num))
  rw [hv0]
  ring

/-- Degree-4 elimination: if the centred quartic `x ^ 4 + A x ^ 2 + B x` has a root
`u` of its second derivative `12 x ^ 2 + 2 A` and a root `v` of its first
derivative `4 x ^ 3 + 2 A x + B`, then `A = B = 0` (characteristic zero; the
contradiction in the generic case is `-35 u ^ 3 = 0`, reflecting `𝓑(4) = {3,5,7}`). -/
theorem centred_quartic_eq_zero {L : Type*} [Field L] [CharZero L] (A B u v : L)
    (h2 : 12 * u ^ 2 + 2 * A = 0) (hu : u ^ 4 + A * u ^ 2 + B * u = 0)
    (h1 : 4 * v ^ 3 + 2 * A * v + B = 0) (hv : v ^ 4 + A * v ^ 2 + B * v = 0) :
    A = 0 ∧ B = 0 := by
  have hA : A = -6 * u ^ 2 := by linear_combination h2 / 2
  subst hA
  have hu' : u * (B - 5 * u ^ 3) = 0 := by linear_combination hu
  rcases mul_eq_zero.mp hu' with hu0 | hB
  · subst hu0
    have hv' : -3 * v ^ 4 = 0 := by linear_combination hv - v * h1
    have hv0 : v = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp
      ((mul_eq_zero.mp hv').resolve_left (by norm_num))
    subst hv0
    constructor
    · ring
    · linear_combination h1
  · have hB' : B = 5 * u ^ 3 := by linear_combination hB
    subst hB'
    by_cases hu0 : u = 0
    · subst hu0
      constructor <;> ring
    exfalso
    by_cases hv0 : v = 0
    · subst hv0
      have h5 : (5 : L) * u ^ 3 = 0 := by linear_combination h1
      exact hu0 (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
        ((mul_eq_zero.mp h5).resolve_left (by norm_num)))
    have hw : v ^ 3 - 6 * u ^ 2 * v + 5 * u ^ 3 = 0 := by
      have hvw : v * (v ^ 3 - 6 * u ^ 2 * v + 5 * u ^ 3) = 0 := by linear_combination hv
      exact (mul_eq_zero.mp hvw).resolve_left hv0
    have hlin : u ^ 2 * (15 * u - 12 * v) = 0 := by linear_combination 4 * hw - h1
    have h4v : 4 * v = 5 * u := by
      have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
      linear_combination ((mul_eq_zero.mp hlin).resolve_left hu2) / (-3)
    have h35 : (-35 : L) * u ^ 3 = 0 := by
      linear_combination 64 * hw - (16 * v ^ 2 + 20 * u * v + 25 * u ^ 2 - 96 * u ^ 2) * h4v
    exact hu0 (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
      ((mul_eq_zero.mp h35).resolve_left (by norm_num)))

/-! ## Explicit forms of monic polynomials of small degree -/

/-- A monic polynomial of `natDegree 4` is `X^4 + a₃ X^3 + a₂ X^2 + a₁ X + a₀`. -/
theorem eq_quartic {R : Type*} [CommRing R] (f : R[X]) (hm : f.Monic) (hd : f.natDegree = 4) :
    f = X ^ 4 + C (f.coeff 3) * X ^ 3 + C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X
      + C (f.coeff 0) := by
  conv_lhs => rw [hm.as_sum, hd]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    pow_one]
  ring

/-- A monic polynomial of `natDegree 3` is `X^3 + a₂ X^2 + a₁ X + a₀`. -/
theorem eq_cubic {R : Type*} [CommRing R] (f : R[X]) (hm : f.Monic) (hd : f.natDegree = 3) :
    f = X ^ 3 + C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  conv_lhs => rw [hm.as_sum, hd]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    pow_one]
  ring

/-- A monic polynomial of `natDegree 2` is `X^2 + a₁ X + a₀`. -/
theorem eq_quadratic {R : Type*} [CommRing R] (f : R[X]) (hm : f.Monic)
    (hd : f.natDegree = 2) : f = X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  conv_lhs => rw [hm.as_sum, hd]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    pow_one]
  ring

/-- A monic polynomial of `natDegree 1` is `X + a₀`. -/
theorem eq_linear {R : Type*} [CommRing R] (f : R[X]) (hm : f.Monic) (hd : f.natDegree = 1) :
    f = X + C (f.coeff 0) := by
  conv_lhs => rw [hm.as_sum, hd]
  simp

/-- A monic polynomial of `natDegree 0` is `1`. -/
theorem eq_one_of_natDegree_eq_zero {R : Type*} [CommRing R] (f : R[X]) (hm : f.Monic)
    (hd : f.natDegree = 0) : f = 1 := by
  conv_lhs => rw [hm.as_sum, hd]
  simp

/-! ## Degree four over a field containing the common roots -/

/-- Casas-Alvero in degree 4, root form: over a field `L` of characteristic zero,
if a monic quartic `f` shares a root with each of `f'`, `f''`, `f'''`, then
`f = (X - α) ^ 4` with `α = -a₃ / 4`. -/
theorem eq_X_sub_C_pow_four_of_common_roots {L : Type*} [Field L] [CharZero L] (f : L[X])
    (hm : f.Monic) (hd : f.natDegree = 4)
    (hroot : ∀ i : ℕ, 1 ≤ i → i < 4 → ∃ a : L, f.eval a = 0 ∧ (derivative^[i] f).eval a = 0) :
    f = (X - C (-(f.coeff 3) / 4)) ^ 4 := by
  have hf := eq_quartic f hm hd
  generalize f.coeff 3 = b at hf ⊢
  generalize f.coeff 2 = c at hf
  generalize f.coeff 1 = e at hf
  generalize f.coeff 0 = g at hf
  subst hf
  have hev : ∀ x : L, eval x (X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C e * X + C g)
      = x ^ 4 + b * x ^ 3 + c * x ^ 2 + e * x + g := by
    intro x
    simp
  have hd1 : ∀ x : L, eval x (derivative^[1] (X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C e * X + C g))
      = 4 * x ^ 3 + 3 * b * x ^ 2 + 2 * c * x + e := by
    intro x
    simp only [Function.iterate_one, derivative_X_pow_succ, Nat.cast_ofNat,
      map_add, map_one, derivative_mul, derivative_C, zero_mul, zero_add, Nat.cast_one, pow_one,
      derivative_X, mul_one, add_zero, eval_add, eval_mul, eval_C, eval_one, eval_pow, eval_X,
      add_left_inj]
    ring
  have hd2 : ∀ x : L, eval x (derivative^[2] (X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C e * X + C g))
      = 12 * x ^ 2 + 6 * b * x + 2 * c := by
    intro x
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one, derivative_mul, derivative_C,
      zero_mul, zero_add, Nat.cast_one, pow_one, derivative_X, mul_one, add_zero, derivative_one,
      eval_add, eval_mul, eval_C, eval_one, eval_pow, eval_X]
    ring
  have hd3 : ∀ x : L, eval x (derivative^[3] (X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C e * X + C g))
      = 24 * x + 6 * b := by
    intro x
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one, derivative_mul, derivative_C,
      zero_mul, zero_add, Nat.cast_one, pow_one, derivative_X, mul_one, add_zero, derivative_one,
      mul_zero, eval_add, eval_mul, eval_C, eval_one, eval_X]
    ring
  obtain ⟨t, ht, ht3⟩ := hroot 3 (by norm_num) (by norm_num)
  obtain ⟨r, hr, hr2⟩ := hroot 2 (by norm_num) (by norm_num)
  obtain ⟨s, hs, hs1⟩ := hroot 1 (by norm_num) (by norm_num)
  rw [hev] at ht hr hs
  rw [hd3] at ht3
  rw [hd2] at hr2
  rw [hd1] at hs1
  have hb : b = -4 * t := by linear_combination ht3 / 6
  subst hb
  obtain ⟨hA, hB⟩ := centred_quartic_eq_zero (c - 6 * t ^ 2) (e + 2 * c * t - 8 * t ^ 3)
    (r - t) (s - t) (by linear_combination hr2) (by linear_combination hr - ht)
    (by linear_combination hs1) (by linear_combination hs - ht)
  have hc : c = 6 * t ^ 2 := by linear_combination hA
  subst hc
  have he : e = -4 * t ^ 3 := by linear_combination hB
  subst he
  have hg : g = t ^ 4 := by linear_combination ht
  subst hg
  have hα : -(-4 * t) / 4 = t := by ring
  rw [hα]
  simp only [C_neg, C_mul, C_pow, C_ofNat]
  ring

/-! ## Degrees two and three over a field containing the common roots -/

/-- Casas-Alvero in degree 3, root form: over a field `L` of characteristic zero,
if a monic cubic `f` shares a root with each of `f'` and `f''`, then
`f = (X - α) ^ 3` with `α = -a₂ / 3`. -/
theorem eq_X_sub_C_pow_three_of_common_roots {L : Type*} [Field L] [CharZero L] (f : L[X])
    (hm : f.Monic) (hd : f.natDegree = 3)
    (hroot : ∀ i : ℕ, 1 ≤ i → i < 3 → ∃ a : L, f.eval a = 0 ∧ (derivative^[i] f).eval a = 0) :
    f = (X - C (-(f.coeff 2) / 3)) ^ 3 := by
  have hf := eq_cubic f hm hd
  generalize f.coeff 2 = b at hf ⊢
  generalize f.coeff 1 = c at hf
  generalize f.coeff 0 = e at hf
  subst hf
  have hev : ∀ x : L, eval x (X ^ 3 + C b * X ^ 2 + C c * X + C e)
      = x ^ 3 + b * x ^ 2 + c * x + e := by
    intro x
    simp
  have hd1 : ∀ x : L, eval x (derivative^[1] (X ^ 3 + C b * X ^ 2 + C c * X + C e))
      = 3 * x ^ 2 + 2 * b * x + c := by
    intro x
    simp only [Function.iterate_one, derivative_X_pow_succ, Nat.cast_ofNat,
      map_add, map_one, derivative_mul, derivative_C, zero_mul, Nat.cast_one, pow_one, zero_add,
      derivative_X, mul_one, add_zero, eval_add, eval_mul, eval_C, eval_one, eval_pow, eval_X,
      add_left_inj]
    ring
  have hd2 : ∀ x : L, eval x (derivative^[2] (X ^ 3 + C b * X ^ 2 + C c * X + C e))
      = 6 * x + 2 * b := by
    intro x
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one, derivative_mul, derivative_C,
      zero_mul, Nat.cast_one, pow_one, zero_add, derivative_X, mul_one, add_zero, derivative_one,
      eval_add, eval_mul, eval_C, eval_one, eval_X]
    ring
  obtain ⟨t, ht, ht2⟩ := hroot 2 (by norm_num) (by norm_num)
  obtain ⟨s, hs, hs1⟩ := hroot 1 (by norm_num) (by norm_num)
  rw [hev] at ht hs
  rw [hd2] at ht2
  rw [hd1] at hs1
  have hb : b = -3 * t := by linear_combination ht2 / 2
  subst hb
  have hA := centred_cubic_eq_zero (c - 3 * t ^ 2) (s - t)
    (by linear_combination hs1) (by linear_combination hs - ht)
  have hc : c = 3 * t ^ 2 := by linear_combination hA
  subst hc
  have he : e = -t ^ 3 := by linear_combination ht
  subst he
  have hα : -(-3 * t) / 3 = t := by ring
  rw [hα]
  simp only [C_neg, C_mul, C_pow, C_ofNat]
  ring

/-- Casas-Alvero in degree 2, root form: over a field `L` of characteristic zero,
if a monic quadratic `f` shares a root with `f'`, then `f = (X - α) ^ 2` with
`α = -a₁ / 2`. -/
theorem eq_X_sub_C_pow_two_of_common_roots {L : Type*} [Field L] [CharZero L] (f : L[X])
    (hm : f.Monic) (hd : f.natDegree = 2)
    (hroot : ∀ i : ℕ, 1 ≤ i → i < 2 → ∃ a : L, f.eval a = 0 ∧ (derivative^[i] f).eval a = 0) :
    f = (X - C (-(f.coeff 1) / 2)) ^ 2 := by
  have hf := eq_quadratic f hm hd
  generalize f.coeff 1 = b at hf ⊢
  generalize f.coeff 0 = c at hf
  subst hf
  obtain ⟨t, ht, ht1⟩ := hroot 1 (by norm_num) (by norm_num)
  have hev : eval t (X ^ 2 + C b * X + C c) = t ^ 2 + b * t + c := by simp
  have hd1 : eval t (derivative^[1] (X ^ 2 + C b * X + C c)) = 2 * t + b := by
    simp [derivative_mul, one_add_one_eq_two]
  rw [hev] at ht
  rw [hd1] at ht1
  have hb : b = -2 * t := by linear_combination ht1
  subst hb
  have hc : c = t ^ 2 := by linear_combination ht
  subst hc
  have hα : -(-2 * t) / 2 = t := by ring
  rw [hα]
  simp only [C_neg, C_mul, C_pow, C_ofNat]
  ring

/-! ## Descent from the algebraic closure -/

/-- Over any field `K`, two polynomials that are not coprime have a common root in
the algebraic closure of `K`. -/
theorem exists_common_root_of_not_isCoprime {K : Type*} [Field K] {p q : K[X]}
    (h : ¬ IsCoprime p q) :
    ∃ a : AlgebraicClosure K, (p.map (algebraMap K (AlgebraicClosure K))).eval a = 0 ∧
      (q.map (algebraMap K (AlgebraicClosure K))).eval a = 0 := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)] at h
  push Not at h
  obtain ⟨a, hpa, hqa⟩ := h
  exact ⟨a, by rw [eval_map_algebraMap]; exact hpa, by rw [eval_map_algebraMap]; exact hqa⟩

/-- The Casas-Alvero hypothesis over `K` yields, for each `1 ≤ i < deg f`, a common
root of `f` and `f^(i)` in the algebraic closure of `K`. -/
theorem common_roots_of_sharesFactorWithDerivatives {K : Type*} [Field K] (f : K[X])
    (h : SharesFactorWithDerivatives f) (i : ℕ) (hi1 : 1 ≤ i) (hi : i < f.natDegree) :
    ∃ a : AlgebraicClosure K, (f.map (algebraMap K (AlgebraicClosure K))).eval a = 0 ∧
      (derivative^[i] (f.map (algebraMap K (AlgebraicClosure K)))).eval a = 0 := by
  obtain ⟨a, ha, hda⟩ := exists_common_root_of_not_isCoprime (h i hi1 hi)
  refine ⟨a, ha, ?_⟩
  rw [iterate_derivative_map]
  exact hda

/-! ## Main theorems -/

/-- **Casas-Alvero conjecture, degree 4** (arXiv:2608.14726, Conjecture 1.1 with
`d = 4`; known, Diaz-Toca and Gonzalez-Vega 2006): over a field `K` of
characteristic zero, a monic quartic `f` with `gcd(f, f^(i)) ≠ 1` for
`i = 1, 2, 3` equals `(X - α) ^ 4` for some `α ∈ K`. -/
theorem casasAlvero_natDegree_eq_four {K : Type*} [Field K] [CharZero K] (f : K[X])
    (hm : f.Monic) (hd : f.natDegree = 4) (h : SharesFactorWithDerivatives f) :
    ∃ α : K, f = (X - C α) ^ 4 := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hdL : (f.map φ).natDegree = 4 := by rw [natDegree_map_eq_of_injective φ.injective, hd]
  have key := eq_X_sub_C_pow_four_of_common_roots (f.map φ) (hm.map φ) hdL
    (fun i hi1 hi => common_roots_of_sharesFactorWithDerivatives f h i hi1 (by omega))
  refine ⟨-(f.coeff 3) / 4, map_injective φ φ.injective ?_⟩
  rw [key, coeff_map]
  simp [Polynomial.map_pow, map_ofNat]

/-- **Casas-Alvero conjecture, degree 3** (arXiv:2608.14726, Conjecture 1.1 with
`d = 3`; known): over a field `K` of characteristic zero, a monic cubic `f` with
`gcd(f, f^(i)) ≠ 1` for `i = 1, 2` equals `(X - α) ^ 3` for some `α ∈ K`. -/
theorem casasAlvero_natDegree_eq_three {K : Type*} [Field K] [CharZero K] (f : K[X])
    (hm : f.Monic) (hd : f.natDegree = 3) (h : SharesFactorWithDerivatives f) :
    ∃ α : K, f = (X - C α) ^ 3 := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hdL : (f.map φ).natDegree = 3 := by rw [natDegree_map_eq_of_injective φ.injective, hd]
  have key := eq_X_sub_C_pow_three_of_common_roots (f.map φ) (hm.map φ) hdL
    (fun i hi1 hi => common_roots_of_sharesFactorWithDerivatives f h i hi1 (by omega))
  refine ⟨-(f.coeff 2) / 3, map_injective φ φ.injective ?_⟩
  rw [key, coeff_map]
  simp [Polynomial.map_pow, map_ofNat]

/-- **Casas-Alvero conjecture, degree 2** (arXiv:2608.14726, Conjecture 1.1 with
`d = 2`; "trivial for `d ≤ 2`"): over a field `K` of characteristic zero, a monic
quadratic `f` with `gcd(f, f') ≠ 1` equals `(X - α) ^ 2` for some `α ∈ K`. -/
theorem casasAlvero_natDegree_eq_two {K : Type*} [Field K] [CharZero K] (f : K[X])
    (hm : f.Monic) (hd : f.natDegree = 2) (h : SharesFactorWithDerivatives f) :
    ∃ α : K, f = (X - C α) ^ 2 := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hdL : (f.map φ).natDegree = 2 := by rw [natDegree_map_eq_of_injective φ.injective, hd]
  have key := eq_X_sub_C_pow_two_of_common_roots (f.map φ) (hm.map φ) hdL
    (fun i hi1 hi => common_roots_of_sharesFactorWithDerivatives f h i hi1 (by omega))
  refine ⟨-(f.coeff 1) / 2, map_injective φ φ.injective ?_⟩
  rw [key, coeff_map]
  simp [Polynomial.map_pow, map_ofNat]

/-- **Casas-Alvero conjecture in degree `d ≤ 4`** (arXiv:2608.14726, Conjecture 1.1
restricted to `d ≤ 4`; known, Diaz-Toca and Gonzalez-Vega 2006): over a field `K`
of characteristic zero, if `f ∈ K[X]` is monic of degree `d ≤ 4` and
`gcd(f, f^(i)) ≠ 1` for `i = 1, …, d - 1`, then `f = (X - α) ^ d` for some
`α ∈ K`.  (For `d ≤ 1` the hypothesis is vacuous and the conclusion is immediate.) -/
theorem casasAlvero_of_natDegree_le_four {K : Type*} [Field K] [CharZero K] (f : K[X])
    (hm : f.Monic) (hd : f.natDegree ≤ 4) (h : SharesFactorWithDerivatives f) :
    ∃ α : K, f = (X - C α) ^ f.natDegree := by
  obtain hn | hn | hn | hn | hn :
      f.natDegree = 0 ∨ f.natDegree = 1 ∨ f.natDegree = 2 ∨ f.natDegree = 3 ∨
        f.natDegree = 4 := by omega
  · refine ⟨0, ?_⟩
    rw [hn, pow_zero]
    exact eq_one_of_natDegree_eq_zero f hm hn
  · refine ⟨-(f.coeff 0), ?_⟩
    rw [hn, pow_one, map_neg, sub_neg_eq_add]
    exact eq_linear f hm hn
  · rw [hn]
    exact casasAlvero_natDegree_eq_two f hm hn h
  · rw [hn]
    exact casasAlvero_natDegree_eq_three f hm hn h
  · rw [hn]
    exact casasAlvero_natDegree_eq_four f hm hn h

end Candidates.CasasAlveroDegreeFour
