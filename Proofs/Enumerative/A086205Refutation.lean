/-
# A086205 — Bala: `det[binomial(i^2 + z, j)] = a(n)` for every complex `z`
# (refuted as stated)

## OEIS source (retrieved with `oeis show A086205` and checked against
## `https://oeis.org/A086205/internal`, 2026-10-21)

```
A086205   NAME:   Determinant of n X n matrix M_(i,j) = binomial(i^2, j).
          OFFSET: 0,3
          DATA:   1,1,6,360,302400,4572288000,1520925880320000,...
          AUTHOR: Benoit Cloitre, Aug 27 2003
          FORMULA: a(n) = Product_{k = 1..n} (2*k-1)!/(k-1)!.
          PROG:   (PARI) a(n)=matdet(matrix(n,n,i,j,binomial(i^2,j)))
FORMULA (block "From _Peter Bala_, Feb 19 2023: (Start)" ... "(End)"),
last line:
  Conjecture: a(n) = the determinant of the n X n matrix
  ( binomial(i^2 + z, j) ) for arbitrary complex z. (End)
```

The PARI program fixes the indexing of the n X n matrix: `1 ≤ i, j ≤ n`.
No later comment, formula or extension in A086205 retracts or amends the
conjecture.

## Status

**Refuted as stated** (`conjecture_false`).  For `n = 1` the matrix is
`(binomial(1 + z, 1)) = (1 + z)`, whose determinant is `1 + z`; this equals
`a(1) = 1` only for `z = 0`.  At `z = 1` it is `2 ≠ 1`.  A Sage check
(`/tmp/claude/a086205.sage`, 2026-10-21) found that for each `1 ≤ n ≤ 5` the
`1 ≤ i, j ≤ n` determinant is a nonconstant polynomial in `z`; for `n = 2` it
is `3z^2/2 + 15z/2 + 6`.

**Probable intent** (`det_cbinom_sq_add_eq`, kernel-checked for every `n`
and every complex `z`).  Index the matrix by `0 ≤ i, j ≤ n`, an
`(n+1) X (n+1)` matrix.  Then the determinant does not depend on `z`: column
`j` is `p_j(i^2)` for the polynomial `p_j(x) = binomial(x + z, j)` of degree
`j` with leading coefficient `1/j!`, so the determinant is
`Vandermonde(0, 1, 4, …, n^2) / ∏ j!`.  At `z = 0` row `0` is
`(1, 0, …, 0)`, so it reduces to the `n X n` matrix of the entry's name.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086205Refutation

open Matrix Polynomial

/-! ## Definition layer -/

/-- The generalized binomial coefficient
`binomial(w, j) = w (w - 1) ⋯ (w - j + 1) / j!` of a complex number `w`. -/
noncomputable def cbinom (w : ℂ) (j : ℕ) : ℂ :=
  (∏ k ∈ Finset.range j, (w - k)) / j.factorial

/-- On natural numbers the generalized binomial coefficient is
`Nat.choose`. -/
theorem cbinom_natCast (m j : ℕ) : cbinom m j = (m.choose j : ℂ) := by
  rw [cbinom, ← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

/-- Ground truth at a non-integer argument: `binomial(1/2, 2) = -1/8`. -/
example : cbinom (1 / 2) 2 = -1 / 8 := by
  simp only [cbinom, one_div, Finset.prod_range_succ, Finset.range_one, Finset.prod_singleton,
    CharP.cast_eq_zero, sub_zero, Nat.cast_one, Nat.factorial_two, Nat.cast_ofNat]
  norm_num

/-- A086205 (offset 0): the determinant of the `n X n` matrix
`M_(i,j) = binomial(i^2, j)`, `1 ≤ i, j ≤ n` (the entry's name and PARI
program).  The index `i : Fin n` stands for the row `i + 1`. -/
def a086205 (n : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin n => ((((i : ℕ) + 1) ^ 2).choose ((j : ℕ) + 1) : ℤ)).det

example : a086205 0 = 1 := by simp [a086205]
example : a086205 1 = 1 := by simp [a086205, Matrix.det_unique]
example : a086205 2 = 6 := by
  rw [a086205, Matrix.det_fin_two]
  decide
example : a086205 3 = 360 := by
  rw [a086205, Matrix.det_fin_three]
  decide
example : a086205 4 = 302400 := by
  rw [a086205, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
  decide

/-! ## The conjecture -/

/-- **Bala's conjecture (A086205, Peter Bala, Feb 19 2023).**

Verbatim: "Conjecture: a(n) = the determinant of the n X n matrix
( binomial(i^2 + z, j) ) for arbitrary complex z."

The `n X n` matrix is indexed by `1 ≤ i, j ≤ n`, as in the entry's name and
PARI program; `i : Fin n` stands for `i + 1`.  `binomial(w, j)` is the
generalized binomial coefficient `cbinom`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, ∀ z : ℂ,
    (Matrix.of fun i j : Fin n => cbinom (((i : ℕ) + 1 : ℂ) ^ 2 + z) ((j : ℕ) + 1)).det =
      a086205 n

/-! ## Refutation -/

/-- **Bala's conjecture is false.**  Counterexample `n = 1`, `z = 1`: the
`1 X 1` matrix is `(binomial(2, 1)) = (2)`, but `a(1) = 1`.  The author
probably intended the `(n+1) X (n+1)` matrix indexed by `0 ≤ i, j ≤ n`; that
form is `det_cbinom_sq_add_eq`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h1 := h 1 1
  have hdet : (Matrix.of fun i j : Fin 1 =>
      cbinom (((i : ℕ) + 1 : ℂ) ^ 2 + 1) ((j : ℕ) + 1)).det = 2 := by
    rw [Matrix.det_unique]
    simp only [cbinom, Fin.val_eq_zero, zero_add, Finset.range_one, CharP.cast_eq_zero, one_pow,
      Finset.prod_singleton, sub_zero, Nat.factorial_one, Nat.cast_one, div_one,
      Fin.default_eq_zero, Fin.isValue, of_apply]
    norm_num
  have ha : a086205 1 = 1 := by simp [a086205, Matrix.det_unique]
  rw [hdet, ha] at h1
  norm_num at h1

/-! ## The probable intent: `0 ≤ i, j ≤ n` -/

/-- Shift invariance: for nodes `x 0, …, x (n-1)` and any `z`,
`det[binomial(x_i + z, j)]_{0 ≤ i, j < n} = Vandermonde(x) / ∏ j!`. -/
theorem det_cbinom_shift (n : ℕ) (x : Fin n → ℂ) (z : ℂ) :
    (Matrix.of fun i j : Fin n => cbinom (x i + z) j).det =
      (∏ j : Fin n, (((j : ℕ).factorial : ℂ))⁻¹) * (Matrix.vandermonde x).det := by
  have hM : (Matrix.of fun i j : Fin n => cbinom (x i + z) j) =
      Matrix.of fun i j : Fin n => (((j : ℕ).factorial : ℂ))⁻¹ *
        (Matrix.of fun i j : Fin n =>
          ((descPochhammer ℂ (j : ℕ)).comp (X + C z)).eval (x i)) i j := by
    ext i j
    simp only [Matrix.of_apply, cbinom, eval_comp, descPochhammer_eval_eq_prod_range, eval_add,
      eval_X, eval_C]
    rw [div_eq_inv_mul]
  rw [hM, Matrix.det_mul_row, ← det_eval_matrixOfPolynomials_eq_det_vandermonde]
  · intro j
    rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]
  · intro j
    exact (monic_descPochhammer ℂ (j : ℕ)).comp_X_add_C z

/-- The `(n+1) X (n+1)` matrix `binomial(i^2, j)`, `0 ≤ i, j ≤ n`, has
determinant `a(n)`: row `0` is `(1, 0, …, 0)`. -/
theorem det_choose_sq_succ (n : ℕ) :
    (Matrix.of fun i j : Fin (n + 1) => (((i : ℕ) ^ 2).choose (j : ℕ) : ℤ)).det =
      a086205 n := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hrest : ∀ j : Fin n, (-1 : ℤ) ^ ((j.succ : Fin (n + 1)) : ℕ) *
      (Matrix.of fun i j : Fin (n + 1) => (((i : ℕ) ^ 2).choose (j : ℕ) : ℤ)) 0 j.succ *
      ((Matrix.of fun i j : Fin (n + 1) => (((i : ℕ) ^ 2).choose (j : ℕ) : ℤ)).submatrix
        Fin.succ (j.succ).succAbove).det = 0 := by
    intro j
    simp [Matrix.of_apply]
  rw [Finset.sum_eq_zero (fun j _ => hrest j), add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.of_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Nat.choose_self, Nat.cast_one, Fin.succAbove_zero, a086205]
  rfl

/-- **Corrected form of Bala's conjecture.**  For every `n` and every
complex `z`, the `(n+1) X (n+1)` matrix `binomial(i^2 + z, j)`,
`0 ≤ i, j ≤ n`, has determinant `a(n)`. -/
theorem det_cbinom_sq_add_eq (n : ℕ) (z : ℂ) :
    (Matrix.of fun i j : Fin (n + 1) => cbinom (((i : ℕ) : ℂ) ^ 2 + z) (j : ℕ)).det =
      a086205 n := by
  have h0 : (Matrix.of fun i j : Fin (n + 1) => cbinom (((i : ℕ) : ℂ) ^ 2 + z) (j : ℕ)).det =
      (Matrix.of fun i j : Fin (n + 1) => cbinom (((i : ℕ) : ℂ) ^ 2 + 0) (j : ℕ)).det := by
    rw [det_cbinom_shift (n + 1) (fun i => ((i : ℕ) : ℂ) ^ 2) z,
      det_cbinom_shift (n + 1) (fun i => ((i : ℕ) : ℂ) ^ 2) 0]
  have hcast : (Matrix.of fun i j : Fin (n + 1) => cbinom (((i : ℕ) : ℂ) ^ 2 + 0) (j : ℕ)) =
      (Int.castRingHom ℂ).mapMatrix
        (Matrix.of fun i j : Fin (n + 1) => (((i : ℕ) ^ 2).choose (j : ℕ) : ℤ)) := by
    ext i j
    simp only [add_zero, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      eq_intCast, Int.cast_natCast]
    rw [← cbinom_natCast]
    push_cast
    rfl
  rw [h0, hcast, ← RingHom.map_det, det_choose_sq_succ]
  rfl

end Candidates.A086205Refutation
