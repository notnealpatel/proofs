/-
# A086205: the determinant identity and its indexing

OEIS A086205, Peter Bala's complex binomial determinant conjecture.
The literal one-based `n`-square statement fails at `n = 1`, `z = 1`:
its determinant is `2`, whereas `a(1) = 1`.
For the zero-based `(n+1)`-square matrix indexed by `0 ≤ i,j ≤ n`,
the determinant identity holds for every natural `n` and complex `z`,
by a Vandermonde shift argument.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086205Refutation

open Matrix Polynomial

/-! ## Definitions -/

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

/-- Examples at a non-integer argument: `binomial(1/2, 2) = -1/8`. -/
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

/-- Bala's conjecture (A086205, Feb 19 2023): the determinant of the
one-based `n`-square matrix `binomial(i²+z,j)` equals `a(n)` for all complex `z`.
Here a `Fin n` index represents `i+1`, and `cbinom` is the generalized
complex binomial coefficient, as in the entry's name and PARI program. -/
def Conjecture : Prop :=
  ∀ n : ℕ, ∀ z : ℂ,
    (Matrix.of fun i j : Fin n => cbinom (((i : ℕ) + 1 : ℂ) ^ 2 + z) ((j : ℕ) + 1)).det =
      a086205 n

/-! ## Refutation -/

/-- The one-based determinant conjecture fails at `n = 1`, `z = 1`:
the determinant is `2`, while `a(1) = 1`. The zero-based `(n+1)`-square
identity is proved in `det_cbinom_sq_add_eq`. -/
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
