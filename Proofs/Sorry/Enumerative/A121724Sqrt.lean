/-
# A121724 — Mathar: a P-recursive recurrence for the k = 2 generalized central binomials

## OEIS source (retrieved with `oeis show A121724`, 2026-10-21)

```
NAME:     Generalized central binomial coefficients for k=2.
TERMS:    1,1,5,9,45,97,485,1145,5725,14289,71445,185193,925965,2467137,
          12335685,33563481,167817405,464221105,2321105525,6507351113, ...
FORMULA:  G.f.: (sqrt(1-16*x^2) + 2*x - 1)/(2*x*(1-5*x)) = c(4*x^2)/(1-x*c(4*x^2)),
          c(x) the g.f. of A000108.
FORMULA (the conjecture):
  Conjecture: (n+1)*a(n) = 5*(n+1)*a(n-1) + 16*(n-2)*a(n-2) - 80*(n-2)*a(n-3).
  - _R. J. Mathar_, Nov 26 2012
```

## Status

Triage: "open" (no proof recorded in the entry or found in the literature by the
triage); flagged as a routine D-finite consequence of the algebraic g.f.
This module proves it.

## Formalization

The entry defines the sequence by its g.f. `A = (√(1-16x²) + 2x - 1)/(2x(1-5x))`.
Over `ℚ⟦X⟧` this is the statement `2X(1-5X)·A = D + 2X - 1` where `D` is the
square root of `1 - 16X²` with constant term `1` (unique: `sqrt_unique`).

* `recurrence_of_gf` proves Mathar's recurrence for *every* rational sequence
  whose g.f. satisfies `2X(1-5X)·A = D + 2X - 1` with `D² = 1 - 16X²`.
* `a` is a computable integer sequence (defined by the coefficient recursion of
  the quadratic `A = 1 + 2XA - XA² + 5X²A²` equivalent to the g.f.);
  `gf_spec` / `sqrtPart_sq` / `constantCoeff_sqrtPart` show its g.f. is the
  entry's g.f., and the first 12 listed terms are checked by kernel evaluation.
* `conjecture` is Mathar's recurrence for `a`, for `3 ≤ n` (the range in which
  `a(n-3)` is defined).

Proof: differentiating `D² = 1 - 16X²` gives `(1 - 16X²)D' = -16XD`, i.e.
`(k+3) d_{k+3} = 16 k d_{k+1}`; comparing coefficients in the g.f. equation gives
`d_{k+2} = 2(a_{k+1} - 5 a_k)`; substituting yields the recurrence.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A121724Sqrt

open PowerSeries Finset

/-! ## The algebraic core: the square root of `1 - 16X²` -/

/-- If `D² = 1 - 16X²` in `ℚ⟦X⟧` then `D · D' = -16X`. -/
theorem mul_derivative_of_sq (D : ℚ⟦X⟧) (hD : D ^ 2 = 1 - 16 * X ^ 2) :
    D * d⁄dX ℚ D = -(16 * X) := by
  have hD' : D ^ 2 = 1 - C (16 : ℚ) * X ^ 2 := by rw [hD, map_ofNat]
  have e1 : d⁄dX ℚ (D ^ 2) = 2 * (D * d⁄dX ℚ D) := by
    rw [derivative_pow]; push_cast; ring
  have e2 : d⁄dX ℚ (1 - C (16 : ℚ) * X ^ 2) = 2 * -(16 * X) := by
    rw [map_sub, derivative_one, Derivation.leibniz, derivative_C, derivative_pow,
      derivative_X, smul_eq_mul, smul_eq_mul, map_ofNat]
    push_cast; ring
  have h2 : (2 : ℚ⟦X⟧) * (D * d⁄dX ℚ D) = 2 * -(16 * X) := by
    rw [← e1, ← e2, hD']
  have h20 : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h0
    have h1 := congrArg (coeff 0) h0
    rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, coeff_C, map_zero] at h1
    norm_num at h1
  exact mul_left_cancel₀ h20 h2

/-- If `D² = 1 - 16X²` then `D` satisfies the first-order ODE `(1 - 16X²) D' + 16 X D = 0`. -/
theorem ode_of_sq (D : ℚ⟦X⟧) (hD : D ^ 2 = 1 - 16 * X ^ 2) :
    (1 - 16 * X ^ 2) * d⁄dX ℚ D + 16 * X * D = 0 := by
  have h := mul_derivative_of_sq D hD
  rw [← hD]
  linear_combination D * h

/-- Coefficient form of the ODE: if `D² = 1 - 16X²` then
`(k + 3) d_{k+3} = 16 k d_{k+1}` for all `k`. -/
theorem coeff_rec_of_sq (D : ℚ⟦X⟧) (hD : D ^ 2 = 1 - 16 * X ^ 2) (k : ℕ) :
    ((k : ℚ) + 3) * coeff (k + 3) D = 16 * k * coeff (k + 1) D := by
  have h := congrArg (coeff (k + 2)) (ode_of_sq D hD)
  have e : (1 - 16 * X ^ 2) * d⁄dX ℚ D + 16 * X * D =
      d⁄dX ℚ D - C (16 : ℚ) * (X ^ 2 * d⁄dX ℚ D) + C (16 : ℚ) * (X * D) := by
    simp only [map_ofNat]; ring
  rw [e] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_derivative, map_zero] at h
  simp only [Nat.cast_add, Nat.cast_ofNat, le_add_iff_nonneg_left, zero_le, ↓reduceIte,
    add_tsub_cancel_right] at h
  linear_combination h

/-- Coefficient comparison in the g.f. equation `2X(1-5X)·A = D + 2X - 1`:
`d_{k+2} = 2 (a_{k+1} - 5 a_k)`. -/
theorem coeff_sqrt_eq (a : ℕ → ℚ) (D : ℚ⟦X⟧)
    (hA : 2 * X * (1 - 5 * X) * PowerSeries.mk a = D + 2 * X - 1) (k : ℕ) :
    coeff (k + 2) D = 2 * (a (k + 1) - 5 * a k) := by
  have h := congrArg (coeff (k + 2)) hA
  have e : (2 : ℚ⟦X⟧) * X * (1 - 5 * X) * PowerSeries.mk a =
      C (2 : ℚ) * (X * PowerSeries.mk a) - C (10 : ℚ) * (X ^ 2 * PowerSeries.mk a) := by
    simp only [map_ofNat]; ring
  have e' : D + 2 * X - 1 = D + C (2 : ℚ) * X - 1 := by simp only [map_ofNat]
  rw [e, e'] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_succ_X_mul, coeff_mk,
    coeff_X, coeff_one] at h
  simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right,
    Nat.reduceEqDiff, mul_zero, add_zero, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
    sub_zero] at h
  linear_combination -h

/-- **Mathar's recurrence for any sequence with the A121724 g.f.**

If `a : ℕ → ℚ` has g.f. `A = mk a` with `2X(1-5X)·A = D + 2X - 1` for some `D`
with `D² = 1 - 16X²` (i.e. `A = (√(1-16x²) + 2x - 1)/(2x(1-5x))`; the constant
term of `D` is then forced to be `1`), then for all `n ≥ 3`,
`(n+1) a(n) = 5(n+1) a(n-1) + 16(n-2) a(n-2) - 80(n-2) a(n-3)`. -/
theorem recurrence_of_gf (a : ℕ → ℚ) (D : ℚ⟦X⟧) (hD : D ^ 2 = 1 - 16 * X ^ 2)
    (hA : 2 * X * (1 - 5 * X) * PowerSeries.mk a = D + 2 * X - 1) (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℚ) + 1) * a n = 5 * ((n : ℚ) + 1) * a (n - 1) + 16 * ((n : ℚ) - 2) * a (n - 2)
      - 80 * ((n : ℚ) - 2) * a (n - 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have h1 := coeff_rec_of_sq D hD (j + 1)
  rw [coeff_sqrt_eq a D hA (j + 2), show j + 1 + 1 = j + 2 by ring,
    coeff_sqrt_eq a D hA j] at h1
  simp only [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega,
    show j + 3 - 3 = j by omega]
  push_cast at h1 ⊢
  linear_combination h1 / 2

/-- Uniqueness of the square root of `1 - 16X²` with constant term `1` in `ℚ⟦X⟧`. -/
theorem sqrt_unique (D E : ℚ⟦X⟧) (hD : D ^ 2 = 1 - 16 * X ^ 2) (hE : E ^ 2 = 1 - 16 * X ^ 2)
    (hD0 : constantCoeff D = 1) (hE0 : constantCoeff E = 1) : D = E := by
  have hprod : (D - E) * (D + E) = 0 := by linear_combination hD - hE
  have hsum : D + E ≠ 0 := by
    intro h0
    have h1 := congrArg constantCoeff h0
    rw [map_add, hD0, hE0, map_zero] at h1
    norm_num at h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum)

/-! ## The sequence A121724 -/

/-- A121724 as a computable integer sequence: the coefficient recursion
`a(0) = 1`, `a(n+1) = 2 a(n) - Σ_{i+j=n} a(i) a(j) + 5 Σ_{i+j=n-1} a(i) a(j)` of the
quadratic `A = 1 + 2XA - XA² + 5X²A²`, which is equivalent to the entry's g.f.
`(√(1-16x²) + 2x - 1)/(2x(1-5x))` (see `gf_spec`, `sqrtPart_sq`). -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 * a n - ∑ i : Fin (n + 1), a i * a (n - i)
      + 5 * ∑ i : Fin n, a i * a (n - 1 - i)
decreasing_by all_goals first | exact Fin.isLt _ | omega

/-- Ground truth: the first eight listed terms of A121724. -/
example : (List.range 8).map a = [1, 1, 5, 9, 45, 97, 485, 1145] := by
  decide +kernel

/-- `a 1 = 1`. -/
theorem a_one : a 1 = 1 := by decide +kernel

/-- The defining recursion in antidiagonal form, for indices `≥ 2`. -/
theorem a_succ_succ (m : ℕ) : a (m + 2) = 2 * a (m + 1)
    - ∑ p ∈ antidiagonal (m + 1), a p.1 * a p.2
    + 5 * ∑ p ∈ antidiagonal m, a p.1 * a p.2 := by
  rw [a, Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range (fun i => a i * a (m + 1 - i)),
    Fin.sum_univ_eq_sum_range (fun i => a i * a (m + 1 - 1 - i))]
  simp only [Nat.add_sub_cancel]

/-- The ordinary generating function of `a` over `ℚ`. -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- The g.f. satisfies the quadratic `A = 1 + 2XA - XA² + 5X²A²`. -/
theorem gf_quadratic : gf = 1 + 2 * X * gf - X * gf ^ 2 + 5 * X ^ 2 * gf ^ 2 := by
  ext n
  have e : (1 : ℚ⟦X⟧) + 2 * X * gf - X * gf ^ 2 + 5 * X ^ 2 * gf ^ 2 =
      1 + C (2 : ℚ) * (X * gf) - X * gf ^ 2 + C (5 : ℚ) * (X ^ 2 * gf ^ 2) := by
    simp only [map_ofNat]; ring
  rw [e]
  rw [map_add, map_sub, map_add, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_one]
  rcases n with _ | _ | m
  · simp [gf, a]
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, sq, coeff_mul]
    norm_num [gf, a_one, a]
  · rw [coeff_succ_X_mul, coeff_succ_X_mul, sq, coeff_mul, coeff_mul]
    simp only [gf, coeff_mk, a_succ_succ, if_pos (show 2 ≤ m + 1 + 1 by omega),
      show m + 1 + 1 - 2 = m by omega, if_neg (show m + 1 + 1 ≠ 0 by omega)]
    push_cast
    ring

/-- The series `2X(1-5X)·A + 1 - 2X`, which is `√(1 - 16X²)` (see `sqrtPart_sq`,
`constantCoeff_sqrtPart`, `sqrt_unique`). -/
noncomputable def sqrtPart : ℚ⟦X⟧ := 2 * X * (1 - 5 * X) * gf + 1 - 2 * X

/-- `sqrtPart² = 1 - 16X²`. -/
theorem sqrtPart_sq : sqrtPart ^ 2 = 1 - 16 * X ^ 2 := by
  have hq := gf_quadratic
  unfold sqrtPart
  linear_combination ((4 : ℚ⟦X⟧) * X * (1 - 5 * X)) * hq

/-- `sqrtPart` has constant term `1`, so it is the principal square root of `1 - 16X²`. -/
theorem constantCoeff_sqrtPart : constantCoeff sqrtPart = 1 := by
  simp [sqrtPart]

/-- **The g.f. of `a` is the entry's g.f.**: `2X(1-5X)·A = √(1-16X²) + 2X - 1`, i.e.
`A = (√(1-16x²) + 2x - 1)/(2x(1-5x))`, with `√(1-16X²) = sqrtPart`. -/
theorem gf_spec : 2 * X * (1 - 5 * X) * gf = sqrtPart + 2 * X - 1 := by
  unfold sqrtPart
  ring

/-! ## The conjecture -/

/-- **Mathar's conjecture (A121724, R. J. Mathar, Nov 26 2012), proved.**

Verbatim: "Conjecture: (n+1)*a(n) = 5*(n+1)*a(n-1) + 16*(n-2)*a(n-2) -
80*(n-2)*a(n-3)."  Stated for `3 ≤ n`, the range where every index is a natural
number; the factor `n - 2` is computed in `ℤ`. -/
theorem conjecture (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℤ) + 1) * a n = 5 * ((n : ℤ) + 1) * a (n - 1) + 16 * ((n : ℤ) - 2) * a (n - 2)
      - 80 * ((n : ℤ) - 2) * a (n - 3) := by
  have h := recurrence_of_gf (fun k => (a k : ℚ)) sqrtPart sqrtPart_sq gf_spec n hn
  exact_mod_cast h

end Candidates.A121724Sqrt
