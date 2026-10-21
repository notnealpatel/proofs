/-
# A317297 — maximum eigenvalue of the even boustrophedon matrix

## OEIS source (retrieved with `oeis show A317297`, 2026-10-21)

```
NAME:     a(n) = (n - 1)*(4*n^2 - 8*n + 5).
TERMS:    0,5,34,111,260,505,870,1379,2056,2925,4010,5335,6924,8801,10990,...
COMMENT (the conjecture):
  Conjecture: For n > 1, a(n) is the maximum eigenvalue of a 2*(n-1) X 2*(n-1)
  square matrix M defined as M[i,j,n] = j + n*(i-1) if i is odd and
  M[i,j,n] = n*i - j + 1 if i is even (see A317614). - _Stefano Spezia_, Dec 27 2018
```

Here the `n` inside `M[i,j,n]` is the matrix size (`N = 2*(n-1)`), as in
A317614: "M(n) is defined as M[i,j,n] = j + n*(i-1) if i is odd and
M[i,j,n] = n*i - j + 1 if i is even".

Sibling conjectures (A322844, Stefano Spezia): for `N > 1`, A322844(N) is the
absolute value of the coefficient of `x^(N-2)` in the characteristic polynomial
of `M(N)`, and the traces of the higher exterior powers vanish.  Both follow from
the unified identity `charpoly M(N) = X^(N-2) * (X^2 - A317614(N) X - A322844(N))`,
proved below as `charpoly_castBoustrophedon_rat`.

## Status

Triage: open — no proof in the entry or in the cross-referenced entries
(A317614 records only `det M(N) = 0` for `N > 2` as proved; A317617 records the
column sums).  The triage did not search the literature beyond OEIS.

## Proof route

`M = A * B` with `A : N × 2` (columns: row offset `alpha`, row slope `beta`) and
`B : 2 × N` (rows: `1`, `j`).  `Matrix.charpoly_mul_comm_of_le` reduces the
charpoly to that of the `2 × 2` matrix `B * A`, whose entries are parity-split
closed-form sums.  For even `N = 2m`, `B * A` is lower triangular with diagonal
`m (4 m^2 + 1)` and `-m`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A317297Boustrophedon

open Polynomial

/-- The `N × N` boustrophedon matrix of A317614 (0-indexed storage, 1-indexed formula). -/
def boustrophedon (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := fun i j =>
  let i' : ℤ := (i : ℕ) + 1
  let j' : ℤ := (j : ℕ) + 1
  if Odd ((i : ℕ) + 1) then j' + N * (i' - 1) else N * i' - j' + 1

example : boustrophedon 2 = !![1, 2; 4, 3] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

example : boustrophedon 3 = !![1, 2, 3; 6, 5, 4; 7, 8, 9] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

example : boustrophedon 4 = !![1, 2, 3, 4; 8, 7, 6, 5; 9, 10, 11, 12; 16, 15, 14, 13] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- Trace check against A317614: `trace M(4) = 32`. -/
example : (boustrophedon 4).trace = 32 := by decide

/-- First column of the left factor: the constant term of row `i` (0-indexed). -/
def alpha (N i : ℕ) : ℤ := if Odd (i + 1) then (N : ℤ) * i else (N : ℤ) * (i + 1) + 1

/-- Second column of the left factor: the slope of row `i` (0-indexed). -/
def beta (i : ℕ) : ℤ := if Odd (i + 1) then 1 else -1

/-- Left factor `A : N × 2`, rows `[alpha N i, beta i]`. -/
def leftFactor (N : ℕ) : Matrix (Fin N) (Fin 2) ℤ := fun i => ![alpha N i, beta i]

/-- Right factor `B : 2 × N`, rows `1` and `j + 1` (the 1-indexed column). -/
def rightFactor (N : ℕ) : Matrix (Fin 2) (Fin N) ℤ := fun k j => ![1, (j : ℕ) + 1] k

/-- Rank-two factorization: row `i` of `M(N)` is `alpha i + beta i * j` (1-indexed `j`). -/
theorem boustrophedon_eq_mul (N : ℕ) : boustrophedon N = leftFactor N * rightFactor N := by
  ext i j
  simp only [boustrophedon, leftFactor, rightFactor, alpha, beta, Matrix.mul_apply,
    Fin.sum_univ_two]
  split_ifs <;>
    simp only [add_sub_cancel_right, Fin.isValue, Matrix.cons_val_zero, Nat.cast_one, mul_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_add, one_mul, Int.reduceNeg,
      neg_mul, neg_add_rev, add_add_neg_add_cancel] <;> ring

/-- Over an even number of rows the slopes `±1` cancel. -/
theorem sum_beta (k : ℕ) : ∑ i ∈ Finset.range (2 * k), beta i = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp [beta, parity_simps]

/-- Sum of the row offsets over the first `2k` rows: `2 N k^2 + k`. -/
theorem sum_alpha (N k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), alpha N i = 2 * (N : ℤ) * k ^ 2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [alpha, even_two, Even.mul_right, Even.add_one, ↓reduceIte, Nat.cast_mul,
      Nat.cast_ofNat, Nat.odd_add, Nat.not_even_one, iff_false, not_true_eq_false, Nat.cast_add,
      Nat.cast_one]
    ring

/-- Weighted slope sum over the first `2k` rows: `-k`. -/
theorem sum_succ_mul_beta (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), ((i : ℤ) + 1) * beta i = -k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [Nat.cast_mul, Nat.cast_ofNat, beta, even_two, Even.mul_right, Even.add_one,
      ↓reduceIte, mul_one, Nat.cast_add, Nat.cast_one, Nat.odd_add, Nat.not_even_one, iff_false,
      not_true_eq_false, Int.reduceNeg, mul_neg, neg_add_rev]
    ring

/-- For even size `2m`, `B * A` is lower triangular with diagonal `m(4m^2+1)`, `-m`. -/
theorem rightFactor_mul_leftFactor_even (m : ℕ) :
    rightFactor (2 * m) * leftFactor (2 * m) =
      !![(m : ℤ) * (4 * m ^ 2 + 1), 0; ∑ i ∈ Finset.range (2 * m), ((i : ℤ) + 1) * alpha (2 * m) i,
        -m] := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp only [rightFactor, leftFactor, Matrix.mul_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Nat.cast_add, Nat.cast_one, one_mul]
  · rw [Fin.sum_univ_eq_sum_range (fun i => alpha (2 * m) i), sum_alpha]
    push_cast; ring
  · rw [Fin.sum_univ_eq_sum_range (fun i => beta i), sum_beta]
  · rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℤ) + 1) * alpha (2 * m) i)]
  · rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℤ) + 1) * beta i), sum_succ_mul_beta]

/-- For even size `2m ≥ 2`: `charpoly M(2m) = X^(2m-2) (X - m(4m^2+1)) (X + m)` over `ℤ`. -/
theorem charpoly_boustrophedon_even (m : ℕ) (hm : 1 ≤ m) :
    (boustrophedon (2 * m)).charpoly =
      X ^ (2 * m - 2) * ((X - C ((m : ℤ) * (4 * m ^ 2 + 1))) * (X + C (m : ℤ))) := by
  have hle : Fintype.card (Fin 2) ≤ Fintype.card (Fin (2 * m)) := by
    simp only [Fintype.card_fin]; omega
  rw [boustrophedon_eq_mul, Matrix.charpoly_mul_comm_of_le _ _ hle,
    rightFactor_mul_leftFactor_even, Matrix.charpoly_fin_two, Matrix.trace_fin_two_of,
    Matrix.det_fin_two_of]
  simp only [Fintype.card_fin, zero_mul, sub_zero, map_add, map_mul, map_neg, map_pow,
    map_natCast, map_ofNat, map_one]
  ring

/-- A317297: `a(n) = (n - 1) * (4 n^2 - 8 n + 5)`, computed in `ℤ` (offset 1). -/
def a317297 (n : ℕ) : ℤ := ((n : ℤ) - 1) * (4 * (n : ℤ) ^ 2 - 8 * n + 5)

example : (List.range 7).map (fun n => a317297 (n + 1)) = [0, 5, 34, 111, 260, 505, 870] := by
  decide

/-- Reindexed closed form: `a(m + 1) = m (4 m^2 + 1)`. -/
theorem a317297_succ (m : ℕ) : a317297 (m + 1) = (m : ℤ) * (4 * m ^ 2 + 1) := by
  unfold a317297; push_cast; ring

/-- The boustrophedon matrix with entries cast into a commutative ring `R`. -/
def castBoustrophedon (R : Type*) [CommRing R] (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  (boustrophedon N).map (Int.castRingHom R)

/-- The even-size charpoly factorization after casting into any nontrivial commutative ring. -/
theorem charpoly_castBoustrophedon_even (R : Type*) [CommRing R] [Nontrivial R] (m : ℕ)
    (hm : 1 ≤ m) :
    (castBoustrophedon R (2 * m)).charpoly =
      X ^ (2 * m - 2) * ((X - C ((m : R) * (4 * m ^ 2 + 1))) * (X + C (m : R))) := by
  rw [castBoustrophedon, Matrix.charpoly_map, charpoly_boustrophedon_even m hm]
  have e1 : Int.castRingHom R ((m : ℤ) * (4 * m ^ 2 + 1)) = (m : R) * (4 * m ^ 2 + 1) := by
    simp only [eq_intCast, Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_one]
  have e2 : Int.castRingHom R (m : ℤ) = (m : R) := by simp
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C,
    e1, e2]

/-- Over a domain, every root of `charpoly M(2m)` is `0`, `m(4m^2+1)` or `-m`. -/
theorem eq_of_isRoot_charpoly_even (R : Type*) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m)
    (μ : R) (hμ : (castBoustrophedon R (2 * m)).charpoly.IsRoot μ) :
    μ = 0 ∨ μ = (m : R) * (4 * m ^ 2 + 1) ∨ μ = -m := by
  rw [charpoly_castBoustrophedon_even R m hm] at hμ
  simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C, mul_eq_zero, pow_eq_zero_iff',
    sub_eq_zero] at hμ
  rcases hμ with ⟨h0, -⟩ | h | h
  · exact Or.inl h0
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

/-- `m(4m^2+1)` is a root of `charpoly M(2m)` for `m ≥ 1`. -/
theorem isRoot_charpoly_even_top (R : Type*) [CommRing R] [Nontrivial R] (m : ℕ) (hm : 1 ≤ m) :
    (castBoustrophedon R (2 * m)).charpoly.IsRoot ((m : R) * (4 * m ^ 2 + 1)) := by
  rw [charpoly_castBoustrophedon_even R m hm]
  simp

/-- **A317297 conjecture (Stefano Spezia, Dec 27 2018).**
For `n ≥ 2`, `a(n) = (n-1)(4n^2-8n+5)` is the maximum (real) eigenvalue of the
`2(n-1) × 2(n-1)` boustrophedon matrix `M[i,j] = j + N(i-1)` (`i` odd),
`N i - j + 1` (`i` even), `N = 2(n-1)`. -/
theorem a317297_isGreatest_eigenvalue (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest
      {μ : ℝ | Module.End.HasEigenvalue (Matrix.toLin' (castBoustrophedon ℝ (2 * (n - 1)))) μ}
      (a317297 n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [show m + 1 - 1 = m by omega]
  have ha : (a317297 (m + 1) : ℝ) = (m : ℝ) * (4 * m ^ 2 + 1) := by
    rw [a317297_succ]; push_cast; ring
  simp only [ha, Set.mem_ofPred_eq, IsGreatest, upperBounds,
    Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
  refine ⟨isRoot_charpoly_even_top ℝ m hm, fun μ hμ => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases eq_of_isRoot_charpoly_even ℝ m hm μ hμ with h | h | h
  · rw [h]; positivity
  · exact h.le
  · rw [h]; nlinarith

/-- Every complex eigenvalue of the `2(n-1) × 2(n-1)` boustrophedon matrix is `0`, `a(n)` or
`-(n-1)`; in particular the spectrum is real, so "maximum eigenvalue" is unambiguous. -/
theorem a317297_complex_eigenvalues (n : ℕ) (hn : 2 ≤ n) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (castBoustrophedon ℂ (2 * (n - 1)))) μ) :
    μ = 0 ∨ μ = (a317297 n : ℂ) ∨ μ = -((n : ℂ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega] at hμ
  have hm : 1 ≤ m := by omega
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin'] at hμ
  rw [a317297_succ]
  push_cast
  simpa only [add_sub_cancel_right] using eq_of_isRoot_charpoly_even ℂ m hm μ hμ

/-! ## Unified characteristic polynomial (all sizes) -/

/-- Weighted offset sum over the first `2k` rows: `3 Σ = N(8k^3+3k^2+k) + 3k^2 + 3k`. -/
theorem three_mul_sum_succ_mul_alpha (N k : ℕ) :
    3 * ∑ i ∈ Finset.range (2 * k), ((i : ℤ) + 1) * alpha N i =
      (N : ℤ) * (8 * k ^ 3 + 3 * k ^ 2 + k) + 3 * k ^ 2 + 3 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      mul_add, mul_add, ih]
    simp only [Nat.cast_mul, Nat.cast_ofNat, alpha, even_two, Even.mul_right, Even.add_one,
      ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.odd_add, Nat.not_even_one, iff_false,
      not_true_eq_false]
    ring

/-- The entries of `B * A` as sums over `range N`. -/
theorem rightFactor_mul_leftFactor (N : ℕ) :
    rightFactor N * leftFactor N =
      !![∑ i ∈ Finset.range N, alpha N i, ∑ i ∈ Finset.range N, beta i;
        ∑ i ∈ Finset.range N, ((i : ℤ) + 1) * alpha N i,
        ∑ i ∈ Finset.range N, ((i : ℤ) + 1) * beta i] := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp only [rightFactor, leftFactor, Matrix.mul_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Nat.cast_add, Nat.cast_one, one_mul]
  · exact Fin.sum_univ_eq_sum_range (fun i => alpha N i) N
  · exact Fin.sum_univ_eq_sum_range (fun i => beta i) N
  · exact Fin.sum_univ_eq_sum_range (fun i => ((i : ℤ) + 1) * alpha N i) N
  · exact Fin.sum_univ_eq_sum_range (fun i => ((i : ℤ) + 1) * beta i) N

/-- A317614: `a(n) = (n^3 + n * (n mod 2)) / 2`, the trace of the boustrophedon matrix. -/
def a317614 (n : ℕ) : ℚ := (1 / 2) * ((n : ℚ) ^ 3 + n * ((n % 2 : ℕ) : ℚ))

/-- A322844 (offset 0): `a(n) = n^2 * (3 * (1 + n^2) - 2 * (2 + n^2) * (n mod 2)) / 12`. -/
def a322844 (n : ℕ) : ℚ :=
  (1 / 12) * (n : ℚ) ^ 2 * (3 * (1 + (n : ℚ) ^ 2) - 2 * (2 + (n : ℚ) ^ 2) * ((n % 2 : ℕ) : ℚ))

example : (List.range 7).map (fun n => a317614 (n + 1)) = [1, 4, 15, 32, 65, 108, 175] := by
  simp only [List.range_succ, List.range_zero, a317614]
  norm_num

example : (List.range 7).map a322844 = [0, 0, 5, 6, 68, 50, 333] := by
  simp only [List.range_succ, List.range_zero]
  norm_num [a322844]

/-- The 2 × 2 compressed matrix `B * A`. -/
def compressed (N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := rightFactor N * leftFactor N

/-- `charpoly M(N) = X^(N-2) * charpoly (B * A)` written via trace and determinant. -/
theorem charpoly_boustrophedon_compressed (N : ℕ) (hN : 2 ≤ N) :
    (boustrophedon N).charpoly =
      X ^ (N - 2) * (X ^ 2 - C (compressed N).trace * X + C (compressed N).det) := by
  have hle : Fintype.card (Fin 2) ≤ Fintype.card (Fin N) := by
    simp only [Fintype.card_fin]; exact hN
  rw [boustrophedon_eq_mul, Matrix.charpoly_mul_comm_of_le _ _ hle, ← compressed,
    Matrix.charpoly_fin_two]
  simp only [Fintype.card_fin]

/-- `trace (B * A) = trace M(N) = A317614(N)`. -/
theorem trace_compressed (N : ℕ) : ((compressed N).trace : ℚ) = a317614 N := by
  rw [compressed, rightFactor_mul_leftFactor, Matrix.trace_fin_two_of]
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · rw [sum_alpha, sum_succ_mul_beta, a317614]
    have hmod : 2 * k % 2 = 0 := by omega
    rw [hmod]; push_cast; ring
  · rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => ((i : ℤ) + 1) * beta i), sum_alpha,
      sum_succ_mul_beta, a317614]
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    rw [hmod]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, alpha, even_two,
      Even.mul_right, Even.add_one, ↓reduceIte, beta, mul_one, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Int.cast_pow, Int.cast_neg, one_div]
    ring

/-- `det (B * A) = -A322844(N)`. -/
theorem det_compressed (N : ℕ) : ((compressed N).det : ℚ) = -a322844 N := by
  rw [compressed, rightFactor_mul_leftFactor, Matrix.det_fin_two_of]
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · rw [sum_alpha, sum_succ_mul_beta, sum_beta, a322844]
    have hmod : 2 * k % 2 = 0 := by omega
    rw [hmod]; push_cast; ring
  · have hS := three_mul_sum_succ_mul_alpha (2 * k + 1) k
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => beta i),
      Finset.sum_range_succ (fun i => ((i : ℤ) + 1) * alpha (2 * k + 1) i),
      Finset.sum_range_succ (fun i => ((i : ℤ) + 1) * beta i), sum_alpha,
      sum_succ_mul_beta, sum_beta, a322844]
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    rw [hmod]
    generalize (∑ i ∈ Finset.range (2 * k), ((i : ℤ) + 1) * alpha (2 * k + 1) i) = S at hS ⊢
    have hSq : (3 : ℚ) * (S : ℚ) = ((2 * k + 1 : ℕ) : ℚ) * (8 * k ^ 3 + 3 * k ^ 2 + k) +
        3 * k ^ 2 + 3 * k := by
      exact_mod_cast hS
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, alpha, even_two,
      Even.mul_right, Even.add_one, ↓reduceIte, beta, mul_one, zero_add, one_mul, Int.cast_sub,
      Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, Int.cast_pow,
      Int.cast_neg, one_div]
    push_cast at hSq
    linear_combination (-1 / 3 : ℚ) * hSq

/-- **Unified characteristic polynomial (A317614 / A322844 / A317297).**
For every size `N ≥ 2`,
`charpoly M(N) = X^(N-2) * (X^2 - A317614(N) X - A322844(N))` over `ℚ`.
This settles the A322844 conjectures (Stefano Spezia): the `x^(N-2)` coefficient is
`-A322844(N)` and all lower coefficients (traces of exterior powers `k > 2`) vanish. -/
theorem charpoly_castBoustrophedon_rat (N : ℕ) (hN : 2 ≤ N) :
    (castBoustrophedon ℚ N).charpoly =
      X ^ (N - 2) * (X ^ 2 - C (a317614 N) * X - C (a322844 N)) := by
  rw [castBoustrophedon, Matrix.charpoly_map, charpoly_boustrophedon_compressed N hN]
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_C, eq_intCast, eq_intCast, trace_compressed, det_compressed,
    map_neg, sub_eq_add_neg _ (C (a322844 N))]

end Candidates.A317297Boustrophedon
