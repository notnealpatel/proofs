/-
# A024199 — Bala: a(n) as a half-sum of factorials times extended double factorials

## OEIS source (pulled with `oeis show A024199`, retrieval date 2026-10-21)

```
NAME:     a(n) = (2n-1)!! * Sum_{k=0..n-1}(-1)^k/(2k+1).
TERMS:    0,1,2,13,76,789,7734,110937,1528920,28018665,497895210,11110528485,...
FORMULA (Meijer, Nov 12 2009):
  a(n) = (-1)^(n-1)*(2*n-3)!! + (2*n-1)*a(n-1) with a(0) = 0.
FORMULA (the conjecture; From _Peter Bala_, Nov 15 2016):
  Conjecture: a(n) = 1/2*Sum_{k = 0..2*n-1} (-1)^(n-k+1)*k!*(2*n - 2*k - 3)!!,
  where the double factorial of an odd integer (positive or negative) may be
  defined in terms of the gamma function as
  (2*N - 1)!! = 2^((N+1)/2)*Gamma(N/2 + 1)/sqrt(Pi).
```

## Reading of the extension

As printed, the left side `(2*N - 1)!!` and the right side
`2^((N+1)/2)*Gamma(N/2 + 1)/sqrt(Pi)` use `N` inconsistently; the right side
is the standard Gamma extension of `N!!` for odd `N`
(it gives `1!! = 1`, `(-1)!! = 1`, `(-3)!! = -1`, `(-5)!! = 1/3`).  We
define `extDoubleFactorial N := 2^((N+1)/2) * Γ(N/2 + 1) / √π` for an
integer `N` (real power, real Gamma) and use it only at odd `N`.  The
ground-truth lemmas below show it agrees with `Nat.doubleFactorial` at
positive odd arguments and satisfies `N!! = N * (N-2)!!` at every odd `N`.

## Status

Triage: open (no proof in the entry or found in the literature).  This file
proves it: both sides satisfy `X(n+1) = (2n+1) X(n) + (-1)^n (2n-1)!!` with
`X(0) = 0`; for the right side this follows from a telescoping certificate
`G(k) = (4n - 2 - 4k) * t_n(k)` for the summand `t_n(k)`.
Computational check (exact rationals): the identity holds for `n ≤ 79`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A024199SumDoubleFactorials

open Finset

/-- Bala's Gamma-function extension of the double factorial:
`N!! = 2^((N+1)/2) * Γ(N/2 + 1) / √π`, intended for odd integers `N`. -/
noncomputable def extDoubleFactorial (N : ℤ) : ℝ :=
  (2 : ℝ) ^ (((N : ℝ) + 1) / 2) * Real.Gamma ((N : ℝ) / 2 + 1) / Real.sqrt Real.pi

/-- OEIS A024199: `a(n) = (2n-1)!! * Σ_{k<n} (-1)^k/(2k+1)`.  At `n = 0` the
natural subtraction gives `0!! = 1 = (-1)!!`, and the sum is empty anyway. -/
def a (n : ℕ) : ℚ :=
  ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℚ) * ∑ k ∈ range n, (-1 : ℚ) ^ k / (2 * k + 1)

/-- At `N = 2j - 1`: `(2j-1)!! = 2^j * Γ(j + 1/2) / √π`. -/
theorem extDoubleFactorial_two_mul_sub_one (j : ℤ) :
    extDoubleFactorial (2 * j - 1) =
      (2 : ℝ) ^ j * Real.Gamma ((j : ℝ) + 1 / 2) / Real.sqrt Real.pi := by
  unfold extDoubleFactorial
  have h1 : (((2 * j - 1 : ℤ) : ℝ) + 1) / 2 = ((j : ℤ) : ℝ) := by push_cast; ring
  have h2 : ((2 * j - 1 : ℤ) : ℝ) / 2 + 1 = (j : ℝ) + 1 / 2 := by push_cast; ring
  rw [h1, h2, Real.rpow_intCast]

/-- `(-1)!! = 1` for the Gamma extension. -/
theorem extDoubleFactorial_neg_one : extDoubleFactorial (-1) = 1 := by
  have h := extDoubleFactorial_two_mul_sub_one 0
  norm_num at h
  rw [h, Real.Gamma_one_half_eq]
  have : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

/-- The recurrence `(2j+1)!! = (2j+1) * (2j-1)!!` holds at every integer `j`. -/
theorem extDoubleFactorial_rec (j : ℤ) :
    extDoubleFactorial (2 * j + 1) = (2 * j + 1) * extDoubleFactorial (2 * j - 1) := by
  have hj : (2 * j + 1 : ℤ) = 2 * (j + 1) - 1 := by ring
  rw [hj, extDoubleFactorial_two_mul_sub_one, extDoubleFactorial_two_mul_sub_one]
  have hs : (j : ℝ) + 1 / 2 ≠ 0 := by
    intro h
    have h2 : (2 * j + 1 : ℤ) = 0 := by
      have : ((2 * j + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    omega
  have hG : Real.Gamma (((j + 1 : ℤ) : ℝ) + 1 / 2) = ((j : ℝ) + 1 / 2) * Real.Gamma ((j : ℝ) + 1 / 2) := by
    rw [← Real.Gamma_add_one hs]
    congr 1
    push_cast
    ring
  rw [hG, zpow_add_one₀ (two_ne_zero)]
  ring

/-- The extension agrees with `Nat.doubleFactorial` at positive odd arguments. -/
theorem extDoubleFactorial_two_mul_add_one (m : ℕ) :
    extDoubleFactorial (2 * (m : ℤ) + 1) = ((Nat.doubleFactorial (2 * m + 1) : ℕ) : ℝ) := by
  induction m with
  | zero =>
    have h := extDoubleFactorial_rec 0
    norm_num [extDoubleFactorial_neg_one] at h
    simpa using h
  | succ m ih =>
    have h := extDoubleFactorial_rec ((m : ℤ) + 1)
    have e1 : (2 * ((m : ℤ) + 1) - 1) = 2 * (m : ℤ) + 1 := by ring
    rw [e1, ih] at h
    have e2 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    rw [e2, Nat.doubleFactorial_add_two]
    push_cast at h ⊢
    rw [h]
    ring

/-- `(2n-1)!!` agrees with `Nat.doubleFactorial (2n-1)` for `n : ℕ`
(including `(-1)!! = 1 = 0‼` at `n = 0`). -/
theorem extDoubleFactorial_two_mul_sub_one_nat (n : ℕ) :
    extDoubleFactorial (2 * (n : ℤ) - 1) = ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) := by
  cases n with
  | zero => simpa using extDoubleFactorial_neg_one
  | succ m =>
    have e1 : 2 * ((m + 1 : ℕ) : ℤ) - 1 = 2 * (m : ℤ) + 1 := by push_cast; ring
    have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e1, e2, extDoubleFactorial_two_mul_add_one]

/-- The summand `t_n(k) = (-1)^(n-k+1) * k! * (2n-2k-3)!!` of Bala's formula. -/
noncomputable def term (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((n : ℤ) - k + 1) * (k.factorial : ℝ) *
    extDoubleFactorial (2 * (n : ℤ) - 2 * (k : ℤ) - 3)

/-- `t_{n+1}(k) = -(2n - 2k - 1) * t_n(k)`. -/
theorem term_succ_left (n k : ℕ) :
    term (n + 1) k = -(2 * (n : ℝ) - 2 * k - 1) * term n k := by
  unfold term
  have hE := extDoubleFactorial_rec ((n : ℤ) - k - 1)
  have e1 : 2 * ((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ) - 3 = 2 * ((n : ℤ) - k - 1) + 1 := by
    push_cast; ring
  have e2 : 2 * ((n : ℤ) - k - 1) - 1 = 2 * (n : ℤ) - 2 * (k : ℤ) - 3 := by ring
  have e3 : (((n + 1 : ℕ) : ℤ) - k + 1) = ((n : ℤ) - k + 1) + 1 := by push_cast; ring
  rw [e1, hE, e2, e3, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  push_cast
  ring

/-- `(2n - 2k - 3) * t_n(k+1) = -(k+1) * t_n(k)`. -/
theorem term_succ_right (n k : ℕ) :
    (2 * (n : ℝ) - 2 * k - 3) * term n (k + 1) = -((k : ℝ) + 1) * term n k := by
  have hE := extDoubleFactorial_rec ((n : ℤ) - k - 2)
  have e1 : 2 * ((n : ℤ) - k - 2) + 1 = 2 * (n : ℤ) - 2 * (k : ℤ) - 3 := by ring
  have e2 : 2 * ((n : ℤ) - k - 2) - 1 = 2 * (n : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) - 3 := by
    push_cast; ring
  rw [e1, e2] at hE
  have hsign : (-1 : ℝ) ^ ((n : ℤ) - k + 1) = -(-1 : ℝ) ^ ((n : ℤ) - ((k + 1 : ℕ) : ℤ) + 1) := by
    have e3 : ((n : ℤ) - k + 1) = ((n : ℤ) - ((k + 1 : ℕ) : ℤ) + 1) + 1 := by push_cast; ring
    rw [e3, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    ring
  have hcoef : (2 * (((n : ℤ) - k - 2 : ℤ) : ℝ) + 1) = 2 * (n : ℝ) - 2 * k - 3 := by
    push_cast; ring
  unfold term
  rw [hE, hsign, Nat.factorial_succ, hcoef]
  generalize (-1 : ℝ) ^ ((n : ℤ) - ((k + 1 : ℕ) : ℤ) + 1) = s
  generalize extDoubleFactorial (2 * (n : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) - 3) = E
  push_cast
  ring

/-- Telescoping step: the right side `S(n) = Σ_{k<2n} t_n(k)` satisfies
`S(n+1) = (2n+1) S(n) + 2 (-1)^n (2n-1)!!`. -/
theorem sum_term_succ (n : ℕ) :
    ∑ k ∈ range (2 * (n + 1)), term (n + 1) k =
      (2 * (n : ℝ) + 1) * ∑ k ∈ range (2 * n), term n k +
        2 * (-1 : ℝ) ^ n * extDoubleFactorial (2 * (n : ℤ) - 1) := by
  set G : ℕ → ℝ := fun k => (4 * (n : ℝ) - 2 - 4 * k) * term n k with hG
  have key : ∀ k, term (n + 1) k = (2 * (n : ℝ) + 1) * term n k + (G (k + 1) - G k) := by
    intro k
    have hL := term_succ_left n k
    have hR := term_succ_right n k
    simp only [hG]
    push_cast
    linear_combination hL - 2 * hR
  rw [sum_congr rfl (fun k _ => key k), sum_add_distrib, ← mul_sum, sum_range_sub]
  have hsplit : ∑ k ∈ range (2 * (n + 1)), term n k =
      ∑ k ∈ range (2 * n), term n k + term n (2 * n) + term n (2 * n + 1) := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
  rw [hsplit]
  have hA := term_succ_right n (2 * n)
  have hB := term_succ_right n (2 * n + 1)
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring] at hB
  have h0 : term n 0 = -(-1 : ℝ) ^ n * extDoubleFactorial (2 * (n : ℤ) - 3) := by
    unfold term
    have e : ((n : ℤ) - ((0 : ℕ) : ℤ) + 1) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_natCast]
    simp
  have hE := extDoubleFactorial_rec ((n : ℤ) - 1)
  have e1 : 2 * ((n : ℤ) - 1) + 1 = 2 * (n : ℤ) - 1 := by ring
  have e2 : 2 * ((n : ℤ) - 1) - 1 = 2 * (n : ℤ) - 3 := by ring
  rw [e1, e2] at hE
  simp only [hG]
  rw [h0, hE]
  push_cast at hA hB ⊢
  linear_combination hA + 2 * hB

/-- `(2n+1)‼ = (2n+1) * (2n-1)‼` in `ℕ` (with `0‼ = 1` at `n = 0`). -/
theorem doubleFactorial_two_mul_add_one (n : ℕ) :
    Nat.doubleFactorial (2 * n + 1) = (2 * n + 1) * Nat.doubleFactorial (2 * n - 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, Nat.doubleFactorial_add_two,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega]

/-- Meijer's recurrence `a(n+1) = (2n+1) a(n) + (-1)^n (2n-1)!!`. -/
theorem a_succ (n : ℕ) :
    a (n + 1) = (2 * (n : ℚ) + 1) * a n +
      (-1 : ℚ) ^ n * ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℚ) := by
  unfold a
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, doubleFactorial_two_mul_add_one,
    sum_range_succ]
  have h : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- `2 a(n) = Σ_{k<2n} t_n(k)` for every `n`. -/
theorem two_mul_a_eq_sum (n : ℕ) :
    2 * ((a n : ℚ) : ℝ) = ∑ k ∈ range (2 * n), term n k := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [sum_term_succ, ← ih, a_succ, extDoubleFactorial_two_mul_sub_one_nat]
    push_cast
    ring


/-! ## Ground truth -/

example : a 0 = 0 := by simp [a]
example : a 1 = 1 := by simp [a, Nat.doubleFactorial]
example : a 2 = 2 := by norm_num [a, Finset.sum_range_succ, Nat.doubleFactorial]
example : a 3 = 13 := by norm_num [a, Finset.sum_range_succ, Nat.doubleFactorial]
example : a 4 = 76 := by norm_num [a, Finset.sum_range_succ, Nat.doubleFactorial]
example : a 5 = 789 := by norm_num [a, Finset.sum_range_succ, Nat.doubleFactorial]
example : a 6 = 7734 := by norm_num [a, Finset.sum_range_succ, Nat.doubleFactorial]

example : extDoubleFactorial 5 = 15 := by
  have h := extDoubleFactorial_two_mul_add_one 2
  norm_num [Nat.doubleFactorial] at h
  exact h

example : extDoubleFactorial (-3) = -1 := by
  have h := extDoubleFactorial_rec (-1)
  norm_num [extDoubleFactorial_neg_one] at h
  linarith

example : extDoubleFactorial (-5) = 1 / 3 := by
  have h1 := extDoubleFactorial_rec (-1)
  have h2 := extDoubleFactorial_rec (-2)
  norm_num [extDoubleFactorial_neg_one] at h1 h2
  linarith

/-- **Bala's conjecture (A024199, Peter Bala, Nov 15 2016), proved.**

Verbatim: "Conjecture: a(n) = 1/2*Sum_{k = 0..2*n-1} (-1)^(n-k+1)*k!*(2*n - 2*k - 3)!!,
where the double factorial of an odd integer (positive or negative) may be defined
in terms of the gamma function."

For every `n : ℕ`, `a(n) = (1/2) Σ_{k=0}^{2n-1} (-1)^(n-k+1) k! (2n-2k-3)!!`, with the
sign as an integer power and the double factorial as `extDoubleFactorial`. -/
theorem a_eq_half_sum (n : ℕ) :
    ((a n : ℚ) : ℝ) = 1 / 2 * ∑ k ∈ range (2 * n),
      (-1 : ℝ) ^ ((n : ℤ) - k + 1) * (k.factorial : ℝ) *
        extDoubleFactorial (2 * (n : ℤ) - 2 * (k : ℤ) - 3) := by
  have h := two_mul_a_eq_sum n
  unfold term at h
  linarith

end Candidates.A024199SumDoubleFactorials
