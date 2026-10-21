/-
# A188570 — Kimberling: every prime divides infinitely many terms (refuted)

## OEIS source (retrieved with `oeis show A188570`, 2026-10-21)

```
NAME:     a(n) = coefficient of the term that is independent of sqrt(2) and
          sqrt(3) in the expansion of (1 + sqrt(2) + sqrt(3))^n.
TERMS:    1,1,6,16,80,296,1296,5216,21952,90304,375936,1555456,6456320,...
COMMENT:  From _Clark Kimberling_, Oct 23 2024: (Start)
          Conjecture: every prime divides a(n) for infinitely many n, and if
          K(p) = (k(1), k(2),...) is the maximal subsequence of indices n such
          that p divides a(n), then the difference sequence of K(p) is
          eventually periodic; indeed, K(p) is purely periodic for the first 6
          primes, with respective period lengths 1,5,5,3,3,5 and these
          periods: [rows for p = 2, 3, 5, 7, 11, 13 omitted] (End)
FORMULA:  a(n) = 4*a(n-1) + 4*a(n-2) - 16*a(n-3) + 8*a(n-4).
          - _Vaclav Kotesovec_, Aug 13 2013
```

No later comment in the entry retracts or corrects the conjecture.

## This module refutes the conjecture

The prime `23` divides no term.  Writing `(1 + √2 + √3)^n` in the basis
`1, √2, √3, √6` with integer coefficients, the coefficient vector modulo `23`
returns to `(1, 0, 0, 0)` after `22` steps, so `a(n) mod 23` is purely periodic
with period `22`, and none of the residues `a(0), …, a(21) mod 23` is `0`
(they are `1, 1, 6, 16, 11, 20, 8, 18, 10, 6, 1, 12, 13, 17, 5, 22, 9, 19, 7,
21, 18, 12`).  A floating-point-free scan of the primes below `400` (Python,
exact integers) finds exactly three primes that never divide a term:
`23, 71, 311`.  (Independently of the refutation, the printed period rows do
not match their labels: the row printed for `p = 2` is the difference pattern
of `K(3)` and the row printed for `p = 3` is that of `K(5)`.)

Everything below is kernel-checked; no `sorry` and no `native_decide`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A188570Refutation

/-! ## Definition layer -/

/-- Multiplication in `ℤ[√2, √3]` (more generally in `R[√2, √3]`) written in
coordinates for the basis `1, √2, √3, √6`: the quadruple `(a, b, c, d)` stands
for `a + b√2 + c√3 + d√6`. -/
def q4mul {R : Type*} [CommSemiring R] (x y : R × R × R × R) : R × R × R × R :=
  (x.1 * y.1 + 2 * x.2.1 * y.2.1 + 3 * x.2.2.1 * y.2.2.1 + 6 * x.2.2.2 * y.2.2.2,
   x.1 * y.2.1 + x.2.1 * y.1 + 3 * x.2.2.1 * y.2.2.2 + 3 * x.2.2.2 * y.2.2.1,
   x.1 * y.2.2.1 + x.2.2.1 * y.1 + 2 * x.2.1 * y.2.2.2 + 2 * x.2.2.2 * y.2.1,
   x.1 * y.2.2.2 + x.2.2.2 * y.1 + x.2.1 * y.2.2.1 + x.2.2.1 * y.2.1)

/-- Multiplication by `1 + √2 + √3`, in the coordinates of `q4mul`. -/
def alphaStep {R : Type*} [CommSemiring R] (x : R × R × R × R) : R × R × R × R :=
  q4mul x (1, 1, 1, 0)

/-- The integer coordinates `(a, b, c, d)` of `(1 + √2 + √3)^n = a + b√2 + c√3 + d√6`
(see `coeffs_real` for the real identity and `coeffs_unique` for uniqueness). -/
def coeffs : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 => alphaStep (coeffs n)

/-- OEIS A188570: `a(n)` is the coefficient of the term independent of `√2` and
`√3` in the expansion of `(1 + √2 + √3)^n`. -/
def a188570 (n : ℕ) : ℤ := (coeffs n).1

-- Ground truth: the first 26 terms of the OEIS DATA line.
example : (List.range 26).map a188570 =
    [1, 1, 6, 16, 80, 296, 1296, 5216, 21952, 90304, 375936, 1555456, 6456320,
      26754560, 110963712, 460015616, 1907494912, 7908659200, 32792076288,
      135963148288, 563742310400, 2337417887744, 9691567030272, 40183767891968,
      166612591968256, 690819710058496] := by
  decide

/-! ## Bridge to the real expansion -/

/-- `coeffs n` really are the coordinates of `(1 + √2 + √3)^n` in the basis
`1, √2, √3, √6`. -/
theorem coeffs_real (n : ℕ) :
    (1 + √2 + √3 : ℝ) ^ n = (coeffs n).1 + (coeffs n).2.1 * √2 + (coeffs n).2.2.1 * √3
      + (coeffs n).2.2.2 * √6 := by
  have h6 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  induction n with
  | zero => simp [coeffs]
  | succ n ih =>
    rw [pow_succ, ih, h6]
    simp only [coeffs, alphaStep, q4mul]
    push_cast
    linear_combination (((coeffs n).2.1 : ℝ) + (coeffs n).2.2.2 * √3) * h2
      + (((coeffs n).2.2.1 : ℝ) + (coeffs n).2.2.2 * √2) * h3

/-- If `√k` is irrational, then `u + v√k = 0` with integers `u, v` forces `u = v = 0`. -/
theorem eq_zero_of_add_mul_sqrt_eq_zero {k : ℕ} (hk : Irrational √(k : ℝ)) {u v : ℤ}
    (h : (u : ℝ) + v * √(k : ℝ) = 0) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    simpa using h
  · exfalso
    apply hk.ne_rat (-u / v)
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    push_cast
    field_simp
    linarith

/-- If `√k` is irrational, then `x^2 = k * y^2` in the integers forces `y = 0`. -/
theorem eq_zero_of_sq_eq_mul_sq {k : ℕ} (hk : Irrational √(k : ℝ)) {x y : ℤ}
    (h : x ^ 2 = k * y ^ 2) : y = 0 := by
  have hk0 : √(k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
  have hR : ((x : ℝ) + y * √(k : ℝ)) * ((x : ℝ) + (-y : ℤ) * √(k : ℝ)) = 0 := by
    have hc : (x : ℝ) ^ 2 = k * (y : ℝ) ^ 2 := by exact_mod_cast h
    push_cast
    linear_combination hc - (y : ℝ) ^ 2 * hk0
  rcases mul_eq_zero.mp hR with h1 | h1
  · exact (eq_zero_of_add_mul_sqrt_eq_zero hk h1).2
  · exact neg_eq_zero.mp (eq_zero_of_add_mul_sqrt_eq_zero hk h1).2

/-- `1, √2, √3, √6` are linearly independent over `ℤ`: an integer relation
`a + b√2 + c√3 + d√6 = 0` is trivial. -/
theorem linearIndependent_sqrt {a b c d : ℤ}
    (h : (a : ℝ) + b * √2 + c * √3 + d * √6 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h6 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have irr2 : Irrational √((2 : ℕ) : ℝ) := by simpa using irrational_sqrt_two
  have irr3 : Irrational √((3 : ℕ) : ℝ) := Nat.prime_three.irrational_sqrt
  have irr6 : Irrational √((6 : ℕ) : ℝ) := irrational_sqrt_natCast_iff.mpr (by
    rintro ⟨r, hr⟩
    have hr6 : r ≤ 6 := by nlinarith
    interval_cases r <;> omega)
  -- Square `a + b√2 = -(c + d√2)√3` and separate the `√2` part.
  have hsq : ((a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 - 6 * d ^ 2 : ℤ) : ℝ)
      + ((2 * a * b - 6 * c * d : ℤ) : ℝ) * √((2 : ℕ) : ℝ) = 0 := by
    rw [h6] at h
    push_cast
    linear_combination ((a : ℝ) + b * √2 - (c + d * √2) * √3) * h
      + ((c : ℝ) + d * √2) ^ 2 * h3 - ((b : ℝ) ^ 2 - 3 * d ^ 2) * h2
  obtain ⟨E1, E2⟩ := eq_zero_of_add_mul_sqrt_eq_zero irr2 hsq
  -- Taking norms from `ℤ[√2]`: `(a² - 2b²)² = (3c² - 6d²)²`.
  have hnorm : (a ^ 2 - 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2)
      * (a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2) = 0 := by
    linear_combination (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 6 * d ^ 2) * E1
      - 2 * (2 * a * b + 6 * c * d) * E2
  rcases mul_eq_zero.mp hnorm with hA | hB
  · -- `a² = 3c²` and `b² = 3d²`.
    have hc : c = 0 := eq_zero_of_sq_eq_mul_sq irr3 (x := a) (by push_cast; linarith)
    have hd : d = 0 := eq_zero_of_sq_eq_mul_sq irr3 (x := b) (by push_cast; linarith)
    subst hc hd
    have ha : a = 0 := by nlinarith
    have hb : b = 0 := by nlinarith
    exact ⟨ha, hb, rfl, rfl⟩
  · -- `a² = 6d²` and `(2b)² = 6c²`.
    have hd : d = 0 := eq_zero_of_sq_eq_mul_sq irr6 (x := a) (by push_cast; linarith)
    have hc : c = 0 := eq_zero_of_sq_eq_mul_sq irr6 (x := 2 * b) (by push_cast; linarith)
    subst hc hd
    have ha : a = 0 := by nlinarith
    have hb : b = 0 := by nlinarith
    exact ⟨ha, hb, rfl, rfl⟩

/-- The representation `(1 + √2 + √3)^n = a + b√2 + c√3 + d√6` with integer
coefficients is unique, so `a188570 n` is *the* coefficient of `1`, as in the
OEIS definition. -/
theorem a188570_eq_of_expansion {n : ℕ} {a b c d : ℤ}
    (h : (1 + √2 + √3 : ℝ) ^ n = a + b * √2 + c * √3 + d * √6) : a = a188570 n := by
  rw [coeffs_real] at h
  have hrel : ((a - a188570 n : ℤ) : ℝ) + ((b - (coeffs n).2.1 : ℤ) : ℝ) * √2
      + ((c - (coeffs n).2.2.1 : ℤ) : ℝ) * √3 + ((d - (coeffs n).2.2.2 : ℤ) : ℝ) * √6 = 0 := by
    simp only [a188570]
    push_cast
    linear_combination -h
  exact sub_eq_zero.mp (linearIndependent_sqrt hrel).1

-- Satisfiability of the expansion hypothesis: `(1 + √2 + √3)^2 = 6 + 2√2 + 2√3 + 2√6`.
example : (1 + √2 + √3 : ℝ) ^ 2 = (6 : ℤ) + (2 : ℤ) * √2 + (2 : ℤ) * √3 + (2 : ℤ) * √6 := by
  rw [coeffs_real]
  rfl

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A188570, Clark Kimberling, Oct 23 2024).**

Verbatim: "Conjecture: every prime divides a(n) for infinitely many n, and if
K(p) = (k(1), k(2),...) is the maximal subsequence of indices n such that p
divides a(n), then the difference sequence of K(p) is eventually periodic".

`Nat.nth (fun n => (p : ℤ) ∣ a188570 n) i` is `k(i+1)`, the `(i+1)`-st index
(in increasing order) with `p ∣ a(n)`; the differences are taken in `ℤ`.
The trailing claims about "the first 6 primes" are data, not part of the
general conjecture, and are not formalized. -/
def KimberlingConjecture : Prop :=
  ∀ p : ℕ, p.Prime →
    {n : ℕ | (p : ℤ) ∣ a188570 n}.Infinite ∧
    ∃ N T : ℕ, 0 < T ∧ ∀ i : ℕ, N ≤ i →
      ((Nat.nth (fun n => (p : ℤ) ∣ a188570 n) (i + T + 1) : ℤ)
          - Nat.nth (fun n => (p : ℤ) ∣ a188570 n) (i + T)) =
        (Nat.nth (fun n => (p : ℤ) ∣ a188570 n) (i + 1) : ℤ)
          - Nat.nth (fun n => (p : ℤ) ∣ a188570 n) i

/-! ## The refutation: the prime 23 -/

/-- Reduction of the four coordinates modulo `23` (representatives in `[0, 23)`). -/
def red23 (x : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (x.1 % 23, x.2.1 % 23, x.2.2.1 % 23, x.2.2.2 % 23)

/-- Multiplication by `1 + √2 + √3` followed by reduction modulo `23`. -/
def alphaStep23 (x : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := red23 (alphaStep x)

set_option maxRecDepth 20000 in
/-- `(1 + √2 + √3)^22 ≡ 1 (mod 23)` in `ℤ[√2, √3]`. -/
theorem alphaStep23_iterate_22 : alphaStep23^[22] (1, 0, 0, 0) = (1, 0, 0, 0) := by
  decide

/-- None of `a(0), …, a(21)` is divisible by `23`. -/
theorem alphaStep23_iterate_fst_ne_zero :
    ∀ m < 22, (alphaStep23^[m] (1, 0, 0, 0)).1 ≠ 0 := by
  decide

/-- Reducing before or after a multiplication by `1 + √2 + √3` agrees modulo `23`. -/
theorem alphaStep23_red23 (x : ℤ × ℤ × ℤ × ℤ) : alphaStep23 (red23 x) = red23 (alphaStep x) := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  have h1 : x1 % 23 ≡ x1 [ZMOD 23] := Int.mod_modEq x1 23
  have h2 : x2 % 23 ≡ x2 [ZMOD 23] := Int.mod_modEq x2 23
  have h3 : x3 % 23 ≡ x3 [ZMOD 23] := Int.mod_modEq x3 23
  have h4 : x4 % 23 ≡ x4 [ZMOD 23] := Int.mod_modEq x4 23
  simp only [alphaStep23, red23, alphaStep, q4mul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Int.ModEq 23 _ _
    gcongr
  · change Int.ModEq 23 _ _
    gcongr
  · change Int.ModEq 23 _ _
    gcongr
  · change Int.ModEq 23 _ _
    gcongr

/-- The coordinates of `(1 + √2 + √3)^n` modulo `23` are the `n`-th iterate of
`alphaStep23`. -/
theorem red23_coeffs (n : ℕ) : red23 (coeffs n) = alphaStep23^[n] (1, 0, 0, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, alphaStep23_red23]
    rfl

/-- `a(n) mod 23` depends only on `n mod 22`. -/
theorem a188570_emod_23 (n : ℕ) :
    a188570 n % 23 = (alphaStep23^[n % 22] (1, 0, 0, 0)).1 := by
  rw [Function.IsPeriodicPt.iterate_mod_apply (f := alphaStep23) (n := 22)
    alphaStep23_iterate_22]
  exact congrArg Prod.fst (red23_coeffs n)

/-- `23` divides no term of A188570. -/
theorem not_twentythree_dvd_a188570 (n : ℕ) : ¬ (23 : ℤ) ∣ a188570 n := by
  rw [Int.dvd_iff_emod_eq_zero, a188570_emod_23]
  exact alphaStep23_iterate_fst_ne_zero _ (Nat.mod_lt _ (by norm_num))

/-- Faithful real-expansion form: whenever `(1 + √2 + √3)^n = a + b√2 + c√3 + d√6`
with integers `a, b, c, d`, the prime `23` does not divide the coefficient `a`. -/
theorem not_twentythree_dvd_of_expansion {n : ℕ} {a b c d : ℤ}
    (h : (1 + √2 + √3 : ℝ) ^ n = a + b * √2 + c * √3 + d * √6) : ¬ (23 : ℤ) ∣ a := by
  rw [a188570_eq_of_expansion h]
  exact not_twentythree_dvd_a188570 n

/-- The first clause of Kimberling's conjecture fails: the prime `23` divides
`a(n)` for no `n` at all, so `K(23)` is empty. -/
theorem forall_prime_infinite_false :
    ¬ ∀ p : ℕ, p.Prime → {n : ℕ | (p : ℤ) ∣ a188570 n}.Infinite := by
  intro hall
  have hempty : {n : ℕ | ((23 : ℕ) : ℤ) ∣ a188570 n} = ∅ := by
    ext n
    simpa using not_twentythree_dvd_a188570 n
  have hinf := hall 23 (by norm_num)
  rw [hempty] at hinf
  exact hinf Set.finite_empty

/-- **Refutation of Kimberling's A188570 conjecture.** Counterexample: the prime
`p = 23` divides no term `a(n)` (the residues `a(n) mod 23` are periodic with
period `22` and never `0`); the primes `71` and `311` behave the same way.
The author presumably intended the statement only for primes `p` for which some
term is divisible by `p`, in which case `K(p)` is infinite and its differences
are periodic because `a(n) mod p` is purely periodic. -/
theorem kimberlingConjecture_false : ¬ KimberlingConjecture := fun h =>
  forall_prime_infinite_false fun p hp => (h p hp).1

end Candidates.A188570Refutation
