/-
# A373561 — gcd-indicator sum of x^2 + y^2 - z^2

## OEIS source (retrieved with `oeis show A373561`, 2026-10-21)

```
NAME:     a(n) = (1/3)*n^5 + (1/2)*n^4 + (1/6)*n^3.
TERMS:    0,1,20,126,480,1375,3276,6860,13056,23085,38500,61226,93600,...
FORMULA:  a(n) = n^3*(n+1)*(2*n+1)/6.
FORMULA:  a(n) = n^2 * A000330(n).
FORMULA (the conjecture, unsigned in the entry; no author or date attached):
  Conjecture: a(n) = Sum_{k=1..n} Sum_{z=1..n} Sum_{y=1..n} Sum_{x=1..n}
  [GCD(f(x,y,z), n) = k] * f(x,y,z), where f(x,y,z) = x^2 + y^2 - z^2.
```

The second Mathematica program of the entry computes exactly this sum
with `p = 2`.

## Status

Triage: "open" (no proof in the entry or found in the literature), but
tractability "trivial": for `n ≥ 1`, `gcd(f, n)` is a positive divisor of
`n`, so it lies in `[1, n]` and the sum over `k` collapses to
`Σ_{x,y,z} f = n^2 · Σ_{x=1}^n x^2 = n^2 · n(n+1)(2n+1)/6`.
Numerically re-checked for `0 ≤ n ≤ 15` (python, 2026-10-21).

## Formalization

* `f x y z = x^2 + y^2 - z^2` evaluated in `ℤ` (it can be negative);
  `GCD(f, n)` is `Int.gcd (f x y z) n`, which is nonnegative and agrees
  with Mathematica's `GCD` (including `GCD[0, n] = n`).
* `a n = n^3 (n+1) (2n+1) / 6` in `ℕ`; the division is exact
  (`six_mul_a`), so it is not a truncation artefact.
* The conjecture is `conjecture` (for `1 ≤ n`, as stated); it is derived
  from `gcdSum_eq_a`, which also covers `n = 0` (both sides `0`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A373561Gcd

open Finset

/-- The cubic form `f(x, y, z) = x^2 + y^2 - z^2` of A373561, computed in `ℤ`
from natural-number arguments. -/
def f (x y z : ℕ) : ℤ := (x : ℤ) ^ 2 + (y : ℤ) ^ 2 - (z : ℤ) ^ 2

/-- A373561: `a(n) = n^3 (n+1) (2n+1) / 6` (exact division, see `six_mul_a`). -/
def a (n : ℕ) : ℕ := n ^ 3 * (n + 1) * (2 * n + 1) / 6

/-- The conjectured gcd-indicator sum of A373561:
`Σ_{k=1}^n Σ_{z=1}^n Σ_{y=1}^n Σ_{x=1}^n [gcd(f(x,y,z), n) = k] · f(x,y,z)`. -/
def gcdSum (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 n, ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n,
    if Int.gcd (f x y z) n = k then f x y z else 0

/-! ## Ground truth against the listed terms -/

example : a 0 = 0 := rfl
example : a 1 = 1 := rfl
example : a 2 = 20 := rfl
example : a 3 = 126 := rfl
example : a 4 = 480 := rfl
example : a 5 = 1375 := rfl
example : a 10 = 38500 := rfl
example : f 1 2 3 = -4 := rfl
example : gcdSum 1 = 1 := by decide
example : gcdSum 2 = 20 := by decide
example : gcdSum 3 = 126 := by decide

/-! ## Proof -/

/-- For `1 ≤ n`, `gcd(m, n)` lies in `[1, n]` for every integer `m`. -/
theorem gcd_mem_Icc (m : ℤ) {n : ℕ} (hn : 1 ≤ n) : Int.gcd m n ∈ Icc 1 n := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpos : 0 < Int.gcd m n := Int.gcd_pos_of_ne_zero_right m hn0
  have hdvd : Int.gcd m n ∣ n := by
    have h := Int.gcd_dvd_right m (n : ℤ)
    exact Int.natCast_dvd_natCast.mp (by simpa using h)
  exact mem_Icc.mpr ⟨hpos, Nat.le_of_dvd (by omega) hdvd⟩

/-- Collapsing the indicator sum: `gcdSum n = Σ_{x,y,z ∈ [1,n]} f(x,y,z)`
for `1 ≤ n`. -/
theorem gcdSum_eq_sum_f {n : ℕ} (hn : 1 ≤ n) :
    gcdSum n = ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n, f x y z := by
  unfold gcdSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]
  rw [if_pos (gcd_mem_Icc (f x y z) hn)]

/-- `6 · Σ_{x=1}^n x^2 = n (n+1) (2n+1)` in `ℤ`. -/
theorem six_mul_sum_sq (n : ℕ) :
    6 * ∑ x ∈ Icc 1 n, ((x : ℤ) ^ 2) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast
    ring

/-- `Σ_{x,y,z ∈ [1,n]} f(x,y,z) = n^2 · Σ_{x=1}^n x^2`. -/
theorem sum_f_eq (n : ℕ) :
    ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n, f x y z
      = (n : ℤ) ^ 2 * ∑ x ∈ Icc 1 n, ((x : ℤ) ^ 2) := by
  simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  ring

/-- The division in `a` is exact: `6 · a(n) = n^3 (n+1) (2n+1)`. -/
theorem six_mul_a (n : ℕ) : 6 * a n = n ^ 3 * (n + 1) * (2 * n + 1) := by
  have h := six_mul_sum_sq n
  have hdvd : (6 : ℤ) ∣ (n ^ 3 * (n + 1) * (2 * n + 1) : ℕ) := by
    push_cast
    exact ⟨(n : ℤ) ^ 2 * ∑ x ∈ Icc 1 n, ((x : ℤ) ^ 2), by linear_combination (-(n : ℤ) ^ 2) * h⟩
  unfold a
  exact Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp (by exact_mod_cast hdvd))

/-- The gcd-indicator sum equals `a(n)` for every `n` (including the empty
case `n = 0`). -/
theorem gcdSum_eq_a (n : ℕ) : gcdSum n = (a n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · rw [gcdSum_eq_sum_f hn, sum_f_eq]
    have h6 : (6 : ℤ) * (a n : ℤ) = n ^ 3 * (n + 1) * (2 * n + 1) := by
      exact_mod_cast six_mul_a n
    have hs := six_mul_sum_sq n
    refine mul_left_cancel₀ (show (6 : ℤ) ≠ 0 by norm_num) ?_
    linear_combination (n : ℤ) ^ 2 * hs - h6

/-- **A373561 conjecture** (OEIS formula line, unsigned): for `n ≥ 1`,
`n^3 (n+1) (2n+1) / 6 = Σ_{k=1}^n Σ_{z=1}^n Σ_{y=1}^n Σ_{x=1}^n
[gcd(x^2 + y^2 - z^2, n) = k] · (x^2 + y^2 - z^2)`. -/
theorem conjecture (n : ℕ) (_hn : 1 ≤ n) :
    ((n ^ 3 * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) = gcdSum n :=
  (gcdSum_eq_a n).symm

end Candidates.A373561Gcd
