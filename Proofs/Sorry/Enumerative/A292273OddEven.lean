/-
# A292273 — Granvik: `a(n) = Re(mu(n) * i^n)`

## OEIS source (retrieved with `oeis show A292273`, 2026-10-21)

```
NAME:     For odd n: a(n) = 0, and for even n: a(n) = -mu(n), where mu is
          Moebius function (A008683).
TERMS:    0,1,0,0,0,-1,0,0,0,-1,0,0,0,-1,0,0,0,0,0,0,0,-1,0,0,0,-1,0,0,0,1,...
FORMULA:  a(n) = (A000035(n)-1) * A008683(n).
FORMULA (the conjecture, verbatim):
  Conjecture: a(n) = Re(A008683(n)*(i^n)). - _Mats Granvik_, Jul 06 2024
```

## Status

Triage status: open (no proof recorded in the entry). The argument is
elementary and is formalized below: for odd `n`, `i^n = ±i` is purely
imaginary; for `n ≡ 2 (mod 4)`, `i^n = -1`; for `n ≡ 0 (mod 4)`, `4 ∣ n`, so
`n` is not squarefree and `mu(n) = 0`.

Computational re-validation (Python, 2026-10-21): the identity holds for
every `1 ≤ n ≤ 200000`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A292273OddEven

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- OEIS A292273: `a(n) = 0` for odd `n` and `a(n) = -mu(n)` for even `n`,
where `mu` is the Möbius function (A008683, Mathlib's `ArithmeticFunction.moebius`). -/
def a (n : ℕ) : ℤ := if Even n then -(μ n) else 0

/-! ## Ground truth against the DATA line `0, 1, 0, 0, 0, -1, …, 1` (offset 1) -/

example : a 1 = 0 := by simp [a]

example : a 2 = 1 := by simp [a, moebius_apply_prime Nat.prime_two]

example : a 3 = 0 := by simp [a, Nat.even_iff]

example : a 4 = 0 := by
  have hsq : ¬ Squarefree 4 := fun h =>
    absurd (Nat.isUnit_iff.mp (h 2 (by norm_num))) (by norm_num)
  simp [a, moebius_eq_zero_of_not_squarefree hsq, Nat.even_iff]

example : a 6 = -1 := by
  have hsq : Squarefree 6 := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    simp [Nat.primeFactorsList_ofNat]
  rw [a, if_pos (by decide), moebius_apply_of_squarefree hsq, cardFactors_apply]
  simp [Nat.primeFactorsList_ofNat]

example : a 30 = 1 := by
  have hsq : Squarefree 30 := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    simp [Nat.primeFactorsList_ofNat]
  rw [a, if_pos (by decide), moebius_apply_of_squarefree hsq, cardFactors_apply]
  simp [Nat.primeFactorsList_ofNat]

/-! ## Proof -/

/-- If `4 ∣ n` then `n` is not squarefree, so `mu(n) = 0`. -/
theorem moebius_eq_zero_of_four_dvd {n : ℕ} (h : 4 ∣ n) : μ n = 0 := by
  apply moebius_eq_zero_of_not_squarefree
  intro hsq
  have h2 : IsUnit (2 : ℕ) := hsq 2 (by simpa using h)
  exact absurd (Nat.isUnit_iff.mp h2) (by norm_num)

/-- Powers of `i` are periodic with period `4`: `i^n = i^(n mod 4)`. -/
theorem I_pow_eq_I_pow_mod_four (n : ℕ) : Complex.I ^ n = Complex.I ^ (n % 4) := by
  conv_lhs =>
    rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

/-- The identity `a(n) = Re(mu(n) * i^n)` holds for every natural `n`
(including the boundary `n = 0`, where both sides vanish since `mu(0) = 0`). -/
theorem a_eq_re_moebius_mul_I_pow_all (n : ℕ) :
    ((a n : ℤ) : ℝ) = (((μ n : ℤ) : ℂ) * Complex.I ^ n).re := by
  rw [I_pow_eq_I_pow_mod_four]
  have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  have hev : Even n ↔ n % 4 = 0 ∨ n % 4 = 2 := by
    rw [Nat.even_iff]
    omega
  interval_cases hr : n % 4
  · have hmu : μ n = 0 := moebius_eq_zero_of_four_dvd (Nat.dvd_of_mod_eq_zero hr)
    simp [a, hmu]
  · have hodd : ¬ Even n := by
      rw [hev]
      omega
    simp [a, hodd]
  · have heven : Even n := by
      rw [hev]
      omega
    simp [a, heven]
  · have hodd : ¬ Even n := by
      rw [hev]
      omega
    simp [a, hodd, pow_succ]

/-- **Granvik's conjecture (A292273, Mats Granvik, Jul 06 2024).**

Verbatim: "Conjecture: a(n) = Re(A008683(n)*(i^n))."  For every `n ≥ 1`, the
A292273 term `a(n)` (`0` for odd `n`, `-mu(n)` for even `n`) equals the real
part of `mu(n) * i^n`.  The `1 ≤ n` hypothesis mirrors the entry's offset; the
identity also holds at `n = 0` (`a_eq_re_moebius_mul_I_pow_all`). -/
theorem a_eq_re_moebius_mul_I_pow (n : ℕ) (_hn : 0 < n) :
    ((a n : ℤ) : ℝ) = (((μ n : ℤ) : ℂ) * Complex.I ^ n).re :=
  a_eq_re_moebius_mul_I_pow_all n

end Candidates.A292273OddEven
