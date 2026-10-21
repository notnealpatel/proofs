/-
# A129194 — Hurt: a(n) is the denominator of 4/n - 2/n^2

## OEIS source (retrieved with `oeis show A129194`, 2026-10-21)

```
NAME:     a(n) = (n/2)^2*(3 - (-1)^n).
TERMS:    0,1,2,9,8,25,18,49,32,81,50,121,72,169,98,225,128,289,162,361,200,
          441,242,529,288,625,338,729,392,841,450,961,512,1089,578,1225,648
COMMENT (the conjecture):
  Conjecture: denominator of 4/n - 2/n^2. - _Wesley Ivan Hurt_, Jul 11 2016
COMMENT (context):
  The sequence alternates between twice a square and an odd square,
  A001105(n) and A016754(n).
FORMULA:  a(n) = A000290(n) / A040001(n). - _Andrew Howroyd_, Jul 25 2018
```

The entry has offset 0 (`a(0) = 0`); the conjecture is meaningful only for
`n ≥ 1`, since `4/0 - 2/0^2` is undefined (Lean's junk value is `0`, whose
denominator is `1 ≠ a(0) = 0`).

## Status

Triage: open (no proof recorded in the entry).  The argument is elementary:
`4/n - 2/n^2 = 2(2n-1)/n^2` and `gcd(2n-1, n) = 1`, so the reduced
denominator is `n^2` for odd `n` and `n^2/2` for even `n`.  This file
proves it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A129194Denominator

/-! ## Definition layer -/

/-- OEIS A129194, transcribed from the entry name:
`a(n) = (n/2)^2 * (3 - (-1)^n)`, evaluated in `ℚ`. -/
def a (n : ℕ) : ℚ := ((n : ℚ) / 2) ^ 2 * (3 - (-1) ^ n)

/-! Ground truth against the first listed terms `0,1,2,9,8,25,18,49,32,81`. -/
example : a 0 = 0 := by norm_num [a]
example : a 1 = 1 := by norm_num [a]
example : a 2 = 2 := by norm_num [a]
example : a 3 = 9 := by norm_num [a]
example : a 4 = 8 := by norm_num [a]
example : a 5 = 25 := by norm_num [a]
example : a 6 = 18 := by norm_num [a]
example : a 7 = 49 := by norm_num [a]
example : a 8 = 32 := by norm_num [a]
example : a 9 = 81 := by norm_num [a]

/-! Ground truth for the denominator side at small `n`. -/
example : ((4 / (1 : ℚ) - 2 / 1 ^ 2).den : ℚ) = 1 := by norm_num
example : ((4 / (4 : ℚ) - 2 / 4 ^ 2).den : ℚ) = 8 := by norm_num
example : ((4 / (5 : ℚ) - 2 / 5 ^ 2).den : ℚ) = 25 := by norm_num

/-! ## Helper lemmas -/

/-- For odd `n = 2m+1`, `4/n - 2/n^2` has reduced denominator `n^2`. -/
theorem den_odd (m : ℕ) :
    ((4 / ((2 * m + 1 : ℕ) : ℚ) - 2 / ((2 * m + 1 : ℕ) : ℚ) ^ 2).den : ℚ)
      = ((2 * m + 1 : ℕ) : ℚ) ^ 2 := by
  have hval : 4 / ((2 * m + 1 : ℕ) : ℚ) - 2 / ((2 * m + 1 : ℕ) : ℚ) ^ 2
      = ((8 * (m : ℤ) + 2 : ℤ) : ℚ) / (((2 * (m : ℤ) + 1) ^ 2 : ℤ) : ℚ) := by
    push_cast
    field_simp
    ring
  have hcop : IsCoprime (8 * (m : ℤ) + 2) ((2 * (m : ℤ) + 1) ^ 2) :=
    IsCoprime.pow_right ⟨(m : ℤ), 1 - 4 * (m : ℤ), by ring⟩
  have hden := Rat.den_div_eq_of_coprime (a := 8 * (m : ℤ) + 2)
    (b := (2 * (m : ℤ) + 1) ^ 2) (by positivity) (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  rw [hval]
  exact_mod_cast hden

/-- For even `n = 2m+2`, `4/n - 2/n^2` has reduced denominator `n^2/2`. -/
theorem den_even (m : ℕ) :
    ((4 / ((2 * m + 2 : ℕ) : ℚ) - 2 / ((2 * m + 2 : ℕ) : ℚ) ^ 2).den : ℚ)
      = 2 * ((m + 1 : ℕ) : ℚ) ^ 2 := by
  have hval : 4 / ((2 * m + 2 : ℕ) : ℚ) - 2 / ((2 * m + 2 : ℕ) : ℚ) ^ 2
      = ((4 * (m : ℤ) + 3 : ℤ) : ℚ) / ((2 * ((m : ℤ) + 1) ^ 2 : ℤ) : ℚ) := by
    push_cast
    field_simp
    ring
  have h2 : IsCoprime (4 * (m : ℤ) + 3) 2 := ⟨1, -(2 * (m : ℤ) + 1), by ring⟩
  have h3 : IsCoprime (4 * (m : ℤ) + 3) ((m : ℤ) + 1) := ⟨-1, 4, by ring⟩
  have hcop : IsCoprime (4 * (m : ℤ) + 3) (2 * ((m : ℤ) + 1) ^ 2) :=
    IsCoprime.mul_right h2 (IsCoprime.pow_right h3)
  have hden := Rat.den_div_eq_of_coprime (a := 4 * (m : ℤ) + 3)
    (b := 2 * ((m : ℤ) + 1) ^ 2) (by positivity) (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  rw [hval]
  exact_mod_cast hden

/-! ## The conjecture -/

/-- **Hurt's conjecture (A129194, Wesley Ivan Hurt, Jul 11 2016).**

Verbatim: "Conjecture: denominator of 4/n - 2/n^2."  That is, for every
`n ≥ 1`, the reduced denominator of the rational `4/n - 2/n^2` equals
`a(n) = (n/2)^2 * (3 - (-1)^n)`.  The guard `1 ≤ n` keeps the divisions off
Lean's junk value at `n = 0`. -/
theorem den_eq_a (n : ℕ) (hn : 1 ≤ n) :
    ((4 / (n : ℚ) - 2 / (n : ℚ) ^ 2).den : ℚ) = a n := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · -- even case: `n = 2k` with `k ≥ 1`, so `n = 2m + 2`
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hn2 : n = 2 * m + 2 := by omega
    subst hn2
    rw [den_even m]
    have hsign : ((-1 : ℚ)) ^ (2 * m + 2) = 1 := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]
      norm_num
    rw [a, hsign]
    push_cast
    ring
  · -- odd case: `n = 2k + 1`
    subst hk
    rw [den_odd k]
    have hsign : ((-1 : ℚ)) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [a, hsign]
    push_cast
    ring

end Candidates.A129194Denominator
