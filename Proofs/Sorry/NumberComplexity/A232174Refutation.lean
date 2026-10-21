/-
# A232174 — Sun: the list of `n` with `a(n) = 1` omits `n = 66`

## OEIS source (retrieved with `oeis show A232174` and https://oeis.org/A232174, 2026-10-21)

```
NAME:     Number of ways to write n = x + y (x, y > 0) with x + n*y and
          x^2 + n*y^2 both prime.
OFFSET:   1
TERMS:    0,1,2,2,1,2,3,1,2,2,3,2,5,1,4,3,2,2,1,1,2,5,4,1,7,2,4,4,6,2,5,1,4,3,
          5,2,8,2,6,3,3,3,5,2,5,4,7,5,7,3,5,3,3,1,11,4,7,6,5,2,4,3,8,5,6,1,14,
          1,6,7,6,6,8,3,6,7,7,5,9,3,3,5,7,7,15,5,6,5,2,5,15,6,12,8,7,3,15,8,10,5
COMMENT:  Conjecture: (i) a(n) > 0 for all n > 1. Also, a(n) = 1 only for
          n = 2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168.
COMMENT:  In a paper published in 2017, the author announced a USD $200 prize
          for the first solution to his conjecture that a(n) > 0 for all n > 1.
          - _Zhi-Wei Sun_, Dec 03 2017
MATH:     a[n_]:=Sum[If[PrimeQ[k+n(n-k)]&&PrimeQ[k^2+n(n-k)^2],1,0],{k,1,n-1}]
AUTHOR:   Zhi-Wei Sun, Nov 19 2013
```

No later comment in the entry retracts or amends the list; parts (ii) and
(iii) of the comment concern other representations and are not treated here.

## Status

This module **refutes** conjecture (i) as stated (the conjunction of the
positivity claim and the "a(n) = 1 only for" list) by refuting the list.
At `n = 66` the unique representation is `66 = 53 + 13`, with
`53 + 66*13 = 911` and `53^2 + 66*13^2 = 13963` both prime, so `a(66) = 1`
(as the entry's own DATA line records), yet `66` is not in the list.
A bounded search (Python, trial division, `n ≤ 400`) finds `a(n) = 1` exactly
for `n ∈ {2, 5, 8, 14, 19, 20, 24, 32, 54, 66, 68, 101, 168}`; the triage
reports the same set for `n ≤ 3000`.  The intended list evidently includes
`66`; that corrected claim, and the $200 positivity claim `a(n) > 0`, remain
open and are not addressed here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A232174Refutation

open Finset

/-! ## Definition layer -/

/-- OEIS A232174: `a(n)` is the number of `x` with `0 < x < n` such that, with
`y = n - x`, both `x + n*y` and `x^2 + n*y^2` are prime.  The `ℕ` subtraction
`n - x` is exact on the range `x < n`; see `mem_filter_a232174_iff` for the
two-variable form `x + y = n`, `x, y > 0`.  (OEIS offset 1; `a 0 = 0`.) -/
def a232174 (n : ℕ) : ℕ :=
  #{x ∈ Ioo 0 n | (x + n * (n - x)).Prime ∧ (x ^ 2 + n * (n - x) ^ 2).Prime}

/-- The counted set is exactly the set of first parts `x` of representations
`n = x + y` with `x, y > 0` and `x + n*y`, `x^2 + n*y^2` both prime, so
`a232174` counts the representations of the OEIS name. -/
theorem mem_filter_a232174_iff (n x : ℕ) :
    x ∈ ({x ∈ Ioo 0 n | (x + n * (n - x)).Prime ∧ (x ^ 2 + n * (n - x) ^ 2).Prime} :
      Finset ℕ) ↔
      ∃ y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x + n * y).Prime ∧ (x ^ 2 + n * y ^ 2).Prime := by
  simp only [mem_filter, mem_Ioo]
  constructor
  · rintro ⟨⟨hx0, hxn⟩, hp1, hp2⟩
    exact ⟨n - x, hx0, by omega, by omega, hp1, hp2⟩
  · rintro ⟨y, hx0, hy0, hxy, hp1, hp2⟩
    have hy : n - x = y := by omega
    rw [hy]
    exact ⟨⟨hx0, by omega⟩, hp1, hp2⟩

/-- Ground truth: `a(1), …, a(12)` match the OEIS data. -/
example : (List.range 12).map (fun i => a232174 (i + 1)) =
    [0, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2] := by
  decide +kernel

/-- Sun's conjecture (i) on A232174 (Zhi-Wei Sun, Nov 19 2013):
`a(n) > 0` for all `n > 1`, and `a(n) = 1` only for
`n = 2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168`.

"Only for" is rendered as the implication `a(n) = 1 → n ∈ list` over the OEIS
domain `n ≥ 1`; this is the weaker reading, so refuting it refutes every
stronger one (e.g. the biconditional). -/
def Conjecture : Prop :=
  (∀ n : ℕ, 1 < n → 0 < a232174 n) ∧
  ∀ n : ℕ, 1 ≤ n → a232174 n = 1 →
    n ∈ ({2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168} : Finset ℕ)

/-! ## The refutation -/

/-- For `n = 66` the only admissible `x` is `53`: `53 + 66*13 = 911` and
`53^2 + 66*13^2 = 13963` are prime, while every other `0 < x < 66` makes one of
the two values composite. -/
theorem filter_a232174_sixtysix :
    ({x ∈ Ioo 0 66 | (x + 66 * (66 - x)).Prime ∧ (x ^ 2 + 66 * (66 - x) ^ 2).Prime} :
      Finset ℕ) = {53} := by
  ext x
  simp only [mem_filter, mem_Ioo, mem_singleton]
  constructor
  · rintro ⟨⟨hx0, hx66⟩, hprime⟩
    interval_cases x <;> first | rfl | norm_num at hprime
  · rintro rfl
    norm_num

/-- `a(66) = 1`, the unique representation being `66 = 53 + 13`
(this is the 66th term of the OEIS data). -/
theorem a232174_sixtysix : a232174 66 = 1 := by
  rw [a232174, filter_a232174_sixtysix, card_singleton]

/-- Sun's conjecture (i) on A232174 is false: `a(66) = 1` (unique
representation `66 = 53 + 13`, with `911` and `13963` prime), but `66` is
missing from the list `2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168`.  The
author evidently intended the list to include `66` (the entry's own DATA line
gives `a(66) = 1`); the positivity part `a(n) > 0` for `n > 1` is untouched. -/
theorem a232174_conjecture_false : ¬ Conjecture := by
  rintro ⟨-, honly⟩
  have hmem := honly 66 (by norm_num) a232174_sixtysix
  simp at hmem

end Candidates.A232174Refutation
