/-
# A165978 — Lowell: no value occurs twice (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A165978`,
## cross-checked against https://oeis.org/A165978)

```
ID:       A165978
NAME:     Largest prime factor of number formed from a(n-1) with a 1 added
          at the end, a(1)=2.
AUTHOR:   J. Lowell, Oct 02 2009
TERMS:    2,7,71,79,113,29,97,971,83,277,163,233,37,53,59,197,73,43,431,479,
          1597,15971,383,1277,43,431,479,1597,15971,383,1277,43,...
COMMENT (the conjecture; the entry records no date on the comment line):
  Conjecture: The same number will never occur twice in this sequence. - Lowell
COMMENT (the retraction already in the entry):
  Disproved - cycle 43,431,479,1597,15971,383,1277 repeats starting at
  a(18). - Chandler
```

## Status

This module refutes Lowell's conjecture by a kernel-checked computation:
`a 18 = 43 = a 25`.  The entry itself already records the disproof
(Chandler), so the refutation is a formal confirmation of a known fact.

## Definitions

* "the number formed from `x` with a 1 added at the end" is `10 * x + 1`
  (checked against `Nat.ofDigits` below);
* "largest prime factor" of `n` is `n.primeFactors.sup id`; it is the
  genuine largest prime factor whenever `2 ≤ n`, which always holds here
  since `10 * x + 1 ≥ 11` for `x ≥ 1`.

The sequence keeps the OEIS offset 1: `a 1 = 2`; `a 0` is an unused
placeholder (`0`) that the conjecture never mentions.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A165978Refutation

/-- The largest prime factor of `n`, as the supremum of its prime factors
(`0` for `n ≤ 1`, which never arises in the sequence). -/
def largestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The number formed from `x` with a digit `1` appended at the end. -/
def appendOne (x : ℕ) : ℕ := 10 * x + 1

/-- OEIS A165978 with offset 1: `a 1 = 2` and `a n` is the largest prime
factor of `a (n-1)` with a `1` appended.  `a 0 = 0` is an unused
placeholder outside the OEIS index range. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => largestPrimeFactor (appendOne (a (n + 1)))

/-! ## Ground-truth checks on the definitions -/

example : appendOne 971 = Nat.ofDigits 10 (1 :: Nat.digits 10 971) := by
  norm_num [appendOne, Nat.ofDigits]

example : largestPrimeFactor 21 = 7 := by
  simp [largestPrimeFactor, Nat.primeFactors, Nat.primeFactorsList_ofNat]

example : largestPrimeFactor 1 = 0 := by simp [largestPrimeFactor]

/-- One step of the recursion, as an equation. -/
theorem a_succ_succ (n : ℕ) : a (n + 2) = largestPrimeFactor (appendOne (a (n + 1))) := rfl

/-- Prefix `a 1, ..., a 25` of A165978, matching the listed OEIS terms. -/
theorem a_prefix :
    a 1 = 2 ∧ a 2 = 7 ∧ a 3 = 71 ∧ a 4 = 79 ∧ a 5 = 113 ∧ a 6 = 29 ∧ a 7 = 97 ∧
    a 8 = 971 ∧ a 9 = 83 ∧ a 10 = 277 ∧ a 11 = 163 ∧ a 12 = 233 ∧ a 13 = 37 ∧
    a 14 = 53 ∧ a 15 = 59 ∧ a 16 = 197 ∧ a 17 = 73 ∧ a 18 = 43 ∧ a 19 = 431 ∧
    a 20 = 479 ∧ a 21 = 1597 ∧ a 22 = 15971 ∧ a 23 = 383 ∧ a 24 = 1277 ∧
    a 25 = 43 := by
  have h1 : a 1 = 2 := rfl
  have step : ∀ n x y : ℕ, a (n + 1) = x → largestPrimeFactor (appendOne x) = y →
      a (n + 2) = y := by
    intro n x y hx hy
    rw [a_succ_succ, hx, hy]
  have h2 := step 0 _ 7 h1 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h3 := step 1 _ 71 h2 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h4 := step 2 _ 79 h3 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h5 := step 3 _ 113 h4 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h6 := step 4 _ 29 h5 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h7 := step 5 _ 97 h6 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h8 := step 6 _ 971 h7 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h9 := step 7 _ 83 h8 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h10 := step 8 _ 277 h9 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h11 := step 9 _ 163 h10 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h12 := step 10 _ 233 h11 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h13 := step 11 _ 37 h12 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h14 := step 12 _ 53 h13 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h15 := step 13 _ 59 h14 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h16 := step 14 _ 197 h15 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h17 := step 15 _ 73 h16 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h18 := step 16 _ 43 h17 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h19 := step 17 _ 431 h18 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h20 := step 18 _ 479 h19 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h21 := step 19 _ 1597 h20 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h22 := step 20 _ 15971 h21 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h23 := step 21 _ 383 h22 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h24 := step 22 _ 1277 h23 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  have h25 := step 23 _ 43 h24 (by
    simp [largestPrimeFactor, appendOne, Nat.primeFactors, Nat.primeFactorsList_ofNat])
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25⟩

/-- **Lowell's conjecture (A165978, J. Lowell, entry of Oct 02 2009).**

Verbatim: "Conjecture: The same number will never occur twice in this
sequence."  Stated over the OEIS index range `n ≥ 1`: any two distinct
indices `1 ≤ m < n` carry distinct values. -/
def Conjecture : Prop := ∀ m n : ℕ, 1 ≤ m → m < n → a m ≠ a n

/-- **Lowell's conjecture is false.**  Counterexample: `a 18 = a 25 = 43`;
from `a 18` on the sequence runs through the 7-cycle
`43, 431, 479, 1597, 15971, 383, 1277` forever (as already recorded in the
entry by Chandler).  No corrected form is evident: the sequence is
eventually periodic, so any injectivity claim fails. -/
theorem lowell_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -, -, -, -, -, -, h25⟩ :=
    a_prefix
  exact hconj 18 25 (by norm_num) (by norm_num) (h18.trans h25.symm)

end Candidates.A165978Refutation
