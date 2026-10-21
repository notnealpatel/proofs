/-
# A192023 — Kimberling: count of 2x2 matrices with entries in 1..n and determinant 2n

## OEIS source (retrieved with `oeis show A192023`, 2026-10-21)

```
NAME:     The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1)
          nodes. The Wiener index of a connected graph is the sum of the
          distances between all unordered pairs of vertices in the graph.
TERMS:    1,10,31,68,125,206,315,456,633,850,1111,1420,1781,2198,2675,...
FORMULA:  a(n) = n*(2*n^2 + 6*n - 5)/3.
COMMENT (the conjecture):
  Conjecture: for n>2, A192023(n-2) is the number of 2 X 2 matrices with all
  terms in {1,2,...,n} and determinant 2n. - _Clark Kimberling_, Mar 31 2012
```

No later comment in the entry retracts or amends the conjecture.

## Status

This module **refutes** the conjecture.  At `n = 3` exactly two matrices with
entries in `{1,2,3}` have determinant `6`, namely `[[3,3],[1,3]]` and
`[[3,1],[3,3]]`, while `A192023(1) = 1`.  A Python sweep (2026-10-21) gives the
counts `2, 9, 16, 33, 42, 69, 92, 123, 130, 228` for `n = 3..12` against
`A192023(n-2) = 1, 10, 31, 68, 125, 206, 315, 456, 633, 850`; they disagree at
every tested `n`.  The variants with entries in `{0,…,n}` or with determinant
`n`, `-2n`, `2`, `1`, `0`, `n^2` do not match either, so no intended corrected
form is evident.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A192023Refutation

/-- `A192023(n) = n (2n^2 + 6n - 5) / 3`, the OEIS FORMULA line (the Wiener index
of the comb graph with `2n` nodes).  Computed in `ℤ`, so `6n - 5` is a genuine
difference; the numerator is divisible by `3` (checked on the listed terms
below), so the integer division is exact there. -/
def a (n : ℕ) : ℤ := (n * (2 * n ^ 2 + 6 * n - 5) : ℤ) / 3

/-- Ground truth: the first ten listed terms of A192023. -/
example : (List.range 10).map (fun k => a (k + 1)) =
    [1, 10, 31, 68, 125, 206, 315, 456, 633, 850] := by decide

/-- The entries `(a, b, c, d)` of `2 × 2` matrices `[[a, b], [c, d]]` with all
terms in `{1, …, n}` and determinant `a d - b c = 2n`.  The entries are natural
numbers; the determinant is computed in `ℤ` (cast before subtracting). -/
def detTwoNMatrices (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t => (t.1 : ℤ) * t.2.2.2 - (t.2.1 : ℤ) * t.2.2.1 = 2 * (n : ℤ))

/-- The determinant used in `detTwoNMatrices` is Mathlib's `Matrix.det` of
`!![a, b; c, d]`. -/
example (p q r s : ℤ) : Matrix.det !![p, q; r, s] = p * s - q * r :=
  Matrix.det_fin_two_of p q r s

/-- Ground truth for the count: `n = 3, 4` give `2, 9`. -/
example : (detTwoNMatrices 3).card = 2 ∧ (detTwoNMatrices 4).card = 9 := by decide

/-- **Kimberling's conjecture (A192023, Clark Kimberling, Mar 31 2012).**

Verbatim: "Conjecture: for n>2, A192023(n-2) is the number of 2 X 2 matrices
with all terms in {1,2,...,n} and determinant 2n."

The guard `2 < n` keeps the natural subtraction `n - 2` off its junk value. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 < n → ((detTwoNMatrices n).card : ℤ) = a (n - 2)

/-- The `n = 3` instance: exactly the two matrices `[[3,3],[1,3]]` and
`[[3,1],[3,3]]` have entries in `{1,2,3}` and determinant `6`. -/
theorem detTwoNMatrices_three : detTwoNMatrices 3 = {(3, 3, 1, 3), (3, 1, 3, 3)} := by
  decide

/-- **Kimberling's A192023 conjecture is false.**  Counterexample `n = 3`: there
are `2` matrices with entries in `{1,2,3}` and determinant `6`
(`[[3,3],[1,3]]` and `[[3,1],[3,3]]`), but `A192023(1) = 1`.  The counts and the
sequence disagree at every `n` from `3` to `12`, and no simple variant of the
statement (entries from `0`, determinant `n` or `-2n`) matches, so no intended
hypothesis is evident. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h3 := h 3 (by norm_num)
  have hcard : (detTwoNMatrices 3).card = 2 := by
    rw [detTwoNMatrices_three]
    decide
  have ha : a (3 - 2) = 1 := by decide
  rw [hcard, ha] at h3
  norm_num at h3

end Candidates.A192023Refutation
