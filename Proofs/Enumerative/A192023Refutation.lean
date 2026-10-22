/-
Refutation of Kimberling's matrix count (OEIS A192023; Clark Kimberling,
Mar 31 2012).

At n=3 the ordered matrices with entries in {1,2,3} and determinant 2n=6
are exactly [[3,3],[1,3]] and [[3,1],[3,3]], hence there are two.
But the formula A192023(n-2)=n'*(2n'²+6n'-5)/3 at n'=1 is 1.
This refutes the universal claim for n>2; no alternative counting convention
or graph-theoretic Wiener-index bridge is asserted.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A192023Refutation

/-- `A192023(n) = n (2n^2 + 6n - 5) / 3`, the OEIS FORMULA line (the Wiener index
of the comb graph with `2n` nodes).  Computed in `ℤ`, so `6n - 5` is a genuine
difference; the numerator is divisible by `3` (checked on the listed terms
below), so the integer division is exact there. -/
def a (n : ℕ) : ℤ := (n * (2 * n ^ 2 + 6 * n - 5) : ℤ) / 3

/-- The first ten listed terms of A192023. -/
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

/-- Examples for the count: `n = 3, 4` give `2, 9`. -/
example : (detTwoNMatrices 3).card = 2 ∧ (detTwoNMatrices 4).card = 9 := by decide

/-- Kimberling's A192023 conjecture (Mar 31 2012): for `n>2`, the number
of ordered matrices with entries in `{1,…,n}` and determinant `2n` is
A192023(n-2). The guard excludes truncated subtraction. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 < n → ((detTwoNMatrices n).card : ℤ) = a (n - 2)

/-- The `n = 3` instance: exactly the two matrices `[[3,3],[1,3]]` and
`[[3,1],[3,3]]` have entries in `{1,2,3}` and determinant `6`. -/
theorem detTwoNMatrices_three : detTwoNMatrices 3 = {(3, 3, 1, 3), (3, 1, 3, 3)} := by
  decide

/-- Kimberling's count fails at `n=3`: there are two matrices with entries
in `{1,2,3}` and determinant `6`, but A192023(1)=1. -/
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
