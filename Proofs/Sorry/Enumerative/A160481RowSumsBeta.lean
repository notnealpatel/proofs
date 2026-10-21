/-
# A160481 — Herzog: closed form for the row sums of the Beta triangle

## OEIS source (retrieved with `oeis show A160481`, 2026-10-21)

```
NAME:     Row sums of the Beta triangle A160480.
TERMS:    -1,-10,-264,-13392,-1111680,-137030400,-23500108800,-5351202662400,
          -1562069156659200,-568747270103040000,...
KEYWORDS: easy,sign,uned
COMMENT:  It is conjectured that the row sums of the Beta triangle depend on
          three different sequences. ...
FORMULA:  Rowsums(n) = (-1)*A120778(n-2)*A000165(n-2)*A049606(n-1) for n >= 2.
FORMULA (the conjecture):
  Conjecture: a(n) = (2*n-3)! - 2^(2*n-3)*(n-1)!*(n-2)!, for n >= 2 (gives the
  first 13 terms). - _Christopher P. Herzog_, Nov 25 2014
```

The Beta triangle A160480 (Johannes W. Meijer) is defined by the recurrence
(FORMULA and Maple program of A160480):

```
BETA(n,n) = 0                                         for n = 1, 2, ...
BETA(n,1) = (2*n-3)^2*BETA(n-1,1) - (2*n-4)!           for n = 2, 3, ...
BETA(n,m) = (2*n-3)^2*BETA(n-1,m) - BETA(n-1,m-1)      for m = 2, 3, ..., n > m
```

and is read by rows `BETA(n,m)`, `n = 2, 3, ...`, `m = 1, ..., n-1`
(terms `-1, -11, 1, -299, 36, -1, -15371, 2063, -85, 1, ...`).

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Herzog's form was checked numerically here for `2 ≤ n ≤ 40`
(Python, exact integers) before formalization.  This file proves it: summing
the recurrence over a row gives `S(n) = (2n-2)(2n-4) S(n-1) - (2n-4)!`, which
Herzog's closed form satisfies.

Meijer's three-factor form via A120778 (numerators of partial sums of
Catalan numbers over powers of 4) is not formalized here; only Herzog's closed
form is the target.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A160481RowSumsBeta

open Finset

/-- The Beta triangle `BETA(n,m)` of OEIS A160480, mirroring Meijer's
recurrence: `BETA(n,n) = 0`, `BETA(n,1) = (2n-3)^2 BETA(n-1,1) - (2n-4)!` for
`n ≥ 2`, and `BETA(n,m) = (2n-3)^2 BETA(n-1,m) - BETA(n-1,m-1)` for
`2 ≤ m < n`.  Entries outside the triangle `1 ≤ m < n` are `0` (as in the
Mathematica program of the entry).  In the clauses below the first index is
`n + 1`, so `2(n+1) - 3 = 2n - 1` and `2(n+1) - 4 = 2n - 2`. -/
def beta : ℕ → ℕ → ℤ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, 1 =>
      if n = 0 then 0 else (2 * n - 1 : ℤ) ^ 2 * beta n 1 - ((2 * n - 2).factorial : ℤ)
  | n + 1, m + 2 =>
      if n + 1 ≤ m + 2 then 0 else (2 * n - 1 : ℤ) ^ 2 * beta n (m + 2) - beta n (m + 1)

/-- The `n`-th row sum `∑_{m=1}^{n-1} BETA(n,m)` of the Beta triangle (A160481). -/
def rowSum (n : ℕ) : ℤ := ∑ m ∈ Ico 1 n, beta n m

/-! ### Ground truth against A160480 and A160481 -/

example : [beta 2 1, beta 3 1, beta 3 2, beta 4 1, beta 4 2, beta 4 3,
    beta 5 1, beta 5 2, beta 5 3, beta 5 4] =
    [-1, -11, 1, -299, 36, -1, -15371, 2063, -85, 1] := by decide

example : [rowSum 2, rowSum 3, rowSum 4, rowSum 5, rowSum 6] =
    [-1, -10, -264, -13392, -1111680] := by decide

/-! ### Vanishing outside the triangle and the unfolded recurrences -/

/-- `BETA(n,0) = 0`: column `0` lies outside the triangle. -/
theorem beta_zero_right (n : ℕ) : beta n 0 = 0 := by
  cases n <;> rfl

/-- `BETA(n,m) = 0` for `n ≤ m`; in particular the diagonal `BETA(n,n)` vanishes. -/
theorem beta_eq_zero_of_le {n m : ℕ} (h : n ≤ m) : beta n m = 0 := by
  match n, m, h with
  | 0, _, _ => rfl
  | _ + 1, 0, h => omega
  | n + 1, 1, h =>
      have hn : n = 0 := by omega
      simp [beta, hn]
  | n + 1, m + 2, h => simp [beta, h]

/-- Column-one recurrence `BETA(n+2,1) = (2n+1)^2 BETA(n+1,1) - (2n)!`. -/
theorem beta_succ_succ_one (n : ℕ) :
    beta (n + 2) 1 = (2 * n + 1 : ℤ) ^ 2 * beta (n + 1) 1 - ((2 * n).factorial : ℤ) := by
  have h2 : 2 * (n + 1) - 2 = 2 * n := by omega
  simp only [beta, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, h2]
  push_cast
  ring

/-- Interior recurrence `BETA(n+2,m+2) = (2n+1)^2 BETA(n+1,m+2) - BETA(n+1,m+1)`
for `m < n`. -/
theorem beta_succ_succ_succ_succ {n m : ℕ} (h : m < n) :
    beta (n + 2) (m + 2) =
      (2 * n + 1 : ℤ) ^ 2 * beta (n + 1) (m + 2) - beta (n + 1) (m + 1) := by
  have hle : ¬ n + 2 ≤ m + 2 := by omega
  rw [beta, if_neg hle]
  push_cast
  ring

/-! ### The row-sum recurrence -/

/-- Summing over any range that covers the row gives the row sum. -/
theorem sum_range_beta_eq_rowSum {n N : ℕ} (h : n ≤ N) :
    ∑ m ∈ range N, beta n m = rowSum n := by
  induction N, h using Nat.le_induction with
  | base =>
      cases n with
      | zero => rfl
      | succ k =>
          rw [rowSum, sum_range_succ', sum_Ico_eq_sum_range, beta_zero_right, add_zero,
            Nat.add_sub_cancel]
          exact sum_congr rfl fun m _ => by rw [add_comm 1 m]
  | succ N hN ih =>
      rw [sum_range_succ, ih, beta_eq_zero_of_le hN, add_zero]

/-- Row-sum recurrence obtained by summing Meijer's recurrence over a row:
`S(k+2) = ((2k+1)^2 - 1) S(k+1) - (2k)!`, i.e. `S(n) = (2n-2)(2n-4) S(n-1) - (2n-4)!`
for `n = k + 2 ≥ 2`. -/
theorem rowSum_succ_succ (k : ℕ) :
    rowSum (k + 2) = ((2 * k + 1 : ℤ) ^ 2 - 1) * rowSum (k + 1) - ((2 * k).factorial : ℤ) := by
  have hrow : rowSum (k + 2) =
      ∑ m ∈ range k, beta (k + 2) (m + 2) + beta (k + 2) 1 := by
    rw [← sum_range_beta_eq_rowSum (le_refl (k + 2)), sum_range_succ', sum_range_succ',
      beta_zero_right, add_zero]
  have hprev2 : rowSum (k + 1) =
      ∑ m ∈ range k, beta (k + 1) (m + 2) + beta (k + 1) 1 := by
    rw [← sum_range_beta_eq_rowSum (Nat.le_succ (k + 1)), sum_range_succ', sum_range_succ',
      beta_zero_right, add_zero]
  have hprev1 : rowSum (k + 1) = ∑ m ∈ range k, beta (k + 1) (m + 1) := by
    rw [← sum_range_beta_eq_rowSum (le_refl (k + 1)), sum_range_succ', beta_zero_right,
      add_zero]
  have hinner : ∑ m ∈ range k, beta (k + 2) (m + 2) =
      (2 * k + 1 : ℤ) ^ 2 * ∑ m ∈ range k, beta (k + 1) (m + 2) -
        ∑ m ∈ range k, beta (k + 1) (m + 1) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun m hm => beta_succ_succ_succ_succ (mem_range.mp hm)
  rw [hrow, hinner, beta_succ_succ_one]
  linear_combination hprev1 - (2 * k + 1 : ℤ) ^ 2 * hprev2

/-! ### Herzog's closed form -/

/-- Herzog's closed form in shifted indices: `S(n+2) = (2n+1)! - 2^(2n+1) (n+1)! n!`. -/
theorem rowSum_add_two (n : ℕ) :
    rowSum (n + 2) =
      ((2 * n + 1).factorial : ℤ) - 2 ^ (2 * n + 1) * ((n + 1).factorial : ℤ) * (n.factorial : ℤ) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [rowSum_succ_succ, ih]
      have e1 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by ring
      have e2 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
      rw [e1, e2, Nat.factorial_succ (2 * n + 2), Nat.factorial_succ (2 * n + 1),
        Nat.factorial_succ (n + 1), Nat.factorial_succ n]
      push_cast
      ring

/-- **Herzog's conjecture (A160481, Christopher P. Herzog, Nov 25 2014).**

Verbatim: "Conjecture: a(n) = (2*n-3)! - 2^(2*n-3)*(n-1)!*(n-2)!, for n >= 2."

Here `a(n) = ∑_{m=1}^{n-1} BETA(n,m)` is the `n`-th row sum of Meijer's Beta
triangle A160480.  The guard `2 ≤ n` keeps every natural-number subtraction
`2n-3`, `n-1`, `n-2` off its truncated value. -/
theorem herzog_rowSum {n : ℕ} (hn : 2 ≤ n) :
    rowSum n = ((2 * n - 3).factorial : ℤ) -
      2 ^ (2 * n - 3) * ((n - 1).factorial : ℤ) * ((n - 2).factorial : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h1 : 2 * (k + 2) - 3 = 2 * k + 1 := by omega
  have h2 : k + 2 - 1 = k + 1 := by omega
  have h3 : k + 2 - 2 = k := by omega
  rw [h1, h2, h3]
  exact rowSum_add_two k

/-- Non-vacuity: the guard `2 ≤ n` is met, e.g. at `n = 5`, where both sides are `-13392`. -/
example : rowSum 5 = -13392 := by
  rw [herzog_rowSum (by norm_num : 2 ≤ 5)]
  decide

end Candidates.A160481RowSumsBeta
