/-
# A006231 — Mathar: a fourth-order holonomic recurrence

## OEIS source (retrieved with `oeis show A006231`, 2026-10-21)

```
NAME:     a(n) = Sum_{k=2..n} n(n-1)...(n-k+1)/k.
TERMS:    0,1,5,20,84,409,2365,16064,125664,1112073,10976173,119481284,
          1421542628,18348340113,255323504917,3809950976992, ...   (offset 1)
FORMULA:  a(n+1) - a(n) = A000522(n) - 1.
FORMULA (the conjecture):
  Conjecture: a(n) + (-n-2)*a(n-1) + (3*n-2)*a(n-2) + 3*(-n+2)*a(n-3)
  + (n-3)*a(n-4) = 0. - _R. J. Mathar_, Aug 06 2013
```

Triage restatement: "For n >= 5: a(n) - (n+2)a(n-1) + (3n-2)a(n-2)
- 3(n-2)a(n-3) + (n-3)a(n-4) = 0, where a(n) = Sum_{k=2..n} n!/((n-k)! k)
(Mathar 2013)."

## Status

Literature status per the triage: open (no proof in the entry or the
literature as far as the triage could tell).  Sage/Python evidence: holds
for `5 ≤ n ≤ 450`.

This module proves the conjecture.  The argument: with
`c n = Σ_{k=1}^{n} n^{(k)}/k = a n + n` and `e n = Σ_{k=0}^{n} n^{(k)}`
(A000522), Pascal's rule for falling factorials gives `c (n+1) = c n + e n`,
and `e (n+1) = (n+1) e n + 1`.  Hence
`a(n+2) - a(n+1) = (n+1)(a(n+1) - a(n)) + (n+1)`, and the second difference
of this three-term inhomogeneous recurrence is Mathar's homogeneous one.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A006231SumMathar

open Finset

/-- OEIS A006231: `a(n) = Σ_{k=2}^{n} n! / ((n-k)! k)`, i.e.
`Σ_{k=2}^{n} n(n-1)⋯(n-k+1)/k`.  Every quotient is exact
(`k ∣ k! ∣ n!/(n-k)!`), see `factorial_div_eq_descFactorial_div`.
The entry has offset `1`; the value at `0` is the empty sum `0`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 2 n, n.factorial / ((n - k).factorial * k)

/-! ## Ground truth against the DATA line (offset 1) -/

example : a 1 = 0 := by decide
example : a 2 = 1 := by decide
example : a 3 = 5 := by decide
example : a 4 = 20 := by decide
example : a 5 = 84 := by decide
example : a 6 = 409 := by decide
example : a 7 = 2365 := by decide

/-! ## Auxiliary sequences -/

/-- `c n = Σ_{k=1}^{n} n^{(k)} / k` (falling factorial over `k`), which equals
`a n + n`. -/
def c (n : ℕ) : ℕ :=
  ∑ k ∈ range n, n.descFactorial (k + 1) / (k + 1)

/-- `e n = Σ_{k=0}^{n} n^{(k)} = Σ_{j=0}^{n} n!/j!` (OEIS A000522). -/
def e (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), n.descFactorial k

/-- The entry's summand `n!/((n-k)! k)` is `n^{(k)}/k` for `k ≤ n`. -/
theorem factorial_div_eq_descFactorial_div {n k : ℕ} (hk : k ≤ n) :
    n.factorial / ((n - k).factorial * k) = n.descFactorial k / k := by
  rw [← Nat.factorial_mul_descFactorial hk]
  exact Nat.mul_div_mul_left _ _ (Nat.factorial_pos _)

/-- Pascal's rule for falling factorials:
`(n+1)^{(k+1)} = n^{(k+1)} + (k+1) n^{(k)}`. -/
theorem succ_descFactorial_succ_eq (n k : ℕ) :
    (n + 1).descFactorial (k + 1) = n.descFactorial (k + 1) + (k + 1) * n.descFactorial k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_succ_succ, Nat.factorial_succ]
  ring

/-- `a n + n = c n`. -/
theorem a_add_self_eq_c (n : ℕ) : a n + n = c n := by
  cases n with
  | zero => rfl
  | succ m =>
    have ha : a (m + 1) = ∑ k ∈ range m, (m + 1).descFactorial (k + 2) / (k + 2) := by
      unfold a
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      have hlen : m + 1 + 1 - 2 = m := by omega
      rw [hlen]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < m := Finset.mem_range.mp hk
      rw [factorial_div_eq_descFactorial_div (by omega), Nat.add_comm 2 k]
    rw [ha, c, Finset.sum_range_succ']
    simp

/-- `c (n+1) = c n + e n`. -/
theorem c_succ (n : ℕ) : c (n + 1) = c n + e n := by
  have hsum : c (n + 1) = ∑ k ∈ range (n + 1),
      (n.descFactorial (k + 1) / (k + 1) + n.descFactorial k) := by
    unfold c
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [succ_descFactorial_succ_eq, Nat.add_mul_div_left _ _ (Nat.succ_pos k)]
  have htop : n.descFactorial (n + 1) / (n + 1) = 0 := by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_succ_self n), Nat.zero_div]
  rw [hsum, Finset.sum_add_distrib, Finset.sum_range_succ, htop, Nat.add_zero, c, e]

/-- `e (n+1) = (n+1) e n + 1` (the A000522 recurrence). -/
theorem e_succ (n : ℕ) : e (n + 1) = (n + 1) * e n + 1 := by
  unfold e
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]

/-- The inhomogeneous three-term recurrence
`a(n+2) - a(n+1) = (n+1)(a(n+1) - a(n)) + (n+1)`, valid for all `n`. -/
theorem a_three_term (n : ℕ) :
    (a (n + 2) : ℤ) - a (n + 1) = ((n : ℤ) + 1) * ((a (n + 1) : ℤ) - a n) + ((n : ℤ) + 1) := by
  have h0 : ((a n : ℕ) : ℤ) + n = c n := by exact_mod_cast a_add_self_eq_c n
  have h1 : ((a (n + 1) : ℕ) : ℤ) + (n + 1) = c (n + 1) := by
    exact_mod_cast a_add_self_eq_c (n + 1)
  have h2 : ((a (n + 2) : ℕ) : ℤ) + (n + 2) = c (n + 2) := by
    exact_mod_cast a_add_self_eq_c (n + 2)
  have hc0 : (c (n + 1) : ℤ) = c n + e n := by exact_mod_cast c_succ n
  have hc1 : (c (n + 2) : ℤ) = c (n + 1) + e (n + 1) := by exact_mod_cast c_succ (n + 1)
  have he : (e (n + 1) : ℤ) = ((n : ℤ) + 1) * e n + 1 := by exact_mod_cast e_succ n
  linear_combination h2 - ((n : ℤ) + 2) * h1 + ((n : ℤ) + 1) * h0 + hc1 + he
    - ((n : ℤ) + 1) * hc0

/-- **Mathar's conjecture for A006231 (R. J. Mathar, Aug 06 2013).**

For `n ≥ 5`:
`a(n) - (n+2) a(n-1) + (3n-2) a(n-2) - 3(n-2) a(n-3) + (n-3) a(n-4) = 0`,
where `a(n) = Σ_{k=2}^{n} n!/((n-k)! k)`.  The coefficients are computed in
`ℤ` after casting `n`; the indices `n - 1, …, n - 4` are natural-number
subtractions kept off truncation by `5 ≤ n`. -/
theorem mathar_recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) - ((n : ℤ) + 2) * a (n - 1) + (3 * (n : ℤ) - 2) * a (n - 2)
      - 3 * ((n : ℤ) - 2) * a (n - 3) + ((n : ℤ) - 3) * a (n - 4) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have i1 : m + 4 - 1 = m + 3 := by omega
  have i2 : m + 4 - 2 = m + 2 := by omega
  have i3 : m + 4 - 3 = m + 1 := by omega
  have i4 : m + 4 - 4 = m := by omega
  rw [i1, i2, i3, i4]
  have L0 := a_three_term m
  have L1 := a_three_term (m + 1)
  have L2 := a_three_term (m + 2)
  push_cast at L0 L1 L2 ⊢
  linear_combination L2 - 2 * L1 + L0

/-- Satisfiability witness: the hypothesis `5 ≤ n` is met at `n = 5`, where the
recurrence reads `84 - 7·20 + 13·5 - 9·1 + 2·0 = 0`. -/
example : (a 5 : ℤ) - (5 + 2) * a 4 + (3 * 5 - 2) * a 3 - 3 * (5 - 2) * a 2
    + (5 - 3) * a 1 = 0 := by decide

end Candidates.A006231SumMathar
