/-
# A175254 — Mathar's conjecture `a(n) = Sum_{k=0..n} A006218(n-k)` is false

## OEIS source (re-pulled with `oeis show A175254` and checked against the
## live entry https://oeis.org/A175254, retrieved 2026-10-21)

```
NAME:     a(n) = Sum_{k<=n} A000203(k)*(n-k+1), where A000203(m) is the sum of
          divisors of m.
OFFSET:   1
TERMS:    1,5,13,28,49,82,123,179,248,335,434,561,702,867,1056,1276,...
FORMULA (the conjecture):
  Conjecture: a(n) = Sum_{k=0..n} A006218(n-k). - _R. J. Mathar_, Oct 17 2012
```

`A006218(m) = Sum_{j=1..m} d(j)` (offset 0, terms `0,1,3,5,8,10,14,...`),
where `d = A000005` is the number of divisors.  No later comment or formula in
the entry retracts or corrects the conjecture.

## Status

This module **refutes** the conjecture.  At `n = 2`:
`a(2) = sigma(1)*2 + sigma(2)*1 = 2 + 3 = 5`, while
`A006218(2) + A006218(1) + A006218(0) = 3 + 1 + 0 = 4`.

The intended identity is evidently the one with `A024916` (partial sums of
`sigma`) in place of `A006218` (partial sums of `d`): the entry's own comment
"Partial sums of A024916" (Omar E. Pol, Jul 03 2014) says exactly that, and it
is proved below as `a_eq_sum_A024916`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A175254Refutation

open Finset ArithmeticFunction

/-- `A175254(n) = ∑_{k=1}^{n} σ(k)·(n-k+1)` (offset 1).  The natural-number
subtraction `n - k` is never truncated: `k ∈ [1, n]` gives `k ≤ n`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Icc 1 n, sigma 1 k * (n - k + 1)

/-- `A006218(m) = ∑_{j=1}^{m} d(j)`, the divisor summatory function
(offset 0, `A006218(0) = 0`). -/
def A006218 (m : ℕ) : ℕ := ∑ j ∈ Icc 1 m, sigma 0 j

/-- `A024916(m) = ∑_{j=1}^{m} σ(j)`, the partial sums of the sum-of-divisors
function (offset 0 here, `A024916(0) = 0`). -/
def A024916 (m : ℕ) : ℕ := ∑ j ∈ Icc 1 m, sigma 1 j

/-! ## Ground truth against the OEIS data lines -/

example : a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 13 ∧ a 4 = 28 ∧ a 5 = 49 ∧ a 6 = 82 := by
  simp only [a, sigma_one_apply]
  decide

example : A006218 0 = 0 ∧ A006218 1 = 1 ∧ A006218 2 = 3 ∧ A006218 3 = 5 ∧
    A006218 4 = 8 ∧ A006218 5 = 10 := by
  simp only [A006218, sigma_zero_apply]
  decide

example : A024916 1 = 1 ∧ A024916 2 = 4 ∧ A024916 3 = 8 ∧ A024916 4 = 15 ∧
    A024916 5 = 21 := by
  simp only [A024916, sigma_one_apply]
  decide

/-! ## The conjecture and its refutation -/

/-- **Mathar's conjecture (A175254, R. J. Mathar, Oct 17 2012).**
Verbatim: "Conjecture: a(n) = Sum_{k=0..n} A006218(n-k)."
Stated for every `n ≥ 1` (the entry's offset); `n - k` with `k ≤ n` is never
truncated. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ range (n + 1), A006218 (n - k)

/-- **Mathar's conjecture for A175254 is false.**  Counterexample `n = 2`:
`a(2) = 5` but `A006218(2) + A006218(1) + A006218(0) = 3 + 1 + 0 = 4`.
The intended statement uses `A024916` (partial sums of `σ`) instead of
`A006218` (partial sums of `d`); see `a_eq_sum_A024916`. -/
theorem mathar_false : ¬ Conjecture := by
  intro h
  have h2 := h 2 (by norm_num)
  have ha : a 2 = 5 := by
    simp only [a, sigma_one_apply]
    decide
  have hr : ∑ k ∈ range (2 + 1), A006218 (2 - k) = 4 := by
    simp only [A006218, sigma_zero_apply]
    decide
  omega

/-- Abel-summation step: `∑_{k=1}^{n} f(k)(n-k+1) = ∑_{m=1}^{n} ∑_{j=1}^{m} f(j)`. -/
theorem sum_mul_sub_add_one_eq (f : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k * (n - k + 1) = ∑ m ∈ Icc 1 n, ∑ j ∈ Icc 1 m, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ∑ k ∈ Icc 1 n, f k * (n + 1 - k + 1) =
        ∑ k ∈ Icc 1 n, f k * (n - k + 1) + ∑ k ∈ Icc 1 n, f k := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := (mem_Icc.mp hk).2
      rw [show n + 1 - k + 1 = (n - k + 1) + 1 by omega, mul_add, mul_one]
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), hstep, ih,
      sum_Icc_succ_top (by omega)]
    simp only [Nat.sub_self, zero_add, mul_one]
    ring

/-- **Corrected form (proved).**  `A175254(n) = ∑_{k=0}^{n} A024916(n-k)`,
i.e. A175254 is the partial-sum sequence of `A024916` (the entry's comment
"Partial sums of A024916", Omar E. Pol, Jul 03 2014).  This is Mathar's
identity with `A006218` replaced by `A024916`. -/
theorem a_eq_sum_A024916 (n : ℕ) :
    a n = ∑ k ∈ range (n + 1), A024916 (n - k) := by
  have hrefl : ∑ k ∈ range (n + 1), A024916 (n - k) =
      ∑ k ∈ range (n + 1), A024916 k := by
    simpa only [Nat.add_sub_cancel] using sum_range_reflect A024916 (n + 1)
  rw [hrefl, sum_range_succ', a, sum_mul_sub_add_one_eq]
  simp only [A024916, show Icc 1 0 = (∅ : Finset ℕ) from rfl, sum_empty, add_zero]
  rw [range_eq_Ico, sum_Ico_add' (fun m => ∑ j ∈ Icc 1 m, sigma 1 j) 0 n 1, zero_add,
    Ico_add_one_right_eq_Icc]

end Candidates.A175254Refutation
