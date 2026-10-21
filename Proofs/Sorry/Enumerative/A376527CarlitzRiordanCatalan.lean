/-
# A376527 — parity of the sum of squares of the Carlitz-Riordan q-Catalan coefficients

## OEIS source (`oeis show A376527`, retrieved 2026-10-21)

```
NAME:     a(n) = Sum_{k=0..n*(n-1)/2} A227543(n,k)^2 for n >= 0.
TERMS:    1,1,2,7,34,216,1610,13461,122254,1183568,12054498,127960158,...
COMMENT:  G.f. F(x,q) of triangle A227543 satisfies F(x,q) = 1 + x*F(x,q)*F(q*x,q).
COMMENT (the conjecture):
  Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0.
AUTHOR:   _Paul D. Hanna_, Oct 11 2024 (the conjecture line carries no separate
          attribution; it is part of Hanna's original entry).
```

## Status

Triage: open (no proof in the entry or the literature found by triage).  It follows
from the classical parity of the Catalan numbers: `c^2 ≡ c (mod 2)`, so
`a(n) ≡ R_n(1) = C_n (mod 2)`, and `C_n` is odd iff `n + 1` is a power of two.
This file proves it completely (`odd_a_iff`, `odd_a_iff_eq_two_pow_sub_one`).

## Computation

Parity checked for `n ≤ 80` with Python (rows built by the recursion below).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A376527CarlitzRiordanCatalan

open Polynomial Finset

/-- The Carlitz-Riordan `q`-Catalan polynomials `R_n(q)` (rows of A227543):
`R_0 = 1` and `R_{n+1}(q) = ∑_{k=0..n} q^k R_k(q) R_{n-k}(q)`. -/
noncomputable def R : ℕ → ℕ[X]
  | 0 => 1
  | n + 1 =>
    ∑ k : Fin n.succ,
      have := k.2
      have := Nat.lt_succ_of_le (Nat.sub_le n k)
      X ^ (k : ℕ) * R k * R (n - k)

/-- `R_0 = 1`. -/
theorem R_zero : R 0 = 1 := by rw [R]

/-- The defining recursion `R_{n+1} = ∑_{k=0..n} q^k R_k R_{n-k}`. -/
theorem R_succ (n : ℕ) :
    R (n + 1) = ∑ k : Fin n.succ, X ^ (k : ℕ) * R k * R (n - k) := by
  rw [R]

/-- `a(n)` (A376527): the sum of the squares of the coefficients of `R_n`.  The entry sums
`A227543(n,k)^2` over `k = 0..n(n-1)/2`; every coefficient beyond `natDegree (R n)` is zero,
so summing up to `natDegree (R n)` gives the same sum of squares of all coefficients. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ range ((R n).natDegree + 1), (R n).coeff k ^ 2

/-! ## Bridge to the Catalan numbers and their parity -/

/-- `R_n(1)` is the Catalan number `C_n`. -/
theorem R_eval_one (n : ℕ) : (R n).eval 1 = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [R_zero]
    | succ m =>
      rw [R_succ, catalan_succ, eval_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [eval_mul, eval_mul, eval_pow, eval_X, one_pow, one_mul,
        ih k (by omega), ih (m - k) (by omega)]

/-- `C_{m+1} = ∑_{i<m+1} C_i C_{m-i}` as a `range` sum. -/
theorem catalan_succ_range (m : ℕ) :
    catalan (m + 1) = ∑ i ∈ range (m + 1), catalan i * catalan (m - i) := by
  rw [catalan_succ, Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (m - i))]

/-- `C_{2j+2} = 2 ∑_{i ≤ j} C_i C_{2j+1-i}`; in particular `C_{2j+2}` is even. -/
theorem catalan_even_index (j : ℕ) :
    catalan (2 * j + 2) = 2 * ∑ i ∈ range (j + 1), catalan i * catalan (2 * j + 1 - i) := by
  have hsplit : catalan (2 * j + 2) =
      ∑ i ∈ range (j + 1), catalan i * catalan (2 * j + 1 - i) +
        ∑ x ∈ range (j + 1), catalan (j + 1 + x) * catalan (2 * j + 1 - (j + 1 + x)) := by
    rw [catalan_succ_range, show 2 * j + 1 + 1 = (j + 1) + (j + 1) by omega, sum_range_add]
  have hrefl : ∑ x ∈ range (j + 1), catalan (j + 1 + x) * catalan (2 * j + 1 - (j + 1 + x)) =
      ∑ i ∈ range (j + 1), catalan i * catalan (2 * j + 1 - i) := by
    rw [← sum_range_reflect (fun i => catalan i * catalan (2 * j + 1 - i)) (j + 1)]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [mul_comm, show 2 * j + 1 - (j + 1 + x) = j + 1 - 1 - x by omega,
      show j + 1 + x = 2 * j + 1 - (j + 1 - 1 - x) by omega]
  rw [hsplit, hrefl]
  ring

/-- `C_{2j+1} = 2 ∑_{i < j} C_i C_{2j-i} + C_j^2`. -/
theorem catalan_odd_index (j : ℕ) :
    catalan (2 * j + 1) =
      2 * ∑ i ∈ range j, catalan i * catalan (2 * j - i) + catalan j ^ 2 := by
  have hsplit : catalan (2 * j + 1) =
      ∑ i ∈ range j, catalan i * catalan (2 * j - i) +
        (∑ x ∈ range j, catalan (j + (x + 1)) * catalan (2 * j - (j + (x + 1))) +
          catalan (j + 0) * catalan (2 * j - (j + 0))) := by
    rw [catalan_succ_range, show 2 * j + 1 = j + (j + 1) by omega, sum_range_add,
      sum_range_succ']
  have hrefl : ∑ x ∈ range j, catalan (j + (x + 1)) * catalan (2 * j - (j + (x + 1))) =
      ∑ i ∈ range j, catalan i * catalan (2 * j - i) := by
    rw [← sum_range_reflect (fun i => catalan i * catalan (2 * j - i)) j]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [mul_comm, show 2 * j - (j + (x + 1)) = j - 1 - x by omega,
      show j + (x + 1) = 2 * j - (j - 1 - x) by omega]
  rw [hsplit, hrefl, show 2 * j - (j + 0) = j by omega, add_zero, sq]
  ring

/-- **Parity of the Catalan numbers.** `C_n` is odd iff `n + 1` is a power of two. -/
theorem odd_catalan_iff (n : ℕ) : Odd (catalan n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · cases j with
      | zero => exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by simp⟩
      | succ i =>
        rw [show 2 * (i + 1) = 2 * i + 2 by ring, catalan_even_index]
        constructor
        · intro h
          exact absurd h (by simp [Nat.not_odd_iff_even])
        · rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k => rw [pow_succ] at hk; omega
    · have heven : Even (2 * ∑ i ∈ range j, catalan i * catalan (2 * j - i)) :=
        even_two_mul _
      rw [catalan_odd_index, Nat.odd_add', iff_true_intro heven, iff_true,
        Nat.odd_pow_iff two_ne_zero, ih j (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩

/-! ## First rows of A227543 -/

/-- `R_1 = 1`. -/
theorem R_one : R 1 = 1 := by
  rw [R_succ]
  simp [R_zero]

/-- `R_2 = 1 + q`. -/
theorem R_two : R 2 = 1 + X := by
  rw [R_succ]
  simp [Fin.sum_univ_succ, R_zero, R_one]

/-- `R_3 = 1 + 2q + q^2 + q^3`. -/
theorem R_three : R 3 = 1 + 2 * X + X ^ 2 + X ^ 3 := by
  rw [R_succ]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, R_zero, mul_one, tsub_zero, R_two, one_mul,
    Fin.val_succ, Nat.reduceSubDiff, zero_add, pow_one, R_one, univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, tsub_self, sum_const, card_singleton, one_smul]
  ring

/-- `R_4 = 1 + 3q + 3q^2 + 3q^3 + 2q^4 + q^5 + q^6`. -/
theorem R_four : R 4 = 1 + 3 * X + 3 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 := by
  rw [R_succ]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, R_zero, mul_one, tsub_zero, R_three, one_mul,
    Fin.val_succ, Nat.reduceSubDiff, zero_add, pow_one, R_one, R_two, univ_unique,
    Fin.default_eq_zero, Fin.val_eq_zero, tsub_self, sum_const, card_singleton, one_smul]
  ring

/-! ## Ground truth: the first listed terms `1, 1, 2, 7, 34` -/

example : a 0 = 1 := by simp [a, R_zero]
example : a 1 = 1 := by simp [a, R_one]
example : a 2 = 2 := by
  have hd : (R 2).natDegree = 1 := by rw [R_two]; compute_degree!
  rw [a, hd]
  simp [sum_range_succ, R_two, coeff_one, coeff_X]
example : a 3 = 7 := by
  have hd : (R 3).natDegree = 3 := by rw [R_three]; compute_degree!
  rw [a, hd]
  simp [sum_range_succ, R_three, coeff_one, coeff_X, coeff_X_pow]
example : a 4 = 34 := by
  have hd : (R 4).natDegree = 6 := by rw [R_four]; compute_degree!
  rw [a, hd]
  simp [sum_range_succ, R_four, coeff_one, coeff_X, coeff_X_pow]

/-! ## The conjecture -/

/-- Mod 2, the sum of squares of the coefficients of `R_n` agrees with `C_n`. -/
theorem a_mod_two (n : ℕ) : a n % 2 = catalan n % 2 := by
  rw [← R_eval_one, eval_eq_sum_range, a]
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one ((R n).coeff i) with h | h <;> rw [h]

/-- **A376527 conjecture (Paul D. Hanna, Oct 11 2024).** The sum of the squares of
the coefficients of the Carlitz-Riordan `q`-Catalan polynomial `R_n` is odd iff
`n + 1` is a power of two, i.e. `n = 2^k - 1` for some `k ≥ 0`. -/
theorem odd_a_iff (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  rw [Nat.odd_iff, a_mod_two, ← Nat.odd_iff, odd_catalan_iff]

/-- The conjecture in the entry's verbatim form `n = 2^k - 1` (subtraction in `ℤ`). -/
theorem odd_a_iff_eq_two_pow_sub_one (n : ℕ) :
    Odd (a n) ↔ ∃ k : ℕ, (n : ℤ) = 2 ^ k - 1 := by
  rw [odd_a_iff]
  refine exists_congr fun k => ?_
  constructor
  · intro hk
    have hk' : ((n + 1 : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by rw [hk]
    push_cast at hk'
    linarith
  · intro hk
    have hk' : ((n + 1 : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hk'

end Candidates.A376527CarlitzRiordanCatalan
