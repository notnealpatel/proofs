/-
# A129454 — Bala's p-adic valuation conjecture is off by one

## OEIS source (retrieved with `oeis show A129454` and the live
## `oeis.org/A129454/internal` page, 2026-10-21)

```
NAME:    a(n) = Product{i=1..n-1} Product{j=1..n-1} Product{k=1..n-1} gcd(i,j,k).
OFFSET:  0,4
TERMS:   1,1,1,2,6,1536,7680,8806025134080,61642175938560,...
FORMULA: a(n) = Product{i=1..n-1} Product{j=1..n-1} Product{k=1..n-1} gcd(i,j,k),
         for n > 2, otherwise a(n) = 1.
COMMENT: Conjecture: Let p be a prime and let ordp(n,p) denote the largest power
         of p which divides n. For example, ordp(48,2)=4 since 48 = 3*(2^4). Then
         we conjecture that the prime factorization of a(n) is given by
         ordp(a(n),p)=(floor(n/p))^3 + (floor(n/p^2))^3 + (floor(n/p^3))^3 + . . ..
         Compare with the comments in A092287.
AUTHOR:  Peter Bala, Apr 16 2007
```

The comment is unsigned, so it belongs to the original submission by the entry
author, Peter Bala (Apr 16 2007).  No later comment retracts or corrects it; the
only later edit (G. C. Greubel, Feb 07 2024) touches the programs.

## Status

This module refutes the conjecture as printed: at `n = 4`, `p = 2` the entry
gives `a(4) = 6`, so `ordp(a(4),2) = 1`, while the formula gives
`floor(4/2)^3 + floor(4/4)^3 = 9` (the value `9` is `ordp(a(5),2)`, since
`a(5) = 1536 = 2^9 * 3`).  The formula is off by one in the index: the
corrected statement `ordp(a(n+1),p) = Σ_{t ≥ 1} floor(n/p^t)^3`, obtained by
counting triples in `[1,n]^3` all divisible by `p^t`, is proved below as
`padicValNat_a_succ`.  (Compare A092287, whose product runs over `[1,n]`
rather than `[1,n-1]`.)
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A129454Refutation

open Finset

/-- OEIS A129454: `a(n) = ∏_{i=1}^{n-1} ∏_{j=1}^{n-1} ∏_{k=1}^{n-1} gcd(i,j,k)`.
The index range `[1, n-1]` is written `Ico 1 n` to avoid natural-number
subtraction; for `n ≤ 1` the products are empty and `a n = 1`, matching the
entry's convention and its first terms. -/
def a (n : ℕ) : ℕ :=
  ∏ i ∈ Ico 1 n, ∏ j ∈ Ico 1 n, ∏ k ∈ Ico 1 n, Nat.gcd (Nat.gcd i j) k

/-! ## Ground truth against the listed terms `1,1,1,2,6,1536,7680,8806025134080` -/

example : a 0 = 1 := by decide
example : a 1 = 1 := by decide
example : a 2 = 1 := by decide
example : a 3 = 2 := by decide
example : a 4 = 6 := by decide
example : a 5 = 1536 := by decide
example : a 6 = 7680 := by decide
example : a 7 = 8806025134080 := by decide

/-! ## The conjecture as printed -/

/-- **Bala's conjecture (A129454, Peter Bala, Apr 16 2007), as printed.**
For every prime `p` and every `n`,
`ordp(a(n),p) = floor(n/p)^3 + floor(n/p^2)^3 + floor(n/p^3)^3 + ⋯`.

`ordp(m,p)` is the exponent of `p` in `m`, i.e. `padicValNat p m` (here
`a n ≥ 1`, so no zero junk arises).  The infinite sum is truncated to
`t ∈ [1, n]`; this loses nothing because `p ^ t ≥ 2 ^ t > n` for `t > n`, so all
omitted terms are `0`. -/
def Conjecture : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, padicValNat p (a n) = ∑ t ∈ Icc 1 n, (n / p ^ t) ^ 3

/-- **The printed conjecture is false.** Counterexample `n = 4`, `p = 2`:
`a 4 = gcd(2,2,2) · gcd(3,3,3) = 6` has `2`-adic valuation `1`, but the
formula gives `(4/2)^3 + (4/4)^3 = 9`.  (Also `n = 2`, `p = 2`: `a 2 = 1`
versus `1`.)  The author presumably intended the index shift
`ordp(a(n+1),p) = Σ_t floor(n/p^t)^3`, proved as `padicValNat_a_succ`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h4 : padicValNat 2 (a 4) = ∑ t ∈ Icc 1 4, (4 / 2 ^ t) ^ 3 := h 2 Nat.prime_two 4
  have ha : a 4 = 6 := by decide
  have hsum : ∑ t ∈ Icc 1 4, (4 / 2 ^ t) ^ 3 = 9 := by decide
  rw [ha, hsum] at h4
  have hdvd : 2 ^ padicValNat 2 6 ∣ 6 := pow_padicValNat_dvd
  rw [h4] at hdvd
  exact absurd hdvd (by decide)

/-! ## The corrected statement -/

/-- The number of multiples of `q` in `[1, n]` is `n / q`, as an indicator sum. -/
theorem sum_ite_dvd_Ico (n q : ℕ) :
    ∑ x ∈ Ico 1 (n + 1), (if q ∣ x then 1 else 0) = n / q := by
  rw [← card_filter, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

/-- Expanding a cube of a sum and exchanging the order of summation:
`Σ_{i,j,k ∈ s} Σ_{t ∈ T} f t i · f t j · f t k = Σ_{t ∈ T} (Σ_{i ∈ s} f t i)^3`. -/
theorem sum_sum_sum_sum_mul_mul (s T : Finset ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ t ∈ T, f t i * f t j * f t k
      = ∑ t ∈ T, (∑ i ∈ s, f t i) ^ 3 := by
  have hcube : ∀ t, (∑ i ∈ s, f t i) ^ 3
      = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f t i * f t j * f t k := by
    intro t
    rw [pow_three', sum_mul_sum]
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
  simp only [hcube]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]

/-- **Corrected form (index shifted by one).** For every prime `p` and every `n`,
`ordp(a(n+1),p) = Σ_{t=1}^{n} floor(n/p^t)^3`; equivalently
`ordp(a(n),p) = Σ_t floor((n-1)/p^t)^3` for `n ≥ 1`.  The sum over `t ∈ [1,n]`
contains every nonzero term. -/
theorem padicValNat_a_succ (p n : ℕ) (hp : p.Prime) :
    padicValNat p (a (n + 1)) = ∑ t ∈ Icc 1 n, (n / p ^ t) ^ 3 := by
  have hpos : ∀ i ∈ Ico 1 (n + 1), 0 < i := fun i hi => by
    simp only [mem_Ico] at hi; omega
  let F : ℕ → ℕ → ℕ := fun t i => if p ^ t ∣ i then 1 else 0
  have key : ∀ i ∈ Ico 1 (n + 1), ∀ j ∈ Ico 1 (n + 1), ∀ k ∈ Ico 1 (n + 1),
      (Nat.gcd (Nat.gcd i j) k).factorization p
        = ∑ t ∈ Icc 1 n, F t i * F t j * F t k := by
    intro i _ j _ k hk
    have hg : 0 < Nat.gcd (Nat.gcd i j) k := Nat.gcd_pos_of_pos_right _ (hpos k hk)
    have hle : Nat.gcd (Nat.gcd i j) k ≤ n := by
      have hgk := Nat.le_of_dvd (hpos k hk) (Nat.gcd_dvd_right (Nat.gcd i j) k)
      simp only [mem_Ico] at hk; omega
    have hlt : Nat.gcd (Nat.gcd i j) k < p ^ (n + 1) :=
      (lt_of_le_of_lt hle (Nat.lt_pow_self hp.one_lt)).trans_le
        (Nat.pow_le_pow_right hp.pos (Nat.le_succ n))
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hg hlt, card_filter]
    refine sum_congr rfl fun t _ => ?_
    simp only [F, Nat.dvd_gcd_iff]
    split_ifs <;> simp_all
  have hne : ∀ i ∈ Ico 1 (n + 1), ∀ j ∈ Ico 1 (n + 1), ∀ k ∈ Ico 1 (n + 1),
      Nat.gcd (Nat.gcd i j) k ≠ 0 := fun i _ j _ k hk =>
    (Nat.gcd_pos_of_pos_right _ (hpos k hk)).ne'
  have hsplit : (a (n + 1)).factorization p = ∑ i ∈ Ico 1 (n + 1), ∑ j ∈ Ico 1 (n + 1),
      ∑ k ∈ Ico 1 (n + 1), (Nat.gcd (Nat.gcd i j) k).factorization p := by
    rw [a, Nat.factorization_prod fun i hi => prod_ne_zero_iff.2 fun j hj =>
      prod_ne_zero_iff.2 fun k hk => hne i hi j hj k hk, Finset.sum_apply']
    refine sum_congr rfl fun i hi => ?_
    rw [Nat.factorization_prod fun j hj =>
      prod_ne_zero_iff.2 fun k hk => hne i hi j hj k hk, Finset.sum_apply']
    refine sum_congr rfl fun j hj => ?_
    rw [Nat.factorization_prod fun k hk => hne i hi j hj k hk, Finset.sum_apply']
  rw [← Nat.factorization_def _ hp, hsplit]
  calc ∑ i ∈ Ico 1 (n + 1), ∑ j ∈ Ico 1 (n + 1), ∑ k ∈ Ico 1 (n + 1),
        (Nat.gcd (Nat.gcd i j) k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), ∑ j ∈ Ico 1 (n + 1), ∑ k ∈ Ico 1 (n + 1),
        ∑ t ∈ Icc 1 n, F t i * F t j * F t k :=
        sum_congr rfl fun i hi => sum_congr rfl fun j hj => sum_congr rfl fun k hk =>
          key i hi j hj k hk
    _ = ∑ t ∈ Icc 1 n, (∑ i ∈ Ico 1 (n + 1), F t i) ^ 3 := sum_sum_sum_sum_mul_mul _ _ F
    _ = ∑ t ∈ Icc 1 n, (n / p ^ t) ^ 3 := sum_congr rfl fun t _ => by
        rw [sum_ite_dvd_Ico n (p ^ t)]

/-- Sanity instance of the corrected form: `ordp(a(5),2) = 9`, matching
`a(5) = 1536 = 2^9 · 3`. -/
example : padicValNat 2 (a 5) = 9 := by
  rw [padicValNat_a_succ 2 4 Nat.prime_two]
  decide

end Candidates.A129454Refutation
