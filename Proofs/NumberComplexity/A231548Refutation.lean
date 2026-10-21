/-
# A231548 — refutation of the antisigma(n) < antisigma(n-3) conjecture

## OEIS source (retrieved with `oeis show A231548` and the live entry, 2026-10-21)

```
NAME:     Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2).
TERMS:    1680,2520,3360,3780,3960,4200,4680,5040,6300,6720,7560,7920,8820,...
COMMENT:  Also numbers n such that antisigma(n) < antisigma(n-2), where
          antisigma(n) = A024816(n) = the sum of the non-divisors of n that are
          between 1 and n.
COMMENT (the conjecture, unsigned; entry author _Jaroslav Krizek_, Nov 12 2013):
          Conjecture: there are no numbers n such that antisigma(n) < antisigma(n-3).
```

No later comment or edit in the entry retracts the conjecture.

## Status

This module **refutes** the conjecture.  At `n = 332640 = 2^5 * 3^3 * 5 * 7 * 11`
we have `n - 3 = 332637 = 3 * 110879` with `110879` prime, so
`sigma(n) = 1451520`, `sigma(n-3) = 443520`, and
`antisigma(n) = 55323399600 < 55323409683 = antisigma(n-3)`.
A bounded sieve (Python, up to 4 * 10^5) found `332640` to be the least
counterexample, followed by `360360`; minimality is computational evidence
only and is not formalized here.

The conjecture is read for `n ≥ 4`, so that `n - 3` is a positive integer
(for `n ≤ 3` the truncated `n - 3 = 0` gives `antisigma 0 = 0`, which can never
exceed `antisigma n`, so the guard does not change the truth value).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A231548Refutation

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Definition layer -/

/-- `antisigma n` (OEIS A024816): the sum of the numbers `k` with `1 ≤ k ≤ n`
that do not divide `n`. -/
def antisigma (n : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ k ∣ n), k

/-- Ground truth: the first twenty terms of A024816 (offset 1). -/
example : (List.range 20).map (fun n => antisigma (n + 1)) =
    [0, 0, 2, 3, 9, 9, 20, 21, 32, 37, 54, 50, 77, 81, 96, 105, 135, 132, 170, 168] := by
  decide

/-- Gauss: `1 + 2 + ⋯ + n = n(n+1)/2`. -/
theorem sum_Icc_one_id (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, k = n * (n + 1) / 2 := by
  have hrange : ∑ k ∈ Finset.range (n + 1), k = ∑ k ∈ Finset.Icc 1 n, k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n),
      Nat.zero_add, Nat.zero_add]
    rfl
  rw [← hrange, Finset.sum_range_id]
  simp [Nat.mul_comm]

/-- The defining identity of A024816: `antisigma n + sigma n = n(n+1)/2`. -/
theorem antisigma_add_sigma_one (n : ℕ) : antisigma n + σ 1 n = n * (n + 1) / 2 := by
  rw [sigma_one_apply, antisigma, Nat.divisors, ← sum_Icc_one_id n]
  have hIco : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := rfl
  rw [hIco]
  exact Finset.sum_filter_not_add_sum_filter _ _ _

/-- `antisigma n = n(n+1)/2 - sigma n` (the truncated subtraction is exact by
`antisigma_add_sigma_one`). -/
theorem antisigma_eq (n : ℕ) : antisigma n = n * (n + 1) / 2 - σ 1 n := by
  have hsum := antisigma_add_sigma_one n
  omega

/-! ## The conjecture -/

/-- **Krizek's conjecture (A231548, comment; entry by Jaroslav Krizek, Nov 12 2013).**

Verbatim: "Conjecture: there are no numbers n such that antisigma(n) <
antisigma(n-3)."  Stated for `n ≥ 4`, i.e. whenever `n - 3` is a positive
integer: `antisigma (n - 3) ≤ antisigma n`. -/
def Conjecture : Prop := ∀ n : ℕ, 4 ≤ n → antisigma (n - 3) ≤ antisigma n

/-! ## The counterexample -/

/-- `sigma p = p + 1` for a prime `p`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have hpow := sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at hpow
  rw [hpow, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, Nat.add_comm]

/-- `sigma(332640) = 1451520`, from `332640 = 2^5 * 3^3 * 5 * 7 * 11`. -/
theorem sigma_one_332640 : σ 1 332640 = 1451520 := by
  have hmul := (isMultiplicative_sigma (k := 1))
  have hfac : (332640 : ℕ) = 2 ^ 5 * (3 ^ 3 * (5 * (7 * 11))) := by norm_num
  rw [hfac, hmul.map_mul_of_coprime (by norm_num), hmul.map_mul_of_coprime (by norm_num),
    hmul.map_mul_of_coprime (by norm_num), hmul.map_mul_of_coprime (by norm_num),
    sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
    sigma_one_prime (by norm_num), sigma_one_prime (by norm_num),
    sigma_one_prime (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `sigma(332637) = 443520`, from `332637 = 3 * 110879` with `110879` prime. -/
theorem sigma_one_332637 : σ 1 332637 = 443520 := by
  have hmul := (isMultiplicative_sigma (k := 1))
  have hfac : (332637 : ℕ) = 3 * 110879 := by norm_num
  rw [hfac, hmul.map_mul_of_coprime (by norm_num),
    sigma_one_prime (by norm_num), sigma_one_prime (by norm_num)]
  norm_num

/-- The counterexample: `antisigma 332640 = 55323399600 < 55323409683 =
antisigma 332637`. -/
theorem antisigma_332640_lt : antisigma 332640 < antisigma (332640 - 3) := by
  rw [antisigma_eq, antisigma_eq, show (332640 : ℕ) - 3 = 332637 by norm_num,
    sigma_one_332640, sigma_one_332637]
  norm_num

/-- **Krizek's A231548 conjecture is false.**  The witness is
`n = 332640 = 2^5 * 3^3 * 5 * 7 * 11`: here `n - 3 = 3 * 110879` with `110879`
prime, so `sigma(n) - sigma(n-3) = 1008000 > 3n - 3 = 997917`, i.e.
`antisigma(n) < antisigma(n-3)`.  The author presumably extrapolated from a
search below `332640`; highly composite `n` with `sigma(n)/n > 4` and
`n - 3` three times a prime break the inequality. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  exact absurd (hconj 332640 (by norm_num)) (Nat.not_le.mpr antisigma_332640_lt)

end Candidates.A231548Refutation
