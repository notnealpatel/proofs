/-
# A274536 — Pol: `sigma(5n) = 6 sigma(n)` iff `5 ∤ n`

## OEIS source (retrieved with `oeis show A274536`, 2026-10-21)

```
NAME:     a(n) = 6 * sigma(n).
TERMS:    6,18,24,42,36,72,48,90,78,108,72,168,84,144,144,186,108,234,120,252,
          192,216,144,360,186,252,240,336,180,432,192,378,288,324,288,546,228
FORMULA (the conjecture):
  Conjecture: a(n) = sigma(5*n) = A283118(n) iff n is not a multiple of 5.
  - _Omar E. Pol_, Oct 02 2018
```

`A283118(n) = sigma(5*n)` (terms 6,18,24,42,31,72,...).

## Status

Triage: "open" in the sense that the entry records no proof; the claim is
elementary.  If `5 ∤ n` then multiplicativity gives `σ(5n) = σ(5) σ(n) = 6 σ(n)`.
If `n = 5^k m` with `k ≥ 1` and `5 ∤ m`, then
`σ(5^(k+1)) = 5 σ(5^k) + 1 < 6 σ(5^k)` because `σ(5^k) > 1`, so
`σ(5n) < 6 σ(n)`.  Computational check: no exception for `1 ≤ n ≤ 200000`.
This file proves the conjecture outright.  The statement needs `0 < n`:
at `n = 0` Mathlib's `σ 1 0 = 0` makes both sides `0` while `5 ∣ 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A274536SigmaDivide

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A274536: `a(n) = 6 * sigma(n)`. -/
def a (n : ℕ) : ℕ := 6 * σ 1 n

/-- A283118: `b(n) = sigma(5 * n)`. -/
def b (n : ℕ) : ℕ := σ 1 (5 * n)

/-- Ground truth: the first listed terms of A274536. -/
example : (List.range 12).map (fun i => a (i + 1)) =
    [6, 18, 24, 42, 36, 72, 48, 90, 78, 108, 72, 168] := by
  decide +kernel

/-- Ground truth: the first listed terms of A283118. -/
example : (List.range 12).map (fun i => b (i + 1)) =
    [6, 18, 24, 42, 31, 72, 48, 90, 78, 93, 72, 168] := by
  decide +kernel

/-- `σ(5^(k+1)) = 5 σ(5^k) + 1`. -/
theorem sigma_five_pow_succ (k : ℕ) :
    σ 1 (5 ^ (k + 1)) = 5 * σ 1 (5 ^ k) + 1 := by
  have h5 : Nat.Prime 5 := by norm_num
  rw [sigma_one_apply_prime_pow h5, sigma_one_apply_prime_pow h5,
    Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

/-- If `5 ∤ m` then `σ(5m) = 6 σ(m)`. -/
theorem sigma_five_mul_of_not_dvd {m : ℕ} (hm : ¬ 5 ∣ m) :
    σ 1 (5 * m) = 6 * σ 1 m := by
  have hcop : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  congr 1

/-- If `0 < n` and `5 ∣ n` then `σ(5n) < 6 σ(n)`. -/
theorem sigma_five_mul_lt_of_dvd {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) :
    σ 1 (5 * n) < 6 * σ 1 n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn
  -- the exponent of `5` is positive
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    rcases e with _ | k
    · simp only [pow_zero, one_mul] at h5
      exact absurd h5 hm
    · exact ⟨k, rfl⟩
  have hcop : ∀ j, Nat.Coprime (5 ^ j) m := fun j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm)
  have hσm : 0 < σ 1 m := sigma_pos 1 m hm0
  have hσk : 0 < σ 1 (5 ^ k) := sigma_pos 1 _ (by positivity)
  have hmul : 5 * (5 ^ (k + 1) * m) = 5 ^ (k + 1 + 1) * m := by ring
  rw [hmul, isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    sigma_five_pow_succ (k + 1), sigma_five_pow_succ k]
  nlinarith

/-- **A274536 conjecture (Omar E. Pol, Oct 02 2018).** For `n ≥ 1`,
`sigma(5n) = 6 sigma(n)` if and only if `n` is not a multiple of `5`. -/
theorem sigma_five_mul_eq_iff {n : ℕ} (hn : 0 < n) :
    σ 1 (5 * n) = 6 * σ 1 n ↔ ¬ 5 ∣ n := by
  constructor
  · intro heq h5
    exact (sigma_five_mul_lt_of_dvd hn h5).ne heq
  · exact sigma_five_mul_of_not_dvd

/-- The conjecture phrased with the sequences: `A274536(n) = A283118(n)` iff
`5 ∤ n`, for `n ≥ 1`. -/
theorem a_eq_b_iff {n : ℕ} (hn : 0 < n) : a n = b n ↔ ¬ 5 ∣ n := by
  rw [a, b, eq_comm]
  exact sigma_five_mul_eq_iff hn

end Candidates.A274536SigmaDivide
