/-
# A135659 — Jasinski: every Mersenne prime greater than 3 is `≡ 7 (mod 24)`

## OEIS source (retrieved with `oeis show A135659`, 2026-10-21)

```
NAME:     a(n) = 24*n + 7.
TERMS:    7,31,55,79,103,127,151,175,199,223,247,271,295,319,343,367,391,...
AUTHOR:   Artur Jasinski, Nov 25 2007
COMMENT (the conjecture, no separate attribution or date in the entry):
  Conjecture: All Mersenne Primes (A000668) > 3 are in this sequence.
```

The comment carries no signature; the entry's author line is
_Artur Jasinski_, Nov 25 2007 (checked against the live entry).
A000668: "Mersenne primes (primes of the form 2^n - 1)", DATA
`3, 7, 31, 127, 8191, 131071, ...`.

## Status

Triage: "open" (no proof in the entry or the literature as far as the triage
could tell), tractability "trivial".  It is a folklore congruence and is
proved below (`jasinski_mersenne_prime_mem`).  Computation (Sage,
2026-10-21): every Mersenne prime `2^n - 1` with `n < 2300` other than `3`
is `≡ 7 (mod 24)`, and `2^p ≡ 8 (mod 24)` for each of the 35 further known
Mersenne exponents `3217 ≤ p ≤ 136279841`.

## Argument

Let `M = 2^n - 1` be prime with `M > 3`.  Then `n ≥ 3`.  If `n = 2k` were
even, `3 = 4 - 1 ∣ 4^k - 1 = M`, so `M = 3`, a contradiction.  Hence
`n = 2k + 3`, and `2^n = 8 · 4^k ≡ 8 (mod 24)` since `4^k ≡ 1 (mod 3)`.
So `M ≡ 7 (mod 24)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A135659MersennePrimeSatisfies

/-- Membership in A135659: `m = 24 * n + 7` for some `n ≥ 0`. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ n : ℕ, m = 24 * n + 7

/-- Membership in A000668: `m` is a prime of the form `2^n - 1`. -/
def IsMersennePrime (m : ℕ) : Prop :=
  m.Prime ∧ ∃ n : ℕ, m = 2 ^ n - 1

/-! ## Ground truth against the DATA lines -/

-- The first listed terms of A135659 are `24 * n + 7` for `n = 0, 1, 2`.
example : IsTerm 7 ∧ IsTerm 31 ∧ IsTerm 55 :=
  ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩

-- `8` is not a term.
example : ¬ IsTerm 8 := by
  rintro ⟨n, hn⟩
  omega

-- The first listed Mersenne primes `3, 7, 31, 127, 8191` of A000668.
example : IsMersennePrime 3 := ⟨by norm_num, 2, rfl⟩
example : IsMersennePrime 7 := ⟨by norm_num, 3, rfl⟩
example : IsMersennePrime 31 := ⟨by norm_num, 5, rfl⟩
example : IsMersennePrime 127 := ⟨by norm_num, 7, rfl⟩
example : IsMersennePrime 8191 := ⟨by norm_num, 13, rfl⟩

-- `15 = 2^4 - 1` is of the right form but not prime.
example : ¬ IsMersennePrime 15 := fun h => by
  have hnp : ¬ (15 : ℕ).Prime := by norm_num
  exact hnp h.1

/-! ## Helper lemmas -/

/-- `2^(2k+3) ≡ 8 (mod 24)` for every `k`. -/
theorem two_pow_two_mul_add_three_mod (k : ℕ) : 2 ^ (2 * k + 3) % 24 = 8 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow : 2 ^ (2 * (k + 1) + 3) = 4 * 2 ^ (2 * k + 3) := by ring
    rw [hpow, Nat.mul_mod, ih]

/-- For even exponent, `3 ∣ 2^(2k) - 1`. -/
theorem three_dvd_two_pow_two_mul_sub_one (k : ℕ) : 3 ∣ 2 ^ (2 * k) - 1 := by
  have hdvd : 4 - 1 ∣ 4 ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow 4 1 k
  rw [pow_mul]
  simpa using hdvd

/-- If `2^n - 1` is a prime greater than `3`, then `n` is odd and at least `3`,
i.e. `n = 2k + 3` for some `k`. -/
theorem exists_eq_two_mul_add_three {n : ℕ} (hp : (2 ^ n - 1).Prime)
    (h3 : 3 < 2 ^ n - 1) : ∃ k : ℕ, n = 2 * k + 3 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have hdvd : 3 ∣ 2 ^ n - 1 := by
      rw [hk, ← two_mul]
      exact three_dvd_two_pow_two_mul_sub_one k
    have heq : 3 = 2 ^ n - 1 :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
    omega
  · have hk1 : k ≠ 0 := by
      rintro rfl
      simp only [hk, mul_zero, zero_add, pow_one] at h3
      omega
    exact ⟨k - 1, by omega⟩

/-! ## The conjecture -/

/-- **Jasinski's conjecture (A135659, comment in the entry by Artur Jasinski,
Nov 25 2007), proved.**

Verbatim: "Conjecture: All Mersenne Primes (A000668) > 3 are in this
sequence."  Stated as: every prime `M` of the form `2^n - 1` with `3 < M`
is of the form `24 * k + 7`.  The guard `3 < M` is from the source and is
load-bearing: `3 = 2^2 - 1` is a Mersenne prime that is not a term. -/
theorem jasinski_mersenne_prime_mem (M : ℕ) (hM : IsMersennePrime M) (h3 : 3 < M) :
    IsTerm M := by
  obtain ⟨hprime, n, rfl⟩ := hM
  obtain ⟨k, rfl⟩ := exists_eq_two_mul_add_three hprime h3
  have hmod : 2 ^ (2 * k + 3) % 24 = 8 := two_pow_two_mul_add_three_mod k
  refine ⟨2 ^ (2 * k + 3) / 24, ?_⟩
  have hdiv := Nat.div_add_mod (2 ^ (2 * k + 3)) 24
  omega

/-- The same statement in the triage's form: if `2^p - 1` is a prime greater
than `3`, then `(2^p - 1) % 24 = 7`. -/
theorem mersenne_mod_twentyFour {p : ℕ} (h : (2 ^ p - 1).Prime) (h3 : 3 < 2 ^ p - 1) :
    (2 ^ p - 1) % 24 = 7 := by
  obtain ⟨k, hk⟩ := jasinski_mersenne_prime_mem (2 ^ p - 1) ⟨h, p, rfl⟩ h3
  omega

/-! ## Sanity layer -/

-- Non-vacuity: the hypotheses are jointly satisfiable at `M = 7`.
example : IsMersennePrime 7 ∧ 3 < 7 := ⟨⟨by norm_num, 3, rfl⟩, by norm_num⟩

-- The guard `3 < M` is load-bearing: `3` is a Mersenne prime and not a term.
example : IsMersennePrime 3 ∧ ¬ IsTerm 3 :=
  ⟨⟨by norm_num, 2, rfl⟩, fun ⟨n, hn⟩ => by omega⟩

-- Primality is load-bearing: `2^9 - 1 = 511 = 7 · 73` is `≡ 7 (mod 24)` by
-- accident, but `2^4 - 1 = 15` is not a term.
example : ¬ IsTerm 15 := fun ⟨n, hn⟩ => by omega

end Candidates.A135659MersennePrimeSatisfies
