/-
# A090825 — Cloitre: refutation of the A053176 membership conjecture

## OEIS source (retrieved with `oeis show A090825` and checked against
## https://oeis.org/A090825 on 2026-10-21)

```
NAME:     Nonprimes n such that (3/2)*(1/n)*(2*n+1)*(3^n+1)*B(2*n) is an
          integer, where B(k) denotes the k-th Bernoulli number.
TERMS:    1,49,91,119,133,169,217,221,247,259,289,301,323,329,335,343,361,
          403,413,427,469,481,497,511,517,527,553,559,589,611,629,637,679,
          703,707,721,731,749
COMMENT:  Conjecture: composite numbers with all prime factors in A053176 are
          in the sequence. For p prime (3/2)*(1/p)*(2*p+1)*(3^p+1)*B(2*p) == 1
          (mod p). There are few terms n with
          (3/2)*(1/n)*(2*n+1)*(3^n+1)*B(2*n) == 1 (mod n): 91,247,....Is this
          subsequence finite?
AUTHOR:   Benoit Cloitre, Feb 11 2004
```

A053176 is the sequence of primes `p` such that `2p + 1` is composite.  The
live entry carries no later comment retracting the conjecture.

## Status

This module **refutes** the conjecture (first sentence of the comment).  The
smallest counterexample is `n = 833 = 7^2 * 17`: both `2*7 + 1 = 15` and
`2*17 + 1 = 35` are composite, but by von Staudt–Clausen the prime
`239 = 2*119 + 1` divides the denominator of `B(1666)` while it divides none of
`3`, `2*833 + 1 = 1667` or `3^833 + 1` (indeed `3^833 ≡ 1 (mod 239)`).

Computational evidence (Sage, exact rationals, not part of the proof): the
conjecture holds for every eligible composite `n < 833`; the counterexamples
up to `2873` are `833, 1547, 2023, 2261, 2303, 2873`.  The open finiteness
question in the same comment is not addressed here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A090825Refutation

/-- Cloitre's quantity `(3/2) * (1/n) * (2n+1) * (3^n+1) * B(2n)` as a rational
number, with `B = bernoulli` (Mathlib's convention `B(1) = -1/2`; only even
indices `2n` occur, where both conventions agree).  At `n = 0` the factor
`1/n` takes Lean's junk value `0`; the sequence predicate below excludes
`n = 0`. -/
noncomputable def cloitreValue (n : ℕ) : ℚ :=
  (3 / 2) * (1 / (n : ℚ)) * (2 * n + 1) * (3 ^ n + 1) * bernoulli (2 * n)

/-- Membership in A090825: `n` is a positive nonprime and `cloitreValue n` is
an integer.  The positivity guard matches the entry's offset (first term `1`)
and keeps `1/n` off its junk value. -/
def InA090825 (n : ℕ) : Prop :=
  0 < n ∧ ¬ n.Prime ∧ ∃ z : ℤ, cloitreValue n = z

/-- Membership in A053176: `p` is a prime and `2p + 1` is composite (`2p + 1 ≥ 5`
is never `1`, so "composite" is "not prime"). -/
def InA053176 (p : ℕ) : Prop :=
  p.Prime ∧ ¬ (2 * p + 1).Prime

/-! ## Ground truth -/

/-- First terms of A053176 (`7, 13, 17, 19`) and the excluded primes `2, 3, 5`
(`5, 7, 11` are prime). -/
example : InA053176 7 ∧ InA053176 13 ∧ InA053176 17 ∧ InA053176 19 ∧
    ¬ InA053176 2 ∧ ¬ InA053176 3 ∧ ¬ InA053176 5 := by
  simp only [InA053176]
  norm_num

/-- `cloitreValue 1 = 3` since `B(2) = 1/6`. -/
theorem cloitreValue_one : cloitreValue 1 = 3 := by
  rw [cloitreValue, bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  norm_num [bernoulli'_two]

/-- The first listed term `1` is in A090825. -/
example : InA090825 1 :=
  ⟨by norm_num, Nat.not_prime_one, ⟨3, by rw [cloitreValue_one]; norm_num⟩⟩

/-- The prime `2` is not in A090825. -/
example : ¬ InA090825 2 := fun h => h.2.1 Nat.prime_two

/-- `B(6) = 1/42`, via the defining recurrence. -/
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (n := 5) (by decide) (by norm_num), Nat.choose]

/-- `B(8) = -1/30`, via the defining recurrence. -/
theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six,
    bernoulli'_eq_zero_of_odd (n := 5) (by decide) (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) (by decide) (by norm_num), Nat.choose]

/-- `4` is not in A090825 (it is absent from the listed terms):
`cloitreValue 4 = -369/40`. -/
example : ¬ InA090825 4 := by
  rintro ⟨-, -, z, hz⟩
  have hval : cloitreValue 4 = -369 / 40 := by
    rw [cloitreValue, bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
    norm_num [bernoulli'_eight]
  rw [hval] at hz
  have hz' : (-369 : ℚ) = 40 * z := by linarith
  have hZ : (-369 : ℤ) = 40 * z := by exact_mod_cast hz'
  omega

/-! ## The conjecture -/

/-- **Cloitre's conjecture (A090825, Benoit Cloitre, Feb 11 2004).**

Verbatim: "Conjecture: composite numbers with all prime factors in A053176 are
in the sequence."

Every composite `n` (that is, `1 < n` and `n` not prime) all of whose prime
factors lie in A053176 belongs to A090825. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime → (∀ p ∈ n.primeFactors, InA053176 p) → InA090825 n

/-! ## The counterexample `n = 833` -/

/-- The von Staudt–Clausen prime set for `B(1666)`: the primes `p < 1668` with
`p - 1 ∣ 1666` are exactly `2, 3, 239, 1667`. -/
theorem vonStaudtPrimes_833 :
    (Finset.range (2 * 833 + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * 833) =
      {2, 3, 239, 1667} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hp, hdvd⟩
    obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    rw [Nat.add_sub_cancel] at hdvd
    have hmem : d ∈ Nat.divisors 1666 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    simp only [Nat.divisors_ofNat, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | norm_num at hp
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

/-- von Staudt–Clausen at `k = 833`: `B(1666) = w - (1/2 + 1/3 + 1/239 + 1/1667)`
for some integer `w`. -/
theorem bernoulli_1666_eq : ∃ w : ℤ,
    bernoulli 1666 = w - (1 / 2 + 1 / 3 + 1 / 239 + 1 / 1667) := by
  obtain ⟨w, hw⟩ := Bernoulli.vonStaudt_clausen 833
  rw [vonStaudtPrimes_833] at hw
  refine ⟨w, ?_⟩
  rw [hw]
  norm_num [Finset.sum_insert]

/-- `239 ∤ 3 * 1667 * (3^833 + 1) * c`, where `c = 6 * 239 * 1667 * (1/2 + 1/3 +
1/239 + 1/1667)` is the cleared numerator of the von Staudt–Clausen sum. -/
theorem not_dvd_239 : ¬ (239 : ℤ) ∣
    3 * 1667 * (3 ^ 833 + 1) * (3 * 239 * 1667 + 2 * 239 * 1667 + 6 * 1667 + 6 * 239) := by
  rw [Int.dvd_iff_emod_eq_zero]
  decide +kernel

/-- `cloitreValue 833` is not an integer: `239` survives in its denominator. -/
theorem cloitreValue_833_not_int : ¬ ∃ m : ℤ, cloitreValue 833 = m := by
  rintro ⟨m, hm⟩
  obtain ⟨w, hw⟩ := bernoulli_1666_eq
  -- Clear the denominators `2 * 833` and `2 * 3 * 239 * 1667`.
  have hQ : ((2 * 833 * (2 * 3 * 239 * 1667) * m : ℤ) : ℚ) =
      ((3 * 1667 * (3 ^ 833 + 1) * ((2 * 3 * 239 * 1667) * w -
        (3 * 239 * 1667 + 2 * 239 * 1667 + 6 * 1667 + 6 * 239)) : ℤ) : ℚ) := by
    rw [Int.cast_mul, ← hm]
    simp only [cloitreValue, hw, Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow,
      Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat]
    generalize (3 : ℚ) ^ 833 = t
    ring
  have hZ := Int.cast_injective hQ
  -- Every term except the cleared numerator carries the factor `239`.
  have h239 : (3 * 1667 * (3 ^ 833 + 1) *
        (3 * 239 * 1667 + 2 * 239 * 1667 + 6 * 1667 + 6 * 239) : ℤ) =
      239 * (2 * 3 * 1667 * (3 * 1667 * (3 ^ 833 + 1) * w - 2 * 833 * m)) := by
    generalize (3 : ℤ) ^ 833 = t at hZ ⊢
    linear_combination hZ
  exact not_dvd_239 ⟨_, h239⟩

/-- `833 = 7^2 * 17` is composite and its prime factors `7` and `17` lie in
A053176 (`15` and `35` are composite). -/
theorem eligible_833 :
    1 < 833 ∧ ¬ (833 : ℕ).Prime ∧ ∀ p ∈ (833 : ℕ).primeFactors, InA053176 p := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro p hp
  have hp' : p = 7 ∨ p = 17 := by
    simpa [Nat.primeFactors, Nat.primeFactorsList_ofNat] using hp
  simp only [InA053176]
  rcases hp' with rfl | rfl <;> norm_num

/-- **Refutation of Cloitre's conjecture.**  `n = 833 = 7^2 * 17` is composite,
its prime factors `7, 17` are in A053176, yet
`(3/2) * (1/833) * 1667 * (3^833 + 1) * B(1666)` is not an integer: by
von Staudt–Clausen the prime `239 = 2 * 119 + 1` divides the denominator of
`B(1666)` and divides none of `3`, `1667`, `3^833 + 1`.

The mechanism is a composite divisor `m = 119` of `n` with `2m + 1` prime, which
the prime-factor hypothesis does not see.  A plausible intended hypothesis is
that `2d + 1` be composite for every divisor `d > 1` of `n`; this stronger form
is only supported computationally (Sage, `n ≤ 2000`) and is not proved here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨h1, hnp, hfac⟩ := eligible_833
  exact cloitreValue_833_not_int (hconj 833 h1 hnp hfac).2.2

end Candidates.A090825Refutation
