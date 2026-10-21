/-
# A215944 — Fermat pseudoprimes divisible by a smaller one: the
# `p*((m+1)p-m)*((n+1)p-n)` / `5461*(42k-13)` dichotomy (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A215944`)

```
NAME:     Fermat pseudoprimes to base 2 with three prime factors divisible
          by a smaller Fermat pseudoprime to base 2.
TERMS:    13981,137149,158369,176149,276013,285541,294409,348161,387731,
          423793,488881,493697,617093,625921,847261,1052503,1052929,1104349,
          1128121,1152271,1398101,1461241,1472353,1507561,1534541,1549411,
          1746289,1840357,1857241,2299081
COMMENT:  These are members of A215150 having three divisors.
          - _T. D. Noe_, Aug 28 2012
COMMENT:  Almost all the numbers from the sequence above can be written as
          p*((m + 1)*p - m)*((n + 1)*p - n), where m, n, p are natural
          numbers (in the brackets is written the Poulet number which every
          one of them is divisible by): ...
COMMENT:  The only few numbers from the sequence above that can't be written
          this way are multiples of the Poulet number 5461 and can be,
          instead, written as 5461*(42*k - 13): 158369 = 5461*29,
          387731 = 5461*71, 617093 = 5461*113 and 1534541 = 5461*281.
COMMENT:  Conjecture: The only Fermat pseudoprimes to base 2 divisible by a
          smaller Fermat pseudoprime to base 2 that can't be written as
          p*((m + 1)*p - m)*((n + 1)*p - n), where m, n, p are natural
          numbers, are multiples of 5461 and can be written as
          5461*(42*k - 13).
COMMENT:  Conjecture is checked for the numbers from the sequence above and
          for the first 15 Poulet numbers with four prime factors.
```

The conjecture comments are unsigned in the retrieved entry; they
belong to the 2012 submission (the entry's comment block is dated by
T. D. Noe's Aug 28 2012 note and lists only the first 30 terms).

## Status

Triage status: **false**.  No proof or refutation was found in the
entry or the literature; the triage found a counterexample by
enumeration of base-2 pseudoprimes below `3.676e8`.

This module **refutes** the conjecture (`conjecture_false`).  The
counterexample is `N = 3048841 = 61 * 151 * 331`, the smallest exception
the triage found (its search is complete below `3.676e8`): `N` is a
base-2 Fermat pseudoprime (`fermatPsp_N`), it is divisible by the
smaller base-2 Fermat pseudoprime `49981 = 151 * 331` (`fermatPsp_d`),
it is not of the form `p*((m+1)p-m)*((n+1)p-n)` (`not_isPQForm_N`,
a finite check over the divisors of `N`), and `5461 ∤ N`
(`N mod 5461 = 1603`), so it is not of the form `5461*(42k-13)`
(`not_is5461Form_N`).

The statement reads "natural numbers" with the weakest convention,
`m n p : ℕ` including `0` and with no primality required of the three
factors; this only enlarges the set of representable numbers, so the
refutation applies under every stricter reading as well.  The Lean
truncated subtraction in `42 * k - 13` makes `k = 0` give `0`, which
is not a pseudoprime; `(m + 1) * p - m` never truncates for `p ≥ 1`.

`Elab.async false` keeps the kernel checks sequential; under a virtual-memory
cap the asynchronous elaboration of the theorems cannot spawn threads.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A215944Refutation

/-! ## Definition layer

Fermat pseudoprimes to base 2 (Poulet numbers, A001567) are Mathlib's
`Nat.FermatPsp n 2`: `n ∣ 2 ^ (n - 1) - 1`, `n` not prime, `1 < n`. -/

/-- The first representation in the conjecture: `N = p*((m+1)p-m)*((n+1)p-n)`
for some natural numbers `p, m, n`. -/
def IsPQForm (N : ℕ) : Prop :=
  ∃ p m n : ℕ, N = p * ((m + 1) * p - m) * ((n + 1) * p - n)

/-- The exceptional representation in the conjecture: `N = 5461*(42k-13)`
for some natural number `k`. -/
def Is5461Form (N : ℕ) : Prop :=
  ∃ k : ℕ, N = 5461 * (42 * k - 13)

/-- `N` is divisible by a smaller base-2 Fermat pseudoprime. -/
def HasSmallerPspDivisor (N : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ N ∧ d < N ∧ Nat.FermatPsp d 2

/-- A215944 membership: a base-2 Fermat pseudoprime with three prime factors
(counted with multiplicity) divisible by a smaller base-2 Fermat pseudoprime. -/
def InA215944 (N : ℕ) : Prop :=
  Nat.FermatPsp N 2 ∧ N.primeFactorsList.length = 3 ∧ HasSmallerPspDivisor N

/-- A product of three primes has a prime factor list of length three. -/
theorem length_primeFactorsList_of_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) : (p * q * r).primeFactorsList.length = 3 := by
  rw [(Nat.perm_primeFactorsList_mul (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero).length_eq,
    List.length_append, (Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero).length_eq,
    List.length_append, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq,
    Nat.primeFactorsList_prime hr]
  rfl

/-! ## Ground truth -/

/-- `341 = 11 * 31`, the smallest base-2 Fermat pseudoprime, is one. -/
example : Nat.FermatPsp 341 2 :=
  ⟨by unfold Nat.ProbablePrime; decide +kernel,
    Nat.not_prime_of_dvd_of_lt (m := 11) (by norm_num) (by norm_num) (by norm_num),
    by norm_num⟩

/-- `11` is prime, so not a pseudoprime; `15` is composite but `2^14 ≢ 1 (mod 15)`. -/
example : ¬ Nat.FermatPsp 11 2 ∧ ¬ Nat.FermatPsp 15 2 := by
  refine ⟨fun h => h.2.1 (by norm_num), fun h => ?_⟩
  have h1 := h.1
  unfold Nat.ProbablePrime at h1
  revert h1
  decide

/-- The first term `13981 = 11 * 31 * 41` of A215944: it lies in the sequence
(divisible by `341`) and has the first form with `p = 11, m = 2, n = 3`. -/
example : InA215944 13981 ∧ IsPQForm 13981 := by
  refine ⟨⟨⟨by unfold Nat.ProbablePrime; decide +kernel,
    Nat.not_prime_of_dvd_of_lt (m := 11) (by norm_num) (by norm_num) (by norm_num),
    by norm_num⟩, ?_, ⟨341, by norm_num, by norm_num,
      ⟨by unfold Nat.ProbablePrime; decide +kernel,
        Nat.not_prime_of_dvd_of_lt (m := 11) (by norm_num) (by norm_num) (by norm_num),
        by norm_num⟩⟩⟩, ⟨11, 2, 3, by norm_num⟩⟩
  rw [show (13981 : ℕ) = 11 * 31 * 41 by norm_num]
  exact length_primeFactorsList_of_three_primes (by norm_num) (by norm_num) (by norm_num)

/-- The listed exception `158369 = 5461 * 29` has the second form with `k = 1`. -/
example : Is5461Form 158369 := ⟨1, by norm_num⟩

/-! ## The counterexample `N = 3048841` -/

/-- `3048841 = 61 * 151 * 331` is a base-2 Fermat pseudoprime. -/
theorem fermatPsp_N : Nat.FermatPsp 3048841 2 := by
  refine ⟨?_, ?_, by norm_num⟩
  · unfold Nat.ProbablePrime
    decide +kernel
  · exact Nat.not_prime_of_dvd_of_lt (m := 61) (by norm_num) (by norm_num) (by norm_num)

/-- `49981 = 151 * 331` is a base-2 Fermat pseudoprime. -/
theorem fermatPsp_d : Nat.FermatPsp 49981 2 := by
  refine ⟨?_, ?_, by norm_num⟩
  · unfold Nat.ProbablePrime
    decide +kernel
  · exact Nat.not_prime_of_dvd_of_lt (m := 151) (by norm_num) (by norm_num) (by norm_num)

/-- `3048841` is divisible by the smaller base-2 Fermat pseudoprime `49981`. -/
theorem hasSmallerPspDivisor_N : HasSmallerPspDivisor 3048841 :=
  ⟨49981, ⟨61, by norm_num⟩, by norm_num, fermatPsp_d⟩

/-- `3048841` has exactly three prime factors, so it is a term of A215944. -/
theorem inA215944_N : InA215944 3048841 := by
  refine ⟨fermatPsp_N, ?_, hasSmallerPspDivisor_N⟩
  rw [show (3048841 : ℕ) = 61 * 151 * 331 by norm_num]
  exact length_primeFactorsList_of_three_primes (by norm_num) (by norm_num) (by norm_num)

/-- The divisors of `3048841 = 61 * 151 * 331`. -/
theorem divisors_N :
    Nat.divisors 3048841 = {1, 61, 151, 331, 9211, 20191, 49981, 3048841} := by
  rw [show (3048841 : ℕ) = 61 * 151 * 331 by norm_num, Nat.divisors_mul, Nat.divisors_mul,
    Nat.Prime.divisors (by norm_num), Nat.Prime.divisors (by norm_num),
    Nat.Prime.divisors (by norm_num)]
  decide +kernel

/-- `3048841` is not of the form `p*((m+1)p-m)*((n+1)p-n)`: both `p` and
`(m+1)p-m` divide `3048841`, and for each of the `8 * 8` divisor pairs the
remaining linear constraints on `m, n` are infeasible. -/
theorem not_isPQForm_N : ¬ IsPQForm 3048841 := by
  rintro ⟨p, m, n, h⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (m + 1) * p - m := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (n + 1) * p - n := ⟨_, rfl⟩
  rw [← hA, ← hB] at h
  have hp : p ∈ Nat.divisors 3048841 :=
    Nat.mem_divisors.mpr ⟨⟨A * B, by rw [h, mul_assoc]⟩, by norm_num⟩
  have hAd : A ∈ Nat.divisors 3048841 :=
    Nat.mem_divisors.mpr ⟨⟨p * B, by rw [h]; ring⟩, by norm_num⟩
  rw [divisors_N] at hp hAd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hAd
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hAd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

/-- `3048841` is not of the form `5461*(42k-13)`, since `5461 ∤ 3048841`. -/
theorem not_is5461Form_N : ¬ Is5461Form 3048841 := by
  rintro ⟨k, h⟩
  omega

/-! ## The conjecture -/

/-- **A215944 conjecture (2012), refuted.**

Verbatim: "Conjecture: The only Fermat pseudoprimes to base 2 divisible by a
smaller Fermat pseudoprime to base 2 that can't be written as
p*((m + 1)*p - m)*((n + 1)*p - n), where m, n, p are natural numbers, are
multiples of 5461 and can be written as 5461*(42*k - 13)."

The theorem states the negation of: every base-2 Fermat pseudoprime `N` with a
smaller base-2 Fermat pseudoprime divisor is of the form
`p*((m+1)p-m)*((n+1)p-n)` or of the form `5461*(42k-13)`.  Counterexample:
`N = 3048841 = 61 * 151 * 331`, divisible by the pseudoprime `49981`. -/
theorem conjecture_false :
    ¬ ∀ N : ℕ, Nat.FermatPsp N 2 → HasSmallerPspDivisor N →
      IsPQForm N ∨ Is5461Form N := by
  intro h
  rcases h 3048841 fermatPsp_N hasSmallerPspDivisor_N with hpq | h5461
  · exact not_isPQForm_N hpq
  · exact not_is5461Form_N h5461

/-- The counterexample already lies in A215944 itself (three prime factors),
so the conjecture fails even restricted to the terms of the sequence. -/
theorem conjecture_false_on_A215944 :
    ∃ N : ℕ, InA215944 N ∧ ¬ IsPQForm N ∧ ¬ Is5461Form N :=
  ⟨3048841, inA215944_N, not_isPQForm_N, not_is5461Form_N⟩

end Candidates.A215944Refutation
