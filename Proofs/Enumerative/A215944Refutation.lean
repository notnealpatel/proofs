/-
Refutation of the representation dichotomy in OEIS A215944
(unsigned conjecture in the 2012 submission; T. D. Noe's note, Aug 28 2012).

N=3048841=61*151*331 is a base-2 Fermat pseudoprime divisible by the
smaller pseudoprime 49981=151*331. It has neither form
p*((m+1)p-m)*((n+1)p-n) nor 5461*(42k-13).
This refutes both the broad wording and its restriction to the three-prime
sequence A215944. No least-counterexample or search-completeness claim is made.
The natural parameters include zero and need not be prime, so nonrepresentation
also holds under stricter readings. At k=0 the truncated 42k-13 gives zero,
not a pseudoprime; (m+1)p-m does not truncate for p≥1.
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

/-! ## Examples -/

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

/-- The A215944 representation dichotomy fails: `3048841=61*151*331` is a
base-2 pseudoprime divisible by the smaller pseudoprime `49981`, but belongs
to neither representation family. -/
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
