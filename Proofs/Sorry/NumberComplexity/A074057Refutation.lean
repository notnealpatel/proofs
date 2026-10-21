/-
# A074057 — Cloitre: `2 φ(n-2) = n-1` iff `n` is a Fermat prime

## OEIS source (retrieved with `oeis show A074057` and the live entry, 2026-10-21)

```
NAME:     a(n) = 2*phi(n-2)-(n-1).
OFFSET:   3
TERMS:    0,-1,0,-1,2,-3,4,-1,2,-3,8,-5,10,-3,0,-1,14,-7,16,-5,...
AUTHOR:   Benoit Cloitre, Sep 15 2002
COMMENT (the conjecture, unsigned, hence by the author Benoit Cloitre,
         Sep 15 2002):
  Conjecture : a(n)=0 if and only if n is a Fermat prime (A019434).
COMMENT (later, refuting):
  The conjecture appears to be false, a(83623937)=0 and 83623937 is not a
  Fermat number (A000215). See A232720 for sequence of n such that a(n)=0.
  - _Michel Marcus_, Nov 28 2013
```

No later comment retracts Marcus's refutation.

## Status

**False.** This module refutes the conjecture at `n = 83623937`, the
witness of Marcus's comment.  Here `n` is prime, `n - 1 = 2^18 * 11 * 29`
is not a power of two (so `n` is not a Fermat number), and
`n - 2 = 83623935 = 3 * 5 * 17 * 353 * 929` with
`φ(n - 2) = 2 * 4 * 16 * 352 * 928 = 41811968 = (n - 1) / 2`.

A second witness, recorded as a theorem below, is `n = F_5 = 4294967297`:
`φ(F_5 - 2) = φ(3 * 5 * 17 * 257 * 65537) = 2^31`, so `a(F_5) = 0`, but
`F_5 = 641 * 6700417` is composite.

Computational evidence (Sage, 2026-10-21): the zeros of `a` with
`3 ≤ n < 10^6` are exactly `3, 5, 17, 257, 65537`, the known Fermat
primes; both witnesses above satisfy `a(n) = 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A074057Refutation

/-- OEIS A074057, `a(n) = 2*phi(n-2) - (n-1)`, valued in `ℤ` (the sequence
is signed).  The entry has offset `3`; the natural subtraction `n - 2` is
off its junk value exactly in that range, which `Conjecture` guards. -/
def a (n : ℕ) : ℤ := 2 * (Nat.totient (n - 2) : ℤ) - ((n : ℤ) - 1)

/-- A Fermat prime (OEIS A019434): a prime of the form `2^(2^k) + 1`. -/
def IsFermatPrime (n : ℕ) : Prop := n.Prime ∧ ∃ k : ℕ, n = Nat.fermatNumber k

/-! ## Ground truth -/

-- The first twelve listed terms `a(3), …, a(14)`.
example : [a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14] =
    [0, -1, 0, -1, 2, -3, 4, -1, 2, -3, 8, -5] := by decide

/-! ## The conjecture -/

/-- **Cloitre's conjecture (A074057, Sep 15 2002).**  Verbatim:
"Conjecture : a(n)=0 if and only if n is a Fermat prime (A019434)."
Quantified over the entry's range `3 ≤ n`. -/
def Conjecture : Prop := ∀ n : ℕ, 3 ≤ n → (a n = 0 ↔ IsFermatPrime n)

/-! ## Refutation -/

/-- `φ(83623935) = 41811968`, from `83623935 = 3 * 5 * 17 * 353 * 929`. -/
theorem totient_83623935 : Nat.totient 83623935 = 41811968 := by
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  have h353 : Nat.Prime 353 := by norm_num
  have h929 : Nat.Prime 929 := by norm_num
  have hfac : (83623935 : ℕ) = 3 * (5 * (17 * (353 * 929))) := by norm_num
  rw [hfac, Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_prime h3, Nat.totient_prime h5, Nat.totient_prime h17,
    Nat.totient_prime h353, Nat.totient_prime h929]

/-- `a(83623937) = 0`. -/
theorem a_83623937 : a 83623937 = 0 := by
  have hsub : (83623937 - 2 : ℕ) = 83623935 := by norm_num
  rw [a, hsub, totient_83623935]
  norm_num

/-- `83623937` is not a Fermat number: `83623937 - 1` is divisible by `11`,
while `2^(2^k)` is not. -/
theorem not_fermatNumber_83623937 (k : ℕ) : 83623937 ≠ Nat.fermatNumber k := by
  intro hk
  have hpow : (83623936 : ℕ) = 2 ^ (2 ^ k) := by
    rw [Nat.fermatNumber] at hk
    omega
  have hdvd : 11 ∣ 2 ^ (2 ^ k) := by
    rw [← hpow]
    norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h11two : 11 ∣ 2 := h11.dvd_of_dvd_pow hdvd
  omega

/-- Satisfiability of the conjecture's iff on its intended side: `17` is a
Fermat prime and `a(17) = 0`, so the statement is not vacuous. -/
example : a 17 = 0 ∧ IsFermatPrime 17 :=
  ⟨by decide, by norm_num, 2, by norm_num [Nat.fermatNumber]⟩

/-- **The conjecture is false.**  Counterexample `n = 83623937` (Michel
Marcus, Nov 28 2013): `a(83623937) = 0` and `83623937` is prime, but it is
not a Fermat number.  The zeros of `a` are exactly the `n ≥ 3` with
`2 φ(n-2) = n-1` (OEIS A232720), a strictly larger set than the Fermat
primes.  No corrected iff is evident: even the direction "Fermat prime ⇒
`a(n) = 0`" for a hypothetical Fermat prime `F_k`, `k ≥ 6`, would fail
(`F_5 ∣ F_k - 2` is composite), so that direction is equivalent to the
open problem that `F_0, …, F_4` are the only Fermat primes. -/
theorem a074057_conjecture_false : ¬ Conjecture := by
  intro hconj
  have hiff : a 83623937 = 0 ↔ IsFermatPrime 83623937 := hconj 83623937 (by norm_num)
  obtain ⟨_, k, hk⟩ := hiff.mp a_83623937
  exact not_fermatNumber_83623937 k hk

/-- Second witness: `F_5 = 2^32 + 1` satisfies `a(F_5) = 0`, since
`F_5 - 2 = 3 * 5 * 17 * 257 * 65537` has totient `2^31`, yet `F_5` is
composite (`641 ∣ F_5`, Euler). -/
theorem a_fermatNumber_five_eq_zero_and_not_prime :
    a (Nat.fermatNumber 5) = 0 ∧ ¬ (Nat.fermatNumber 5).Prime := by
  have hF : Nat.fermatNumber 5 = 4294967297 := by norm_num [Nat.fermatNumber]
  rw [hF]
  constructor
  · have h3 : Nat.Prime 3 := by norm_num
    have h5 : Nat.Prime 5 := by norm_num
    have h17 : Nat.Prime 17 := by norm_num
    have h257 : Nat.Prime 257 := by norm_num
    have h65537 : Nat.Prime 65537 := by norm_num
    have hsub : (4294967297 - 2 : ℕ) = 3 * (5 * (17 * (257 * 65537))) := by norm_num
    rw [a, hsub, Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime h3, Nat.totient_prime h5, Nat.totient_prime h17,
      Nat.totient_prime h257, Nat.totient_prime h65537]
    norm_num
  · intro hprime
    have hdvd : 641 ∣ 4294967297 := by norm_num
    have h641 : 641 = 1 ∨ 641 = 4294967297 := (Nat.dvd_prime hprime).mp hdvd
    omega

end Candidates.A074057Refutation
