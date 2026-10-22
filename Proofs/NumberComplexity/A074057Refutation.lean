/-
# A074057 — Cloitre: `2 φ(n-2) = n-1` iff `n` is a Fermat prime

OEIS A074057, Benoit Cloitre: `a(n) = 2φ(n-2) - (n-1)`, offset `3`.
Michel Marcus's counterexample is `n = 83623937`: `a(n) = 0`, but `n`
is not a Fermat number. Here `φ(83623935) = 41811968`.
A second witness is the composite Fermat number `F_5 = 4294967297`.
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

/-! ## Examples -/

-- The first twelve listed terms `a(3), …, a(14)`.
example : [a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14] =
    [0, -1, 0, -1, 2, -3, 4, -1, 2, -3, 8, -5] := by decide

/-! ## The conjecture -/

/-- Cloitre’s conjecture (A074057): for `3 ≤ n` (the entry’s offset),
`a(n) = 0` iff `n` is a Fermat prime (A019434). -/
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

/-- Marcus’s counterexample to Cloitre’s conjecture (A074057):
`a(83623937) = 0`, but `83623937` is not a Fermat number.
The zeros are the `n ≥ 3` satisfying `2φ(n-2) = n-1` (A232720);
the module does not give a classification of those zeros. -/
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
