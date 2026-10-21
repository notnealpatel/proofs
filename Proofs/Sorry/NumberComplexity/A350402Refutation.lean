/-
# A350402 — Gerasimov: terms of A350402 other than `2` lie in A094179

## OEIS source (retrieved with `oeis show A350402` and the live entry, 2026-10-21)

```
NAME:     Numbers k such that binomial(k, 2) divides binomial(2^k-2, 2).
TERMS:    2,3,7,11,19,31,43,127,163,211,271,311,331,379,487,571,631,811,883,
          991,1459,1471,1747,2311,2531,2647,2791,2971,3079,3631,3943,4091,...
AUTHOR:   Juri-Stepan Gerasimov, Dec 29 2021
COMMENT (the conjecture, unsigned, hence by the entry author):
  Conjecture: aside from the first term, this is a subsequence of A094179
  (numbers congruent to 3 mod 4 which are divisible only by primes congruent
  to 3 mod 4).
COMMENT (later, retracting it):
  The conjecture is false: a(2295) = 508606771 = 19531 * 26041 is not in
  A094179, nor even A004614. - _Charles R Greathouse IV_, Jan 22 2022
```

A094179: "Numbers congruent to 3 mod 4 which are divisible only by primes
congruent to 3 mod 4."  Terms: 3,7,11,19,23,27,31,43,47,59,63,...

## Status

**False** (already retracted in the entry by Greathouse).  This module gives a
kernel-checked refutation with the counterexample `k = 508606771`:

* `k = 19531 * 26041`, both factors prime, and `26041 ≡ 1 (mod 4)`;
* `binomial(k, 2) ∣ binomial(2^k - 2, 2)`, certified by fast modular
  exponentiation: `2^k ≡ 206944677598751738 (mod k (k - 1))`.

Note `k ≡ 3 (mod 4)`, so only the prime-factor clause fails.  Computation
(Python, exhaustive for `3 ≤ k < 3 * 10^6`) finds every term above `2` to be
`≡ 3 (mod 4)`; the residue clause of the conjecture is plausibly the intended
surviving content.  It is not addressed here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A350402Refutation

/-! ## Definition layer -/

/-- Membership in A350402: `2 ≤ k` and `binomial(k, 2) ∣ binomial(2^k - 2, 2)`.
The guard `2 ≤ k` matches the entry's offset (PARI: `isok(n) = (n>1) && ...`);
for `k ≥ 1` the truncated subtraction `2^k - 2` is the honest value. -/
def InA350402 (k : ℕ) : Prop :=
  2 ≤ k ∧ k.choose 2 ∣ (2 ^ k - 2).choose 2

/-- Membership in A094179: `k ≡ 3 (mod 4)` and every prime factor of `k` is
`≡ 3 (mod 4)`. -/
def InA094179 (k : ℕ) : Prop :=
  k % 4 = 3 ∧ ∀ p : ℕ, p.Prime → p ∣ k → p % 4 = 3

/-! ## Ground truth -/

-- `2` is the first term of A350402 (`binomial(2,2) = 1`).
example : InA350402 2 := ⟨le_refl 2, by decide⟩

-- `3`, `7`, `11` are the next terms of A350402.
example : InA350402 3 := ⟨by norm_num, by decide⟩
example : InA350402 7 :=
  ⟨by norm_num, by rw [Nat.choose_two_right, Nat.choose_two_right]; decide⟩
example : InA350402 11 :=
  ⟨by norm_num, by rw [Nat.choose_two_right, Nat.choose_two_right]; decide⟩

-- `5` is not a term: `binomial(5,2) = 10` does not divide `binomial(30,2) = 435`.
example : ¬ InA350402 5 := by
  rintro ⟨-, h⟩
  rw [Nat.choose_two_right, Nat.choose_two_right] at h
  revert h
  decide

-- `7` and `27 = 3^3` are terms of A094179.
example : InA094179 7 :=
  ⟨by norm_num, fun p hp hdvd => by
    rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd]⟩
example : InA094179 27 :=
  ⟨by norm_num, fun p hp hdvd => by
    have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (n := 3) (by norm_num [hdvd])
    rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3]⟩

-- `15 ≡ 3 (mod 4)` is not in A094179: its prime factor `5 ≡ 1 (mod 4)`.
example : ¬ InA094179 15 := fun h => by
  have h5 := h.2 5 (by norm_num) (by norm_num)
  norm_num at h5

/-! ## The conjecture -/

/-- **Gerasimov's conjecture (A350402, Juri-Stepan Gerasimov, Dec 29 2021).**

Verbatim: "Conjecture: aside from the first term, this is a subsequence of
A094179 (numbers congruent to 3 mod 4 which are divisible only by primes
congruent to 3 mod 4)."

Formally: every `k` in A350402 with `k ≠ 2` lies in A094179. -/
def Conjecture : Prop :=
  ∀ k : ℕ, InA350402 k → k ≠ 2 → InA094179 k

-- The hypothesis is jointly satisfiable: `3` is a term other than `2`.
example : InA350402 3 ∧ (3 : ℕ) ≠ 2 := ⟨⟨by norm_num, by decide⟩, by norm_num⟩

/-! ## Arithmetic bridge -/

/-- `binomial(a, 2) ∣ binomial(b, 2)` iff `a (a - 1) ∣ b (b - 1)`. -/
theorem choose_two_dvd_choose_two_iff (a b : ℕ) :
    a.choose 2 ∣ b.choose 2 ↔ a * (a - 1) ∣ b * (b - 1) := by
  have ha : a * (a - 1) = 2 * a.choose 2 := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self a).two_dvd]
  have hb : b * (b - 1) = 2 * b.choose 2 := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self b).two_dvd]
  rw [ha, hb]
  exact (Nat.mul_dvd_mul_iff_left two_pos).symm

/-! ## The counterexample `k = 508606771` -/

/-- `4 ≤ 2^k` for `2 ≤ k`. -/
theorem four_le_two_pow {k : ℕ} (hk : 2 ≤ k) : 4 ≤ 2 ^ k :=
  Nat.pow_le_pow_right (n := 2) (by norm_num) hk

/-- `26041` is prime. -/
theorem prime_26041 : Nat.Prime 26041 := by norm_num

/-- `19531` is prime. -/
theorem prime_19531 : Nat.Prime 19531 := by norm_num

/-- `508606771 = 19531 * 26041`. -/
theorem factor_508606771 : 508606771 = 19531 * 26041 := by norm_num

/-- `2^508606771 ≡ 206944677598751738 (mod 508606771 * 508606770)`, by fast
modular exponentiation (`reduce_mod_char`). -/
theorem two_pow_zmod :
    (2 : ZMod 258680846998439670) ^ 508606771 = 206944677598751738 := by
  reduce_mod_char

/-- `508606771` is a term of A350402: `binomial(k, 2) ∣ binomial(2^k - 2, 2)`. -/
theorem inA350402_508606771 : InA350402 508606771 := by
  refine ⟨by norm_num, ?_⟩
  rw [choose_two_dvd_choose_two_iff]
  have hm : (508606771 : ℕ) * (508606771 - 1) = 258680846998439670 := by norm_num
  rw [hm, ← ZMod.natCast_eq_zero_iff]
  -- Name the huge power so that no tactic tries to evaluate it.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 ^ 508606771 = N := ⟨_, rfl⟩
  rw [hN]
  have hcast : ((N : ℕ) : ZMod 258680846998439670) = 206944677598751738 := by
    rw [← hN, Nat.cast_pow, Nat.cast_ofNat, two_pow_zmod]
  have h4 : 4 ≤ N := hN ▸ four_le_two_pow (by norm_num)
  have h2 : 2 ≤ N := le_trans (by norm_num) h4
  have h3 : 1 ≤ N - 2 := Nat.le_sub_of_add_le (le_trans (by norm_num) h4)
  rw [Nat.cast_mul, Nat.cast_sub h3, Nat.cast_sub h2, hcast, Nat.cast_ofNat, Nat.cast_one]
  reduce_mod_char

/-- `508606771` is not in A094179: its prime factor `26041` is `≡ 1 (mod 4)`. -/
theorem not_inA094179_508606771 : ¬ InA094179 508606771 := fun h => by
  have h4 := h.2 26041 prime_26041 (by norm_num)
  norm_num at h4

/-- **Refutation of Gerasimov's conjecture (A350402).**  The term
`k = 508606771 = 19531 * 26041` (`a(2295)`, found by Greathouse) satisfies
`binomial(k, 2) ∣ binomial(2^k - 2, 2)` and `k ≠ 2`, but its prime factor
`26041 ≡ 1 (mod 4)` keeps it out of A094179.  The residue clause
`k ≡ 3 (mod 4)` still holds at this `k`. -/
theorem conjecture_false : ¬ Conjecture := fun h =>
  not_inA094179_508606771 (h 508606771 inA350402_508606771 (by norm_num))

end Candidates.A350402Refutation
