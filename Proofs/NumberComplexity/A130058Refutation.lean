/-
# A130058 — Adamchuk: non-squarefree terms of A073631 are multiples of 23^2 (refuted)

Alexander Adamchuk's conjectures in OEIS A130058 and A073631 assert that
all nonsquarefree nonprimes `k` dividing `3^(k-1)-2^(k-1)` are multiples of
`23²`, and that the only square terms are `1` and `529`.

This module refutes both claims.  `q = 3842760169` is the second Wieferich
prime to base `3/2` (A376896: 23, 3842760169, 41975417117), i.e.
`q^2 ∣ 3^(q-1) - 2^(q-1)`.  Raising to the power `q + 1` shows that
`n = q^2 = 14766805716452908561` satisfies `n ∣ 3^(n-1) - 2^(n-1)`.
So `n` is a nonprime, non-squarefree, perfect-square term of A073631, yet
`n % 529 = 349`.  The membership is checked here directly by modular
exponentiation (`reduce_mod_char`) with modulus `n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A130058Refutation

/-! ## Definitions -/

/-- Membership in A073631: `k` is a positive nonprime with
`k ∣ 3^(k-1) - 2^(k-1)`.  The difference is taken in `ℤ`, and the guard
`0 < k` keeps the truncated exponent `k - 1` off its junk value. -/
def InA073631 (k : ℕ) : Prop :=
  0 < k ∧ ¬ k.Prime ∧ (k : ℤ) ∣ (3 : ℤ) ^ (k - 1) - 2 ^ (k - 1)

/-- Membership in A130058: `m` is positive and `k = m * 23^2` divides
`3^(k-1) - 2^(k-1)` (difference in `ℤ`). -/
def InA130058 (m : ℕ) : Prop :=
  0 < m ∧ ((m * 23 ^ 2 : ℕ) : ℤ) ∣ (3 : ℤ) ^ (m * 23 ^ 2 - 1) - 2 ^ (m * 23 ^ 2 - 1)

/-- Bridge: the divisibility `k ∣ 3^e - 2^e` in `ℤ` is the equality
`3^e = 2^e` in `ZMod k`. -/
theorem dvd_three_pow_sub_two_pow_iff (k e : ℕ) :
    (k : ℤ) ∣ (3 : ℤ) ^ e - 2 ^ e ↔ (3 : ZMod k) ^ e = 2 ^ e := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow, Int.cast_pow,
    Int.cast_ofNat, Int.cast_ofNat, sub_eq_zero]

/-! ### Examples against the listed terms -/

example : InA073631 1 := ⟨by norm_num, by norm_num, by norm_num⟩

example : InA073631 65 :=
  ⟨by norm_num, by norm_num, (dvd_three_pow_sub_two_pow_iff 65 _).mpr (by reduce_mod_char)⟩

example : InA073631 529 :=
  ⟨by norm_num, by norm_num, (dvd_three_pow_sub_two_pow_iff 529 _).mpr (by reduce_mod_char)⟩

/-- `5` is excluded from A073631 because it is prime. -/
example : ¬ InA073631 5 := fun h => h.2.1 (by norm_num)

/-- `25` is excluded from A073631 since `25 ∤ 3^24 - 2^24`. -/
example : ¬ InA073631 25 := fun h =>
  absurd ((dvd_three_pow_sub_two_pow_iff 25 _).mp h.2.2) (by reduce_mod_char; decide)

example : InA130058 1 :=
  ⟨by norm_num, (dvd_three_pow_sub_two_pow_iff _ _).mpr (by reduce_mod_char)⟩

example : InA130058 67 :=
  ⟨by norm_num, (dvd_three_pow_sub_two_pow_iff _ _).mpr (by reduce_mod_char)⟩

/-- `2` is not a term of A130058 (the second listed term is `67`). -/
example : ¬ InA130058 2 := fun h =>
  absurd ((dvd_three_pow_sub_two_pow_iff _ _).mp h.2) (by reduce_mod_char; decide)

/-! ## The conjectures -/

/-- **Adamchuk's conjecture (A130058 and A073631).**
"Conjecture: All nonsquarefree terms of A073631 are the multiples
of 23^2." -/
def Conjecture : Prop :=
  ∀ k : ℕ, InA073631 k → ¬ Squarefree k → 23 ^ 2 ∣ k

/-- **Adamchuk's squares remark (A073631).**
"It appears that a(1) = 1 and a(4) = 529 = 23^2 are the only perfect
squares in a(n)." -/
def SquaresConjecture : Prop :=
  ∀ k : ℕ, InA073631 k → IsSquare k → k = 1 ∨ k = 529

/-! ## The counterexample `n = 3842760169^2` -/

/-- `q = 3842760169` is a Wieferich prime to base `3/2`:
`3^(q-1) ≡ 2^(q-1) (mod q^2)`. -/
theorem wieferich_three_two_3842760169 :
    ((3842760169 ^ 2 : ℕ) : ℤ) ∣ (3 : ℤ) ^ (3842760169 - 1) - 2 ^ (3842760169 - 1) :=
  (dvd_three_pow_sub_two_pow_iff _ _).mpr (by reduce_mod_char)

/-- `n = 3842760169^2 = 14766805716452908561` is a term of A073631. -/
theorem inA073631_counterexample : InA073631 14766805716452908561 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · have hn : (14766805716452908561 : ℕ) = 3842760169 * 3842760169 := by norm_num
    rw [hn]
    exact Nat.not_prime_mul (by norm_num) (by norm_num)
  · exact (dvd_three_pow_sub_two_pow_iff _ _).mpr (by reduce_mod_char)

/-- `n = 3842760169^2` is not squarefree. -/
theorem not_squarefree_counterexample : ¬ Squarefree 14766805716452908561 := by
  intro hsq
  have hunit : IsUnit (3842760169 : ℕ) := hsq 3842760169 (by norm_num)
  rw [Nat.isUnit_iff] at hunit
  norm_num at hunit

/-- `n = 3842760169^2` is not divisible by `23^2 = 529` (`n % 529 = 349`). -/
theorem not_dvd_counterexample : ¬ (23 ^ 2 ∣ 14766805716452908561) := by
  norm_num

/-- **Refutation.** `n = 3842760169^2 = 14766805716452908561` is a nonprime,
non-squarefree term of A073631 that is not a multiple of `23^2`.  The
structural reason: if `p^2` divides a term `k`, then `p` is a base-`3/2`
Wieferich prime, and the second such prime `3842760169` (A376896) gives a
term outside the multiples of `23^2`. -/
theorem conjecture_false : ¬ Conjecture := fun h =>
  not_dvd_counterexample
    (h _ inA073631_counterexample not_squarefree_counterexample)

/-- **Refutation of the squares remark.** `n = 3842760169^2` is a perfect
square term of A073631 different from `1` and `529`. -/
theorem squaresConjecture_false : ¬ SquaresConjecture := fun h => by
  have hsq : IsSquare (14766805716452908561 : ℕ) := ⟨3842760169, by norm_num⟩
  rcases h _ inA073631_counterexample hsq with h1 | h529
  · norm_num at h1
  · norm_num at h529

end Candidates.A130058Refutation
