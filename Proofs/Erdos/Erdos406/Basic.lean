/-
Erdős problem 406 asks whether only finitely many powers of two have no digit
`2` in base three.  This file does not claim that open conjecture.

OEIS A351928 is related but different: its `n`-th term is the least positive
exponent whose power of two has no `2` among its last `n` ternary digits (and
has at least `n` ternary digits).  It is not the set of exponents occurring in
Erdős 406.
-/

import Erdos.Erdos175.KummerDigits

set_option autoImplicit false

namespace Erdos406

/-- `ZeroOneBase3 m` means that every digit in the standard base-three
expansion of `m` is either zero or one. -/
def ZeroOneBase3 (m : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 3 m, d ≤ 1

instance (m : ℕ) : Decidable (ZeroOneBase3 m) := by
  unfold ZeroOneBase3
  infer_instance

/-- Ground truth for the definition: `4 = (11)₃`. -/
example : ZeroOneBase3 4 := by decide

/-- Ground truth for the definition: `16 = (121)₃` contains a digit two. -/
example : ¬ ZeroOneBase3 16 := by decide

/-- Boundary behavior: Mathlib represents zero by the empty digit list, so
`ZeroOneBase3 0` holds vacuously. -/
example : Nat.digits 3 0 = [] ∧ ZeroOneBase3 0 := by decide

/-- The three known powers of two with only zero and one as ternary digits are
`2⁰ = 1`, `2² = 4 = (11)₃`, and `2⁸ = 256 = (100111)₃`. -/
theorem known_witnesses :
    ZeroOneBase3 (2 ^ 0) ∧ ZeroOneBase3 (2 ^ 2) ∧ ZeroOneBase3 (2 ^ 8) := by
  decide

/-- Explicit small nonexamples: the powers with exponents `1, 3, 4, 5, 6, 7`
each contain a ternary digit two. -/
theorem small_nonexamples :
    ¬ ZeroOneBase3 (2 ^ 1) ∧
    ¬ ZeroOneBase3 (2 ^ 3) ∧
    ¬ ZeroOneBase3 (2 ^ 4) ∧
    ¬ ZeroOneBase3 (2 ^ 5) ∧
    ¬ ZeroOneBase3 (2 ^ 6) ∧
    ¬ ZeroOneBase3 (2 ^ 7) := by
  decide

/-- For base three, the existing Kummer digit criterion says exactly that a
central binomial coefficient is prime to three when its index has only zero
and one as ternary digits. -/
theorem three_not_dvd_centralBinom_iff_zeroOneBase3 (m : ℕ) :
    ¬ 3 ∣ Nat.centralBinom m ↔ ZeroOneBase3 m := by
  rw [Erdos175.prime_not_dvd_centralBinom_iff_digits Nat.prime_three]
  constructor
  · intro h d hd
    have hdigit := h d hd
    omega
  · intro h d hd
    have hdigit := h d hd
    omega

/-- Honest conditional consequence of Erdős 406: if the set of exceptional
exponents is finite, then eventually `3` divides
`C(2^(k+1), 2^k) = centralBinom (2^k)`. -/
theorem eventually_three_dvd_centralBinom_of_finite
    (hfinite : {k : ℕ | ZeroOneBase3 (2 ^ k)}.Finite) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 3 ∣ Nat.centralBinom (2 ^ k) := by
  obtain ⟨M, hM⟩ := hfinite.exists_le
  refine ⟨M + 1, fun k hk => ?_⟩
  by_contra hnot
  have hzeroOne : ZeroOneBase3 (2 ^ k) :=
    (three_not_dvd_centralBinom_iff_zeroOneBase3 (2 ^ k)).mp hnot
  have hle : k ≤ M := hM k hzeroOne
  omega

/-- The conditional conclusion has the exact binomial-coefficient form quoted
in Erdős 406. -/
theorem eventually_three_dvd_choose_of_finite
    (hfinite : {k : ℕ | ZeroOneBase3 (2 ^ k)}.Finite) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 3 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
  obtain ⟨K, hK⟩ := eventually_three_dvd_centralBinom_of_finite hfinite
  refine ⟨K, fun k hk => ?_⟩
  simpa [Nat.centralBinom_eq_two_mul_choose, pow_succ'] using hK k hk

end Erdos406

#print axioms Erdos406.known_witnesses
#print axioms Erdos406.small_nonexamples
#print axioms Erdos406.three_not_dvd_centralBinom_iff_zeroOneBase3
#print axioms Erdos406.eventually_three_dvd_centralBinom_of_finite
#print axioms Erdos406.eventually_three_dvd_choose_of_finite
