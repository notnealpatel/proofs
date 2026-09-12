import Erdos.Erdos175.KummerDigits

/-!
# The digit criterion for Erdős #376 / OEIS A030979

The single-prime Kummer bridge is already proved in
`Erdos175.prime_not_dvd_centralBinom_iff_digits`, for every prime (not only odd
primes). This file specializes that bridge to coprimality with `105 = 3 * 5 * 7`.
It makes no infinitude assertion. See `README.md` for live-source reconciliation.
-/

set_option autoImplicit false

namespace Erdos376

/-- For a prime `p`, `C(2n,n)` is coprime to `p` exactly when every base-`p`
digit `d` of `n` satisfies `2 * d < p`. In particular this holds for odd primes;
oddness is unnecessary in the existing Kummer bridge. -/
theorem coprime_centralBinom_prime_iff_digits {p n : ℕ} (hp : p.Prime) :
    Nat.Coprime (Nat.centralBinom n) p ↔ ∀ d ∈ Nat.digits p n, 2 * d < p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd,
    Erdos175.prime_not_dvd_centralBinom_iff_digits hp]

/-- `C(2n,n)` is coprime to `105` exactly when the base-three digits of `n`
are in `{0,1}`, its base-five digits are in `{0,1,2}`, and its base-seven digits
are in `{0,1,2,3}`. This is a pointwise equivalence, including `n = 0`. -/
theorem coprime_105_iff_digits (n : ℕ) :
    Nat.Coprime (Nat.centralBinom n) 105 ↔
      (∀ d ∈ Nat.digits 3 n, d < 2) ∧
      (∀ d ∈ Nat.digits 5 n, d < 3) ∧
      (∀ d ∈ Nat.digits 7 n, d < 4) := by
  have h105 : 105 = 3 * (5 * 7) := rfl
  rw [h105, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right,
    coprime_centralBinom_prime_iff_digits Nat.prime_three,
    coprime_centralBinom_prime_iff_digits (by decide : Nat.Prime 5),
    coprime_centralBinom_prime_iff_digits (by decide : Nat.Prime 7)]
  have h3 : ∀ d : ℕ, 2 * d < 3 ↔ d < 2 := by omega
  have h5 : ∀ d : ℕ, 2 * d < 5 ↔ d < 3 := by omega
  have h7 : ∀ d : ℕ, 2 * d < 7 ↔ d < 4 := by omega
  simp only [h3, h5, h7]

/-- Joint satisfiability at an odd prime and a positive A030979 term: the
base-three digit list is nonempty, and the central binomial coefficient is
coprime to three. -/
example : Nat.Prime 3 ∧ Odd (3 : ℕ) ∧ Nat.digits 3 10 = [1, 0, 1] ∧
    Nat.Coprime (Nat.centralBinom 10) 3 := by
  refine ⟨Nat.prime_three, by decide, by decide, ?_⟩
  exact (coprime_centralBinom_prime_iff_digits Nat.prime_three).mpr (by decide)

/-- Zero has an empty digit list in each relevant base, and `C(0,0) = 1` is
coprime to `105`; the vacuous digit condition at zero is intentional. -/
example : Nat.digits 3 0 = [] ∧ Nat.digits 5 0 = [] ∧ Nat.digits 7 0 = [] ∧
    Nat.centralBinom 0 = 1 ∧ Nat.Coprime (Nat.centralBinom 0) 105 := by decide

/-- The imported single-prime bridge also covers the smallest prime: zero
passes the binary digit condition, whereas one does not. -/
example : Nat.Prime 2 ∧ ¬ (2 ∣ Nat.centralBinom 0) ∧
    (2 ∣ Nat.centralBinom 1) ∧ Nat.digits 2 1 = [1] := by decide

end Erdos376

#check @Erdos175.prime_not_dvd_centralBinom_iff_digits
#check @Erdos376.coprime_centralBinom_prime_iff_digits
#check @Erdos376.coprime_105_iff_digits
#print axioms Erdos175.prime_not_dvd_centralBinom_iff_digits
#print axioms Erdos376.coprime_centralBinom_prime_iff_digits
#print axioms Erdos376.coprime_105_iff_digits
