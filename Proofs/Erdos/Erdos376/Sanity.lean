import Erdos.Erdos376.DigitCriterion
import Erdos.Erdos376.DigitCertificates

/-!
# Small A030979 sanity instances

The digit certificates imply coprimality via the exact Kummer equivalence.
In particular, there is no need to evaluate `Nat.centralBinom 20007`.
-/

set_option autoImplicit false

namespace Erdos376

/-- Every number in the displayed list of small A030979 entries has central
binomial coefficient coprime to `105`. This is a finite membership certificate,
not a completeness or infinitude claim. -/
theorem small_a030979_coprime_certificates :
    ∀ n ∈ ([0, 1, 10, 756, 757, 3160, 3186, 3187, 3250, 7560, 7561, 7651, 20007] :
      List ℕ), Nat.Coprime (Nat.centralBinom n) 105 := by
  intro n hn
  exact (coprime_105_iff_digits n).mpr (small_a030979_digit_certificates n hn)

/-- The integer `2` is not an A030979 term: its base-three digit `2` violates
the criterion, so `C(4,2)` is not coprime to `105`. -/
theorem not_coprime_105_two : ¬ Nat.Coprime (Nat.centralBinom 2) 105 := by
  intro hcoprime
  exact not_digits_three_two ((coprime_105_iff_digits 2).mp hcoprime).1

/-- The positive certificate has nonzero instances with nonempty digit lists. -/
example : Nat.Coprime (Nat.centralBinom 756) 105 ∧
    Nat.Coprime (Nat.centralBinom 757) 105 := by
  constructor
  · exact small_a030979_coprime_certificates 756 (by decide)
  · exact small_a030979_coprime_certificates 757 (by decide)

/-- Independent arithmetic checks at the zero boundary and the smallest
excluded positive integer agree with the digit-based certificates. -/
example : Nat.centralBinom 0 = 1 ∧ Nat.centralBinom 2 = 6 ∧
    Nat.gcd (Nat.centralBinom 2) 105 = 3 := by decide

/-- An incoming carry cannot be ignored: even at an allowed digit of an odd
prime base, adding one can reach the base. The no-carry proof instead propagates
incoming carry zero from the units place. -/
example : Nat.Prime 3 ∧ Odd (3 : ℕ) ∧ 2 * (1 : ℕ) < 3 ∧
    ¬ (2 * (1 : ℕ) + 1 < 3) := by decide

end Erdos376

#check @Erdos376.small_a030979_coprime_certificates
#check @Erdos376.not_coprime_105_two
#print axioms Erdos376.small_a030979_coprime_certificates
#print axioms Erdos376.not_coprime_105_two
