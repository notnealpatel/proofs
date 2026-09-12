import Palomar.MeanDivisorParity.Definitions
import Enumerative.MeanDivisors

/-!
# Mean-divisor subset parity

This module imports the declarations shared with
`Palomar.MeanDivisorParity.Challenge` without importing that module. The proofs
transport the declarations already established in `Enumerative.MeanDivisors`.
-/

set_option autoImplicit false

open Finset

namespace Palomar.MeanDivisorParity

private lemma meanDivSubsets_eq_source (n : ℕ) :
    meanDivSubsets n = A114976.meanDivSubsets n := by
  unfold meanDivSubsets A114976.meanDivSubsets
  apply Finset.filter_congr
  intro S hS
  rfl

private lemma a_eq_source (n : ℕ) : a n = A114976.a n := by
  rw [a, A114976.a, meanDivSubsets_eq_source]

/-- The mean-divisor subset count is congruent modulo two to the divisor count. -/
theorem a_modEq_card_divisors (n : ℕ) : a n ≡ n.divisors.card [MOD 2] := by
  rw [a_eq_source]
  exact A114976.a_modEq_card_divisors n

/-- At a nonzero input, the mean-divisor subset count is odd exactly for a square. -/
theorem odd_a_iff_isSquare {n : ℕ} (hn : n ≠ 0) : Odd (a n) ↔ IsSquare n := by
  rw [a_eq_source]
  exact A114976.odd_a_iff_isSquare hn

/-- The mean-divisor subset count equals two exactly at prime inputs. -/
theorem a_eq_two_iff_prime (n : ℕ) : a n = 2 ↔ n.Prime := by
  rw [a_eq_source]
  exact A114976.a_eq_two_iff_prime n

example : a 6 % 2 = (Nat.divisors 6).card % 2 := by decide
example : Odd (a 4) ∧ IsSquare (4 : ℕ) := ⟨⟨2, by decide⟩, ⟨2, by decide⟩⟩
example : a 5 = 2 ∧ (5 : ℕ).Prime := ⟨by decide, by decide⟩

#check @a_modEq_card_divisors
#check @odd_a_iff_isSquare
#check @a_eq_two_iff_prime
#print axioms Palomar.MeanDivisorParity.a_modEq_card_divisors
#print axioms Palomar.MeanDivisorParity.odd_a_iff_isSquare
#print axioms Palomar.MeanDivisorParity.a_eq_two_iff_prime

end Palomar.MeanDivisorParity
