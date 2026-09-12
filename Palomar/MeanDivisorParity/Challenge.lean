import Palomar.MeanDivisorParity.Definitions

/-!
# Mean-divisor subset parity

For `n : ℕ`, `a n` counts the nonempty subsets of `{1, ..., n}` whose
arithmetic mean is an integer dividing `n`.  The mean is expressed by
`S.sum id = m * S.card`, so no totalized natural-number division occurs.
The selected results compare the parity of this literal count with the number
of divisors, characterize odd values at nonzero inputs by perfect squares, and
record the prime case.
-/

set_option autoImplicit false

open Finset

namespace Palomar.MeanDivisorParity

/-- The mean-divisor subset count is congruent modulo two to the divisor count. -/
theorem a_modEq_card_divisors (n : ℕ) : a n ≡ n.divisors.card [MOD 2] := by
  sorry

/-- At a nonzero input, the mean-divisor subset count is odd exactly for a square. -/
theorem odd_a_iff_isSquare {n : ℕ} (hn : n ≠ 0) : Odd (a n) ↔ IsSquare n := by
  sorry

/-- The mean-divisor subset count equals two exactly at prime inputs. -/
theorem a_eq_two_iff_prime (n : ℕ) : a n = 2 ↔ n.Prime := by
  sorry

example : a 6 % 2 = (Nat.divisors 6).card % 2 := by decide
example : Odd (a 4) ∧ IsSquare (4 : ℕ) := ⟨⟨2, by decide⟩, ⟨2, by decide⟩⟩
example : a 5 = 2 ∧ (5 : ℕ).Prime := ⟨by decide, by decide⟩

#check @a_modEq_card_divisors
#check @odd_a_iff_isSquare
#check @a_eq_two_iff_prime

end Palomar.MeanDivisorParity
