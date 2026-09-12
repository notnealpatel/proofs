import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Kernel-checked digit certificates for small A030979 entries

These finite checks use `decide` on short digit lists, not on the large central
binomial coefficients. Keeping the computations here lets downstream uses of
the Kummer bridge reuse this module's compiled proofs.
-/

set_option autoImplicit false

namespace Erdos376

/-- Each of the first thirteen entries returned by the live A030979 query
satisfies the three digit bounds. This certifies membership only, not that the
list exhausts all solutions in an interval. -/
theorem small_a030979_digit_certificates :
    ∀ n ∈ ([0, 1, 10, 756, 757, 3160, 3186, 3187, 3250, 7560, 7561, 7651, 20007] :
      List ℕ),
      (∀ d ∈ Nat.digits 3 n, d < 2) ∧
      (∀ d ∈ Nat.digits 5 n, d < 3) ∧
      (∀ d ∈ Nat.digits 7 n, d < 4) := by decide

/-- The numeral `756` has ternary expansion `(1001000)₃`, with the least
significant digit first in `Nat.digits`. This corrects the scratch prose. -/
theorem digits_three_756 : Nat.digits 3 756 = [0, 0, 0, 1, 0, 0, 1] := by decide

/-- The small nonterm `2` fails the base-three digit bound. -/
theorem not_digits_three_two : ¬ (∀ d ∈ Nat.digits 3 2, d < 2) := by decide

end Erdos376

#print axioms Erdos376.small_a030979_digit_certificates
#print axioms Erdos376.digits_three_756
#print axioms Erdos376.not_digits_three_two
