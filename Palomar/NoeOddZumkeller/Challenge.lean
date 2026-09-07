import Mathlib.NumberTheory.Divisors

/-!
# Noe's odd-Zumkeller forward assertion and the odd-perfect obstruction

A positive integer is Zumkeller when its positive divisors can be partitioned
into two parts having equal sums.  The A174865 condition used here is literal:
the integer is odd, its divisor sum is strictly greater than twice the integer,
and that divisor sum is even.

The selected theorem does not prove either side of its biconditional.  It says
that the universal forward assertion for odd Zumkeller numbers is equivalent to
the nonexistence of odd perfect numbers.  In particular, strict abundance is
not weakened to nondeficiency.
-/

set_option autoImplicit false

open Finset

namespace Palomar.NoeOddZumkeller

/-- A positive natural number is Zumkeller when a subset of its positive
divisors has the same sum as its complementary subset. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ A ∈ n.divisors.powerset,
    ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d

/-- Zumkeller membership is decidable because the subset witness ranges over
the finite powerset of the positive divisors. -/
instance decidablePredIsZumkeller : DecidablePred IsZumkeller := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ ∃ A ∈ n.divisors.powerset,
    ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d))

/-- Literal strict abundance in divisor-sum form: `2n < σ(n)`. -/
def IsAbundant (n : ℕ) : Prop :=
  2 * n < ∑ d ∈ n.divisors, d

/-- Literal abundance is decidable by finite divisor summation. -/
instance decidablePredIsAbundant : DecidablePred IsAbundant := fun n =>
  inferInstanceAs (Decidable (2 * n < ∑ d ∈ n.divisors, d))

/-- The A174865 condition: odd, strictly abundant, and with even divisor sum. -/
def IsA174865 (n : ℕ) : Prop :=
  Odd n ∧ IsAbundant n ∧ Even (∑ d ∈ n.divisors, d)

/-- A174865 membership is decidable. -/
instance decidablePredIsA174865 : DecidablePred IsA174865 := fun n =>
  inferInstanceAs (Decidable
    (Odd n ∧ IsAbundant n ∧ Even (∑ d ∈ n.divisors, d)))

example : IsZumkeller 6 := by decide
example : ¬ IsZumkeller 0 := by simp [IsZumkeller]
example : IsAbundant 12 := by decide
example : ¬ IsAbundant 6 := by decide
set_option maxRecDepth 100000 in
example : IsA174865 945 := by decide

/-- The forward assertion that every odd Zumkeller number satisfies the literal
A174865 condition is equivalent to the nonexistence of an odd perfect number. -/
theorem noeOddZumkellerForward_iff_not_exists_odd_perfect :
    (∀ n : ℕ, Odd n → IsZumkeller n → IsA174865 n) ↔
      ¬ ∃ n : ℕ, Odd n ∧ n.Perfect := by
  sorry

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The local conditions are jointly inhabited at `945`; the universal
assertion is therefore not merely about an empty Zumkeller antecedent. -/
example : Odd 945 ∧ IsZumkeller 945 ∧ IsA174865 945 := by
  refine ⟨by decide, ?_, by decide⟩
  refine ⟨by decide, {15, 945}, by decide, ?_⟩
  decide

/-- The strict/nondeficient boundary is genuine: the perfect number `6` is
Zumkeller and has even divisor sum, but it is not abundant. -/
example : (6 : ℕ).Perfect ∧ IsZumkeller 6 ∧
    Even (∑ d ∈ (6 : ℕ).divisors, d) ∧ ¬ IsAbundant 6 := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide⟩

#check @Palomar.NoeOddZumkeller.noeOddZumkellerForward_iff_not_exists_odd_perfect

end Palomar.NoeOddZumkeller
