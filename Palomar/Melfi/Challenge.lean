import Mathlib.NumberTheory.Divisors

/-!
# Melfi's theorem on sums of practical numbers

A positive natural number is *practical* when every natural number up to it is a
sum of distinct positive divisors.  The finite set below enforces distinctness,
and membership in `n.divisors.powerset` says that every chosen term is a divisor
of `n`.

The headline is Giuseppe Melfi's theorem that every positive even natural number
is a sum of two practical numbers.  Positivity is explicit because zero is even
but cannot be such a sum.
-/

set_option autoImplicit false

namespace Palomar.Melfi

/-- A natural number is practical when it is positive and every natural number
at most it is a sum of a finite subset of its positive divisors. -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ≤ n, ∃ S ∈ n.divisors.powerset, ∑ d ∈ S, d = m

/-- Practicality is decidable because both quantifiers range over finite sets. -/
instance decidablePredPractical : DecidablePred Practical := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ ∀ m ≤ n, ∃ S ∈ n.divisors.powerset,
    ∑ d ∈ S, d = m))

example : Practical 1 := by decide
example : Practical 2 := by decide
example : Practical 6 := by decide
example : ¬ Practical 0 := by decide
example : ¬ Practical 3 := by decide

/-- Every positive even natural number is a sum of two practical numbers. -/
theorem even_eq_practical_add_practical {n : ℕ} (heven : Even n) (hn : 0 < n) :
    ∃ q r : ℕ, Practical q ∧ Practical r ∧ q + r = n := by
  sorry

-- The hypotheses and conclusion are jointly satisfiable at the first positive even input.
example : Even 2 ∧ 0 < (2 : ℕ) ∧
    ∃ q r : ℕ, Practical q ∧ Practical r ∧ q + r = 2 := by
  refine ⟨by decide, by decide, 1, 1, by decide, by decide, rfl⟩

#check @even_eq_practical_add_practical

end Palomar.Melfi
