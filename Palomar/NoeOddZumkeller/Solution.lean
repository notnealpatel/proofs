import Enumerative.NoeZumkellerOdd

/-!
# Proof of Noe's odd-Zumkeller forward obstruction

This module repeats the Challenge declarations without importing the Challenge.
It bridges the literal package predicates to the existing proof in
`Enumerative.NoeZumkellerOdd`.
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

/-- The package Zumkeller predicate is literally the repository predicate. -/
theorem isZumkeller_iff_source (n : ℕ) :
    IsZumkeller n ↔ _root_.IsZumkeller n := Iff.rfl

/-- The package's literal A174865 condition agrees with the repository's
abundance/even-abundance formulation. -/
theorem isA174865_iff_source (n : ℕ) :
    IsA174865 n ↔ _root_.IsA174865 n := by
  rw [_root_.isA174865_iff]
  simp only [IsA174865, IsAbundant, even_iff_two_dvd]

/-- The forward assertion that every odd Zumkeller number satisfies the literal
A174865 condition is equivalent to the nonexistence of an odd perfect number. -/
theorem noeOddZumkellerForward_iff_not_exists_odd_perfect :
    (∀ n : ℕ, Odd n → IsZumkeller n → IsA174865 n) ↔
      ¬ ∃ n : ℕ, Odd n ∧ n.Perfect := by
  constructor
  · intro hforward
    apply _root_.noeOddZumkellerForward_iff_not_exists_odd_perfect.mp
    intro n hodd hzum
    apply (isA174865_iff_source n).mp
    exact hforward n hodd ((isZumkeller_iff_source n).mpr hzum)
  · intro hno n hodd hzum
    apply (isA174865_iff_source n).mpr
    apply _root_.noeOddZumkellerForward_iff_not_exists_odd_perfect.mpr hno n hodd
    exact (isZumkeller_iff_source n).mp hzum

/-- The local conditions are jointly inhabited at `945`; the universal
assertion is therefore not merely about an empty Zumkeller antecedent. -/
example : Odd 945 ∧ IsZumkeller 945 ∧ IsA174865 945 :=
  ⟨by decide, (isZumkeller_iff_source 945).mpr _root_.isZumkeller_945,
    (isA174865_iff_source 945).mpr _root_.isA174865_945⟩

/-- The strict/nondeficient boundary is genuine: the perfect number `6` is
Zumkeller and has even divisor sum, but it is not abundant. -/
example : (6 : ℕ).Perfect ∧ IsZumkeller 6 ∧
    Even (∑ d ∈ (6 : ℕ).divisors, d) ∧ ¬ IsAbundant 6 := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide⟩

#check @Palomar.NoeOddZumkeller.noeOddZumkellerForward_iff_not_exists_odd_perfect
#print axioms Palomar.NoeOddZumkeller.noeOddZumkellerForward_iff_not_exists_odd_perfect

end Palomar.NoeOddZumkeller
