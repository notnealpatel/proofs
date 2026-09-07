import Enumerative.CongruentBSD

/-!
# A concrete primitive congruent number: 21

The selected statement repeats the Mathlib-only Challenge statement without
importing the Challenge. Its proof unfolds the source predicate and applies
the unconditional certificate for the triangle `(7/2, 12, 25/2)`.
-/

set_option autoImplicit false

namespace Palomar.CongruentTwentyOne

example : Nonempty ℚ := ⟨0⟩

/-- `21` is squarefree and is the area of a right triangle with three positive
rational sides, so it is a primitive congruent number. -/
theorem isPrimitiveCongruent_twentyOne :
    Squarefree (21 : ℕ) ∧
      ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧
        a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * (21 : ℚ) := by
  change A273929.IsPrimitiveCongruent 21
  exact A273929.isPrimitiveCongruent_twentyOne

#check @Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne
#print axioms Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne

end Palomar.CongruentTwentyOne
