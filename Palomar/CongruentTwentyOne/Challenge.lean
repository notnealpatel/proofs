import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Field.Rat

/-!
# A concrete primitive congruent number: 21

The selected statement is expanded using only Mathlib notions. It asks for
squarefreeness and positive rational sides of a right triangle of area 21.
It is not a general congruent-number criterion or a claim conditional on BSD.
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
  sorry

#check @Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne
#print axioms Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne

end Palomar.CongruentTwentyOne
