import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Squarefreeness of the middle binomial coefficient: bounded odd range

The statement uses only Mathlib's natural numbers, oddness, binomial coefficient,
and squarefreeness. Natural division by the fixed positive divisor `2` gives
`floor(n / 2)`. No project theorem or project-specific predicate is imported.
-/

set_option autoImplicit false

namespace Palomar.SquarefreeBinomialOddRange

/-- The hypotheses hold jointly at the first odd index above the lower bound. -/
example : Odd (73 : ℕ) ∧ 72 ≤ (73 : ℕ) ∧ (73 : ℕ) < 10 ^ 8 :=
  ⟨⟨36, rfl⟩, by decide, by decide⟩

example : (73 : ℕ) / 2 = 36 := rfl

/-- For every odd natural number `n` with `72 ≤ n < 10^8`, the middle
binomial coefficient `n.choose (n / 2)` is not squarefree. -/
theorem not_squarefree_choose_half_of_odd {n : ℕ} (hn : Odd n)
    (h72 : 72 ≤ n) (hlt : n < 10 ^ 8) : ¬ Squarefree (n.choose (n / 2)) := by
  sorry

#check @Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd

end Palomar.SquarefreeBinomialOddRange
