import Erdos.Erdos175.SquarefreeCentralBinom

/-!
# Squarefreeness of the middle binomial coefficient: bounded odd range

This file does not import the Challenge. Its statement uses the same Mathlib
constants and applies only the repository's bounded odd-range theorem. In
particular it does not apply the combined Noe theorem or its even branch.
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
  exact Erdos175.A046098.not_squarefree_choose_half_of_odd hn h72 hlt

#check @Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd
#print axioms Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd

end Palomar.SquarefreeBinomialOddRange
