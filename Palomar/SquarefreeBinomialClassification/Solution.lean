import Erdos.Erdos175.SquarefreeCentralBinom

/-!
# Proved bridge for the complete bounded A046098 classification

This module does not import the Challenge. It restates the same theorem with
ordinary Mathlib constants and bridges directly to the repository theorem
`Erdos175.A046098.squarefree_choose_half_iff`. The source bound is retained
unchanged.
-/

set_option autoImplicit false

namespace Palomar.SquarefreeBinomialClassification

/-- The bounded quantifier has concrete witnesses, including both endpoints of
the listed range. The value `10^8` itself is excluded by the strict bound. -/
example : (0 : ℕ) < 10 ^ 8 ∧ (71 : ℕ) < 10 ^ 8 ∧
    (99999999 : ℕ) < 10 ^ 8 ∧ ¬ (100000000 : ℕ) < 10 ^ 8 := by
  decide

/-- The finite set contains `0` and `71`, but excludes the next index `72`. -/
example : (0 : ℕ) ∈ ({0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71} : Finset ℕ) ∧
    (71 : ℕ) ∈ ({0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71} : Finset ℕ) ∧
    (72 : ℕ) ∉ ({0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71} : Finset ℕ) := by
  decide

/-- For every natural number `n < 10^8`, the middle binomial coefficient
`C(n, floor(n/2))` is squarefree exactly at the thirteen displayed indices. -/
theorem squarefree_choose_half_iff {n : Nat} (hlt : n < 10^8) :
    Squarefree (n.choose (n/2)) ↔
      n ∈ ({0,1,2,3,4,5,7,8,11,17,19,23,71} : Finset Nat) := by
  exact Erdos175.A046098.squarefree_choose_half_iff hlt

#check @Palomar.SquarefreeBinomialClassification.squarefree_choose_half_iff
#print axioms Palomar.SquarefreeBinomialClassification.squarefree_choose_half_iff

end Palomar.SquarefreeBinomialClassification
