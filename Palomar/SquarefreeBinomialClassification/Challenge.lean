import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Complete bounded classification for A046098

For every natural number `n` strictly below `10^8`, this module states exactly
when the middle binomial coefficient `n.choose (n / 2)` is squarefree. Natural
number division by `2` is floor division. The statement uses only ordinary
Mathlib notions; it has no package-defined mathematics or certificate
hypotheses. The bound is part of the claim, and no unbounded classification is
asserted.
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
  sorry

#check @Palomar.SquarefreeBinomialClassification.squarefree_choose_half_iff

end Palomar.SquarefreeBinomialClassification
