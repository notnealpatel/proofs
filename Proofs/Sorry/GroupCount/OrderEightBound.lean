import Sorry.GroupCount.HolderPQ

/-!
# The group-count bound up to order eight

The orders below eight have at most two isomorphism classes. Two explicit
nonisomorphic groups of order eight give the required lower bound, without
classifying all groups of order eight.
-/

set_option autoImplicit false

namespace GroupCount

/-- There are exactly two isomorphism classes of groups of order six. -/
theorem gnu_six : gnu 6 = 2 := by
  have h := gnu_mul_primes Nat.prime_two Nat.prime_three (by omega)
  simpa using h

/-- The cyclic group of order eight has two elements whose square is the identity. -/
theorem powOneCount_cyclic_eight_two :
    (GroupStructure.cyclic 8).powOneCount 2 = 2 := by decide

/-- The product of cyclic groups of orders four and two has four elements whose
square is the identity. -/
theorem powOneCount_cyclic_four_prod_cyclic_two_two :
    ((GroupStructure.cyclic 4).prod (GroupStructure.cyclic 2)).powOneCount 2 = 4 := by
  decide

/-- At least two isomorphism classes of groups have order eight, as witnessed by
`C₈` and `C₄ × C₂`, distinguished by their numbers of square roots of the identity. -/
theorem two_le_gnu_eight : 2 ≤ gnu 8 := by
  apply two_le_gnu_of_not_iso (S := GroupStructure.cyclic 8)
    (T := (GroupStructure.cyclic 4).prod (GroupStructure.cyclic 2))
  apply GroupStructure.not_iso_of_powOneCount_ne (k := 2)
  rw [powOneCount_cyclic_eight_two, powOneCount_cyclic_four_prod_cyclic_two_two]
  decide

/-- For every positive order at most `2³`, the number of isomorphism classes of
that order is at most the number of isomorphism classes of order `2³`.
This is the raw production implication for Erdős problem 1160 at `m = 3`. -/
theorem gnu_le_gnu_two_pow_three (n : ℕ) (hn : 1 ≤ n) (h : n ≤ 2 ^ 3) :
    gnu n ≤ gnu (2 ^ 3) := by
  have h8 : 2 ≤ gnu 8 := two_le_gnu_eight
  interval_cases n
  · rw [gnu_one]
    exact le_trans (by decide : 1 ≤ 2) h8
  · rw [gnu_two]
    exact le_trans (by decide : 1 ≤ 2) h8
  · rw [gnu_three]
    exact le_trans (by decide : 1 ≤ 2) h8
  · rw [gnu_four]
    exact h8
  · rw [gnu_five]
    exact le_trans (by decide : 1 ≤ 2) h8
  · rw [gnu_six]
    exact h8
  · rw [gnu_seven]
    exact le_trans (by decide : 1 ≤ 2) h8
  · exact le_refl _

example : 1 ≤ (6 : ℕ) ∧ (6 : ℕ) ≤ 2 ^ 3 := by decide

example : gnu 6 ≤ gnu (2 ^ 3) :=
  gnu_le_gnu_two_pow_three 6 (by decide) (by decide)

example : Nonempty (GroupStructure 8) := ⟨GroupStructure.cyclic 8⟩

example : Nonempty (Fin 8) := ⟨0⟩

end GroupCount
