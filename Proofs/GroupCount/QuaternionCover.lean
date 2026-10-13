import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false

namespace GroupCount.QuaternionCover

open QuaternionGroup

/-- Three elements of Q8 with no commuting distinct pair. -/
def witness : Set (QuaternionGroup 2) := {a 1, xa 0, xa 1}

example : (a 1 : QuaternionGroup 2) ∈ witness := by
  unfold witness
  decide
example : (a 0 : QuaternionGroup 2) ∉ witness := by
  unfold witness
  decide

/-- The three four-element carriers for the cyclic subgroups covering Q8. -/
def carrier (i : Fin 3) : Finset (QuaternionGroup 2) :=
  ![{a 0, a 1, a 2, a 3}, {a 0, a 2, xa 0, xa 2}, {a 0, a 2, xa 1, xa 3}] i

example : carrier 0 = {a 0, a 1, a 2, a 3} := rfl
example : carrier 1 = {a 0, a 2, xa 0, xa 2} := rfl
example : carrier 2 = {a 0, a 2, xa 1, xa 3} := rfl

private theorem carrier_one : ∀ i, (1 : QuaternionGroup 2) ∈ carrier i := by decide
private theorem carrier_mul : ∀ i x y, x ∈ carrier i → y ∈ carrier i → x * y ∈ carrier i := by decide
private theorem carrier_inv : ∀ i x, x ∈ carrier i → x⁻¹ ∈ carrier i := by decide

/-- The three explicit four-element subgroups of Q8. -/
def subgroup (i : Fin 3) : Subgroup (QuaternionGroup 2) where
  carrier := ↑(carrier i)
  one_mem' := carrier_one i
  mul_mem' := fun {x y} => carrier_mul i x y
  inv_mem' := fun {x} => carrier_inv i x

example (i : Fin 3) (g : QuaternionGroup 2) : g ∈ subgroup i ↔ g ∈ carrier i := Iff.rfl

/-- Every pair of elements in any one of the three subgroups commutes. -/
theorem subgroup_commute : ∀ i x, x ∈ subgroup i → ∀ y, y ∈ subgroup i → Commute x y := by
  change ∀ i x, x ∈ carrier i → ∀ y, y ∈ carrier i → x * y = y * x
  decide

/-- Every element of Q8 belongs to at least one of the three subgroups. -/
theorem subgroup_cover : ∀ g : QuaternionGroup 2, ∃ i : Fin 3, g ∈ subgroup i := by
  change ∀ g : QuaternionGroup 2, ∃ i : Fin 3, g ∈ carrier i
  decide

/-- The explicit noncommuting witness has exactly three elements. -/
theorem witness_ncard : witness.ncard = 3 := by
  change ({a 1, xa 0, xa 1} : Set (QuaternionGroup 2)).ncard = 3
  have h : (xa 0 : QuaternionGroup 2) ≠ xa 1 := by decide
  simp [Set.ncard_insert_of_notMem, h, -a_zero]

/-- Distinct elements in the explicit witness do not commute. -/
theorem witness_pairwise : ∀ x ∈ witness, ∀ y ∈ witness, x ≠ y → ¬ Commute x y := by
  unfold witness Commute SemiconjBy
  decide

/-- Q8 has a three-element set of pairwise noncommuting elements. -/
theorem noncommuting_triple : ∃ S : Set (QuaternionGroup 2),
    S.ncard = 3 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y :=
  ⟨witness, witness_ncard, witness_pairwise⟩

/-- Q8 is covered by three explicit internally abelian subgroups. -/
theorem abelian_cover : ∃ H : Fin 3 → Subgroup (QuaternionGroup 2),
    (∀ i, ∀ x ∈ H i, ∀ y ∈ H i, Commute x y) ∧ ∀ g, ∃ i, g ∈ H i :=
  ⟨subgroup, subgroup_commute, subgroup_cover⟩

end GroupCount.QuaternionCover
