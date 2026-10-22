import Sorry.GroupCount.Gnu
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion

set_option autoImplicit false

namespace GroupCount.OrderEightModels

/-- The dihedral group used here has eight elements. -/
theorem dihedral_card : Fintype.card (DihedralGroup 4) = 8 := by
  simpa using (DihedralGroup.card (n := 4))

/-- The quaternion group used here has eight elements. -/
theorem quaternion_card : Fintype.card (QuaternionGroup 2) = 8 := by
  simpa using (QuaternionGroup.card (n := 2))

/-- A labeled presentation of the dihedral group of order eight. -/
noncomputable def dihedral : GroupStructure 8 :=
  GroupStructure.ofEquiv (Fintype.equivFinOfCardEq dihedral_card).symm

/-- A labeled presentation of the quaternion group of order eight. -/
noncomputable def quaternion : GroupStructure 8 :=
  GroupStructure.ofEquiv (Fintype.equivFinOfCardEq quaternion_card).symm

/-- The selected dihedral presentation is multiplicatively equivalent to Mathlib's model. -/
noncomputable def dihedralMulEquiv : dihedral.Carrier ≃* DihedralGroup 4 :=
  GroupStructure.ofEquivMulEquiv _

/-- The selected quaternion presentation is multiplicatively equivalent to Mathlib's model. -/
noncomputable def quaternionMulEquiv : quaternion.Carrier ≃* QuaternionGroup 2 :=
  GroupStructure.ofEquivMulEquiv _

example : Nonempty (dihedral.Carrier ≃* DihedralGroup 4) := ⟨dihedralMulEquiv⟩
example : Nonempty (quaternion.Carrier ≃* QuaternionGroup 2) := ⟨quaternionMulEquiv⟩

/-- Transport the count of roots of unity along a multiplicative equivalence. -/
theorem powOneCount_eq_card_of_mulEquiv {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (S : GroupStructure 8) (e : S.Carrier ≃* G) (k : ℕ) :
    S.powOneCount k = Fintype.card {g : G // g ^ k = 1} := by
  rw [GroupStructure.powOneCount_eq_card_pow]
  refine Fintype.card_congr (Equiv.subtypeEquiv e.toEquiv fun a => ?_)
  show a ^ k = 1 ↔ e a ^ k = 1
  rw [← map_pow, e.map_eq_one_iff]

/-- The dihedral model has six square roots of unity. -/
theorem dihedral_powOneCount_two : dihedral.powOneCount 2 = 6 := by
  rw [powOneCount_eq_card_of_mulEquiv dihedral dihedralMulEquiv]
  decide

/-- Every element of the dihedral model has fourth power one. -/
theorem dihedral_powOneCount_four : dihedral.powOneCount 4 = 8 := by
  rw [powOneCount_eq_card_of_mulEquiv dihedral dihedralMulEquiv]
  decide

/-- The quaternion model has two square roots of unity. -/
theorem quaternion_powOneCount_two : quaternion.powOneCount 2 = 2 := by
  rw [powOneCount_eq_card_of_mulEquiv quaternion quaternionMulEquiv]
  decide

/-- Every element of the quaternion model has fourth power one. -/
theorem quaternion_powOneCount_four : quaternion.powOneCount 4 = 8 := by
  rw [powOneCount_eq_card_of_mulEquiv quaternion quaternionMulEquiv]
  decide

/-- The fixed family, in order: C8, C4 × C2, C2³, D8, Q8.
No exhaustiveness claim is part of this definition. -/
noncomputable def family (i : Fin 5) : GroupStructure 8 :=
  ![GroupStructure.cyclic 8,
    (GroupStructure.cyclic 4).prod (GroupStructure.cyclic 2),
    ((GroupStructure.cyclic 2).prod (GroupStructure.cyclic 2)).prod
      (GroupStructure.cyclic 2), dihedral, quaternion] i

example : family 0 = GroupStructure.cyclic 8 := rfl
example : family 1 = (GroupStructure.cyclic 4).prod (GroupStructure.cyclic 2) := rfl
example : family 2 = ((GroupStructure.cyclic 2).prod (GroupStructure.cyclic 2)).prod
    (GroupStructure.cyclic 2) := rfl
example : family 3 = dihedral := rfl
example : family 4 = quaternion := rfl
example : Nonempty (Fin 5) := ⟨0⟩

/-- The fourth member's carrier is the dihedral group of order eight. -/
noncomputable def familyDihedralMulEquiv : (family 3).Carrier ≃* DihedralGroup 4 :=
  dihedralMulEquiv

/-- The fifth member's carrier is the quaternion group of order eight. -/
noncomputable def familyQuaternionMulEquiv : (family 4).Carrier ≃* QuaternionGroup 2 :=
  quaternionMulEquiv

example : Nonempty ((family 3).Carrier ≃* DihedralGroup 4) := ⟨familyDihedralMulEquiv⟩
example : Nonempty ((family 4).Carrier ≃* QuaternionGroup 2) := ⟨familyQuaternionMulEquiv⟩

/-- The square- and fourth-root counts of the five models distinguish all five. -/
theorem family_powOneCounts (i : Fin 5) :
    ((family i).powOneCount 2, (family i).powOneCount 4) =
      ![(2, 4), (4, 8), (8, 8), (6, 8), (2, 8)] i := by
  fin_cases i
  · decide
  · decide
  · decide
  · exact Prod.ext dihedral_powOneCount_two dihedral_powOneCount_four
  · exact Prod.ext quaternion_powOneCount_two quaternion_powOneCount_four

/-- Isomorphic members of the fixed five-model family have the same index. -/
theorem family_irredundant (i j : Fin 5) (h : (family i).Iso (family j)) : i = j := by
  have hinj : Function.Injective
      (fun k : Fin 5 => (![(2, 4), (4, 8), (8, 8), (6, 8), (2, 8)] k : ℕ × ℕ)) := by
    decide
  apply hinj
  change (![(2, 4), (4, 8), (8, 8), (6, 8), (2, 8)] i : ℕ × ℕ) =
    ![(2, 4), (4, 8), (8, 8), (6, 8), (2, 8)] j
  rw [← family_powOneCounts i, ← family_powOneCounts j]
  exact Prod.ext (GroupStructure.powOneCount_eq_of_iso h 2)
    (GroupStructure.powOneCount_eq_of_iso h 4)

example : (family 0).Iso (family 0) := .refl _
example : ¬ (family 0).Iso (family 4) := by
  intro h
  have heq := family_irredundant 0 4 h
  exact (by decide : (0 : Fin 5) ≠ 4) heq

/-- There are at least five isomorphism classes of groups of order eight.
The reverse inequality still requires an exhaustive classification. -/
theorem five_le_gnu_eight : 5 ≤ gnu 8 := by
  simpa using card_le_gnu_of_pairwise_not_iso family family_irredundant

end GroupCount.OrderEightModels
