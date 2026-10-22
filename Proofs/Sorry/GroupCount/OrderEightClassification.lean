import Sorry.GroupCount.OrderEightModels
import GroupCount.OrderEightGenerators
import GroupCount.OrderEightRelations
import GroupCount.OrderEightElementary

set_option autoImplicit false

namespace GroupCount.OrderEightModels

/-- Every group structure on eight elements is isomorphic to one of
C8, C4 × C2, C2³, D8, and Q8, in that order in `family`. -/
theorem family_exhaustive (S : GroupStructure 8) : ∃ i : Fin 5, (family i).Iso S := by
  classical
  let G := S.Carrier
  have hcard : Nat.card G = 8 := S.natCard_carrier
  by_cases hex8 : ∃ a : G, orderOf a = 8
  · obtain ⟨a, ha⟩ := hex8
    letI : IsCyclic G := isCyclic_of_orderOf_eq_card a (ha.trans hcard.symm)
    refine ⟨0, GroupStructure.iso_of_mulEquiv ?_⟩
    change (GroupStructure.cyclic 8).Carrier ≃* G
    exact mulEquivOfCyclicCardEq (by rw [GroupStructure.natCard_carrier, hcard])
  · have hno8 : ∀ a : G, orderOf a ≠ 8 := by simpa only [not_exists] using hex8
    let e2 : (GroupStructure.cyclic 2).Carrier ≃* Multiplicative (ZMod 2) :=
      mulEquivOfCyclicCardEq (by simp)
    by_cases hex4 : ∃ a : G, orderOf a = 4
    · obtain ⟨a, ha⟩ := hex4
      obtain ⟨b, hb, hrel⟩ := normalized_order_eight_generators hcard a ha hno8
      rcases hrel with ⟨hc, hs⟩ | ⟨hi, hs | hs⟩
      · let e4 : (GroupStructure.cyclic 4).Carrier ≃* Multiplicative (ZMod 4) :=
          mulEquivOfCyclicCardEq (by simp)
        let model : (family 1).Carrier ≃*
            (Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) :=
          (GroupStructure.prodMulEquiv (GroupStructure.cyclic 4) (GroupStructure.cyclic 2)).trans
            (e4.prodCongr e2)
        refine ⟨1, GroupStructure.iso_of_mulEquiv ?_⟩
        exact model.trans (OrderEightRelations.commutingMulEquiv hcard a b ha hb hc hs).symm
      · refine ⟨3, GroupStructure.iso_of_mulEquiv ?_⟩
        exact familyDihedralMulEquiv.trans
          (OrderEightRelations.dihedralMulEquiv hcard a b ha hb hi hs).symm
      · refine ⟨4, GroupStructure.iso_of_mulEquiv ?_⟩
        exact familyQuaternionMulEquiv.trans
          (OrderEightRelations.quaternionMulEquiv hcard a b ha hb hi hs).symm
    · have hno4 : ∀ a : G, orderOf a ≠ 4 := by simpa only [not_exists] using hex4
      have hsmall : ∀ d : ℕ, d < 9 → d ∣ 8 → d ≠ 4 → d ≠ 8 → d ∣ 2 := by decide
      have hsq : ∀ a : G, a ^ 2 = 1 := by
        intro a
        have hd : orderOf a ∣ 8 := by
          simpa only [hcard] using orderOf_dvd_natCard a
        have hlt : orderOf a < 9 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
        exact orderOf_dvd_iff_pow_eq_one.mp (hsmall _ hlt hd (hno4 a) (hno8 a))
      obtain ⟨e⟩ := OrderEightElementary.nonempty_mulEquiv_of_card_eight_of_square_one hcard hsq
      let model : (family 2).Carrier ≃*
          ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) :=
        (GroupStructure.prodMulEquiv
          ((GroupStructure.cyclic 2).prod (GroupStructure.cyclic 2))
          (GroupStructure.cyclic 2)).trans
          (((GroupStructure.prodMulEquiv (GroupStructure.cyclic 2) (GroupStructure.cyclic 2)).trans
            (e2.prodCongr e2)).prodCongr e2)
      exact ⟨2, GroupStructure.iso_of_mulEquiv (model.trans e.symm)⟩

example : ∃ i : Fin 5, (family i).Iso (GroupStructure.cyclic 8) :=
  family_exhaustive (GroupStructure.cyclic 8)

example : Nat.card (family 0).Carrier = 8 ∧ Nonempty (family 0).Carrier :=
  ⟨(family 0).natCard_carrier, ⟨1⟩⟩

end GroupCount.OrderEightModels

namespace GroupCount

/-- There are exactly five isomorphism classes of groups of order eight. -/
theorem gnu_eight : gnu 8 = 5 := by
  have h := card_eq_gnu_of_classification OrderEightModels.family
    OrderEightModels.family_exhaustive OrderEightModels.family_irredundant
  simpa using h.symm

end GroupCount
