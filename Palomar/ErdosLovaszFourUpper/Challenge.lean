import Mathlib

set_option autoImplicit false

namespace Palomar.ErdosLovaszFourUpper

/-- An `r`-uniform intersecting finite family with no cover of size less than
`r`. Intersecting includes the diagonal, so no edge is empty. A cover is a
finite set meeting every edge; the last clause explicitly excludes all small
covers by requiring an edge disjoint from each candidate. -/
def IsErdosLovaszFamily {α : Type*} (r : ℕ) (F : Finset (Finset α)) : Prop :=
  (∀ A ∈ F, A.card = r) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < r → ∃ A ∈ F, Disjoint A S

example : IsErdosLovaszFamily 1 ({{0}} : Finset (Finset (Fin 1))) := by
  unfold IsErdosLovaszFamily
  decide
example : ¬ IsErdosLovaszFamily 1 (∅ : Finset (Finset (Fin 1))) := by
  unfold IsErdosLovaszFamily
  decide

/-- All edge counts of such families over all finite labelled ground types
`Fin N`. There is no upper bound on `N`. -/
def erdosLovaszCards (r : ℕ) : Set ℕ :=
  {k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))), IsErdosLovaszFamily r F ∧ F.card = k}

example : (1 : ℕ) ∈ erdosLovaszCards 1 := by
  refine ⟨1, {{0}}, ?_, by decide⟩
  unfold IsErdosLovaszFamily
  decide

/-- The minimum edge count `g(r)`. The totalized natural infimum is zero on
an empty index set; `erdosLovaszCards_four_nonempty` excludes that branch at
the selected parameter `r = 4`. -/
noncomputable def erdosLovaszNum (r : ℕ) : ℕ := sInf (erdosLovaszCards r)

example : erdosLovaszNum 0 = 0 := by
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  refine ⟨0, ∅, ?_, rfl⟩
  unfold IsErdosLovaszFamily
  simp

/-- At `r = 4` the minimum ranges over a nonempty set: all four-subsets of
seven vertices form an admissible family. This excludes a vacuous upper
bound caused by the default value of `Nat.sInf`. -/
theorem erdosLovaszCards_four_nonempty : (erdosLovaszCards 4).Nonempty := by
  refine ⟨_, 7, (Finset.univ : Finset (Fin 7)).powersetCard 4, ?_, rfl⟩
  refine ⟨fun A hA => (Finset.mem_powersetCard.mp hA).2, ?_, ?_⟩
  · intro A hA B hB
    have hAc : A.card = 4 := (Finset.mem_powersetCard.mp hA).2
    have hBc : B.card = 4 := (Finset.mem_powersetCard.mp hB).2
    have hunion : (A ∪ B).card ≤ 7 := by simpa using Finset.card_le_univ (A ∪ B)
    have hsum := Finset.card_union_add_card_inter A B
    have hpos : 0 < (A ∩ B).card := by omega
    exact Finset.not_disjoint_iff_nonempty_inter.mpr (Finset.card_pos.mp hpos)
  · intro S hS
    have hcompl : Sᶜ.card = 7 - S.card := by simpa using Finset.card_compl S
    obtain ⟨A, hAS, hAcard⟩ :=
      Finset.exists_subset_card_eq (s := Sᶜ) (n := 4) (by omega)
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hAcard⟩, ?_⟩
    rw [Finset.disjoint_left]
    intro x hxA hxS
    exact (Finset.mem_compl.mp (hAS hxA)) hxS

/-- Tripathi's explicit nine-edge family proves `g(4) ≤ 9`. This is only the
upper bound, not the full equality `g(4) = 9`. -/
theorem erdosLovaszNum_four_le : erdosLovaszNum 4 ≤ 9 := by
  sorry

#check @Palomar.ErdosLovaszFourUpper.IsErdosLovaszFamily
#check @Palomar.ErdosLovaszFourUpper.erdosLovaszCards
#check @Palomar.ErdosLovaszFourUpper.erdosLovaszNum
#check @Palomar.ErdosLovaszFourUpper.erdosLovaszCards_four_nonempty
#check @Palomar.ErdosLovaszFourUpper.erdosLovaszNum_four_le
#print axioms Palomar.ErdosLovaszFourUpper.erdosLovaszNum_four_le

end Palomar.ErdosLovaszFourUpper
