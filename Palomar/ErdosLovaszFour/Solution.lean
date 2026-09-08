import Erdos.ErdosLovasz

set_option autoImplicit false

namespace Palomar.ErdosLovaszFour

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

example : ¬ IsErdosLovaszFamily 4 (∅ : Finset (Finset (Fin 0))) := by
  unfold IsErdosLovaszFamily
  decide

example : ¬ IsErdosLovaszFamily 4
    ({{0, 1, 2, 3}} : Finset (Finset (Fin 4))) := by
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
seven vertices form an admissible family. This excludes a vacuous equality
involving the default value of `Nat.sInf` on an empty set. -/
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

/-- The package family predicate agrees definitionally with the substantive
repository predicate on every ground type and at every parameter. -/
theorem isErdosLovaszFamily_iff_source {α : Type*} (r : ℕ) (F : Finset (Finset α)) :
    IsErdosLovaszFamily r F ↔ _root_.IsErdosLovaszFamily r F := Iff.rfl

/-- The package set of attainable edge counts is the repository set. -/
theorem erdosLovaszCards_eq_source (r : ℕ) :
    erdosLovaszCards r = _root_.erdosLovaszCards r := rfl

/-- Taking the infimum of the definitionally identical edge-count sets
identifies the package invariant with the repository invariant. -/
theorem erdosLovaszNum_eq_source (r : ℕ) :
    erdosLovaszNum r = _root_.erdosLovaszNum r := rfl

/-- The exact Erdős–Lovász value at uniformity four is nine. -/
theorem tripathi_erdosLovaszNum_four : erdosLovaszNum 4 = 9 := by
  rw [erdosLovaszNum_eq_source]
  exact _root_.tripathi_erdosLovaszNum_four

example : IsErdosLovaszFamily 4 witnessFour ∧ witnessFour.card = 9 :=
  ⟨(isErdosLovaszFamily_iff_source 4 witnessFour).mpr
    _root_.isErdosLovaszFamily_witnessFour, witnessFour_card⟩

example : (9 : ℕ) ∈ erdosLovaszCards 4 :=
  ⟨11, witnessFour, (isErdosLovaszFamily_iff_source 4 witnessFour).mpr
    _root_.isErdosLovaszFamily_witnessFour, witnessFour_card⟩

#check @Palomar.ErdosLovaszFour.IsErdosLovaszFamily
#check @Palomar.ErdosLovaszFour.erdosLovaszCards
#check @Palomar.ErdosLovaszFour.erdosLovaszNum
#check @Palomar.ErdosLovaszFour.erdosLovaszCards_four_nonempty
#check @Palomar.ErdosLovaszFour.isErdosLovaszFamily_iff_source
#check @Palomar.ErdosLovaszFour.erdosLovaszCards_eq_source
#check @Palomar.ErdosLovaszFour.erdosLovaszNum_eq_source
#check @Palomar.ErdosLovaszFour.tripathi_erdosLovaszNum_four
#print axioms Palomar.ErdosLovaszFour.erdosLovaszCards_four_nonempty
#print axioms Palomar.ErdosLovaszFour.isErdosLovaszFamily_iff_source
#print axioms Palomar.ErdosLovaszFour.erdosLovaszCards_eq_source
#print axioms Palomar.ErdosLovaszFour.erdosLovaszNum_eq_source
#print axioms Palomar.ErdosLovaszFour.tripathi_erdosLovaszNum_four
#print axioms _root_.ErdosLovaszFourLower.nine_le_card
#print axioms _root_.IsErdosLovaszFamily.nine_le_card
#print axioms _root_.tripathi_nine_le_erdosLovaszNum_four
#print axioms _root_.erdosLovaszNum_four_le
#print axioms _root_.tripathi_erdosLovaszNum_four

end Palomar.ErdosLovaszFour
