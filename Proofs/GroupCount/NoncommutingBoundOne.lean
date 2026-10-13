import Mathlib

set_option autoImplicit false

namespace GroupCount

/-- A group with no pairwise noncommuting set of size greater than one has
all of its elements commuting, without any finiteness assumption on the group. -/
theorem commute_of_noncommuting_bound_one (G : Type*) [Group G]
    (hbound : ∀ S : Set G,
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y) →
      S.Finite ∧ S.ncard ≤ 1) :
    ∀ x y : G, Commute x y := by
  intro x y
  by_contra hxy
  have hne : x ≠ y := by
    intro heq
    exact hxy (heq ▸ Commute.refl x)
  have hpair : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G),
      a ≠ b → ¬ Commute a b := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hxy
    · exact fun hyx => hxy hyx.symm
    · exact (hab rfl).elim
  have hcard := (hbound {x, y} hpair).2
  rw [Set.ncard_pair hne] at hcard
  omega

/-- A group satisfying the noncommuting bound one is covered by the single
abelian subgroup consisting of the whole group. -/
theorem covered_by_one_of_noncommuting_bound_one (G : Type*) [Group G]
    (hbound : ∀ S : Set G,
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y) →
      S.Finite ∧ S.ncard ≤ 1) :
    ∃ H : Fin 1 → Subgroup G,
      (∀ i, ∀ x ∈ H i, ∀ y ∈ H i, Commute x y) ∧
      ∀ g : G, ∃ i, g ∈ H i := by
  refine ⟨fun _ => ⊤, ?_, ?_⟩
  · intro i x hx y hy
    exact commute_of_noncommuting_bound_one G hbound x y
  · intro g
    exact ⟨0, Subgroup.mem_top g⟩

/-- Every subset of a subsingleton group is finite and has at most one element;
in particular such a group satisfies the noncommuting bound one. -/
theorem noncommuting_bound_one_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    ∀ S : Set G,
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y) →
      S.Finite ∧ S.ncard ≤ 1 := by
  intro S hS
  have hsub : S.Subsingleton := fun x hx y hy => Subsingleton.elim x y
  exact ⟨hsub.finite, (Set.ncard_le_one hsub.finite).2 hsub⟩

example :
    (∀ S : Set (Multiplicative Unit),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y) →
      S.Finite ∧ S.ncard ≤ 1) ∧
    (∃ H : Fin 1 → Subgroup (Multiplicative Unit),
      (∀ i, ∀ x ∈ H i, ∀ y ∈ H i, Commute x y) ∧
      ∀ g : Multiplicative Unit, ∃ i, g ∈ H i) := by
  have hbound := noncommuting_bound_one_of_subsingleton (Multiplicative Unit)
  exact ⟨hbound, covered_by_one_of_noncommuting_bound_one (Multiplicative Unit) hbound⟩

end GroupCount
