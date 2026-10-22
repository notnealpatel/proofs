import Sorry.GroupCount.Gnu

set_option autoImplicit false

namespace GroupCount

/-- There are at most two isomorphism classes of groups of any positive order at most four. -/
theorem gnu_le_two_of_le_four (n : ℕ) (hn : 1 ≤ n) (h : n ≤ 4) :
    gnu n ≤ 2 := by
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [gnu_one]
    decide
  · rw [gnu_prime Nat.prime_two]
    decide
  · rw [gnu_prime Nat.prime_three]
    decide
  · rw [gnu_four]

/-- In a commutative group, any set whose distinct members fail to commute is finite
and has cardinality at most one, including when the set is empty. -/
theorem pairwise_noncommuting_finite_ncard_le_one (G : Type*) [CommGroup G]
    (S : Set G) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Commute x y) :
    S.Finite ∧ S.ncard ≤ 1 := by
  have hsub : S.Subsingleton := by
    intro x hx y hy
    by_contra hne
    exact hS x hx y hy hne (Commute.all x y)
  exact ⟨hsub.finite, (Set.ncard_le_one hsub.finite).2 hsub⟩

/-- Every commutative group is covered by one abelian subgroup, namely the whole group. -/
theorem commGroup_covered_by_one (G : Type*) [CommGroup G] :
    ∃ H : Fin 1 → Subgroup G,
      (∀ i, ∀ x ∈ H i, ∀ y ∈ H i, Commute x y) ∧
      ∀ g : G, ∃ i, g ∈ H i := by
  refine ⟨fun _ => ⊤, ?_, ?_⟩
  · intro i x hx y hy
    exact Commute.all x y
  · intro g
    exact ⟨0, Subgroup.mem_top g⟩

example : 1 ≤ (4 : ℕ) ∧ (4 : ℕ) ≤ 4 := by decide

example : gnu 4 ≤ 2 := gnu_le_two_of_le_four 4 (by decide) (by decide)

example : ∀ x ∈ ({(1 : ℤˣ)} : Set ℤˣ), ∀ y ∈ ({(1 : ℤˣ)} : Set ℤˣ),
    x ≠ y → ¬ Commute x y := by
  intro x hx y hy hne
  have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
  have hy1 : y = 1 := Set.mem_singleton_iff.mp hy
  exact (hne (hx1.trans hy1.symm)).elim

example : ({(1 : ℤˣ)} : Set ℤˣ).Finite ∧ ({(1 : ℤˣ)} : Set ℤˣ).ncard ≤ 1 := by
  exact ⟨Set.finite_singleton 1, by simp⟩

example : (∅ : Set ℤˣ).Finite ∧ (∅ : Set ℤˣ).ncard ≤ 1 := by
  apply pairwise_noncommuting_finite_ncard_le_one ℤˣ ∅
  intro x hx
  exact (Set.notMem_empty x hx).elim

example : Nonempty (Fin 1) := ⟨0⟩

example : ∃ H : Fin 1 → Subgroup ℤˣ,
    (∀ i, ∀ x ∈ H i, ∀ y ∈ H i, Commute x y) ∧
    ∀ g : ℤˣ, ∃ i, g ∈ H i := commGroup_covered_by_one ℤˣ

end GroupCount
