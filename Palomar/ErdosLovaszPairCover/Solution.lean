import Erdos.ErdosLovaszPairCover

/-!
# The elementary pair-cover lower bound for the Erdős–Lovász number

For a positive integer `r`, let `g(r)` be the minimum number of edges in an
`r`-uniform intersecting finite hypergraph with transversal number `r`.  The
selected claim is the elementary bound `2 * r - 1 ≤ g(r)` for every positive
`r`.

The model below uses the equivalent no-small-cover condition: every finite set
of fewer than `r` vertices is disjoint from some edge.  It ranges over all
finite labelled ground types `Fin N`, with no bound on `N`.  The explicit
positive-parameter existence and attainment theorems keep the selected claim
away from the default value of an empty natural infimum.
-/

set_option autoImplicit false

namespace Palomar.ErdosLovaszPairCover

/-- An `r`-uniform intersecting finite family with no transversal of cardinality
less than `r`.  Intersecting includes the diagonal and therefore excludes an
empty edge. -/
def IsErdosLovaszFamily {α : Type*} (r : ℕ) (F : Finset (Finset α)) : Prop :=
  (∀ A ∈ F, A.card = r) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < r → ∃ A ∈ F, Disjoint A S

example : IsErdosLovaszFamily 0 (∅ : Finset (Finset (Fin 0))) := by
  unfold IsErdosLovaszFamily
  decide

example : ¬ IsErdosLovaszFamily 1 (∅ : Finset (Finset (Fin 0))) := by
  unfold IsErdosLovaszFamily
  decide

example : IsErdosLovaszFamily 1 ({{0}} : Finset (Finset (Fin 1))) := by
  unfold IsErdosLovaszFamily
  decide

example : IsErdosLovaszFamily 2
    ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by
  unfold IsErdosLovaszFamily
  decide

/-- All edge counts attained by Erdős–Lovász families over all finite labelled
ground types `Fin N`. -/
def erdosLovaszCards (r : ℕ) : Set ℕ :=
  {k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))), IsErdosLovaszFamily r F ∧ F.card = k}

example : (0 : ℕ) ∈ erdosLovaszCards 0 := by
  exact ⟨0, ∅, by unfold IsErdosLovaszFamily; decide, rfl⟩

example : (1 : ℕ) ∈ erdosLovaszCards 1 := by
  exact ⟨1, {{0}}, by unfold IsErdosLovaszFamily; decide, by decide⟩

example : (3 : ℕ) ∈ erdosLovaszCards 2 := by
  exact ⟨3, {{0, 1}, {0, 2}, {1, 2}},
    by unfold IsErdosLovaszFamily; decide, by decide⟩

/-- The Erdős–Lovász number `g(r)`, defined as the natural infimum of all
attainable edge counts. -/
noncomputable def erdosLovaszNum (r : ℕ) : ℕ := sInf (erdosLovaszCards r)

example : erdosLovaszNum 0 = 0 := by
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  exact ⟨0, ∅, by unfold IsErdosLovaszFamily; decide, rfl⟩

/-- All `(m + 1)`-subsets of a `(2 * m + 1)`-element type form an
Erdős–Lovász family. -/
theorem isErdosLovaszFamily_powersetCard (m : ℕ) :
    IsErdosLovaszFamily (m + 1)
      (Finset.powersetCard (m + 1) (Finset.univ : Finset (Fin (2 * m + 1)))) := by
  refine ⟨fun A hA => (Finset.mem_powersetCard.mp hA).2, ?_, ?_⟩
  · intro A hA B hB
    have hAc : A.card = m + 1 := (Finset.mem_powersetCard.mp hA).2
    have hBc : B.card = m + 1 := (Finset.mem_powersetCard.mp hB).2
    have hunion : (A ∪ B).card ≤ 2 * m + 1 := by
      simpa using Finset.card_le_univ (A ∪ B)
    have hsum : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
      Finset.card_union_add_card_inter A B
    have hpos : 0 < (A ∩ B).card := by omega
    exact Finset.not_disjoint_iff_nonempty_inter.mpr (Finset.card_pos.mp hpos)
  · intro S hS
    have hcomplcard : Sᶜ.card = 2 * m + 1 - S.card := by
      simpa using Finset.card_compl S
    obtain ⟨A, hAsub, hAcard⟩ :=
      Finset.exists_subset_card_eq (s := Sᶜ) (n := m + 1) (by omega)
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hAcard⟩, ?_⟩
    rw [Finset.disjoint_left]
    intro a haA haS
    exact (Finset.mem_compl.mp (hAsub haA)) haS

/-- For every positive parameter, the set whose natural infimum defines
`erdosLovaszNum` is nonempty. -/
theorem erdosLovaszCards_nonempty {r : ℕ} (hr : 0 < r) :
    (erdosLovaszCards r).Nonempty := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  exact ⟨_, 2 * m + 1, Finset.powersetCard (m + 1) Finset.univ,
    isErdosLovaszFamily_powersetCard m, rfl⟩

/-- At every positive parameter, the natural infimum is attained by an actual
finite Erdős–Lovász family. -/
theorem erdosLovaszNum_mem {r : ℕ} (hr : 0 < r) :
    erdosLovaszNum r ∈ erdosLovaszCards r :=
  Nat.sInf_mem (erdosLovaszCards_nonempty hr)

/-- The independent family predicate is definitionally identical to the source
predicate for every parameter and every ground type. -/
theorem isErdosLovaszFamily_iff_source {α : Type*} (r : ℕ)
    (F : Finset (Finset α)) :
    IsErdosLovaszFamily r F ↔ _root_.IsErdosLovaszFamily r F :=
  Iff.rfl

/-- The independent attainable-edge-count set is definitionally identical to
the source set at every parameter. -/
theorem erdosLovaszCards_eq_source (r : ℕ) :
    erdosLovaszCards r = _root_.erdosLovaszCards r :=
  rfl

/-- The independent natural-infimum invariant is definitionally identical to
the source invariant at every parameter. -/
theorem erdosLovaszNum_eq_source (r : ℕ) :
    erdosLovaszNum r = _root_.erdosLovaszNum r :=
  rfl

/-- The source theorem also certifies that the definitionally identical
independent natural infimum is attained, rather than defaulting on an empty
index set. -/
theorem erdosLovaszNum_mem_via_source {r : ℕ} (hr : 0 < r) :
    erdosLovaszNum r ∈ erdosLovaszCards r := by
  rw [erdosLovaszNum_eq_source, erdosLovaszCards_eq_source]
  exact _root_.erdosLovaszNum_mem hr

/-- Every positive-parameter Erdős–Lovász family has at least `2 * r - 1`
edges.  Equivalently, `2 * r - 1 ≤ g(r)`. -/
theorem two_mul_sub_one_le_erdosLovaszNum {r : ℕ} (hr : 0 < r) :
    2 * r - 1 ≤ erdosLovaszNum r := by
  rw [erdosLovaszNum_eq_source]
  exact _root_.two_mul_sub_one_le_erdosLovaszNum hr

example : 2 * 1 - 1 = erdosLovaszNum 1 := by
  rw [erdosLovaszNum_eq_source, _root_.erdosLovaszNum_one]

example : 2 * 2 - 1 = erdosLovaszNum 2 := by
  rw [erdosLovaszNum_eq_source, _root_.erdosLovaszNum_two]

#check @Palomar.ErdosLovaszPairCover.IsErdosLovaszFamily
#check @Palomar.ErdosLovaszPairCover.erdosLovaszCards
#check @Palomar.ErdosLovaszPairCover.erdosLovaszNum
#check @Palomar.ErdosLovaszPairCover.erdosLovaszCards_nonempty
#check @Palomar.ErdosLovaszPairCover.erdosLovaszNum_mem
#check @Palomar.ErdosLovaszPairCover.isErdosLovaszFamily_iff_source
#check @Palomar.ErdosLovaszPairCover.erdosLovaszCards_eq_source
#check @Palomar.ErdosLovaszPairCover.erdosLovaszNum_eq_source
#check @Palomar.ErdosLovaszPairCover.erdosLovaszNum_mem_via_source
#check @Palomar.ErdosLovaszPairCover.two_mul_sub_one_le_erdosLovaszNum
#print axioms Palomar.ErdosLovaszPairCover.erdosLovaszCards_nonempty
#print axioms Palomar.ErdosLovaszPairCover.erdosLovaszNum_mem
#print axioms Palomar.ErdosLovaszPairCover.isErdosLovaszFamily_iff_source
#print axioms Palomar.ErdosLovaszPairCover.erdosLovaszCards_eq_source
#print axioms Palomar.ErdosLovaszPairCover.erdosLovaszNum_eq_source
#print axioms Palomar.ErdosLovaszPairCover.erdosLovaszNum_mem_via_source
#print axioms Palomar.ErdosLovaszPairCover.two_mul_sub_one_le_erdosLovaszNum
#print axioms _root_.two_mul_sub_one_le_erdosLovaszNum

end Palomar.ErdosLovaszPairCover
