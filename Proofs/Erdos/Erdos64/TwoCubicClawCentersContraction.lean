import Erdos.Erdos64.TwoCubicClawCentersForcedAdjacency

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersContraction

open SimpleGraph

universe u

/-- Contract the edge between `U` and `V` by retaining `U` and deleting `V`.
Only this auxiliary graph, not the original graph, is contracted. -/
def contracted {A : Type u} (K : SimpleGraph A) (U V : A) :
    SimpleGraph {x : A // x ≠ V} where
  Adj x y := x ≠ y ∧
    (K.Adj x.val y.val ∨ (x.val = U ∧ K.Adj V y.val) ∨ (y.val = U ∧ K.Adj x.val V))
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hxy | hxy | hxy
    · exact Or.inl hxy.symm
    · exact Or.inr (Or.inr ⟨hxy.1, hxy.2.symm⟩)
    · exact Or.inr (Or.inl ⟨hxy.1, hxy.2.symm⟩)⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

example : ¬ (contracted (⊥ : SimpleGraph Bool) false true).Adj
    ⟨false, by decide⟩ ⟨false, by decide⟩ := by intro h; exact h.1 rfl

example : (contracted (SimpleGraph.fromRel (fun a b : Fin 3 => a.val + 1 = b.val)) 0 1).Adj
    ⟨0, by decide⟩ ⟨2, by decide⟩ := by
  unfold contracted SimpleGraph.fromRel
  decide

/-- The quotient vertex map replaces the deleted endpoint by the retained endpoint. -/
def collapse {A : Type u} [DecidableEq A] (U V : A) (hUV : U ≠ V)
    (a : A) : {x : A // x ≠ V} :=
  if h : a = V then ⟨U, hUV⟩ else ⟨a, h⟩

example {A : Type u} [DecidableEq A] (U V : A) (hUV : U ≠ V) :
    collapse U V hUV V = ⟨U, hUV⟩ := by simp [collapse]

example {A : Type u} [DecidableEq A] (U V : A) (hUV : U ≠ V) (a : A) (ha : a ≠ V) :
    (collapse U V hUV a).val = a := by simp [collapse, ha]

section

variable {A : Type u} [Fintype A] [DecidableEq A] (K : SimpleGraph A)
    [DecidableRel K.Adj] (U V : A) (hUV : U ≠ V)

variable [DecidableRel (contracted K U V).Adj]

/-- At any vertex other than the contraction root, its new neighbors are exactly
the images of its old neighbors. -/
theorem neighbors_nonroot (x : {a : A // a ≠ V}) (hx : x.val ≠ U) :
    (contracted K U V).neighborFinset x =
      (K.neighborFinset x.val).image (collapse U V hUV) := by
  ext y
  simp only [mem_neighborFinset, Finset.mem_image]
  constructor
  · intro h
    rcases h.2 with he | he | he
    · refine ⟨y.val, he, ?_⟩
      simp [collapse, y.property]
    · exact (hx he.1).elim
    · refine ⟨V, he.2, ?_⟩
      apply Subtype.ext
      simp [collapse, he.1]
  · rintro ⟨a, ha, he⟩
    by_cases hav : a = V
    · subst a
      have hy : y.val = U := by
        have hv := congrArg Subtype.val he
        simpa [collapse] using hv.symm
      refine ⟨fun hxy => hx ((congrArg Subtype.val hxy).trans hy), Or.inr (Or.inr ⟨hy, ha⟩)⟩
    · have hy : a = y.val := by simpa [collapse, hav] using congrArg Subtype.val he
      have hadj : K.Adj x.val y.val := hy ▸ ha
      exact ⟨fun hxy => hadj.ne (congrArg Subtype.val hxy), Or.inl hadj⟩

/-- With no common endpoint neighbor, collapsing the endpoints is injective on
any nonroot vertex's neighbor finset. -/
theorem collapse_injOn_neighbors
    (hcommon : ∀ a, K.Adj U a → K.Adj V a → False)
    (x : {a : A // a ≠ V}) : Set.InjOn (collapse U V hUV) (K.neighborFinset x.val) := by
  intro a ha b hb he
  have hax : K.Adj x.val a := (K.mem_neighborFinset _ _).mp ha
  have hbx : K.Adj x.val b := (K.mem_neighborFinset _ _).mp hb
  by_cases hav : a = V <;> by_cases hbv : b = V
  · exact hav.trans hbv.symm
  · have hbU : b = U := by simpa [collapse, hav, hbv] using (congrArg Subtype.val he).symm
    exact (hcommon x.val (hbU ▸ hbx.symm) (hav ▸ hax.symm)).elim
  · have haU : a = U := by simpa [collapse, hav, hbv] using congrArg Subtype.val he
    exact (hcommon x.val (haU ▸ hax.symm) (hbv ▸ hbx.symm)).elim
  · simpa [collapse, hav, hbv] using congrArg Subtype.val he

include hUV in
/-- The contraction preserves the degree of every nonroot vertex. -/
theorem degree_nonroot
    (hcommon : ∀ a, K.Adj U a → K.Adj V a → False)
    (x : {a : A // a ≠ V}) (hx : x.val ≠ U) :
    (contracted K U V).degree x = K.degree x.val := by
  rw [← card_neighborFinset_eq_degree, neighbors_nonroot K U V hUV x hx,
    Finset.card_image_of_injOn (collapse_injOn_neighbors K U V hUV hcommon x),
    card_neighborFinset_eq_degree]

/-- The retained contraction root has the union of the endpoints' external
neighbor sets, with each vertex mapped into the deleted-endpoint subtype. -/
theorem neighbors_root :
    (contracted K U V).neighborFinset ⟨U, hUV⟩ =
      ((K.neighborFinset U).erase V ∪ (K.neighborFinset V).erase U).image
        (collapse U V hUV) := by
  ext y
  simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_union,
    Finset.mem_erase]
  constructor
  · intro h
    rcases h.2 with he | he | he
    · refine ⟨y.val, Or.inl ⟨y.property, he⟩, ?_⟩
      simp [collapse, y.property]
    · have hyU : y.val ≠ U := fun heq => h.1 (Subtype.ext heq.symm)
      refine ⟨y.val, Or.inr ⟨hyU, he.2⟩, ?_⟩
      simp [collapse, y.property]
    · exact (h.1 (Subtype.ext he.1.symm)).elim
  · rintro ⟨a, ha, he⟩
    have hav : a ≠ V := by
      rcases ha with ha | ha
      · exact ha.1
      · exact ha.2.ne.symm
    have hy : a = y.val := by simpa [collapse, hav] using congrArg Subtype.val he
    subst a
    rcases ha with ha | ha
    · have hadj := ha.2
      exact ⟨fun heq => hadj.ne (congrArg Subtype.val heq), Or.inl hadj⟩
    · exact ⟨fun heq => ha.1 (congrArg Subtype.val heq).symm,
        Or.inr (Or.inl ⟨rfl, ha.2⟩)⟩

omit [DecidableRel (contracted K U V).Adj] in
/-- Adjacent cubic endpoints without a common neighbor have four distinct external
neighbors. -/
theorem card_external_neighbors (he : K.Adj U V) (hU : K.degree U = 3) (hV : K.degree V = 3)
    (hcommon : ∀ a, K.Adj U a → K.Adj V a → False) :
    ((K.neighborFinset U).erase V ∪ (K.neighborFinset V).erase U).card = 4 := by
  have hd : Disjoint ((K.neighborFinset U).erase V) ((K.neighborFinset V).erase U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hcommon a ((K.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2)
      ((K.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hb).2)
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_erase_of_mem ((K.mem_neighborFinset _ _).mpr he),
    Finset.card_erase_of_mem ((K.mem_neighborFinset _ _).mpr he.symm),
    card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hU, hV]

/-- Contracting adjacent cubic endpoints with disjoint external neighbors gives a
degree-four root. -/
theorem degree_root (he : K.Adj U V) (hU : K.degree U = 3) (hV : K.degree V = 3)
    (hcommon : ∀ a, K.Adj U a → K.Adj V a → False) :
    (contracted K U V).degree ⟨U, hUV⟩ = 4 := by
  rw [← card_neighborFinset_eq_degree, neighbors_root K U V hUV]
  have hi : Set.InjOn (collapse U V hUV)
      (↑((K.neighborFinset U).erase V ∪ (K.neighborFinset V).erase U) : Set A) := by
    intro a ha b hb heq
    have hn (a : A) (ha : a ∈ (K.neighborFinset U).erase V ∪ (K.neighborFinset V).erase U) : a ≠ V := by
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_erase.mp ha).1
      · exact ((K.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ha).2).ne.symm
    simpa [collapse, hn a ha, hn b hb] using congrArg Subtype.val heq
  rw [Finset.card_image_of_injOn hi, card_external_neighbors K U V he hU hV hcommon]

end

example :
    let r : Fin 8 → Fin 8 → Prop := fun a b =>
      (a.val, b.val) ∈ [(0, 1), (0, 2), (0, 5), (1, 3), (1, 6), (2, 3),
        (2, 4), (3, 4), (4, 7), (5, 6), (5, 7), (6, 7)]
    let K := SimpleGraph.fromRel r
    letI : DecidableRel K.Adj := fun a b =>
      show Decidable (a ≠ b ∧ (r a b ∨ r b a)) from inferInstance
    (0 : Fin 8) ≠ 1 ∧ K.Adj 0 1 ∧ (∀ a, K.degree a = 3) ∧
      (∀ a, K.Adj 0 a → K.Adj 1 a → False) := by
  intro r K
  letI : DecidableRel K.Adj := fun a b =>
    show Decidable (a ≠ b ∧ (r a b ∨ r b a)) from inferInstance
  decide

end Erdos64.TwoCubicClawCentersContraction
