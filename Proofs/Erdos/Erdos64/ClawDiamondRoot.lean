import Erdos.Erdos64.UniqueCubicClawCenter

/-!
Canonical maximal-clique root certificates for claw-free, induced-diamond-free graphs
without simplicial vertices. We reuse the accepted canonical sets and root graph.
The standard bag description is due to Cygan et al., arXiv:1503.00704,
`kernel.tex`, lines 8–44: bags are maximal cliques and singleton simplicial bags.
Here nonsimpliciality excludes the latter. No bound on clique size is imposed.
-/

set_option autoImplicit false

namespace Erdos64.ClawDiamondRoot

open SimpleGraph
open Erdos64.UniqueCubicClawCenter (Claw edgeClique RootNode cliqueRoot
  clique_subset_edgeClique neighbor_mem_two_edgeCliques)

universe u

-- The four-cycle jointly realizes all three global hypotheses, on a nonempty domain.
set_option synthInstance.maxSize 512 in
example :
    let R : SimpleGraph (Fin 4) := {
      Adj := fun x y => x.val % 2 ≠ y.val % 2
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h rfl⟩ }
    (∀ x, ¬ Claw R x) ∧
    (∀ x, ∃ a b, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b) ∧
    (∀ a b c d, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) ∧ R.Adj 0 1 := by
  dsimp only [Claw]
  decide

-- Induced diamond exclusion permits K₄; it is not the old strong exclusion.
example : ∀ a b c d : Fin 4, c ≠ d → (⊤ : SimpleGraph (Fin 4)).Adj a b →
    (⊤ : SimpleGraph (Fin 4)).Adj a c → (⊤ : SimpleGraph (Fin 4)).Adj a d →
    (⊤ : SimpleGraph (Fin 4)).Adj b c → (⊤ : SimpleGraph (Fin 4)).Adj b d →
    ¬ (⊤ : SimpleGraph (Fin 4)).Adj c d → False := by
  decide

/-- The canonical set associated to an edge is a clique. -/
theorem edgeClique_isClique {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) {x y : V} (hxy : R.Adj x y) :
    R.IsClique (edgeClique R x y) := by
  intro a ha b hb hab
  rcases ha with rfl | rfl | ⟨hxa, hya⟩
  · rcases hb with rfl | rfl | ⟨hxb, hyb⟩
    · exact False.elim (hab rfl)
    · exact hxy
    · exact hxb
  · rcases hb with rfl | rfl | ⟨hxb, hyb⟩
    · exact hxy.symm
    · exact False.elim (hab rfl)
    · exact hyb
  · rcases hb with rfl | rfl | ⟨hxb, hyb⟩
    · exact hxa.symm
    · exact hya.symm
    · by_contra hnab
      exact hDiamond x y a b hab hxy hxa hxb hya hyb hnab


/-- The canonical edge clique is inclusion-maximal, not merely maximum among some family. -/
theorem edgeClique_maximal {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) {x y : V} (hxy : R.Adj x y) :
    Maximal R.IsClique (edgeClique R x y) := by
  apply SimpleGraph.isMaximalClique_iff.mpr
  refine ⟨edgeClique_isClique R hDiamond hxy, ?_⟩
  intro C hC hsub
  exact clique_subset_edgeClique R hC (hsub (Or.inl rfl)) (hsub (Or.inr (Or.inl rfl)))


/-- An edge belongs to exactly one inclusion-maximal clique, its canonical edge clique. -/
theorem maximal_clique_eq_edgeClique {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) {x y : V} (hxy : R.Adj x y)
    {C : Set V} (hC : Maximal R.IsClique C) (hx : x ∈ C) (hy : y ∈ C) :
    C = edgeClique R x y := by
  have hC' := SimpleGraph.isMaximalClique_iff.mp hC
  have hsub := clique_subset_edgeClique R hC'.1 hx hy
  exact Set.Subset.antisymm hsub (hC'.2 _ (edgeClique_isClique R hDiamond hxy) hsub)


/-- A maximal clique through a vertex contains another vertex whenever that vertex has a neighbor. -/
theorem maximal_clique_other_vertex {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) {x a : V} (ha : R.Adj x a)
    {C : Set V} (hC : Maximal R.IsClique C) (_hx : x ∈ C) :
    ∃ y ∈ C, y ≠ x := by
  by_contra hnone
  have hsingleton : ∀ y ∈ C, y = x := by
    intro y hy
    by_contra hne
    exact hnone ⟨y, hy, hne⟩
  have hsub : C ⊆ edgeClique R x a := by
    intro y hy
    exact Or.inl (hsingleton y hy)
  have hext := (SimpleGraph.isMaximalClique_iff.mp hC).2 _ (edgeClique_isClique R hDiamond ha) hsub
  have haC : a ∈ C := hext (Or.inr (Or.inl rfl))
  exact ha.ne (hsingleton a haC).symm


/-- Without simplicial vertices, claw and induced diamond exclusion imply exactly two
maximal cliques at every vertex, with no restriction on their sizes. -/
theorem exactly_two_maximal_cliques {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) (hclaw : ∀ x, ¬ Claw R x)
    (hNonsimplicial : ∀ x, ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b) (x : V) :
    ∃ C D : Set V, Maximal R.IsClique C ∧ Maximal R.IsClique D ∧ C ≠ D ∧
      x ∈ C ∧ x ∈ D ∧ ∀ E : Set V, Maximal R.IsClique E →
        (x ∈ E ↔ E = C ∨ E = D) := by
  obtain ⟨a, b, ha, hb, hab, hnab⟩ := hNonsimplicial x
  let C := edgeClique R x a
  let D := edgeClique R x b
  have hC : Maximal R.IsClique C := edgeClique_maximal R hDiamond ha
  have hD' : Maximal R.IsClique D := edgeClique_maximal R hDiamond hb
  have hne : C ≠ D := by
    intro heq
    have haD : a ∈ D := by
      rw [← heq]
      exact Or.inr (Or.inl rfl)
    rcases haD with hax | hab' | ⟨_, hba⟩
    · exact ha.ne hax.symm
    · exact hab hab'
    · exact hnab hba.symm
  refine ⟨C, D, hC, hD', hne, Or.inl rfl, Or.inl rfl, ?_⟩
  intro E hE
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := maximal_clique_other_vertex R hDiamond ha hE hx
    have exy : R.Adj x y := (SimpleGraph.isMaximalClique_iff.mp hE).1 hx hy hyx.symm
    have heqE := maximal_clique_eq_edgeClique R hDiamond exy hE hx hy
    rcases neighbor_mem_two_edgeCliques R hclaw ha hb hab hnab exy with hyC | hyD
    · have heqC := maximal_clique_eq_edgeClique R hDiamond exy hC (Or.inl rfl) hyC
      exact Or.inl (heqE.trans heqC.symm)
    · have heqD := maximal_clique_eq_edgeClique R hDiamond exy hD' (Or.inl rfl) hyD
      exact Or.inr (heqE.trans heqD.symm)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inl rfl


/-- Distinct maximal cliques have subsingleton intersection (at most one vertex). -/
theorem maximal_clique_intersection_subsingleton {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False)
    {C D : Set V} (hC : Maximal R.IsClique C) (hD : Maximal R.IsClique D)
    (hne : C ≠ D) : (C ∩ D).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have exy : R.Adj x y := (SimpleGraph.isMaximalClique_iff.mp hC).1 hx.1 hy.1 hxy
  have heqC := maximal_clique_eq_edgeClique R hDiamond exy hC hx.1 hy.1
  have heqD := maximal_clique_eq_edgeClique R hDiamond exy hD hx.2 hy.2
  exact hne (heqC.trans heqD.symm)

/-- Distinct maximal cliques intersect in at most one vertex, so root edges have unique labels. -/
theorem root_intersection_unique {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) {C D : RootNode R} (hne : C ≠ D)
    {x y : V} (hxC : x ∈ C.val) (hxD : x ∈ D.val)
    (hyC : y ∈ C.val) (hyD : y ∈ D.val) : x = y := by
  by_contra hxy
  have exy : R.Adj x y := (SimpleGraph.isMaximalClique_iff.mp C.property).1 hxC hyC hxy
  have heqC := maximal_clique_eq_edgeClique R hDiamond exy C.property hxC hyC
  have heqD := maximal_clique_eq_edgeClique R hDiamond exy D.property hxD hyD
  exact hne (Subtype.ext (heqC.trans heqD.symm))


/-- Every original vertex labels exactly two distinct root nodes and no others. -/
theorem exactly_two_root_nodes {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) (hclaw : ∀ x, ¬ Claw R x)
    (hNonsimplicial : ∀ x, ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b) (x : V) :
    ∃ C D : RootNode R, C ≠ D ∧ x ∈ C.val ∧ x ∈ D.val ∧
      ∀ E : RootNode R, x ∈ E.val ↔ E = C ∨ E = D := by
  obtain ⟨C, D, hC, hD', hne, hxC, hxD, hfiber⟩ := exactly_two_maximal_cliques R hDiamond hclaw hNonsimplicial x
  refine ⟨⟨C, hC⟩, ⟨D, hD'⟩, fun heq => hne (congrArg Subtype.val heq), hxC, hxD, ?_⟩
  intro E
  rw [hfiber E.val E.property]
  constructor
  · rintro (heq | heq)
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr (Subtype.ext heq)
  · rintro (heq | heq)
    · exact Or.inl (congrArg Subtype.val heq)
    · exact Or.inr (congrArg Subtype.val heq)


/-- For an edge in the original graph, exactly one root node contains both endpoint labels. -/
theorem exactly_one_root_node_of_adj {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) {x y : V} (hxy : R.Adj x y) :
    ∃! C : RootNode R, x ∈ C.val ∧ y ∈ C.val := by
  let C : RootNode R := ⟨edgeClique R x y, edgeClique_maximal R hDiamond hxy⟩
  refine ⟨C, ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩, ?_⟩
  intro D hmem
  exact Subtype.ext (maximal_clique_eq_edgeClique R hDiamond hxy D.property hmem.1 hmem.2)


/-- Once two root nodes through a label are known, they exhaust that label's incidence fiber. -/
theorem root_incidence_exhausted {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) (hclaw : ∀ x, ¬ Claw R x)
    (hNonsimplicial : ∀ x, ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b) {x : V} {C D E : RootNode R}
    (hne : C ≠ D) (hxC : x ∈ C.val) (hxD : x ∈ D.val) (hxE : x ∈ E.val) :
    E = C ∨ E = D := by
  obtain ⟨A, B, hAB, hxA, hxB, hfiber⟩ := exactly_two_root_nodes R hDiamond hclaw hNonsimplicial x
  have hC := (hfiber C).mp hxC
  have hD' := (hfiber D).mp hxD
  have hE := (hfiber E).mp hxE
  rcases hC with rfl | rfl <;> rcases hD' with rfl | rfl <;> rcases hE with rfl | rfl
  all_goals simp_all


/-- Three pairwise distinct root nodes cannot all contain one label. -/
theorem no_three_root_nodes {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) (hclaw : ∀ x, ¬ Claw R x)
    (hNonsimplicial : ∀ x, ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b) {x : V} {C D E : RootNode R}
    (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E)
    (hxC : x ∈ C.val) (hxD : x ∈ D.val) (hxE : x ∈ E.val) : False := by
  rcases root_incidence_exhausted R hDiamond hclaw hNonsimplicial hCD hxC hxD hxE with heq | heq
  · exact hCE heq.symm
  · exact hDE heq.symm


/-- The canonical clique root is triangle-free. -/
theorem cliqueRoot_triangle_free {V : Type u} (R : SimpleGraph V)
    (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
      R.Adj b c → R.Adj b d → ¬ R.Adj c d → False) (hclaw : ∀ x, ¬ Claw R x)
    (hNonsimplicial : ∀ x, ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b) {A B C : RootNode R}
    (hAB : (cliqueRoot R).Adj A B) (hBC : (cliqueRoot R).Adj B C)
    (hCA : (cliqueRoot R).Adj C A) : False := by
  obtain ⟨a, haA, haB⟩ := hAB.2
  obtain ⟨b, hbB, hbC⟩ := hBC.2
  obtain ⟨c, hcC, hcA⟩ := hCA.2
  have hab : a ≠ b := by
    intro heq
    rw [← heq] at hbC
    exact no_three_root_nodes R hDiamond hclaw hNonsimplicial hAB.1 hCA.1.symm hBC.1 haA haB hbC
  have hbc : b ≠ c := by
    intro heq
    rw [← heq] at hcA
    exact no_three_root_nodes R hDiamond hclaw hNonsimplicial hAB.1 hCA.1.symm hBC.1 hcA hbB hbC
  have eab : R.Adj a b := (SimpleGraph.isMaximalClique_iff.mp B.property).1 haB hbB hab
  have ebc : R.Adj b c := (SimpleGraph.isMaximalClique_iff.mp C.property).1 hbC hcC hbc
  have heqB := maximal_clique_eq_edgeClique R hDiamond eab B.property haB hbB
  have hcB : c ∈ B.val := by
    rw [heqB]
    by_cases hac : a = c
    · exact Or.inl hac.symm
    · have eac : R.Adj a c := (SimpleGraph.isMaximalClique_iff.mp A.property).1 haA hcA hac
      exact Or.inr (Or.inr ⟨eac, ebc⟩)
  have heqB' := maximal_clique_eq_edgeClique R hDiamond ebc B.property hbB hcB
  have heqC := maximal_clique_eq_edgeClique R hDiamond ebc C.property hbC hcC
  exact hBC.1 (Subtype.ext (heqB'.trans heqC.symm))


end Erdos64.ClawDiamondRoot
