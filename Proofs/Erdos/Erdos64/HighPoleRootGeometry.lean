import Erdos.Erdos64.HighPoleCompletion
import Erdos.Erdos64.GeneralRootIncidence

set_option autoImplicit false

namespace Erdos64.HighPoleRootGeometry

open SimpleGraph Erdos64.UniqueCubicClawCenter

universe u

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The original neighbors of the deleted vertex form an actual maximal clique
in its completion, even when the deleted vertex has degree greater than three. -/
theorem pole_isMaximalClique (hG : IsCounterexample G) {v : V} (hclaw : Claw G v) :
    Maximal (completion G v).IsClique {p | G.Adj v p.val} := by
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ := hclaw
  let a' : {x : V // x ≠ v} := ⟨a, ha.ne.symm⟩
  let b' : {x : V // x ≠ v} := ⟨b, hb.ne.symm⟩
  have hab' : a' ≠ b' := fun heq => hab (congrArg Subtype.val heq)
  have eab : (completion G v).Adj a' b' := Or.inr ⟨hab', ha, hb⟩
  have heq : edgeClique (completion G v) a' b' = {p | G.Adj v p.val} := by
    apply Set.Subset.antisymm
    · intro p hp
      rcases hp with rfl | rfl | ⟨epa, epb⟩
      · exact ha
      · exact hb
      · exact completion_common_poles G hG hab' ha hb epa.symm epb.symm
    · intro p hp
      by_cases hpa : p = a'
      · exact Or.inl hpa
      by_cases hpb : p = b'
      · exact Or.inr (Or.inl hpb)
      exact Or.inr (Or.inr ⟨Or.inr ⟨Ne.symm hpa, ha, hp⟩,
        Or.inr ⟨Ne.symm hpb, hb, hp⟩⟩)
  rw [← heq]
  exact ClawDiamondRoot.edgeClique_maximal _
    (HighPoleCompletion.completion_inducedDiamondFree G hG) eab

/-- The canonical pole root is precisely the original neighborhood of the
 deleted vertex, viewed as surviving labels. -/
noncomputable def poleRoot (hG : IsCounterexample G) {v : V} (hclaw : Claw G v) :
    RootNode (completion G v) :=
  ⟨{p | G.Adj v p.val}, pole_isMaximalClique G hG hclaw⟩

/-- The labels of the canonical pole root are exactly the original poles. -/
theorem poleRoot_val (hG : IsCounterexample G) {v : V} (hclaw : Claw G v) :
    (poleRoot G hG hclaw).val = {p | G.Adj v p.val} := rfl

private theorem nonSim (hG : IsCounterexample G) {v : V}
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b) :
    ∀ x : {x : V // x ≠ v}, ∃ a b, a ≠ b ∧ (completion G v).Adj x a ∧
      (completion G v).Adj x b ∧ ¬ (completion G v).Adj a b := by
  intro x
  obtain ⟨a, b, ha, hb, hab, hnab⟩ :=
    HighPoleCompletion.completion_nonsimplicial G hG hNind x
  exact ⟨a, b, hab, ha, hb, hnab⟩

/-- The pole root has degree equal to the original degree of the deleted vertex,
 not necessarily three. -/
theorem poleRoot_degree (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    (cliqueRoot (completion G v)).degree (poleRoot G hG hclaw) = G.degree v := by
  classical
  rw [GeneralRootIncidence.degree_eq_card _
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hunique) (nonSim G hG hNind)]
  let e : {p : {x : V // x ≠ v} // p ∈ (poleRoot G hG hclaw).val} ≃
      G.neighborSet v := {
    toFun := fun p => ⟨p.val.val, p.property⟩
    invFun := fun p => ⟨⟨p.val, p.property.ne.symm⟩, p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (SimpleGraph.card_neighborSet_eq_degree G v)

/-- A nonpole maximal clique contains at most one original pole label. -/
theorem nonpole_meets_poles_at_most_one (hG : IsCounterexample G) {v : V}
    (hclaw : Claw G v) (A : RootNode (completion G v))
    (hA : A ≠ poleRoot G hG hclaw) {x y : {x : V // x ≠ v}}
    (hxA : x ∈ A.val) (hyA : y ∈ A.val)
    (hx : G.Adj v x.val) (hy : G.Adj v y.val) : x = y :=
  ClawDiamondRoot.root_intersection_unique _
    (HighPoleCompletion.completion_inducedDiamondFree G hG) hA hxA hx hyA hy

/-- Edges within a nonpole root clique are original graph edges, not edges
 introduced by completing the deleted vertex's neighborhood. -/
theorem nonpole_adj_original (hG : IsCounterexample G) {v : V}
    (hclaw : Claw G v) (A : RootNode (completion G v))
    (hA : A ≠ poleRoot G hG hclaw) {x y : {x : V // x ≠ v}}
    (hxA : x ∈ A.val) (hyA : y ∈ A.val) (hxy : x ≠ y) : G.Adj x.val y.val := by
  have e := (SimpleGraph.isMaximalClique_iff.mp A.property).1 hxA hyA hxy
  rcases (completion_adj_iff G v x y).mp e with hold | ⟨_, hx, hy⟩
  · exact hold
  · exact False.elim (hxy (nonpole_meets_poles_at_most_one G hG hclaw A hA hxA hyA hx hy))

private theorem nonpole_card_le_three (hG : IsCounterexample G) {v : V}
    (hclaw : Claw G v) (A : RootNode (completion G v))
    (hA : A ≠ poleRoot G hG hclaw) : Fintype.card A.val ≤ 3 := by
  classical
  rw [← Set.toFinset_card]
  by_contra hnot
  have hlarge : 3 < A.val.toFinset.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < A.val.toFinset.card)
  have herase : 2 < (A.val.toFinset.erase x).card := by
    have hc := Finset.card_erase_add_one hx
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp herase
  have ha' : a ≠ x ∧ a ∈ A.val := by simpa using ha
  have hb' : b ≠ x ∧ b ∈ A.val := by simpa using hb
  have hc' : c ≠ x ∧ c ∈ A.val := by simpa using hc
  have hx' : x ∈ A.val := Set.mem_toFinset.mp hx
  have ne_val : ∀ {s t : {x : V // x ≠ v}}, s ≠ t → s.val ≠ t.val := by
    intro s t hne heq
    exact hne (Subtype.ext heq)
  exact not_four_cycle G hG (ne_val (Ne.symm ha'.1)) (ne_val (Ne.symm hb'.1))
    (ne_val (Ne.symm hc'.1)) (ne_val hab) (ne_val hac) (ne_val hbc)
    (nonpole_adj_original G hG hclaw A hA hx' ha'.2 (Ne.symm ha'.1))
    (nonpole_adj_original G hG hclaw A hA ha'.2 hb'.2 hab)
    (nonpole_adj_original G hG hclaw A hA hb'.2 hc'.2 hbc)
    (nonpole_adj_original G hG hclaw A hA hc'.2 hx' hc'.1)

/-- Every nonpole root node has degree two or three. The pole itself is excluded
 because its degree is the unrestricted original degree of the deleted center. -/
theorem nonpole_degree_two_or_three (hG : IsCounterexample G) {v : V}
    (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A : RootNode (completion G v)) (hA : A ≠ poleRoot G hG hclaw) :
    (cliqueRoot (completion G v)).degree A = 2 ∨
      (cliqueRoot (completion G v)).degree A = 3 := by
  classical
  letI : Nonempty {x : V // x ≠ v} := completion_nonempty G hclaw
  have hlo := GeneralRootIncidence.root_min_degree _
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hunique) (nonSim G hG hNind) A
  have hhi : (cliqueRoot (completion G v)).degree A ≤ 3 := by
    rw [GeneralRootIncidence.degree_eq_card _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hunique) (nonSim G hG hNind)]
    exact nonpole_card_le_three G hG hclaw A hA
  omega

private theorem original_pole_edge_triangle (hG : IsCounterexample G) {v : V}
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    {p q : {x : V // x ≠ v}} (hp : G.Adj v p.val) (hpq : G.Adj p.val q.val) :
    ∃ r : {x : V // x ≠ v}, (completion G v).Adj p r ∧
      (completion G v).Adj q r := by
  classical
  let s := (G.neighborFinset p.val).erase v
  have hv : v ∈ G.neighborFinset p.val := (G.mem_neighborFinset _ _).mpr hp.symm
  have hs : s.card = 2 := by
    have hc : s.card + 1 = G.degree p.val := Finset.card_erase_add_one hv
    have hd := HighPoleCompletion.pole_degree_three G hG hunique hNind p.val hp
    omega
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hs
  have ha : a ≠ v ∧ G.Adj p.val a := by
    have hm : a ∈ s := by rw [hsab]; simp
    simpa [s] using hm
  have hb : b ≠ v ∧ G.Adj p.val b := by
    have hm : b ∈ s := by rw [hsab]; simp
    simpa [s] using hm
  have hqab : q.val = a ∨ q.val = b := by
    have hm : q.val ∈ s := by simp [s, q.property, hpq]
    simpa [hsab] using hm
  have eab := HighPoleCompletion.external_neighbors_adj G hunique hNind hp
    ha.2 hb.2 ha.1 hb.1 hab
  rcases hqab with hqa | hqb
  · refine ⟨⟨b, hb.1⟩, Or.inl hb.2, Or.inl ?_⟩
    simpa only [hqa] using eab
  · refine ⟨⟨a, ha.1⟩, Or.inl ha.2, Or.inl ?_⟩
    simpa only [hqb] using eab.symm

/-- Every root neighbor of the canonical pole root has degree three, although
 the pole root's own degree can be any original degree at least three. -/
theorem pole_arm_degree_three (hG : IsCounterexample G) {v : V}
    (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A : RootNode (completion G v))
    (hPA : (cliqueRoot (completion G v)).Adj (poleRoot G hG hclaw) A) :
    (cliqueRoot (completion G v)).degree A = 3 := by
  classical
  obtain ⟨p, hpP, hpA⟩ := hPA.2
  have hp : G.Adj v p.val := hpP
  have hA : A ≠ poleRoot G hG hclaw := hPA.1.symm
  have hD := HighPoleCompletion.completion_inducedDiamondFree G hG (v := v)
  obtain ⟨a, b, ha, hb, hab, hnab⟩ :=
    HighPoleCompletion.completion_nonsimplicial G hG hNind p
  obtain ⟨q, hqA, hqp⟩ :=
    ClawDiamondRoot.maximal_clique_other_vertex _ hD ha A.property hpA
  have hpq := nonpole_adj_original G hG hclaw A hA hpA hqA (Ne.symm hqp)
  have epq : (completion G v).Adj p q := Or.inl hpq
  obtain ⟨r, epr, eqr⟩ := original_pole_edge_triangle G hG hunique hNind hp hpq
  have heq := ClawDiamondRoot.maximal_clique_eq_edgeClique _ hD epq A.property hpA hqA
  have hrA : r ∈ A.val := by
    rw [heq]
    exact Or.inr (Or.inr ⟨epr, eqr⟩)
  have hsub : ({p, q, r} : Finset {x : V // x ≠ v}) ⊆ A.val.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_toFinset.mpr hpA
    · exact Set.mem_toFinset.mpr hqA
    · exact Set.mem_toFinset.mpr hrA
  have hthree : ({p, q, r} : Finset {x : V // x ≠ v}).card = 3 := by
    simp [epq.ne, epr.ne, eqr.ne]
  have hlo : 3 ≤ (cliqueRoot (completion G v)).degree A := by
    rw [GeneralRootIncidence.degree_eq_card _ hD
      (completion_claw_free G hunique) (nonSim G hG hNind), ← Set.toFinset_card]
    have hc := Finset.card_le_card hsub
    omega
  rcases nonpole_degree_two_or_three G hG hclaw hunique hNind A hA with htwo | hthree
  · omega
  · exact hthree

end Erdos64.HighPoleRootGeometry
