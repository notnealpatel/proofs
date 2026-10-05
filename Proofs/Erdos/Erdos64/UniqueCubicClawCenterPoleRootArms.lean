import Erdos.Erdos64.UniqueCubicClawCenter

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- Every completed edge incident to an original pole belongs to a triangle. -/
theorem completion_pole_edge_triangle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hv : G.degree v = 3) (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    {p q : {x : V // x ≠ v}} (hp : G.Adj v p.val)
    (hpq : (completion G v).Adj p q) :
    ∃ r, (completion G v).Adj p r ∧ (completion G v).Adj q r := by
  classical
  rcases hpq with hold | ⟨hne, _, hq⟩
  · let s := (G.neighborFinset p.val).erase v
    have hmem : v ∈ G.neighborFinset p.val := (G.mem_neighborFinset _ _).mpr hp.symm
    have hcount : s.card = 2 := by
      have hc : s.card + 1 = G.degree p.val := Finset.card_erase_add_one hmem
      have hd := pole_degree_three G hG hv hclaw hunique hp
      omega
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcount
    have ha : a ≠ v ∧ G.Adj p.val a := by
      have hm : a ∈ s := by rw [hs]; simp
      simpa [s] using hm
    have hb : b ≠ v ∧ G.Adj p.val b := by
      have hm : b ∈ s := by rw [hs]; simp
      simpa [s] using hm
    have hqab : q.val = a ∨ q.val = b := by
      have hm : q.val ∈ s := by simp [s, q.property, hold]
      simpa [hs] using hm
    have eab := external_neighbors_adj G hv hclaw hunique hp ha.2 hb.2 ha.1 hb.1 hab
    rcases hqab with hqa | hqb
    · refine ⟨⟨b, hb.1⟩, Or.inl hb.2, Or.inl ?_⟩
      simpa only [hqa] using eab
    · refine ⟨⟨a, ha.1⟩, Or.inl ha.2, Or.inl ?_⟩
      simpa only [hqb] using eab.symm
  · obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, _, _, _⟩ := hclaw
    have hl := neighbors_eq_claw_leaves G hv hab hac hbc ha hb hc
    have hval : p.val ≠ q.val := fun heq => hne (Subtype.ext heq)
    have hex : ∃ r : V, G.Adj v r ∧ p.val ≠ r ∧ q.val ≠ r := by
      rcases (hl p.val).mp hp with hpa | hpb | hpc <;>
        rcases (hl q.val).mp hq with hqa | hqb | hqc
      · exact False.elim (hval (hpa.trans hqa.symm))
      · exact ⟨c, hc, hpa ▸ hac, hqb ▸ hbc⟩
      · exact ⟨b, hb, hpa ▸ hab, hqc ▸ hbc.symm⟩
      · exact ⟨c, hc, hpb ▸ hbc, hqa ▸ hac⟩
      · exact False.elim (hval (hpb.trans hqb.symm))
      · exact ⟨a, ha, hpb ▸ hab.symm, hqc ▸ hac.symm⟩
      · exact ⟨b, hb, hpc ▸ hbc.symm, hqa ▸ hab⟩
      · exact ⟨a, ha, hpc ▸ hac.symm, hqb ▸ hab.symm⟩
      · exact False.elim (hval (hpc.trans hqc.symm))
    obtain ⟨r, hr, hpr, hqr⟩ := hex
    let r' : {x : V // x ≠ v} := ⟨r, hr.ne.symm⟩
    exact ⟨r', Or.inr ⟨fun heq => hpr (congrArg Subtype.val heq), hp, hr⟩,
      Or.inr ⟨fun heq => hqr (congrArg Subtype.val heq), hq, hr⟩⟩

/-- Three distinct labels in a root clique force its root degree to be three. -/
private theorem root_degree_three_of_three_members {W : Type u} [Fintype W]
    [Nonempty W] (R : SimpleGraph W) [DecidableRel R.Adj]
    [DecidableRel (cliqueRoot R).Adj] (hD : StrongDiamondFree R)
    (hclaw : ∀ x, ¬ Claw R x) (hmin : ∀ x, 3 ≤ R.degree x)
    (C : RootNode R) {a b c : W} (ha : a ∈ C.val) (hb : b ∈ C.val)
    (hc : c ∈ C.val) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (cliqueRoot R).degree C = 3 := by
  classical
  have hsub : ({a, b, c} : Finset W) ⊆ C.val.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_toFinset.mpr ha
    · exact Set.mem_toFinset.mpr hb
    · exact Set.mem_toFinset.mpr hc
  have hbound : 3 ≤ (cliqueRoot R).degree C := by
    rw [cliqueRoot_degree_eq_card R hD hclaw hmin C, ← Set.toFinset_card]
    have hcard := Finset.card_le_card hsub
    have hthree : ({a, b, c} : Finset W).card = 3 := by simp [hab, hac, hbc]
    omega
  rcases cliqueRoot_degree_two_or_three R hD hclaw hmin C with htwo | hthree
  · omega
  · exact hthree

/-- Every maximal completed clique containing an original pole has root degree three. -/
theorem completion_root_degree_three_of_pole {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (C : RootNode (completion G v)) {p : {x : V // x ≠ v}}
    (hp : G.Adj v p.val) (hpC : p ∈ C.val) :
    (cliqueRoot (completion G v)).degree C = 3 := by
  classical
  letI : Nonempty {x : V // x ≠ v} := completion_nonempty G hclaw
  let Q := completion G v
  have hD := completion_strongDiamondFree G hG hv
  have hfree := completion_claw_free G hunique
  have hmin := completion_min_degree G hG hv hclaw
  obtain ⟨a, b, ha, _, _, _⟩ := exists_nonadjacent_neighbors Q hD (hmin p)
  obtain ⟨q, hqC, hqp⟩ := maximal_clique_other_vertex Q hD ha C.property hpC
  have hpq : Q.Adj p q := (SimpleGraph.isMaximalClique_iff.mp C.property).1 hpC hqC hqp.symm
  obtain ⟨r, hpr, hqr⟩ := completion_pole_edge_triangle G hG hv hclaw hunique hp hpq
  have heq := maximal_clique_eq_edgeClique Q hD hpq C.property hpC hqC
  have hrC : r ∈ C.val := by
    rw [heq]
    exact Or.inr (Or.inr ⟨hpr, hqr⟩)
  exact root_degree_three_of_three_members Q hD hfree hmin C hpC hqC hrC
    hpq.ne hpr.ne hqr.ne

/-- The pole triangle gives a cubic root node whose every neighboring root node is cubic,
derived solely from the original unique cubic claw counterexample hypotheses. -/
theorem exists_pole_root_with_cubic_arms {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v) :
    ∃ z : RootNode (completion G v),
      z.val = {p | G.Adj v p.val} ∧
      (cliqueRoot (completion G v)).degree z = 3 ∧
      ∀ D, (cliqueRoot (completion G v)).Adj z D →
        (cliqueRoot (completion G v)).degree D = 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ := hclaw
  let a' : {x : V // x ≠ v} := ⟨a, ha.ne.symm⟩
  let b' : {x : V // x ≠ v} := ⟨b, hb.ne.symm⟩
  have hab' : a' ≠ b' := fun heq => hab (congrArg Subtype.val heq)
  have eab : (completion G v).Adj a' b' := Or.inr ⟨hab', ha, hb⟩
  let z : RootNode (completion G v) :=
    ⟨edgeClique (completion G v) a' b',
      edgeClique_maximal _ (completion_strongDiamondFree G hG hv) eab⟩
  have hz : z.val = {p | G.Adj v p.val} := by
    apply Set.Subset.antisymm
    · intro p hp
      rcases hp with hpa | hpb | ⟨epa, epb⟩
      · subst p
        exact ha
      · subst p
        exact hb
      · exact completion_common_poles G hG hab' ha hb epa.symm epb.symm
    · intro p hp
      by_cases hpa : p = a'
      · exact Or.inl hpa
      by_cases hpb : p = b'
      · exact Or.inr (Or.inl hpb)
      exact Or.inr (Or.inr ⟨Or.inr ⟨Ne.symm hpa, ha, hp⟩,
        Or.inr ⟨Ne.symm hpb, hb, hp⟩⟩)
  refine ⟨z, hz, completion_root_degree_three_of_pole G hG hv
    ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ hunique z ha
      (Or.inl rfl), ?_⟩
  intro D hD
  obtain ⟨p, hpz, hpD⟩ := hD.2
  have hp : G.Adj v p.val := by
    rw [hz] at hpz
    exact hpz
  exact completion_root_degree_three_of_pole G hG hv
    ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ hunique D hp hpD

end Erdos64.UniqueCubicClawCenter
