/-
Same-class terminal case of the reviewed informal bipartite two-defect repair
(BIPARTITE-SIDE-ELIMINATION.md and BIPARTITE-REPAIR-REVIEW.md).
This module proves only edge addition between same-color defects, not pruning,
identification, contraction, the full repair theorem, or E64. No novelty is claimed.
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace Erdos64.BipartiteTwoDefectRepair

open SimpleGraph
open scoped Classical

private theorem walk_length_add_added_edge_count_mod_two {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) (u v : V) (huv : c u = c v)
    {x y : V} (p : (G ⊔ edge u v).Walk x y) :
    (p.length + p.edges.count s(u,v)) % 2 = if c x = c y then 0 else 1 := by
  classical
  induction p with
  | nil => simp
  | @cons x z y h p ih =>
    have he : s(x,z) = s(u,v) ↔ c x = c z := by
      simp only [sup_adj, edge_adj] at h
      rcases h with h | h
      · constructor
        · intro he
          have hends : x = u ∧ z = v ∨ x = v ∧ z = u := by simpa only [Sym2.eq_iff] using he
          rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact huv
          · exact huv.symm
        · intro hxz
          exact False.elim (hc h hxz)
      · rcases h.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [huv, Sym2.eq_swap]
    simp only [Walk.length_cons, Walk.edges_cons, List.count_cons]
    by_cases hcount : s(x,z) = s(u,v)
    · simp only [beq_iff_eq, hcount, ↓reduceIte]
      have hxz := he.mp hcount
      cases hx : c x <;> cases hz : c z <;> cases hy : c y <;>
        simp_all <;> omega
    · simp only [beq_iff_eq, hcount, ↓reduceIte]
      have hxz : c x ≠ c z := fun hh => hcount (he.mpr hh)
      cases hx : c x <;> cases hz : c z <;> cases hy : c y <;>
        simp_all <;> omega

/-- An even genuine cycle after adding a same-color edge avoids that edge entirely.
The Boolean coloring witnesses bipartiteness; no finiteness or connectedness is needed. -/
theorem even_cycle_avoids_added_edge {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) (u v : V) (huv : c u = c v)
    {x : V} (p : (G ⊔ edge u v).Walk x x) (hp : p.IsCycle)
    (heven : Even p.length) : s(u,v) ∉ p.edges := by
  classical
  have hpar := walk_length_add_added_edge_count_mod_two G c hc u v huv p
  simp only [↓reduceIte] at hpar
  have hcount : p.edges.count s(u,v) ≤ 1 :=
    List.nodup_iff_count_le_one.mp hp.isCircuit.isTrail.edges_nodup _
  obtain ⟨k, hk⟩ := heven
  have hzero : p.edges.count s(u,v) = 0 := by omega
  exact List.count_eq_zero.mp hzero

/-- Every even genuine cycle in the graph obtained by adding a same-color edge has a
same-length genuine cycle in the original graph, for all lengths (not just dyadic ones). -/
theorem even_cycle_transport {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) (u v : V) (huv : c u = c v)
    {n : ℕ} (hn : Even n)
    (h : ∃ x, ∃ p : (G ⊔ edge u v).Walk x x, p.IsCycle ∧ p.length = n) :
    ∃ x, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = n := by
  classical
  obtain ⟨x, p, hp, hlen⟩ := h
  have havoid := even_cycle_avoids_added_edge G c hc u v huv p hp (hlen ▸ hn)
  have hsub : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
    intro e he
    have hmem := p.edges_subset_edgeSet he
    rw [edgeSet_sup, Set.mem_union] at hmem
    rcases hmem with hG | hnew
    · exact hG
    · have heq : e = s(u,v) := (edgeSet_edge u v ▸ hnew).1
      exact False.elim (havoid (heq ▸ he))
  exact ⟨x, p.transfer G hsub, hp.transfer hsub, (p.length_transfer hsub).trans hlen⟩

private theorem degree_add_edge_at {V : Type*} [Fintype V] (G : SimpleGraph V)
    (u v : V) (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    (G ⊔ edge u v).degree u = G.degree u + 1 := by
  classical
  have hneighbors : (G ⊔ edge u v).neighborFinset u = insert v (G.neighborFinset u) := by
    ext w
    simp only [mem_neighborFinset, sup_adj, edge_adj, Finset.mem_insert]
    constructor
    · rintro (hG | ⟨hnew, _⟩)
      · exact Or.inr hG
      · rcases hnew with ⟨_, hw⟩ | ⟨hu, _⟩
        · exact Or.inl hw
        · exact False.elim (hne hu)
    · rintro (rfl | hG)
      · exact Or.inr ⟨Or.inl ⟨True.intro, rfl⟩, hne⟩
      · exact Or.inl hG
  rw [← card_neighborFinset_eq_degree, hneighbors, Finset.card_insert_of_notMem]
  · rfl
  · simpa using hnadj

/- Joint satisfiability: K4,4 with four deleted edges, leaving exactly the
   two same-class degree-two defects 0 and 1. Other degrees are three or four.
   The output also has a genuine even cycle 2-4-3-5-2, so cycle transport
   is not merely being tested on an empty even-cycle spectrum. -/
example : ∃ (G : SimpleGraph (Fin 8)) (c : Fin 8 → Bool)
    (_ : DecidableRel G.Adj),
    (∀ x y, G.Adj x y → c x ≠ c y) ∧ c 0 = c 1 ∧
    (0 : Fin 8) ≠ 1 ∧ G.degree 0 = 2 ∧ G.degree 1 = 2 ∧
    (∀ w, w ≠ 0 → w ≠ 1 → 3 ≤ G.degree w) ∧
    (∃ p : (G ⊔ edge 0 1).Walk 2 2, p.IsCycle ∧ p.length = 4) := by
  let G : SimpleGraph (Fin 8) := fromRel fun x y =>
    x.val < 4 ∧ 4 ≤ y.val ∧
      ¬ (x = 0 ∧ y.val < 6) ∧ ¬ (x = 1 ∧ 6 ≤ y.val)
  let c : Fin 8 → Bool := fun x => decide (x.val < 4)
  refine ⟨G, c, (by dsimp [G]; infer_instance), ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  let p : (G ⊔ edge 0 1).Walk 2 2 :=
    .cons (by decide : (G ⊔ edge 0 1).Adj 2 4)
      (.cons (by decide : (G ⊔ edge 0 1).Adj 4 3)
        (.cons (by decide : (G ⊔ edge 0 1).Adj 3 5)
          (.cons (by decide : (G ⊔ edge 0 1).Adj 5 2) .nil)))
  refine ⟨p, ?_, rfl⟩
  simp [p, Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.support]

/-- Terminal same-class two-defect repair: distinct same-color vertices of degree two
become degree three by adding their edge, all other degrees remain at least three,
and every even genuine output cycle has an exact-length genuine input cycle.
The output uses the original finite nonempty vertex type, so its order is unchanged.
No connectedness, C4-freeness, or regularity is assumed. -/
theorem same_class_two_defect_repair {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) (u v : V)
    (hne : u ≠ v) (huv : c u = c v)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2)
    (hother : ∀ w, w ≠ u → w ≠ v → 3 ≤ G.degree w) :
    Nonempty V ∧
      (∀ w, 3 ≤ (G ⊔ edge u v).degree w) ∧
      (∀ n : ℕ, Even n →
        (∃ x, ∃ p : (G ⊔ edge u v).Walk x x, p.IsCycle ∧ p.length = n) →
        ∃ x, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = n) := by
  classical
  have hnadj : ¬ G.Adj u v := fun h => hc h huv
  refine ⟨⟨u⟩, ?_, ?_⟩
  · intro w
    by_cases hwu : w = u
    · subst w
      rw [degree_add_edge_at G u v hne hnadj, hdu]
    · by_cases hwv : w = v
      · subst w
        have hdeg := degree_add_edge_at G v u hne.symm (fun h => hnadj h.symm)
        have hthree : 3 ≤ (G ⊔ edge v u).degree v := by omega
        have hle : G ⊔ edge v u ≤ G ⊔ edge u v := by
          rw [edge_comm (s := v) (t := u)]
        exact hthree.trans ((G ⊔ edge v u).degree_le_of_le hle)
      · exact (hother w hwu hwv).trans (G.degree_le_of_le le_sup_left)
  · intro n hn hcycle
    exact even_cycle_transport G c hc u v huv hn hcycle

end Erdos64.BipartiteTwoDefectRepair
