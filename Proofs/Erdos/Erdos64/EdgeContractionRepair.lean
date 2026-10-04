import Erdos.Erdos64.BipartiteIdentificationRepair
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

namespace Erdos64.EdgeContractionRepair
open SimpleGraph
open scoped Classical

/-- Removing an existing edge lowers the degree of its first endpoint by exactly one. -/
theorem degree_delete_edge_add_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (p q : V) (hpq : G.Adj p q) :
    (G.deleteEdges {s(p,q)}).degree p + 1 = G.degree p := by
  classical
  have hn : (G.deleteEdges {s(p,q)}).neighborFinset p = (G.neighborFinset p).erase q := by
    ext v
    simp [hpq.ne, and_comm]
  rw [← card_neighborFinset_eq_degree, hn, Finset.card_erase_of_mem (by simpa using hpq)]
  have hpos : 0 < G.degree p := (G.degree_pos_iff_exists_adj p).mpr ⟨q, hpq⟩
  rw [card_neighborFinset_eq_degree]
  omega

/-- Removing an edge leaves all other vertex degrees unchanged. -/
theorem degree_delete_edge_other {V : Type*} [Fintype V]
    (G : SimpleGraph V) (p q v : V) (hvp : v ≠ p) (hvq : v ≠ q) :
    (G.deleteEdges {s(p,q)}).degree v = G.degree v := by
  classical
  have hn : (G.deleteEdges {s(p,q)}).neighborFinset v = G.neighborFinset v := by
    ext z
    simp [hvp, hvq]
  rw [← card_neighborFinset_eq_degree, hn, card_neighborFinset_eq_degree]

/-- Inclusion of graphs preserves genuine cycles and their exact length. -/
theorem cycle_mono_transport {V : Type*} {H G : SimpleGraph V} (hHG : H ≤ G)
    {n : ℕ} (h : ∃ x, ∃ w : H.Walk x x, w.IsCycle ∧ w.length = n) :
    ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = n := by
  obtain ⟨x,w,hw,hlen⟩ := h
  let f : H →g G := ⟨id, fun {_ _} h => hHG h⟩
  exact ⟨f x, w.map f, hw.map Function.injective_id, by rw [Walk.length_map, hlen]⟩

/-- Explicit bipartite contraction of a single degree-two defect with an adjacent
vertex of degree at least three. The output is nonempty, has minimum degree three,
uses one fewer vertex, and transports every even genuine cycle with exact length.
No connectivity, C4 condition, or general one-defect repair conjecture is used. -/
theorem one_defect_edge_contraction {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (p q : V) (hpq : G.Adj p q) (hdp : G.degree p = 2)
    (hother : ∀ v, v ≠ p → 3 ≤ G.degree v) :
    let H := G.deleteEdges {s(p,q)}
    let Q := BipartiteIdentificationRepair.identifiedGraph H p q hpq.ne
    Nonempty (BipartiteIdentificationRepair.IdentifiedVertex q) ∧
      (∀ v, 3 ≤ Q.degree v) ∧
      Fintype.card (BipartiteIdentificationRepair.IdentifiedVertex q) ≤ Fintype.card V ∧
      (∀ n, Even n → (∃ x, ∃ w : Q.Walk x x, w.IsCycle ∧ w.length = n) →
        ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = n) := by
  classical
  dsimp only
  let H := G.deleteEdges {s(p,q)}
  have hHc : ∀ ⦃x y⦄, H.Adj x y → c x ≠ c y := fun {_ _} h => hc (deleteEdges_le _ h)
  have hnon : ¬ H.Adj p q := by simp [H]
  have hdp' : H.degree p + 1 = G.degree p := by
    convert degree_delete_edge_add_one G p q hpq using 1
  have hdq' : H.degree q + 1 = G.degree q := by
    have he : s(q,p) = s(p,q) := Sym2.eq_swap
    have ht := degree_delete_edge_add_one G q p hpq.symm
    rw [he] at ht
    convert ht using 1
  have hdq : 3 ≤ G.degree q := hother q hpq.ne.symm
  refine ⟨⟨⟨p,hpq.ne⟩⟩, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v.val = p
    · have heq : v = ⟨p,hpq.ne⟩ := Subtype.ext hv
      rw [heq, BipartiteIdentificationRepair.degree_merged H c hHc p q hpq.ne (hc hpq) hnon]
      have hsum : 3 ≤ H.degree p + H.degree q := by omega
      convert hsum using 1 <;> (congr 2 <;> exact Subsingleton.elim _ _)
    · rw [BipartiteIdentificationRepair.degree_other H c hHc p q hpq.ne (hc hpq) v hv]
      have hdv : H.degree v.val = G.degree v.val := by
        convert degree_delete_edge_other G p q v.val hv v.property using 1
      have hvthree : 3 ≤ H.degree v.val := hdv.symm ▸ hother v.val hv
      convert hvthree using 1
      congr 1
      exact Subsingleton.elim _ _
  · rw [BipartiteIdentificationRepair.card_identifiedVertex]
    omega
  · intro n hn hcycle
    exact cycle_mono_transport (deleteEdges_le _) (BipartiteIdentificationRepair.even_cycle_transport
      H c hHc p q hpq.ne (hc hpq) hnon hn hcycle)

/- Joint nonvacuity for the one-defect contraction: K3,4 with one edge removed.
The sole defect is vertex 3, and vertex 1 is an adjacent high-degree vertex. -/
example : ∃ (G : SimpleGraph (Fin 7)) (c : Fin 7 → Bool) (_ : DecidableRel G.Adj),
    (∀ x y, G.Adj x y → c x ≠ c y) ∧ G.Adj 3 1 ∧ G.degree 3 = 2 ∧
    (∀ v, v ≠ 3 → 3 ≤ G.degree v) := by
  let G : SimpleGraph (Fin 7) := fromRel fun x y =>
    x.val < 3 ∧ 3 ≤ y.val ∧ ¬ (x = 0 ∧ y = 3)
  let c : Fin 7 → Bool := fun x => decide (x.val < 3)
  refine ⟨G,c,(by dsimp [G]; infer_instance), ?_⟩
  decide

end Erdos64.EdgeContractionRepair
