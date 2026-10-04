import Erdos.Erdos64.AdjacentDefectRepair
import Erdos.Erdos64.BipartiteTwoDefectRepair

set_option autoImplicit false
namespace Erdos64.BipartiteRepair
open SimpleGraph
open scoped Classical

/-- The two specified degree-two defects admit a repair in all color and adjacency cases. -/
theorem two_defects {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (hC4 : ¬ ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4)
    (p q : V) (hpq : p ≠ q) (hdp : G.degree p = 2) (hdq : G.degree q = 2)
    (hother : ∀ v, v ≠ p → v ≠ q → 3 ≤ G.degree v) :
    Nonempty (BipartiteRepairResult G) := by
  classical
  by_cases hcolor : c p = c q
  · obtain ⟨hne,hd,hcycles⟩ := BipartiteTwoDefectRepair.same_class_two_defect_repair
      G c hc p q hpq hcolor hdp hdq hother
    exact ⟨{
      Vertex := V
      vertices := inferInstance
      inhabited := hne
      graph := G ⊔ edge p q
      order_le := le_rfl
      min_degree := by
        intro v
        convert hd v using 1
        congr 1
        exact Subsingleton.elim _ _
      even_cycles := hcycles }⟩
  · by_cases hadj : G.Adj p q
    · exact AdjacentDefectRepair.adjacent_two_defect_repair G c hc hC4 p q hadj hdp hdq hother
    · obtain ⟨hne,_,hd,hcard,hcycles⟩ := BipartiteIdentificationRepair.opposite_class_two_defect_repair
        G c hc p q hpq hcolor hadj hdp hdq hother
      exact ⟨{
        Vertex := BipartiteIdentificationRepair.IdentifiedVertex q
        vertices := inferInstance
        inhabited := hne
        graph := BipartiteIdentificationRepair.identifiedGraph G p q hpq
        order_le := hcard.trans_le (Nat.sub_le _ _)
        min_degree := hd
        even_cycles := hcycles }⟩

/-- A nonempty minimum-degree-two graph with at most two defects admits the full repair. -/
theorem min_two_repair {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (hC4 : ¬ ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4)
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hlow : (Finset.univ.filter (fun v => G.degree v ≤ 2)).card ≤ 2) :
    Nonempty (BipartiteRepairResult G) := by
  classical
  let S := Finset.univ.filter (fun v => G.degree v ≤ 2)
  have hmem : ∀ v, v ∈ S ↔ G.degree v ≤ 2 := by intro v; simp [S]
  by_cases hzero : S.card = 0
  · have hempty := Finset.card_eq_zero.mp hzero
    have hd : ∀ v, 3 ≤ G.degree v := by
      intro v
      have hv : ¬ G.degree v ≤ 2 := by rw [← hmem v, hempty]; simp
      omega
    exact ⟨BipartiteRepairResult.identity G hd⟩
  · by_cases hone : S.card = 1
    · obtain ⟨p,hS⟩ := Finset.card_eq_one.mp hone
      have hdp : G.degree p = 2 := by
        have hl : G.degree p ≤ 2 := (hmem p).mp (by simp [hS])
        have hm := hmin p
        omega
      have hother : ∀ v, v ≠ p → 3 ≤ G.degree v := by
        intro v hv
        have hn : ¬ G.degree v ≤ 2 := by rw [← hmem v, hS]; simpa using hv
        omega
      have hpos : 0 < G.degree p := by omega
      obtain ⟨q,hpq⟩ := (G.degree_pos_iff_exists_adj p).mp hpos
      obtain ⟨hne,hd,hcard,hcycles⟩ := EdgeContractionRepair.one_defect_edge_contraction
        G c hc p q hpq hdp hother
      exact ⟨{
        Vertex := BipartiteIdentificationRepair.IdentifiedVertex q
        vertices := inferInstance
        inhabited := hne
        graph := BipartiteIdentificationRepair.identifiedGraph (G.deleteEdges {s(p,q)}) p q hpq.ne
        order_le := hcard
        min_degree := hd
        even_cycles := hcycles }⟩
    · have htwo : S.card = 2 := by change S.card ≤ 2 at hlow; omega
      obtain ⟨p,q,hpq,hS⟩ := Finset.card_eq_two.mp htwo
      have hdp : G.degree p = 2 := by
        have hl : G.degree p ≤ 2 := (hmem p).mp (by simp [hS])
        have hm := hmin p
        omega
      have hdq : G.degree q = 2 := by
        have hl : G.degree q ≤ 2 := (hmem q).mp (by simp [hS])
        have hm := hmin q
        omega
      have hother : ∀ v, v ≠ p → v ≠ q → 3 ≤ G.degree v := by
        intro v hvp hvq
        have hn : ¬ G.degree v ≤ 2 := by rw [← hmem v, hS]; simp [hvp,hvq]
        omega
      exact two_defects G c hc hC4 p q hpq hdp hdq hother

set_option maxHeartbeats 800000 in
/-- Full connectivity-free bipartite two-defect repair. Degree-zero and degree-one
exceptions are allowed: an induced core is extracted first. The finite nonempty output
has no larger order and minimum degree three, and every even genuine output cycle
lifts to a genuine input cycle of exactly the same length. No output connectivity,
bipartiteness, C4-freeness, or cubicity is asserted. This does not prove unrestricted E64. -/
theorem exists_repair {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (hC4 : ¬ ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4)
    (hlow : (Finset.univ.filter (fun v => G.degree v ≤ 2)).card ≤ 2)
    (hhigh : ∃ v, 3 ≤ G.degree v) : Nonempty (BipartiteRepairResult G) := by
  classical
  obtain ⟨s,hne,hcard,hmin,hlow'⟩ := TwoDefectCore.exists_induced_core_of_low_degree_count G hlow hhigh
  letI : Fintype ↥(s : Set V) := FinsetCoe.fintype s
  letI : Nonempty ↥(s : Set V) := hne
  let K := G.induce (s : Set V)
  let d : ↥(s : Set V) → Bool := fun v => c v.val
  have hKc : ∀ ⦃x y⦄, K.Adj x y → d x ≠ d y := fun {_ _} h => hc h
  have hKC4 : ¬ ∃ x, ∃ w : K.Walk x x, w.IsCycle ∧ w.length = 4 := by
    intro h
    exact hC4 (TwoDefectCore.cycle_induce_transport G _ h)
  obtain ⟨R⟩ := @min_two_repair ↥(s : Set V) (FinsetCoe.fintype s) hne K d hKc hKC4
    (by
      intro v
      convert hmin v using 1 <;> (congr 1; exact Subsingleton.elim _ _))
    (by
      convert hlow' using 1
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_of_eq (congrArg
        (fun f : Fintype (K.neighborSet v) => @SimpleGraph.degree _ K v f ≤ 2)
        (Subsingleton.elim _ _)))
  exact ⟨{
    Vertex := R.Vertex
    vertices := R.vertices
    inhabited := R.inhabited
    graph := R.graph
    order_le := R.order_le.trans hcard
    min_degree := R.min_degree
    even_cycles := fun n hn h => TwoDefectCore.cycle_induce_transport G _ (R.even_cycles n hn h) }⟩

end Erdos64.BipartiteRepair
