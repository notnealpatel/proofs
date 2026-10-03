import Erdos.Erdos64.SubcubicFunnelH7

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel
open SimpleGraph

/-- The finite H7 graph has maximum degree three, computed by the standard
neighbor-finset degree, not by an assumed saturation rule. -/
theorem h7_subcubic : ∀ v, h7.degree v ≤ 3 := by decide

/-- The H7 graph has no genuine simple four-cycle. -/
theorem h7_no_cycle_four : ¬ HasSimpleCycleOfLength h7 4 := by
  apply not_cycle_four_of_common_neighbor_unique
  decide

/-- Seven vertices cannot support a genuine simple eight-cycle. -/
theorem h7_no_cycle_eight : ¬ HasSimpleCycleOfLength h7 8 := by
  rintro ⟨v, w, hw, hl⟩
  have hc := cycle_length_le_card hw
  simp only [Fintype.card_fin] at hc
  omega

/-- The specified H7 ports are separated by more than two edges. -/
theorem h7_ports_separated : 2 < h7.edist 0 1 := by
  rw [SimpleGraph.two_lt_edist_iff]
  refine ⟨by decide, by decide, ?_⟩
  ext v
  fin_cases v <;> simp [SimpleGraph.commonNeighbors_eq, h7]

/-- Joint satisfiability of every structural hypothesis, together with the
nonfactor branch, on an explicit finite simple graph. -/
theorem h7_fixture :
    (∀ v, h7.degree v ≤ 3) ∧
    ¬ HasSimpleCycleOfLength h7 4 ∧
    ¬ HasSimpleCycleOfLength h7 8 ∧
    (0 : Fin 7) ≠ 1 ∧ 2 < h7.edist 0 1 ∧
    (∃ w : h7.Walk 0 1, w.IsPath ∧ w.length = 4) ∧
    AlignedH7 h7 0 1 ∧
    ¬ ∃ z, ∀ w : h7.Walk 0 1, w.IsPath → w.length = 4 →
      z ∈ w.support ∧ z ≠ 0 ∧ z ≠ 1 := by
  exact ⟨h7_subcubic, h7_no_cycle_four, h7_no_cycle_eight, by decide,
    h7_ports_separated, nonempty_path4_iff.mp h7_nonfactor.1,
    h7_aligned, h7_aligned.no_common_walk_internal⟩

/-- A five-vertex funnel fixture: the triangle at the first port feeds a
single two-edge tail into the second port. Vertex order is `(s,t,a,b,c)`. -/
def funnel5 : SimpleGraph (Fin 5) where
  Adj i j := (i, j) ∈ ([(0,2), (0,3), (2,3), (3,4), (4,1)] :
    List (Fin 5 × Fin 5)) ∨
    (j, i) ∈ ([(0,2), (0,3), (2,3), (3,4), (4,1)] : List (Fin 5 × Fin 5))
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

instance : DecidableRel funnel5.Adj := fun _i _j => inferInstanceAs (Decidable (_ ∨ _))

/-- The fixture adjacency is exactly its five specified undirected edges. -/
theorem funnel5_adj_iff (i j : Fin 5) : funnel5.Adj i j ↔
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨
    (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨
    (j = 0 ∧ i = 2) ∨ (j = 0 ∧ i = 3) ∨ (j = 2 ∧ i = 3) ∨
    (j = 3 ∧ i = 4) ∨ (j = 4 ∧ i = 1) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The sole four-edge path tuple in the five-vertex fixture. -/
def funnel5Path : Path4 funnel5 0 1 :=
  ⟨2, 3, 4, by decide, by decide, by decide, by decide, by decide⟩

example : funnel5Path.first = 2 ∧ funnel5Path.middle = 3 ∧ funnel5Path.last = 4 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Every four-path in the fixture has exactly the displayed internal vertices. -/
theorem funnel5_path_unique (p : Path4 funnel5 0 1) :
    p.first = 2 ∧ p.middle = 3 ∧ p.last = 4 := by
  have hf : ∀ a b c : Fin 5, funnel5.Adj 0 a → funnel5.Adj a b →
      funnel5.Adj b c → funnel5.Adj c 1 → a = 2 ∧ b = 3 ∧ c = 4 := by decide
  exact hf p.first p.middle p.last p.edge₀ p.edge₁ p.edge₂ p.edge₃

/-- Joint satisfiability of every structural hypothesis on the funnel branch,
with a common internal vertex adjacent to the first endpoint. -/
theorem funnel5_fixture :
    (∀ v, funnel5.degree v ≤ 3) ∧
    ¬ HasSimpleCycleOfLength funnel5 4 ∧
    ¬ HasSimpleCycleOfLength funnel5 8 ∧
    (0 : Fin 5) ≠ 1 ∧ 2 < funnel5.edist 0 1 ∧
    (∃ w : funnel5.Walk 0 1, w.IsPath ∧ w.length = 4) ∧
    funnel5.Adj 0 2 ∧
    (∀ w : funnel5.Walk 0 1, w.IsPath → w.length = 4 →
      (2 : Fin 5) ∈ w.support ∧ (2 : Fin 5) ≠ 0 ∧ (2 : Fin 5) ≠ 1) := by
  have h4 : ¬ HasSimpleCycleOfLength funnel5 4 := by
    apply not_cycle_four_of_common_neighbor_unique
    decide
  have h8 : ¬ HasSimpleCycleOfLength funnel5 8 := by
    rintro ⟨v, w, hw, hl⟩
    have hc := cycle_length_le_card hw
    simp only [Fintype.card_fin] at hc
    omega
  have hsep : 2 < funnel5.edist 0 1 := by
    rw [SimpleGraph.two_lt_edist_iff]
    refine ⟨by decide, by decide, ?_⟩
    ext v
    fin_cases v <;> simp [SimpleGraph.commonNeighbors_eq, funnel5]
  have hall : ∀ p : Path4 funnel5 0 1, p.Internal 2 := by
    intro p
    exact Or.inl (funnel5_path_unique p).1.symm
  exact ⟨by decide, h4, h8, by decide, hsep,
    ⟨funnel5Path.walk, funnel5Path.walk_isPath, funnel5Path.walk_length⟩,
    by decide, (common_internal_iff 2).mp hall⟩

end Erdos64.SubcubicFunnel
