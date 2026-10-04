import Erdos.Erdos64.EdgeContractionRepair

set_option autoImplicit false
universe u
namespace Erdos64
open SimpleGraph
open scoped Classical

/-- A consumable finite, nonempty repaired simple graph of no greater order and
minimum degree three, with exact-length transport of every even genuine cycle.
Its vertex type may be a subtype; no bipartiteness or connectivity of the output is asserted. -/
structure BipartiteRepairResult {V : Type u} [Fintype V] (G : SimpleGraph V) where
  Vertex : Type u
  vertices : Fintype Vertex
  inhabited : Nonempty Vertex
  graph : SimpleGraph Vertex
  order_le : @Fintype.card Vertex vertices ≤ Fintype.card V
  min_degree : letI := vertices; ∀ v, 3 ≤ graph.degree v
  even_cycles : ∀ n, Even n →
    (∃ x, ∃ w : graph.Walk x x, w.IsCycle ∧ w.length = n) →
    ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = n

/-- A nonempty graph of minimum degree three repairs itself. -/
noncomputable def BipartiteRepairResult.identity {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hd : ∀ v, 3 ≤ G.degree v) : BipartiteRepairResult G where
  Vertex := V
  vertices := inferInstance
  inhabited := inferInstance
  graph := G
  order_le := le_rfl
  min_degree := hd
  even_cycles := fun _ _ h => h

example (G : SimpleGraph (Fin 4)) (hd : ∀ v, 3 ≤ G.degree v) :
    (BipartiteRepairResult.identity G hd).graph = G := rfl

example : Nonempty (BipartiteRepairResult (⊤ : SimpleGraph (Fin 4))) := by
  have hd : ∀ v : Fin 4, 3 ≤ (⊤ : SimpleGraph (Fin 4)).degree v := by decide
  refine ⟨BipartiteRepairResult.identity _ ?_⟩
  intro v
  convert hd v using 1
  congr 1
  exact Subsingleton.elim _ _

end Erdos64
