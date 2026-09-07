import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false

/-- Tripathi's nine-block 4-uniform family on eleven vertices, from
arXiv:1409.4610, §An Example. The paper's labels `1, …, 11` are shifted to
`0, …, 10`, respectively. -/
def witnessFour : Finset (Finset (Fin 11)) :=
  {{0, 1, 2, 3}, {0, 4, 5, 6}, {1, 4, 7, 8},
   {2, 5, 7, 9}, {3, 6, 8, 9}, {0, 7, 8, 10},
   {1, 5, 6, 10}, {2, 3, 4, 10}, {0, 1, 4, 9}}

/-- Tripathi's family has exactly nine distinct edges. -/
theorem witnessFour_card : witnessFour.card = 9 := by decide

/-- Every edge of Tripathi's family has exactly four vertices. -/
theorem witnessFour_uniform : ∀ A ∈ witnessFour, A.card = 4 := by decide

/-- Every two edges of Tripathi's family meet, including an edge with itself. -/
theorem witnessFour_intersecting :
    ∀ A ∈ witnessFour, ∀ B ∈ witnessFour, ¬ Disjoint A B := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- Each of the 165 three-element subsets of the eleven vertices misses an
edge of Tripathi's family. This kernel-`decide` certificate enumerates only
`powersetCard 3`, not all finite sets or families. -/
theorem witnessFour_triples :
    ∀ S ∈ (Finset.univ : Finset (Fin 11)).powersetCard 3,
      ∃ A ∈ witnessFour, Disjoint A S := by decide

example : ({0, 1, 2, 3} : Finset (Fin 11)) ∈ witnessFour := by decide
example : ({0, 1, 2, 3} : Finset (Fin 11)).card = 4 := by decide
example : ((Finset.univ : Finset (Fin 11)).powersetCard 3).card = 165 := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide
example : Nonempty (Fin 11) := ⟨0⟩

#check @witnessFour_card
#check @witnessFour_uniform
#check @witnessFour_intersecting
#check @witnessFour_triples
#print axioms witnessFour_card
#print axioms witnessFour_uniform
#print axioms witnessFour_intersecting
#print axioms witnessFour_triples
