import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace ErdosCandidates.E993

/-- The join of a ten-vertex clique with six isolated vertices. -/
def valleyGraph : SimpleGraph (Fin 16) where
  Adj x y := x ≠ y ∧ (x.val < 10 ∨ y.val < 10)
  symm.symm := by intro x y h; exact ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := by intro x h; exact h.1 rfl

instance : DecidableRel valleyGraph.Adj := fun _ _ => inferInstanceAs
  (Decidable (_ ≠ _ ∧ (_ < 10 ∨ _ < 10)))

example : valleyGraph.Adj 0 15 := by decide
example : ¬ valleyGraph.Adj 10 15 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- Kernel-checked counts on subsets of sizes one, two, and three for the
join of K₁₀ and six isolated vertices. Only 16, 120, and 560 subsets are tested. -/
theorem valleyGraph_certificate :
    ((Finset.univ.powersetCard 1).filter
      (fun s : Finset (Fin 16) => valleyGraphᶜ.IsClique s)).card = 16 ∧
    ((Finset.univ.powersetCard 2).filter
      (fun s : Finset (Fin 16) => valleyGraphᶜ.IsClique s)).card = 15 ∧
    ((Finset.univ.powersetCard 3).filter
      (fun s : Finset (Fin 16) => valleyGraphᶜ.IsClique s)).card = 20 := by
  decide

end ErdosCandidates.E993
