import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false
namespace Erdos64.BipartiteRepairFixtures
open SimpleGraph

/-- The Heawood incidence graph with a leaf 14 attached to point 0 and an isolated
vertex 15. It is disconnected and has defects of degree one and zero. -/
def disconnectedFixture : SimpleGraph (Fin 16) := fromRel fun x y =>
  (x.val < 7 ∧ 7 ≤ y.val ∧ y.val < 14 ∧
    ((y.val + 7 - x.val) % 7 = 0 ∨ (y.val + 7 - x.val) % 7 = 1 ∨
      (y.val + 7 - x.val) % 7 = 3)) ∨ (x = 0 ∧ y = 14)

instance : DecidableRel disconnectedFixture.Adj := by unfold disconnectedFixture; infer_instance

example : disconnectedFixture.Adj 0 14 := by decide
example : ∀ v, ¬ disconnectedFixture.Adj 15 v := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked certificates for the disconnected fixture: a proper coloring,
precisely two low vertices of degrees one and zero, and at most one common neighbor. -/
theorem disconnectedFixture_checks :
    (∀ x y, disconnectedFixture.Adj x y →
      decide (x.val < 7) ≠ decide (y.val < 7)) ∧
    disconnectedFixture.degree 14 = 1 ∧ disconnectedFixture.degree 15 = 0 ∧
    (∀ v, v ≠ 14 → v ≠ 15 → 3 ≤ disconnectedFixture.degree v) ∧
    (∀ a b, a ≠ b →
      (disconnectedFixture.neighborFinset a ∩ disconnectedFixture.neighborFinset b).card ≤ 1) ∧
    (Finset.univ.filter (fun v => disconnectedFixture.degree v ≤ 2)).card = 2 := by
  decide

end Erdos64.BipartiteRepairFixtures
