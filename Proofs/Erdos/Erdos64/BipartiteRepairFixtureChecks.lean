import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false
namespace Erdos64.BipartiteRepairFixtures
open SimpleGraph

/-- The Heawood incidence graph with edge 0--7 replaced by the path 0--14--15--7.
This supplies two adjacent degree-two defects, with all other degrees three. -/
def adjacentFixture : SimpleGraph (Fin 16) := fromRel fun x y =>
  (x.val < 7 ∧ 7 ≤ y.val ∧ y.val < 14 ∧
    ((y.val + 7 - x.val) % 7 = 0 ∨ (y.val + 7 - x.val) % 7 = 1 ∨
      (y.val + 7 - x.val) % 7 = 3) ∧ ¬ (x = 0 ∧ y = 7)) ∨
  (x = 0 ∧ y = 14) ∨ (x = 14 ∧ y = 15) ∨ (x = 15 ∧ y = 7)

instance : DecidableRel adjacentFixture.Adj := by unfold adjacentFixture; infer_instance

example : adjacentFixture.Adj 14 15 := by decide
example : ¬ adjacentFixture.Adj 0 7 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked color, degree, and common-neighbor certificates for the adjacent-defect fixture. -/
theorem adjacentFixture_checks : (∀ x y, adjacentFixture.Adj x y →
      decide (x.val < 7 ∨ x = 15) ≠ decide (y.val < 7 ∨ y = 15)) ∧
    adjacentFixture.degree 14 = 2 ∧ adjacentFixture.degree 15 = 2 ∧
    (∀ v, v ≠ 14 → v ≠ 15 → 3 ≤ adjacentFixture.degree v) ∧
    (∀ a b, a ≠ b →
      (adjacentFixture.neighborFinset a ∩ adjacentFixture.neighborFinset b).card ≤ 1) := by
  decide


/-- Exactly the two inserted subdivision vertices are low-degree. -/
theorem adjacentFixture_low_count :
    (Finset.univ.filter (fun v => adjacentFixture.degree v ≤ 2)).card = 2 := by
  decide

end Erdos64.BipartiteRepairFixtures
