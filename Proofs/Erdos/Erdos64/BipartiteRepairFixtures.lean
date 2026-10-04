import Erdos.Erdos64.BipartiteRepair
import Erdos.Erdos64.BipartiteRepairCycleCertificate

set_option autoImplicit false
namespace Erdos64.BipartiteRepairFixtures
open SimpleGraph
open scoped Classical

/-- The full repair theorem applies to the subdivided Heawood graph with two
adjacent degree-two vertices. Its hypotheses are certified jointly. -/
theorem adjacentFixture_repair : Nonempty (BipartiteRepairResult adjacentFixture) := by
  exact BipartiteRepair.exists_repair adjacentFixture
    (fun x => decide (x.val < 7 ∨ x = 15))
    adjacentFixture_hypotheses.1 adjacentFixture_hypotheses.2.1
    adjacentFixture_hypotheses.2.2.1 adjacentFixture_hypotheses.2.2.2

/-- The full repair theorem also applies to the disconnected Heawood graph with
an attached leaf and an isolated vertex, so degrees one and zero are exercised. -/
theorem disconnectedFixture_repair : Nonempty (BipartiteRepairResult disconnectedFixture) := by
  exact BipartiteRepair.exists_repair disconnectedFixture
    (fun x => decide (x.val < 7))
    disconnectedFixture_hypotheses.1 disconnectedFixture_hypotheses.2.1
    disconnectedFixture_hypotheses.2.2.1 disconnectedFixture_hypotheses.2.2.2

/-- A concrete adjacent-defect application supplies a finite nonempty output of
order at most sixteen and minimum degree three, preserving every even genuine
cycle at exactly its original length when transported back to the fixture. -/
theorem adjacentFixture_output_contract :
    ∃ R : BipartiteRepairResult adjacentFixture,
      letI := R.vertices
      Nonempty R.Vertex ∧ Fintype.card R.Vertex ≤ 16 ∧
      (∀ v, 3 ≤ R.graph.degree v) ∧
      (∀ n, Even n →
        (∃ x, ∃ w : R.graph.Walk x x, w.IsCycle ∧ w.length = n) →
        ∃ x, ∃ w : adjacentFixture.Walk x x, w.IsCycle ∧ w.length = n) := by
  obtain ⟨R⟩ := adjacentFixture_repair
  refine ⟨R, R.inhabited, ?_, R.min_degree, R.even_cycles⟩
  simpa using R.order_le

/-- The disconnected degree-zero/degree-one application supplies the same full
output contract: nonempty, order at most sixteen, minimum degree three, and
exact-length lifting of every even genuine cycle. -/
theorem disconnectedFixture_output_contract :
    ∃ R : BipartiteRepairResult disconnectedFixture,
      letI := R.vertices
      Nonempty R.Vertex ∧ Fintype.card R.Vertex ≤ 16 ∧
      (∀ v, 3 ≤ R.graph.degree v) ∧
      (∀ n, Even n →
        (∃ x, ∃ w : R.graph.Walk x x, w.IsCycle ∧ w.length = n) →
        ∃ x, ∃ w : disconnectedFixture.Walk x x, w.IsCycle ∧ w.length = n) := by
  obtain ⟨R⟩ := disconnectedFixture_repair
  refine ⟨R, R.inhabited, ?_, R.min_degree, R.even_cycles⟩
  simpa using R.order_le

end Erdos64.BipartiteRepairFixtures
