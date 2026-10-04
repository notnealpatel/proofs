import Mathlib.Combinatorics.SimpleGraph.Paths
import Erdos.Erdos64.BipartiteRepairFixtureChecks
import Erdos.Erdos64.BipartiteRepairDisconnectedFixtureChecks

set_option autoImplicit false
namespace Erdos64.BipartiteRepairFixtures
open SimpleGraph

/-- A graph with at most one common neighbor for each distinct pair has no genuine
cycle of length four. -/
theorem no_four_cycle_of_common_neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (h : ∀ a b, a ≠ b → (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1) :
    ¬ ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 4 := by
  rintro ⟨x,w,hw,hlen⟩
  have h13 : w.getVert 1 ≠ w.getVert 3 := by
    intro he
    have hi := hw.getVert_injOn (by simp [hlen]) (by simp [hlen]) he
    omega
  have h24 : w.getVert 2 ≠ w.getVert 4 := by
    intro he
    have hi := hw.getVert_injOn (by simp [hlen]) (by simp [hlen]) he
    omega
  have h12 := w.adj_getVert_succ (i := 1) (by omega)
  have h23 := w.adj_getVert_succ (i := 2) (by omega)
  have h34 := w.adj_getVert_succ (i := 3) (by omega)
  have h41 : G.Adj (w.getVert 4) (w.getVert 1) := by
    have he : w.getVert 4 = w.getVert 0 := by rw [← hlen, w.getVert_length, w.getVert_zero]
    rw [he]
    exact w.adj_getVert_succ (i := 0) (by omega)
  have hsubset : {w.getVert 2, w.getVert 4} ⊆ G.neighborFinset (w.getVert 1) ∩
      G.neighborFinset (w.getVert 3) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [h12,h23.symm]
    · simp [h41.symm,h34]
  have htwo : ({w.getVert 2, w.getVert 4} : Finset V).card = 2 := by simp [h24]
  have hle := (Finset.card_le_card hsubset).trans (h _ _ h13)
  omega

/-- The subdivided-Heawood fixture has no genuine four-cycle. -/
theorem adjacentFixture_no_four_cycle :
    ¬ ∃ x, ∃ w : adjacentFixture.Walk x x, w.IsCycle ∧ w.length = 4 := by
  exact no_four_cycle_of_common_neighbors _ adjacentFixture_checks.2.2.2.2

/-- All hypotheses of the full repair hold jointly for the adjacent-defect fixture. -/
theorem adjacentFixture_hypotheses :
    (∀ ⦃x y⦄, adjacentFixture.Adj x y →
      decide (x.val < 7 ∨ x = 15) ≠ decide (y.val < 7 ∨ y = 15)) ∧
    (¬ ∃ x, ∃ w : adjacentFixture.Walk x x, w.IsCycle ∧ w.length = 4) ∧
    (Finset.univ.filter (fun v => adjacentFixture.degree v ≤ 2)).card ≤ 2 ∧
    (∃ v, 3 ≤ adjacentFixture.degree v) := by
  refine ⟨fun {x y} h => adjacentFixture_checks.1 x y h,
    adjacentFixture_no_four_cycle, le_of_eq adjacentFixture_low_count, 0, ?_⟩
  exact adjacentFixture_checks.2.2.2.1 0 (by decide) (by decide)

/-- The disconnected leaf-plus-isolate fixture has no genuine four-cycle. -/
theorem disconnectedFixture_no_four_cycle :
    ¬ ∃ x, ∃ w : disconnectedFixture.Walk x x, w.IsCycle ∧ w.length = 4 := by
  exact no_four_cycle_of_common_neighbors _ disconnectedFixture_checks.2.2.2.2.1

/-- All hypotheses of the full repair hold jointly for a disconnected graph whose
exceptional vertices have degrees zero and one. -/
theorem disconnectedFixture_hypotheses :
    (∀ ⦃x y⦄, disconnectedFixture.Adj x y →
      decide (x.val < 7) ≠ decide (y.val < 7)) ∧
    (¬ ∃ x, ∃ w : disconnectedFixture.Walk x x, w.IsCycle ∧ w.length = 4) ∧
    (Finset.univ.filter (fun v => disconnectedFixture.degree v ≤ 2)).card ≤ 2 ∧
    (∃ v, 3 ≤ disconnectedFixture.degree v) := by
  refine ⟨fun {x y} h => disconnectedFixture_checks.1 x y h,
    disconnectedFixture_no_four_cycle, le_of_eq disconnectedFixture_checks.2.2.2.2.2, 0, ?_⟩
  exact disconnectedFixture_checks.2.2.2.1 0 (by decide) (by decide)

end Erdos64.BipartiteRepairFixtures
