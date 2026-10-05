import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

noncomputable local instance (V : Type*) : DecidableEq V := Classical.decEq V

private theorem exists_compressed_walk {V : Type*} (G : SimpleGraph V) (f : ℕ → V)
    (n : ℕ) (hstep : ∀ i, i < n → f i = f (i + 1) ∨ G.Adj (f i) (f (i + 1))) :
    ∃ q : G.Walk (f 0) (f n),
      q.length = ((List.range n).filter (fun i => decide (f i ≠ f (i + 1)))).length ∧
      q.support.dropLast = ((List.range n).filter (fun i => decide (f i ≠ f (i + 1)))).map f := by
  classical
  induction n with
  | zero => exact ⟨.nil, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨q, hlength, hsupport⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    by_cases heq : f n = f (n + 1)
    · refine ⟨q.copy rfl heq, ?_, ?_⟩
      · simpa [List.range_succ, List.filter_append, heq] using hlength
      · simpa [List.range_succ, List.filter_append, heq] using hsupport
    · have hadj : G.Adj (f n) (f (n + 1)) := (hstep n (Nat.lt_succ_self n)).resolve_left heq
      refine ⟨q.concat hadj, ?_, ?_⟩
      · simpa [List.range_succ, List.filter_append, heq] using hlength
      · simp only [SimpleGraph.Walk.support_concat, List.dropLast_append_cons,
          List.dropLast_singleton, List.append_nil]
        rw [← q.dropLast_support_concat, hsupport]
        simp [List.range_succ, List.filter_append, heq]

/-- A closed sequence whose steps are either stationary or graph edges contracts to a
simple cycle when its nonstationary departures are distinct and number at least three. -/
theorem exists_cycle_of_reflexive_sequence {V : Type*} (G : SimpleGraph V) (f : ℕ → V)
    (n : ℕ) (hclosed : f n = f 0)
    (hstep : ∀ i, i < n → f i = f (i + 1) ∨ G.Adj (f i) (f (i + 1)))
    (hinj : ∀ i j, i < n → j < n → f i ≠ f (i + 1) → f j ≠ f (j + 1) →
      f i = f j → i = j)
    (hlen : 3 ≤ ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card) :
    ∃ p : G.Walk (f 0) (f 0), p.IsCycle ∧
      p.length = ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card := by
  classical
  obtain ⟨q, hlength, hsupport⟩ := exists_compressed_walk G f n hstep
  have hcard : ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card =
      ((List.range n).filter (fun i => decide (f i ≠ f (i + 1)))).length := by
    simpa [List.toFinset_range] using List.toFinset_card_of_nodup
      ((List.nodup_range (n := n)).filter (fun i => decide (f i ≠ f (i + 1))))
  have hnodup : (((List.range n).filter (fun i => decide (f i ≠ f (i + 1)))).map f).Nodup := by
    apply List.Nodup.map_on _ ((List.nodup_range (n := n)).filter _)
    intro i hi j hj hij
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi hj
    exact hinj i j hi.1 hj.1 hi.2 hj.2 hij
  let p := q.copy rfl hclosed
  have hpLength : p.length = ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card := by
    simpa [p, hcard] using hlength
  have hpNodup : p.support.dropLast.Nodup := by
    simpa [p, hsupport] using hnodup
  refine ⟨p, SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, ?_⟩, hpLength⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [p.support_tail_of_not_nil (SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega))]
    exact p.tail_support_perm_dropLast_support.nodup_iff.mpr hpNodup
  · omega

end Erdos64.TriangleIncidence
