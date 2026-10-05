import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

/-- A nodup list of at least three vertices, with adjacent consecutive vertices and a
closing edge to its head, determines an ordinary cycle of the same length. -/
theorem exists_cycle_of_nodup_list {V : Type*} (G : SimpleGraph V)
    (xs : List V) (hne : xs ≠ []) (hnodup : xs.Nodup)
    (hlen : 3 ≤ xs.length)
    (hchain : List.IsChain G.Adj (xs ++ [xs.head hne])) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = xs.length := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x ys =>
    let q := SimpleGraph.Walk.ofSupport (x :: (ys ++ [x]))
      ((ys ++ [x]).cons_ne_nil x) (by simpa using hchain)
    have hstart : (x :: (ys ++ [x])).head ((ys ++ [x]).cons_ne_nil x) = x := by
      simp
    have hend : (x :: (ys ++ [x])).getLast ((ys ++ [x]).cons_ne_nil x) = x := by
      simp
    let p : G.Walk x x := q.copy hstart hend
    have hs : p.support = x :: (ys ++ [x]) := by
      change (q.copy _ _).support = _
      rw [SimpleGraph.Walk.support_copy]
      exact SimpleGraph.Walk.support_ofSupport _ _
    have hl : p.length = (x :: ys).length := by
      have hsupportLength := p.length_support
      rw [hs] at hsupportLength
      simp only [List.length_cons, List.length_append, List.length_nil] at hsupportLength
      simp only [List.length_cons]
      omega
    have hnotnil : ¬ p.Nil := by
      intro hp
      have hz : p.length = 0 := hp.length_eq_zero
      rw [hl] at hz
      simp only [List.length_cons] at hlen hz
      omega
    have ht : p.tail.support = ys ++ [x] := by
      rw [SimpleGraph.Walk.support_tail_of_not_nil p hnotnil, hs]
      rfl
    have hn : (ys ++ [x]).Nodup := by
      have hperm : List.Perm (ys ++ [x]) (x :: ys) := by
        simp
      exact hperm.nodup_iff.mpr hnodup
    have hp : p.tail.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, ht]
      exact hn
    refine ⟨x, p, ?_, hl⟩
    exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨hp, by simpa only [hl] using hlen⟩

end Erdos64.UniqueCubicClawCenter
