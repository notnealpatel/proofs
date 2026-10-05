import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

private lemma card_filter_range_step (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((Finset.range (n + 1)).filter P).card =
      ((Finset.range n).filter P).card + (if P n then 1 else 0) := by
  by_cases h : P n <;> simp [Finset.range_add_one, Finset.filter_insert, h]

/-- Counting a predicate on triples of consecutive slots splits into its three slot counts. -/
theorem card_filter_triples (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (3*k)).filter P).card =
      ((Finset.range k).filter (fun i => P (3*i))).card +
      ((Finset.range k).filter (fun i => P (3*i+1))).card +
      ((Finset.range k).filter (fun i => P (3*i+2))).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k + 1) = ((3 * k + 1) + 1) + 1 by omega]
    rw [card_filter_range_step, card_filter_range_step, card_filter_range_step,
      card_filter_range_step, card_filter_range_step, card_filter_range_step, ih]
    simp only [Nat.add_assoc]
    omega

/-- Counting a predicate on natural indices modulo a positive range agrees with counting on `Fin`. -/
theorem card_filter_range_mod (k : ℕ) (hk : 0 < k) (A : Fin k → Prop)
    [DecidablePred A] :
    ((Finset.range k).filter (fun i => A ⟨i % k, Nat.mod_lt i hk⟩)).card =
      (Finset.univ.filter A).card := by
  apply Finset.card_bij (fun i _ => (⟨i % k, Nat.mod_lt i hk⟩ : Fin k))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    have hi_lt : i < k := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj_lt : j < k := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hval := congrArg Fin.val hij
    simpa only [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] using hval
  · intro b hb
    have heq : (⟨b.val % k, Nat.mod_lt b.val hk⟩ : Fin k) = b := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt b.isLt
    refine ⟨b.val, ?_, heq⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr b.isLt, heq.symm ▸ (Finset.mem_filter.mp hb).2⟩

end Erdos64.TriangleIncidence
