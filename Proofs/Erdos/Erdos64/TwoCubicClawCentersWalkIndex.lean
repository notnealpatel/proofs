import Erdos.Erdos64.TwoCubicClawCentersSmallCycle

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph

universe u

/-- A simple closed walk has an injective cyclic vertex indexing with adjacent consecutive terms. -/
theorem walk_cycle_index {W : Type u} {K : SimpleGraph W} {a : W} (p : K.Walk a a) (hp : p.IsCycle) :
    ∃ m : ℕ, p.length = m + 1 ∧ 3 ≤ m + 1 ∧
      ∃ c : Fin (m + 1) → W, Function.Injective c ∧
        ∀ i, K.Adj (c i) (c (i + 1)) := by
  have hlen : 3 ≤ p.length := hp.three_le_length
  let m := p.length - 1
  have hm : p.length = m + 1 := by
    dsimp only [m]
    omega
  let c : Fin (m + 1) → W := fun i => p.getVert i.val
  have hc : Function.Injective c := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn' (show i.val ≤ p.length - 1 by omega)
      (show j.val ≤ p.length - 1 by omega)
    exact hij
  refine ⟨m, hm, hm ▸ hlen, c, hc, ?_⟩
  intro i
  have hi : i.val < p.length := by omega
  have hone : (1 : Fin (m + 1)).val = 1 := by
    change 1 % (m + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hn : i.val + 1 < p.length
  · have ha := p.adj_getVert_succ (i := i.val) hi
    change K.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin (m + 1)).val)
    simpa only [Fin.val_add, hone,
      Nat.mod_eq_of_lt (show i.val + 1 < m + 1 by omega)] using ha
  · have he : i.val + 1 = p.length := by omega
    have hz : (i + 1 : Fin (m + 1)).val = 0 := by
      simp only [Fin.val_add, hone, ← hm, he, Nat.mod_self]
    have ha := p.adj_getVert_succ hi
    change K.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin (m + 1)).val)
    simpa only [hz, p.getVert_zero, he, p.getVert_length] using ha


end Erdos64.TwoCubicClawCentersQuotient
