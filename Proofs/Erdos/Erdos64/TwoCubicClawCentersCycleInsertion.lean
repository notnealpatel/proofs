import Erdos.Erdos64.TwoCubicClawCentersContraction

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersContraction

open SimpleGraph

universe u

/-- Prepending a fresh vertex to an injective finite sequence preserves injectivity. -/
theorem cons_injective {A : Type u} {m : ℕ} (P : A) (d : Fin (m + 1) → A)
    (hd : Function.Injective d) (hfresh : ∀ i, P ≠ d i) :
    Function.Injective (Fin.cons P d) := by
  intro i j he
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact (hfresh j (by simpa only [Fin.cons_zero, Fin.cons_succ] using he)).elim
  | succ i =>
    cases j using Fin.cases with
    | zero => exact (hfresh i (by simpa only [Fin.cons_zero, Fin.cons_succ] using he.symm)).elim
    | succ j => exact congrArg Fin.succ (hd (by simpa only [Fin.cons_succ] using he))

/-- Prepending a vertex closes a simple ordered path into a cyclic adjacent sequence,
provided the new head joins both ends of the path. -/
theorem cons_cyclic_adj {A : Type u} (K : SimpleGraph A) {m : ℕ}
    (P : A) (d : Fin (m + 1) → A)
    (hfirst : K.Adj P (d 0))
    (hmiddle : ∀ i : Fin m, K.Adj (d i.castSucc) (d i.succ))
    (hlast : K.Adj (d (Fin.last m)) P) :
    ∀ i : Fin (m + 2), K.Adj (Fin.cons (α := fun _ : Fin (m + 2) => A) P d i) (Fin.cons (α := fun _ : Fin (m + 2) => A) P d (i + 1)) := by
  have hone : (1 : Fin (m + 2)).val = 1 := by
    change 1 % (m + 2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  intro i
  cases i using Fin.lastCases with
  | last =>
    have he : (Fin.last (m + 1) + 1 : Fin (m + 2)) = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_last, hone, Fin.val_zero, Nat.mod_self]
    rw [he]
    simpa only [show Fin.last (m + 1) = (Fin.last m).succ from rfl,
      Fin.cons_succ, Fin.cons_zero] using hlast
  | cast j =>
    have he : (j.castSucc + 1 : Fin (m + 2)) = j.succ := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_castSucc, hone, Fin.val_succ,
        Nat.mod_eq_of_lt (show j.val + 1 < m + 2 by omega)]
    rw [he]
    cases j using Fin.cases with
    | zero => simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hfirst
    | succ j =>
      change K.Adj (Fin.cons (α := fun _ : Fin (m + 2) => A) P d j.castSucc.succ) (Fin.cons (α := fun _ : Fin (m + 2) => A) P d j.succ.succ)
      simpa only [Fin.cons_succ] using hmiddle j

end Erdos64.TwoCubicClawCentersContraction
