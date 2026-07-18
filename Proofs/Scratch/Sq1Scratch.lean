import Mathlib
import Xlib.TPP
import Xlib.CUCapacity
import Xlib.STPPWreath

open Xlib.STPPWreath Xlib.CUCapacity Xlib.TPP

-- Can Lean infer Nontrivial (wreathGroup (n+1))?
example (n : ℕ) : Nontrivial (wreathGroup (n + 1)) := by
  apply Fintype.one_lt_card_iff_nontrivial.mp
  rw [Fintype.card_eq_nat_card]
  have h1 := ImprimitiveWreathProduct.card (cyclicGroup (n+1)) (n+1)
  have h2 : Nat.card (cyclicGroup (n+1)) = 2 * (n+1) := by
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
  rw [h2] at h1; rw [h1]
  calc 1 < 2 * (n + 1) := by omega
    _ ≤ (2 * (n + 1)) ^ (n + 1) := Nat.le_self_pow (by omega) _
    _ ≤ (2 * (n + 1)) ^ (n + 1) * (n + 1).factorial :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
