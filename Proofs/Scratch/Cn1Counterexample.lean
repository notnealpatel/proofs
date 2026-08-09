/-
  Scratch/Cn1Counterexample — machine check of the support-nesting
  counterexample that kills the additive C2 bound (card Cn1).

  Over `ZMod 2`, `u = ![1,0]` and `u' = ![1,1]` are linearly
  independent with nested supports (`supp u ⊆ supp u'`).  With all
  complementary vectors `![1]`, the `i = 0` slice of
  `triad u v w + triad u' v' w'` cancels: `nnz = 1`, strictly below
  the additive target `wt v * wt w + wt v' * wt w' = 2`, while the
  proved max bound `max 1 1 = 1` is tight.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.ZMod.Basic
import BilinearComplexity.Conspiracy

namespace Cn1Counterexample

open BilinearComplexity

abbrev u : Fin 2 → ZMod 2 := ![1, 0]
abbrev u' : Fin 2 → ZMod 2 := ![1, 1]
abbrev e : Fin 1 → ZMod 2 := ![1]

/-- The pair is linearly independent over `ZMod 2` … -/
example : LinearIndependent (ZMod 2) ![u, u'] := by
  rw [LinearIndependent.pair_iff]
  decide

/-- … the supports are nested: `u` vanishes wherever `u'` does … -/
example : ∀ i, u' i = 0 → u i = 0 := by decide

/-- … the additive target would be `2` … -/
example : wt e * wt e + wt e * wt e = 2 := by decide

/-- … but the `i = 0` slice cancels, leaving a single nonzero entry. -/
example : nnz (triad u e e + triad u' e e) = 1 := by decide

/-- The proved C2 max bound is tight here: `max 1 1 = 1 ≤ 1`. -/
example : max (wt e * wt e) (wt e * wt e) = 1 := by decide

end Cn1Counterexample
