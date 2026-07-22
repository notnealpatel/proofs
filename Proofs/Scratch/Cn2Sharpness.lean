/-
  Scratch/Cn2Sharpness — machine checks of the sharpness witnesses for
  the S2/S3 pair-conspiracy strata over F₂ (card Cn2).

  S3 (all three modes unequal, `a = b = c = 2`): the pair-sum count
  equals the largest of the three C2 bounds, so the conjunction
  `pair_bounds_of_ne` is sharp in max form; the SAME witness violates
  the additive strengthening (support nesting `supp u' ⊂ supp u`), so
  max — not `+` — is the right shape.

  S2 (modes 1, 2 unequal, mode 3 shared, `a = b = 2`, `c = 1`): the
  pair-sum count equals both C2 bounds, so `pair_bounds_shared₃` is
  sharp.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Data.ZMod.Basic
import Proofs.BilinearComplexity.Conspiracy

namespace Cn2Sharpness

open BilinearComplexity

/-! ## S3 witness: all three factor pairs unequal, `a = b = c = 2` -/

abbrev u : Fin 2 → ZMod 2 := ![1, 1]
abbrev u' : Fin 2 → ZMod 2 := ![1, 0]
abbrev v : Fin 2 → ZMod 2 := ![1, 0]
abbrev v' : Fin 2 → ZMod 2 := ![1, 1]
abbrev w : Fin 2 → ZMod 2 := ![1, 0]
abbrev w' : Fin 2 → ZMod 2 := ![1, 1]

/-- The witness sits in stratum S3: all six factors nonzero … -/
example : u ≠ 0 ∧ u' ≠ 0 ∧ v ≠ 0 ∧ v' ≠ 0 ∧ w ≠ 0 ∧ w' ≠ 0 := by decide

/-- … and all three factor pairs unequal. -/
example : u ≠ u' ∧ v ≠ v' ∧ w ≠ w' := by decide

/-- The three C2 bounds evaluate to `4, 2, 2` … -/
example : max (wt v * wt w) (wt v' * wt w') = 4
    ∧ max (wt u * wt w) (wt u' * wt w') = 2
    ∧ max (wt u * wt v) (wt u' * wt v') = 2 := by decide

/-- … and the pair-sum count achieves the largest of them:
`pair_bounds_of_ne` is sharp in max form. -/
example : nnz (triad u v w + triad u' v' w') = 4 := by decide

/-- The mode-1 supports are nested (`supp u' ⊆ supp u`) … -/
example : ∀ i, u' i ≠ 0 → u i ≠ 0 := by decide

/-- … and accordingly the additive strengthening fails at the same
witness: `4 < 1 + 4`. -/
example : nnz (triad u v w + triad u' v' w') < wt v * wt w + wt v' * wt w' := by
  decide

/-! ## S2 witness: modes 1, 2 unequal, mode 3 shared, `a = b = 2`, `c = 1` -/

abbrev e : Fin 1 → ZMod 2 := ![1]

/-- The shared mode-3 factor is nonzero (modes 1, 2 as above). -/
example : e ≠ 0 := by decide

/-- Both S2 cross-mode bounds evaluate to `2` … -/
example : max (wt v * wt e) (wt v' * wt e) = 2
    ∧ max (wt u * wt e) (wt u' * wt e) = 2 := by decide

/-- … and the pair-sum count achieves them: `pair_bounds_shared₃` is
sharp. -/
example : nnz (triad u v e + triad u' v' e) = 2 := by decide

end Cn2Sharpness
