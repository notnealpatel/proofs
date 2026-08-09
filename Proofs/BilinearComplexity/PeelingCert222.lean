/-
  BilinearComplexity/PeelingCert222 — certified exact minpeak of the Strassen
  2×2×2 decomposition over F_2 (Nc1).

  The canonical Strassen (1969) gauge has seven triads whose sum is
  `matMulTensor (ZMod 2) 2 2 2`, with vectors taken from
  `strassenU/V/W` in `Strassen.lean` (lines 44–77). Over F_2, signs
  disappear (−1 = 1), but the combinatorial structure persists.

  **Certified value**: `minPeakOverPerms T L = 10`, the minimum peak
  (j ≥ 1 convention) over all 7! = 5040 orderings of the 7 triads.
  This equals the orbit minimum under GL(2,F_2)^3 (CONTEXT EXACT),
  confirming the Strassen gauge is already optimal among sandwich gauges.

  Convention: j ≥ 1 (the j = 0 value nnz(T) = 8 is excluded from
  the peak; see Peeling.lean header).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.Peeling
import BilinearComplexity.Strassen
import Mathlib.Data.ZMod.Defs

namespace BilinearComplexity

/-- The Strassen decomposition as a `Decomp (ZMod 2) 4 4 4`: a list of
7 triads obtained by evaluating `strassenU/V/W` at each `s : Fin 7`.
Over `ZMod 2`, all signs collapse (`-1 = 1`), but the decomposition
identity holds. -/
abbrev strassenDecomp222 : Decomp (ZMod 2) 4 4 4 :=
  List.ofFn fun (s : Fin 7) =>
    (strassenU (ZMod 2) s, strassenV (ZMod 2) s, strassenW (ZMod 2) s)

set_option maxHeartbeats 1600000 in
/-- The Strassen triads sum to `matMulTensor (ZMod 2) 2 2 2`.
Certified by **kernel** `decide` (64-entry × 7-summand identity over F_2), so the
axiom closure stays inside `{propext, Classical.choice, Quot.sound}` — no
compiler trust. The raised heartbeat budget is for the elaborator's `Decidable`
evaluation; the kernel replays the same reduction. -/
theorem strassen_isDecomp_F2 :
    isDecompB (matMulTensor (ZMod 2) 2 2 2) strassenDecomp222 = true := by
  decide

/-- The exact minimum peak over all 5040 orderings of the 7 Strassen
triads is 10. This is the certified `minpeak` of the fixed Strassen
gauge over F_2. -/
theorem strassen_minpeak_F2 :
    minPeakOverPerms (matMulTensor (ZMod 2) 2 2 2) strassenDecomp222 = 10 := by
  native_decide

end BilinearComplexity
