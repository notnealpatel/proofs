/-
  Scratch example: instantiate IsFullyCompressed.hasSunflower end-to-end.

  Family: all 9 singletons {{0},{1},...,{8}} on Fin 9, with k=1, s=2.
  Threshold: s^(2(s-1)) * 2^k = 2^2 * 2^1 = 8 < 9 = |F|.
  Conclusion: the family has a 2-sunflower.

  Uses the franklShiftC computable twin from Counterexample.lean and
  native_decide for the ground checks (compression stability, uniformity,
  cardinality bound).
-/

import Erdos.Erdos20.ShiftedSunflower
import Erdos.Erdos20.Counterexample

open Finset Erdos20Counterexample

-- Pin the same decidability instances as Counterexample.lean.
attribute [local instance 2000] Finset.decidableDforallFinset
  Finset.decidableExistsAndFinset

namespace SunflowerExample

/-- The family of all 9 singletons on Fin 9. -/
abbrev singletons9 : Finset (Finset (Fin 9)) :=
  { {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8} }

/-- The family is 1-uniform. -/
theorem singletons9_uniform : ∀ S ∈ singletons9, S.card = 1 := by
  native_decide

/-- The family has 9 members. -/
theorem singletons9_card : singletons9.card = 9 := by
  native_decide

/-- The family is fully compressed: every i < j shift fixes it.
    (All singletons are already minimal under Frankl compression.) -/
theorem singletons9_compressed : IsFullyCompressed singletons9 := by
  have h : ∀ i j : Fin 9, i < j → franklShiftC i j singletons9 = singletons9 := by
    native_decide
  intro i j hij
  rw [← franklShiftC_eq]
  exact h i j hij

/-- The cardinality exceeds the threshold: 2^(2*1) * 2^1 = 8 < 9. -/
theorem singletons9_threshold : 2 ^ (2 * (2 - 1)) * 2 ^ 1 < singletons9.card := by
  rw [singletons9_card]
  norm_num

/-- Main result: the nine singletons on Fin 9 have a 2-sunflower. -/
theorem singletons9_hasSunflower : HasSunflower singletons9 2 :=
  IsFullyCompressed.hasSunflower (by norm_num : 1 ≤ 2)
    singletons9_compressed singletons9_uniform singletons9_threshold

#print axioms singletons9_hasSunflower

end SunflowerExample
