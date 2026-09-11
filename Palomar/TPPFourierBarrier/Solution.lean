import Palomar.TPPFourierBarrier.Definitions
import GroupTPP.BCGPUBarrier

/-!
# Proof of the BCGPU Fourier barrier for TPP triples

This module imports the challenge's shared declarations and identifies them with
the repository's canonical character-degree and triple-product-property
definitions, then applies the proved source theorem
`GroupTPP.BCGPUBarrier.bcgpu_thm_3_2`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Palomar.TPPFourierBarrier

/-- The package character degrees are definitionally the repository's canonical
character degrees. -/
theorem characterDegrees_eq_groupTPP (G : Type*) [Group G] [Fintype G] :
    characterDegrees G = GroupTPP.CharDegrees.charDegrees G := by
  rfl

/-- The package's strictly-greater-than-one minimum agrees with the invariant
used by the repository Fourier barrier. -/
theorem minIrrepDimGTOne_eq_groupTPP (G : Type*) [Group G] [Fintype G] :
    minIrrepDimGTOne G = GroupTPP.CharDegrees.minNontrivIrrepDim G := by
  rw [minIrrepDimGTOne, GroupTPP.CharDegrees.minNontrivIrrepDim,
    characterDegrees_eq_groupTPP]

/-- **BCGPU Theorem 3.2.** If `S`, `T`, and `U` have the triple product
property in a finite nonabelian group `G`, then their cardinality product is at
most `|G|^(3/2) / sqrt(n(G)) + |G|`, where `n(G)` is the least complex
irreducible dimension strictly greater than one. -/
theorem tpp_card_product_le_fourier_barrier {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {S T U : Finset G} (hG : ∃ a b : G, a * b ≠ b * a)
    (hTPP : TripleProductProperty S T U) :
    (S.card * T.card * U.card : ℝ) ≤
      (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) /
        Real.sqrt (minIrrepDimGTOne G : ℝ) + (Fintype.card G : ℝ) := by
  have hTPP' : GroupTPP.TPP.TripleProductProperty S T U := hTPP
  simpa only [GroupTPP.BCGPUBarrier.nG, minIrrepDimGTOne_eq_groupTPP] using
    GroupTPP.BCGPUBarrier.bcgpu_thm_3_2 hG hTPP'

#check @tpp_card_product_le_fourier_barrier
#print axioms Palomar.TPPFourierBarrier.tpp_card_product_le_fourier_barrier

end Palomar.TPPFourierBarrier
