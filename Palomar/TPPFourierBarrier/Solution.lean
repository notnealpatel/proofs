import GroupTPP.BCGPUBarrier

/-!
# Proof of the BCGPU Fourier barrier for TPP triples

This module repeats the challenge's ordinary definitions without importing the
challenge.  It identifies them with the repository's canonical character-degree
and triple-product-property definitions, then applies the proved source theorem
`GroupTPP.BCGPUBarrier.bcgpu_thm_3_2`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Palomar.TPPFourierBarrier

/-- Three finite subsets of a group have the triple product property when the
identity has only the diagonal representation as a product of their three left
quotients. -/
def TripleProductProperty {G : Type*} [Group G] (S T U : Finset G) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ t' ∈ T, ∀ u ∈ U, ∀ u' ∈ U,
    s'⁻¹ * s * t'⁻¹ * t * u'⁻¹ * u = 1 → s = s' ∧ t = t' ∧ u = u'

/-- The character-degree multiset of a finite group, represented canonically
by the composition lengths of the isotypic components of its complex group
algebra. -/
noncomputable def characterDegrees (G : Type*) [Group G] [Fintype G] : Multiset ℕ :=
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI : Fintype ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
    Fintype.ofFinite _
  (Finset.univ : Finset ↥(isotypicComponents (MonoidAlgebra ℂ G)
    (MonoidAlgebra ℂ G))).val.map fun c => (Module.length (MonoidAlgebra ℂ G) c.1).toNat

/-- `minIrrepDimGTOne G` is the least complex irreducible character degree
strictly greater than one, or zero when no such degree exists. -/
noncomputable def minIrrepDimGTOne (G : Type*) [Group G] [Fintype G] : ℕ :=
  ((characterDegrees G).filter (fun d => 1 < d)).toFinset.min.untopD 0

/-- Unfolding check for the ordinary isotypic-component definition of the
character-degree multiset. -/
theorem characterDegrees_eq_isotypic_lengths (G : Type*) [Group G] [Fintype G] :
    characterDegrees G =
      haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
      letI : Fintype ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
        Fintype.ofFinite _
      (Finset.univ : Finset ↥(isotypicComponents (MonoidAlgebra ℂ G)
        (MonoidAlgebra ℂ G))).val.map
          fun c => (Module.length (MonoidAlgebra ℂ G) c.1).toNat := rfl

/-- Unfolding check that the minimum discards all degree-one characters. -/
theorem minIrrepDimGTOne_eq_filtered_min (G : Type*) [Group G] [Fintype G] :
    minIrrepDimGTOne G =
      ((characterDegrees G).filter (fun d => 1 < d)).toFinset.min.untopD 0 := rfl

example : TripleProductProperty ({1} : Finset (Equiv.Perm (Fin 3))) {1} {1} := by
  simp [TripleProductProperty]

-- The hypotheses are jointly satisfiable in the nonabelian symmetric group on three letters.
example : (∃ a b : Equiv.Perm (Fin 3), a * b ≠ b * a) ∧
    TripleProductProperty ({1} : Finset (Equiv.Perm (Fin 3))) {1} {1} := by
  constructor
  · decide
  · simp [TripleProductProperty]

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
