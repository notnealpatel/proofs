import Palomar.TPPFourierBarrier.Definitions

/-!
# The BCGPU Fourier barrier for triple-product-property triples

This challenge states Theorem 3.2 of Blasiak--Church--Cohn--Grochow--Umans for
one finite nonabelian group.  The invariant `minIrrepDimGTOne G` is formed from
the dimensions of the complex irreducible representations and deliberately
filters for dimensions strictly greater than one.  Thus nontrivial
one-dimensional characters do not determine the invariant.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Palomar.TPPFourierBarrier

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
  sorry

#check @tpp_card_product_le_fourier_barrier

end Palomar.TPPFourierBarrier
