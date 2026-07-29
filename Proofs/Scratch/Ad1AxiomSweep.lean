import Enumerative
import BilinearComplexity.PeelingCert222
import BilinearComplexity.PeelingCert333
import ShearEC.ShearQuadraticRank
import GroupTPP.ExtraspecialLattice

/-!
# Ad1 axiom sweep

Per-item `#print axioms` checks for task card Ad1 (audit-debt burn-down).
"Clean" = a subset of `{propext, Classical.choice, Quot.sound}`.

Item 1 (Fubini kernel-clean swap), item 2 (decide downgrades), item 3
(ShearEC restatement + witness).
-/

set_option autoImplicit false

section Item1
open A051293

#print axioms fubini_succ_eq_sum_range
#print axioms fubini_zero
#print axioms fubini_one
#print axioms fubini_two
#print axioms fubini_three
#print axioms fubini_four
#print axioms fubini_five
#print axioms fubini_polylog
#print axioms S_expansion
#print axioms asymptotic_expansion
#print axioms leading_term
#print axioms cloitre_conjecture

end Item1

section Item2
open BilinearComplexity

#print axioms strassen_isDecomp_F2
#print axioms schoolbookDecomp333_length

end Item2

section Item3
open ShearEC.ShearQuadraticRank

#print axioms no_rank_one_factorization
#print axioms not_isSumOfProducts_one_quad
#print axioms two_le_shearCount_of_quad
#print axioms quadWitness_polys
#print axioms quadWitness_shearCount
#print axioms quadEmb_injective
#print axioms two_le_shearCount_of_quad_tight

end Item3

section Item5
open ExtraspecialLattice

#print axioms extraspecialD4
#print axioms card_D4Z
#print axioms finrank_D4V
#print axioms D4B_nondeg
#print axioms card_le_two_of_disjoint_D4Z
#print axioms exists_isotropic_of_disjoint_D4Z
#print axioms D4corr_card
#print axioms subgroupCount_D4_eq_fixedDim

-- the five downstream theorems, now witnessed rather than merely conditional
#check @card_le_of_disjoint_center
example {H : Subgroup D4} (hH : Disjoint H extraspecialD4.Z) :
    Nat.card H ≤ 2 ^ extraspecialD4.n :=
  card_le_of_disjoint_center extraspecialD4 hH
example {H : Subgroup D4} (hH : 2 ^ (extraspecialD4.n + 1) ≤ Nat.card H) :
    extraspecialD4.Z ≤ H :=
  center_le_of_card_ge extraspecialD4 hH
noncomputable example {k : ℕ} (hk : extraspecialD4.n + 1 ≤ k) :
    { H : Subgroup D4 // Nat.card H = 2 ^ k } ≃
      fixedDimSubspaces (ZMod 2) extraspecialD4.V (k - 1) :=
  upperSubgroupEquiv extraspecialD4 hk
-- elaboration/axiom-sweep check only: both sides instantiate at D4, so the
-- conclusion is a tautology; a meaningful instantiation needs a second rank-1
-- witness (Q8 companion, Ad1-burndown.md residual 1).
example {k : ℕ} (hk : extraspecialD4.n + 1 ≤ k) :
    subgroupCount D4 k = subgroupCount D4 k :=
  subgroupCount_eq_of_same_rank extraspecialD4 extraspecialD4 rfl hk

end Item5
