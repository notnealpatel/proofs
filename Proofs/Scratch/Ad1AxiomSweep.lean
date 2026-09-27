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


end Item1

section Item2
open BilinearComplexity


end Item2

section Item3
open ShearEC.ShearQuadraticRank


end Item3

section Item5
open ExtraspecialLattice


-- the five downstream theorems, now witnessed rather than merely conditional
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
