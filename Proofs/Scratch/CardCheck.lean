import Mathlib
open scoped Pointwise

-- correct orientation (avoid motive issue by stating with explicit ker)
example {G : Type*} [Group G] (f : G →* G ⧸ N) (S : Subgroup G) (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker.relIndex S = Nat.card (S.map (QuotientGroup.mk' N)) :=
  Subgroup.relIndex_ker _

-- ker_mk' as a separate rewrite target works fine on its own
example {G : Type*} (N : Subgroup G) [Group G] [N.Normal] :
    (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N

-- key identity: relIndex N S * card (N ⊓ S) = card S  (finite)
example {G : Type*} [Group G] [Finite G] (N S : Subgroup G) :
    N.relIndex S * Nat.card (N ⊓ S : Subgroup G) = Nat.card S := by
  rw [Subgroup.relIndex, ← Subgroup.card_subgroupOf N S]
  exact Subgroup.index_mul_card (N.subgroupOf S)
