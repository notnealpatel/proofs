import Sorry.GroupTPP.TPPProd

set_option autoImplicit false

namespace GroupTPP.TPP

/-- Padding a finite group by any finite group multiplies its TPP capacity
by at least the order of the padding group. -/
theorem tppCapacity_mul_card_le_prod
    {G A : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Group A] [Fintype A] [DecidableEq A] :
    tppCapacity G * Fintype.card A ≤ tppCapacity (G × A) := by
  classical
  unfold tppCapacity
  rw [Finset.sup_mul₀]
  refine Finset.sup_le fun p hp => ?_
  have htpp : TripleProductProperty p.1 p.2.1 p.2.2 := mem_tppTriples.mp hp
  have hle := le_tppCapacity (htpp.prod (tpp_trivial (G := A)))
  simpa only [tppCapacity, Finset.card_product, Finset.card_univ, Finset.card_singleton,
    mul_one, mul_assoc, mul_left_comm, mul_comm] using hle

end GroupTPP.TPP
