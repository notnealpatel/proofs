import GroupTPP.STPPWreath

/-! Le1 axiom audit: every new declaration of the CU wreath TPP witness section
must depend on exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no `Lean.ofReduceBool` (`native_decide`). -/

open GroupTPP.STPPWreath

#print axioms cuVecU
#print axioms cuVecV
#print axioms wreathCocycleHom
#print axioms wreathCocycleHom_right
#print axioms wreathCocycleHom_left_apply
#print axioms wreathCocycleHom_injective
#print axioms wreathCocycleCarrier
#print axioms mem_wreathCocycleCarrier
#print axioms wreathCocycleCarrier_card
#print axioms wreathH₁_card
#print axioms wreathH₂_card
#print axioms wreathH₃_card
#print axioms perm_eq_one_of_two_mul_val_eq
#print axioms tripleProductProperty_wreathWitness
#print axioms factorial_pow_three_le_tppCapacity
