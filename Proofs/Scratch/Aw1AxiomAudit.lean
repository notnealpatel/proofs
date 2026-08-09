import GroupTPP.STPPWreath

/-! Aw1 axiom audit: the restated growing-base wreath theorem and its cyclic
instance must depend on exactly `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, no `Lean.ofReduceBool` (`native_decide`). The private `family*`
helpers are audited transitively through these two. -/

open GroupTPP.STPPWreath

#print axioms abelian_wreath_family_tendsto_two
#print axioms abelian_wreath_family_tendsto_two_cyclic
