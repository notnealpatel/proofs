import Xlib

/-! # Axiom audit: shear-review remediation (T3 functional form, witness)

All new theorems should depend only on `propext, Classical.choice, Quot.sound`.
-/

#print axioms Xlib.ShearQuadraticRank.eq_of_eval_eq_of_totalDegree_lt
#print axioms Xlib.ShearQuadraticRank.polys_eq_of_run_eq
#print axioms Xlib.ShearQuadraticRank.lt_shearCount_of_not_sumOfProducts_run
#print axioms Xlib.ShearQuadraticRank.lt_shearCount_or_card_le_two_pow_of_run
#print axioms Xlib.ShearQuadraticRank.not_isSumOfProducts_one_quad
#print axioms Xlib.ShearQuadraticRank.two_le_shearCount_of_quad
#print axioms Xlib.TotalDegreeAeval.totalDegree_aeval_le_sup_vars
