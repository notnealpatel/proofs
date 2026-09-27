import Erdos.Covering.RankOfApparition

/-!
# Explicit axiom audit for `Erdos.Covering.RankOfApparition`

This explicitly built non-default validation leaf is not imported by production.
Build it explicitly to check the declarations listed below. It does not automatically guard
future production builds or declarations omitted from the list.
-/

set_option autoImplicit false

namespace Erdos.Covering

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Name :=
    [``fibPairShift, ``fibPairShift_apply, ``fibPairShift_pow_apply,
      ``exists_pos_dvd_fib, ``rankOfApparition, ``rankOfApparition_spec,
      ``rankOfApparition_pos, ``dvd_fib_rankOfApparition, ``rankOfApparition_le,
      ``rankOfApparition_eq_of, ``rankOfApparition_zero,
      ``dvd_fib_iff_rankOfApparition_dvd, ``IsFibonacciLike,
      ``IsFibonacciLike.apply_add_aux, ``IsFibonacciLike.apply_add,
      ``IsFibonacciLike.dvd_add_of_dvd, ``IsFibonacciLike.dvd_of_dvd_add,
      ``IsFibonacciLike.dvd_of_mod_eq, ``IsFibonacciLike.forall_mod_eq_dvd,
      ``IsFibonacciLike.dvd_head_of_dvd_succ,
      ``IsFibonacciLike.not_dvd_succ_of_dvd, ``not_dvd_zero_and_one_of_isCoprime,
      ``IsFibonacciLike.rankOfApparition_dvd, ``IsFibonacciLike.dvd_iff_mod_eq,
      ``IsFibonacciLike.setOf_dvd_eq_empty_or_residueClass, ``lucas,
      ``isFibonacciLike_lucas, ``rankOfApparition_two, ``rankOfApparition_three,
      ``rankOfApparition_four, ``rankOfApparition_five,
      ``IsFibonacciLike.setOf_dvd_eq_empty_of_forall_lt,
      ``setOf_dvd_lucas_five_eq_empty,
      ``exists_isFibonacciLike_setOf_dvd_eq_empty, ``setOf_dvd_lucas_three,
      ``setOf_dvd_fib_three, ``setOf_dvd_fib_three_ne_setOf_dvd_lucas_three,
      ``exists_isFibonacciLike_setOf_dvd_eq_residueClass,
      ``setOf_dvd_two_mul_fib_four,
      ``exists_not_prime_setOf_dvd_ne_empty_and_ne_residueClass,
      ``IsFibonacciLike.dvd_of_dvd_zero_of_dvd_one,
      ``IsFibonacciLike.setOf_dvd_eq_univ, ``univ_ne_setOf_mod_eq,
      ``exists_degenerate_setOf_dvd_ne_empty_and_ne_residueClass]
  let env ← getEnv
  for declaration in declarations do
    let some info := env.find? declaration
      | throwError "axiom audit declaration is missing: {declaration}"
    if let .axiomInfo _ := info then
      throwError "audited declaration is itself an axiom: {declaration}"
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unexpected axiom {axiomName}"
  logInfo m!"RankOfApparition axiom audit passed for {declarations.length} explicit declarations"

end Erdos.Covering
