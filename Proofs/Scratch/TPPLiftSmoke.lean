import GroupTPP.TPPLift

/-! Smoke tests for the TPPLift census-decide path. Not part of the API. -/

open GroupTPP.TPP

-- C₂ ground facts are decide-checkable.
example : (sgn * sgn = 1) ∧ sgn ≠ 1 := by decide

-- The lift law instantiates at a concrete group.
example : stppCapacity (C₂ × DihedralGroup 3) =
    2 * max (stppCapacity (DihedralGroup 3)) (SigmaMaxLift (DihedralGroup 3)) :=
  stppCapacity_prod_eq_two_mul_max

-- Decidability of SignKilled on concrete data: ⊥-subgroups of S₃.
example : SignKilled (1 : (⊥ : Subgroup (DihedralGroup 3)) →* C₂)
    (1 : (⊥ : Subgroup (DihedralGroup 3)) →* C₂)
    (1 : (⊥ : Subgroup (DihedralGroup 3)) →* C₂) := by
  decide

-- liftTPP_iff_signKilled instantiates with A := C₂ on a concrete group.
example (χ : (⊥ : Subgroup (DihedralGroup 3)) →* C₂)
    [DecidablePred (· ∈ charLift χ)] :
    SubgroupTripleProductProperty (charLift χ) (charLift χ) (charLift χ) ↔
      SignKilled χ χ χ :=
  liftTPP_iff_signKilled χ χ χ
