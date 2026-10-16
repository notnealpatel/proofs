import GroupTPP.CharDegreesBranching

set_option autoImplicit false

noncomputable section

namespace GroupTPP.IsotypicDimension

/-- The dimension of an isotypic component is its finite composition length
multiplied by the dimension of its simple type. No semisimplicity of the ambient
module or algebra is required: the component itself is semisimple. -/
theorem finrank_isotypicComponent
    {F A M T : Type*} [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    [FiniteDimensional F M]
    [AddCommGroup T] [Module A T] [Module F T] [IsScalarTower F A T]
    [FiniteDimensional F T] [IsSimpleModule A T] :
    Module.finrank F (isotypicComponent A M T) =
      (Module.length A (isotypicComponent A M T)).toNat * Module.finrank F T := by
  classical
  letI : IsNoetherian A M := isNoetherian_of_tower F inferInstance
  have htype := IsIsotypicOfType.isotypicComponent A M T
  obtain ⟨m, ⟨e⟩⟩ := htype.linearEquiv_fun
  have hlength : Module.length A (isotypicComponent A M T) = (m : ℕ∞) := by
    rw [e.length_eq, Module.length_pi_of_fintype]
    simp [Module.length_eq_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hfinite : Module.length A (isotypicComponent A M T) ≠ ⊤ := by
    rw [hlength]
    exact ENat.natCast_ne_top m
  have hm : (Module.length A (isotypicComponent A M T)).toNat = m := by
    rw [hlength, ENat.toNat_natCast]
  rw [hm, (e.restrictScalars F).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- For genuine subgroup restriction, each simple subgroup type contributes its
complex dimension times its finite multiplicity to the restricted module. -/
theorem finrank_restricted_isotypicComponent
    {L : Type*} [Group L] (K : Subgroup L)
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ L) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ L) M] [FiniteDimensional ℂ M]
    (T : Type*) [AddCommGroup T] [Module ℂ T] [Module (MonoidAlgebra ℂ K) T]
    [IsScalarTower ℂ (MonoidAlgebra ℂ K) T] [FiniteDimensional ℂ T]
    [IsSimpleModule (MonoidAlgebra ℂ K) T] :
    letI := Module.compHom M
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
    letI := CharDegreesBranching.restriction_tower K M
    Module.finrank ℂ (isotypicComponent (MonoidAlgebra ℂ K) M T) =
      (Module.length (MonoidAlgebra ℂ K)
        (isotypicComponent (MonoidAlgebra ℂ K) M T)).toNat * Module.finrank ℂ T := by
  letI := Module.compHom M
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
  letI := CharDegreesBranching.restriction_tower K M
  exact finrank_isotypicComponent

example :
    Module.finrank ℂ (isotypicComponent ℂ ℂ ℂ) =
      (Module.length ℂ (isotypicComponent ℂ ℂ ℂ)).toNat * Module.finrank ℂ ℂ :=
  finrank_isotypicComponent

end GroupTPP.IsotypicDimension
