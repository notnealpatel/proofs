import GroupTPP.CharDegreesRestriction
import GroupTPP.CharDegreesMultiplicity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.ENat.BigOperators

set_option autoImplicit false

noncomputable section
namespace GroupTPP.CharDegreesBranching

/-- Restricting any complex group-algebra module along the actual subgroup inclusion
preserves compatibility with its complex vector-space structure. -/
theorem restriction_tower {L : Type*} [Group L] (K : Subgroup L)
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ L) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ L) M] :
    letI := Module.compHom M
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
    IsScalarTower ℂ (MonoidAlgebra ℂ K) M := by
  let phi := MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype
  letI := Module.compHom M phi.toRingHom
  apply IsScalarTower.of_algebraMap_smul
  intro z x
  change phi (algebraMap ℂ (MonoidAlgebra ℂ K) z) • x = z • x
  rw [phi.commutes, algebraMap_smul]

/-- Every isotypic component of a genuinely restricted finite-dimensional module
has finite length, so taking its natural length never discards infinity. -/
theorem restricted_isotypicLength_ne_top {L : Type*} [Group L] (K : Subgroup L)
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ L) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ L) M] [FiniteDimensional ℂ M]
    (T : Type*) [AddCommGroup T] [Module (MonoidAlgebra ℂ K) T] :
    letI := Module.compHom M
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
    Module.length (MonoidAlgebra ℂ K)
      (isotypicComponent (MonoidAlgebra ℂ K) M T) ≠ ⊤ := by
  letI := Module.compHom M
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
  letI := restriction_tower K M
  letI : IsArtinian (MonoidAlgebra ℂ K) M := isArtinian_of_tower ℂ inferInstance
  letI : IsNoetherian (MonoidAlgebra ℂ K) M := isNoetherian_of_tower ℂ inferInstance
  exact Module.length_ne_top

/-- The natural multiplicity of a simple subgroup type in the restricted regular
module is the subgroup index times its multiplicity in the subgroup regular module.
This is the coset side of the branching column identity, without assuming a matrix. -/
theorem regularRestriction_isotypicLength {L : Type*} [Group L] [Finite L]
    (K : Subgroup L) (T : Type*) [AddCommGroup T]
    [Module (MonoidAlgebra ℂ K) T] [IsSimpleModule (MonoidAlgebra ℂ K) T] :
    letI := Module.compHom (MonoidAlgebra ℂ L)
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
    (Module.length (MonoidAlgebra ℂ K)
      (isotypicComponent (MonoidAlgebra ℂ K) (MonoidAlgebra ℂ L) T)).toNat =
      K.index * (Module.length (MonoidAlgebra ℂ K)
        (isotypicComponent (MonoidAlgebra ℂ K) (MonoidAlgebra ℂ K) T)).toNat := by
  classical
  letI := Fintype.ofFinite L
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel K))
  letI := Module.compHom (MonoidAlgebra ℂ L)
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype).toRingHom
  have hfinite : Module.length (MonoidAlgebra ℂ K)
      (isotypicComponent (MonoidAlgebra ℂ K) (MonoidAlgebra ℂ K) T) ≠ ⊤ := by
    letI : IsArtinian (MonoidAlgebra ℂ K) (MonoidAlgebra ℂ K) :=
      isArtinian_of_tower ℂ inferInstance
    letI : IsNoetherian (MonoidAlgebra ℂ K) (MonoidAlgebra ℂ K) :=
      isNoetherian_of_tower ℂ inferInstance
    exact Module.length_ne_top
  have hlength := CharDegreesMultiplicity.isotypicLength_eq (T := T)
    (CharDegreesRestriction.regularRestrictionEquiv K).symm
  rw [hlength, CharDegreesMultiplicity.isotypicLength_pi]
  rw [ENat.toNat_sum (fun _ _ => hfinite)]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, CharDegreesRestriction.card_rightCosets]

example :
    letI := Module.compHom (MonoidAlgebra ℂ PUnit.{1})
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (⊥ : Subgroup PUnit.{1}).subtype).toRingHom
    IsScalarTower ℂ (MonoidAlgebra ℂ (⊥ : Subgroup PUnit.{1}))
      (MonoidAlgebra ℂ PUnit.{1}) := restriction_tower _ _

end GroupTPP.CharDegreesBranching

