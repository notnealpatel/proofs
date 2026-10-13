import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.GroupTheory.Index
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

noncomputable section
namespace GroupTPP
namespace CharDegreesRestriction

variable {G : Type*} [Group G] (A : Subgroup G)

/-- Unique right-coset coordinates express a group element as a subgroup element
multiplied on the right by the chosen coset representative. -/
private def cosetEquiv : (Quotient (QuotientGroup.rightRel A) × A) ≃ G where
  toFun p := (p.2 : G) * p.1.out
  invFun g := (Quotient.mk'' g, ⟨g * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel A)).out⁻¹,
    (QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq (Quotient.mk'' g))))⟩)
  left_inv p := by
    have hq : (Quotient.mk'' ((p.2 : G) * p.1.out) : Quotient (QuotientGroup.rightRel A)) = p.1 := by
      rw [← Quotient.out_eq p.1]
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simpa using A.inv_mem p.2.property
    apply Prod.ext
    · exact hq
    · apply Subtype.ext
      simp only [hq]
      simp
  right_inv g := by simp

/-- Reindexing the complex delta basis by right-coset coordinates is a linear equivalence. -/
private def coefficientEquiv [Finite G] :
    (Quotient (QuotientGroup.rightRel A) → MonoidAlgebra ℂ A) ≃ₗ[ℂ] MonoidAlgebra ℂ G :=
  ((Finsupp.linearEquivFunOnFinite ℂ (MonoidAlgebra ℂ A) _).symm.trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℂ))).trans
    (((Finsupp.curryLinearEquiv ℂ).symm.trans (Finsupp.domLCongr (cosetEquiv A))).trans
      (MonoidAlgebra.coeffLinearEquiv ℂ).symm)

/-- The coefficient reindexing is the sum of the included coefficients times their
right-coset representatives. -/
private theorem coefficientEquiv_formula [Finite G]
    (u : Quotient (QuotientGroup.rightRel A) → MonoidAlgebra ℂ A) :
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel A))
    coefficientEquiv A u = ∑ q, (MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype) (u q) *
      MonoidAlgebra.single q.out 1 := by
  classical
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel A))
  suffices h : ∀ f : Quotient (QuotientGroup.rightRel A) →₀ MonoidAlgebra ℂ A,
      coefficientEquiv A (f : _ → _) = ∑ q,
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype) (f q) * MonoidAlgebra.single q.out 1 by
    exact h ((Finsupp.linearEquivFunOnFinite ℂ (MonoidAlgebra ℂ A) _).symm u)
  intro f
  induction f using Finsupp.induction_linear with
  | zero =>
      change coefficientEquiv A 0 = _
      simp
  | add f g hf hg =>
      simp only [Finsupp.coe_add, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
      exact congrArg₂ (· + ·) hf hg
  | single q b =>
      induction b using MonoidAlgebra.induction_on with
      | of a =>
          simp [coefficientEquiv, Finsupp.uncurry_single, Finsupp.equivMapDomain_eq_mapDomain,
            cosetEquiv, MonoidAlgebra.of, MonoidAlgebra.mapDomainAlgHom,
            MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.single_mul_single, Finsupp.single_apply,
            apply_ite]
      | add b c hb hc =>
          simp only [Finsupp.single_add, map_add, Finsupp.coe_add, Pi.add_apply,
            add_mul, Finset.sum_add_distrib] at *
          exact congrArg₂ (· + ·) hb hc
      | smul z b hb =>
          simp only [← Finsupp.smul_single, Finsupp.coe_smul, map_smul,
            Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum] at *
          exact congrArg (z • ·) hb

/-- Inversion identifies the number of right cosets with the subgroup index. -/
theorem card_rightCosets : Nat.card (Quotient (QuotientGroup.rightRel A)) = A.index :=
  Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel A)

/-- Restriction of the regular group algebra uses the genuine inclusion action. -/
noncomputable def regularRestrictionEquiv [Finite G] :
    letI := Module.compHom (MonoidAlgebra ℂ G)
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype).toRingHom
    (Quotient (QuotientGroup.rightRel A) → MonoidAlgebra ℂ A) ≃ₗ[MonoidAlgebra ℂ A]
      MonoidAlgebra ℂ G := by
  classical
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel A))
  let phi := MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype
  letI := Module.compHom (MonoidAlgebra ℂ G) phi.toRingHom
  exact { (coefficientEquiv A).toAddEquiv with
    map_smul' := fun b u => by
      change coefficientEquiv A (b • u) = phi b * coefficientEquiv A u
      rw [coefficientEquiv_formula, coefficientEquiv_formula, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      change phi (b * u q) * _ = phi b * (phi (u q) * _)
      rw [map_mul, mul_assoc] }

/-- The restricted action is compatible with the original complex scalar action. -/
theorem regularRestriction_tower :
    letI := Module.compHom (MonoidAlgebra ℂ G)
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype).toRingHom
    IsScalarTower ℂ (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ G) := by
  let phi := MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype
  letI := Module.compHom (MonoidAlgebra ℂ G) phi.toRingHom
  apply IsScalarTower.of_algebraMap_smul
  intro z x
  change phi (algebraMap ℂ (MonoidAlgebra ℂ A) z) * x = z • x
  rw [phi.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- The equivalence sends a coordinate family to the sum of its included coefficients
multiplied by the corresponding right-coset representatives. -/
theorem regularRestrictionEquiv_apply [Finite G]
    (u : Quotient (QuotientGroup.rightRel A) → MonoidAlgebra ℂ A) :
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel A))
    letI := Module.compHom (MonoidAlgebra ℂ G)
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype).toRingHom
    regularRestrictionEquiv A u = ∑ q,
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype) (u q) * MonoidAlgebra.single q.out 1 :=
  coefficientEquiv_formula A u

/-- A finite group's right-coset space is nonempty, so its subgroup index is positive. -/
theorem index_pos [Finite G] : 0 < A.index := by
  rw [← card_rightCosets A]
  letI : Nonempty (Quotient (QuotientGroup.rightRel A)) := ⟨Quotient.mk'' 1⟩
  exact Nat.card_pos

example : Nonempty (Quotient (QuotientGroup.rightRel (⊥ : Subgroup PUnit.{1}))) :=
  ⟨Quotient.mk'' 1⟩

example :
    letI := Module.compHom (MonoidAlgebra ℂ PUnit.{1})
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (⊥ : Subgroup PUnit.{1}).subtype).toRingHom
    Nonempty ((Quotient (QuotientGroup.rightRel (⊥ : Subgroup PUnit.{1})) →
      MonoidAlgebra ℂ (⊥ : Subgroup PUnit.{1})) ≃ₗ[MonoidAlgebra ℂ (⊥ : Subgroup PUnit.{1})]
        MonoidAlgebra ℂ PUnit.{1}) :=
  ⟨regularRestrictionEquiv (⊥ : Subgroup PUnit.{1})⟩

example :
    letI := Module.compHom (MonoidAlgebra ℂ PUnit.{1})
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (⊥ : Subgroup PUnit.{1}).subtype).toRingHom
    IsScalarTower ℂ (MonoidAlgebra ℂ (⊥ : Subgroup PUnit.{1})) (MonoidAlgebra ℂ PUnit.{1}) :=
  regularRestriction_tower (⊥ : Subgroup PUnit.{1})

example : Nat.card (Quotient (QuotientGroup.rightRel (⊥ : Subgroup PUnit.{1}))) =
    (⊥ : Subgroup PUnit.{1}).index := card_rightCosets _

end CharDegreesRestriction
end GroupTPP
