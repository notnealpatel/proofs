import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false

namespace GroupTPP.CharDegreesMultiplicity

variable {R M N T : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup T]
  [Module R M] [Module R N] [Module R T] [IsSimpleModule R T]

/-- An ambient linear equivalence restricts to an equivalence of the components of a simple type. -/
def isotypicLinearEquiv (e : M ≃ₗ[R] N) :
    isotypicComponent R M T ≃ₗ[R] isotypicComponent R N T where
  toFun x := ⟨e x, e.toLinearMap.le_comap_isotypicComponent T x.property⟩
  invFun y := ⟨e.symm y, e.symm.toLinearMap.le_comap_isotypicComponent T y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' c x := Subtype.ext (e.map_smul c x)

example (e : M ≃ₗ[R] N) (x : isotypicComponent R M T) :
    ((isotypicLinearEquiv (T := T) e x : isotypicComponent R N T) : N) = e x := rfl

example (e : M ≃ₗ[R] N) (y : isotypicComponent R N T) :
    (((isotypicLinearEquiv (T := T) e).symm y : isotypicComponent R M T) : M) =
      e.symm y := rfl

/-- The extended-natural length of an isotypic component is invariant under ambient equivalence. -/
theorem isotypicLength_eq (e : M ≃ₗ[R] N) :
    Module.length R (isotypicComponent R M T) =
      Module.length R (isotypicComponent R N T) :=
  (isotypicLinearEquiv (T := T) e).length_eq

variable {ι : Type*} [Fintype ι]
  (A : ι → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

private theorem mem_isotypicComponent_pi (x : Π i, A i)
    (hx : ∀ i, x i ∈ isotypicComponent R (A i) T) :
    x ∈ isotypicComponent R (Π i, A i) T := by
  classical
  have hinj (i : ι) : (LinearMap.single R A i) (x i) ∈
      isotypicComponent R (Π i, A i) T :=
    (LinearMap.single R A i).le_comap_isotypicComponent T (hx i)
  have hsum : (∑ i, (LinearMap.single R A i) (x i)) ∈
      isotypicComponent R (Π i, A i) T :=
    Submodule.sum_mem _ (fun i _ => hinj i)
  have hreassemble : (∑ i, (LinearMap.single R A i) (x i)) = x := by
    ext j
    simp [LinearMap.single_apply]
  exact hreassemble ▸ hsum

/-- The isotypic component of a finite dependent product is the product of the coordinate components,
via coordinate restriction and reassembly, including the empty product. -/
def isotypicPiLinearEquiv :
    isotypicComponent R (Π i, A i) T ≃ₗ[R] Π i, isotypicComponent R (A i) T where
  toFun x i := ⟨x.val i,
    (LinearMap.proj i : (Π j, A j) →ₗ[R] A i).le_comap_isotypicComponent T x.property⟩
  invFun y := ⟨fun i => (y i).val, mem_isotypicComponent_pi A _ (fun i => (y i).property)⟩
  left_inv x := Subtype.ext rfl
  right_inv y := by
    funext i
    exact Subtype.ext rfl
  map_add' x y := by
    funext i
    exact Subtype.ext rfl
  map_smul' c x := by
    funext i
    exact Subtype.ext rfl

example (x : isotypicComponent R (Π i, A i) T) (i : ι) :
    ((isotypicPiLinearEquiv (T := T) A x i : isotypicComponent R (A i) T) : A i) =
      x.val i := rfl

example (y : Π i, isotypicComponent R (A i) T) (i : ι) :
    ((isotypicPiLinearEquiv (T := T) A).symm y).val i = (y i).val := rfl

/-- The extended-natural length of the component of a finite product is the sum of coordinate
component lengths; no finite-length assumption is needed. -/
theorem isotypicLength_pi :
    Module.length R (isotypicComponent R (Π i, A i) T) =
      ∑ i, Module.length R (isotypicComponent R (A i) T) := by
  calc
    Module.length R (isotypicComponent R (Π i, A i) T) =
        Module.length R (Π i, isotypicComponent R (A i) T) :=
      (isotypicPiLinearEquiv (T := T) A).length_eq
    _ = ∑ i, Module.length R (isotypicComponent R (A i) T) :=
      Module.length_pi_of_fintype R _

end GroupTPP.CharDegreesMultiplicity
