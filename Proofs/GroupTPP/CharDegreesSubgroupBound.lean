import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Simple-module dimension bound from an invariant subgroup subspace

Coset representatives acting on a basis of a nonzero invariant subspace span
any simple submodule of the complex regular group algebra. No normality or
commutativity assumption on the subgroup is needed.
-/

set_option autoImplicit false

namespace GroupTPP.CharDegreesSubgroupBound

/-- A simple submodule of the complex regular algebra has dimension at most
`A.index` times the dimension of any nonzero complex subspace invariant under
`A`. Coset representatives acting on a basis of that subspace span the module. -/
theorem finrank_simple_le_index_mul_finrank
    {G : Type*} [Group G] [Fintype G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S]
    (A : Subgroup G) (W : Submodule ℂ S) (hW : W ≠ ⊥)
    (hinv : ∀ a : A, ∀ w : S, w ∈ W →
      (MonoidAlgebra.single (a : G) (1 : ℂ) • w) ∈ W) :
    Module.finrank ℂ S ≤ A.index * Module.finrank ℂ W := by
  classical
  haveI : Fintype (G ⧸ A) := Fintype.ofFinite _
  haveI : Module.Free ℂ W := Module.Free.of_divisionRing ℂ W
  let b := Module.finBasis ℂ W
  let T : Finset S := Finset.univ.image
    (fun p : (G ⧸ A) × Fin (Module.finrank ℂ W) =>
      MonoidAlgebra.single p.1.out (1 : ℂ) • (b p.2 : S))
  let U : Submodule ℂ S := Submodule.span ℂ (T : Set S)
  have hrep : ∀ (x : G ⧸ A) (w : W),
      MonoidAlgebra.single x.out (1 : ℂ) • (w : S) ∈ U := by
    intro x w
    let L : W →ₗ[ℂ] S :=
      { toFun := fun v => MonoidAlgebra.single x.out (1 : ℂ) • (v : S)
        map_add' := fun v u => smul_add _ _ _
        map_smul' := fun c v => smul_comm _ _ _ }
    change L w ∈ U
    rw [← b.sum_repr w, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    apply Submodule.smul_mem
    change MonoidAlgebra.single x.out (1 : ℂ) • (b i : S) ∈
      Submodule.span ℂ (T : Set S)
    have hmem : MonoidAlgebra.single x.out (1 : ℂ) • (b i : S) ∈ T :=
      Finset.mem_image.mpr ⟨(x, i), Finset.mem_univ _, rfl⟩
    exact Submodule.subset_span hmem
  have hgen : ∀ (g : G) (w : S), w ∈ W →
      MonoidAlgebra.single g (1 : ℂ) • w ∈ U := by
    intro g w hw
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A g
    have hg : (QuotientGroup.mk g : G ⧸ A).out * ((a⁻¹ : A) : G) = g := by
      rw [ha]
      simp
    have hsplit : MonoidAlgebra.single g (1 : ℂ) =
        MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ A).out 1 *
          MonoidAlgebra.single ((a⁻¹ : A) : G) 1 := by
      rw [MonoidAlgebra.single_mul_single, one_mul, hg]
    rw [hsplit, mul_smul]
    exact hrep (QuotientGroup.mk g)
      ⟨MonoidAlgebra.single ((a⁻¹ : A) : G) 1 • w, hinv a⁻¹ w hw⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hSw : Submodule.span (MonoidAlgebra ℂ G) {w} = ⊤ :=
    IsSimpleModule.span_singleton_eq_top (MonoidAlgebra ℂ G) hw0
  have hsub : ∀ s : S, s ∈ U := by
    intro s
    have hs : s ∈ Submodule.span (MonoidAlgebra ℂ G) {w} := by
      rw [hSw]
      exact Submodule.mem_top
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hs
    rw [← hz]
    refine MonoidAlgebra.induction_on
      (motive := fun p => p • w ∈ U) z
      (fun g => ?_) (fun p q hp hq => ?_) (fun c p hp => ?_)
    · simpa [MonoidAlgebra.of_apply] using hgen g w hw
    · rw [add_smul]
      exact U.add_mem hp hq
    · rw [smul_assoc]
      exact U.smul_mem c hp
  have hU : U = ⊤ := Submodule.eq_top_iff'.mpr hsub
  have hdim : Module.finrank ℂ S ≤ T.card := by
    have hbound : Module.finrank ℂ U ≤ T.card := by
      simpa [U, Set.finrank] using finrank_span_finset_le_card T
    have heq : Module.finrank ℂ U = Module.finrank ℂ S := by
      rw [hU]
      exact finrank_top ℂ S
    exact heq ▸ hbound
  have hcard : T.card ≤ A.index * Module.finrank ℂ W := by
    calc
      T.card ≤ (Finset.univ : Finset ((G ⧸ A) × Fin (Module.finrank ℂ W))).card :=
        Finset.card_image_le
      _ = Fintype.card (G ⧸ A) * Module.finrank ℂ W := by simp
      _ = A.index * Module.finrank ℂ W := by
        rw [← Nat.card_eq_fintype_card]
        rfl
  exact hdim.trans hcard

end GroupTPP.CharDegreesSubgroupBound
