import Xlib.CharDegreesComm
import Xlib.FDRepBridge

/-! # Ab2 probe (throwaway): CharDegreesIndexBound plumbing

Full draft of `finrank_simple_le_index` + `charDegree_le_index_of_comm`
to smoke out scalar-tower / coercion / instance issues before committing
to `Xlib/CharDegreesIndexBound.lean`. -/

open scoped IsMulCommutative
open Xlib.CharDegrees Xlib.FDRepBridge Xlib.CharDegreesComm

namespace Scratch.Ab2Probe

variable {G : Type*} [Group G] [Fintype G]

/-- Membership direction: each isotypic length is a member of `charDegrees`. -/
private theorem length_isotypic_mem_charDegrees (G : Type*) [Group G] [Fintype G]
    (c : ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) :
    (Module.length (MonoidAlgebra ℂ G) c.1).toNat ∈ charDegrees G := by
  unfold charDegrees Xlib.Wedderburn.isotypicLengthMultiset
  exact Multiset.mem_map.mpr ⟨c, by simp, rfl⟩

/-- Extraction direction: each member of `charDegrees` is an isotypic length. -/
private theorem exists_isotypic_of_mem_charDegrees {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (hn : n ∈ charDegrees G) :
    ∃ c : ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
      (Module.length (MonoidAlgebra ℂ G) c.1).toNat = n := by
  unfold charDegrees Xlib.Wedderburn.isotypicLengthMultiset at hn
  obtain ⟨c, -, hc⟩ := Multiset.mem_map.mp hn
  exact ⟨c, hc⟩

set_option backward.isDefEq.respectTransparency false in
/-- Phase 1: a simple `ℂ[G]`-submodule of the regular module contains a common
eigenvector for a commutative subgroup `A`. -/
private theorem exists_eigenvector (A : Subgroup G) [IsMulCommutative A]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] :
    ∃ v : MonoidAlgebra ℂ G, v ∈ S ∧ v ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, MonoidAlgebra.single (a : G) 1 * v = c • v := by
  haveI : Nontrivial ↥S := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ↥S
  haveI : NeZero (Nat.card ↥A : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : Fintype ↥A := Fintype.ofFinite _
  set φ : MonoidAlgebra ℂ ↥A →ₐ[ℂ] MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype with hφdef
  have hφsingle : ∀ b : ↥A, φ (MonoidAlgebra.single b 1) = MonoidAlgebra.single (b : G) 1 := by
    intro b
    simp [hφdef, MonoidAlgebra.mapDomainAlgHom_apply]
  letI : Module (MonoidAlgebra ℂ ↥A) ↥S := Module.compHom ↥S φ.toRingHom
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ ↥A) ↥S :=
    ⟨fun c z s => by
      show (φ (c • z)) • s = c • (φ z • s)
      rw [map_smul, smul_assoc]⟩
  obtain ⟨W, -, hW⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (⊤ : Submodule (MonoidAlgebra ℂ ↥A) ↥S)).resolve_left (by
        intro htop
        obtain ⟨x, hx⟩ := exists_ne (0 : ↥S)
        exact hx ((Submodule.eq_bot_iff _).mp htop x Submodule.mem_top))
  haveI := hW
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (R := MonoidAlgebra ℂ ↥A) (M := ↥W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ ↥A) ↥I := IsSimpleModule.congr e.symm
  have hmem : isotypicComponent (MonoidAlgebra ℂ ↥A) (MonoidAlgebra ℂ ↥A) ↥I
      ∈ isotypicComponents (MonoidAlgebra ℂ ↥A) (MonoidAlgebra ℂ ↥A) :=
    ⟨I, inferInstance, rfl⟩
  have hbridge := charDegrees_eq_simpleModuleDims (↥A) ⟨_, hmem⟩ I I.le_isotypicComponent
  have hmemdeg := length_isotypic_mem_charDegrees (↥A) ⟨_, hmem⟩
  rw [charDegrees_of_commGroup ↥A] at hmemdeg
  have hI1 : Module.finrank ℂ ↥I = 1 := by
    rw [← hbridge]
    exact Multiset.eq_of_mem_replicate hmemdeg
  have hW1 : Module.finrank ℂ ↥W = 1 := by
    rw [(e.restrictScalars ℂ).finrank_eq]
    exact hI1
  obtain ⟨w₀, hw₀0, hsp⟩ := finrank_eq_one_iff'.mp hW1
  refine ⟨((w₀ : ↥S) : MonoidAlgebra ℂ G), (w₀ : ↥S).2, ?_, ?_⟩
  · simpa [ZeroMemClass.coe_eq_zero] using hw₀0
  · intro a
    obtain ⟨c, hc⟩ := hsp ((MonoidAlgebra.single a 1 : MonoidAlgebra ℂ ↥A) • w₀)
    refine ⟨c, ?_⟩
    calc MonoidAlgebra.single (a : G) 1 * ((w₀ : ↥S) : MonoidAlgebra ℂ G)
        = φ (MonoidAlgebra.single a 1) * ((w₀ : ↥S) : MonoidAlgebra ℂ G) := by
          rw [hφsingle]
      _ = (((MonoidAlgebra.single a 1 : MonoidAlgebra ℂ ↥A) • w₀ : ↥W) : MonoidAlgebra ℂ G) := rfl
      _ = ((c • w₀ : ↥W) : MonoidAlgebra ℂ G) := by rw [hc]
      _ = c • ((w₀ : ↥S) : MonoidAlgebra ℂ G) := rfl

/-- Huppert Prop 2.6, module side. -/
theorem finrank_simple_le_index (A : Subgroup G) [IsMulCommutative A]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] :
    Module.finrank ℂ S ≤ A.index := by
  classical
  obtain ⟨v, hvS, hv0, heig⟩ := exists_eigenvector A S
  haveI : Fintype (G ⧸ A) := Fintype.ofFinite _
  set T : Finset (MonoidAlgebra ℂ G) :=
    Finset.univ.image (fun x : G ⧸ A => MonoidAlgebra.single x.out (1 : ℂ) * v) with hT
  have hSv : Submodule.span (MonoidAlgebra ℂ G) {v} = S := by
    rcases ((isSimpleModule_iff_isAtom.mp ‹_›).le_iff).mp
        ((Submodule.span_singleton_le_iff_mem v S).mpr hvS) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv0
    · exact h
  have hgen : ∀ g : G, MonoidAlgebra.single g (1 : ℂ) * v ∈
      Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G)) := by
    intro g
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A g
    obtain ⟨c, hc⟩ := heig a⁻¹
    have hg : (QuotientGroup.mk g : G ⧸ A).out * ((a⁻¹ : ↥A) : G) = g := by
      rw [ha]; simp
    have hsplit : MonoidAlgebra.single g (1 : ℂ) =
        MonoidAlgebra.single ((QuotientGroup.mk g : G ⧸ A).out) 1 *
          MonoidAlgebra.single ((a⁻¹ : ↥A) : G) 1 := by
      rw [MonoidAlgebra.single_mul_single, one_mul, hg]
    rw [hsplit, mul_assoc, hc, mul_smul_comm]
    exact Submodule.smul_mem _ c (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk g)))))
  have hsub : ∀ x : MonoidAlgebra ℂ G, x ∈ S →
      x ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G)) := by
    intro x hx
    rw [← hSv] at hx
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hz, smul_eq_mul]
    refine MonoidAlgebra.induction_on
      (p := fun w => w * v ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))) z
      (fun g => ?_) (fun p q hp hq => ?_) (fun r p hp => ?_)
    · simpa [MonoidAlgebra.of_apply] using hgen g
    · show (p + q) * v ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))
      rw [add_mul]
      exact add_mem hp hq
    · show (r • p) * v ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hp
  haveI : Module.Finite ℂ ↥(Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))) :=
    FiniteDimensional.span_of_finite ℂ T.finite_toSet
  have hle1 : Module.finrank ℂ ↥S ≤
      Module.finrank ℂ ↥(Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := { toFun := fun x : ↥S =>
                (⟨↑x, hsub ↑x x.2⟩ : ↥(Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G)))),
              map_add' := fun x y => rfl,
              map_smul' := fun c x => rfl }) ?_
    intro x y hxy
    have hval := congrArg
      (Subtype.val (p := fun m => m ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G)))) hxy
    exact Subtype.ext hval
  have hle2 : Module.finrank ℂ ↥(Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))) ≤ T.card := by
    simpa [Set.finrank] using finrank_span_finset_le_card T
  have hle3 : T.card ≤ A.index := by
    calc T.card ≤ (Finset.univ : Finset (G ⧸ A)).card := Finset.card_image_le
      _ = Fintype.card (G ⧸ A) := rfl
      _ = Nat.card (G ⧸ A) := Nat.card_eq_fintype_card.symm
      _ = A.index := rfl
  omega

/-- Huppert Prop 2.6: character degrees are at most the index of a commutative
subgroup. -/
theorem charDegree_le_index_of_comm (A : Subgroup G) [IsMulCommutative A]
    {c : ℕ} (hc : c ∈ charDegrees G) : c ≤ A.index := by
  obtain ⟨comp, hcomp⟩ := exists_isotypic_of_mem_charDegrees hc
  obtain ⟨Ssub, hSsimple, hSeq⟩ := comp.2
  haveI := hSsimple
  have hbridge := charDegrees_eq_simpleModuleDims G comp Ssub
    (by rw [hSeq]; exact Ssub.le_isotypicComponent)
  rw [hcomp] at hbridge
  rw [hbridge]
  exact finrank_simple_le_index A Ssub

end Scratch.Ab2Probe
