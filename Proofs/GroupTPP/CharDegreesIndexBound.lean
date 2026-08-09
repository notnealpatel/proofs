import GroupTPP.CharDegrees
import GroupTPP.CharDegreesComm
import GroupTPP.FDRepBridge

/-!
# Character degrees are bounded by the index of an abelian subgroup

This file proves **Huppert Prop. 2.6 / Isaacs Thm. 2.6** (absent from Mathlib,
upstream candidate): every irreducible complex character degree of a finite
group `G` is at most the index of any commutative subgroup `A ≤ G`.

## Main results

* `finrank_simple_le_index` — for `S` a simple `ℂ[G]`-submodule of the regular
  module and `A : Subgroup G` with `IsMulCommutative A`,
  `Module.finrank ℂ S ≤ A.index`.
* `charDegree_le_index_of_comm` — `c ∈ charDegrees G → c ≤ A.index` for
  commutative `A : Subgroup G`.

## Proof sketch (no induced representations)

Restrict scalars along `φ := MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype :
ℂ[A] →ₐ[ℂ] ℂ[G]` (the `ℂ[A]`-module structure on `S` is `Module.compHom` and
the single `IsScalarTower ℂ ℂ[A] S` instance is proved by hand).  Maschke makes
`S` semisimple over `ℂ[A]`, so it contains a simple `ℂ[A]`-submodule `W`; `W`
is `ℂ[A]`-isomorphic to an ideal `I` of `ℂ[A]`
(`IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`), and
`Module.finrank ℂ I = 1` because `I` sits inside its isotypic component, whose
length is an entry of `charDegrees A = {1, …, 1}`
(`GroupTPP.FDRepBridge.charDegrees_eq_simpleModuleDims` +
`GroupTPP.CharDegreesComm.charDegrees_of_commGroup`).  Hence `W = ℂ·v` for an
eigenvector `v ∈ S`: every `a ∈ A` acts on `v` by a scalar.

Simplicity of `S` over `ℂ[G]` gives `S = ℂ[G]·v`, so `S` is spanned over `ℂ`
by `{single g 1 * v : g ∈ G}`; since `single g 1 * v` depends on the coset
`g•A` only up to a scalar, the transversal `{single (Quotient.out x) 1 * v :
x : G ⧸ A}` of size `A.index` spans, and `finrank_span_finset_le_card` closes.

## Elaboration notes

The `Module.compHom`/`letI` context makes several instance unifications
elaboration-order sensitive (the `Submodule.addCommMonoid` vs
`(Submodule.addCommGroup _).toAddCommMonoid` diamond is defeq but fails when
checked against pending metavariables).  `IsSimpleModule.congr` is therefore
invoked with a fully explicit `@`-application, the rank-one generator is
extracted through a clean-context helper with the module pinned by `(V := W)`,
and `synthInstance.maxHeartbeats` is raised for the eigenvector lemma.

## References

* B. Huppert, *Endliche Gruppen I*, V.2.6.
* I. M. Isaacs, *Character Theory of Finite Groups*, Thm. 2.6 / Prob. 2.9
  (Ito's lemma context).
* CKSU FOCS'05 [arXiv:math/0511460], "basic facts" (tex 257–259): used for the
  abelian branch of `lemma:wreath-char-degrees`.
-/

open scoped IsMulCommutative
open GroupTPP.CharDegrees GroupTPP.FDRepBridge GroupTPP.CharDegreesComm

namespace GroupTPP.CharDegreesIndexBound

variable {G : Type*} [Group G] [Fintype G]

/-- Each isotypic length of the regular module is a member of `charDegrees`. -/
private theorem length_isotypic_mem_charDegrees (G : Type*) [Group G] [Fintype G]
    (c : ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) :
    (Module.length (MonoidAlgebra ℂ G) c.1).toNat ∈ charDegrees G := by
  unfold charDegrees GroupTPP.Wedderburn.isotypicLengthMultiset
  exact Multiset.mem_map.mpr ⟨c, by simp, rfl⟩

/-- Each member of `charDegrees` is the length of an isotypic component. -/
private theorem exists_isotypic_of_mem_charDegrees {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (hn : n ∈ charDegrees G) :
    ∃ c : ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
      (Module.length (MonoidAlgebra ℂ G) c.1).toNat = n := by
  unfold charDegrees GroupTPP.Wedderburn.isotypicLengthMultiset at hn
  obtain ⟨c, -, hc⟩ := Multiset.mem_map.mp hn
  exact ⟨c, hc⟩

/-- Clean-context generator extraction from `finrank ℂ V = 1`.  (Stated with the
scalars fixed to `ℂ` so that applying it inside a `letI`-heavy context needs no
flex-flex instance unification; see the module docstring.) -/
private theorem exists_generator_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : Module.finrank ℂ V = 1) : ∃ v : V, v ≠ 0 ∧ ∀ w : V, ∃ c : ℂ, c • v = w := by
  obtain ⟨v, h0, hs⟩ := finrank_eq_one_iff'.mp h
  exact ⟨v, h0, hs⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Common eigenvector for a commutative subgroup.**  A simple
`ℂ[G]`-submodule `S` of the regular module contains a nonzero vector `v` on
which every element of a commutative subgroup `A` acts by a scalar:
`single a 1 * v = c • v`.

This is the restriction-of-scalars half of Huppert Prop. 2.6: `S` viewed as a
`ℂ[A]`-module (via `MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype` and
`Module.compHom`) is semisimple by Maschke, its simple `ℂ[A]`-submodule is
`ℂ[A]`-isomorphic to an ideal of `ℂ[A]`, and all simple pieces of the
commutative semisimple algebra `ℂ[A]` are one-dimensional by the abelian
character-degree collapse (`charDegrees_of_commGroup` transported through
`charDegrees_eq_simpleModuleDims`). -/
private theorem exists_eigenvector (A : Subgroup G) [IsMulCommutative A]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] :
    ∃ v : MonoidAlgebra ℂ G, v ∈ S ∧ v ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, MonoidAlgebra.single (a : G) 1 * v = c • v := by
  haveI : Nontrivial ↥S := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ↥S
  haveI : NeZero (Nat.card ↥A : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : Fintype ↥A := Fintype.ofFinite _
  -- the restriction-of-scalars algebra map ℂ[A] →ₐ[ℂ] ℂ[G]
  set φ : MonoidAlgebra ℂ ↥A →ₐ[ℂ] MonoidAlgebra ℂ G :=
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ A.subtype with hφdef
  have hφsingle : ∀ b : ↥A, φ (MonoidAlgebra.single b 1) = MonoidAlgebra.single (b : G) 1 := by
    intro b
    simp [hφdef, MonoidAlgebra.mapDomainAlgHom_apply]
  -- S as a ℂ[A]-module, with the ℂ-, ℂ[A]-, ℂ[G]-actions aligned
  letI : Module (MonoidAlgebra ℂ ↥A) ↥S := Module.compHom ↥S φ.toRingHom
  letI : IsScalarTower ℂ (MonoidAlgebra ℂ ↥A) ↥S :=
    ⟨fun c z s => by
      show (φ (c • z)) • s = c • (φ z • s)
      rw [map_smul, smul_assoc]⟩
  -- a simple ℂ[A]-submodule W of S (Maschke: ℂ[A]-semisimplicity of S)
  obtain ⟨W, -, hW⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (⊤ : Submodule (MonoidAlgebra ℂ ↥A) ↥S)).resolve_left (by
        intro htop
        obtain ⟨x, hx⟩ := exists_ne (0 : ↥S)
        exact hx ((Submodule.eq_bot_iff _).mp htop x Submodule.mem_top))
  haveI := hW
  -- W is ℂ[A]-isomorphic to a (simple) ideal I of ℂ[A]
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (R := MonoidAlgebra ℂ ↥A) (M := ↥W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ ↥A) ↥I :=
    @IsSimpleModule.congr (MonoidAlgebra ℂ ↥A) _ ↥I (Submodule.addCommGroup I)
      (Submodule.module I) ↥W (Submodule.addCommGroup W) (Submodule.module W) e.symm hW
  -- finrank ℂ I = 1 via the abelian character-degree collapse
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
  -- extract the spanning vector and push the eigen-equations to ℂ[G]
  obtain ⟨w₀, hw₀0, hsp⟩ := exists_generator_of_finrank_eq_one (V := ↥W) hW1
  refine ⟨((w₀ : ↥S) : MonoidAlgebra ℂ G), (w₀ : ↥S).2, ?_, ?_⟩
  · simpa [ZeroMemClass.coe_eq_zero] using hw₀0
  · intro a
    obtain ⟨c, hc⟩ := hsp (((MonoidAlgebra.single a 1 : MonoidAlgebra ℂ ↥A) • w₀ : ↥W))
    refine ⟨c, ?_⟩
    calc MonoidAlgebra.single (a : G) 1 * ((w₀ : ↥S) : MonoidAlgebra ℂ G)
        = φ (MonoidAlgebra.single a 1) * ((w₀ : ↥S) : MonoidAlgebra ℂ G) := by
          rw [hφsingle]
      _ = (((MonoidAlgebra.single a 1 : MonoidAlgebra ℂ ↥A) • w₀ : ↥W) : MonoidAlgebra ℂ G) := rfl
      _ = ((c • w₀ : ↥W) : MonoidAlgebra ℂ G) := by rw [hc]
      _ = c • ((w₀ : ↥S) : MonoidAlgebra ℂ G) := rfl

/-- **Huppert Prop. 2.6, module side (upstream candidate).**  If `S` is a simple
`ℂ[G]`-submodule of the regular module of a finite group `G` and `A ≤ G` is a
commutative subgroup, then `Module.finrank ℂ S ≤ A.index`.

Proof: `S = ℂ[G]·v` for the common `A`-eigenvector `v` of
`exists_eigenvector`; since `single (g*a) 1 * v = c • (single g 1 * v)` for
`a ∈ A`, the images of the coset representatives `Quotient.out x`, `x : G ⧸ A`
already span `S` over `ℂ`, and there are `A.index` of them. -/
theorem finrank_simple_le_index (A : Subgroup G) [IsMulCommutative A]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] :
    Module.finrank ℂ S ≤ A.index := by
  classical
  obtain ⟨v, hvS, hv0, heig⟩ := exists_eigenvector A S
  haveI : Fintype (G ⧸ A) := Fintype.ofFinite _
  -- the transversal image {single (out x) 1 * v : x : G ⧸ A}
  set T : Finset (MonoidAlgebra ℂ G) :=
    Finset.univ.image (fun x : G ⧸ A => MonoidAlgebra.single x.out (1 : ℂ) * v)
  -- simplicity: S is the ℂ[G]-span of v
  have hSv : Submodule.span (MonoidAlgebra ℂ G) {v} = S := by
    rcases ((isSimpleModule_iff_isAtom.mp ‹_›).le_iff).mp
        ((Submodule.span_singleton_le_iff_mem v S).mpr hvS) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv0
    · exact h
  -- coset collapse: every single g 1 * v lies in the ℂ-span of the transversal image
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
  -- hence S ⊆ span ℂ T
  have hsub : ∀ x : MonoidAlgebra ℂ G, x ∈ S →
      x ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G)) := by
    intro x hx
    rw [← hSv] at hx
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hz, smul_eq_mul]
    refine MonoidAlgebra.induction_on
      (motive := fun w => w * v ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))) z
      (fun g => ?_) (fun p q hp hq => ?_) (fun r p hp => ?_)
    · simpa [MonoidAlgebra.of_apply] using hgen g
    · show (p + q) * v ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))
      rw [add_mul]
      exact add_mem hp hq
    · show (r • p) * v ∈ Submodule.span ℂ (T : Set (MonoidAlgebra ℂ G))
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hp
  -- close: finrank S ≤ finrank (span ℂ T) ≤ |T| ≤ |G ⧸ A| = A.index
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

/-- **Huppert Prop. 2.6 / Isaacs Thm. 2.6 (upstream candidate).**  Every
irreducible complex character degree of a finite group `G` is at most the index
of a commutative subgroup `A ≤ G`:
`c ∈ charDegrees G → c ≤ A.index`.

Via `charDegrees_eq_simpleModuleDims`, each entry of `charDegrees G` is the
`ℂ`-dimension of a simple `ℂ[G]`-submodule of the regular module, which
`finrank_simple_le_index` bounds by `A.index`. -/
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

end GroupTPP.CharDegreesIndexBound
