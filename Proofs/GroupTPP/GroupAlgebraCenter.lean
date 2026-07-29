import Mathlib

/-!
# The center of a group algebra: class sums and the conjugacy-class dimension count

This file proves that the center of a group algebra `k[G]` of a finite group `G`
over a commutative (semi)ring `k` is free with basis **the class sums**

  `classSum k x = ∑ g ∈ x.carrier, single g 1`   (`x : ConjClasses G`),

and deduces the dimension count

  `finrank k Z(k[G]) = Nat.card (ConjClasses G)`.

None of this exists in Mathlib (grounded 2026-07-12: no mention of
`Subalgebra.center`/`ConjClasses` in `Mathlib/Algebra/MonoidAlgebra/`) —
**upstream candidate**.

## Main definitions

* `GroupTPP.GroupAlgebraCenter.classSum` — the class sum of a conjugacy class in `k[G]`.
* `GroupTPP.GroupAlgebraCenter.classSumBasis` — the class sums as a
  `Basis (ConjClasses G) k (Subalgebra.center k (MonoidAlgebra k G))`.

## Main results

* `GroupTPP.GroupAlgebraCenter.mem_center_iff` — an element of `k[G]` is central iff
  its coefficient function is constant on conjugacy classes (no finiteness needed).
* `GroupTPP.GroupAlgebraCenter.finrank_center` — `finrank k Z(k[G]) = #ConjClasses G`
  for finite `G` (over any `k` satisfying the strong rank condition, e.g. any
  field or nontrivial commutative ring).

The consumption for representation theory (`#irreps = #conjugacy classes` over
`ℂ`) is `GroupTPP.CharDegrees.card_charDegrees`.
-/

open Module

namespace GroupTPP.GroupAlgebraCenter

open MonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Group G]

/-! ### Centrality is conjugation-invariance of coefficients -/

/-- **Membership characterization for the center of a group algebra**: an element
of `k[G]` is central iff its coefficient function is constant on conjugacy
classes. Holds for any group `G` (no finiteness) and any commutative semiring `k`. -/
theorem mem_center_iff {f : MonoidAlgebra k G} :
    f ∈ Subalgebra.center k (MonoidAlgebra k G) ↔ ∀ g h : G, f (h * g * h⁻¹) = f g := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro hf g h
    simpa using (congr($(hf (single h 1)) (h * g))).symm
  · intro hf b
    induction b using MonoidAlgebra.induction_linear with
    | zero => rw [zero_mul, mul_zero]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | single m r =>
      ext y
      rw [single_mul_apply, mul_single_apply, mul_comm]
      congr 1
      have h1 := hf (y * m⁻¹) m⁻¹
      rw [show m⁻¹ * (y * m⁻¹) * m⁻¹⁻¹ = m⁻¹ * y by group] at h1
      exact h1

/-- A central element of `k[G]` has equal coefficients at conjugate group
elements. -/
theorem apply_eq_of_mem_center_of_mk_eq {f : MonoidAlgebra k G}
    (hf : f ∈ Subalgebra.center k (MonoidAlgebra k G)) {a b : G}
    (hab : ConjClasses.mk a = ConjClasses.mk b) : f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab)
  exact (mem_center_iff.mp hf a c).symm

/-! ### Class sums -/

section ClassSum

variable (k) [Finite G]

/-- **The class sum** of a conjugacy class `x` of a finite group `G`: the sum
`∑ g ∈ x.carrier, single g 1` of the class's elements inside the group algebra
`k[G]`. -/
noncomputable def classSum (x : ConjClasses G) : MonoidAlgebra k G :=
  ∑ g ∈ x.carrier.toFinite.toFinset, MonoidAlgebra.single g 1

lemma classSum_apply_of_mk_eq {x : ConjClasses G} {g : G} (h : ConjClasses.mk g = x) :
    classSum k x g = 1 := by
  have hg : g ∈ x.carrier.toFinite.toFinset := by
    rw [Set.Finite.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq]
    exact h
  refine (Finsupp.finsetSum_apply _ _ _).trans
    ((Finset.sum_eq_single_of_mem g hg fun b _ hbg => ?_).trans ?_)
  · exact Finsupp.single_eq_of_ne' hbg
  · exact Finsupp.single_eq_same

lemma classSum_apply_of_mk_ne {x : ConjClasses G} {g : G} (h : ConjClasses.mk g ≠ x) :
    classSum k x g = 0 := by
  refine (Finsupp.finsetSum_apply _ _ _).trans (Finset.sum_eq_zero fun b hb => ?_)
  refine Finsupp.single_eq_of_ne' fun hbg => h ?_
  subst hbg
  rwa [Set.Finite.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq] at hb

/-- Class sums are central: their coefficient functions are the indicator
functions of conjugacy classes. -/
theorem classSum_mem_center (x : ConjClasses G) :
    classSum k x ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [mem_center_iff]
  intro g h
  have hmk : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm
  by_cases hx : ConjClasses.mk g = x
  · rw [classSum_apply_of_mk_eq k (hmk.trans hx), classSum_apply_of_mk_eq k hx]
  · rw [classSum_apply_of_mk_ne k fun hc => hx (by rwa [hmk] at hc),
      classSum_apply_of_mk_ne k hx]

/-- The class sum as an element of the center. -/
noncomputable def classSumCenter (x : ConjClasses G) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ⟨classSum k x, classSum_mem_center k x⟩

@[simp] lemma coe_classSumCenter (x : ConjClasses G) :
    (classSumCenter k x : MonoidAlgebra k G) = classSum k x := rfl

/-- A finite linear combination of class sums evaluates, at a group element `g`,
to the coefficient of the class of `g`. -/
lemma sum_smul_classSum_apply [Fintype (ConjClasses G)] (c : ConjClasses G → k) (g : G) :
    (∑ x, c x • classSum k x) g = c (ConjClasses.mk g) := by
  refine (Finsupp.finsetSum_apply _ _ _).trans
    ((Finset.sum_eq_single_of_mem (ConjClasses.mk g) (Finset.mem_univ _)
      fun b _ hb => ?_).trans ?_)
  · rw [MonoidAlgebra.smul_apply, classSum_apply_of_mk_ne k (Ne.symm hb), smul_zero]
  · rw [MonoidAlgebra.smul_apply, classSum_apply_of_mk_eq k rfl, smul_eq_mul, mul_one]

/-- The class sums are linearly independent in the center. -/
theorem linearIndependent_classSumCenter :
    LinearIndependent k (classSumCenter k (G := G)) := by
  letI := Fintype.ofFinite (ConjClasses G)
  rw [Fintype.linearIndependent_iffₛ]
  intro c c' hcc x
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
  have hcc' : ∑ x, c x • classSum k x = ∑ x, c' x • classSum k x := by
    simpa using congrArg Subtype.val hcc
  calc c (ConjClasses.mk g)
      = (∑ x, c x • classSum k x) g := (sum_smul_classSum_apply k c g).symm
    _ = (∑ x, c' x • classSum k x) g := by rw [hcc']
    _ = c' (ConjClasses.mk g) := sum_smul_classSum_apply k c' g

/-- The class sums span the center. -/
theorem span_classSumCenter :
    ⊤ ≤ Submodule.span k (Set.range (classSumCenter k (G := G))) := by
  letI := Fintype.ofFinite (ConjClasses G)
  obtain ⟨rep, hrep⟩ := ConjClasses.mk_surjective.hasRightInverse (f := ConjClasses.mk (α := G))
  rintro ⟨f, hf⟩ -
  have key : (⟨f, hf⟩ : Subalgebra.center k (MonoidAlgebra k G)) =
      ∑ x, f (rep x) • classSumCenter k x := by
    apply Subtype.ext
    have hcoe : ((∑ x, f (rep x) • classSumCenter k x :
        Subalgebra.center k (MonoidAlgebra k G)) : MonoidAlgebra k G) =
        ∑ x, f (rep x) • classSum k x := by
      simp
    rw [hcoe]
    ext g
    rw [sum_smul_classSum_apply k _ g]
    exact (apply_eq_of_mem_center_of_mk_eq hf (hrep (ConjClasses.mk g))).symm
  rw [key]
  exact Submodule.sum_mem _ fun x _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

/-- **The class-sum basis of the center of a group algebra**: for a finite group
`G`, the class sums `∑ g ∈ x.carrier, single g 1` (over the conjugacy classes
`x` of `G`) form a `k`-basis of the center of `k[G]`. -/
noncomputable def classSumBasis :
    Basis (ConjClasses G) k (Subalgebra.center k (MonoidAlgebra k G)) :=
  Basis.mk (linearIndependent_classSumCenter k) (span_classSumCenter k)

@[simp] lemma classSumBasis_apply (x : ConjClasses G) :
    (classSumBasis k (G := G) x : MonoidAlgebra k G) = classSum k x := by
  rw [classSumBasis, Basis.mk_apply, coe_classSumCenter]

end ClassSum

/-! ### The dimension count -/

/-- **The dimension of the center of a group algebra is the number of conjugacy
classes**: `finrank k Z(k[G]) = #ConjClasses G` for a finite group `G`, over any
commutative semiring `k` with the strong rank condition (e.g. any field, or any
nontrivial commutative ring). -/
theorem finrank_center (k G : Type*) [CommSemiring k] [StrongRankCondition k]
    [Group G] [Finite G] :
    Module.finrank k (Subalgebra.center k (MonoidAlgebra k G)) =
      Nat.card (ConjClasses G) := by
  letI := Fintype.ofFinite (ConjClasses G)
  rw [Module.finrank_eq_card_basis (classSumBasis k), Nat.card_eq_fintype_card]

end GroupTPP.GroupAlgebraCenter
