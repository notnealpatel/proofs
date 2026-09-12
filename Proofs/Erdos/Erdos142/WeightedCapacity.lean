/-
  Erdos142/WeightedCapacity — weighted local-capacity certificates.

  This file proves a finite double-counting bound.  A nonnegative weight is
  attached to each region, local cardinality bounds control the weighted
  incidence sum, and any load below one is paid for by an explicit defect
  term.  It also specializes the certificate to three-term-progression-free
  sets using Mathlib's `addRothNumber`.

  These results only provide certificate infrastructure.  In particular,
  they do not assert a numerical solution of Erdős problem 142.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- The load at `x` is the sum of the weights of the indexed regions
containing `x`. -/
def weightedLoad {α ι : Type*} [DecidableEq α] (J : Finset ι)
    (C : ι → Finset α) (weight : ι → ℝ) (x : α) : ℝ :=
  ∑ j ∈ J, if x ∈ C j then weight j else 0

/-- An empty family of regions gives every point load zero. -/
example (x : ℕ) :
    weightedLoad (∅ : Finset (Fin 0)) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) x = 0 := by
  simp [weightedLoad]

/-- Ground-truth check: a point in regions of weights two and three has
load five. -/
example :
    weightedLoad ({0, 1} : Finset (Fin 2))
      (fun _ => ({4} : Finset ℕ)) (fun j => if j = 0 then (2 : ℝ) else 3) 4 = 5 := by
  norm_num [weightedLoad]

section FiniteIncidence

variable {α ι : Type*} [DecidableEq α]

/-- Double-counting weighted incidences: summing point loads over a finite set
is the same as summing each region's weight times its intersection size. -/
theorem sum_weightedLoad_eq (A : Finset α) (J : Finset ι)
    (C : ι → Finset α) (weight : ι → ℝ) :
    (∑ x ∈ A, weightedLoad J C weight x) =
      ∑ j ∈ J, weight j * ((A ∩ C j).card : ℝ) := by
  unfold weightedLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]

/-- A weighted local-capacity certificate.  If `A ⊆ U`, each indexed region
contains at most `R j` points of `A`, and all region weights are nonnegative,
then `A` is bounded by weighted capacity plus the sum of the positive load
deficits on `U`. -/
theorem card_le_weighted_local_capacity (U A : Finset α) (J : Finset ι)
    (C : ι → Finset α) (weight : ι → ℝ) (R : ι → ℕ)
    (hAU : A ⊆ U) (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hcap : ∀ j ∈ J, (A ∩ C j).card ≤ R j) :
    (A.card : ℝ) ≤
      (∑ j ∈ J, weight j * (R j : ℝ)) +
        ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 := by
  have hpoint : ∀ x ∈ A, (1 : ℝ) ≤
      weightedLoad J C weight x + max (1 - weightedLoad J C weight x) 0 := by
    intro x hx
    have hsub : (1 : ℝ) - weightedLoad J C weight x ≤
        max (1 - weightedLoad J C weight x) 0 :=
      le_max_left _ _
    simpa only [sub_le_iff_le_add, add_comm] using hsub
  calc
    (A.card : ℝ) = ∑ x ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ A, (weightedLoad J C weight x +
        max (1 - weightedLoad J C weight x) 0) := Finset.sum_le_sum hpoint
    _ = (∑ x ∈ A, weightedLoad J C weight x) +
        ∑ x ∈ A, max (1 - weightedLoad J C weight x) 0 := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j ∈ J, weight j * ((A ∩ C j).card : ℝ)) +
        ∑ x ∈ A, max (1 - weightedLoad J C weight x) 0 := by
          rw [sum_weightedLoad_eq]
    _ ≤ (∑ j ∈ J, weight j * (R j : ℝ)) +
        ∑ x ∈ A, max (1 - weightedLoad J C weight x) 0 := by
          apply add_le_add
          · apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcap j hj)) (hweight j hj)
          · exact le_rfl
    _ ≤ (∑ j ∈ J, weight j * (R j : ℝ)) +
        ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 := by
          apply add_le_add
          · exact le_rfl
          · exact Finset.sum_le_sum_of_subset_of_nonneg hAU
              (fun x hxU hxA => le_max_right _ _)

/-- Covered variant of the weighted local-capacity certificate.  When every
point of `U` has load at least one, every deficit vanishes. -/
theorem card_le_weighted_local_capacity_of_covered (U A : Finset α) (J : Finset ι)
    (C : ι → Finset α) (weight : ι → ℝ) (R : ι → ℕ)
    (hAU : A ⊆ U) (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hcap : ∀ j ∈ J, (A ∩ C j).card ≤ R j)
    (hcovered : ∀ x ∈ U, 1 ≤ weightedLoad J C weight x) :
    (A.card : ℝ) ≤ ∑ j ∈ J, weight j * (R j : ℝ) := by
  have hbound := card_le_weighted_local_capacity U A J C weight R hAU hweight hcap
  have hdefect : (∑ x ∈ U, max (1 - weightedLoad J C weight x) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [max_eq_right (sub_nonpos.mpr (hcovered x hx))]
  simpa only [hdefect, add_zero] using hbound

/-- Satisfiability check for the generic and covered certificates: one point,
one region of weight one, and capacity one satisfy all hypotheses jointly. -/
example :
    (({0} : Finset ℕ).card : ℝ) ≤
      ∑ _ ∈ ({0} : Finset (Fin 1)), (1 : ℝ) * (↑(1 : ℕ) : ℝ) := by
  apply card_le_weighted_local_capacity_of_covered
    ({0} : Finset ℕ) ({0} : Finset ℕ) ({0} : Finset (Fin 1))
    (fun _ => ({0} : Finset ℕ)) (fun _ => (1 : ℝ)) (fun _ => 1)
  · exact Finset.Subset.rfl
  · simp
  · simp
  · simp [weightedLoad]

end FiniteIncidence

section ThreeAPFree

variable {α ι : Type*} [DecidableEq α] [AddMonoid α]

/-- A weighted certificate for a three-term-progression-free set.  The local
capacity assumptions are stated independently as upper bounds on Mathlib's
`addRothNumber` for `U ∩ C j`; no progression counter or solver is involved. -/
theorem threeAPFree_card_le_weighted_local_capacity
    (U A : Finset α) (J : Finset ι) (C : ι → Finset α)
    (weight : ι → ℝ) (R : ι → ℕ)
    (hAU : A ⊆ U) (hfree : ThreeAPFree (A : Set α))
    (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hlocal : ∀ j ∈ J, addRothNumber (U ∩ C j) ≤ R j) :
    (A.card : ℝ) ≤
      (∑ j ∈ J, weight j * (R j : ℝ)) +
        ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 := by
  apply card_le_weighted_local_capacity U A J C weight R hAU hweight
  intro j hj
  have hfree_inter : ThreeAPFree (↑(A ∩ C j) : Set α) := by
    apply hfree.mono
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  calc
    (A ∩ C j).card ≤ addRothNumber (U ∩ C j) := by
      apply hfree_inter.le_addRothNumber
      intro x hx
      have hxinter := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hAU hxinter.1, hxinter.2⟩
    _ ≤ R j := hlocal j hj

/-- Covered specialization for a three-term-progression-free set.  Explicit
local `addRothNumber` caps and point loads at least one give the certificate
without a deficit term. -/
theorem threeAPFree_card_le_weighted_local_capacity_of_covered
    (U A : Finset α) (J : Finset ι) (C : ι → Finset α)
    (weight : ι → ℝ) (R : ι → ℕ)
    (hAU : A ⊆ U) (hfree : ThreeAPFree (A : Set α))
    (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hlocal : ∀ j ∈ J, addRothNumber (U ∩ C j) ≤ R j)
    (hcovered : ∀ x ∈ U, 1 ≤ weightedLoad J C weight x) :
    (A.card : ℝ) ≤ ∑ j ∈ J, weight j * (R j : ℝ) := by
  have hbound := threeAPFree_card_le_weighted_local_capacity
    U A J C weight R hAU hfree hweight hlocal
  have hdefect : (∑ x ∈ U, max (1 - weightedLoad J C weight x) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [max_eq_right (sub_nonpos.mpr (hcovered x hx))]
  simpa only [hdefect, add_zero] using hbound

/-- Satisfiability check for the progression-free specialization over `ℕ`:
the singleton is progression-free and its singleton region has Roth number
at most one. -/
example :
    (({0} : Finset ℕ).card : ℝ) ≤
      ∑ _ ∈ ({0} : Finset (Fin 1)), (1 : ℝ) * (↑(1 : ℕ) : ℝ) := by
  apply threeAPFree_card_le_weighted_local_capacity_of_covered
    ({0} : Finset ℕ) ({0} : Finset ℕ) ({0} : Finset (Fin 1))
    (fun _ => ({0} : Finset ℕ)) (fun _ => (1 : ℝ)) (fun _ => 1)
  · exact Finset.Subset.rfl
  · simpa only [Finset.coe_singleton] using threeAPFree_singleton (0 : ℕ)
  · simp
  · intro _ _
    simp
  · simp [weightedLoad]

end ThreeAPFree

#check @sum_weightedLoad_eq
#check @card_le_weighted_local_capacity
#check @card_le_weighted_local_capacity_of_covered
#check @threeAPFree_card_le_weighted_local_capacity
#check @threeAPFree_card_le_weighted_local_capacity_of_covered

#print axioms sum_weightedLoad_eq
#print axioms card_le_weighted_local_capacity
#print axioms card_le_weighted_local_capacity_of_covered
#print axioms threeAPFree_card_le_weighted_local_capacity
#print axioms threeAPFree_card_le_weighted_local_capacity_of_covered

end Erdos142
