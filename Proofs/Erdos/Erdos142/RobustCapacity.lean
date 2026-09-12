/-
  Erdos142/RobustCapacity — robust weighted local-capacity certificates.

  Local Roth-number bounds remain useful for sets containing progressions:
  each progression pays once in every patch containing its three vertices.
  A uniform bound on this weighted edge load turns the total payment into the
  canonical progression count from `ThreeAPCount`.

  This is finite counting infrastructure, not an asymptotic estimate for
  Erdős problem 142.
-/

import Erdos.Erdos142.ThreeAPCount
import Erdos.Erdos142.WeightedCapacity

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- The weighted load of a canonical progression edge is the total weight of
all indexed regions containing that edge. -/
def weightedThreeAPLoad {ι : Type*} (J : Finset ι) (C : ι → Finset ℕ)
    (weight : ι → ℝ) (e : Finset ℕ) : ℝ :=
  ∑ j ∈ J, if e ⊆ C j then weight j else 0

/-- Ground truth with overlapping patches: the edge `{0, 1, 2}` has load five
when it lies in patches of weights two and three. -/
example :
    weightedThreeAPLoad ({0, 1} : Finset (Fin 2))
      (fun _ => ({0, 1, 2} : Finset ℕ))
      (fun j => if j = 0 then (2 : ℝ) else 3) {0, 1, 2} = 5 := by
  norm_num [weightedThreeAPLoad]

/-- Restricting a finite set by `C` restricts its canonical progression edges
exactly to the edges contained in `C`. -/
theorem threeAPEdges_inter (A C : Finset ℕ) :
    threeAPEdges (A ∩ C) = (threeAPEdges A).filter fun e => e ⊆ C := by
  ext e
  rw [Finset.mem_filter, mem_threeAPEdges, mem_threeAPEdges]
  constructor
  · rintro ⟨heAC, hecard, hefree⟩
    exact ⟨⟨fun x hx => (Finset.mem_inter.mp (heAC hx)).1, hecard, hefree⟩,
      fun x hx => (Finset.mem_inter.mp (heAC hx)).2⟩
  · rintro ⟨⟨heA, hecard, hefree⟩, heC⟩
    exact ⟨fun x hx => Finset.mem_inter.mpr ⟨heA hx, heC hx⟩, hecard, hefree⟩

/-- Weighted progression incidences can be counted either patch by patch or
edge by edge. -/
theorem sum_weighted_threeAPCount_eq {ι : Type*} (A : Finset ℕ)
    (J : Finset ι) (C : ι → Finset ℕ) (weight : ι → ℝ) :
    (∑ j ∈ J, weight j * (threeAPCount (A ∩ C j) : ℝ)) =
      ∑ e ∈ threeAPEdges A, weightedThreeAPLoad J C weight e := by
  calc
    (∑ j ∈ J, weight j * (threeAPCount (A ∩ C j) : ℝ)) =
        ∑ j ∈ J, ∑ e ∈ threeAPEdges A,
          if e ⊆ C j then weight j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [threeAPCount, threeAPEdges_inter, mul_comm,
              ← Finset.sum_filter]
            simp
    _ = ∑ e ∈ threeAPEdges A, ∑ j ∈ J,
          if e ⊆ C j then weight j else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ e ∈ threeAPEdges A, weightedThreeAPLoad J C weight e := by
          rfl

/-- A robust weighted local-capacity certificate. Local Roth bounds control
progression-free remainders, while each progression of `A` pays at most `M`
through the weighted family of patches. -/
theorem card_le_robust_weighted_local_capacity {ι : Type*}
    (U A : Finset ℕ) (J : Finset ι) (C : ι → Finset ℕ)
    (weight : ι → ℝ) (R : ι → ℕ) (M : ℝ)
    (hAU : A ⊆ U) (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hlocal : ∀ j ∈ J, addRothNumber (U ∩ C j) ≤ R j)
    (hedge : ∀ e ∈ threeAPEdges U, weightedThreeAPLoad J C weight e ≤ M) :
    (A.card : ℝ) ≤
      (∑ j ∈ J, weight j * (R j : ℝ)) +
        ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 +
          M * (threeAPCount A : ℝ) := by
  let capacity : ι → ℕ := fun j => R j + threeAPCount (A ∩ C j)
  have hcap : ∀ j ∈ J, (A ∩ C j).card ≤ capacity j := by
    intro j hj
    have hsubset : A ∩ C j ⊆ U ∩ C j := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hAU (Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp hx).2⟩
    calc
      (A ∩ C j).card ≤ addRothNumber (U ∩ C j) +
          threeAPCount (A ∩ C j) :=
        card_le_addRothNumber_add_threeAPCount hsubset
      _ ≤ R j + threeAPCount (A ∩ C j) :=
        Nat.add_le_add_right (hlocal j hj) _
      _ = capacity j := rfl
  have hcapacity := card_le_weighted_local_capacity
    U A J C weight capacity hAU hweight hcap
  have hedgeA : ∀ e ∈ threeAPEdges A,
      weightedThreeAPLoad J C weight e ≤ M := by
    intro e he
    apply hedge e
    rw [mem_threeAPEdges] at he ⊢
    exact ⟨he.1.trans hAU, he.2⟩
  have hincidence :
      (∑ j ∈ J, weight j * (threeAPCount (A ∩ C j) : ℝ)) ≤
        M * (threeAPCount A : ℝ) := by
    rw [sum_weighted_threeAPCount_eq]
    calc
      (∑ e ∈ threeAPEdges A, weightedThreeAPLoad J C weight e) ≤
          ∑ _e ∈ threeAPEdges A, M := Finset.sum_le_sum hedgeA
      _ = M * (threeAPCount A : ℝ) := by
        simp [threeAPCount, mul_comm]
  have hsplit :
      (∑ j ∈ J, weight j * (capacity j : ℝ)) =
        (∑ j ∈ J, weight j * (R j : ℝ)) +
          ∑ j ∈ J, weight j * (threeAPCount (A ∩ C j) : ℝ) := by
    simp only [capacity, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [hsplit] at hcapacity
  calc
    (A.card : ℝ) ≤
        ((∑ j ∈ J, weight j * (R j : ℝ)) +
          ∑ j ∈ J, weight j * (threeAPCount (A ∩ C j) : ℝ)) +
            ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 := hcapacity
    _ = ((∑ j ∈ J, weight j * (R j : ℝ)) +
          ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0) +
            ∑ j ∈ J, weight j * (threeAPCount (A ∩ C j) : ℝ) := by
      ring
    _ ≤ (∑ j ∈ J, weight j * (R j : ℝ)) +
          ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 +
            M * (threeAPCount A : ℝ) :=
      add_le_add_right hincidence _

/-- Covered specialization of the robust certificate. If every point of `U`
has load at least one, the point-defect term vanishes. -/
theorem card_le_robust_weighted_local_capacity_of_covered {ι : Type*}
    (U A : Finset ℕ) (J : Finset ι) (C : ι → Finset ℕ)
    (weight : ι → ℝ) (R : ι → ℕ) (M : ℝ)
    (hAU : A ⊆ U) (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hlocal : ∀ j ∈ J, addRothNumber (U ∩ C j) ≤ R j)
    (hedge : ∀ e ∈ threeAPEdges U, weightedThreeAPLoad J C weight e ≤ M)
    (hcovered : ∀ x ∈ U, 1 ≤ weightedLoad J C weight x) :
    (A.card : ℝ) ≤
      (∑ j ∈ J, weight j * (R j : ℝ)) + M * (threeAPCount A : ℝ) := by
  have hbound := card_le_robust_weighted_local_capacity
    U A J C weight R M hAU hweight hlocal hedge
  have hdefect : (∑ x ∈ U, max (1 - weightedLoad J C weight x) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [max_eq_right (sub_nonpos.mpr (hcovered x hx))]
  simpa only [hdefect, add_zero] using hbound

/-- Threshold contrapositive: if `A` is larger than the robust certificate
with an allowance of `T` progression edges, then `A` has more than `T`
canonical progressions. -/
theorem lt_threeAPCount_of_robust_weighted_capacity_lt_card {ι : Type*}
    (U A : Finset ℕ) (J : Finset ι) (C : ι → Finset ℕ)
    (weight : ι → ℝ) (R : ι → ℕ) (M : ℝ) (T : ℕ)
    (hAU : A ⊆ U) (hweight : ∀ j ∈ J, 0 ≤ weight j)
    (hlocal : ∀ j ∈ J, addRothNumber (U ∩ C j) ≤ R j)
    (hedge : ∀ e ∈ threeAPEdges U, weightedThreeAPLoad J C weight e ≤ M)
    (hM : 0 < M)
    (hlarge :
      (∑ j ∈ J, weight j * (R j : ℝ)) +
        ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 + M * (T : ℝ) <
          (A.card : ℝ)) :
    T < threeAPCount A := by
  by_contra hnot
  have hcount : threeAPCount A ≤ T := Nat.le_of_not_gt hnot
  have hmul : M * (threeAPCount A : ℝ) ≤ M * (T : ℝ) := by
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount) (le_of_lt hM)
  have hbound := card_le_robust_weighted_local_capacity
    U A J C weight R M hAU hweight hlocal hedge
  have hupper :
      (A.card : ℝ) ≤
        (∑ j ∈ J, weight j * (R j : ℝ)) +
          ∑ x ∈ U, max (1 - weightedLoad J C weight x) 0 + M * (T : ℝ) :=
    hbound.trans (add_le_add_right hmul _)
  exact (not_lt_of_ge hupper) hlarge

/-- Joint satisfiability check with two overlapping patches. Both patches
contain `{0, 1, 2}`, their half-weights cover every point, and the unique edge
has total load one. -/
example :
    let U : Finset ℕ := {0, 1, 2}
    let A : Finset ℕ := {0, 1, 2}
    let J : Finset (Fin 2) := {0, 1}
    let C : Fin 2 → Finset ℕ := fun _ => U
    let weight : Fin 2 → ℝ := fun _ => 1 / 2
    let R : Fin 2 → ℕ := fun _ => 2
    weightedThreeAPLoad J C weight {0, 1, 2} = 1 ∧
      (∀ x ∈ U, 1 ≤ weightedLoad J C weight x) ∧
        (A.card : ℝ) ≤
          (∑ j ∈ J, weight j * (R j : ℝ)) + 1 * (threeAPCount A : ℝ) := by
  dsimp only
  have hcovered : ∀ x ∈ ({0, 1, 2} : Finset ℕ),
      1 ≤ weightedLoad ({0, 1} : Finset (Fin 2))
        (fun _ => ({0, 1, 2} : Finset ℕ)) (fun _ => (1 : ℝ) / 2) x := by
    intro x hx
    have hxU : x = 0 ∨ x = 1 ∨ x = 2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    norm_num [weightedLoad, hxU]
  refine ⟨by norm_num [weightedThreeAPLoad], hcovered, ?_⟩
  apply card_le_robust_weighted_local_capacity_of_covered
  · exact Finset.Subset.rfl
  · norm_num
  · intro j hj
    have hcard : addRothNumber ({0, 1, 2} ∩ ({0, 1, 2} : Finset ℕ)) ≤ 2 := by
      decide
    exact hcard
  · intro e he
    have hesub : e ⊆ ({0, 1, 2} : Finset ℕ) :=
      (mem_threeAPEdges.mp he).1
    norm_num [weightedThreeAPLoad, hesub]
  · exact hcovered

#check @weightedThreeAPLoad
#check @threeAPEdges_inter
#check @sum_weighted_threeAPCount_eq
#check @card_le_robust_weighted_local_capacity
#check @card_le_robust_weighted_local_capacity_of_covered
#check @lt_threeAPCount_of_robust_weighted_capacity_lt_card

#print axioms threeAPEdges_inter
#print axioms sum_weighted_threeAPCount_eq
#print axioms card_le_robust_weighted_local_capacity
#print axioms card_le_robust_weighted_local_capacity_of_covered
#print axioms lt_threeAPCount_of_robust_weighted_capacity_lt_card

end Erdos142
