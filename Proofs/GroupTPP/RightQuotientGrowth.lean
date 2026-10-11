import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace GroupTPP.RightQuotientGrowth

/-- The finite right quotient consists of the products `x * y⁻¹`, not `x⁻¹ * y`. -/
noncomputable def rightQuotient {G : Type*} [Group G] (Y : Finset G) : Finset G := by
  classical
  exact (Y ×ˢ Y).image (fun p => p.1 * p.2⁻¹)

/-- Membership in the right quotient is witnessed by two elements of the original finset. -/
theorem mem_rightQuotient {G : Type*} [Group G] (Y : Finset G) (z : G) :
    z ∈ rightQuotient Y ↔ ∃ x ∈ Y, ∃ y ∈ Y, x * y⁻¹ = z := by
  classical
  simp only [rightQuotient, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hz⟩
    exact ⟨x, hx, y, hy, hz⟩
  · rintro ⟨x, hx, y, hy, hz⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hz⟩

/-- The carrier of a finite subgroup as a finset, without finiteness of the ambient group. -/
noncomputable def subgroupCarrier {G : Type*} [Group G] (X : Subgroup G) [Fintype X] :
    Finset G := by
  classical
  exact Finset.univ.image (fun x : X => (x : G))

/-- The finite carrier has exactly the subgroup's membership predicate. -/
theorem mem_subgroupCarrier {G : Type*} [Group G] (X : Subgroup G) [Fintype X] (x : G) :
    x ∈ subgroupCarrier X ↔ x ∈ X := by
  classical
  simp [subgroupCarrier]

/-- The carrier cardinality is the cardinality of the subgroup type. -/
theorem card_subgroupCarrier {G : Type*} [Group G] (X : Subgroup G) [Fintype X] :
    (subgroupCarrier X).card = Fintype.card X := by
  classical
  exact (Finset.card_image_of_injective _ Subtype.val_injective).trans Finset.card_univ

/-- Adjoining an element to a subgroup gives exactly three pieces in the right quotient. -/
theorem rightQuotient_insert {G : Type*} [Group G] (X : Subgroup G) [Fintype X]
    (c : G) :
    rightQuotient (insert c (subgroupCarrier X)) =
      subgroupCarrier X ∪ (subgroupCarrier X).image (fun x => c * x) ∪
        (subgroupCarrier X).image (fun x => x * c⁻¹) := by
  classical
  ext z
  rw [mem_rightQuotient]
  simp only [Finset.mem_union, Finset.mem_image, mem_subgroupCarrier]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inl (Or.inl (by simpa only [mul_inv_cancel] using X.one_mem))
      · exact Or.inl (Or.inr ⟨y⁻¹, X.inv_mem (mem_subgroupCarrier X y |>.mp hy), rfl⟩)
    · have hxX : x ∈ X := (mem_subgroupCarrier X x).mp hx
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inr ⟨x, hxX, rfl⟩
      · exact Or.inl (Or.inl (X.mul_mem hxX
          (X.inv_mem ((mem_subgroupCarrier X y).mp hy))))
  · rintro ((hz | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact ⟨z, Finset.mem_insert_of_mem ((mem_subgroupCarrier X z).mpr hz),
        1, Finset.mem_insert_of_mem ((mem_subgroupCarrier X 1).mpr X.one_mem), by simp⟩
    · exact ⟨c, Finset.mem_insert_self _ _, x⁻¹,
        Finset.mem_insert_of_mem ((mem_subgroupCarrier X _).mpr (X.inv_mem hx)), by simp⟩
    · exact ⟨x, Finset.mem_insert_of_mem ((mem_subgroupCarrier X x).mpr hx),
        c, Finset.mem_insert_self _ _, rfl⟩

/-- Left multiplication by `c` preserves the carrier cardinality by cancellation. -/
theorem card_left_image {G : Type*} [Group G] (X : Subgroup G) [Fintype X] (c : G) :
    ((subgroupCarrier X).image (fun x => c * x)).card = (subgroupCarrier X).card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h)

/-- Right multiplication by `c⁻¹` preserves the carrier cardinality by cancellation. -/
theorem card_right_image {G : Type*} [Group G] (X : Subgroup G) [Fintype X] (c : G) :
    ((subgroupCarrier X).image (fun x => x * c⁻¹)).card = (subgroupCarrier X).card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel h)

/-- If `c` lies outside the subgroup, its left coset is disjoint from the subgroup. -/
theorem disjoint_left_image {G : Type*} [Group G] (X : Subgroup G) [Fintype X]
    (c : G) (hc : c ∉ X) :
    Disjoint (subgroupCarrier X) ((subgroupCarrier X).image (fun x => c * x)) := by
  apply Finset.disjoint_left.mpr
  intro y hy hcy
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hcy
  have hyX : y ∈ X := (mem_subgroupCarrier X y).mp hy
  have hxX : x ∈ X := (mem_subgroupCarrier X x).mp hx
  have hcX : c ∈ X := by
    have hprod : y * x⁻¹ ∈ X := X.mul_mem hyX (X.inv_mem hxX)
    simpa only [← hxy, mul_inv_cancel_right] using hprod
  exact hc hcX

/-- Adjoining an element outside a finite subgroup at least doubles its right quotient size. -/
theorem two_card_le_rightQuotient_insert {G : Type*} [Group G]
    (X : Subgroup G) [Fintype X] (c : G) (hc : c ∉ X) :
    2 * (subgroupCarrier X).card ≤ (rightQuotient (insert c (subgroupCarrier X))).card := by
  rw [rightQuotient_insert]
  have hsubset : subgroupCarrier X ∪ (subgroupCarrier X).image (fun x => c * x) ⊆
      subgroupCarrier X ∪ (subgroupCarrier X).image (fun x => c * x) ∪
        (subgroupCarrier X).image (fun x => x * c⁻¹) := Finset.subset_union_left
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint (disjoint_left_image X c hc), card_left_image] at hcard
  omega

/-- Adjoining any element to a finite subgroup at most triples its right quotient size. -/
theorem rightQuotient_insert_card_le_three {G : Type*} [Group G]
    (X : Subgroup G) [Fintype X] (c : G) :
    (rightQuotient (insert c (subgroupCarrier X))).card ≤ 3 * (subgroupCarrier X).card := by
  rw [rightQuotient_insert]
  have houter := Finset.card_union_le
    (subgroupCarrier X ∪ (subgroupCarrier X).image (fun x => c * x))
    ((subgroupCarrier X).image (fun x => x * c⁻¹))
  have hinner := Finset.card_union_le (subgroupCarrier X)
    ((subgroupCarrier X).image (fun x => c * x))
  rw [card_left_image] at hinner
  rw [card_right_image] at houter
  omega

/-- Quotient-growth feasibility: the right quotient after adjoining an outside element has
size between twice and three times the subgroup size. No TPP preservation is asserted. -/
theorem rightQuotient_insert_card_bounds {G : Type*} [Group G]
    (X : Subgroup G) [Fintype X] (c : G) (hc : c ∉ X) :
    2 * Fintype.card X ≤ (rightQuotient (insert c (subgroupCarrier X))).card ∧
      (rightQuotient (insert c (subgroupCarrier X))).card ≤ 3 * Fintype.card X := by
  rw [← card_subgroupCarrier X]
  exact ⟨two_card_le_rightQuotient_insert X c hc, rightQuotient_insert_card_le_three X c⟩

/-- A subgroup carrier always contains the identity, so the baseline is not empty. -/
theorem subgroupCarrier_nonempty {G : Type*} [Group G] (X : Subgroup G) [Fintype X] :
    (subgroupCarrier X).Nonempty := by
  exact ⟨1, (mem_subgroupCarrier X 1).mpr X.one_mem⟩

example {G : Type*} [Group G] : rightQuotient ({1} : Finset G) = {1} := by
  ext z
  simp [mem_rightQuotient, eq_comm]

/-- The trivial subgroup has the singleton identity as its finite carrier. -/
theorem subgroupCarrier_bot {G : Type*} [Group G] :
    subgroupCarrier (⊥ : Subgroup G) = {1} := by
  ext z
  simp [mem_subgroupCarrier]

example : (Multiplicative.ofAdd (1 : ZMod 2)) ∉ (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
  change (1 : ZMod 2) ≠ 0
  exact one_ne_zero

example : by
    classical
    exact (rightQuotient (insert (Multiplicative.ofAdd (1 : ZMod 2))
      (subgroupCarrier (⊥ : Subgroup (Multiplicative (ZMod 2)))))).card = 2 := by
  classical
  have hX : subgroupCarrier (⊥ : Subgroup (Multiplicative (ZMod 2))) = {1} := by
    ext z
    simp [mem_subgroupCarrier]
  rw [hX]
  have hQ : rightQuotient {Multiplicative.ofAdd (1 : ZMod 2), 1} =
      {1, Multiplicative.ofAdd (1 : ZMod 2), (Multiplicative.ofAdd (1 : ZMod 2))⁻¹} := by
    ext z
    simp [mem_rightQuotient, eq_comm, or_assoc, or_left_comm, or_comm]
  rw [hQ]
  change ({(0 : ZMod 2), 1, -1} : Finset (ZMod 2)).card = 2
  have hneg : (-1 : ZMod 2) = 1 := rfl
  rw [hneg]
  norm_num [Finset.card_insert_of_notMem]

example : (Multiplicative.ofAdd (1 : ZMod 3)) ∉ (⊥ : Subgroup (Multiplicative (ZMod 3))) := by
  change (1 : ZMod 3) ≠ 0
  exact one_ne_zero

example : by
    classical
    exact (rightQuotient (insert (Multiplicative.ofAdd (1 : ZMod 3))
      (subgroupCarrier (⊥ : Subgroup (Multiplicative (ZMod 3)))))).card = 3 := by
  classical
  have hX : subgroupCarrier (⊥ : Subgroup (Multiplicative (ZMod 3))) = {1} := by
    ext z
    simp [mem_subgroupCarrier]
  rw [hX]
  have hQ : rightQuotient {Multiplicative.ofAdd (1 : ZMod 3), 1} =
      {1, Multiplicative.ofAdd (1 : ZMod 3), (Multiplicative.ofAdd (1 : ZMod 3))⁻¹} := by
    ext z
    simp [mem_rightQuotient, eq_comm, or_assoc, or_left_comm, or_comm]
  rw [hQ]
  change ({(0 : ZMod 3), 1, -1} : Finset (ZMod 3)).card = 3
  have hneg : (-1 : ZMod 3) = 2 := rfl
  rw [hneg]
  have h02 : (0 : ZMod 3) ≠ 2 := by
    intro h
    have hv : (0 : ℕ) = 2 := congrArg ZMod.val h
    omega
  have h12 : (1 : ZMod 3) ≠ 2 := by
    intro h
    have hv : (1 : ℕ) = 2 := congrArg ZMod.val h
    omega
  norm_num [Finset.card_insert_of_notMem, h02, h12]

end GroupTPP.RightQuotientGrowth
