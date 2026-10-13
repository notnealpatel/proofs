import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace ErdosCandidates.E362

/-- The number of subsets of `A` whose elements sum to `t`. -/
def sumCount (A : Finset ℕ) (t : ℕ) : ℕ :=
  (A.powerset.filter (fun S => ∑ n ∈ S, n = t)).card

example : sumCount {1, 2, 3} 3 = 2 := by decide
example : sumCount {1, 2, 3, 4} 5 = 2 := by decide
example : sumCount ∅ 0 = 1 := by decide
example : sumCount ∅ 1 = 0 := by decide

private theorem subtype_subset_iff (A S T : Finset ℕ)
    (hS : S ⊆ A) :
    S.subtype (· ∈ A) ⊆ T.subtype (· ∈ A) ↔ S ⊆ T := by
  constructor
  · intro h a ha
    exact Finset.mem_subtype.mp (h (Finset.mem_subtype.mpr ha :
      (⟨a, hS ha⟩ : A) ∈ S.subtype (· ∈ A)))
  · intro h a ha
    exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp ha))

/-- Subsets with the same sum in a set of positive natural numbers form an
antichain, so Sperner's theorem bounds their number by the middle binomial coefficient. -/
theorem sumCount_le_choose (A : Finset ℕ) (t : ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    sumCount A t ≤ A.card.choose (A.card / 2) := by
  classical
  let F := A.powerset.filter (fun S => ∑ n ∈ S, n = t)
  have hmem (S : Finset ℕ) (hS : S ∈ F) : S ⊆ A ∧ ∑ n ∈ S, n = t := by
    exact ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1,
      (Finset.mem_filter.mp hS).2⟩
  have hanti : IsAntichain (· ⊆ ·) (F : Set (Finset ℕ)) := by
    intro S hS T hT hne hST
    have hTS : ¬ T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
    obtain ⟨a, haT, haS⟩ := Finset.not_subset.mp hTS
    have hpos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one (hA a ((hmem T hT).1 haT))
    have hsum : (∑ n ∈ S, n) < ∑ n ∈ T, n :=
      Finset.sum_lt_sum_of_subset hST haT haS hpos (fun n _ _ => Nat.zero_le n)
    rw [(hmem S hS).2, (hmem T hT).2] at hsum
    exact (lt_irrefl t) hsum
  let f : Finset ℕ → Finset A := fun S => S.subtype (· ∈ A)
  have hinj : Set.InjOn f (F : Set (Finset ℕ)) := by
    intro S hS T hT heq
    apply Finset.Subset.antisymm
    · exact (subtype_subset_iff A S T (hmem S hS).1).mp heq.le
    · exact (subtype_subset_iff A T S (hmem T hT).1).mp heq.ge
  have himage : IsAntichain (· ⊆ ·) (F.image f : Set (Finset A)) := by
    intro U hU V hV hne hUV
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hV
    have hST : S ⊆ T := (subtype_subset_iff A S T (hmem S hS).1).mp hUV
    exact hanti hS hT (fun h => hne (congrArg f h)) hST
  have hcard : (F.image f).card = F.card := Finset.card_image_of_injOn hinj
  have hbound := himage.sperner
  rw [Fintype.card_coe, hcard] at hbound
  exact hbound

example : (∀ a ∈ ({1, 2, 3} : Finset ℕ), 1 ≤ a) ∧
    sumCount {1, 2, 3} 3 = 2 := by decide
example : (∀ a ∈ (∅ : Finset ℕ), 1 ≤ a) ∧ sumCount ∅ 0 = 1 := by decide

end ErdosCandidates.E362
