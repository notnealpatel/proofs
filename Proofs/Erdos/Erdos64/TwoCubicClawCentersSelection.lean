import Erdos.Erdos64.TwoCubicClawCentersCycleSpares
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

/-- One can choose one representative of every attained label of a finite set. -/
theorem exists_injective_representatives {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Finset α) (f : α → β) :
    ∃ T ⊆ H, Set.InjOn f (↑T : Set α) ∧ T.card = (H.image f).card := by
  classical
  let B := {b : β // b ∈ H.image f}
  have hex (b : B) : ∃ a, a ∈ H ∧ f a = b.val := Finset.mem_image.mp b.property
  let g : B → α := fun b => Classical.choose (hex b)
  have hg (b : B) : g b ∈ H ∧ f (g b) = b.val := Classical.choose_spec (hex b)
  have hinj : Function.Injective g := by
    intro b c he
    exact Subtype.ext ((hg b).2.symm.trans ((congrArg f he).trans (hg c).2))
  refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact (hg b).1
  · intro a ha b hb he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    have hxy : x = y := Subtype.ext ((hg x).2.symm.trans (he.trans (hg y).2))
    exact congrArg g hxy
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]

/-- If a map has fibers of size at most two and is private on a subset, its image
has twice-cardinality at least the domain cardinality plus the private subset cardinality. -/
theorem card_add_private_le_twice_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H P : Finset α) (f : α → β)
    (hPH : P ⊆ H)
    (hprivate : ∀ i ∈ P, ∀ j ∈ H, f i = f j → i = j)
    (hfiber : ∀ b ∈ (H \ P).image f, ((H \ P).filter (fun i => f i = b)).card ≤ 2) :
    H.card + P.card ≤ 2 * (H.image f).card := by
  classical
  have hp : Set.InjOn f (↑P : Set α) := by
    intro i hi j hj he
    exact hprivate i hi j (hPH hj) he
  have hd : Disjoint (P.image f) ((H \ P).image f) := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp hc
    have he := hprivate i hi j (Finset.mem_sdiff.mp hj).1 (hfi.trans hfj.symm)
    exact (Finset.mem_sdiff.mp hj).2 (he ▸ hi)
  have himage : H.image f = P.image f ∪ (H \ P).image f := by
    rw [← Finset.image_union, Finset.union_sdiff_of_subset hPH]
  have hcount : (H.image f).card = P.card + ((H \ P).image f).card := by
    rw [himage, Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hp]
  have hrem := Finset.card_le_mul_card_image (H \ P) 2 hfiber
  have hsplit := Finset.card_sdiff_add_card_eq_card hPH
  omega

end Erdos64.TwoCubicClawCentersQuotient
