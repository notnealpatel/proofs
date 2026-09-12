/-
  Erdős Problem #142 — a finite 3-AP supersaturation foundation.

  This file records only the standard finite deletion argument.  A nontrivial
  three-term arithmetic progression in a finite set is represented by its
  three-element underlying finset, so it is counted exactly once.  Choosing
  one point from every such edge and deleting the chosen points leaves a
  3-AP-free set while deleting at most as many points as there are edges.
  Combining this with Mathlib's `addRothNumber` gives the corresponding
  subtraction-free supersaturation inequalities.

  This is reusable finite infrastructure, not an asymptotic solution of
  Erdős Problem #142 and not a new mathematical supersaturation estimate.
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-- The canonical finset of nontrivial three-term arithmetic progressions in
`A`.  An edge is its three-element underlying finset, and hence occurs once,
independently of either orientation of the progression. -/
def threeAPEdges (A : Finset ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard 3).filter fun e => ¬ ThreeAPFree (e : Set ℕ)

/-- The number of nontrivial three-term arithmetic progressions in `A`, each
counted once via its three-element underlying finset. -/
def threeAPCount (A : Finset ℕ) : ℕ :=
  (threeAPEdges A).card

/-- Membership in `threeAPEdges` unfolds to being a three-element subset
which is not 3-AP-free. -/
theorem mem_threeAPEdges {A e : Finset ℕ} :
    e ∈ threeAPEdges A ↔ e ⊆ A ∧ e.card = 3 ∧ ¬ ThreeAPFree (e : Set ℕ) := by
  simp only [threeAPEdges, mem_filter, mem_powersetCard]
  tauto

/-- A finite set is 3-AP-free exactly when each of its three-element subsets
is 3-AP-free. -/
theorem threeAPFree_iff_forall_powersetCard (A : Finset ℕ) :
    ThreeAPFree (A : Set ℕ) ↔
      ∀ e ∈ A.powersetCard 3, ThreeAPFree (e : Set ℕ) := by
  constructor
  · intro hA e he
    exact hA.mono (by simpa only [coe_subset] using (mem_powersetCard.mp he).1)
  · intro h a ha b hb c hc habc
    by_contra hne
    have hbc : b ≠ c := by
      rintro rfl
      omega
    have hac : a ≠ c := by
      rintro rfl
      omega
    let e : Finset ℕ := {a, b, c}
    have heA : e ⊆ A := by
      intro x hx
      simp only [e, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hecard : e.card = 3 := by
      simp [e, hne, hbc, hac]
    have he : e ∈ A.powersetCard 3 := mem_powersetCard.mpr ⟨heA, hecard⟩
    have hae : a ∈ e := by simp [e]
    have hbe : b ∈ e := by simp [e]
    have hce : c ∈ e := by simp [e]
    exact hne (h e he hae hbe hce habc)

/-- Ground truth for the edge representation: `{0, 1, 2}` has exactly
one canonical edge, namely itself. -/
example : threeAPEdges {0, 1, 2} = {{0, 1, 2}} := by decide

/-- Ground truth: the empty set has no nontrivial three-term progression. -/
example : threeAPCount ∅ = 0 := by decide

/-- Ground truth: `{0, 1, 2}` contains exactly its one three-term progression. -/
example : threeAPCount {0, 1, 2} = 1 := by decide

/-- Ground truth: `{0, 1, 3}` contains no nontrivial three-term progression. -/
example : threeAPCount {0, 1, 3} = 0 := by decide

/-- The progression count vanishes exactly on finite 3-AP-free sets. -/
theorem threeAPCount_eq_zero_iff (A : Finset ℕ) :
    threeAPCount A = 0 ↔ ThreeAPFree (A : Set ℕ) := by
  rw [threeAPFree_iff_forall_powersetCard]
  simp only [threeAPCount, card_eq_zero, threeAPEdges, filter_eq_empty_iff,
    Classical.not_not]

/-- The canonical progression count is monotone under inclusion. -/
theorem threeAPCount_mono {A U : Finset ℕ} (hAU : A ⊆ U) :
    threeAPCount A ≤ threeAPCount U := by
  apply card_le_card
  intro e he
  rw [mem_threeAPEdges] at he ⊢
  exact ⟨he.1.trans hAU, he.2⟩

/-- **Finite deletion lemma.** Every finite set `A` contains a 3-AP-free
subset `B` such that `A.card ≤ B.card + threeAPCount A`.

The proof chooses one point from every canonical 3-AP edge and deletes the
set of chosen points.  Every surviving edge would contain its own chosen
point, while the image of the choice map has cardinality at most the edge
family.  The inequality is stated without natural-number subtraction. -/
theorem exists_threeAPFree_subset_card_le_add_count (A : Finset ℕ) :
    ∃ B ⊆ A, ThreeAPFree (B : Set ℕ) ∧
      A.card ≤ B.card + threeAPCount A := by
  classical
  let E := threeAPEdges A
  let pick : {e // e ∈ E} → ℕ := fun e =>
    e.1.min' (by
      have hecard : e.1.card = 3 := (mem_threeAPEdges.mp e.2).2.1
      exact card_pos.mp (by omega))
  let R : Finset ℕ := E.attach.image pick
  let B := A \ R
  have hBA : B ⊆ A := sdiff_subset
  have hpick_mem (e : {e // e ∈ E}) : pick e ∈ e.1 := by
    exact min'_mem e.1 _
  have hRcard : R.card ≤ E.card := by
    calc
      R.card ≤ E.attach.card := card_image_le
      _ = E.card := card_attach
  have hfree : ThreeAPFree (B : Set ℕ) := by
    rw [threeAPFree_iff_forall_powersetCard]
    intro e heB
    by_contra he_not_free
    have heBA : e ⊆ A := (mem_powersetCard.mp heB).1.trans hBA
    have heE : e ∈ E := by
      apply mem_threeAPEdges.mpr
      exact ⟨heBA, (mem_powersetCard.mp heB).2, he_not_free⟩
    let ee : {e // e ∈ E} := ⟨e, heE⟩
    have hpick_e : pick ee ∈ e := hpick_mem ee
    have hpick_R : pick ee ∈ R := by
      apply mem_image.mpr
      exact ⟨ee, mem_attach E ee, rfl⟩
    have hpick_B : pick ee ∈ B := (mem_powersetCard.mp heB).1 hpick_e
    exact (mem_sdiff.mp hpick_B).2 hpick_R
  have hinter_card : (A ∩ R).card ≤ E.card := by
    exact (card_le_card inter_subset_right).trans hRcard
  refine ⟨B, hBA, hfree, ?_⟩
  have hpartition : B.card + (A ∩ R).card = A.card := by
    exact card_sdiff_add_card_inter A R
  rw [← hpartition, threeAPCount]
  exact Nat.add_le_add_left hinter_card B.card

/-- Supersaturation relative to an arbitrary finite ambient set: if `A ⊆ U`,
then `A.card` is at most the additive Roth number of `U` plus the canonical
number of 3-APs in `A`. -/
theorem card_le_addRothNumber_add_threeAPCount {A U : Finset ℕ} (hAU : A ⊆ U) :
    A.card ≤ addRothNumber U + threeAPCount A := by
  obtain ⟨B, hBA, hfree, hcard⟩ := exists_threeAPFree_subset_card_le_add_count A
  have hBRoth : B.card ≤ addRothNumber U :=
    hfree.le_addRothNumber (hBA.trans hAU)
  exact hcard.trans (Nat.add_le_add_right hBRoth (threeAPCount A))

/-- Interval specialization of the finite deletion bound: if `A` lies below
`N`, then `A.card ≤ rothNumberNat N + threeAPCount A`. -/
theorem card_le_rothNumberNat_add_threeAPCount {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.range N) :
    A.card ≤ rothNumberNat N + threeAPCount A := by
  simpa only [rothNumberNat_def] using
    card_le_addRothNumber_add_threeAPCount hA

/-- Satisfiability check for the inclusion hypotheses in both supersaturation
corollaries, using the non-3-AP-free set `{0, 1, 2}` in `range 3`. -/
example :
    let A : Finset ℕ := {0, 1, 2}
    let U := Finset.range 3
    A ⊆ U ∧ A.card ≤ addRothNumber U + threeAPCount A ∧
      A.card ≤ rothNumberNat 3 + threeAPCount A := by
  dsimp only
  have hAU : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range 3 := by decide
  exact ⟨hAU, card_le_addRothNumber_add_threeAPCount hAU,
    card_le_rothNumberNat_add_threeAPCount hAU⟩

#check @exists_threeAPFree_subset_card_le_add_count
#check @card_le_addRothNumber_add_threeAPCount
#check @card_le_rothNumberNat_add_threeAPCount

#print axioms exists_threeAPFree_subset_card_le_add_count
#print axioms card_le_addRothNumber_add_threeAPCount
#print axioms card_le_rothNumberNat_add_threeAPCount

end Erdos142
