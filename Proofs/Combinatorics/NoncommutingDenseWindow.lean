import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Marked windows for unequal integer interval overlaps

This module implements the normalized unequal-side geometric step of the dense
box route. It does not establish the rectangular halo estimate or the mixed-sum
deficit theorem. Windows are enlarged, never the set whose density is measured.
-/

set_option autoImplicit false

namespace NoncommutingDense

noncomputable section

/-- The overlap of `[0,u-1]` and `[t-v+1,t]`, with integer endpoints. -/
def overlap (u v t : ℤ) : Finset ℤ :=
  Finset.Icc 0 (u - 1) ∩ Finset.Icc (t - v + 1) t

/-- Mark the left endpoint on a strict suffix and the source parameter otherwise. -/
def overlapMark (u v t : ℤ) : ℤ :=
  if u ≤ t ∧ v ≤ t then t - v + 1 else t

/-- Retain the overlap, except on the unequal-side plateau, where it is enlarged
from `[0,u-1]` to `[0,t]`. -/
def overlapWindow (u v t : ℤ) : Finset ℤ :=
  if u ≤ t ∧ t < v then Finset.Icc 0 t else overlap u v t

example : overlap 2 4 2 = {0,1} := by decide
example : overlap 1 1 0 = {0} := by decide
example : overlapMark 2 4 4 = 1 := by decide
example : overlapMark 2 4 2 = 2 := by decide
example : overlapWindow 2 4 2 = {0,1,2} := by decide
example : overlapWindow 1 1 0 = {0} := by decide

/-- Valid source parameters give a nonempty overlap. -/
theorem overlap_nonempty (u v t : ℤ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : 0 ≤ t) (htop : t ≤ u + v - 2) : (overlap u v t).Nonempty := by
  refine ⟨max 0 (t - v + 1), ?_⟩
  simp only [overlap, Finset.mem_inter, Finset.mem_Icc]
  omega

/-- The window contains the original overlap, its mark, and stays in the fixed
expanded grid `[0,max(u,v)-1]`. -/
theorem overlapWindow_geometry (u v t : ℤ) (_hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : 0 ≤ t) (htop : t ≤ u + v - 2) :
    overlap u v t ⊆ overlapWindow u v t ∧
      overlapMark u v t ∈ overlapWindow u v t ∧
      overlapWindow u v t ⊆ Finset.Icc 0 (max u v - 1) := by
  by_cases hp : u ≤ t ∧ t < v
  · have hs : ¬(u ≤ t ∧ v ≤ t) := by omega
    simp only [overlapWindow, overlapMark, if_pos hp, if_neg hs]
    constructor
    · intro x hx
      simp only [overlap, Finset.mem_inter, Finset.mem_Icc] at hx ⊢
      omega
    · constructor
      · simp only [Finset.mem_Icc]
        omega
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
  · simp only [overlapWindow, if_neg hp]
    refine ⟨Finset.Subset.refl _, ?_, ?_⟩
    · simp only [overlapMark]
      split_ifs <;> simp only [overlap, Finset.mem_inter, Finset.mem_Icc] <;> omega
    · intro x hx
      simp only [overlap, Finset.mem_inter, Finset.mem_Icc] at hx ⊢
      omega

/-- On the plateau the original overlap has exactly `u` points. -/
theorem overlap_card_of_plateau (u v t : ℤ) (_hu : 1 ≤ u)
    (ht : u ≤ t) (htv : t < v) : (overlap u v t).card = u.toNat := by
  have heq : overlap u v t = Finset.Icc 0 (u - 1) := by
    ext x
    simp only [overlap, Finset.mem_inter, Finset.mem_Icc]
    omega
  rw [heq, Int.card_Icc]
  congr 1
  omega

/-- If the side ratio is at most `κ`, the window has at most `κ` times the
original number of points. Cardinalities are cast before real arithmetic. -/
theorem overlapWindow_card_le (u v t : ℤ) (κ : ℝ) (hu : 1 ≤ u)
    (_hv : 1 ≤ v) (ht : 0 ≤ t) (_htop : t ≤ u + v - 2)
    (hκ : 1 ≤ κ) (hvu : (v : ℝ) ≤ κ * (u : ℝ)) :
    ((overlapWindow u v t).card : ℝ) ≤ κ * (overlap u v t).card := by
  by_cases hp : u ≤ t ∧ t < v
  · rw [overlapWindow, if_pos hp, Int.card_Icc,
      overlap_card_of_plateau u v t hu hp.1 hp.2]
    have htn : 0 ≤ t + 1 - 0 := by omega
    have hun : 0 ≤ u := by omega
    have htc : ((t + 1 - 0).toNat : ℝ) = (t + 1 - 0 : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg htn
    have huc : (u.toNat : ℝ) = (u : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hun
    rw [htc, huc]
    have htv : (t : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast (show t + 1 ≤ v by omega)
    push_cast
    linarith
  · rw [overlapWindow, if_neg hp]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hκ

/-- A marked point has only the two possible source parameters `q` and
`q+v-1`; no additional preimage is introduced by the plateau. -/
theorem overlapMark_sources (u v t q : ℤ) (hmark : overlapMark u v t = q) :
    t = q ∨ t = q + v - 1 := by
  unfold overlapMark at hmark
  split_ifs at hmark <;> omega

/-- In any finite source set, the mark map has multiplicity at most two. -/
theorem card_overlapMark_fiber_le_two (u v q : ℤ) (T : Finset ℤ) :
    (T.filter (fun t => overlapMark u v t = q)).card ≤ 2 := by
  have hsub : T.filter (fun t => overlapMark u v t = q) ⊆ {q, q + v - 1} := by
    intro t ht
    have hs := overlapMark_sources u v t q (Finset.mem_filter.mp ht).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))

/-- Equal side lengths never trigger the plateau enlargement. -/
theorem overlapWindow_eq_overlap_of_eq_sides (u t : ℤ) :
    overlapWindow u u t = overlap u u t := by
  have hp : ¬(u ≤ t ∧ t < u) := by omega
  simp only [overlapWindow, if_neg hp]

example : 1 ≤ (2 : ℤ) ∧ 1 ≤ (4 : ℤ) ∧ 0 ≤ (2 : ℤ) ∧
    (2 : ℤ) ≤ 2 + 4 - 2 ∧ (1 : ℝ) ≤ 2 ∧ (4 : ℝ) ≤ 2 * (2 : ℝ) := by norm_num

end

end NoncommutingDense
