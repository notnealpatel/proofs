import Combinatorics.NoncommutingDenseRectangle

set_option autoImplicit false

namespace NoncommutingBoxWindows

open NoncommutingDense

noncomputable section

/-- An integer interval of length `u`, based at `a`. -/
def interval (a u : ℤ) : Finset ℤ := Finset.Icc a (a + u - 1)

/-- The untranslated overlap for a sum source `s`. -/
def actualOverlap (a u b v s : ℤ) : Finset ℤ :=
  interval a u ∩ (interval b v).image (fun y => s - y)

/-- The normalized window translated back to the original first coordinate. -/
def actualWindow (a u b v s : ℤ) : Finset ℤ :=
  (overlapWindow u v (s - a - b)).image (fun x => a + x)

/-- The marked point in the original coordinate. -/
def actualMark (a u b v s : ℤ) : ℤ := a + overlapMark u v (s - a - b)

/-- The fixed expanded grid, independent of the sum source. -/
def actualGrid (a u v : ℤ) : Finset ℤ := interval a (max u v)

example : interval (-2) 3 = {-2,-1,0} := by decide
example : actualOverlap 5 2 (-3) 4 4 = {5,6} := by decide
example : actualWindow 5 2 (-3) 4 4 = {5,6,7} := by decide
example : actualMark 5 2 (-3) 4 4 = 7 := by decide
example : actualGrid 5 2 4 = {5,6,7,8} := by decide

/-- Membership in the actual overlap is the pair of interval inequalities. -/
theorem mem_actualOverlap (a u b v s x : ℤ) :
    x ∈ actualOverlap a u b v s ↔
      a ≤ x ∧ x ≤ a + u - 1 ∧ b ≤ s - x ∧ s - x ≤ b + v - 1 := by
  simp only [actualOverlap, interval, Finset.mem_inter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h₁,h₂⟩, y, ⟨h₃,h₄⟩, he⟩
    omega
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨h₁,h₂⟩, s - x, ⟨h₃,h₄⟩, by omega⟩

/-- Exact normalization of an overlap, without transforming the hole set. -/
theorem actualOverlap_eq_image (a u b v s : ℤ) :
    actualOverlap a u b v s =
      (overlap u v (s - a - b)).image (fun x => a + x) := by
  ext x
  rw [mem_actualOverlap]
  simp only [Finset.mem_image, overlap, Finset.mem_inter, Finset.mem_Icc]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    refine ⟨x - a, ?_, by omega⟩
    omega
  · rintro ⟨y, ⟨⟨h₁,h₂⟩,h₃,h₄⟩, he⟩
    omega

/-- A nonempty overlap forces the normalized source into its valid range. -/
theorem actualOverlap_source_bounds (a u b v s : ℤ)
    (_hu : 1 ≤ u) (_hv : 1 ≤ v) (hne : (actualOverlap a u b v s).Nonempty) :
    0 ≤ s - a - b ∧ s - a - b ≤ u + v - 2 := by
  obtain ⟨x,hx⟩ := hne
  rw [mem_actualOverlap] at hx
  omega

/-- Translation of a normalized fixed interval gives the actual fixed grid. -/
theorem image_grid (a u v : ℤ) :
    (Finset.Icc 0 (max u v - 1)).image (fun x => a + x) = actualGrid a u v := by
  ext x
  simp only [actualGrid, interval, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨h₁,h₂⟩, he⟩
    omega
  · rintro ⟨h₁,h₂⟩
    exact ⟨x - a, ⟨by omega, by omega⟩, by omega⟩

/-- The actual window contains the actual overlap and mark, is nonempty,
and lies in a source-independent grid. -/
theorem actualWindow_geometry (a u b v s : ℤ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hne : (actualOverlap a u b v s).Nonempty) :
    actualOverlap a u b v s ⊆ actualWindow a u b v s ∧
    actualMark a u b v s ∈ actualWindow a u b v s ∧
    (actualWindow a u b v s).Nonempty ∧
    actualWindow a u b v s ⊆ actualGrid a u v := by
  obtain ⟨ht,htop⟩ := actualOverlap_source_bounds a u b v s hu hv hne
  obtain ⟨hsub,hmark,hgrid⟩ := overlapWindow_geometry u v (s-a-b) hu hv ht htop
  have hm : actualMark a u b v s ∈ actualWindow a u b v s :=
    Finset.mem_image.mpr ⟨_, hmark, rfl⟩
  refine ⟨?_, hm, ⟨_,hm⟩, ?_⟩
  · rw [actualOverlap_eq_image]
    exact Finset.image_subset_image hsub
  · rw [← image_grid]
    exact Finset.image_subset_image hgrid

/-- Translation preserves the normalized cardinality estimate. -/
theorem actualWindow_card_le (a u b v s : ℤ) (κ : ℝ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hne : (actualOverlap a u b v s).Nonempty)
    (hκ : 1 ≤ κ) (hvu : (v : ℝ) ≤ κ * u) :
    ((actualWindow a u b v s).card : ℝ) ≤ κ * (actualOverlap a u b v s).card := by
  obtain ⟨ht,htop⟩ := actualOverlap_source_bounds a u b v s hu hv hne
  rw [actualOverlap_eq_image, actualWindow,
    Finset.card_image_of_injective _ (add_right_injective a),
    Finset.card_image_of_injective _ (add_right_injective a)]
  exact overlapWindow_card_le u v (s-a-b) κ hu hv ht htop hκ hvu

/-- An actual-coordinate dense rectangle has a nonempty marked window product,
inside fixed grids, with density transported for exactly the same hole set `E`. -/
theorem actualRectangle_certificate (E : Finset (ℤ × ℤ))
    (a u b v s a' u' b' v' s' : ℤ) (κ : ℝ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : 1 ≤ u') (hv' : 1 ≤ v')
    (hne : (actualOverlap a u b v s).Nonempty)
    (hne' : (actualOverlap a' u' b' v' s').Nonempty)
    (hκ : 1 ≤ κ) (hvu : (v : ℝ) ≤ κ * u) (hvu' : (v' : ℝ) ≤ κ * u')
    (hdensity : ((actualOverlap a u b v s ×ˢ actualOverlap a' u' b' v' s').card : ℝ) ≤
      3 * (E ∩ (actualOverlap a u b v s ×ˢ actualOverlap a' u' b' v' s')).card) :
    (actualWindow a u b v s ×ˢ actualWindow a' u' b' v' s').Nonempty ∧
    (actualMark a u b v s, actualMark a' u' b' v' s') ∈
      actualWindow a u b v s ×ˢ actualWindow a' u' b' v' s' ∧
    actualWindow a u b v s ×ˢ actualWindow a' u' b' v' s' ⊆
      actualGrid a u v ×ˢ actualGrid a' u' v' ∧
    ((actualWindow a u b v s ×ˢ actualWindow a' u' b' v' s').card : ℝ) ≤
      3 * κ ^ 2 * (E ∩ (actualWindow a u b v s ×ˢ actualWindow a' u' b' v' s')).card := by
  obtain ⟨hsub,hm,_,hg⟩ := actualWindow_geometry a u b v s hu hv hne
  obtain ⟨hsub',hm',_,hg'⟩ := actualWindow_geometry a' u' b' v' s' hu' hv' hne'
  have hp : (actualMark a u b v s, actualMark a' u' b' v' s') ∈
      actualWindow a u b v s ×ˢ actualWindow a' u' b' v' s' :=
    Finset.mem_product.mpr ⟨hm,hm'⟩
  refine ⟨⟨_,hp⟩, hp, Finset.product_subset_product hg hg', ?_⟩
  exact rectangle_density_transport E _ _ _ _ κ hκ hsub hsub'
    (actualWindow_card_le a u b v s κ hu hv hne hκ hvu)
    (actualWindow_card_le a' u' b' v' s' κ hu' hv' hne' hκ hvu') hdensity

/-- The first origin cancels: a mark has only these two possible sum sources. -/
theorem actualMark_sources (a u b v s q : ℤ) (h : actualMark a u b v s = q) :
    s = q + b ∨ s = q + b + v - 1 := by
  have hm : overlapMark u v (s-a-b) = q-a := by
    unfold actualMark at h
    omega
  have hs := overlapMark_sources u v (s-a-b) (q-a) hm
  omega

/-- In any finite set of actual source pairs, a fixed mark pair has at most
four preimages; translations introduce no additional reflection factor. -/
theorem card_actualMark_pair_fiber_le_four
    (a u b v a' u' b' v' q q' : ℤ) (T : Finset (ℤ × ℤ)) :
    (T.filter (fun p => actualMark a u b v p.1 = q ∧
      actualMark a' u' b' v' p.2 = q')).card ≤ 4 := by
  have hsub : T.filter (fun p => actualMark a u b v p.1 = q ∧
      actualMark a' u' b' v' p.2 = q') ⊆
      {q+b, q+b+v-1} ×ˢ {q'+b', q'+b'+v'-1} := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := (Finset.mem_filter.mp hp).2
    apply Finset.mem_product.mpr
    constructor
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using
        actualMark_sources a u b v p.1 q h₁
    · simpa only [Finset.mem_insert, Finset.mem_singleton] using
        actualMark_sources a' u' b' v' p.2 q' h₂
  have hc : ({q+b, q+b+v-1} : Finset ℤ).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have hc' : ({q'+b', q'+b'+v'-1} : Finset ℤ).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  calc
    _ ≤ ({q+b, q+b+v-1} ×ˢ {q'+b', q'+b'+v'-1} : Finset (ℤ × ℤ)).card :=
      Finset.card_le_card hsub
    _ = ({q+b, q+b+v-1} : Finset ℤ).card *
        ({q'+b', q'+b'+v'-1} : Finset ℤ).card := Finset.card_product _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul hc hc'
    _ = 4 := rfl

/-- Reflection negates an interval and changes its origin, preserving length. -/
theorem image_neg_interval (r N : ℤ) (_hN : 1 ≤ N) :
    (interval r N).image (fun x => -x) = interval (-r-N+1) N := by
  ext x
  simp only [interval, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨h₁,h₂⟩, he⟩
    omega
  · rintro ⟨h₁,h₂⟩
    exact ⟨-x, ⟨by omega, by omega⟩, by omega⟩

example : actualOverlap 5 3 (-3) 4 5 = {5,6,7} ∧
    actualWindow 5 3 (-3) 4 5 = {5,6,7,8} ∧
    actualMark 5 3 (-3) 4 5 = 8 := by decide

example : actualOverlap (-2) 1 7 1 5 = {-2} ∧
    actualWindow (-2) 1 7 1 5 = {-2} ∧
    actualMark (-2) 1 7 1 5 = -2 := by decide

example : actualOverlap 5 2 (-3) 4 2 = {5} ∧
    actualOverlap 5 2 (-3) 4 6 = {6} ∧
    actualWindow 5 2 (-3) 4 6 = {6} ∧
    actualMark 5 2 (-3) 4 6 = 6 := by decide

example : (interval 3 4).image (fun x => -x) = interval (-6) 4 := by decide

example : 1 ≤ (2 : ℤ) ∧ 1 ≤ (4 : ℤ) ∧ 1 ≤ (3 : ℤ) ∧ 1 ≤ (4 : ℤ) ∧
    (actualOverlap 5 2 (-3) 4 4).Nonempty ∧
    (actualOverlap (-2) 3 7 4 8).Nonempty ∧
    (1 : ℝ) ≤ 2 ∧ (4 : ℝ) ≤ 2 * 2 ∧ (4 : ℝ) ≤ 2 * 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by decide, by decide, by norm_num, by norm_num, by norm_num⟩

example :
    ((actualWindow 5 2 (-3) 4 4 ×ˢ actualWindow (-2) 3 7 4 8).card : ℝ) ≤
      3 * (2 : ℝ)^2 *
        (({(5,-2),(6,-1)} : Finset (ℤ × ℤ)) ∩
          (actualWindow 5 2 (-3) 4 4 ×ˢ actualWindow (-2) 3 7 4 8)).card := by
  have hne : (actualOverlap 5 2 (-3) 4 4).Nonempty := by decide
  have hne' : (actualOverlap (-2) 3 7 4 8).Nonempty := by decide
  have hd : ((actualOverlap 5 2 (-3) 4 4 ×ˢ
      actualOverlap (-2) 3 7 4 8).card : ℝ) ≤
      3 * (({(5,-2),(6,-1)} : Finset (ℤ × ℤ)) ∩
        (actualOverlap 5 2 (-3) 4 4 ×ˢ actualOverlap (-2) 3 7 4 8)).card := by
    have hc : (actualOverlap 5 2 (-3) 4 4 ×ˢ
        actualOverlap (-2) 3 7 4 8).card = 6 := by decide
    have he : (({(5,-2),(6,-1)} : Finset (ℤ × ℤ)) ∩
        (actualOverlap 5 2 (-3) 4 4 ×ˢ actualOverlap (-2) 3 7 4 8)).card = 2 := by decide
    norm_num [hc, he]
  exact (actualRectangle_certificate {(5,-2),(6,-1)} 5 2 (-3) 4 4 (-2) 3 7 4 8 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hne hne'
    (by norm_num) (by norm_num) (by norm_num) hd).2.2.2

example :
    ((actualWindow (-2) 1 7 1 5 ×ˢ actualWindow 3 1 (-4) 1 (-1)).card : ℝ) ≤
      3 * (1 : ℝ)^2 *
        (({(-2,3)} : Finset (ℤ × ℤ)) ∩
          (actualWindow (-2) 1 7 1 5 ×ˢ actualWindow 3 1 (-4) 1 (-1))).card := by
  have hd : ((actualOverlap (-2) 1 7 1 5 ×ˢ
      actualOverlap 3 1 (-4) 1 (-1)).card : ℝ) ≤
      3 * (({(-2,3)} : Finset (ℤ × ℤ)) ∩
        (actualOverlap (-2) 1 7 1 5 ×ˢ actualOverlap 3 1 (-4) 1 (-1))).card := by
    norm_num [actualOverlap, interval]
  exact (actualRectangle_certificate {(-2,3)} (-2) 1 7 1 5 3 1 (-4) 1 (-1) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
    (by norm_num) (by norm_num) (by norm_num) hd).2.2.2

end
end NoncommutingBoxWindows
