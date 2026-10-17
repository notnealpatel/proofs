import Combinatorics.NoncommutingBoxWindows
import Combinatorics.NoncommutingCoveringDensity
import Combinatorics.NoncommutingProjectionHoles
import Combinatorics.NoncommutingDenseHalo

set_option autoImplicit false

namespace NoncommutingBoxHalo

open NoncommutingBoxWindows NoncommutingDense NoncommutingFiber
open NoncommutingProjectionHoles

noncomputable section

/-- Every translated window is an integer interval, including empty windows. -/
theorem actualWindow_is_Icc (a u b v s : ℤ) :
    ∃ l r : ℤ, actualWindow a u b v s = Finset.Icc l r := by
  have hi (l r : ℤ) : (Finset.Icc l r).image (fun x => a+x) =
      Finset.Icc (a+l) (a+r) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy,hy'⟩, he⟩
      omega
    · rintro ⟨hx,hx'⟩
      exact ⟨x-a, ⟨by omega, by omega⟩, by omega⟩
  have ho (t : ℤ) : overlap u v t = Finset.Icc (max 0 (t-v+1)) (min (u-1) t) := by
    ext x
    simp only [overlap, Finset.mem_inter, Finset.mem_Icc, max_le_iff, le_min_iff]
    tauto
  unfold actualWindow overlapWindow
  split_ifs
  · exact ⟨a, a+(s-a-b), by simpa only [add_zero] using hi 0 (s-a-b)⟩
  · rw [ho, hi]
    exact ⟨_, _, rfl⟩

/-- The halo density used for comparable unequal sides is positive and at most one. -/
theorem halo_density_bounds (κ : ℝ) (hκ : 1 ≤ κ) :
    0 < 1 / (3*κ^2) ∧ 1 / (3*κ^2) ≤ 1 := by
  have hp : 0 < 3*κ^2 := by positivity
  constructor
  · exact div_pos (by norm_num) hp
  · apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg (κ-1)]

/-- A dense actual overlap rectangle places its actual mark in the fixed-grid
halo, with the very same holes, at density `1/(3κ²)`. -/
theorem actualMark_mem_rectangleHalo (E : Finset (ℤ × ℤ))
    (a u b v s a' u' b' v' s' : ℤ) (κ : ℝ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : 1 ≤ u') (hv' : 1 ≤ v')
    (hne : (actualOverlap a u b v s).Nonempty)
    (hne' : (actualOverlap a' u' b' v' s').Nonempty)
    (hκ : 1 ≤ κ) (hvu : (v : ℝ) ≤ κ*u) (hvu' : (v' : ℝ) ≤ κ*u')
    (hd : ((actualOverlap a u b v s ×ˢ actualOverlap a' u' b' v' s').card : ℝ) ≤
      3 * (E ∩ (actualOverlap a u b v s ×ˢ actualOverlap a' u' b' v' s')).card) :
    (actualMark a u b v s, actualMark a' u' b' v' s') ∈
      rectangleHalo (actualGrid a u v) (actualGrid a' u' v') E (1/(3*κ^2)) := by
  obtain ⟨hn,hm,hg,hdw⟩ := actualRectangle_certificate E a u b v s a' u' b' v' s' κ
    hu hv hu' hv' hne hne' hκ hvu hvu' hd
  obtain ⟨l,r,he⟩ := actualWindow_is_Icc a u b v s
  obtain ⟨l',r',he'⟩ := actualWindow_is_Icc a' u' b' v' s'
  rw [he,he'] at hn hm hg hdw
  obtain ⟨hm₁,hm₂⟩ := Finset.mem_product.mp hm
  have hlr : l ≤ r := (Finset.mem_Icc.mp hm₁).1.trans (Finset.mem_Icc.mp hm₁).2
  have hlr' : l' ≤ r' := (Finset.mem_Icc.mp hm₂).1.trans (Finset.mem_Icc.mp hm₂).2
  have hX : Finset.Icc l r ⊆ actualGrid a u v := by
    intro x hx
    exact (Finset.mem_product.mp (@hg (x, actualMark a' u' b' v' s') (Finset.mem_product.mpr ⟨hx,hm₂⟩))).1
  have hY : Finset.Icc l' r' ⊆ actualGrid a' u' v' := by
    intro y hy
    exact (Finset.mem_product.mp (@hg (actualMark a u b v s, y) (Finset.mem_product.mpr ⟨hm₁,hy⟩))).2
  apply Finset.mem_filter.mpr
  refine ⟨hg hm, l, hX (Finset.mem_Icc.mpr ⟨le_rfl,hlr⟩),
    r, hX (Finset.mem_Icc.mpr ⟨hlr,le_rfl⟩),
    l', hY (Finset.mem_Icc.mpr ⟨le_rfl,hlr'⟩),
    r', hY (Finset.mem_Icc.mpr ⟨hlr',le_rfl⟩),
    hlr, hlr', hX, hY, hm₁, hm₂, ?_⟩
  have hp : 0 < 3*κ^2 := by positivity
  rw [one_div_mul_eq_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  simpa only [Finset.card_product, Nat.cast_mul, mul_comm] using hdw

/-- A missing actual mixed-sum output selects one of the three fixed signed
projection halos. The holes are the actual projection complements of `A`. -/
theorem missing_output_mem_halo
    (r1 N1 r2 N2 r3 N3 : ℤ) (κ : ℝ)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) (hκ : 1 ≤ κ)
    (h12 : (N1 : ℝ) ≤ κ*N2) (h13 : (N1 : ℝ) ≤ κ*N3)
    (h21 : (N2 : ℝ) ≤ κ*N1) (h23 : (N2 : ℝ) ≤ κ*N3)
    (h31 : (N3 : ℝ) ≤ κ*N1) (h32 : (N3 : ℝ) ≤ κ*N2)
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3))
    (s : ℤ × ℤ × ℤ)
    (hs : s ∈ mixedSum (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)))
    (hm : s ∉ mixedSum A) :
    (actualMark r2 N2 r3 N3 s.1, actualMark (-r1-N1+1) N1 r3 N3 s.2.1) ∈
      rectangleHalo (actualGrid r2 N2 N3) (actualGrid (-r1-N1+1) N1 N3)
        (H0 (interval r1 N1) (interval r2 N2) A) (1/(3*κ^2)) ∨
    (actualMark r3 N3 r2 N2 s.1, actualMark (-r1-N1+1) N1 (-r2-N2+1) N2 s.2.2) ∈
      rectangleHalo (actualGrid r3 N3 N2) (actualGrid (-r1-N1+1) N1 N2)
        (H1 (interval r1 N1) (interval r3 N3) A) (1/(3*κ^2)) ∨
    (actualMark r3 N3 (-r1-N1+1) N1 s.2.1,
        actualMark (-r2-N2+1) N2 (-r1-N1+1) N1 s.2.2) ∈
      rectangleHalo (actualGrid r3 N3 N1) (actualGrid (-r2-N2+1) N2 N1)
        (H2 (interval r2 N2) (interval r3 N3) A) (1/(3*κ^2)) := by
  have hplus (I : Finset ℤ) (z : ℤ) :
      I.image (fun x => z+x) = (I.image Neg.neg).image (fun x => z-x) := by
    simp only [Finset.image_image, Function.comp_def, sub_neg_eq_add]
  have hn1 := image_neg_interval r1 N1 hN1
  have hn2 := image_neg_interval r2 N2 hN2
  have hf := NoncommutingCoveringDensity.rectangle_factor_identifications
    (interval r1 N1) (interval r2 N2) (interval r3 N3) s
  have h := NoncommutingCoveringDensity.missing_output_rectangle_density
    (interval r1 N1) (interval r2 N2) (interval r3 N3) A hA s hs hm
  dsimp only at h
  rw [hf.1, hf.2.1, hf.2.2] at h
  have hj : (interval r1 N1).image Neg.neg ∩
      (interval r2 N2).image (fun y => s.2.2+y) =
      actualOverlap (-r1-N1+1) N1 (-r2-N2+1) N2 s.2.2 := by
    rw [hplus, hn1, hn2]
    rfl
  have hr1 : interval r3 N3 ∩ (interval r1 N1).image (fun x => s.2.1+x) =
      actualOverlap r3 N3 (-r1-N1+1) N1 s.2.1 := by
    rw [hplus, hn1]
    rfl
  have hr2 : (interval r2 N2).image Neg.neg ∩
      (interval r1 N1).image (fun x => s.2.2+x) =
      actualOverlap (-r2-N2+1) N2 (-r1-N1+1) N1 s.2.2 := by
    rw [hplus, hn1, hn2]
    rfl
  rw [hj, hr1, hr2] at h
  obtain ⟨_,_,_,h0,h1,h2,hd⟩ := h
  have e2 : (interval r1 N1).image Neg.neg ∩
      (interval r3 N3).image (fun z => s.2.1-z) =
      actualOverlap (-r1-N1+1) N1 r3 N3 s.2.1 := by rw [hn1]; rfl
  rw [e2] at h0 hd
  have proj (X Y : Finset ℤ) (hn : (X ×ˢ Y).Nonempty) : X.Nonempty ∧ Y.Nonempty := by
    obtain ⟨p,hp⟩ := hn
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact ⟨⟨p.1,hx⟩, ⟨p.2,hy⟩⟩
  rcases hd with hd | hd | hd
  · apply Or.inl
    apply actualMark_mem_rectangleHalo _ _ _ _ _ _ _ _ _ _ _ κ
      hN2 hN3 hN1 hN3 (proj _ _ h0).1
      (proj _ _ h0).2 hκ h32 h31
    exact_mod_cast hd
  · apply Or.inr ∘ Or.inl
    apply actualMark_mem_rectangleHalo _ _ _ _ _ _ _ _ _ _ _ κ
      hN3 hN2 hN1 hN2 (proj _ _ h1).1
      (proj _ _ h1).2 hκ h23 h21
    exact_mod_cast hd
  · apply Or.inr ∘ Or.inr
    apply actualMark_mem_rectangleHalo _ _ _ _ _ _ _ _ _ _ _ κ
      hN3 hN1 hN2 hN1 (proj _ _ h2).1
      (proj _ _ h2).2 hκ h13 h12
    exact_mod_cast hd

example : (actualWindow 5 3 (-2) 4 6) = Finset.Icc 5 8 := by decide
example : (actualWindow (-2) 1 7 1 5) = Finset.Icc (-2) (-2) := by decide
example : 0 < 1 / (3*(2 : ℝ)^2) ∧ 1 / (3*(2 : ℝ)^2) ≤ 1 := by norm_num

end
end NoncommutingBoxHalo
