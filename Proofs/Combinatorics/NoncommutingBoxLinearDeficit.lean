import Combinatorics.NoncommutingBoxDeficit
import Combinatorics.NoncommutingProportionalOverlap

set_option autoImplicit false

namespace NoncommutingBoxLinearDeficit

noncomputable section
open NoncommutingBoxWindows NoncommutingCubeCounting
open NoncommutingProjectionHoles NoncommutingFiber NoncommutingDense
open NoncommutingProportionalOverlap
open scoped Pointwise BigOperators

private theorem overlap_is_Icc (a u b v s : ℤ) :
    actualOverlap a u b v s =
      Finset.Icc (max a (s-b-v+1)) (min (a+u-1) (s-b)) := by
  ext x
  rw [mem_actualOverlap]
  simp only [Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

private theorem mark_mem_halo (E : Finset (ℤ × ℤ))
    (a u b v s a' u' b' v' s' : ℤ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : 1 ≤ u') (hv' : 1 ≤ v')
    (hne : (actualOverlap a u b v s).Nonempty)
    (hne' : (actualOverlap a' u' b' v' s').Nonempty)
    (hd : ((actualOverlap a u b v s ×ˢ actualOverlap a' u' b' v' s').card : ℝ) ≤
      3 * (E ∩ (actualOverlap a u b v s ×ˢ actualOverlap a' u' b' v' s')).card) :
    (mark a u b v s, mark a' u' b' v' s') ∈
      rectangleHalo (interval a u) (interval a' u') E (1/3) := by
  have hm := mark_mem_actualOverlap a u b v s hu hv hne
  have hm' := mark_mem_actualOverlap a' u' b' v' s' hu' hv' hne'
  have hX : actualOverlap a u b v s ⊆ interval a u := Finset.inter_subset_left
  have hY : actualOverlap a' u' b' v' s' ⊆ interval a' u' := Finset.inter_subset_left
  rw [overlap_is_Icc] at hm hX
  rw [overlap_is_Icc] at hm' hY
  let l := max a (s-b-v+1)
  let r := min (a+u-1) (s-b)
  let l' := max a' (s'-b'-v'+1)
  let r' := min (a'+u'-1) (s'-b')
  have hlr : l ≤ r := (Finset.mem_Icc.mp hm).1.trans (Finset.mem_Icc.mp hm).2
  have hlr' : l' ≤ r' := (Finset.mem_Icc.mp hm').1.trans (Finset.mem_Icc.mp hm').2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hX hm, hY hm'⟩,
    l, hX (Finset.mem_Icc.mpr ⟨le_rfl, hlr⟩),
    r, hX (Finset.mem_Icc.mpr ⟨hlr, le_rfl⟩),
    l', hY (Finset.mem_Icc.mpr ⟨le_rfl, hlr'⟩),
    r', hY (Finset.mem_Icc.mpr ⟨hlr', le_rfl⟩),
    hlr, hlr', hX, hY, hm, hm', ?_⟩
  rw [overlap_is_Icc, overlap_is_Icc] at hd
  simp only [Finset.card_product, Nat.cast_mul] at hd
  linarith

private theorem missing_output_mem_halo
    (r1 N1 r2 N2 r3 N3 : ℤ)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3)
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3))
    (s : ℤ × ℤ × ℤ)
    (hs : s ∈ mixedSum (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)))
    (hm : s ∉ mixedSum A) :
    (mark r2 N2 r3 N3 s.1, mark (-r1-N1+1) N1 r3 N3 s.2.1) ∈
      rectangleHalo (interval r2 N2) (interval (-r1-N1+1) N1)
        (H0 (interval r1 N1) (interval r2 N2) A) (1/3) ∨
    (mark r3 N3 r2 N2 s.1, mark (-r1-N1+1) N1 (-r2-N2+1) N2 s.2.2) ∈
      rectangleHalo (interval r3 N3) (interval (-r1-N1+1) N1)
        (H1 (interval r1 N1) (interval r3 N3) A) (1/3) ∨
    (mark r3 N3 (-r1-N1+1) N1 s.2.1,
        mark (-r2-N2+1) N2 (-r1-N1+1) N1 s.2.2) ∈
      rectangleHalo (interval r3 N3) (interval (-r2-N2+1) N2)
        (H2 (interval r2 N2) (interval r3 N3) A) (1/3) := by
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
    apply mark_mem_halo _ _ _ _ _ _ _ _ _ _ _
      hN2 hN3 hN1 hN3 (proj _ _ h0).1
      (proj _ _ h0).2
    exact_mod_cast hd
  · apply Or.inr ∘ Or.inl
    apply mark_mem_halo _ _ _ _ _ _ _ _ _ _ _
      hN3 hN2 hN1 hN2 (proj _ _ h1).1
      (proj _ _ h1).2
    exact_mod_cast hd
  · apply Or.inr ∘ Or.inr
    apply mark_mem_halo _ _ _ _ _ _ _ _ _ _ _
      hN3 hN1 hN2 hN1 (proj _ _ h2).1
      (proj _ _ h2).2
    exact_mod_cast hd

private theorem card_mark_preimage_le (P H : Finset (ℤ × ℤ))
    (a u b v a' u' b' v' : ℤ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : 1 ≤ u') (hv' : 1 ≤ v') :
    ((P.filter (fun p => (mark a u b v p.1, mark a' u' b' v' p.2) ∈ H)).card : ℝ) ≤
      (9 * max 1 ((v : ℝ)/u) * max 1 ((v' : ℝ)/u')) * H.card := by
  classical
  let T := P.filter (fun p => (mark a u b v p.1, mark a' u' b' v' p.2) ∈ H)
  let f := fun p : ℤ × ℤ => (mark a u b v p.1, mark a' u' b' v' p.2)
  have hc : T.card = ∑ z ∈ H, (T.filter (fun p => f p = z)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => (Finset.mem_filter.mp hp).2)
  have hcR : (T.card : ℝ) = ∑ z ∈ H, ((T.filter (fun p => f p = z)).card : ℝ) := by
    exact_mod_cast hc
  change (T.card : ℝ) ≤ _
  rw [hcR]
  calc
    _ ≤ ∑ _z ∈ H, (9 * max 1 ((v : ℝ)/u) * max 1 ((v' : ℝ)/u')) := by
      apply Finset.sum_le_sum
      rintro ⟨j,j'⟩ _
      exact pair_mark_fiber_card_real T a u b v a' u' b' v' j j' hu hv hu' hv'
    _ = _ := by simp [mul_comm]

private theorem aspect_cancellation (a b c κ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hκ : 1 ≤ κ)
    (hab : a ≤ κ*b) (hac : a ≤ κ*c)
    (hba : b ≤ κ*a) (hbc : b ≤ κ*c)
    (hca : c ≤ κ*a) (hcb : c ≤ κ*b) :
    (a+b)/c * max 1 (c/b) * max 1 (c/a) ≤ 2*κ := by
  have hab' : a/b ≤ κ := (div_le_iff₀ hb).mpr hab
  have hac' : a/c ≤ κ := (div_le_iff₀ hc).mpr hac
  have hba' : b/a ≤ κ := (div_le_iff₀ ha).mpr hba
  have hbc' : b/c ≤ κ := (div_le_iff₀ hc).mpr hbc
  have hca' : c/a ≤ κ := (div_le_iff₀ ha).mpr hca
  have hcb' : c/b ≤ κ := (div_le_iff₀ hb).mpr hcb
  rcases le_total 1 (c/b) with hb1 | hb1 <;>
    rcases le_total 1 (c/a) with ha1 | ha1
  · rw [max_eq_right hb1, max_eq_right ha1]
    have he : (a+b)/c * (c/b) * (c/a) = c/a+c/b := by
      field_simp
      ring
    rw [he]
    linarith
  · rw [max_eq_right hb1, max_eq_left ha1]
    have he : (a+b)/c * (c/b) * 1 = 1+a/b := by
      field_simp
      ring
    rw [he]
    linarith
  · rw [max_eq_left hb1, max_eq_right ha1]
    have he : (a+b)/c * 1 * (c/a) = 1+b/a := by
      field_simp
    rw [he]
    linarith
  · rw [max_eq_left hb1, max_eq_left ha1]
    have he : (a+b)/c * 1 * 1 = a/c+b/c := by ring
    rw [he]
    linarith

/-- The deficit estimate with all six side-ratio inequalities explicit. -/
theorem mixedSum_box_deficit_le_ratios
    (r1 N1 r2 N2 r3 N3 : ℤ) (κ : ℝ)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) (hκ : 1 ≤ κ)
    (h12 : (N1 : ℝ) ≤ κ*N2) (h13 : (N1 : ℝ) ≤ κ*N3)
    (h21 : (N2 : ℝ) ≤ κ*N1) (h23 : (N2 : ℝ) ≤ κ*N3)
    (h31 : (N3 : ℝ) ≤ κ*N1) (h32 : (N3 : ℝ) ≤ κ*N2)
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) :
    ((mixedSum (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \
      mixedSum A).card : ℝ) ≤
      14580*κ*( (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \ A).card := by
  classical
  let B := interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)
  let S := mixedSum B \ mixedSum A
  let E0 := H0 (interval r1 N1) (interval r2 N2) A
  let E1 := H1 (interval r1 N1) (interval r3 N3) A
  let E2 := H2 (interval r2 N2) (interval r3 N3) A
  let F0 := rectangleHalo (interval r2 N2) (interval (-r1-N1+1) N1) E0 (1/3)
  let F1 := rectangleHalo (interval r3 N3) (interval (-r1-N1+1) N1) E1 (1/3)
  let F2 := rectangleHalo (interval r3 N3) (interval (-r2-N2+1) N2) E2 (1/3)
  let P0 := S.image (fun s => (s.1,s.2.1))
  let P1 := S.image (fun s => (s.1,s.2.2))
  let P2 := S.image (fun s => (s.2.1,s.2.2))
  let T0 := P0.filter (fun p =>
    (mark r2 N2 r3 N3 p.1, mark (-r1-N1+1) N1 r3 N3 p.2) ∈ F0)
  let T1 := P1.filter (fun p =>
    (mark r3 N3 r2 N2 p.1, mark (-r1-N1+1) N1 (-r2-N2+1) N2 p.2) ∈ F1)
  let T2 := P2.filter (fun p =>
    (mark r3 N3 (-r1-N1+1) N1 p.1,
      mark (-r2-N2+1) N2 (-r1-N1+1) N1 p.2) ∈ F2)
  let Q0 := Finset.Icc (-r1-r2-N1-N2+2) (-r1-r2)
  let Q1 := Finset.Icc (-r1-N1+1+r3) (-r1+r3+N3-1)
  let Q2 := Finset.Icc (r2+r3) (r2+r3+N2+N3-2)
  have hcover : ∀ s ∈ S,
      ((s.1,s.2.1) ∈ T0 ∧ s.2.2 ∈ Q0) ∨
      ((s.1,s.2.2) ∈ T1 ∧ s.2.1 ∈ Q1) ∨
      ((s.2.1,s.2.2) ∈ T2 ∧ s.1 ∈ Q2) := by
    intro s hs
    obtain ⟨hsum,hm⟩ := Finset.mem_sdiff.mp hs
    have hr := NoncommutingBoxDeficit.mixedSum_box_ranges r1 N1 r2 N2 r3 N3 s hsum
    have hc := missing_output_mem_halo r1 N1 r2 N2 r3 N3
      hN1 hN2 hN3 A hA s hsum hm
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hs,hc⟩,hr.2.2⟩
    · exact Or.inr (Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hs,hc⟩,hr.2.1⟩)
    · exact Or.inr (Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hs,hc⟩,hr.1⟩)
  have hc := card_le_pair_lift_union S T0 T1 T2 Q0 Q1 Q2 hcover
  have halo_bound (a u c w : ℤ) (hu : 1 ≤ u) (hw : 1 ≤ w)
      (E : Finset (ℤ × ℤ)) (he : E ⊆ interval a u ×ˢ interval c w) :
      ((rectangleHalo (interval a u) (interval c w) E (1/3)).card : ℝ) ≤ 270*E.card := by
    exact_mod_cast rectangleHalo_third_bound a (a+u-1) c (c+w-1)
      (by omega) (by omega) E he
  have hf0 : (F0.card : ℝ) ≤ 270*E0.card := by
    apply halo_bound _ _ _ _ hN2 hN1
    simpa only [E0,H0,G0,image_neg_interval r1 N1 hN1] using
      (Finset.sdiff_subset : E0 ⊆ G0 (interval r1 N1) (interval r2 N2))
  have hf1 : (F1.card : ℝ) ≤ 270*E1.card := by
    apply halo_bound _ _ _ _ hN3 hN1
    simpa only [E1,H1,G1,image_neg_interval r1 N1 hN1] using
      (Finset.sdiff_subset : E1 ⊆ G1 (interval r1 N1) (interval r3 N3))
  have hf2 : (F2.card : ℝ) ≤ 270*E2.card := by
    apply halo_bound _ _ _ _ hN3 hN2
    simpa only [E2,H2,G2,image_neg_interval r2 N2 hN2] using
      (Finset.sdiff_subset : E2 ⊆ G2 (interval r2 N2) (interval r3 N3))
  have ht0 : (T0.card : ℝ) ≤
      2430 * max 1 ((N3 : ℝ)/N2) * max 1 ((N3 : ℝ)/N1) * E0.card := by
    have ht := card_mark_preimage_le P0 F0 r2 N2 r3 N3 (-r1-N1+1) N1 r3 N3
      hN2 hN3 hN1 hN3
    calc
      _ ≤ (9 * max 1 ((N3 : ℝ)/N2) * max 1 ((N3 : ℝ)/N1)) * F0.card := ht
      _ ≤ (9 * max 1 ((N3 : ℝ)/N2) * max 1 ((N3 : ℝ)/N1)) * (270*E0.card) :=
        mul_le_mul_of_nonneg_left hf0 (by positivity)
      _ = _ := by ring
  have ht1 : (T1.card : ℝ) ≤
      2430 * max 1 ((N2 : ℝ)/N3) * max 1 ((N2 : ℝ)/N1) * E1.card := by
    have ht := card_mark_preimage_le P1 F1 r3 N3 r2 N2 (-r1-N1+1) N1 (-r2-N2+1) N2
      hN3 hN2 hN1 hN2
    calc
      _ ≤ (9 * max 1 ((N2 : ℝ)/N3) * max 1 ((N2 : ℝ)/N1)) * F1.card := ht
      _ ≤ (9 * max 1 ((N2 : ℝ)/N3) * max 1 ((N2 : ℝ)/N1)) * (270*E1.card) :=
        mul_le_mul_of_nonneg_left hf1 (by positivity)
      _ = _ := by ring
  have ht2 : (T2.card : ℝ) ≤
      2430 * max 1 ((N1 : ℝ)/N3) * max 1 ((N1 : ℝ)/N2) * E2.card := by
    have ht := card_mark_preimage_le P2 F2 r3 N3 (-r1-N1+1) N1 (-r2-N2+1) N2 (-r1-N1+1) N1
      hN3 hN1 hN2 hN1
    calc
      _ ≤ (9 * max 1 ((N1 : ℝ)/N3) * max 1 ((N1 : ℝ)/N2)) * F2.card := ht
      _ ≤ (9 * max 1 ((N1 : ℝ)/N3) * max 1 ((N1 : ℝ)/N2)) * (270*E2.card) :=
        mul_le_mul_of_nonneg_left hf2 (by positivity)
      _ = _ := by ring
  have hq0 : (Q0.card : ℝ) ≤ (N1 : ℝ)+N2 := by
    have he : Q0 = interval (-r1-r2-N1-N2+2) (N1+N2-1) := by
      dsimp [Q0,interval]; congr 1; ring
    rw [he, NoncommutingBoxDeficit.interval_card_real _ _ (by omega)]
    push_cast
    linarith
  have hq1 : (Q1.card : ℝ) ≤ (N1 : ℝ)+N3 := by
    have he : Q1 = interval (-r1-N1+1+r3) (N1+N3-1) := by
      dsimp [Q1,interval]; congr 1; ring
    rw [he, NoncommutingBoxDeficit.interval_card_real _ _ (by omega)]
    push_cast
    linarith
  have hq2 : (Q2.card : ℝ) ≤ (N2 : ℝ)+N3 := by
    have he : Q2 = interval (r2+r3) (N2+N3-1) := by
      dsimp [Q2,interval]; congr 1; ring
    rw [he, NoncommutingBoxDeficit.interval_card_real _ _ (by omega)]
    push_cast
    linarith
  have hh := projection_hole_bounds (interval r1 N1) (interval r2 N2) (interval r3 N3) A hA
  have hh0 : (N3 : ℝ)*E0.card ≤ (B \ A).card := by
    have ht : ((interval r3 N3).card : ℝ)*E0.card ≤ (B \ A).card := by exact_mod_cast hh.1
    rwa [NoncommutingBoxDeficit.interval_card_real _ _ hN3] at ht
  have hh1 : (N2 : ℝ)*E1.card ≤ (B \ A).card := by
    have ht : ((interval r2 N2).card : ℝ)*E1.card ≤ (B \ A).card := by exact_mod_cast hh.2.1
    rwa [NoncommutingBoxDeficit.interval_card_real _ _ hN2] at ht
  have hh2 : (N1 : ℝ)*E2.card ≤ (B \ A).card := by
    have ht : ((interval r1 N1).card : ℝ)*E2.card ≤ (B \ A).card := by exact_mod_cast hh.2.2
    rwa [NoncommutingBoxDeficit.interval_card_real _ _ hN1] at ht
  have contribution (T E : Finset (ℤ × ℤ)) (q : ℕ) (a b c : ℤ)
      (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hq : (q : ℝ) ≤ (a : ℝ)+b)
      (ht : (T.card : ℝ) ≤ 2430 * max 1 ((c : ℝ)/b) * max 1 ((c : ℝ)/a) * E.card)
      (hh : (c : ℝ)*E.card ≤ (B \ A).card)
      (hcancel : ((a : ℝ)+b)/c * max 1 ((c : ℝ)/b) * max 1 ((c : ℝ)/a) ≤ 2*κ) :
      (q : ℝ)*T.card ≤ 4860*κ*(B \ A).card := by
    have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
    have habpos : (0 : ℝ) ≤ (a : ℝ)+b := by
      have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
      linarith
    have hscale := mul_le_mul_of_nonneg_right hcancel hcpos.le
    have he : (((a : ℝ)+b)/c * max 1 ((c : ℝ)/b) * max 1 ((c : ℝ)/a)) * c =
        ((a : ℝ)+b) * max 1 ((c : ℝ)/b) * max 1 ((c : ℝ)/a) := by
      field_simp
    rw [he] at hscale
    calc
      _ ≤ ((a : ℝ)+b) * (2430 * max 1 ((c : ℝ)/b) * max 1 ((c : ℝ)/a) * E.card) :=
        mul_le_mul hq ht (Nat.cast_nonneg _) habpos
      _ = 2430 * (((a : ℝ)+b) * max 1 ((c : ℝ)/b) * max 1 ((c : ℝ)/a)) * E.card := by ring
      _ ≤ 2430 * (2*κ*c) * E.card := by gcongr
      _ = (4860*κ) * ((c : ℝ)*E.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
  have hn1 : (0 : ℝ) < N1 := by exact_mod_cast (show 0 < N1 by omega)
  have hn2 : (0 : ℝ) < N2 := by exact_mod_cast (show 0 < N2 by omega)
  have hn3 : (0 : ℝ) < N3 := by exact_mod_cast (show 0 < N3 by omega)
  have hc0 := contribution T0 E0 Q0.card N1 N2 N3 hN1 hN2 hN3 hq0 ht0 hh0
    (aspect_cancellation _ _ _ κ hn1 hn2 hn3 hκ h12 h13 h21 h23 h31 h32)
  have hc1 := contribution T1 E1 Q1.card N1 N3 N2 hN1 hN3 hN2 hq1 ht1 hh1
    (aspect_cancellation _ _ _ κ hn1 hn3 hn2 hκ h13 h12 h31 h32 h21 h23)
  have hc2 := contribution T2 E2 Q2.card N2 N3 N1 hN2 hN3 hN1 hq2 ht2 hh2
    (aspect_cancellation _ _ _ κ hn2 hn3 hn1 hκ h23 h21 h32 h31 h12 h13)
  have hc' : (S.card : ℝ) ≤ (Q0.card : ℝ)*T0.card + (Q1.card : ℝ)*T1.card + (Q2.card : ℝ)*T2.card := by
    exact_mod_cast hc
  change (S.card : ℝ) ≤ 14580*κ*(B \ A).card
  linarith

/-- For an arbitrary translated positive integer box whose longest side is at
most `κ` times its shortest, the actual mixed-sum deficit is at most
`14580 κ` times its exact missing input mass. -/
theorem mixedSum_box_deficit_le
    (r1 N1 r2 N2 r3 N3 : ℤ) (κ : ℝ)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) (hκ : 1 ≤ κ)
    (hcomp : max (N1 : ℝ) (max (N2 : ℝ) (N3 : ℝ)) ≤
      κ * min (N1 : ℝ) (min (N2 : ℝ) (N3 : ℝ)))
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) :
    ((mixedSum (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \
      mixedSum A).card : ℝ) ≤
      14580*κ*((interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \ A).card := by
  have ratio (x y : ℝ)
      (hx : x ≤ max (N1 : ℝ) (max (N2 : ℝ) (N3 : ℝ)))
      (hy : min (N1 : ℝ) (min (N2 : ℝ) (N3 : ℝ)) ≤ y) : x ≤ κ*y :=
    hx.trans (hcomp.trans (mul_le_mul_of_nonneg_left hy (by linarith)))
  have hi1 : (N1 : ℝ) ≤ max (N1 : ℝ) (max (N2 : ℝ) (N3 : ℝ)) := le_max_left _ _
  have hi2 : (N2 : ℝ) ≤ max (N1 : ℝ) (max (N2 : ℝ) (N3 : ℝ)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hi3 : (N3 : ℝ) ≤ max (N1 : ℝ) (max (N2 : ℝ) (N3 : ℝ)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hj1 : min (N1 : ℝ) (min (N2 : ℝ) (N3 : ℝ)) ≤ N1 := min_le_left _ _
  have hj2 : min (N1 : ℝ) (min (N2 : ℝ) (N3 : ℝ)) ≤ N2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hj3 : min (N1 : ℝ) (min (N2 : ℝ) (N3 : ℝ)) ≤ N3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact mixedSum_box_deficit_le_ratios r1 N1 r2 N2 r3 N3 κ hN1 hN2 hN3 hκ
    (ratio _ _ hi1 hj2) (ratio _ _ hi1 hj3) (ratio _ _ hi2 hj1)
    (ratio _ _ hi2 hj3) (ratio _ _ hi3 hj1) (ratio _ _ hi3 hj2) A hA

example (r1 r2 r3 : ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 2 ×ˢ (interval r2 3 ×ˢ interval r3 4)) :
    ((mixedSum (interval r1 2 ×ˢ (interval r2 3 ×ˢ interval r3 4)) \ mixedSum A).card : ℝ) ≤
      14580*(2 : ℝ)*((interval r1 2 ×ˢ (interval r2 3 ×ˢ interval r3 4)) \ A).card := by
  exact mixedSum_box_deficit_le r1 2 r2 3 r3 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) A hA

example : (1 : ℤ) ≤ 2 ∧ (1 : ℤ) ≤ 3 ∧ (1 : ℤ) ≤ 4 ∧ (1 : ℝ) ≤ 2 ∧
    max (2 : ℝ) (max 3 4) ≤ 2*min (2 : ℝ) (min 3 4) ∧
    ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)) ⊆ interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4) ∧
    (interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4)).Nonempty := by
  norm_num [interval, Finset.singleton_subset_iff, Finset.mem_product, Finset.mem_Icc]

example (N : ℤ) (hN : 1 ≤ N) (r1 r2 r3 : ℤ)
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 1 ×ˢ (interval r2 N ×ˢ interval r3 N)) :
    ((mixedSum (interval r1 1 ×ˢ (interval r2 N ×ˢ interval r3 N)) \ mixedSum A).card : ℝ) ≤
      14580*(N : ℝ)*((interval r1 1 ×ˢ (interval r2 N ×ˢ interval r3 N)) \ A).card := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply mixedSum_box_deficit_le r1 1 r2 N r3 N N (by norm_num) hN hN hNr _ A hA
  simpa only [Int.cast_one, max_self, max_eq_right hNr, min_self,
    min_eq_left hNr, mul_one] using le_refl (N : ℝ)

example :
    ((mixedSum (interval 0 1 ×ˢ (interval 0 2 ×ˢ interval 0 2)) \ mixedSum {(0,0,0)}).card : ℝ) ≤
      14580*(2 : ℝ)*((interval 0 1 ×ˢ (interval 0 2 ×ˢ interval 0 2)) \ {(0,0,0)}).card := by
  exact mixedSum_box_deficit_le 0 1 0 2 0 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    {(0,0,0)} (by decide)

example : (1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 2 ∧ (1 : ℝ) ≤ 2 ∧
    max (1 : ℝ) (max 2 2) ≤ 2*min (1 : ℝ) (min 2 2) ∧
    ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)) ⊆ interval 0 1 ×ˢ (interval 0 2 ×ˢ interval 0 2) ∧
    (interval 0 1 ×ˢ (interval 0 2 ×ˢ interval 0 2)).Nonempty := by
  norm_num [interval, Finset.singleton_subset_iff, Finset.mem_product, Finset.mem_Icc]

example :
    ((mixedSum (interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4)) \ mixedSum ∅).card : ℝ) ≤
      14580*(2 : ℝ)*((interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4)) \ ∅).card := by
  exact mixedSum_box_deficit_le 0 2 0 3 0 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ∅
    (Finset.empty_subset _)

example :
    ((mixedSum (interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4)) \ mixedSum (interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4))).card : ℝ) ≤
      14580*(2 : ℝ)*((interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4)) \ (interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4))).card := by
  exact mixedSum_box_deficit_le 0 2 0 3 0 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (Finset.Subset.refl _)

end
end NoncommutingBoxLinearDeficit
