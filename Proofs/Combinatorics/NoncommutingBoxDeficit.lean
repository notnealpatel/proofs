import Combinatorics.NoncommutingBoxHalo
import Combinatorics.NoncommutingCubeCounting

set_option autoImplicit false

namespace NoncommutingBoxDeficit

noncomputable section
open NoncommutingBoxWindows NoncommutingBoxHalo NoncommutingCubeCounting
open NoncommutingProjectionHoles NoncommutingFiber NoncommutingDense
open scoped Pointwise

/-- Actual box outputs lie in their three signed sum intervals. -/
theorem mixedSum_box_ranges (r1 N1 r2 N2 r3 N3 : ℤ)
    (s : ℤ × ℤ × ℤ)
    (hs : s ∈ mixedSum (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3))) :
    s.1 ∈ Finset.Icc (r2+r3) (r2+r3+N2+N3-2) ∧
    s.2.1 ∈ Finset.Icc (-r1-N1+1+r3) (-r1+r3+N3-1) ∧
    s.2.2 ∈ Finset.Icc (-r1-r2-N1-N2+2) (-r1-r2) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hs
  obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_add.mp hu
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
  simp only [interval, Finset.mem_product, Finset.mem_Icc] at hx hy hz
  simp only [L0, L1, L2, Prod.fst_add, Prod.snd_add, Finset.mem_Icc]
  omega

/-- Unequal actual pair marks have at most four preimages per halo point. -/
theorem card_actualMark_preimage_le (a u b v a' u' b' v' : ℤ)
    (P H : Finset (ℤ × ℤ)) :
    (P.filter (fun p => (actualMark a u b v p.1,
      actualMark a' u' b' v' p.2) ∈ H)).card ≤ 4 * H.card := by
  classical
  let T := P.filter (fun p => (actualMark a u b v p.1,
    actualMark a' u' b' v' p.2) ∈ H)
  let f := fun p : ℤ × ℤ => (actualMark a u b v p.1, actualMark a' u' b' v' p.2)
  have hc : T.card ≤ 4 * (T.image f).card :=
    Finset.card_le_mul_card_image T 4 (fun q _ => by
      rcases q with ⟨q,q'⟩
      simpa only [f, Prod.mk.injEq] using
        card_actualMark_pair_fiber_le_four a u b v a' u' b' v' q q' T)
  have hi : T.image f ⊆ H := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hp).2
  exact hc.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card hi))

/-- Comparable-box density bounds a fixed-grid halo by `324 κ⁴` per hole. -/
theorem card_actualGrid_halo_le (a u v c w t : ℤ) (κ : ℝ)
    (hu : 1 ≤ u) (hw : 1 ≤ w) (hκ : 1 ≤ κ)
    (E : Finset (ℤ × ℤ)) (hE : E ⊆ actualGrid a u v ×ˢ actualGrid c w t) :
    ((rectangleHalo (actualGrid a u v) (actualGrid c w t) E (1/(3*κ^2))).card : ℝ)
      ≤ 324*κ^4*E.card := by
  have hd := halo_density_bounds κ hκ
  have hb := rectangleHalo_card_le a (a+max u v-1) c (c+max w t-1)
    (by omega) (by omega) E hE (1/(3*κ^2)) hd.1 hd.2
  have hp : 0 < κ := by linarith
  have he : 18*(2-1/(3*κ^2))/(1/(3*κ^2))^2 ≤ 324*κ^4 := by
    field_simp
    nlinarith [sq_nonneg κ]
  exact hb.trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))

/-- An original interval is contained in its expanded actual grid. -/
theorem interval_subset_actualGrid (a u v : ℤ) : interval a u ⊆ actualGrid a u v := by
  intro x hx
  simp only [interval, actualGrid, Finset.mem_Icc] at hx ⊢
  omega

/-- A positive integer interval has its stated real cardinality. -/
theorem interval_card_real (r N : ℤ) (hN : 1 ≤ N) :
    ((interval r N).card : ℝ) = N := by
  rw [interval, Int.card_Icc]
  have he : r+N-1+1-r = N := by ring
  rw [he]
  exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ N by omega)


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
      7776*κ^5*( (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \ A).card := by
  classical
  let B := interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)
  let S := mixedSum B \ mixedSum A
  let E0 := H0 (interval r1 N1) (interval r2 N2) A
  let E1 := H1 (interval r1 N1) (interval r3 N3) A
  let E2 := H2 (interval r2 N2) (interval r3 N3) A
  let F0 := rectangleHalo (actualGrid r2 N2 N3) (actualGrid (-r1-N1+1) N1 N3) E0 (1/(3*κ^2))
  let F1 := rectangleHalo (actualGrid r3 N3 N2) (actualGrid (-r1-N1+1) N1 N2) E1 (1/(3*κ^2))
  let F2 := rectangleHalo (actualGrid r3 N3 N1) (actualGrid (-r2-N2+1) N2 N1) E2 (1/(3*κ^2))
  let P0 := S.image (fun s => (s.1,s.2.1))
  let P1 := S.image (fun s => (s.1,s.2.2))
  let P2 := S.image (fun s => (s.2.1,s.2.2))
  let T0 := P0.filter (fun p =>
    (actualMark r2 N2 r3 N3 p.1, actualMark (-r1-N1+1) N1 r3 N3 p.2) ∈ F0)
  let T1 := P1.filter (fun p =>
    (actualMark r3 N3 r2 N2 p.1, actualMark (-r1-N1+1) N1 (-r2-N2+1) N2 p.2) ∈ F1)
  let T2 := P2.filter (fun p =>
    (actualMark r3 N3 (-r1-N1+1) N1 p.1,
      actualMark (-r2-N2+1) N2 (-r1-N1+1) N1 p.2) ∈ F2)
  let Q0 := Finset.Icc (-r1-r2-N1-N2+2) (-r1-r2)
  let Q1 := Finset.Icc (-r1-N1+1+r3) (-r1+r3+N3-1)
  let Q2 := Finset.Icc (r2+r3) (r2+r3+N2+N3-2)
  have hcover : ∀ s ∈ S,
      ((s.1,s.2.1) ∈ T0 ∧ s.2.2 ∈ Q0) ∨
      ((s.1,s.2.2) ∈ T1 ∧ s.2.1 ∈ Q1) ∨
      ((s.2.1,s.2.2) ∈ T2 ∧ s.1 ∈ Q2) := by
    intro s hs
    obtain ⟨hsum,hm⟩ := Finset.mem_sdiff.mp hs
    have hr := mixedSum_box_ranges r1 N1 r2 N2 r3 N3 s hsum
    have hc := missing_output_mem_halo r1 N1 r2 N2 r3 N3 κ
      hN1 hN2 hN3 hκ h12 h13 h21 h23 h31 h32 A hA s hsum hm
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hs,hc⟩,hr.2.2⟩
    · exact Or.inr (Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hs,hc⟩,hr.2.1⟩)
    · exact Or.inr (Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hs,hc⟩,hr.1⟩)
  have hc := card_le_pair_lift_union S T0 T1 T2 Q0 Q1 Q2 hcover
  have hgrid (a u v c w t : ℤ) (E : Finset (ℤ × ℤ))
      (he : E ⊆ interval a u ×ˢ interval c w) :
      E ⊆ actualGrid a u v ×ˢ actualGrid c w t := by
    intro p hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp (he hp)
    exact Finset.mem_product.mpr ⟨interval_subset_actualGrid _ _ _ hx,
      interval_subset_actualGrid _ _ _ hy⟩
  have hf0 : (F0.card : ℝ) ≤ 324*κ^4*E0.card := by
    apply card_actualGrid_halo_le _ _ _ _ _ _ κ hN2 hN1 hκ
    apply hgrid
    simpa only [E0,H0,G0,image_neg_interval r1 N1 hN1] using
      (Finset.sdiff_subset : E0 ⊆ G0 (interval r1 N1) (interval r2 N2))
  have hf1 : (F1.card : ℝ) ≤ 324*κ^4*E1.card := by
    apply card_actualGrid_halo_le _ _ _ _ _ _ κ hN3 hN1 hκ
    apply hgrid
    simpa only [E1,H1,G1,image_neg_interval r1 N1 hN1] using
      (Finset.sdiff_subset : E1 ⊆ G1 (interval r1 N1) (interval r3 N3))
  have hf2 : (F2.card : ℝ) ≤ 324*κ^4*E2.card := by
    apply card_actualGrid_halo_le _ _ _ _ _ _ κ hN3 hN2 hκ
    apply hgrid
    simpa only [E2,H2,G2,image_neg_interval r2 N2 hN2] using
      (Finset.sdiff_subset : E2 ⊆ G2 (interval r2 N2) (interval r3 N3))
  have ht0 : (T0.card : ℝ) ≤ 1296*κ^4*E0.card := by
    have ht := card_actualMark_preimage_le r2 N2 r3 N3 (-r1-N1+1) N1 r3 N3 P0 F0
    have ht' : (T0.card : ℝ) ≤ 4*F0.card := by exact_mod_cast ht
    linarith
  have ht1 : (T1.card : ℝ) ≤ 1296*κ^4*E1.card := by
    have ht := card_actualMark_preimage_le r3 N3 r2 N2 (-r1-N1+1) N1 (-r2-N2+1) N2 P1 F1
    have ht' : (T1.card : ℝ) ≤ 4*F1.card := by exact_mod_cast ht
    linarith
  have ht2 : (T2.card : ℝ) ≤ 1296*κ^4*E2.card := by
    have ht := card_actualMark_preimage_le r3 N3 (-r1-N1+1) N1 (-r2-N2+1) N2 (-r1-N1+1) N1 P2 F2
    have ht' : (T2.card : ℝ) ≤ 4*F2.card := by exact_mod_cast ht
    linarith
  have hq0 : (Q0.card : ℝ) ≤ 2*κ*N3 := by
    have he : Q0 = interval (-r1-r2-N1-N2+2) (N1+N2-1) := by
      dsimp [Q0,interval]; congr 1; ring
    rw [he, interval_card_real _ _ (by omega)]
    push_cast
    linarith
  have hq1 : (Q1.card : ℝ) ≤ 2*κ*N2 := by
    have he : Q1 = interval (-r1-N1+1+r3) (N1+N3-1) := by
      dsimp [Q1,interval]; congr 1; ring
    rw [he, interval_card_real _ _ (by omega)]
    push_cast
    linarith
  have hq2 : (Q2.card : ℝ) ≤ 2*κ*N1 := by
    have he : Q2 = interval (r2+r3) (N2+N3-1) := by
      dsimp [Q2,interval]; congr 1; ring
    rw [he, interval_card_real _ _ (by omega)]
    push_cast
    linarith
  have hh := projection_hole_bounds (interval r1 N1) (interval r2 N2) (interval r3 N3) A hA
  have hh0 : (N3 : ℝ)*E0.card ≤ (B \ A).card := by
    have ht : ((interval r3 N3).card : ℝ)*E0.card ≤ (B \ A).card := by exact_mod_cast hh.1
    rwa [interval_card_real _ _ hN3] at ht
  have hh1 : (N2 : ℝ)*E1.card ≤ (B \ A).card := by
    have ht : ((interval r2 N2).card : ℝ)*E1.card ≤ (B \ A).card := by exact_mod_cast hh.2.1
    rwa [interval_card_real _ _ hN2] at ht
  have hh2 : (N1 : ℝ)*E2.card ≤ (B \ A).card := by
    have ht : ((interval r1 N1).card : ℝ)*E2.card ≤ (B \ A).card := by exact_mod_cast hh.2.2
    rwa [interval_card_real _ _ hN1] at ht
  have contribution (T E : Finset (ℤ × ℤ)) (q : ℕ) (n : ℤ)
      (hn : 1 ≤ n) (hq : (q : ℝ) ≤ 2*κ*n)
      (ht : (T.card : ℝ) ≤ 1296*κ^4*E.card)
      (hh : (n : ℝ)*E.card ≤ (B \ A).card) :
      (q : ℝ)*T.card ≤ 2592*κ^5*(B \ A).card := by
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast (show 0 ≤ n by omega)
    calc
      (q : ℝ)*T.card ≤ (2*κ*n)*(1296*κ^4*E.card) :=
        mul_le_mul hq ht (Nat.cast_nonneg _) (by positivity)
      _ = (2592*κ^5)*((n : ℝ)*E.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
  have hc0 := contribution T0 E0 Q0.card N3 hN3 hq0 ht0 hh0
  have hc1 := contribution T1 E1 Q1.card N2 hN2 hq1 ht1 hh1
  have hc2 := contribution T2 E2 Q2.card N1 hN1 hq2 ht2 hh2
  have hc' : (S.card : ℝ) ≤ (Q0.card : ℝ)*T0.card + (Q1.card : ℝ)*T1.card + (Q2.card : ℝ)*T2.card := by
    exact_mod_cast hc
  change (S.card : ℝ) ≤ 7776*κ^5*(B \ A).card
  linarith

/-- For an arbitrary translated positive integer box whose longest side is at
most `κ` times its shortest, the actual mixed-sum deficit is at most
`7776 κ⁵` times its exact missing input mass. -/
theorem mixedSum_box_deficit_le
    (r1 N1 r2 N2 r3 N3 : ℤ) (κ : ℝ)
    (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2) (hN3 : 1 ≤ N3) (hκ : 1 ≤ κ)
    (hcomp : max (N1 : ℝ) (max (N2 : ℝ) (N3 : ℝ)) ≤
      κ * min (N1 : ℝ) (min (N2 : ℝ) (N3 : ℝ)))
    (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) :
    ((mixedSum (interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \
      mixedSum A).card : ℝ) ≤
      7776*κ^5*((interval r1 N1 ×ˢ (interval r2 N2 ×ˢ interval r3 N3)) \ A).card := by
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
      7776*(2 : ℝ)^5*((interval r1 2 ×ˢ (interval r2 3 ×ˢ interval r3 4)) \ A).card := by
  exact mixedSum_box_deficit_le r1 2 r2 3 r3 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) A hA

example : (1 : ℤ) ≤ 2 ∧ (1 : ℤ) ≤ 3 ∧ (1 : ℤ) ≤ 4 ∧ (1 : ℝ) ≤ 2 ∧
    max (2 : ℝ) (max 3 4) ≤ 2*min (2 : ℝ) (min 3 4) ∧
    ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)) ⊆ interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4) ∧
    (interval 0 2 ×ˢ (interval 0 3 ×ˢ interval 0 4)).Nonempty := by
  norm_num [interval, Finset.singleton_subset_iff, Finset.mem_product, Finset.mem_Icc]

end
end NoncommutingBoxDeficit
