import Combinatorics.NoncommutingCubeWindows
import Combinatorics.NoncommutingCubeCounting
import Combinatorics.NoncommutingDenseHalo

set_option autoImplicit false

namespace NoncommutingCubeDeficit

noncomputable section
open NoncommutingCubeWindows NoncommutingCubeCounting NoncommutingProjectionHoles
open NoncommutingFiber NoncommutingDense

/-- An actual dense interval certificate places its mark in the one-third halo,
without changing either the signed grid or the hole set. -/
theorem mem_halo_of_certificate (X Y U V : Finset ℤ) (H : Finset (ℤ × ℤ))
    (p : ℤ × ℤ) (hc : RectangleCertificate X Y H U V p) :
    p ∈ rectangleHalo U V H (1/3) := by
  classical
  obtain ⟨_, _, ⟨l,u,hlu,hX⟩, ⟨s,t,hst,hY⟩, hXU, hYV, hp, hd⟩ := hc
  subst X
  subst Y
  obtain ⟨hpx,hpy⟩ := Finset.mem_product.mp hp
  have hl : l ∈ U := hXU (Finset.mem_Icc.mpr ⟨le_rfl,hlu⟩)
  have hu : u ∈ U := hXU (Finset.mem_Icc.mpr ⟨hlu,le_rfl⟩)
  have hs : s ∈ V := hYV (Finset.mem_Icc.mpr ⟨le_rfl,hst⟩)
  have ht : t ∈ V := hYV (Finset.mem_Icc.mpr ⟨hst,le_rfl⟩)
  have hd' : ((Finset.Icc l u).card : ℝ) * (Finset.Icc s t).card ≤
      3 * ((H ∩ (Finset.Icc l u ×ˢ Finset.Icc s t)).card : ℝ) := by
    exact_mod_cast (show (Finset.Icc l u).card * (Finset.Icc s t).card ≤ _ by
      simpa only [Finset.card_product] using hd)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hXU hpx,hYV hpy⟩,
    l,hl,u,hu,s,hs,t,ht,hlu,hst,hXU,hYV,hpx,hpy,?_⟩
  linarith

/-- A finite collection of source pairs whose marks lie in a given halo has
at most four times as many elements as the halo. -/
theorem card_mark_preimage_le (a b c d N : ℤ) (P H : Finset (ℤ × ℤ)) :
    (P.filter (fun p => (mark a b N p.1, mark c d N p.2) ∈ H)).card ≤
      4 * H.card := by
  classical
  let T := P.filter (fun p => (mark a b N p.1, mark c d N p.2) ∈ H)
  let f := fun p : ℤ × ℤ => (mark a b N p.1, mark c d N p.2)
  have hc : T.card ≤ 4 * (T.image f).card :=
    Finset.card_le_mul_card_image T 4 (fun q _ =>
      card_mark_pair_fiber_le_four a b c d N q T)
  have hi : T.image f ⊆ H := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hp).2
  exact hc.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card hi))

/-- The one-third halo in any two signed length-`N` grids costs at most 270
points per projection hole. -/
theorem card_halo_C_le (a c N : ℤ) (hN : 1 ≤ N) (E : Finset (ℤ × ℤ))
    (hE : E ⊆ C a N ×ˢ C c N) :
    (rectangleHalo (C a N) (C c N) E (1/3)).card ≤ 270 * E.card := by
  exact rectangleHalo_third_bound a (a+N-1) c (c+N-1)
    (by omega) (by omega) E hE

/-- For a subset of an actual translated equal-sided integer cube, the deficit
in the actual noncommuting mixed sum is at most 6480 times the missing input
mass. This is the equal-cube implication, with no geometric premises. -/
theorem mixedSum_cube_deficit_le (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ cube r1 r2 r3 N) :
    (mixedSum (cube r1 r2 r3 N) \ mixedSum A).card ≤
      6480 * (cube r1 r2 r3 N \ A).card := by
  classical
  let S := mixedSum (cube r1 r2 r3 N) \ mixedSum A
  let E0 := H0 (C r1 N) (C r2 N) A
  let E1 := H1 (C r1 N) (C r3 N) A
  let E2 := H2 (C r2 N) (C r3 N) A
  let F0 := rectangleHalo (C r2 N) (C (-r1-N+1) N) E0 (1/3)
  let F1 := rectangleHalo (C r3 N) (C (-r1-N+1) N) E1 (1/3)
  let F2 := rectangleHalo (C r3 N) (C (-r2-N+1) N) E2 (1/3)
  let P0 := S.image (fun s => (s.1,s.2.1))
  let P1 := S.image (fun s => (s.1,s.2.2))
  let P2 := S.image (fun s => (s.2.1,s.2.2))
  let T0 := P0.filter (fun p =>
    (mark r2 r3 N p.1, mark (-r1-N+1) r3 N p.2) ∈ F0)
  let T1 := P1.filter (fun p =>
    (mark r3 r2 N p.1, mark (-r1-N+1) (-r2-N+1) N p.2) ∈ F1)
  let T2 := P2.filter (fun p =>
    (mark r3 (-r1-N+1) N p.1, mark (-r2-N+1) (-r1-N+1) N p.2) ∈ F2)
  have hf0 : F0.card ≤ 270 * E0.card := by
    apply card_halo_C_le _ _ _ hN
    simpa only [E0, H0, G0, neg_C] using
      (Finset.sdiff_subset : H0 (C r1 N) (C r2 N) A ⊆ G0 (C r1 N) (C r2 N))
  have hf1 : F1.card ≤ 270 * E1.card := by
    apply card_halo_C_le _ _ _ hN
    simpa only [E1, H1, G1, neg_C] using
      (Finset.sdiff_subset : H1 (C r1 N) (C r3 N) A ⊆ G1 (C r1 N) (C r3 N))
  have hf2 : F2.card ≤ 270 * E2.card := by
    apply card_halo_C_le _ _ _ hN
    simpa only [E2, H2, G2, neg_C] using
      (Finset.sdiff_subset : H2 (C r2 N) (C r3 N) A ⊆ G2 (C r2 N) (C r3 N))
  have ht0 : T0.card ≤ 1080 * E0.card :=
    (card_mark_preimage_le r2 r3 (-r1-N+1) r3 N P0 F0).trans
      (by omega)
  have ht1 : T1.card ≤ 1080 * E1.card :=
    (card_mark_preimage_le r3 r2 (-r1-N+1) (-r2-N+1) N P1 F1).trans
      (by omega)
  have ht2 : T2.card ≤ 1080 * E2.card :=
    (card_mark_preimage_le r3 (-r1-N+1) (-r2-N+1) (-r1-N+1) N P2 F2).trans
      (by omega)
  have hcover : ∀ s ∈ S, (s.1,s.2.1) ∈ T0 ∨
      (s.1,s.2.2) ∈ T1 ∨ (s.2.1,s.2.2) ∈ T2 := by
    intro s hs
    obtain ⟨hsum, hmiss⟩ := Finset.mem_sdiff.mp hs
    have hc := missing_output_certificate r1 r2 r3 N hN A hA s hsum hmiss
    rcases hc with hc0 | hc1 | hc2
    · exact Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ hs, mem_halo_of_certificate _ _ _ _ _ _ hc0⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ hs, mem_halo_of_certificate _ _ _ _ _ _ hc1⟩))
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ hs, mem_halo_of_certificate _ _ _ _ _ _ hc2⟩))
  have hcount := card_le_cube_pair_union r1 r2 r3 N hN S T0 T1 T2
    Finset.sdiff_subset hcover
  have hcard (r : ℤ) : (C r N).card = N.toNat := by
    rw [C, Int.card_Icc]
    congr 1
    ring
  have hholes := projection_hole_bounds (C r1 N) (C r2 N) (C r3 N) A hA
  rw [hcard r1, hcard r2, hcard r3] at hholes
  let h := (cube r1 r2 r3 N \ A).card
  have he : N.toNat * (E0.card + E1.card + E2.card) ≤ 3*h := by
    obtain ⟨he0,he1,he2⟩ := hholes
    change N.toNat * E0.card ≤ h at he0
    change N.toNat * E1.card ≤ h at he1
    change N.toNat * E2.card ≤ h at he2
    nlinarith
  have ht : T0.card + T1.card + T2.card ≤
      1080 * (E0.card + E1.card + E2.card) := by omega
  have hm : (2*N-1).toNat ≤ 2*N.toNat := by omega
  have hn : 0 < N.toNat := by omega
  have hscaled : N.toNat * S.card ≤ N.toNat * (6480*h) := by
    calc
      N.toNat * S.card ≤ N.toNat * ((2*N-1).toNat *
          (T0.card + T1.card + T2.card)) := Nat.mul_le_mul_left _ hcount
      _ ≤ N.toNat * ((2*N-1).toNat *
          (1080 * (E0.card + E1.card + E2.card))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
      _ = ((2*N-1).toNat * 1080) *
          (N.toNat * (E0.card + E1.card + E2.card)) := by ring
      _ ≤ ((2*N-1).toNat * 1080) * (3*h) := Nat.mul_le_mul_left _ he
      _ = (2*N-1).toNat * (3240*h) := by ring
      _ ≤ (2*N.toNat) * (3240*h) := Nat.mul_le_mul_right _ hm
      _ = N.toNat * (6480*h) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hn

example : RectangleCertificate {10} {20} {(10,20)} {10} {20} (10,20) := by
  exact ⟨by decide, by decide, ⟨10,10,by decide,by decide⟩,
    ⟨20,20,by decide,by decide⟩,by decide,by decide,by decide,by decide⟩

example : (cube 10 20 30 1).Nonempty ∧ (cube 10 20 30 2).Nonempty := by
  exact ⟨⟨(10,20,30),corner_mem_cube _ _ _ _ (by decide)⟩,
    ⟨(10,20,30),corner_mem_cube _ _ _ _ (by decide)⟩⟩

example : (mixedSum (cube 10 20 30 1) \ mixedSum (cube 10 20 30 1)).card ≤
    6480 * (cube 10 20 30 1 \ cube 10 20 30 1).card :=
  mixedSum_cube_deficit_le 10 20 30 1 (by decide) _ (Finset.Subset.refl _)

example : (mixedSum (cube 10 20 30 1) \ mixedSum ∅).card ≤
    6480 * (cube 10 20 30 1 \ ∅).card :=
  mixedSum_cube_deficit_le 10 20 30 1 (by decide) ∅ (by decide)

example : (mixedSum (cube 10 20 30 2) \ mixedSum {(10,20,30)}).card ≤
    6480 * (cube 10 20 30 2 \ {(10,20,30)}).card :=
  mixedSum_cube_deficit_le 10 20 30 2 (by decide) {(10,20,30)} (by decide)

end
end NoncommutingCubeDeficit
