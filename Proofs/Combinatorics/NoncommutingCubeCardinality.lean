import Combinatorics.NoncommutingCubeDeficit

set_option autoImplicit false

namespace NoncommutingCubeCardinality

open NoncommutingFiber NoncommutingCubeCounting
open scoped Pointwise

private theorem interval_sum_witness (a b c d s : ℤ)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : a + c ≤ s ∧ s ≤ b + d) :
    ∃ x y : ℤ, (a ≤ x ∧ x ≤ b) ∧ (c ≤ y ∧ y ≤ d) ∧ x + y = s := by
  refine ⟨max a (s-d), s - max a (s-d), ?_⟩
  omega

/-- The actual mixed sum of a positive-side translated integer cube is exactly
its three signed output intervals: all three output coordinates vary independently. -/
theorem mixedSum_cube_eq (r1 r2 r3 N : ℤ) (hN : 1 ≤ N) :
    mixedSum (cube r1 r2 r3 N) =
      Finset.Icc (r2+r3) (r2+r3+2*N-2) ×ˢ
        (Finset.Icc (-r1+r3-N+1) (-r1+r3+N-1) ×ˢ
          Finset.Icc (-r1-r2-2*N+2) (-r1-r2)) := by
  apply Finset.Subset.antisymm
  · intro s hs
    exact Finset.mem_product.mpr
      ⟨(mixedSum_cube_ranges r1 r2 r3 N hN s hs).1,
        Finset.mem_product.mpr (mixedSum_cube_ranges r1 r2 r3 N hN s hs).2⟩
  · rintro ⟨a,b,c⟩ hs
    simp only [Finset.mem_product, Finset.mem_Icc] at hs
    obtain ⟨y0,z1,hy0,hz1,ha⟩ := interval_sum_witness
      r2 (r2+N-1) r3 (r3+N-1) a (by omega) (by omega) (by omega)
    obtain ⟨nx0,z2,hnx0,hz2,hb⟩ := interval_sum_witness
      (-r1-N+1) (-r1) r3 (r3+N-1) b (by omega) (by omega) (by omega)
    obtain ⟨nx1,ny2,hnx1,hny2,hc⟩ := interval_sum_witness
      (-r1-N+1) (-r1) (-r2-N+1) (-r2) c (by omega) (by omega) (by omega)
    have hp : (-nx0,y0,r3) ∈ cube r1 r2 r3 N := by
      simp only [cube, Finset.mem_product, Finset.mem_Icc]
      omega
    have hq : (-nx1,r2,z1) ∈ cube r1 r2 r3 N := by
      simp only [cube, Finset.mem_product, Finset.mem_Icc]
      omega
    have hr : (r1,-ny2,z2) ∈ cube r1 r2 r3 N := by
      simp only [cube, Finset.mem_product, Finset.mem_Icc]
      omega
    have he : L0 (-nx0,y0,r3) + L1 (-nx1,r2,z1) + L2 (r1,-ny2,z2) =
        (a,b,c) := by
      simp only [L0, L1, L2, Prod.mk_add_mk, neg_neg, add_zero, zero_add]
      exact Prod.ext ha (Prod.ext hb hc)
    rw [← he]
    exact Finset.add_mem_add
      (Finset.add_mem_add (Finset.mem_image_of_mem L0 hp)
        (Finset.mem_image_of_mem L1 hq)) (Finset.mem_image_of_mem L2 hr)

/-- The exact actual output cardinality of any translated cube of positive side. -/
theorem card_mixedSum_cube (r1 r2 r3 N : ℤ) (hN : 1 ≤ N) :
    (mixedSum (cube r1 r2 r3 N)).card = (2*N-1).toNat ^ 3 := by
  rw [mixedSum_cube_eq r1 r2 r3 N hN, Finset.card_product, Finset.card_product]
  obtain ⟨h0,h1,h2⟩ := output_interval_cards r1 r2 r3 N hN
  rw [h0,h1,h2]
  ring

/-- A positive-side translated cube has exactly the cube of its side length
many integer points. -/
theorem card_cube (r1 r2 r3 N : ℤ) (_hN : 1 ≤ N) :
    (cube r1 r2 r3 N).card = N.toNat ^ 3 := by
  have hi (r : ℤ) : (Finset.Icc r (r+N-1)).card = N.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  simp only [cube, Finset.card_product, hi]
  ring

/-- Enlarging the input cannot remove any actual mixed-sum output. -/
theorem mixedSum_mono {A B : Finset (ℤ × ℤ × ℤ)} (h : A ⊆ B) :
    mixedSum A ⊆ mixedSum B := by
  exact Finset.add_subset_add
    (Finset.add_subset_add (Finset.image_subset_image h) (Finset.image_subset_image h))
    (Finset.image_subset_image h)

/-- The actual cube deficit theorem gives a subtraction-free lower bound
with the exact full-cube output cardinality on the left. -/
theorem cube_raw_lower_bound (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ cube r1 r2 r3 N) :
    (2*N-1).toNat ^ 3 ≤ (mixedSum A).card +
      6480 * (cube r1 r2 r3 N \ A).card := by
  have hsplit := Finset.card_sdiff_add_card_eq_card (mixedSum_mono hA)
  have hd := NoncommutingCubeDeficit.mixedSum_cube_deficit_le r1 r2 r3 N hN A hA
  rw [card_mixedSum_cube r1 r2 r3 N hN] at hsplit
  omega

private theorem cube_boundary_cost (N : ℤ) (hN : 1 ≤ N) :
    8 * N.toNat ^ 3 ≤ (2*N-1).toNat ^ 3 + 12 * N.toNat ^ 2 := by
  have hn : (N.toNat : ℤ) = N := Int.toNat_of_nonneg (by omega)
  have hm : ((2*N-1).toNat : ℤ) = 2*(N.toNat : ℤ)-1 := by
    rw [Int.toNat_of_nonneg (by omega), hn]
  have hp : ((2*N-1).toNat : ℤ)^3 + 12*(N.toNat : ℤ)^2 =
      8*(N.toNat : ℤ)^3 + 6*(N.toNat : ℤ)-1 := by
    rw [hm]
    ring
  have hz : 8*(N.toNat : ℤ)^3 ≤
      ((2*N-1).toNat : ℤ)^3 + 12*(N.toNat : ℤ)^2 := by omega
  exact_mod_cast hz

/-- Every subset of a positive-side translated cube obeys the archive lower
bound, with missing input mass and a quadratic boundary cost. No density
hypothesis is needed, and all arithmetic is subtraction-free in naturals. -/
theorem cube_archive_lower_bound (r1 r2 r3 N : ℤ) (hN : 1 ≤ N)
    (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ cube r1 r2 r3 N) :
    8*A.card ≤ (mixedSum A).card +
      6480*((cube r1 r2 r3 N \ A).card + N.toNat^2) := by
  have hcard : A.card ≤ N.toNat^3 := by
    simpa only [card_cube r1 r2 r3 N hN] using Finset.card_le_card hA
  have hraw := cube_raw_lower_bound r1 r2 r3 N hN A hA
  have hboundary := cube_boundary_cost N hN
  nlinarith

example : (1 : ℤ) ≤ 1 ∧
    (cube 10 20 30 1).Nonempty ∧ (cube 10 20 30 2).Nonempty ∧
    ({(10,20,30)} : Finset (ℤ × ℤ × ℤ)) ⊆ cube 10 20 30 2 := by
  decide

example : 8*(cube 10 20 30 1).card ≤
    (mixedSum (cube 10 20 30 1)).card +
      6480*((cube 10 20 30 1 \ cube 10 20 30 1).card + (1 : ℤ).toNat^2) :=
  cube_archive_lower_bound 10 20 30 1 (by decide) _ (Finset.Subset.refl _)

example : 8*(∅ : Finset (ℤ × ℤ × ℤ)).card ≤ (mixedSum ∅).card +
    6480*((cube 10 20 30 1 \ ∅).card + (1 : ℤ).toNat^2) :=
  cube_archive_lower_bound 10 20 30 1 (by decide) ∅ (by decide)

example : 8*({(10,20,30)} : Finset (ℤ × ℤ × ℤ)).card ≤
    (mixedSum {(10,20,30)}).card +
      6480*((cube 10 20 30 2 \ {(10,20,30)}).card + (2 : ℤ).toNat^2) :=
  cube_archive_lower_bound 10 20 30 2 (by decide) {(10,20,30)} (by decide)

end NoncommutingCubeCardinality
