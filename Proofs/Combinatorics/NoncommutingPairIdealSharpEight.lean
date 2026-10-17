import Combinatorics.NoncommutingDownsetSharpEight

set_option autoImplicit false

namespace NoncommutingPairIdealSharpEight

open NoncommutingFiber NoncommutingCubeCounting
open scoped Pointwise

/-- A pair set is closed under decreasing both coordinates to nonnegative integers. -/
def PairIdeal (P : Finset (ℤ × ℤ)) : Prop :=
  ∀ s ∈ P, ∀ x y : ℤ, 0 ≤ x → x ≤ s.1 → 0 ≤ y → y ≤ s.2 → (x,y) ∈ P

example : PairIdeal {(0,0)} := by
  intro s hs x y hx hxs hy hys
  simp only [Finset.mem_singleton] at hs ⊢
  subst s
  dsimp at hxs hys
  have hxy : x = 0 ∧ y = 0 := by omega
  exact Prod.ext hxy.1 hxy.2

/-- Projection onto coordinates zero and one. -/
def π01 (s : ℤ × ℤ × ℤ) : ℤ × ℤ := (s.1,s.2.1)
/-- Projection onto coordinates zero and two. -/
def π02 (s : ℤ × ℤ × ℤ) : ℤ × ℤ := (s.1,s.2.2)
/-- Projection onto coordinates one and two. -/
def π12 (s : ℤ × ℤ × ℤ) : ℤ × ℤ := (s.2.1,s.2.2)

example : π01 (1,2,3) = (1,2) := rfl
example : π02 (1,2,3) = (1,3) := rfl
example : π12 (1,2,3) = (2,3) := rfl

/-- Downward closure inside the nonnegative cube, with an actual point as witness. -/
noncomputable def downClosure (N : ℤ) (A : Finset (ℤ × ℤ × ℤ)) :
    Finset (ℤ × ℤ × ℤ) :=
  (cube 0 0 0 N).filter (fun w => ∃ s ∈ A,
    w.1 ≤ s.1 ∧ w.2.1 ≤ s.2.1 ∧ w.2.2 ≤ s.2.2)

example : downClosure 1 {(0,0,0)} = {(0,0,0)} := by decide
example : downClosure 1 ∅ = ∅ := by simp [downClosure]

private theorem subset_downClosure (N : ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ cube 0 0 0 N) : A ⊆ downClosure N A := by
  intro s hs
  exact Finset.mem_filter.mpr ⟨hA hs, s, hs, le_rfl, le_rfl, le_rfl⟩

private theorem downClosure_down (N : ℤ) (A : Finset (ℤ × ℤ × ℤ)) :
    ∀ s ∈ downClosure N A, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ downClosure N A := by
  intro s hs w hx hxs hy hys hz hzs
  obtain ⟨hsQ, t, ht, htx, hty, htz⟩ := Finset.mem_filter.mp hs
  have hsB := hsQ
  simp only [cube, Finset.mem_product, Finset.mem_Icc] at hsB
  apply Finset.mem_filter.mpr
  constructor
  · simp only [cube, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hx, hxs.trans hsB.1.2⟩, ⟨hy, hys.trans hsB.2.1.2⟩,
      ⟨hz, hzs.trans hsB.2.2.2⟩⟩
  · exact ⟨t, ht, hxs.trans htx, hys.trans hty, hzs.trans htz⟩

private theorem image_downClosure (N : ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (hA : A ⊆ cube 0 0 0 N) (p : (ℤ × ℤ × ℤ) → ℤ × ℤ)
    (hp : ∀ w s : ℤ × ℤ × ℤ,
      0 ≤ w.1 → 0 ≤ w.2.1 → 0 ≤ w.2.2 →
      w.1 ≤ s.1 → w.2.1 ≤ s.2.1 → w.2.2 ≤ s.2.2 →
      0 ≤ (p w).1 ∧ (p w).1 ≤ (p s).1 ∧
      0 ≤ (p w).2 ∧ (p w).2 ≤ (p s).2)
    (hi : PairIdeal (A.image p)) :
    (downClosure N A).image p = A.image p := by
  apply Finset.Subset.antisymm
  · intro q hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hwQ, s, hs, hx, hy, hz⟩ := Finset.mem_filter.mp hw
    simp only [cube, Finset.mem_product, Finset.mem_Icc] at hwQ
    have hb := hp w s hwQ.1.1 hwQ.2.1.1 hwQ.2.2.1 hx hy hz
    exact hi (p s) (Finset.mem_image_of_mem p hs) (p w).1 (p w).2
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  · exact Finset.image_subset_image (subset_downClosure N A hA)

/-- Equal actual pair projections give equal actual three-independent-choice mixed sums. -/
theorem mixedSum_eq_of_pair_images (A B : Finset (ℤ × ℤ × ℤ))
    (h01 : A.image π01 = B.image π01)
    (h02 : A.image π02 = B.image π02)
    (h12 : A.image π12 = B.image π12) : mixedSum A = mixedSum B := by
  have h0 := congrArg (Finset.image (fun p : ℤ × ℤ => (p.2,-p.1,(0 : ℤ)))) h01
  have h1 := congrArg (Finset.image (fun p : ℤ × ℤ => (p.2,(0 : ℤ),-p.1))) h02
  have h2 := congrArg (Finset.image (fun p : ℤ × ℤ => ((0 : ℤ),p.2,-p.1))) h12
  simp only [Finset.image_image] at h0 h1 h2
  change A.image L0 = B.image L0 at h0
  change A.image L1 = B.image L1 at h1
  change A.image L2 = B.image L2 at h2
  simp only [mixedSum, h0, h1, h2]

/-- For every subset of a positive nonnegative cube whose three actual pair
projections are ideals, the actual mixed-sum deficit is at most eight times
its input deficit. No down-closure of the input set is assumed. -/
theorem mixedSum_cube_deficit_le (N : ℤ) (hN : 1 ≤ N)
    (A : Finset (ℤ × ℤ × ℤ)) (hA : A ⊆ cube 0 0 0 N)
    (h01 : PairIdeal (A.image π01)) (h02 : PairIdeal (A.image π02))
    (h12 : PairIdeal (A.image π12)) :
    (mixedSum (cube 0 0 0 N) \ mixedSum A).card ≤
      8 * (cube 0 0 0 N \ A).card := by
  have he01 := image_downClosure N A hA π01 (by
    intro w s hx hy hz hxs hys hzs
    exact ⟨hx,hxs,hy,hys⟩) h01
  have he02 := image_downClosure N A hA π02 (by
    intro w s hx hy hz hxs hys hzs
    exact ⟨hx,hxs,hz,hzs⟩) h02
  have he12 := image_downClosure N A hA π12 (by
    intro w s hx hy hz hxs hys hzs
    exact ⟨hy,hys,hz,hzs⟩) h12
  have hm := mixedSum_eq_of_pair_images (downClosure N A) A he01 he02 he12
  have hd := NoncommutingDownsetSharpEight.mixedSum_cube_deficit_le N hN
    (downClosure N A) (Finset.filter_subset _ _) (downClosure_down N A)
  rw [hm] at hd
  apply hd.trans
  apply Nat.mul_le_mul_left 8
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsQ, hsD⟩ := Finset.mem_sdiff.mp hs
  exact Finset.mem_sdiff.mpr ⟨hsQ, fun hsA => hsD (subset_downClosure N A hA hsA)⟩

/-- The twenty points of the side-three cube with at most one coordinate equal to two. -/
noncomputable def exampleB : Finset (ℤ × ℤ × ℤ) :=
  (cube 0 0 0 3).filter (fun s =>
    (s.1 ≠ 2 ∨ s.2.1 ≠ 2) ∧ (s.1 ≠ 2 ∨ s.2.2 ≠ 2) ∧
    (s.2.1 ≠ 2 ∨ s.2.2 ≠ 2))

/-- Removing the origin destroys down-closure without changing the three pair ideals. -/
noncomputable def exampleA : Finset (ℤ × ℤ × ℤ) := exampleB.erase (0,0,0)

/-- The common eight-point pair ideal, missing the upper corner of the side-three square. -/
noncomputable def exampleP : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2).erase (2,2)

example : exampleB.card = 20 := by decide
example : exampleA.card = 19 := by decide
example : exampleP.card = 8 := by decide

/-- The eight-point square with its upper corner removed is a pair ideal. -/
theorem exampleP_ideal : PairIdeal exampleP := by
  intro s hs x y hx hxs hy hys
  simp only [exampleP, Finset.mem_erase, Finset.mem_product,
    Finset.mem_Icc] at hs ⊢
  constructor
  · intro he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp at he1 he2
    have hs1 : s.1 = 2 := by omega
    have hs2 : s.2 = 2 := by omega
    exact hs.1 (Prod.ext hs1 hs2)
  · exact ⟨⟨hx, hxs.trans hs.2.1.2⟩, ⟨hy, hys.trans hs.2.2.2⟩⟩

/-- All three actual pair projections in the non-downset example equal the proper eight-point ideal. -/
theorem example_pair_images :
    exampleA.image π01 = exampleP ∧ exampleA.image π02 = exampleP ∧
      exampleA.image π12 = exampleP := by decide

/-- The example jointly satisfies cube containment and all three pair-ideal hypotheses. -/
theorem example_hypotheses : exampleA ⊆ cube 0 0 0 3 ∧
    PairIdeal (exampleA.image π01) ∧ PairIdeal (exampleA.image π02) ∧
      PairIdeal (exampleA.image π12) := by
  refine ⟨?_, ?_⟩
  · exact (Finset.erase_subset _ _).trans (Finset.filter_subset _ _)
  · rw [example_pair_images.1, example_pair_images.2.1, example_pair_images.2.2]
    exact ⟨exampleP_ideal, exampleP_ideal, exampleP_ideal⟩

/-- The example is genuinely outside the coordinate-downset theorem's input class. -/
theorem example_not_downclosed :
    ¬ (∀ s ∈ exampleA, ∀ w : ℤ × ℤ × ℤ,
      0 ≤ w.1 → w.1 ≤ s.1 → 0 ≤ w.2.1 → w.2.1 ≤ s.2.1 →
      0 ≤ w.2.2 → w.2.2 ≤ s.2.2 → w ∈ exampleA) := by
  intro hd
  have hs : (1,0,0) ∈ exampleA := by decide
  have hz := hd (1,0,0) hs (0,0,0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hn : (0,0,0) ∉ exampleA := by decide
  exact hn hz

/-- The down-closure bridge fills exactly the deleted origin in this example. -/
theorem example_downClosure : downClosure 3 exampleA = exampleB := by decide

end NoncommutingPairIdealSharpEight
