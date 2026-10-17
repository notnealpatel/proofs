import Combinatorics.ElementaryLoomisWhitneySmallError
import Sorry.Combinatorics.NoncommutingGoodAnchorGap

set_option autoImplicit false

namespace NoncommutingMicroGap

open NoncommutingGoodAnchorGap

/-- A top quantile pool has exactly ceiling one tenth of the axis, and
any anchor in it retains at least nine tenths of that axis below it. -/
theorem exists_top_pool (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ T : Finset ℤ, T ⊆ S ∧ T.card = (S.card+9)/10 ∧ T.Nonempty ∧
      ∀ t ∈ T, 9*S.card ≤ 10*(S.filter (· ≤ t)).card := by
  let b := S.card
  let k := (b+9)/10
  have hb : 0 < b := Finset.card_pos.mpr hS
  have hk : 0 < k := by dsimp [k]; omega
  have hkb : k ≤ b := by dsimp [k]; omega
  let e := S.orderEmbOfFin rfl
  let f : Fin k → ℤ := fun i => e ⟨b-k+i.val, by omega⟩
  let T := Finset.univ.image f
  have hf : Function.Injective f := by
    intro i j hij
    have hh := e.injective hij
    have hv := congrArg (fun i : Fin b => i.val) hh
    apply Fin.ext
    dsimp only [f] at hv
    omega
  have hc : T.card = k := by simp [T,Finset.card_image_of_injective _ hf]
  have hsub : T ⊆ S := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact S.orderEmbOfFin_mem rfl _
  refine ⟨T,hsub,hc,Finset.card_pos.mp (by omega),?_⟩
  intro t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  let g : Fin (b-k+1) → ℤ := fun i => e ⟨i.val,by omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    have hh := e.injective hij
    exact Fin.ext (congrArg (fun i : Fin b => i.val) hh)
  have hlow : Finset.univ.image g ⊆ S.filter (· ≤ f j) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨S.orderEmbOfFin_mem rfl _, ?_⟩
    apply e.monotone
    change i.val ≤ b-k+j.val
    omega
  have hl := Finset.card_le_card hlow
  rw [Finset.card_image_of_injective _ hg] at hl
  simp only [Finset.card_univ,Fintype.card_fin] at hl
  dsimp only [b,k] at *
  omega

/-- A bottom quantile pool has exactly ceiling one tenth of the axis,
and every anchor retains at least nine tenths above it. -/
theorem exists_bottom_pool (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ T : Finset ℤ, T ⊆ S ∧ T.card = (S.card+9)/10 ∧ T.Nonempty ∧
      ∀ t ∈ T, 9*S.card ≤ 10*(S.filter (t ≤ ·)).card := by
  let b := S.card
  let k := (b+9)/10
  have hb : 0 < b := Finset.card_pos.mpr hS
  have hk : 0 < k := by dsimp [k]; omega
  have hkb : k ≤ b := by dsimp [k]; omega
  let e := S.orderEmbOfFin rfl
  let f : Fin k → ℤ := fun i => e ⟨i.val, by omega⟩
  let T := Finset.univ.image f
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg (fun i : Fin b => i.val) (e.injective hij))
  have hc : T.card = k := by simp [T,Finset.card_image_of_injective _ hf]
  have hsub : T ⊆ S := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact S.orderEmbOfFin_mem rfl _
  refine ⟨T,hsub,hc,Finset.card_pos.mp (by omega),?_⟩
  intro t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  let g : Fin (b-k+1) → ℤ := fun i => e ⟨k-1+i.val,by omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    have hv := congrArg (fun i : Fin b => i.val) (e.injective hij)
    apply Fin.ext
    dsimp only [g] at hv
    omega
  have hhigh : Finset.univ.image g ⊆ S.filter (f j ≤ ·) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨S.orderEmbOfFin_mem rfl _, ?_⟩
    apply e.monotone
    change j.val ≤ k-1+i.val
    omega
  have hl := Finset.card_le_card hhigh
  rw [Finset.card_image_of_injective _ hg] at hl
  simp only [Finset.card_univ,Fintype.card_fin] at hl
  dsimp only [b,k] at *
  omega

/-- Actual missing-edge fibers and the two exact quantile pools supply anchors
with all six corrected costs totaling at most 42 times the missing volume. -/
theorem exists_good_anchor (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty) :
    ∃ x0 ∈ X, ∃ y0 ∈ Y, ∃ z0 ∈ Z,
      9*Y.card ≤ 10*(Y.filter (· ≤ y0)).card ∧
      9*Z.card ≤ 10*(Z.filter (z0 ≤ ·)).card ∧
      anchorCost X Y Z A x0 y0 z0 ≤ 42*((X ×ˢ (Y ×ˢ Z)) \ A).card := by
  let P := A.image (fun t => (t.1,t.2.1))
  let Q := A.image (fun t => (t.1,t.2.2))
  let R := A.image (fun t => (t.2.1,t.2.2))
  let r := ((X ×ˢ (Y ×ˢ Z)) \ A).card
  obtain ⟨T,hTY,hTc,hTne,hretY⟩ := exists_top_pool Y hY
  obtain ⟨U,hUZ,hUc,hUne,hretZ⟩ := exists_bottom_pool Z hZ
  have hTsize : Y.card ≤ 10*T.card := by omega
  have hUsize : Z.card ≤ 10*U.card := by omega
  have hfxy : Z.card*(∑ x ∈ X, (Y.filter (fun y => (x,y) ∉ P)).card) ≤ r := by
    rw [sum_missing_degree]
    exact missing_xy_fibers X Y Z A
  have hgxy : Z.card*(∑ y ∈ Y, (X.filter (fun x => (x,y) ∉ P)).card) ≤ r := by
    rw [sum_missing_degree_right]
    exact missing_xy_fibers X Y Z A
  have hfxz : Y.card*(∑ x ∈ X, (Z.filter (fun z => (x,z) ∉ Q)).card) ≤ r := by
    rw [sum_missing_degree]
    exact missing_xz_fibers X Y Z A
  have hgxz : Y.card*(∑ z ∈ Z, (X.filter (fun x => (x,z) ∉ Q)).card) ≤ r := by
    rw [sum_missing_degree_right]
    exact missing_xz_fibers X Y Z A
  have hfyz : X.card*(∑ y ∈ Y, (Z.filter (fun z => (y,z) ∉ R)).card) ≤ r := by
    rw [sum_missing_degree]
    exact missing_yz_fibers X Y Z A
  have hgyz : X.card*(∑ z ∈ Z, (Y.filter (fun y => (y,z) ∉ R)).card) ≤ r := by
    rw [sum_missing_degree_right]
    exact missing_yz_fibers X Y Z A
  obtain ⟨x0,hx,hcostX⟩ := choose_two_costs X X (Finset.Subset.refl _) hX
    1 Z.card Y.card r (by omega) _ _ hfxy hfxz
  obtain ⟨y0,hy,hcostY⟩ := choose_two_costs Y T hTY hTne
    10 X.card Z.card r hTsize _ _ hfyz hgxy
  obtain ⟨z0,hz,hcostZ⟩ := choose_two_costs Z U hUZ hUne
    10 Y.card X.card r hUsize _ _ hgxz hgyz
  refine ⟨x0,hx,y0,hTY hy,z0,hUZ hz,hretY y0 hy,hretZ z0 hz,?_⟩
  have htotal := Nat.add_le_add (Nat.add_le_add hcostX hcostY) hcostZ
  dsimp only [P,Q,R] at htotal
  change anchorCost X Y Z A x0 y0 z0 ≤ 42*r
  unfold anchorCost
  nlinarith only [htotal]

/-- Three pairwise overlap bounds imply the one-tenth-volume bound at volume 730. -/
theorem ten_mul_le_volume (a b c o : ℕ) (hn : 730 ≤ a*b*c)
    (hab : o ≤ a*b) (hac : o ≤ a*c) (hbc : o ≤ b*c) : 10*o ≤ a*b*c := by
  by_cases ha : 10 ≤ a
  · calc
      10*o ≤ a*o := Nat.mul_le_mul_right o ha
      _ ≤ a*(b*c) := Nat.mul_le_mul_left a hbc
      _ = _ := by ring
  by_cases hb : 10 ≤ b
  · calc
      10*o ≤ b*o := Nat.mul_le_mul_right o hb
      _ ≤ b*(a*c) := Nat.mul_le_mul_left b hac
      _ = _ := by ring
  by_cases hc : 10 ≤ c
  · calc
      10*o ≤ c*o := Nat.mul_le_mul_right o hc
      _ ≤ c*(a*b) := Nat.mul_le_mul_left c hab
      _ = _ := by ring
  have ha9 : a ≤ 9 := by omega
  have hb9 : b ≤ 9 := by omega
  have hc9 : c ≤ 9 := by omega
  have hn9 := Nat.mul_le_mul (Nat.mul_le_mul ha9 hb9) hc9
  omega

/-- Every subset of a finite integer box of volume at least 730 satisfies the
q=10 mixed-sum counting inequality, with no small-hole assumption. -/
theorem product_bridge (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (_hA : A ⊆ X ×ˢ (Y ×ˢ Z))
    (hn : 730 ≤ (X ×ˢ (Y ×ˢ Z)).card) : 76*(X ×ˢ (Y ×ˢ Z)).card ≤
      50*(NoncommutingFiber.mixedSum A).card + 2100*((X ×ˢ (Y ×ˢ Z)) \ A).card := by
  have hnvol : 730 ≤ X.card*Y.card*Z.card := by
    simpa only [Finset.card_product, ← Nat.mul_assoc] using hn
  have hvpos : 0 < X.card*Y.card*Z.card := by omega
  have hx : 0 < X.card := by
    by_contra hh
    have he : X.card = 0 := by omega
    simp [he] at hvpos
  have hy : 0 < Y.card := by
    by_contra hh
    have he : Y.card = 0 := by omega
    simp [he] at hvpos
  have hz : 0 < Z.card := by
    by_contra hh
    have he : Z.card = 0 := by omega
    simp [he] at hvpos
  obtain ⟨x0,hx0,y0,hy0,z0,hz0,hretY,hretZ,hcost⟩ := exists_good_anchor X Y Z A
    (Finset.card_pos.mp hx) (Finset.card_pos.mp hy) (Finset.card_pos.mp hz)
  let Y' := Y.filter (· ≤ y0)
  let Z' := Z.filter (z0 ≤ ·)
  let C1 := (X ×ˢ (Y' ×ˢ Z')).image (block1 x0 y0 z0)
  let C2 := (X ×ˢ (Y ×ˢ Z')).image (block2 x0 y0 z0)
  let n := X.card*Y.card*Z.card
  let p := X.card*Y'.card*Z'.card
  let o := (C1 ∩ C2).card
  let w := anchorCost X Y Z A x0 y0 z0
  let r := ((X ×ˢ (Y ×ˢ Z)) \ A).card
  let m := (NoncommutingFiber.mixedSum A).card
  have hov := overlap_card_bounds X Y Z x0 y0 z0
  have ho : 10*o ≤ n := ten_mul_le_volume _ _ _ _ hnvol hov.1 hov.2.1 hov.2.2
  have hw : w ≤ 42*r := hcost
  have hprod : 81*n ≤ 100*p := by
    have hh := Nat.mul_le_mul_left X.card (Nat.mul_le_mul hretY hretZ)
    dsimp only [n,p,Y',Z']
    nlinarith only [hh]
  have hb := two_blocks_le_mixedSum_add_cost X Y Z A x0 y0 z0
  have hsecond : p ≤ X.card*Y.card*Z'.card := by
    dsimp only [p]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Finset.card_filter_le Y _))
  have hblocks : 2*p ≤ m+o+w := by
    change p + X.card*Y.card*Z'.card ≤ m+o+w at hb
    omega
  have hfinal : 76*n ≤ 50*m+2100*r := by omega
  simpa only [n,m,r,Finset.card_product,←Nat.mul_assoc] using hfinal


/-- Every integer triple set of size at least 1001 has mixed sum larger than
 its size by the unconditional rational factor 1000001/1000000. -/
theorem global_gap (A : Finset (ℤ × ℤ × ℤ)) (hN : 1001 ≤ A.card) :
    1000001*A.card ≤ 1000000*(NoncommutingFiber.mixedSum A).card := by
  by_contra hgap
  have hsmall : 1000000*(NoncommutingFiber.mixedSum A).card < 1000001*A.card :=
    Nat.lt_of_not_ge hgap
  have hNr : (1001:ℝ) ≤ A.card := by exact_mod_cast hN
  have hMr : (1000000:ℝ)*(NoncommutingFiber.mixedSum A).card <
      1000001*(A.card : ℝ) := by exact_mod_cast hsmall
  have hM : ((NoncommutingFiber.mixedSum A).card : ℝ) ≤
      (1000001/1000000:ℝ)*A.card := by linarith
  have hMsq := mul_self_le_mul_self (Nat.cast_nonneg (NoncommutingFiber.mixedSum A).card :
      (0:ℝ) ≤ (NoncommutingFiber.mixedSum A).card) hM
  have hP : (ElementaryLoomisWhitneyStability.projectionProduct A : ℝ) ≤
      ((NoncommutingFiber.mixedSum A).card : ℝ)^2 := by
    exact_mod_cast NoncommutingFiber.pair_projections_le_mixedSum_sq A
  have hprod : (ElementaryLoomisWhitneyStability.projectionProduct A : ℝ) ≤
      (1+(1/490000:ℝ))*(A.card : ℝ)^2 := by
    nlinarith only [hP,hMsq,sq_nonneg (A.card : ℝ)]
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨X,Y,Z,hbox⟩ := ElementaryLoomisWhitneySmallError.near_box A hA
    (1/490000) (by norm_num) (by norm_num) hprod
  have hsqrt : Real.sqrt (1/490000:ℝ) = 1/700 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hsqrt] at hbox
  let B := X ×ˢ (Y ×ˢ Z)
  let A0 := A ∩ B
  let E := (A \ B) ∪ (B \ A)
  have hE : (E.card : ℝ) ≤ (2/175:ℝ)*A.card := by
    dsimp only [E,B]
    linarith only [hbox]
  have hnlow : (A.card : ℝ) ≤ B.card + E.card := by
    have hc := ElementaryLoomisWhitneyStability.card_le_add_symm A B
    have hcomm : ((B \ A) ∪ (A \ B)) = E := Finset.union_comm _ _
    rw [hcomm] at hc
    exact_mod_cast hc
  have hrE : ((B \ A).card : ℝ) ≤ E.card := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_right : B \ A ⊆ E)
  have hnreal : (730:ℝ) ≤ B.card := by linarith
  have hmissing : B \ A0 = B \ A := by
    ext t
    simp only [A0, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hbridge := product_bridge X Y Z A0
    Finset.inter_subset_right (by exact_mod_cast hnreal)
  have hmono : (NoncommutingFiber.mixedSum A0).card ≤ (NoncommutingFiber.mixedSum A).card :=
    Finset.card_le_card (NoncommutingGoodAnchorGap.mixedSum_mono Finset.inter_subset_left)
  have hbr : (76:ℝ)*B.card ≤ 50*(NoncommutingFiber.mixedSum A0).card +
      2100*((B \ A).card : ℝ) := by
    have hb : 76*B.card ≤ 50*(NoncommutingFiber.mixedSum A0).card +
        2100*(B \ A0).card := hbridge
    rw [hmissing] at hb
    exact_mod_cast hb
  have hmonor : ((NoncommutingFiber.mixedSum A0).card : ℝ) ≤
      (NoncommutingFiber.mixedSum A).card := by exact_mod_cast hmono
  linarith

example : let B := (Finset.Icc (0 : ℤ) 9) ×ˢ
      ((Finset.Icc (0 : ℤ) 9) ×ˢ (Finset.Icc (0 : ℤ) 9))
    B ⊆ B ∧ 730 ≤ B.card := by
  norm_num
  decide

example : 1001 ≤ ((Finset.Icc (0 : ℤ) 1000) ×ˢ (({0} : Finset ℤ) ×ˢ {0})).card := by
  norm_num

example : ({0} : Finset ℤ).Nonempty ∧ ({1} : Finset ℤ).Nonempty ∧
    ({2} : Finset ℤ).Nonempty := by simp

example : 730 ≤ 10*10*10 ∧ 100 ≤ 10*10 ∧ 100 ≤ 10*10 ∧ 100 ≤ 10*10 := by
  norm_num

example : let S := Finset.Icc (0 : ℤ) 9
    let B := S ×ˢ (S ×ˢ S)
    let H := ({0} : Finset ℤ) ×ˢ (({0} : Finset ℤ) ×ˢ S)
    let A := B \ H
    B.card = 1000 ∧ (B \ A).card = 10 ∧
      ¬1000*(B \ A).card ≤ B.card ∧
      1100 ≤ (NoncommutingFiber.mixedSum A).card := by
  dsimp only
  let S := Finset.Icc (0 : ℤ) 9
  let B := S ×ˢ (S ×ˢ S)
  let H := ({0} : Finset ℤ) ×ˢ (({0} : Finset ℤ) ×ˢ S)
  have hsub : H ⊆ B := by
    intro t ht
    simp only [H, B, Finset.mem_product, Finset.mem_singleton] at ht ⊢
    rcases ht with ⟨hx,hy,hz⟩
    exact ⟨by simp [hx,S],by simp [hy,S],hz⟩
  have hn : B.card = 1000 := by
    norm_num [B,S]
    decide
  have hr : (B \ (B \ H)).card = 10 := by
    have he : B \ (B \ H) = H := by
      ext t
      simp only [Finset.mem_sdiff]
      constructor
      · intro ht
        by_contra hn
        exact ht.2 ⟨ht.1,hn⟩
      · intro ht
        exact ⟨hsub ht, fun hn => hn.2 ht⟩
    rw [he]
    norm_num [H,S]
    rfl
  have hb := product_bridge S S S (B \ H) Finset.sdiff_subset (by change 730 ≤ B.card; omega)
  change 76*B.card ≤ 50*(NoncommutingFiber.mixedSum (B \ H)).card +
    2100*(B \ (B \ H)).card at hb
  change B.card = 1000 ∧ (B \ (B \ H)).card = 10 ∧
    ¬1000*(B \ (B \ H)).card ≤ B.card ∧
    1100 ≤ (NoncommutingFiber.mixedSum (B \ H)).card
  omega

end NoncommutingMicroGap
