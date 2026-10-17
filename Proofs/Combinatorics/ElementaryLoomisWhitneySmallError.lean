import Combinatorics.ElementaryLoomisWhitneyStability

set_option autoImplicit false

namespace ElementaryLoomisWhitneySmallError

open ElementaryLoomisWhitneyStability

/-- The three-step estimate uses square-root five-fourths at most nine-eighths. -/
theorem three_step_error_le (x y z δ P : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (hx2 : x^2 ≤ δ*P) (hy2 : y^2 ≤ (5/4)*δ*P) (hz2 : z^2 ≤ (25/16)*δ*P) :
    x+y+z ≤ (27/8 : ℝ)*Real.sqrt δ*Real.sqrt P := by
  let b := Real.sqrt δ * Real.sqrt P
  have hb : 0 ≤ b := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb2 : b^2 = δ*P := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt hδ, Real.sq_sqrt hP]
  have hxb : x ≤ b := by nlinarith only [hx, hb, hx2, hb2]
  have hyb : y ≤ (9/8:ℝ)*b := by
    nlinarith only [hy, hb, hy2, hb2, sq_nonneg (y-(9/8:ℝ)*b)]
  have hzb : z ≤ (5/4)*b := by nlinarith only [hz, hb, hz2, hb2]
  change x+y+z ≤ (27/8:ℝ)*Real.sqrt δ*Real.sqrt P
  dsimp only [b] at hxb hyb hzb
  linarith

/-- Three literal edge replacements telescope to a supported-triangle error bound;
 rectangle sizes and added ghost edges are fully charged. -/
theorem triangle_replacement_bound {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (F R : Finset (I × J)) (G S : Finset (I × K)) (H T : Finset (J × K))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4)
    (hF : (((F \ R) ∪ (R \ F)).card : ℝ) ≤ δ*F.card)
    (hG : (((G \ S) ∪ (S \ G)).card : ℝ) ≤ δ*G.card)
    (hH : (((H \ T) ∪ (T \ H)).card : ℝ) ≤ δ*H.card) :
    (((triangles F G H \ triangles R S T) ∪
      (triangles R S T \ triangles F G H)).card : ℝ) ≤
      (27/8:ℝ)*Real.sqrt δ*Real.sqrt ((F.card : ℝ)*G.card*H.card) := by
  let A := triangles F G H
  let B := triangles R G H
  let C := triangles R S H
  let D := triangles R S T
  let x : ℝ := ((A \ B) ∪ (B \ A)).card
  let y : ℝ := ((B \ C) ∪ (C \ B)).card
  let z : ℝ := ((C \ D) ∪ (D \ C)).card
  have hR : (R.card : ℝ) ≤ (5/4)*F.card := by
    have hc : (R.card : ℝ) ≤ F.card + ((F \ R) ∪ (R \ F)).card := by
      exact_mod_cast card_le_add_symm R F
    have hmul := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg F.card : (0:ℝ) ≤ F.card)
    linarith
  have hS : (S.card : ℝ) ≤ (5/4)*G.card := by
    have hc : (S.card : ℝ) ≤ G.card + ((G \ S) ∪ (S \ G)).card := by
      exact_mod_cast card_le_add_symm S G
    have hmul := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg G.card : (0:ℝ) ≤ G.card)
    linarith
  have hx : x^2 ≤ δ*((F.card : ℝ)*G.card*H.card) := by
    have hc : x^2 ≤ (((F \ R) ∪ (R \ F)).card : ℝ)*G.card*H.card := by
      dsimp only [x,A,B]
      exact_mod_cast triangles_change_xy F R G H
    calc
      _ ≤ _ := hc
      _ ≤ (δ*F.card)*G.card*H.card := by gcongr
      _ = _ := by ring
  have hy : y^2 ≤ (5/4)*δ*((F.card : ℝ)*G.card*H.card) := by
    have hc : y^2 ≤ (R.card : ℝ)*((G \ S) ∪ (S \ G)).card*H.card := by
      dsimp only [y,B,C]
      exact_mod_cast triangles_change_xz R G S H
    calc
      _ ≤ _ := hc
      _ ≤ ((5/4)*F.card)*(δ*G.card)*H.card := by gcongr
      _ = _ := by ring
  have hz : z^2 ≤ (25/16)*δ*((F.card : ℝ)*G.card*H.card) := by
    have hc : z^2 ≤ (R.card : ℝ)*S.card*((H \ T) ∪ (T \ H)).card := by
      dsimp only [z,C,D]
      exact_mod_cast triangles_change_yz R S H T
    calc
      _ ≤ _ := hc
      _ ≤ ((5/4)*F.card)*((5/4)*G.card)*(δ*H.card) := by gcongr
      _ = _ := by ring
  have htel : (((A \ D) ∪ (D \ A)).card : ℝ) ≤ x+y+z := by
    have h1 := card_symm_triangle A B D
    have h2 := card_symm_triangle B C D
    dsimp only [x,y,z]
    exact_mod_cast (show ((A \ D) ∪ (D \ A)).card ≤
      ((A \ B) ∪ (B \ A)).card + ((B \ C) ∪ (C \ B)).card +
        ((C \ D) ∪ (D \ C)).card by omega)
  exact htel.trans (three_step_error_le x y z δ _ (by dsimp [x]; positivity)
    (by dsimp [y]; positivity) (by dsimp [z]; positivity) hδ (by positivity) hx hy hz)

/-- Exact small-epsilon arithmetic, retaining the constant 907/128 before the endpoint 8. -/
theorem small_epsilon_constant (ε N P : ℝ) (he : 0 ≤ ε) (he4 : ε ≤ 1/16)
    (hN : 0 ≤ N) (hP : 0 ≤ P) (hprod : P ≤ (1+ε)*N^2) :
    (ε/2)*N + (27/8:ℝ)*Real.sqrt (4*ε)*Real.sqrt P ≤
      (907/128:ℝ)*Real.sqrt ε*N := by
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt ε)^2 = ε := Real.sq_sqrt he
  have hs_half : Real.sqrt ε ≤ 1/4 := by nlinarith only [hs, hs2, he4]
  have he_s : ε/2 ≤ Real.sqrt ε/8 := by nlinarith only [hs, hs2, hs_half]
  have hroot : Real.sqrt P ≤ (33/32:ℝ)*N := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hmul := mul_le_mul_of_nonneg_right he4 (sq_nonneg N)
      nlinarith only [hprod, hmul, sq_nonneg N]
  have hfour : Real.sqrt (4*ε) = 2*Real.sqrt ε := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  rw [hfour]
  have hfirst := mul_le_mul_of_nonneg_right he_s hN
  have hsecond := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (27/8:ℝ)*(2*Real.sqrt ε) by positivity)
  nlinarith only [hfirst, hsecond]

/-- Near equality in finite three-coordinate Loomis--Whitney gives a Cartesian box
 with literal symmetric-difference error at most eight square-root epsilon times volume. -/
theorem near_box_finite {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (A : Finset (I × J × K)) (hA : A.Nonempty) (ε : ℝ)
    (he : 0 < ε) (he1 : ε ≤ 1/16)
    (hprod : (projectionProduct A : ℝ) ≤ (1+ε)*(A.card : ℝ)^2) :
    ∃ X : Finset I, ∃ Y : Finset J, ∃ Z : Finset K,
      (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
        8*Real.sqrt ε*A.card := by
  have hN : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  let F := A.image (fun t => (t.1,t.2.1))
  let G := A.image (fun t => (t.1,t.2.2))
  let H := A.image (fun t => (t.2.1,t.2.2))
  let S := triangles F G H
  have hAS : A ⊆ S := by
    intro t ht
    exact (mem_triangles F G H t).mpr ⟨Finset.mem_image_of_mem _ ht,
      Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
  have hNS : (A.card : ℝ)^2 ≤ (S.card : ℝ)^2 := by
    exact_mod_cast Nat.pow_le_pow_left (Finset.card_le_card hAS) 2
  have hprod' : (F.card : ℝ)*G.card*H.card ≤ (1+ε)*(A.card : ℝ)^2 := by
    simpa only [projectionProduct, Nat.cast_mul] using hprod
  obtain ⟨U,U',V,V',W,W',hF,hG,hH⟩ := exists_three_rectangles F G H
    (hA.image _) (hA.image _) (hA.image _) A.card ε he.le hprod' hNS
  let B := (U ∩ U') ×ˢ ((V ∩ V') ×ˢ (W ∩ W'))
  have hSB : (((S \ B) ∪ (B \ S)).card : ℝ) ≤
      (27/8:ℝ)*Real.sqrt (4*ε)*Real.sqrt (projectionProduct A : ℝ) := by
    have hr := triangle_replacement_bound F (U ×ˢ V) G (U' ×ˢ W) H
      (V' ×ˢ W') (4*ε) (by positivity) (by linarith) hF hG hH
    rw [triangles_rectangles] at hr
    simpa only [S,B,projectionProduct,Nat.cast_mul] using hr
  have hSsq : (S.card : ℝ)^2 ≤ (1+ε)*(A.card : ℝ)^2 := by
    have hc : (S.card : ℝ)^2 ≤ (F.card : ℝ)*G.card*H.card := by
      exact_mod_cast card_triangles_sq_le F G H
    exact hc.trans hprod'
  have hcomplete := completion_error_le A S hAS ε he.le hSsq
  have hSA : ((A \ S) ∪ (S \ A)) = S \ A := by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hAS, Finset.empty_union]
  have htel : (((A \ B) ∪ (B \ A)).card : ℝ) ≤
      ((S \ A).card : ℝ) + ((S \ B) ∪ (B \ S)).card := by
    have ht := card_symm_triangle A S B
    rw [hSA] at ht
    exact_mod_cast ht
  have hsmall := small_epsilon_constant ε A.card (projectionProduct A) he.le he1 hN
    (Nat.cast_nonneg _) hprod
  refine ⟨U ∩ U',V ∩ V',W ∩ W',?_⟩
  change (((A \ B) ∪ (B \ A)).card : ℝ) ≤ _
  have hrootN : 0 ≤ Real.sqrt ε * (A.card : ℝ) := mul_nonneg (Real.sqrt_nonneg _) hN
  linarith

/-- For every nonempty finite integer triple set, near equality in ordinary
 Loomis--Whitney gives a finite box within eight square-root epsilon times its size. -/
theorem near_box (A : Finset (ℤ × ℤ × ℤ)) (hA : A.Nonempty) (ε : ℝ)
    (he : 0 < ε) (he1 : ε ≤ 1/16)
    (hprod : (projectionProduct A : ℝ) ≤ (1+ε)*(A.card : ℝ)^2) :
    ∃ X Y Z : Finset ℤ,
      (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
        8*Real.sqrt ε*A.card := by
  let I := ↥(A.image (fun t => t.1))
  let J := ↥(A.image (fun t => t.2.1))
  let K := ↥(A.image (fun t => t.2.2))
  let f : I → ℤ := Subtype.val
  let g : J → ℤ := Subtype.val
  let h : K → ℤ := Subtype.val
  let q := Prod.map f (Prod.map g h)
  have hf : Function.Injective f := Subtype.val_injective
  have hg : Function.Injective g := Subtype.val_injective
  have hh : Function.Injective h := Subtype.val_injective
  have hq : Function.Injective q := hf.prodMap (hg.prodMap hh)
  let A' : Finset (I × J × K) := Finset.univ.filter (fun t => q t ∈ A)
  have him : A'.image q = A := by
    ext t
    constructor
    · intro ht
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hs).2
    · intro ht
      let s : I × J × K := (⟨t.1,Finset.mem_image_of_mem _ ht⟩,
        ⟨t.2.1,Finset.mem_image_of_mem _ ht⟩,⟨t.2.2,Finset.mem_image_of_mem _ ht⟩)
      exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,rfl⟩
  have hc : A'.card = A.card := by
    rw [← him, Finset.card_image_of_injective _ hq]
  have hp : projectionProduct A' = projectionProduct A := by
    exact (projectionProduct_image A' f g h hf hg hh).symm.trans
      (congrArg (fun B : Finset (ℤ × ℤ × ℤ) => projectionProduct B) him)
  have hA' : A'.Nonempty := by
    have hi : (A'.image q).Nonempty := him.symm ▸ hA
    exact Finset.image_nonempty.mp hi
  obtain ⟨X,Y,Z,hbox⟩ := near_box_finite A' hA' ε he he1 (by simpa only [hc,hp] using hprod)
  refine ⟨X.image f,Y.image g,Z.image h,?_⟩
  have hb : (X ×ˢ (Y ×ˢ Z)).image q = X.image f ×ˢ (Y.image g ×ˢ Z.image h) := by
    dsimp only [q]
    rw [Finset.prodMap_image_product, Finset.prodMap_image_product]
  have herr := card_symm_image A' (X ×ˢ (Y ×ˢ Z)) q hq
  rw [him,hb] at herr
  rw [herr,← hc]
  exact hbox

example : ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)).Nonempty ∧
    (0:ℝ) < 1/16 ∧ (1/16:ℝ) ≤ 1/16 ∧
    (projectionProduct ({(0,0,0)} : Finset (ℤ × ℤ × ℤ)) : ℝ) ≤
      (1+1/16:ℝ)*(({(0,0,0)} : Finset (ℤ × ℤ × ℤ)).card : ℝ)^2 := by
  norm_num [projectionProduct]

example : (0:ℝ) ≤ 1 ∧ (1:ℝ)^2 ≤ 1*1 ∧
    (1:ℝ)^2 ≤ (5/4)*1*1 ∧ (1:ℝ)^2 ≤ (25/16)*1*1 := by norm_num

example : (0:ℝ) ≤ 1/16 ∧ (1/16:ℝ) ≤ 1/16 ∧ (0:ℝ) ≤ 1 ∧
    (1:ℝ) ≤ (1+1/16)*1^2 := by norm_num

example : let F : Finset (Fin 1 × Fin 1) := {(0,0)}
    (0:ℝ) ≤ 1/4 ∧ (1/4:ℝ) ≤ 1/4 ∧
      (((F \ F) ∪ (F \ F)).card : ℝ) ≤ (1/4)*F.card := by
  norm_num

end ElementaryLoomisWhitneySmallError
