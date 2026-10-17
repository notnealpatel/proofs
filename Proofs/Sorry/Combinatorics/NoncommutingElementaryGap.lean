import Combinatorics.ElementaryLoomisWhitneyStability
import Sorry.Combinatorics.NoncommutingGoodAnchorGap

set_option autoImplicit false

namespace NoncommutingElementaryGap

/-- Every integer triple set of size at least 1001 has mixed sum larger than
 its size by the unconditional rational factor 1000000001/1000000000. -/
theorem global_gap (A : Finset (ℤ × ℤ × ℤ)) (hN : 1001 ≤ A.card) :
    1000000001*A.card ≤ 1000000000*(NoncommutingFiber.mixedSum A).card := by
  by_contra hgap
  have hsmall : 1000000000*(NoncommutingFiber.mixedSum A).card < 1000000001*A.card :=
    Nat.lt_of_not_ge hgap
  have hNr : (1001:ℝ) ≤ A.card := by exact_mod_cast hN
  have hMr : (1000000000:ℝ)*(NoncommutingFiber.mixedSum A).card <
      1000000001*(A.card : ℝ) := by exact_mod_cast hsmall
  have hM : ((NoncommutingFiber.mixedSum A).card : ℝ) ≤
      (1000000001/1000000000:ℝ)*A.card := by linarith
  have hMsq := mul_self_le_mul_self (Nat.cast_nonneg (NoncommutingFiber.mixedSum A).card :
      (0:ℝ) ≤ (NoncommutingFiber.mixedSum A).card) hM
  have hP : (ElementaryLoomisWhitneyStability.projectionProduct A : ℝ) ≤
      ((NoncommutingFiber.mixedSum A).card : ℝ)^2 := by
    exact_mod_cast NoncommutingFiber.pair_projections_le_mixedSum_sq A
  have hprod : (ElementaryLoomisWhitneyStability.projectionProduct A : ℝ) ≤
      (1+(1/400000000:ℝ))*(A.card : ℝ)^2 := by
    nlinarith only [hP,hMsq,sq_nonneg (A.card : ℝ)]
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨X,Y,Z,hbox⟩ := ElementaryLoomisWhitneyStability.near_box A hA
    (1/400000000) (by norm_num) (by norm_num) hprod
  have hsqrt : Real.sqrt (1/400000000:ℝ) = 1/20000 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hsqrt] at hbox
  let B := X ×ˢ (Y ×ˢ Z)
  let A0 := A ∩ B
  let E := (A \ B) ∪ (B \ A)
  have hE : (E.card : ℝ) ≤ (3/5000:ℝ)*A.card := by
    dsimp only [E,B]
    linarith only [hbox]
  have hnlow : (A.card : ℝ) ≤ B.card + E.card := by
    have hc := ElementaryLoomisWhitneyStability.card_le_add_symm A B
    have hcomm : ((B \ A) ∪ (A \ B)) = E := Finset.union_comm _ _
    rw [hcomm] at hc
    exact_mod_cast hc
  have hrE : ((B \ A).card : ℝ) ≤ E.card := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_right : B \ A ⊆ E)
  have hnreal : (1000:ℝ) ≤ B.card := by linarith
  have hrreal : (1000:ℝ)*((B \ A).card : ℝ) ≤ B.card := by linarith
  have hmissing : B \ A0 = B \ A := by
    ext t
    simp only [A0, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hbridge := NoncommutingGoodAnchorGap.dense_product_bridge X Y Z A0
    Finset.inter_subset_right (by exact_mod_cast hnreal)
    (by change 1000*(B \ A0).card ≤ B.card; rw [hmissing]; exact_mod_cast hrreal)
  have hmono : (NoncommutingFiber.mixedSum A0).card ≤ (NoncommutingFiber.mixedSum A).card :=
    Finset.card_le_card (NoncommutingGoodAnchorGap.mixedSum_mono Finset.inter_subset_left)
  have hbr : (3:ℝ)*B.card ≤ 2*(NoncommutingFiber.mixedSum A0).card := by exact_mod_cast hbridge
  have hmonor : ((NoncommutingFiber.mixedSum A0).card : ℝ) ≤
      (NoncommutingFiber.mixedSum A).card := by exact_mod_cast hmono
  linarith

example : 1001 ≤ ((Finset.range 1001).image (fun n : ℕ => ((n:ℤ),(0:ℤ),(0:ℤ)))).card := by
  have hi : Function.Injective (fun n : ℕ => ((n:ℤ), (0:ℤ), (0:ℤ))) := by
    intro a b heq
    have hc := congrArg (fun t : ℤ × ℤ × ℤ => t.1) heq
    change (a:ℤ) = (b:ℤ) at hc
    exact_mod_cast hc
  rw [Finset.card_image_of_injective _ hi, Finset.card_range]

end NoncommutingElementaryGap
