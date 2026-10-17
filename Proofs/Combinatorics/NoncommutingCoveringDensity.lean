import Combinatorics.NoncommutingFiber

set_option autoImplicit false

open scoped Pointwise

namespace NoncommutingCoveringDensity

open NoncommutingFiber

private theorem cover_density (J1 J2 J3 : Finset ℤ)
    (H0 H1 H2 : Finset (ℤ × ℤ)) (s : ℤ × ℤ × ℤ)
    (h1 : J1.Nonempty) (h2 : J2.Nonempty) (h3 : J3.Nonempty)
    (hc : ∀ a ∈ J1, ∀ b ∈ J2, ∀ d ∈ J3,
      (a,b) ∈ H0 ∨ (s.1-a,d) ∈ H1 ∨ (s.2.1-b,s.2.2-d) ∈ H2) :
    let R0 := J1 ×ˢ J2
    let R1 := (J1.image (fun a => s.1-a)) ×ˢ J3
    let R2 := (J2.image (fun b => s.2.1-b)) ×ˢ (J3.image (fun d => s.2.2-d))
    R0.card ≤ 3 * (H0 ∩ R0).card ∨
      R1.card ≤ 3 * (H1 ∩ R1).card ∨ R2.card ≤ 3 * (H2 ∩ R2).card := by
  dsimp only
  let T := J1 ×ˢ (J2 ×ˢ J3)
  let E0 := T.filter (fun t => (t.1,t.2.1) ∈ H0)
  let E1 := T.filter (fun t => (s.1-t.1,t.2.2) ∈ H1)
  let E2 := T.filter (fun t => (s.2.1-t.2.1,s.2.2-t.2.2) ∈ H2)
  have hcover : T ⊆ E0 ∪ E1 ∪ E2 := by
    intro t ht
    obtain ⟨ha,hb,hd⟩ := by simpa only [T, Finset.mem_product] using ht
    rcases hc t.1 ha t.2.1 hb t.2.2 hd with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,h⟩)
  have c0 : E0.card ≤ (H0 ∩ (J1 ×ˢ J2)).card * J3.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun t => ((t.1,t.2.1),t.2.2))
    · intro t ht
      obtain ⟨ht,hh⟩ := Finset.mem_filter.mp ht
      obtain ⟨ha,hb,hd⟩ := by simpa only [T, Finset.mem_product] using ht
      exact Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hh,
        Finset.mem_product.mpr ⟨ha,hb⟩⟩,hd⟩
    · rintro ⟨a,b,d⟩ _ ⟨a',b',d'⟩ _ he
      simpa only [Prod.mk.injEq, and_assoc] using he
  have c1 : E1.card ≤
      (H1 ∩ ((J1.image (fun a => s.1-a)) ×ˢ J3)).card * J2.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun t => ((s.1-t.1,t.2.2),t.2.1))
    · intro t ht
      obtain ⟨ht,hh⟩ := Finset.mem_filter.mp ht
      obtain ⟨ha,hb,hd⟩ := by simpa only [T, Finset.mem_product] using ht
      exact Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hh,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ha,hd⟩⟩,hb⟩
    · rintro ⟨a,b,d⟩ _ ⟨a',b',d'⟩ _ he
      simp only [Prod.mk.injEq] at he ⊢
      omega
  have c2 : E2.card ≤
      (H2 ∩ ((J2.image (fun b => s.2.1-b)) ×ˢ
        (J3.image (fun d => s.2.2-d)))).card * J1.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun t => ((s.2.1-t.2.1,s.2.2-t.2.2),t.1))
    · intro t ht
      obtain ⟨ht,hh⟩ := Finset.mem_filter.mp ht
      obtain ⟨ha,hb,hd⟩ := by simpa only [T, Finset.mem_product] using ht
      exact Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hh,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,
          Finset.mem_image_of_mem _ hd⟩⟩,ha⟩
    · rintro ⟨a,b,d⟩ _ ⟨a',b',d'⟩ _ he
      simp only [Prod.mk.injEq] at he ⊢
      omega
  have count : J1.card * J2.card * J3.card ≤
      (H0 ∩ (J1 ×ˢ J2)).card * J3.card +
      (H1 ∩ ((J1.image (fun a => s.1-a)) ×ˢ J3)).card * J2.card +
      (H2 ∩ ((J2.image (fun b => s.2.1-b)) ×ˢ
        (J3.image (fun d => s.2.2-d)))).card * J1.card := by
    have hu := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hv := Finset.card_union_le E0 E1
    simp only [T, Finset.card_product] at hu
    nlinarith
  have ci (J : Finset ℤ) (v : ℤ) : (J.image (fun a => v-a)).card = J.card :=
    Finset.card_image_of_injective J (by intro a b h; dsimp only at h; omega)
  simp only [Finset.card_product, ci] at ⊢
  by_contra hn
  push Not at hn
  have n1 := Finset.card_pos.mpr h1
  have n2 := Finset.card_pos.mpr h2
  have n3 := Finset.card_pos.mpr h3
  have q0 := Nat.mul_lt_mul_of_pos_right hn.1 n3
  have q1 := Nat.mul_lt_mul_of_pos_right hn.2.1 n2
  have q2 := Nat.mul_lt_mul_of_pos_right hn.2.2 n1
  nlinarith

/-- A missing mixed-sum output of a finite integer box has a nonempty common
fiber and a signed projection rectangle with at least one-third holes.
The holes are the actual projection complements of `A`; no covering or
independence hypothesis is assumed. All density inequalities are division-free. -/
theorem missing_output_rectangle_density
    (I1 I2 I3 : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (_hA : A ⊆ I1 ×ˢ (I2 ×ˢ I3)) (s : ℤ × ℤ × ℤ)
    (hs : s ∈ mixedSum (I1 ×ˢ (I2 ×ˢ I3))) (hmissing : s ∉ mixedSum A) :
    let J1 := I2 ∩ I3.image (fun z => s.1-z)
    let J2 := I1.image Neg.neg ∩ I3.image (fun z => s.2.1-z)
    let J3 := I1.image Neg.neg ∩ I2.image (fun y => s.2.2+y)
    let H0 := (I2 ×ˢ I1.image Neg.neg) \ A.image (fun t => (t.2.1,-t.1))
    let H1 := (I3 ×ˢ I1.image Neg.neg) \ A.image (fun t => (t.2.2,-t.1))
    let H2 := (I3 ×ˢ I2.image Neg.neg) \ A.image (fun t => (t.2.2,-t.2.1))
    let R0 := J1 ×ˢ J2
    let R1 := (J1.image (fun a => s.1-a)) ×ˢ J3
    let R2 := (J2.image (fun b => s.2.1-b)) ×ˢ (J3.image (fun d => s.2.2-d))
    J1.Nonempty ∧ J2.Nonempty ∧ J3.Nonempty ∧
    R0.Nonempty ∧ R1.Nonempty ∧ R2.Nonempty ∧
    (R0.card ≤ 3 * (H0 ∩ R0).card ∨
      R1.card ≤ 3 * (H1 ∩ R1).card ∨ R2.card ≤ 3 * (H2 ∩ R2).card) := by
  dsimp only
  let J1 := I2 ∩ I3.image (fun z => s.1-z)
  let J2 := I1.image Neg.neg ∩ I3.image (fun z => s.2.1-z)
  let J3 := I1.image Neg.neg ∩ I2.image (fun y => s.2.2+y)
  have witnesses : ∃ x ∈ I1 ×ˢ (I2 ×ˢ I3), ∃ y ∈ I1 ×ˢ (I2 ×ˢ I3),
      ∃ z ∈ I1 ×ˢ (I2 ×ˢ I3), L0 x + L1 y + L2 z = s := by
    obtain ⟨u,hu,v,hv,he⟩ := Finset.mem_add.mp hs
    obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨x,hx,y,hy,z,hz,he⟩
  obtain ⟨x,hx,y,hy,z,hz,he⟩ := witnesses
  have coords : x.2.1 + y.2.2 = s.1 ∧ -x.1 + z.2.2 = s.2.1 ∧
      -y.1 - z.2.1 = s.2.2 := by
    simpa [L0,L1,L2, Prod.ext_iff, sub_eq_add_neg] using he
  simp only [Finset.mem_product] at hx hy hz
  have n1 : J1.Nonempty := by
    refine ⟨x.2.1, Finset.mem_inter.mpr ⟨hx.2.1, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨y.2.2,hy.2.2,by omega⟩
  have n2 : J2.Nonempty := by
    refine ⟨-x.1, Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ hx.1, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨z.2.2,hz.2.2,by omega⟩
  have n3 : J3.Nonempty := by
    refine ⟨-y.1, Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ hy.1, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨z.2.1,hz.2.1,by omega⟩
  refine ⟨n1,n2,n3, n1.product n2, (n1.image _).product n3,
    (n2.image _).product (n3.image _), ?_⟩
  apply cover_density J1 J2 J3 _ _ _ s n1 n2 n3
  intro a ha b hb d hd
  have ha' := Finset.mem_inter.mp ha
  have hb' := Finset.mem_inter.mp hb
  have hd' := Finset.mem_inter.mp hd
  have cI : s.1-a ∈ I3 := by
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp ha'.2
    have he' : s.1-a = c := by omega
    exact he' ▸ hc
  have eI : s.2.1-b ∈ I3 := by
    obtain ⟨e,he,hv⟩ := Finset.mem_image.mp hb'.2
    have hv' : s.2.1-b = e := by omega
    exact hv' ▸ he
  have fI : s.2.2-d ∈ I2.image Neg.neg := by
    obtain ⟨f,hf,hv⟩ := Finset.mem_image.mp hd'.2
    apply Finset.mem_image.mpr
    exact ⟨f,hf,by omega⟩
  by_contra hn
  have p0 : (a,b) ∈ A.image (fun t => (t.2.1,-t.1)) := by
    by_contra hp
    exact hn (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨ha'.1,hb'.1⟩,hp⟩))
  have p1 : (s.1-a,d) ∈ A.image (fun t => (t.2.2,-t.1)) := by
    by_contra hp
    exact hn (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨cI,hd'.1⟩,hp⟩)))
  have p2 : (s.2.1-b,s.2.2-d) ∈ A.image (fun t => (t.2.2,-t.2.1)) := by
    by_contra hp
    exact hn (Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨eI,fI⟩,hp⟩)))
  obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp p0
  obtain ⟨v,hv,hvv⟩ := Finset.mem_image.mp p1
  obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp p2
  apply hmissing
  apply Finset.mem_add.mpr
  refine ⟨L0 u + L1 v, Finset.mem_add.mpr
    ⟨L0 u,Finset.mem_image_of_mem _ hu,L1 v,Finset.mem_image_of_mem _ hv,rfl⟩,
    L2 w,Finset.mem_image_of_mem _ hw,?_⟩
  simp only [Prod.mk.injEq] at huv hvv hwv
  ext <;> simp [L0,L1,L2] <;> omega

/-- The affine images of the common fiber factors are exactly the
translated/reflected factors in the actual projection grids. -/
theorem rectangle_factor_identifications (I1 I2 I3 : Finset ℤ) (s : ℤ × ℤ × ℤ) :
    ((I2 ∩ I3.image (fun z => s.1-z)).image (fun a => s.1-a) =
      I3 ∩ I2.image (fun a => s.1-a)) ∧
    ((I1.image Neg.neg ∩ I3.image (fun z => s.2.1-z)).image
      (fun b => s.2.1-b) = I3 ∩ I1.image (fun x => s.2.1+x)) ∧
    ((I1.image Neg.neg ∩ I2.image (fun y => s.2.2+y)).image
      (fun d => s.2.2-d) = I2.image Neg.neg ∩ I1.image (fun x => s.2.2+x)) := by
  constructor
  · ext t
    simp only [Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨a,⟨ha,z,hz,hza⟩,hat⟩
      have hzt : z = t := by omega
      exact ⟨hzt ▸ hz, a,ha,hat⟩
    · rintro ⟨ht,a,ha,hat⟩
      exact ⟨a,⟨ha,t,ht,by omega⟩,hat⟩
  constructor
  · ext t
    simp only [Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨b,⟨⟨x,hx,hxb⟩,z,hz,hzb⟩,hbt⟩
      have hzt : z = t := by omega
      exact ⟨hzt ▸ hz,x,hx,by omega⟩
    · rintro ⟨ht,x,hx,hxt⟩
      exact ⟨-x,⟨⟨x,hx,rfl⟩,t,ht,by omega⟩,by omega⟩
  · ext t
    simp only [Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨d,⟨⟨x,hx,hxd⟩,y,hy,hyd⟩,hdt⟩
      exact ⟨⟨y,hy,by omega⟩,x,hx,by omega⟩
    · rintro ⟨⟨y,hy,hyt⟩,x,hx,hxt⟩
      exact ⟨-x,⟨⟨x,hx,rfl⟩,y,hy,by omega⟩,by omega⟩

example : (∅ : Finset (ℤ × ℤ × ℤ)) ⊆
    ({1} : Finset ℤ) ×ˢ (({2} : Finset ℤ) ×ˢ ({3} : Finset ℤ)) ∧
    (5,2,-3) ∈ mixedSum (({1} : Finset ℤ) ×ˢ
      (({2} : Finset ℤ) ×ˢ ({3} : Finset ℤ))) ∧
    (5,2,-3) ∉ mixedSum (∅ : Finset (ℤ × ℤ × ℤ)) := by decide

example : ({(1,2,3)} : Finset (ℤ × ℤ × ℤ)) ⊆
    ({1,4} : Finset ℤ) ×ˢ (({2} : Finset ℤ) ×ˢ ({3} : Finset ℤ)) ∧
    (5,-1,-6) ∈ mixedSum (({1,4} : Finset ℤ) ×ˢ
      (({2} : Finset ℤ) ×ˢ ({3} : Finset ℤ))) ∧
    (5,-1,-6) ∉ mixedSum {(1,2,3)} := by decide

example (I2 I3 : Finset ℤ) :
    mixedSum ((∅ : Finset ℤ) ×ˢ (I2 ×ˢ I3)) = ∅ := by
  simp [mixedSum]

example : let R := ({2} : Finset ℤ) ×ˢ ({-1} : Finset ℤ)
    let H := R \ (∅ : Finset (ℤ × ℤ))
    R.Nonempty ∧ R.card ≤ 3 * (H ∩ R).card := by decide

end NoncommutingCoveringDensity
