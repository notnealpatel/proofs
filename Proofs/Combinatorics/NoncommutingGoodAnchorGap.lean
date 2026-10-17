import Combinatorics.NoncommutingFiber
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace NoncommutingGoodAnchorGap

/-- The product of the three ordinary pair-projection cardinalities. -/
def projectionProduct (A : Finset (ℤ × ℤ × ℤ)) : ℕ :=
  (A.image (fun t => (t.1,t.2.1))).card *
    (A.image (fun t => (t.1,t.2.2))).card *
    (A.image (fun t => (t.2.1,t.2.2))).card

example : projectionProduct {(1,2,3)} = 1 := by decide
example : projectionProduct ∅ = 0 := by decide

/-- The general dimension-three EFKY source statement, not proved here.
The box factors are arbitrary finite integer sets, and epsilon is any positive real. -/
def EFKY456 : Prop := ∀ (A : Finset (ℤ × ℤ × ℤ)) (ε : ℝ),
  0 < ε → (1 - ε) * Real.sqrt (projectionProduct A : ℝ) ≤ (A.card : ℝ) →
  ∃ X Y Z : Finset ℤ,
    (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
      456 * ε * (A.card : ℝ)

example : EFKY456 ↔ (∀ (A : Finset (ℤ × ℤ × ℤ)) (ε : ℝ),
  0 < ε → (1 - ε) * Real.sqrt (projectionProduct A : ℝ) ≤ (A.card : ℝ) →
  ∃ X Y Z : Finset ℤ,
    (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
      456 * ε * (A.card : ℝ)) := Iff.rfl

/-- The stronger production projection bound implies the required square-root bound. -/
theorem sqrt_projectionProduct_le (A : Finset (ℤ × ℤ × ℤ)) :
    Real.sqrt (projectionProduct A : ℝ) ≤ (NoncommutingFiber.mixedSum A).card := by
  have h := NoncommutingFiber.pair_projections_le_mixedSum_sq A
  change projectionProduct A ≤ _ at h
  have hr : (projectionProduct A : ℝ) ≤
      ((NoncommutingFiber.mixedSum A).card : ℝ) ^ 2 := by exact_mod_cast h
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hr⟩

/-- Ordinary mixed sums are monotone because their witnesses are independent. -/
theorem mixedSum_mono {A C : Finset (ℤ × ℤ × ℤ)} (h : A ⊆ C) :
    NoncommutingFiber.mixedSum A ⊆ NoncommutingFiber.mixedSum C := by
  intro s hs
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hs
  obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_add.mp hu
  apply Finset.mem_add.mpr
  refine ⟨p + q, Finset.mem_add.mpr ⟨p, ?_, q, ?_, rfl⟩, v, ?_, rfl⟩
  · exact Finset.image_subset_image h hp
  · exact Finset.image_subset_image h hq
  · exact Finset.image_subset_image h hv

/-- Applying the exact source parameter at epsilon `1/1000001` supplies
an arbitrary finite box near a putative counterexample. -/
theorem near_box_of_counterexample (hEFKY : EFKY456)
    (A : Finset (ℤ × ℤ × ℤ))
    (hsmall : 1000000 * (NoncommutingFiber.mixedSum A).card < 1000001 * A.card) :
    ∃ X Y Z : Finset ℤ,
      (((A \ (X ×ˢ (Y ×ˢ Z))) ∪ ((X ×ˢ (Y ×ˢ Z)) \ A)).card : ℝ) ≤
        (456 / 1000001 : ℝ) * A.card := by
  have hs := sqrt_projectionProduct_le A
  have hn : (1000000 : ℝ) * (NoncommutingFiber.mixedSum A).card <
      1000001 * (A.card : ℝ) := by exact_mod_cast hsmall
  have hnear : (1 - (1 / 1000001 : ℝ)) *
      Real.sqrt (projectionProduct A : ℝ) ≤ (A.card : ℝ) := by linarith
  obtain ⟨X,Y,Z,hbox⟩ := hEFKY A (1 / 1000001) (by norm_num) hnear
  refine ⟨X,Y,Z, ?_⟩
  convert hbox using 1 <;> ring

/-- The first anchor block map, with parameters `(x,y,z)`. -/
def block1 (x0 y0 z0 : ℤ) (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.2.1 + z0, t.2.2 - x0, -t.1 - y0)

/-- The second anchor block map, with parameters `(x,y,z)`. -/
def block2 (x0 y0 z0 : ℤ) (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.2.2 + y0, z0 - t.1, -t.2.1 - x0)

example : block1 1 2 3 (4,5,6) = (8,5,-6) := rfl
example : block2 1 2 3 (4,5,6) = (8,-1,-6) := rfl

/-- All three parameters are recovered from a first-block output. -/
theorem block1_injective (x0 y0 z0 : ℤ) : Function.Injective (block1 x0 y0 z0) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ h
  simp only [block1, Prod.mk.injEq] at h ⊢
  omega

/-- All three parameters are recovered from a second-block output. -/
theorem block2_injective (x0 y0 z0 : ℤ) : Function.Injective (block2 x0 y0 z0) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ h
  simp only [block2, Prod.mk.injEq] at h ⊢
  omega

/-- Three separately attained pair edges supply independent summand witnesses. -/
theorem sum_mem_of_pair_edges (A : Finset (ℤ × ℤ × ℤ))
    (x y u z v w : ℤ)
    (hxy : (x,y) ∈ A.image (fun t => (t.1,t.2.1)))
    (huz : (u,z) ∈ A.image (fun t => (t.1,t.2.2)))
    (hvw : (v,w) ∈ A.image (fun t => (t.2.1,t.2.2))) :
    (y+z, -x+w, -u-v) ∈ NoncommutingFiber.mixedSum A := by
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hxy
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp huz
  obtain ⟨c,hc,hec⟩ := Finset.mem_image.mp hvw
  have hs : NoncommutingFiber.L0 a + NoncommutingFiber.L1 b +
      NoncommutingFiber.L2 c ∈ NoncommutingFiber.mixedSum A := by
    exact Finset.mem_add.mpr ⟨_, Finset.mem_add.mpr
      ⟨_, Finset.mem_image_of_mem _ ha, _, Finset.mem_image_of_mem _ hb, rfl⟩,
      _, Finset.mem_image_of_mem _ hc, rfl⟩
  have he : NoncommutingFiber.L0 a + NoncommutingFiber.L1 b +
      NoncommutingFiber.L2 c = (y+z, -x+w, -u-v) := by
    simp only [Prod.mk.injEq] at hea heb hec
    ext <;> simp [NoncommutingFiber.L0, NoncommutingFiber.L1,
      NoncommutingFiber.L2, hea.1, hea.2, heb.1, heb.2, hec.1, hec.2] <;> ring
  rwa [he] at hs

/-- Ordered truncations force the first coordinate of every common output. -/
theorem overlap_first (X Y Z : Finset ℤ) (x0 y0 z0 : ℤ)
    (s : ℤ × ℤ × ℤ)
    (h1 : s ∈ (X ×ˢ ((Y.filter (· ≤ y0)) ×ˢ (Z.filter (z0 ≤ ·)))).image
      (block1 x0 y0 z0))
    (h2 : s ∈ (X ×ˢ (Y ×ˢ (Z.filter (z0 ≤ ·)))).image (block2 x0 y0 z0)) :
    s.1 = y0 + z0 := by
  obtain ⟨⟨x,y,z⟩,ht,rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨⟨u,v,w⟩,hu,he⟩ := Finset.mem_image.mp h2
  simp only [Finset.mem_product, Finset.mem_filter] at ht hu
  simp only [block1, block2, Prod.mk.injEq] at he ⊢
  omega

/-- True overlap injects into each of `X×Y`, `X×Z`, and `Y×Z`, including
when any factor is a singleton or has arbitrary gaps. -/
theorem overlap_card_bounds (X Y Z : Finset ℤ) (x0 y0 z0 : ℤ) :
    let C1 := (X ×ˢ ((Y.filter (· ≤ y0)) ×ˢ (Z.filter (z0 ≤ ·)))).image
      (block1 x0 y0 z0)
    let C2 := (X ×ˢ (Y ×ˢ (Z.filter (z0 ≤ ·)))).image (block2 x0 y0 z0)
    (C1 ∩ C2).card ≤ X.card * Y.card ∧
    (C1 ∩ C2).card ≤ X.card * Z.card ∧
    (C1 ∩ C2).card ≤ Y.card * Z.card := by
  dsimp only
  let C1 := (X ×ˢ ((Y.filter (· ≤ y0)) ×ˢ (Z.filter (z0 ≤ ·)))).image
    (block1 x0 y0 z0)
  let C2 := (X ×ˢ (Y ×ˢ (Z.filter (z0 ≤ ·)))).image (block2 x0 y0 z0)
  have hfirst (s : ℤ × ℤ × ℤ) (hs : s ∈ C1 ∩ C2) : s.1 = y0 + z0 :=
    overlap_first X Y Z x0 y0 z0 s (Finset.mem_inter.mp hs).1
      (Finset.mem_inter.mp hs).2
  have hxy : (C1 ∩ C2).card ≤ (X ×ˢ Y).card := by
    apply Finset.card_le_card_of_injOn (fun s : ℤ × ℤ × ℤ => (z0-s.2.1,-s.2.2-x0))
    · intro s hs
      obtain ⟨⟨x,y,z⟩,ht,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hs).2
      simp only [Finset.mem_product, Finset.mem_filter] at ht
      simpa [block2] using And.intro ht.1 ht.2.1
    · intro s hs t ht he
      have hs1 := hfirst s hs
      have ht1 := hfirst t ht
      simp only [Prod.mk.injEq] at he
      apply Prod.ext
      · omega
      · apply Prod.ext <;> omega
  have hxz : (C1 ∩ C2).card ≤ (X ×ˢ Z).card := by
    apply Finset.card_le_card_of_injOn (fun s : ℤ × ℤ × ℤ => (-s.2.2-y0,s.2.1+x0))
    · intro s hs
      obtain ⟨⟨x,y,z⟩,ht,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hs).1
      simp only [Finset.mem_product, Finset.mem_filter] at ht
      simpa [block1] using And.intro ht.1 ht.2.2.1
    · intro s hs t ht he
      have hs1 := hfirst s hs
      have ht1 := hfirst t ht
      simp only [Prod.mk.injEq] at he
      apply Prod.ext
      · omega
      · apply Prod.ext <;> omega
  have hyz : (C1 ∩ C2).card ≤ (Y ×ˢ Z).card := by
    apply Finset.card_le_card_of_injOn (fun s : ℤ × ℤ × ℤ => (-s.2.2-x0,s.2.1+x0))
    · intro s hs
      have hs2 := (Finset.mem_inter.mp hs).2
      obtain ⟨⟨x,y,z⟩,ht,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hs).1
      obtain ⟨⟨u,v,w⟩,hu,he⟩ := Finset.mem_image.mp hs2
      simp only [Finset.mem_product, Finset.mem_filter] at ht hu
      simp only [block1, block2, Prod.mk.injEq] at he
      apply Finset.mem_product.mpr
      constructor
      · have hv : -((block1 x0 y0 z0 (x,y,z)).2.2)-x0 = v := by
          simp only [block1]; omega
        change -((block1 x0 y0 z0 (x,y,z)).2.2)-x0 ∈ Y
        rw [hv]
        exact hu.2.1
      · simpa [block1] using ht.2.2.1
    · intro s hs t ht he
      have hs1 := hfirst s hs
      have ht1 := hfirst t ht
      simp only [Prod.mk.injEq] at he
      apply Prod.ext
      · omega
      · apply Prod.ext <;> omega
  simpa only [Finset.card_product] using And.intro hxy (And.intro hxz hyz)

/-- Three pairwise overlap bounds imply the one-tenth-volume bound at volume 1000. -/
theorem ten_mul_le_volume (a b c o : ℕ) (hn : 1000 ≤ a*b*c)
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

/-- Deleting parameters failing any one of three independent coordinate tests
costs at most the sum of the three full free-coordinate fiber counts. -/
theorem product_card_le_good_add_bad (X Y Z : Finset ℤ)
    (p q r : ℤ → Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r] :
    X.card * Y.card * Z.card ≤
      (X.filter p).card * (Y.filter q).card * (Z.filter r).card +
      (X.filter (fun x => ¬p x)).card * Y.card * Z.card +
      X.card * (Y.filter (fun y => ¬q y)).card * Z.card +
      X.card * Y.card * (Z.filter (fun z => ¬r z)).card := by
  let G := (X.filter p) ×ˢ ((Y.filter q) ×ˢ (Z.filter r))
  let D1 := (X.filter (fun x => ¬p x)) ×ˢ (Y ×ˢ Z)
  let D2 := X ×ˢ ((Y.filter (fun y => ¬q y)) ×ˢ Z)
  let D3 := X ×ˢ (Y ×ˢ (Z.filter (fun z => ¬r z)))
  have hcover : X ×ˢ (Y ×ˢ Z) ⊆ ((G ∪ D1) ∪ D2) ∪ D3 := by
    rintro ⟨x,y,z⟩ ht
    simp only [Finset.mem_product] at ht
    by_cases hp : p x
    · by_cases hq : q y
      · by_cases hr : r z
        · simp [G,D1,D2,D3,ht,hp,hq,hr]
        · simp [G,D1,D2,D3,ht,hp,hq,hr]
      · simp [G,D1,D2,D3,ht,hp,hq]
    · simp [G,D1,D2,D3,ht,hp]
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have h12 := Finset.card_union_le (G ∪ D1) D2
  have h1 := Finset.card_union_le G D1
  have htotal : (X ×ˢ (Y ×ˢ Z)).card ≤ G.card+D1.card+D2.card+D3.card := by omega
  simpa only [G,D1,D2,D3,Finset.card_product,Nat.mul_assoc] using htotal

/-- For an injective block, valid independent coordinate tests give certified
outputs; the remaining outputs are charged with all their free-axis factors. -/
theorem block_card_le_certified_add_bad (X Y Z : Finset ℤ)
    (p q r : ℤ → Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (f : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)) (hf : Function.Injective f)
    (M : Finset (ℤ × ℤ × ℤ))
    (hvalid : ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z, p x → q y → r z → f (x,y,z) ∈ M) :
    X.card * Y.card * Z.card ≤
      (((X ×ˢ (Y ×ˢ Z)).image f) ∩ M).card +
      (X.filter (fun x => ¬p x)).card * Y.card * Z.card +
      X.card * (Y.filter (fun y => ¬q y)).card * Z.card +
      X.card * Y.card * (Z.filter (fun z => ¬r z)).card := by
  let G := (X.filter p) ×ˢ ((Y.filter q) ×ˢ (Z.filter r))
  have hsub : G.image f ⊆ ((X ×ˢ (Y ×ˢ Z)).image f) ∩ M := by
    intro s hs
    obtain ⟨⟨x,y,z⟩,ht,rfl⟩ := Finset.mem_image.mp hs
    simp only [G,Finset.mem_product,Finset.mem_filter] at ht
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
      ⟨(x,y,z), Finset.mem_product.mpr ⟨ht.1.1,
        Finset.mem_product.mpr ⟨ht.2.1.1,ht.2.2.1⟩⟩,rfl⟩,
      hvalid x ht.1.1 y ht.2.1.1 z ht.2.2.1 ht.1.2 ht.2.1.2 ht.2.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective G hf] at hc
  simp only [G,Finset.card_product, ← Nat.mul_assoc] at hc
  have hh := product_card_le_good_add_bad X Y Z p q r
  omega

/-- The six corrected degree costs, with both free-coordinate factors retained. -/
def anchorCost (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (x0 y0 z0 : ℤ) : ℕ :=
  X.card * Z.card * (Y.filter (fun y => (x0,y) ∉ A.image (fun t => (t.1,t.2.1)))).card +
  X.card * Y.card * (Z.filter (fun z => (x0,z) ∉ A.image (fun t => (t.1,t.2.2)))).card +
  X.card * Y.card * (Z.filter (fun z => (y0,z) ∉ A.image (fun t => (t.2.1,t.2.2)))).card +
  Y.card * Z.card * (X.filter (fun x => (x,y0) ∉ A.image (fun t => (t.1,t.2.1)))).card +
  Y.card * Z.card * (X.filter (fun x => (x,z0) ∉ A.image (fun t => (t.1,t.2.2)))).card +
  X.card * Z.card * (Y.filter (fun y => (y,z0) ∉ A.image (fun t => (t.2.1,t.2.2)))).card

example : anchorCost {1} {2} {3} ∅ 1 2 3 = 6 := by decide
example : anchorCost {1} {2} {3} {(1,2,3)} 1 2 3 = 0 := by decide

/-- The two full blocks, less their true overlap and six full-fiber costs,
are certified in the actual mixed sum; no common witness is required. -/
theorem two_blocks_le_mixedSum_add_cost (X Y Z : Finset ℤ)
    (A : Finset (ℤ × ℤ × ℤ)) (x0 y0 z0 : ℤ) :
    let Y' := Y.filter (· ≤ y0)
    let Z' := Z.filter (z0 ≤ ·)
    let C1 := (X ×ˢ (Y' ×ˢ Z')).image (block1 x0 y0 z0)
    let C2 := (X ×ˢ (Y ×ˢ Z')).image (block2 x0 y0 z0)
    X.card * Y'.card * Z'.card + X.card * Y.card * Z'.card ≤
      (NoncommutingFiber.mixedSum A).card + (C1 ∩ C2).card + anchorCost X Y Z A x0 y0 z0 := by
  let Y' := Y.filter (· ≤ y0)
  let Z' := Z.filter (z0 ≤ ·)
  let M := NoncommutingFiber.mixedSum A
  let P := A.image (fun t => (t.1,t.2.1))
  let Q := A.image (fun t => (t.1,t.2.2))
  let R := A.image (fun t => (t.2.1,t.2.2))
  let C1 := (X ×ˢ (Y' ×ˢ Z')).image (block1 x0 y0 z0)
  let C2 := (X ×ˢ (Y ×ˢ Z')).image (block2 x0 y0 z0)
  have h1 := block_card_le_certified_add_bad X Y' Z'
    (fun x => (x,z0) ∈ Q) (fun y => (x0,y) ∈ P) (fun z => (y0,z) ∈ R)
    (block1 x0 y0 z0) (block1_injective x0 y0 z0) M (by
      intro x hx y hy z hz hp hq hr
      simpa [block1, M, sub_eq_add_neg, add_comm] using
        sum_mem_of_pair_edges A x0 y x z0 y0 z hq hp hr)
  have h2 := block_card_le_certified_add_bad X Y Z'
    (fun x => (x,y0) ∈ P) (fun y => (y,z0) ∈ R) (fun z => (x0,z) ∈ Q)
    (block2 x0 y0 z0) (block2_injective x0 y0 z0) M (by
      intro x hx y hy z hz hp hq hr
      simpa [block2, M, sub_eq_add_neg, add_comm] using
        sum_mem_of_pair_edges A x y0 x0 z y z0 hp hr hq)
  have hY : Y'.card ≤ Y.card := Finset.card_filter_le _ _
  have hZ : Z'.card ≤ Z.card := Finset.card_filter_le _ _
  have hYbad : (Y'.filter (fun y => (x0,y) ∉ P)).card ≤
      (Y.filter (fun y => (x0,y) ∉ P)).card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hy,hp⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,hp⟩
  have hZbad (S : Finset (ℤ × ℤ)) (v : ℤ) :
      (Z'.filter (fun z => (v,z) ∉ S)).card ≤
      (Z.filter (fun z => (v,z) ∉ S)).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hz,hp⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,hp⟩
  have h11 : (X.filter (fun x => (x,z0) ∉ Q)).card * Y'.card * Z'.card ≤
      Y.card * Z.card * (X.filter (fun x => (x,z0) ∉ Q)).card := by
    calc
      _ ≤ (X.filter (fun x => (x,z0) ∉ Q)).card * Y.card * Z.card := by gcongr
      _ = _ := by ring
  have h12 : X.card * (Y'.filter (fun y => (x0,y) ∉ P)).card * Z'.card ≤
      X.card * Z.card * (Y.filter (fun y => (x0,y) ∉ P)).card := by
    calc
      _ ≤ X.card * (Y.filter (fun y => (x0,y) ∉ P)).card * Z.card := by gcongr
      _ = _ := by ring
  have h13 : X.card * Y'.card * (Z'.filter (fun z => (y0,z) ∉ R)).card ≤
      X.card * Y.card * (Z.filter (fun z => (y0,z) ∉ R)).card := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hY) (hZbad R y0)
  have h21 : (X.filter (fun x => (x,y0) ∉ P)).card * Y.card * Z'.card ≤
      Y.card * Z.card * (X.filter (fun x => (x,y0) ∉ P)).card := by
    calc
      _ ≤ (X.filter (fun x => (x,y0) ∉ P)).card * Y.card * Z.card := by gcongr
      _ = _ := by ring
  have h22 : X.card * (Y.filter (fun y => (y,z0) ∉ R)).card * Z'.card ≤
      X.card * Z.card * (Y.filter (fun y => (y,z0) ∉ R)).card := by
    calc
      _ ≤ X.card * (Y.filter (fun y => (y,z0) ∉ R)).card * Z.card := by gcongr
      _ = _ := by ring
  have h23 : X.card * Y.card * (Z'.filter (fun z => (x0,z) ∉ Q)).card ≤
      X.card * Y.card * (Z.filter (fun z => (x0,z) ∉ Q)).card := by
    exact Nat.mul_le_mul_left _ (hZbad Q x0)
  have hsum : (C1 ∩ M).card + (C2 ∩ M).card ≤ M.card + (C1 ∩ C2).card := by
    have he := Finset.card_union_add_card_inter (C1 ∩ M) (C2 ∩ M)
    have hu : ((C1 ∩ M) ∪ (C2 ∩ M)).card ≤ M.card := by
      apply Finset.card_le_card
      intro s hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact (Finset.mem_inter.mp hs).2
      · exact (Finset.mem_inter.mp hs).2
    have hi : ((C1 ∩ M) ∩ (C2 ∩ M)).card ≤ (C1 ∩ C2).card := by
      apply Finset.card_le_card
      intro s hs
      obtain ⟨hs1,hs2⟩ := Finset.mem_inter.mp hs
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hs1).1,(Finset.mem_inter.mp hs2).1⟩
    omega
  change X.card * Y'.card * Z'.card + X.card * Y.card * Z'.card ≤
    M.card + (C1 ∩ C2).card + anchorCost X Y Z A x0 y0 z0
  change X.card * Y'.card * Z'.card ≤ (C1 ∩ M).card + _ + _ + _ at h1
  change X.card * Y.card * Z'.card ≤ (C2 ∩ M).card + _ + _ + _ at h2
  unfold anchorCost
  dsimp only [P,Q,R] at h1 h2 h11 h12 h13 h21 h22 h23
  omega

/-- A top quantile pool has exactly ceiling one twentieth of the axis, and
any anchor in it retains at least nineteen twentieths of that axis below it. -/
theorem exists_top_pool (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ T : Finset ℤ, T ⊆ S ∧ T.card = (S.card+19)/20 ∧ T.Nonempty ∧
      ∀ t ∈ T, 19*S.card ≤ 20*(S.filter (· ≤ t)).card := by
  let b := S.card
  let k := (b+19)/20
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

/-- A bottom quantile pool has exactly ceiling one twentieth of the axis,
and every anchor retains at least nineteen twentieths above it. -/
theorem exists_bottom_pool (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ T : Finset ℤ, T ⊆ S ∧ T.card = (S.card+19)/20 ∧ T.Nonempty ∧
      ∀ t ∈ T, 19*S.card ≤ 20*(S.filter (t ≤ ·)).card := by
  let b := S.card
  let k := (b+19)/20
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

/-- Summing missing-edge degrees over the first endpoint counts every hole once. -/
theorem sum_missing_degree (X Y : Finset ℤ) (P : Finset (ℤ × ℤ)) :
    (∑ x ∈ X, (Y.filter (fun y => (x,y) ∉ P)).card) = ((X ×ˢ Y) \ P).card := by
  simp only [Finset.sdiff_eq_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]

/-- Summing missing-edge degrees over the second endpoint also counts every hole once. -/
theorem sum_missing_degree_right (X Y : Finset ℤ) (P : Finset (ℤ × ℤ)) :
    (∑ y ∈ Y, (X.filter (fun x => (x,y) ∉ P)).card) = ((X ×ˢ Y) \ P).card := by
  rw [← sum_missing_degree X Y P]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- Every absent `XY` edge has a disjoint full `Z` fiber missing from the box. -/
theorem missing_xy_fibers (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ)) :
    Z.card * ((X ×ˢ Y) \ A.image (fun t => (t.1,t.2.1))).card ≤
      ((X ×ˢ (Y ×ˢ Z)) \ A).card := by
  have hc : ((((X ×ˢ Y) \ A.image (fun t => (t.1,t.2.1))) ×ˢ Z)).card ≤
      ((X ×ˢ (Y ×ˢ Z)) \ A).card := by
    apply Finset.card_le_card_of_injOn (fun t : (ℤ × ℤ) × ℤ => (t.1.1,t.1.2,t.2))
    · rintro ⟨⟨x,y⟩,z⟩ ht
      obtain ⟨he,hz⟩ := Finset.mem_product.mp ht
      obtain ⟨hxy,hn⟩ := Finset.mem_sdiff.mp he
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr
        ⟨hx, Finset.mem_product.mpr ⟨hy,hz⟩⟩,
        fun ha => hn (Finset.mem_image_of_mem _ ha)⟩
    · rintro ⟨⟨x,y⟩,z⟩ _ ⟨⟨x',y'⟩,z'⟩ _ he
      simpa only [Prod.mk.injEq,and_assoc] using he
  simpa only [Finset.card_product,Nat.mul_comm] using hc

/-- Every absent `XZ` edge has a disjoint full `Y` fiber missing from the box. -/
theorem missing_xz_fibers (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ)) :
    Y.card * ((X ×ˢ Z) \ A.image (fun t => (t.1,t.2.2))).card ≤
      ((X ×ˢ (Y ×ˢ Z)) \ A).card := by
  have hc : ((((X ×ˢ Z) \ A.image (fun t => (t.1,t.2.2))) ×ˢ Y)).card ≤
      ((X ×ˢ (Y ×ˢ Z)) \ A).card := by
    apply Finset.card_le_card_of_injOn (fun t : (ℤ × ℤ) × ℤ => (t.1.1,t.2,t.1.2))
    · rintro ⟨⟨x,z⟩,y⟩ ht
      obtain ⟨he,hy⟩ := Finset.mem_product.mp ht
      obtain ⟨hxz,hn⟩ := Finset.mem_sdiff.mp he
      obtain ⟨hx,hz⟩ := Finset.mem_product.mp hxz
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr
        ⟨hx, Finset.mem_product.mpr ⟨hy,hz⟩⟩,
        fun ha => hn (Finset.mem_image_of_mem _ ha)⟩
    · rintro ⟨⟨x,z⟩,y⟩ _ ⟨⟨x',z'⟩,y'⟩ _ he
      simpa only [Prod.mk.injEq,and_assoc,and_left_comm,and_comm] using he
  simpa only [Finset.card_product,Nat.mul_comm] using hc

/-- Every absent `YZ` edge has a disjoint full `X` fiber missing from the box. -/
theorem missing_yz_fibers (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ)) :
    X.card * ((Y ×ˢ Z) \ A.image (fun t => (t.2.1,t.2.2))).card ≤
      ((X ×ˢ (Y ×ˢ Z)) \ A).card := by
  have hc : ((((Y ×ˢ Z) \ A.image (fun t => (t.2.1,t.2.2))) ×ˢ X)).card ≤
      ((X ×ˢ (Y ×ˢ Z)) \ A).card := by
    apply Finset.card_le_card_of_injOn (fun t : (ℤ × ℤ) × ℤ => (t.2,t.1.1,t.1.2))
    · rintro ⟨⟨y,z⟩,x⟩ ht
      obtain ⟨he,hx⟩ := Finset.mem_product.mp ht
      obtain ⟨hyz,hn⟩ := Finset.mem_sdiff.mp he
      obtain ⟨hy,hz⟩ := Finset.mem_product.mp hyz
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr
        ⟨hx, Finset.mem_product.mpr ⟨hy,hz⟩⟩,
        fun ha => hn (Finset.mem_image_of_mem _ ha)⟩
    · rintro ⟨⟨y,z⟩,x⟩ _ ⟨⟨y',z'⟩,x'⟩ _ he
      simpa only [Prod.mk.injEq,and_assoc,and_left_comm,and_comm] using he
  simpa only [Finset.card_product,Nat.mul_comm] using hc

/-- A finite nonempty family with average at most `K` has a member at most `K`. -/
theorem exists_cost_le (S : Finset ℤ) (hS : S.Nonempty) (f : ℤ → ℕ) (K : ℕ)
    (hsum : (∑ x ∈ S, f x) ≤ S.card*K) : ∃ x ∈ S, f x ≤ K := by
  by_contra hn
  push Not at hn
  have hstrict : (∑ _x ∈ S, K) < ∑ x ∈ S, f x := by
    exact Finset.sum_lt_sum_of_nonempty hS (fun x hx => hn x hx)
  simp only [Finset.sum_const, smul_eq_mul] at hstrict
  omega

/-- Choosing from a pool occupying at least a `1/q` fraction controls the
sum of two weighted degrees, without any positivity assumptions on the weights. -/
theorem choose_two_costs (S T : Finset ℤ) (hT : T ⊆ S) (hne : T.Nonempty)
    (q a b r : ℕ) (hpool : S.card ≤ q*T.card) (f g : ℤ → ℕ)
    (hf : a * (∑ x ∈ S, f x) ≤ r) (hg : b * (∑ x ∈ S, g x) ≤ r) :
    ∃ x ∈ T, S.card*a*f x + S.card*b*g x ≤ 2*q*r := by
  have hfs : (∑ x ∈ T, f x) ≤ ∑ x ∈ S, f x := Finset.sum_le_sum_of_subset hT
  have hgs : (∑ x ∈ T, g x) ≤ ∑ x ∈ S, g x := Finset.sum_le_sum_of_subset hT
  have hft : a*(∑ x ∈ T, f x) ≤ r := (Nat.mul_le_mul_left a hfs).trans hf
  have hgt : b*(∑ x ∈ T, g x) ≤ r := (Nat.mul_le_mul_left b hgs).trans hg
  apply exists_cost_le T hne
  calc
    (∑ x ∈ T, (S.card*a*f x + S.card*b*g x)) =
        S.card*(a*(∑ x ∈ T, f x)+b*(∑ x ∈ T, g x)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ S.card*(r+r) := Nat.mul_le_mul_left _ (Nat.add_le_add hft hgt)
    _ ≤ (q*T.card)*(r+r) := Nat.mul_le_mul_right _ hpool
    _ = T.card*(2*q*r) := by ring

/-- Actual missing-edge fibers and the two exact quantile pools supply anchors
with all six corrected costs totaling at most 82 times the missing volume. -/
theorem exists_good_anchor (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (hX : X.Nonempty) (hY : Y.Nonempty) (hZ : Z.Nonempty) :
    ∃ x0 ∈ X, ∃ y0 ∈ Y, ∃ z0 ∈ Z,
      19*Y.card ≤ 20*(Y.filter (· ≤ y0)).card ∧
      19*Z.card ≤ 20*(Z.filter (z0 ≤ ·)).card ∧
      anchorCost X Y Z A x0 y0 z0 ≤ 82*((X ×ˢ (Y ×ˢ Z)) \ A).card := by
  let P := A.image (fun t => (t.1,t.2.1))
  let Q := A.image (fun t => (t.1,t.2.2))
  let R := A.image (fun t => (t.2.1,t.2.2))
  let r := ((X ×ˢ (Y ×ˢ Z)) \ A).card
  obtain ⟨T,hTY,hTc,hTne,hretY⟩ := exists_top_pool Y hY
  obtain ⟨U,hUZ,hUc,hUne,hretZ⟩ := exists_bottom_pool Z hZ
  have hTsize : Y.card ≤ 20*T.card := by omega
  have hUsize : Z.card ≤ 20*U.card := by omega
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
    20 X.card Z.card r hTsize _ _ hfyz hgxy
  obtain ⟨z0,hz,hcostZ⟩ := choose_two_costs Z U hUZ hUne
    20 Y.card X.card r hUsize _ _ hgxz hgyz
  refine ⟨x0,hx,y0,hTY hy,z0,hUZ hz,hretY y0 hy,hretZ z0 hz,?_⟩
  have htotal := Nat.add_le_add (Nat.add_le_add hcostX hcostY) hcostZ
  dsimp only [P,Q,R] at htotal
  change anchorCost X Y Z A x0 y0 z0 ≤ 82*r
  unfold anchorCost
  nlinarith only [htotal]

/-- A 999/1000-dense subset of any integer Cartesian box of volume at least
1000 has mixed sum of cardinality at least three halves of the box volume. -/
theorem dense_product_bridge (X Y Z : Finset ℤ) (A : Finset (ℤ × ℤ × ℤ))
    (_hA : A ⊆ X ×ˢ (Y ×ˢ Z))
    (hn : 1000 ≤ (X ×ˢ (Y ×ˢ Z)).card)
    (hr : 1000*((X ×ˢ (Y ×ˢ Z)) \ A).card ≤ (X ×ˢ (Y ×ˢ Z)).card) :
    3*(X ×ˢ (Y ×ˢ Z)).card ≤ 2*(NoncommutingFiber.mixedSum A).card := by
  have hnvol : 1000 ≤ X.card*Y.card*Z.card := by
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
  have hw : w ≤ 82*r := hcost
  have hrn : 1000*r ≤ n := by
    simpa only [Finset.card_product,←Nat.mul_assoc] using hr
  have hprod : 361*n ≤ 400*p := by
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
  have hfinal : 3*n ≤ 2*m := by omega
  simpa only [n,m,Finset.card_product,←Nat.mul_assoc] using hfinal

/-- The exact general EFKY source statement implies the global mixed-sum gap
for every finite integer set with at least 1001 points. The source itself
remains an explicit premise, not an axiom or a proved repository theorem. -/
theorem global_gap_of_EFKY456 (hEFKY : EFKY456)
    (A : Finset (ℤ × ℤ × ℤ)) (hN : 1001 ≤ A.card) :
    1000001*A.card ≤ 1000000*(NoncommutingFiber.mixedSum A).card := by
  by_contra hgap
  have hsmall : 1000000*(NoncommutingFiber.mixedSum A).card < 1000001*A.card := by omega
  obtain ⟨X,Y,Z,hsym⟩ := near_box_of_counterexample hEFKY A hsmall
  let B := X ×ˢ (Y ×ˢ Z)
  let D := (A \ B) ∪ (B \ A)
  let A0 := A ∩ B
  have hD : 1000001*D.card ≤ 456*A.card := by
    have hre : (1000001 : ℝ)*(D.card : ℝ) ≤ 456*(A.card : ℝ) := by
      change (D.card : ℝ) ≤ (456 / 1000001 : ℝ)*A.card at hsym
      linarith
    exact_mod_cast hre
  have hrD : (B \ A).card ≤ D.card :=
    Finset.card_le_card Finset.subset_union_right
  have hcover : A ⊆ B ∪ D := by
    intro a ha
    by_cases hab : a ∈ B
    · exact Finset.mem_union_left _ hab
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha,hab⟩))
  have hNnD : A.card ≤ B.card+D.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hn : 1000 ≤ B.card := by omega
  have hr : 1000*(B \ A0).card ≤ B.card := by
    have he : B \ A0 = B \ A := by
      ext a
      simp [A0]
    rw [he]
    omega
  have hA0 : A0 ⊆ B := Finset.inter_subset_right
  have hbridge := dense_product_bridge X Y Z A0 hA0 hn hr
  have hmono : (NoncommutingFiber.mixedSum A0).card ≤
      (NoncommutingFiber.mixedSum A).card :=
    Finset.card_le_card (mixedSum_mono Finset.inter_subset_left)
  change 3*B.card ≤ 2*(NoncommutingFiber.mixedSum A0).card at hbridge
  omega

example : let B := (Finset.Icc (0 : ℤ) 999) ×ˢ (({0} : Finset ℤ) ×ˢ {0})
    B ⊆ B ∧ 1000 ≤ B.card ∧ 1000*(B \ B).card ≤ B.card := by
  norm_num

example : 1001 ≤ ((Finset.Icc (0 : ℤ) 1000) ×ˢ (({0} : Finset ℤ) ×ˢ {0})).card := by
  norm_num

end NoncommutingGoodAnchorGap
