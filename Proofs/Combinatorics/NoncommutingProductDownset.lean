import Combinatorics.NoncommutingCubeCardinality

set_option autoImplicit false

namespace NoncommutingProductDownset

open NoncommutingFiber NoncommutingCubeCounting
open scoped Pointwise

/-- Dilation of a nonnegative coordinate ideal is tested by clamping the translated point. -/
theorem mem_dilation_iff (D : Finset (ℤ × ℤ)) (t : ℤ) (ht : 0 ≤ t)
    (hpos : ∀ p ∈ D, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hdown : ∀ p ∈ D, ∀ q : ℤ × ℤ, 0 ≤ q.1 → q.1 ≤ p.1 →
      0 ≤ q.2 → q.2 ≤ p.2 → q ∈ D) (p : ℤ × ℤ) :
    p ∈ D + (Finset.Icc 0 t ×ˢ Finset.Icc 0 t) ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ (max 0 (p.1-t), max 0 (p.2-t)) ∈ D := by
  constructor
  · intro hp
    obtain ⟨q, hq, r, hr, he⟩ := Finset.mem_add.mp hp
    obtain ⟨hx, hy⟩ := hpos q hq
    simp only [Finset.mem_product, Finset.mem_Icc] at hr
    have he1 : q.1 + r.1 = p.1 := congrArg Prod.fst he
    have he2 : q.2 + r.2 = p.2 := congrArg Prod.snd he
    refine ⟨by omega, by omega, hdown q hq _ (by positivity) ?_ (by positivity) ?_⟩ <;>
      simp only [Prod.fst, Prod.snd] <;> omega
  · rintro ⟨hx, hy, hq⟩
    refine Finset.mem_add.mpr ⟨_, hq, (min p.1 t, min p.2 t), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_Icc]
      omega
    · apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd] <;>
        omega

example :
    (0, 0) ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ)) ∧
    (∀ p ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ)), 0 ≤ p.1 ∧ 0 ≤ p.2) ∧
    (∀ p ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ)), ∀ q : ℤ × ℤ,
      0 ≤ q.1 → q.1 ≤ p.1 → 0 ≤ q.2 → q.2 ≤ p.2 →
      q ∈ ({(0, 0), (1, 0), (0, 1)} : Finset (ℤ × ℤ))) := by
  constructor
  · decide
  constructor
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro p (rfl | rfl | rfl) <;> norm_num
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro p (rfl | rfl | rfl) q hx hx' hy hy' <;>
      rcases q with ⟨x,y⟩ <;> simp only [Prod.mk.injEq] <;> omega

/-- A nonempty nonnegative coordinate ideal dilates by a square with exactly the
area, two projection strips, and corner-square contributions. -/
theorem card_dilation (D : Finset (ℤ × ℤ)) (t : ℤ) (ht : 0 ≤ t)
    (hne : D.Nonempty)
    (hpos : ∀ p ∈ D, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hdown : ∀ p ∈ D, ∀ q : ℤ × ℤ, 0 ≤ q.1 → q.1 ≤ p.1 →
      0 ≤ q.2 → q.2 ≤ p.2 → q ∈ D) :
    ((D + (Finset.Icc 0 t ×ˢ Finset.Icc 0 t)).card : ℤ) =
      D.card + t * ((D.image Prod.fst).card + (D.image Prod.snd).card : ℤ) + t^2 := by
  let I := Finset.Icc 0 (t-1)
  let B := D.image (fun p => (p.1+t, p.2+t))
  let X := I ×ˢ ((D.image Prod.snd).image (fun y => y+t))
  let Y := ((D.image Prod.fst).image (fun x => x+t)) ×ˢ I
  let Z := I ×ˢ I
  have hz : (0, 0) ∈ D := by
    obtain ⟨p, hp⟩ := hne
    exact hdown p hp _ (by omega) (hpos p hp).1 (by omega) (hpos p hp).2
  have hB (p : ℤ × ℤ) : p ∈ B ↔ t ≤ p.1 ∧ t ≤ p.2 ∧ (p.1-t,p.2-t) ∈ D := by
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hx, hy⟩ := hpos q hq
      simpa using And.intro (by omega : t ≤ q.1+t)
        (And.intro (by omega : t ≤ q.2+t) hq)
    · rintro ⟨_, _, hp⟩
      exact Finset.mem_image.mpr ⟨_, hp, by simp⟩
  have hX (p : ℤ × ℤ) : p ∈ X ↔ 0 ≤ p.1 ∧ p.1 < t ∧ t ≤ p.2 ∧ (0,p.2-t) ∈ D := by
    constructor
    · intro hp
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      have hqpos := hpos q hq
      have hx' := Finset.mem_Icc.mp hx
      refine ⟨hx'.1, by omega, by omega, ?_⟩
      have haxis := hdown q hq (0,q.2) (by omega) hqpos.1 hqpos.2 (by omega)
      simpa [← he] using haxis
    · rintro ⟨hx, hx', hy, hp⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hx, by omega⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨p.2-t, Finset.mem_image.mpr ⟨_, hp, rfl⟩, by omega⟩
  have hY (p : ℤ × ℤ) : p ∈ Y ↔ t ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 < t ∧ (p.1-t,0) ∈ D := by
    constructor
    · intro hp
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      have hqpos := hpos q hq
      have hy' := Finset.mem_Icc.mp hy
      refine ⟨by omega, hy'.1, by omega, ?_⟩
      have haxis := hdown q hq (q.1,0) hqpos.1 (by omega) (by omega) hqpos.2
      simpa [← he] using haxis
    · rintro ⟨hx, hy, hy', hp⟩
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_Icc.mpr ⟨hy, by omega⟩⟩
      exact Finset.mem_image.mpr ⟨p.1-t, Finset.mem_image.mpr ⟨_, hp, rfl⟩, by omega⟩
  have hZ (p : ℤ × ℤ) : p ∈ Z ↔ 0 ≤ p.1 ∧ p.1 < t ∧ 0 ≤ p.2 ∧ p.2 < t := by
    simp only [Z, I, Finset.mem_product, Finset.mem_Icc]
    omega
  have heq : D + (Finset.Icc 0 t ×ˢ Finset.Icc 0 t) = B ∪ X ∪ Y ∪ Z := by
    ext p
    rw [mem_dilation_iff D t ht hpos hdown]
    simp only [Finset.mem_union, hB, hX, hY, hZ]
    by_cases hx : t ≤ p.1 <;> by_cases hy : t ≤ p.2
    · simp only [max_eq_right (by omega : 0 ≤ p.1-t),
        max_eq_right (by omega : 0 ≤ p.2-t)]
      simp [hx, hy, not_lt.mpr hx, not_lt.mpr hy,
        show 0 ≤ p.1 by omega, show 0 ≤ p.2 by omega]
    · simp only [max_eq_right (by omega : 0 ≤ p.1-t),
        max_eq_left (by omega : p.2-t ≤ 0)]
      simp [hx, hy, not_lt.mpr hx, show p.2 < t by omega,
        show 0 ≤ p.1 by omega]
    · simp only [max_eq_left (by omega : p.1-t ≤ 0),
        max_eq_right (by omega : 0 ≤ p.2-t)]
      simp [hx, hy, not_lt.mpr hy, show p.1 < t by omega,
        show 0 ≤ p.2 by omega]
    · simp only [max_eq_left (by omega : p.1-t ≤ 0),
        max_eq_left (by omega : p.2-t ≤ 0)]
      simp [hx, hy, hz, show p.1 < t by omega, show p.2 < t by omega]
  have hdBX : Disjoint B X := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have hp' := (hB p).mp hp
    have hq' := (hX p).mp hq
    omega
  have hdY : Disjoint (B ∪ X) Y := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have hq' := (hY p).mp hq
    rcases Finset.mem_union.mp hp with hp | hp
    · have hp' := (hB p).mp hp
      omega
    · have hp' := (hX p).mp hp
      omega
  have hdZ : Disjoint (B ∪ X ∪ Y) Z := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have hq' := (hZ p).mp hq
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · have hp' := (hB p).mp hp
        omega
      · have hp' := (hX p).mp hp
        omega
    · have hp' := (hY p).mp hp
      omega
  have hcI : (I.card : ℤ) = t := by
    dsimp [I]
    rw [Int.card_Icc]
    simp [Int.toNat_of_nonneg ht]
  have hcB : B.card = D.card := Finset.card_image_of_injective _ (by
    intro p q he
    apply Prod.ext <;> have h := congrArg Prod.fst he <;>
      have h' := congrArg Prod.snd he <;> dsimp at * <;> omega)
  have hcX : X.card = I.card * (D.image Prod.snd).card := by
    rw [Finset.card_product, Finset.card_image_of_injective _ (add_left_injective t)]
  have hcY : Y.card = (D.image Prod.fst).card * I.card := by
    rw [Finset.card_product, Finset.card_image_of_injective _ (add_left_injective t)]
  rw [heq, Finset.card_union_of_disjoint hdZ, Finset.card_union_of_disjoint hdY,
    Finset.card_union_of_disjoint hdBX, hcB, hcX, hcY]
  simp only [Z, Finset.card_product, Nat.cast_add, Nat.cast_mul, hcI]
  ring

/-- A nonempty finite nonnegative integer ideal is the interval determined by its cardinality. -/
theorem ideal_eq_Icc_card (S : Finset ℤ) (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 ≤ x)
    (hdown : ∀ x ∈ S, ∀ y : ℤ, 0 ≤ y → y ≤ x → y ∈ S) :
    S = Finset.Icc 0 ((S.card : ℤ)-1) := by
  let m := S.max' hne
  have hm : m ∈ S := Finset.max'_mem S hne
  have hm0 := hpos m hm
  have heq : S = Finset.Icc 0 m := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_Icc.mpr ⟨hpos x hx, Finset.le_max' S x hx⟩
    · intro hx
      exact hdown m hm x (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2
  have hc : (S.card : ℤ) = m+1 := by
    rw [heq, Int.card_Icc]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ m+1)]
  rw [hc]
  simpa using heq

/-- The actual mixed sum of an interval times any planar set factors as a signed
injective image of the projection sum times the square dilation. -/
theorem mixedSum_product_eq (D : Finset (ℤ × ℤ)) (t : ℤ) (ht : 0 ≤ t) :
    mixedSum (Finset.Icc 0 t ×ˢ D) =
      (((D.image Prod.fst + D.image Prod.snd) ×ˢ
        (D + (Finset.Icc 0 t ×ˢ Finset.Icc 0 t))).image
          (fun p : ℤ × (ℤ × ℤ) => (p.1, p.2.2-t, -p.2.1))) := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨s, hs, w, hw, rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hx0, hd0⟩ := Finset.mem_product.mp hp0
    obtain ⟨hx1, hd1⟩ := Finset.mem_product.mp hp1
    obtain ⟨_, hd2⟩ := Finset.mem_product.mp hp2
    refine Finset.mem_image.mpr ⟨(p0.2.1+p1.2.2,
      p2.2.1+p1.1, p2.2.2+(t-p0.1)), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.add_mem_add (Finset.mem_image_of_mem Prod.fst hd0)
        (Finset.mem_image_of_mem Prod.snd hd1)
    · exact Finset.mem_add.mpr ⟨_, hd2, (p1.1,t-p0.1),
        Finset.mem_product.mpr ⟨hx1, Finset.mem_Icc.mpr (by
          have hx := Finset.mem_Icc.mp hx0
          omega)⟩, rfl⟩
    · simp only [L0, L1, L2, Prod.mk_add_mk]
      apply Prod.ext
      · simp
      · apply Prod.ext <;> dsimp <;> ring
  · intro p hp
    obtain ⟨⟨s,v⟩, hpair, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hs,hv⟩ := Finset.mem_product.mp hpair
    obtain ⟨y,hy,z,hz,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨d0,hd0,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d1,hd1,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨d,hd,r,hr,rfl⟩ := Finset.mem_add.mp hv
    obtain ⟨hr1,hr2⟩ := Finset.mem_product.mp hr
    have hp0 : (t-r.2,d0.1,d0.2) ∈ Finset.Icc 0 t ×ˢ D := by
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, hd0⟩
      have hr' := Finset.mem_Icc.mp hr2
      omega
    have hp1 : (r.1,d1.1,d1.2) ∈ Finset.Icc 0 t ×ˢ D :=
      Finset.mem_product.mpr ⟨hr1, hd1⟩
    have hp2 : (0,d.1,d.2) ∈ Finset.Icc 0 t ×ˢ D :=
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _,ht⟩, hd⟩
    have he : L0 (t-r.2,d0.1,d0.2) + L1 (r.1,d1.1,d1.2) +
        L2 (0,d.1,d.2) = (d0.1+d1.2,(d+r).2-t,-(d+r).1) := by
      simp only [L0,L1,L2,Prod.mk_add_mk,Prod.fst_add,Prod.snd_add]
      apply Prod.ext
      · simp
      · apply Prod.ext <;> dsimp <;> ring
    rw [← he]
    exact Finset.add_mem_add
      (Finset.add_mem_add (Finset.mem_image_of_mem L0 hp0)
        (Finset.mem_image_of_mem L1 hp1)) (Finset.mem_image_of_mem L2 hp2)

/-- The exact actual output cardinality of an interval times a nonempty planar ideal. -/
theorem card_mixedSum_product (D : Finset (ℤ × ℤ)) (a : ℤ) (ha : 1 ≤ a)
    (hne : D.Nonempty)
    (hpos : ∀ p ∈ D, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hdown : ∀ p ∈ D, ∀ q : ℤ × ℤ, 0 ≤ q.1 → q.1 ≤ p.1 →
      0 ≤ q.2 → q.2 ≤ p.2 → q ∈ D) :
    ((mixedSum (Finset.Icc 0 (a-1) ×ˢ D)).card : ℤ) =
      ((D.image Prod.fst).card + (D.image Prod.snd).card - 1 : ℤ) *
        (D.card + (a-1)*((D.image Prod.fst).card + (D.image Prod.snd).card : ℤ) + (a-1)^2) := by
  let b : ℤ := (D.image Prod.fst).card
  let c : ℤ := (D.image Prod.snd).card
  have hb : 1 ≤ b := by
    have hp : 0 < (D.image Prod.fst).card := (hne.image Prod.fst).card_pos
    have hp' : 1 ≤ (D.image Prod.fst).card := hp
    dsimp [b]
    exact_mod_cast hp'
  have hc : 1 ≤ c := by
    have hp : 0 < (D.image Prod.snd).card := (hne.image Prod.snd).card_pos
    have hp' : 1 ≤ (D.image Prod.snd).card := hp
    dsimp [c]
    exact_mod_cast hp'
  have hfst : D.image Prod.fst = Finset.Icc 0 (b-1) := by
    apply ideal_eq_Icc_card _ (hne.image Prod.fst)
    · intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact (hpos p hp).1
    · intro x hx y hy hyx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨(y,0),
        hdown p hp _ hy hyx (le_refl _) (hpos p hp).2, rfl⟩
  have hsnd : D.image Prod.snd = Finset.Icc 0 (c-1) := by
    apply ideal_eq_Icc_card _ (hne.image Prod.snd)
    · intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact (hpos p hp).2
    · intro x hx y hy hyx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨(0,y),
        hdown p hp _ (le_refl _) (hpos p hp).1 hy hyx, rfl⟩
  have hsum : D.image Prod.fst + D.image Prod.snd = Finset.Icc 0 (b+c-2) := by
    rw [hfst, hsnd]
    ext s
    constructor
    · intro hs
      obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hs
      have hx' := Finset.mem_Icc.mp hx
      have hy' := Finset.mem_Icc.mp hy
      exact Finset.mem_Icc.mpr (by omega)
    · intro hs
      have hs' := Finset.mem_Icc.mp hs
      refine Finset.mem_add.mpr ⟨max 0 (s-c+1), Finset.mem_Icc.mpr (by omega),
        s-max 0 (s-c+1), Finset.mem_Icc.mpr (by omega), by ring⟩
  have hsumcard : ((D.image Prod.fst + D.image Prod.snd).card : ℤ) = b+c-1 := by
    rw [hsum, Int.card_Icc]
    have he : b+c-2+1-0 = b+c-1 := by ring
    rw [he, Int.toNat_of_nonneg (by omega)]
  have hinj : Function.Injective (fun p : ℤ × (ℤ × ℤ) => (p.1,p.2.2-(a-1),-p.2.1)) := by
    rintro ⟨s,y,z⟩ ⟨s',y',z'⟩ he
    simp only [Prod.mk.injEq, neg_inj, sub_left_inj] at he ⊢
    exact ⟨he.1,he.2.2,he.2.1⟩
  rw [mixedSum_product_eq D (a-1) (by omega), Finset.card_image_of_injective _ hinj,
    Finset.card_product, Nat.cast_mul, hsumcard,
    card_dilation D (a-1) (by omega) hne hpos hdown]

private theorem scalar_sharp8 (N a b c d : ℤ)
    (hN : 1 ≤ N) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (haN : a ≤ N) (hbN : b ≤ N) (hcN : c ≤ N)
    (hd : 0 ≤ d) (hdmax : d ≤ b*c) :
    8*a*d - (b+c-1)*(d+(a-1)*(b+c)+(a-1)^2) ≤
      8*N^3-(2*N-1)^3 := by
  let G := fun x y z : ℤ => x^2+y^2+z^2+3*(x*y+x*z+y*z)-2*(x+y+z)+1
  have hGN : G N N N = 8*N^3-(2*N-1)^3 := by dsimp [G]; ring
  have hGmono (x y z w : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
      (hxw : x ≤ w) : G x y z ≤ G w y z := by
    have hp : 0 ≤ (w-x)*(w+x+3*y+3*z-2) :=
      mul_nonneg (by omega) (by omega)
    dsimp [G]
    nlinarith only [hp]
  have hG : G a b c ≤ G N N N := by
    calc
      G a b c ≤ G N b c := hGmono a b c N ha hb hc haN
      _ = G b N c := by dsimp [G]; ring
      _ ≤ G N N c := hGmono b N c N hb hN hc hbN
      _ = G c N N := by dsimp [G]; ring
      _ ≤ G N N N := hGmono c N N N hc hN hN hcN
  by_cases hk : 8*a-b-c+1 ≤ 0
  · have hkprod := mul_nonpos_of_nonpos_of_nonneg hk hd
    have hp : 0 ≤ (b+c-1)*(a-1)*(a+b+c-1) :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
    have hC : 0 ≤ 8*N^3-(2*N-1)^3 := by
      have hn : 0 ≤ N*(N-1) := mul_nonneg (by omega) (by omega)
      nlinarith
    nlinarith only [hkprod, hp, hC]
  · have hmass := mul_le_mul_of_nonneg_left hdmax (by omega : 0 ≤ 8*a-b-c+1)
    have hsquares : 8*a*b*c ≤ (a+b)*(a+c)*(b+c) := by
      have h1 := mul_nonneg (by omega : 0 ≤ a) (sq_nonneg (b-c))
      have h2 := mul_nonneg (by omega : 0 ≤ b) (sq_nonneg (c-a))
      have h3 := mul_nonneg (by omega : 0 ≤ c) (sq_nonneg (a-b))
      nlinarith only [h1,h2,h3]
    have he : 8*a*d - (b+c-1)*(d+(a-1)*(b+c)+(a-1)^2) ≤ G a b c := by
      dsimp [G]
      nlinarith only [hmass, hsquares]
    exact he.trans (hG.trans_eq hGN)

/-- Every product of a positive interval and a nonempty planar coordinate ideal
inside the cube obeys the sharp-eight subtraction-free output lower bound. -/
theorem cube_lower_bound (N a : ℤ) (hN : 1 ≤ N) (ha : 1 ≤ a) (haN : a ≤ N)
    (D : Finset (ℤ × ℤ)) (hne : D.Nonempty)
    (hD : D ⊆ Finset.Icc 0 (N-1) ×ˢ Finset.Icc 0 (N-1))
    (hdown : ∀ p ∈ D, ∀ q : ℤ × ℤ, 0 ≤ q.1 → q.1 ≤ p.1 →
      0 ≤ q.2 → q.2 ≤ p.2 → q ∈ D) :
    (2*N-1).toNat^3 ≤ (mixedSum (Finset.Icc 0 (a-1) ×ˢ D)).card +
      8*(cube 0 0 0 N \ (Finset.Icc 0 (a-1) ×ˢ D)).card := by
  let A := Finset.Icc 0 (a-1) ×ˢ D
  let b : ℤ := (D.image Prod.fst).card
  let c : ℤ := (D.image Prod.snd).card
  have hpos (p : ℤ × ℤ) (hp : p ∈ D) : 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    have hp' := Finset.mem_product.mp (hD hp)
    exact ⟨(Finset.mem_Icc.mp hp'.1).1,(Finset.mem_Icc.mp hp'.2).1⟩
  have hA : A ⊆ cube 0 0 0 N := by
    intro p hp
    obtain ⟨hx,hd⟩ := Finset.mem_product.mp hp
    have hx' := Finset.mem_Icc.mp hx
    have hd' := hD hd
    simp only [cube, zero_add, Finset.mem_product, Finset.mem_Icc] at hd' ⊢
    exact ⟨by omega,hd'⟩
  have hcI : ((Finset.Icc 0 (N-1)).card : ℤ) = N := by
    rw [Int.card_Icc]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ N)]
  have hpBounds (f : ℤ × ℤ → ℤ)
      (hf : ∀ p ∈ D, f p ∈ Finset.Icc 0 (N-1)) :
      1 ≤ ((D.image f).card : ℤ) ∧ ((D.image f).card : ℤ) ≤ N := by
    have hlo : 1 ≤ (D.image f).card := (hne.image f).card_pos
    have hsub : D.image f ⊆ Finset.Icc 0 (N-1) := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact hf p hp
    have hhi := Finset.card_le_card hsub
    constructor
    · exact_mod_cast hlo
    · have hz : ((D.image f).card : ℤ) ≤ (Finset.Icc 0 (N-1)).card := by exact_mod_cast hhi
      simpa only [hcI] using hz
  obtain ⟨hb,hbN⟩ := hpBounds Prod.fst (fun p hp => (Finset.mem_product.mp (hD hp)).1)
  obtain ⟨hc,hcN⟩ := hpBounds Prod.snd (fun p hp => (Finset.mem_product.mp (hD hp)).2)
  have hdmax : (D.card : ℤ) ≤ b*c := by
    have hsub : D ⊆ D.image Prod.fst ×ˢ D.image Prod.snd := by
      intro p hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hp,
        Finset.mem_image_of_mem Prod.snd hp⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product] at hh
    dsimp [b,c]
    exact_mod_cast hh
  have hnum := scalar_sharp8 N a b c D.card hN ha hb hc haN hbN hcN
    (Nat.cast_nonneg _) hdmax
  have hformula := card_mixedSum_product D a ha hne hpos hdown
  have hcA : (A.card : ℤ) = a*D.card := by
    dsimp [A]
    rw [Finset.card_product, Nat.cast_mul, Int.card_Icc]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ a)]
  have hsplit := Finset.card_sdiff_add_card_eq_card hA
  rw [NoncommutingCubeCardinality.card_cube 0 0 0 N hN] at hsplit
  have hsplitZ := congrArg (fun n : ℕ => (n : ℤ)) hsplit
  simp only [Nat.cast_add, Nat.cast_pow, Int.toNat_of_nonneg (by omega : 0 ≤ N), hcA] at hsplitZ
  have hgoal : (2*N-1)^3 ≤ ((mixedSum A).card : ℤ) + 8*((cube 0 0 0 N \ A).card : ℤ) := by
    change 8*a*D.card - (b+c-1)*(D.card+(a-1)*(b+c)+(a-1)^2) ≤ _ at hnum
    change ((mixedSum A).card : ℤ) = (b+c-1)*(D.card+(a-1)*(b+c)+(a-1)^2) at hformula
    linarith only [hnum,hformula,hsplitZ]
  have hout : ((2*N-1).toNat : ℤ) = 2*N-1 := Int.toNat_of_nonneg (by omega)
  rw [← hout] at hgoal
  exact_mod_cast hgoal

/-- The actual mixed-sum deficit of an interval times a planar ideal is at most
eight times its missing input mass in the containing cube. -/
theorem mixedSum_cube_deficit_le (N a : ℤ) (hN : 1 ≤ N) (ha : 1 ≤ a) (haN : a ≤ N)
    (D : Finset (ℤ × ℤ)) (hne : D.Nonempty)
    (hD : D ⊆ Finset.Icc 0 (N-1) ×ˢ Finset.Icc 0 (N-1))
    (hdown : ∀ p ∈ D, ∀ q : ℤ × ℤ, 0 ≤ q.1 → q.1 ≤ p.1 →
      0 ≤ q.2 → q.2 ≤ p.2 → q ∈ D) :
    (mixedSum (cube 0 0 0 N) \ mixedSum (Finset.Icc 0 (a-1) ×ˢ D)).card ≤
      8*(cube 0 0 0 N \ (Finset.Icc 0 (a-1) ×ˢ D)).card := by
  have hA : Finset.Icc 0 (a-1) ×ˢ D ⊆ cube 0 0 0 N := by
    intro p hp
    obtain ⟨hx,hd⟩ := Finset.mem_product.mp hp
    have hx' := Finset.mem_Icc.mp hx
    have hd' := hD hd
    simp only [cube, zero_add, Finset.mem_product, Finset.mem_Icc] at hd' ⊢
    exact ⟨by omega,hd'⟩
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (NoncommutingCubeCardinality.mixedSum_mono hA)
  rw [NoncommutingCubeCardinality.card_mixedSum_cube 0 0 0 N hN] at hsplit
  have hlower := cube_lower_bound N a hN ha haN D hne hD hdown
  omega

example :
    let D := (Finset.Icc (0 : ℤ) 2 ×ˢ Finset.Icc (0 : ℤ) 2).filter
      (fun p => p.1+p.2 ≤ 2)
    (mixedSum (cube 0 0 0 3) \ mixedSum (Finset.Icc 0 2 ×ˢ D)).card ≤
        8*(cube 0 0 0 3 \ (Finset.Icc 0 2 ×ˢ D)).card := by
  let D := (Finset.Icc (0 : ℤ) 2 ×ˢ Finset.Icc (0 : ℤ) 2).filter
    (fun p => p.1+p.2 ≤ 2)
  have hne : D.Nonempty := by decide
  have hD : D ⊆ Finset.Icc 0 (3-1) ×ˢ Finset.Icc 0 (3-1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hdown : ∀ p ∈ D, ∀ q : ℤ × ℤ, 0 ≤ q.1 → q.1 ≤ p.1 →
      0 ≤ q.2 → q.2 ≤ p.2 → q ∈ D := by
    intro p hp q hx hx' hy hy'
    simp only [D,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc] at hp ⊢
    omega
  simpa only [show (3 : ℤ)-1 = 2 by norm_num] using
    mixedSum_cube_deficit_le 3 3 (by decide) (by decide) (by decide) D hne hD hdown

end NoncommutingProductDownset
