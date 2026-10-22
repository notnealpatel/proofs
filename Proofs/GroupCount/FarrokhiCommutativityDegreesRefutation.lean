/-
# Farrokhi — coprime direct products and the number of relative commutativity degrees

## Source

M. Farrokhi D. G., *Finite groups with five relative commutativity degrees*,
arXiv:1912.04550 (v1, Dec 2019; published in Results in Mathematics,
DOI 10.1007/s00025-021-01591-3).  The statement is the unnumbered
Conjecture after Lemma 2.6 (Conjecture 2.7 in the arXiv numbering).

Definitions (Section 1):

  d(H,G) := #{(h,g) ∈ H × G : hg = gh} / (|H||G|),
  D(G) = {d(H,G) : H ≤ G}.

Lemma 2.6 (proved in the paper): for finite groups `H`, `K` of coprime orders,
`D(H × K) = D(H)D(K)` is the set of products of elements of `D(H)` by elements
of `D(K)`, and `D(H) ∩ D(K) = {1}`.

The conjecture asserts `|D(H × K)| = |D(H)| × |D(K)|` for finite groups of
coprime orders. This module gives a counterexample:
`H = F₂₁ = C₇ ⋊ C₃` and `K = D₃₄` (dihedral of order 34) have coprime orders
21 and 34, and

  d(F₂₁, F₂₁) · d(C₁₇, D₃₄) = (5/21)(9/17) = 15/119 = (3/7)(5/17)
    = d(C₇, F₂₁) · d(D₃₄, D₃₄),

so the product map `D(H) × D(K) → D(H)D(K)` is not injective and
`|D(H × K)| < |D(H)||D(K)|`. The exact cardinality of `D(H × K)` is not
needed for this strict inequality.
-/
import Mathlib

set_option autoImplicit false

namespace Farrokhi.CommutativityDegrees

/-! ## Definitions mirroring the source -/

/-- The relative commutativity degree `d(L, G) = #{(l, g) ∈ L × G : lg = gl} / (|L||G|)`
of a subgroup `L` of a group `G` (Erfanian–Rezaei–Lescot; Farrokhi, Section 1).
For infinite `G` the cardinals are `0` and the value is the junk value `0`; every
statement below concerns finite groups. -/
noncomputable def relComm {G : Type*} [Group G] (L : Subgroup G) : ℚ :=
  (Nat.card {p : L × G // (p.1 : G) * p.2 = p.2 * p.1} : ℚ) /
    ((Nat.card L : ℚ) * Nat.card G)

/-- The set `D(G) = {d(L, G) : L ≤ G}` of relative commutativity degrees of `G`. -/
def relCommSet (G : Type*) [Group G] : Set ℚ :=
  Set.range (fun L : Subgroup G => relComm L)

/-! ## Counting bridge to computable filters -/

/-- The numerator of `d(L, G)` equals the number of commuting pairs `(x, g) ∈ G × G`
with `x` satisfying a decidable predicate equivalent to membership in `L`. -/
theorem card_commPairs_eq_filter {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (L : Subgroup G) (P : G → Prop) [DecidablePred P] (hP : ∀ x, x ∈ L ↔ P x) :
    Nat.card {p : L × G // (p.1 : G) * p.2 = p.2 * p.1} =
      ((Finset.univ : Finset (G × G)).filter
        (fun p => P p.1 ∧ p.1 * p.2 = p.2 * p.1)).card := by
  let e : {p : L × G // (p.1 : G) * p.2 = p.2 * p.1} ≃
      {p : G × G // P p.1 ∧ p.1 * p.2 = p.2 * p.1} :=
    { toFun := fun p => ⟨((p.1.1 : G), p.1.2), (hP _).1 p.1.1.2, p.2⟩
      invFun := fun p => ⟨(⟨p.1.1, (hP _).2 p.2.1⟩, p.1.2), p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The order of `L` equals the number of elements satisfying a decidable predicate
equivalent to membership in `L`. -/
theorem card_subgroup_eq_filter {G : Type*} [Group G] [Fintype G]
    (L : Subgroup G) (P : G → Prop) [DecidablePred P] (hP : ∀ x, x ∈ L ↔ P x) :
    Nat.card L = ((Finset.univ : Finset G).filter P).card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight hP), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-! ## Coprime direct products -/

/-- Coprime Goursat: if `gcd(|H|, |K|) = 1`, every subgroup of `H × K` is the product of
its two projections. -/
theorem eq_prod_map_of_coprime {H K : Type*} [Group H] [Group K]
    (hcop : (Nat.card H).Coprime (Nat.card K)) (L : Subgroup (H × K)) :
    L = (L.map (MonoidHom.fst H K)).prod (L.map (MonoidHom.snd H K)) := by
  obtain ⟨n, hn1, hn0⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨m, hm1, hm0⟩ := Nat.chineseRemainder hcop 0 1
  -- `x ^ n` kills the `K`-coordinate and fixes the `H`-coordinate; `x ^ m` the reverse.
  have hpowH : ∀ (h : H) (a b : ℕ), a ≡ b [MOD Nat.card H] → h ^ a = h ^ b := fun h a b hab =>
    pow_eq_pow_iff_modEq.2 (Nat.ModEq.of_dvd (orderOf_dvd_natCard h) hab)
  have hpowK : ∀ (k : K) (a b : ℕ), a ≡ b [MOD Nat.card K] → k ^ a = k ^ b := fun k a b hab =>
    pow_eq_pow_iff_modEq.2 (Nat.ModEq.of_dvd (orderOf_dvd_natCard k) hab)
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_prod.2 ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨h, k⟩ hx
    obtain ⟨⟨⟨h, k'⟩, hL, rfl⟩, ⟨⟨h', k⟩, hL', rfl⟩⟩ := Subgroup.mem_prod.1 hx
    have hh : ((h, (1 : K)) : H × K) ∈ L := by
      have hpow := L.pow_mem hL n
      have he : ((h, k') : H × K) ^ n = (h, 1) := by
        rw [Prod.pow_mk, hpowH h n 1 hn1, hpowK k' n 0 hn0, pow_one, pow_zero]
      rwa [he] at hpow
    have hk : (((1 : H), k) : H × K) ∈ L := by
      have hpow := L.pow_mem hL' m
      have he : ((h', k) : H × K) ^ m = (1, k) := by
        rw [Prod.pow_mk, hpowH h' m 0 hm1, hpowK k m 1 hm0, pow_one, pow_zero]
      rwa [he] at hpow
    have hmul := L.mul_mem hh hk
    simpa only [MonoidHom.coe_fst, MonoidHom.coe_snd, Prod.mk_mul_mk, mul_one, one_mul]
      using hmul

/-- Multiplicativity: `d(L₁ × L₂, H × K) = d(L₁, H) · d(L₂, K)`. -/
theorem relComm_prod {H K : Type*} [Group H] [Group K] (L₁ : Subgroup H) (L₂ : Subgroup K) :
    relComm (L₁.prod L₂) = relComm L₁ * relComm L₂ := by
  let e : {p : (L₁.prod L₂) × (H × K) // (p.1 : H × K) * p.2 = p.2 * p.1} ≃
      {p : L₁ × H // (p.1 : H) * p.2 = p.2 * p.1} ×
        {q : L₂ × K // (q.1 : K) * q.2 = q.2 * q.1} :=
    { toFun := fun p =>
        (⟨(⟨(p.1.1 : H × K).1, (Subgroup.mem_prod.1 p.1.1.2).1⟩, p.1.2.1),
            congrArg Prod.fst p.2⟩,
          ⟨(⟨(p.1.1 : H × K).2, (Subgroup.mem_prod.1 p.1.1.2).2⟩, p.1.2.2),
            congrArg Prod.snd p.2⟩)
      invFun := fun q =>
        ⟨(⟨((q.1.1.1 : H), (q.2.1.1 : K)), Subgroup.mem_prod.2 ⟨q.1.1.1.2, q.2.1.1.2⟩⟩,
            (q.1.1.2, q.2.1.2)),
          Prod.ext q.1.2 q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hL : Nat.card (L₁.prod L₂) = Nat.card L₁ * Nat.card L₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv L₁ L₂).toEquiv, Nat.card_prod]
  unfold relComm
  rw [Nat.card_congr e, Nat.card_prod, hL, Nat.card_prod]
  push_cast
  rw [div_mul_div_comm]
  ring_nf

/-- For coprime finite orders, `D(H × K)` is contained in the set of products
`D(H)D(K)` (one half of Farrokhi's Lemma 2.6(1)). -/
theorem relCommSet_prod_subset_of_coprime {H K : Type*} [Group H] [Group K]
    (hcop : (Nat.card H).Coprime (Nat.card K)) :
    relCommSet (H × K) ⊆
      (fun q : ℚ × ℚ => q.1 * q.2) '' (relCommSet H ×ˢ relCommSet K) := by
  rintro _ ⟨L, rfl⟩
  refine ⟨(relComm (L.map (MonoidHom.fst H K)), relComm (L.map (MonoidHom.snd H K))),
    ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
  dsimp only
  rw [← relComm_prod, ← eq_prod_map_of_coprime hcop L]

/-- A non-injective map on a finite set strictly shrinks its cardinality. -/
theorem ncard_image_lt_of_collision {α β : Type*} {S : Set α} (hS : S.Finite) (f : α → β)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hf : f x = f y) :
    (f '' S).ncard < S.ncard := by
  have himage : f '' S = f '' (S \ {x}) := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      by_cases hzx : z = x
      · subst hzx
        exact ⟨y, ⟨hy, fun h => hxy (Set.mem_singleton_iff.1 h).symm⟩, hf.symm⟩
      · exact ⟨z, ⟨hz, fun h => hzx (Set.mem_singleton_iff.1 h)⟩, rfl⟩
    · exact Set.image_mono Set.sdiff_subset
  rw [himage]
  calc (f '' (S \ {x})).ncard ≤ (S \ {x}).ncard := Set.ncard_image_le hS.sdiff
    _ < S.ncard := Set.ncard_sdiff_singleton_lt_of_mem hx hS

/-- `D(G)` is finite for a finite group `G`. -/
theorem relCommSet_finite (G : Type*) [Group G] [Finite G] : (relCommSet G).Finite :=
  Set.finite_range _

/-! ## The Frobenius group `F₂₁ = C₇ ⋊ C₃` -/

/-- Underlying data of `F₂₁ = C₇ ⋊ C₃`: a pair `(a, b) ∈ ℤ/7 × ℤ/3`, where the generator
of `C₃` acts on `C₇` by `x ↦ 2x` (and `2` has order `3` mod `7`). -/
@[ext]
structure F21 where
  /-- The `C₇` coordinate. -/
  a : ZMod 7
  /-- The `C₃` coordinate. -/
  b : ZMod 3
deriving DecidableEq

namespace F21

/-- The twisting character `C₃ → (ℤ/7)ˣ`, `b ↦ 2^b`. -/
def tw (b : ZMod 3) : ZMod 7 := 2 ^ b.val

/-- `tw` is multiplicative (since `2^3 = 1` in `ℤ/7`). -/
theorem tw_add (b d : ZMod 3) : tw (b + d) = tw b * tw d := by decide +revert

/-- `tw 0 = 1`. -/
theorem tw_zero : tw 0 = 1 := by decide

/-- Semidirect multiplication `(a, b)(c, d) = (a + 2^b c, b + d)`. -/
instance : Mul F21 := ⟨fun x y => ⟨x.a + tw x.b * y.a, x.b + y.b⟩⟩
/-- Identity `(0, 0)`. -/
instance : One F21 := ⟨⟨0, 0⟩⟩
/-- Inverse `(a, b)⁻¹ = (-(2^(-b) a), -b)`. -/
instance : Inv F21 := ⟨fun x => ⟨-(tw (-x.b) * x.a), -x.b⟩⟩

/-- First coordinate of a product. -/
@[simp] theorem mul_a (x y : F21) : (x * y).a = x.a + tw x.b * y.a := rfl
/-- Second coordinate of a product. -/
@[simp] theorem mul_b (x y : F21) : (x * y).b = x.b + y.b := rfl
/-- First coordinate of the identity. -/
@[simp] theorem one_a : (1 : F21).a = 0 := rfl
/-- Second coordinate of the identity. -/
@[simp] theorem one_b : (1 : F21).b = 0 := rfl
/-- First coordinate of an inverse. -/
@[simp] theorem inv_a (x : F21) : x⁻¹.a = -(tw (-x.b) * x.a) := rfl
/-- Second coordinate of an inverse. -/
@[simp] theorem inv_b (x : F21) : x⁻¹.b = -x.b := rfl

/-- `F₂₁` is a group. -/
instance : Group F21 where
  mul_assoc x y z := by
    ext
    · simp only [mul_a, mul_b, tw_add]; ring
    · simp only [mul_b]; ring
  one_mul x := by ext <;> simp [tw_zero]
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp only [mul_a, inv_a, inv_b, one_a]
      ring
    · simp

/-- `F₂₁ ≃ ℤ/7 × ℤ/3` as types. -/
def equivProd : F21 ≃ ZMod 7 × ZMod 3 where
  toFun x := (x.a, x.b)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `F₂₁` is finite, enumerated through `ℤ/7 × ℤ/3`. -/
instance : Fintype F21 := Fintype.ofEquiv _ equivProd.symm

/-- `|F₂₁| = 21`. -/
theorem natCard : Nat.card F21 = 21 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- `F₂₁` is non-abelian. -/
example : (⟨0, 1⟩ : F21) * ⟨1, 0⟩ ≠ ⟨1, 0⟩ * ⟨0, 1⟩ := by decide

/-- The normal subgroup `C₇ = {(a, 0)}` of `F₂₁`. -/
def c7 : Subgroup F21 where
  carrier := {x | x.b = 0}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    simp [hx, hy]
  one_mem' := rfl
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp [hx]

/-- `d(F₂₁, F₂₁) = 5/21` (the `|D(G)| = 3` formula `(p + q² - 1)/(pq²)` at `p = 7`,
`q = 3`). -/
theorem relComm_top : relComm (⊤ : Subgroup F21) = 5 / 21 := by
  unfold relComm
  rw [card_commPairs_eq_filter ⊤ (fun _ => True) (fun x => iff_of_true trivial trivial),
    card_subgroup_eq_filter ⊤ (fun _ => True) (fun x => iff_of_true trivial trivial),
    natCard]
  have hcomm : ((Finset.univ : Finset (F21 × F21)).filter
      (fun p => True ∧ p.1 * p.2 = p.2 * p.1)).card = 105 := by decide
  have hcard : ((Finset.univ : Finset F21).filter (fun _ => True)).card = 21 := by decide
  rw [hcomm, hcard]
  norm_num

/-- `d(C₇, F₂₁) = 3/7` (the formula `(p + q - 1)/(pq)` at `p = 7`, `q = 3`). -/
theorem relComm_c7 : relComm c7 = 3 / 7 := by
  unfold relComm
  rw [card_commPairs_eq_filter c7 (fun x => x.b = 0) (fun x => Iff.rfl),
    card_subgroup_eq_filter c7 (fun x => x.b = 0) (fun x => Iff.rfl), natCard]
  have hcomm : ((Finset.univ : Finset (F21 × F21)).filter
      (fun p => p.1.b = 0 ∧ p.1 * p.2 = p.2 * p.1)).card = 63 := by decide
  have hcard : ((Finset.univ : Finset F21).filter (fun x => x.b = 0)).card = 7 := by decide
  rw [hcomm, hcard]
  norm_num

end F21

/-! ## The dihedral group `D₃₄ = DihedralGroup 17` -/

open DihedralGroup

/-- Whether an element of the dihedral group is a rotation. -/
def isRot {n : ℕ} : DihedralGroup n → Bool
  | .r _ => true
  | .sr _ => false

/-- The cyclic subgroup of rotations of `DihedralGroup n`. -/
def rotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {x | isRot x = true}
  mul_mem' {x y} hx hy := by
    cases x <;> cases y <;> simp_all [isRot]
  one_mem' := rfl
  inv_mem' {x} hx := by
    cases x <;> simp_all [isRot]

set_option maxRecDepth 100000 in
/-- `d(D₃₄, D₃₄) = 5/17` (the formula `(p + q² - 1)/(pq²)` at `p = 17`, `q = 2`). -/
theorem relComm_top_dihedral : relComm (⊤ : Subgroup (DihedralGroup 17)) = 5 / 17 := by
  unfold relComm
  rw [card_commPairs_eq_filter ⊤ (fun _ => True) (fun x => iff_of_true trivial trivial),
    card_subgroup_eq_filter ⊤ (fun _ => True) (fun x => iff_of_true trivial trivial),
    DihedralGroup.nat_card]
  have hcomm : ((Finset.univ : Finset (DihedralGroup 17 × DihedralGroup 17)).filter
      (fun p => True ∧ p.1 * p.2 = p.2 * p.1)).card = 340 := by decide
  have hcard : ((Finset.univ : Finset (DihedralGroup 17)).filter (fun _ => True)).card = 34 := by
    decide
  rw [hcomm, hcard]
  norm_num

set_option maxRecDepth 100000 in
/-- `d(C₁₇, D₃₄) = 9/17` (the formula `(p + q - 1)/(pq)` at `p = 17`, `q = 2`). -/
theorem relComm_rotations : relComm (rotations 17) = 9 / 17 := by
  unfold relComm
  rw [card_commPairs_eq_filter (rotations 17) (fun x => isRot x = true) (fun x => Iff.rfl),
    card_subgroup_eq_filter (rotations 17) (fun x => isRot x = true) (fun x => Iff.rfl),
    DihedralGroup.nat_card]
  have hcomm : ((Finset.univ : Finset (DihedralGroup 17 × DihedralGroup 17)).filter
      (fun p => isRot p.1 = true ∧ p.1 * p.2 = p.2 * p.1)).card = 306 := by decide
  have hcard : ((Finset.univ : Finset (DihedralGroup 17)).filter
      (fun x => isRot x = true)).card = 17 := by decide
  rw [hcomm, hcard]
  norm_num

/-! ## The refutation -/

/-- `|F₂₁| = 21` and `|D₃₄| = 34` are coprime. -/
theorem coprime_card : (Nat.card F21).Coprime (Nat.card (DihedralGroup 17)) := by
  rw [F21.natCard, DihedralGroup.nat_card]; decide

/-- **Counterexample to Farrokhi's coprime conjecture (arXiv:1912.04550, Conjecture after
Lemma 2.6).**  For `H = F₂₁ = C₇ ⋊ C₃` and `K = D₃₄` (coprime orders 21 and 34),
`|D(H × K)| < |D(H)| · |D(K)|`, because
`d(F₂₁, F₂₁) d(C₁₇, D₃₄) = (5/21)(9/17) = (3/7)(5/17) = d(C₇, F₂₁) d(D₃₄, D₃₄)`. -/
theorem ncard_relCommSet_prod_lt :
    (relCommSet (F21 × DihedralGroup 17)).ncard <
      (relCommSet F21).ncard * (relCommSet (DihedralGroup 17)).ncard := by
  set S : Set (ℚ × ℚ) := relCommSet F21 ×ˢ relCommSet (DihedralGroup 17) with hSdef
  have hS : S.Finite := (relCommSet_finite F21).prod (relCommSet_finite _)
  have hx : ((5 / 21 : ℚ), (9 / 17 : ℚ)) ∈ S :=
    ⟨⟨⊤, F21.relComm_top⟩, ⟨rotations 17, relComm_rotations⟩⟩
  have hy : ((3 / 7 : ℚ), (5 / 17 : ℚ)) ∈ S :=
    ⟨⟨F21.c7, F21.relComm_c7⟩, ⟨⊤, relComm_top_dihedral⟩⟩
  have hxy : ((5 / 21 : ℚ), (9 / 17 : ℚ)) ≠ ((3 / 7 : ℚ), (5 / 17 : ℚ)) := by
    intro h
    have h1 := congrArg Prod.fst h
    norm_num at h1
  have hcollide : (5 / 21 : ℚ) * (9 / 17) = 3 / 7 * (5 / 17) := by norm_num
  have hsub := relCommSet_prod_subset_of_coprime coprime_card
  calc (relCommSet (F21 × DihedralGroup 17)).ncard
      ≤ ((fun q : ℚ × ℚ => q.1 * q.2) '' S).ncard := Set.ncard_le_ncard hsub (hS.image _)
    _ < S.ncard := ncard_image_lt_of_collision hS _ hx hy hxy hcollide
    _ = (relCommSet F21).ncard * (relCommSet (DihedralGroup 17)).ncard := Set.ncard_prod

/-- **Farrokhi's coprime direct-product conjecture is false.**  The conjecture
(arXiv:1912.04550, after Lemma 2.6) asserts that for all finite groups `H`, `K` of coprime
orders, `|D(H × K)| = |D(H)| · |D(K)|`; `H = F₂₁`, `K = D₃₄` is a counterexample. -/
theorem not_coprime_conjecture :
    ¬ ∀ (H K : Type) [Group H] [Group K] [Finite H] [Finite K],
      (Nat.card H).Coprime (Nat.card K) →
        (relCommSet (H × K)).ncard = (relCommSet H).ncard * (relCommSet K).ncard := by
  intro h
  have heq := h F21 (DihedralGroup 17) coprime_card
  exact (lt_irrefl _) (heq ▸ ncard_relCommSet_prod_lt)

end Farrokhi.CommutativityDegrees
