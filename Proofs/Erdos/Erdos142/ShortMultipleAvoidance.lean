/-
  Erdős Problem #142 — avoidance of short-multiple preimages of a box.

  Provenance: Elsholtz–Hunter–Proske–Sauermann (EHPS), "Improving Behrend's
  construction", arXiv:2406.12290.  The good-direction Behrend argument chooses
  a nonzero "dilation" vector `b` so that no short multiple `t • b` with
  `1 ≤ t < N` falls into a small signed box `B`, and then embeds a length-`N`
  progression `a + {0,…,N-1} • b` into the prime grid injectively.  The present
  module isolates the finite, self-contained counting step of that argument:

  * the ambient group is the function module `Fin (2*k) → ZMod q` (the exponent
    vectors of the `2k`-dimensional residue grid);
  * `shortMultiplePreimage t B` is the preimage of `B` under the dilation
    `b ↦ t • b`;
  * multiplication by a nonzero residue of a prime field is a bijection, so
    every short-multiple preimage has exactly `#B` elements;
  * a union bound over the `N - 1` short multiples therefore shows the union of
    the preimages has at most `N * #B < q ^ (2*k)` elements, strictly fewer than
    the whole grid, so some `b` lies outside all of them.

  The box itself is factored through the structure `ShortMultipleBox`, carrying
  the data a concrete signed box must supply (`0 ∈ B`, negation stability, and
  the cardinality bound `#B ≤ (2*R - 1)^(2*k)`).  The counting theorems are
  parametric in an arbitrary `Finset`, so the concrete signed box can be
  constructed in a downstream module without revisiting the counting argument.

  This module only proves the finite existence statement and its injectivity
  corollary; it makes no area, density, or asymptotic-improvement claim.
-/

import Mathlib

set_option autoImplicit false

open Finset

namespace Erdos142

/-- The **short-multiple preimage** of a box `B`: the set of dilations `b` whose
short multiple `t • b` lands in `B`.  Membership is stated through the natural
scalar action on functions, matching the `t • b` convention used throughout. -/
def shortMultiplePreimage {q k : ℕ} [NeZero q] (t : ℕ) (B : Finset (Fin (2*k) → ZMod q)) :
    Finset (Fin (2*k) → ZMod q) :=
  Finset.univ.filter fun b => t • b ∈ B

/-- Membership in the short-multiple preimage is exactly membership of the
short multiple in the box. -/
@[simp]
theorem mem_shortMultiplePreimage {q k : ℕ} [NeZero q] {t : ℕ} {B : Finset (Fin (2*k) → ZMod q)}
    {b : Fin (2*k) → ZMod q} :
    b ∈ shortMultiplePreimage t B ↔ t • b ∈ B := by
  simp [shortMultiplePreimage]

/-- A **short-multiple box** in the prime grid `Fin (2*k) → ZMod q`: a finite
family of forbidden dilation targets that contains the origin, is stable under
negation, and has at most `(2*R - 1)^(2*k)` elements.  A concrete signed box is
constructed by filling these fields; the counting theorems below only consume
them. -/
structure ShortMultipleBox (q k R : ℕ) where
  /-- The forbidden set of dilation vectors. -/
  carrier : Finset (Fin (2*k) → ZMod q)
  /-- The origin is forbidden. -/
  zero_mem : (0 : Fin (2*k) → ZMod q) ∈ carrier
  /-- The forbidden set is symmetric under negation. -/
  neg_mem : ∀ b ∈ carrier, -b ∈ carrier
  /-- The size bound `#carrier ≤ (2*R - 1)^(2*k)`. -/
  card_le : carrier.card ≤ (2*R - 1)^(2*k)

/-- The singleton box `{0}` is a short-multiple box for `R = 1`, for every
prime modulus and every grid dimension. -/
example (q k : ℕ) : ShortMultipleBox q k 1 where
  carrier := {0}
  zero_mem := by simp
  neg_mem := by
    intro b hb
    rw [Finset.mem_singleton] at hb ⊢
    rw [hb, neg_zero]
  card_le := by
    rw [Finset.card_singleton]
    have : (2 * 1 - 1) ^ (2 * k) = 1 := by norm_num
    rw [this]

/-- **Union bound for short-multiple preimages.**  In a prime field, dilation by
a short multiple `1 ≤ t < N ≤ q` is a bijection of the grid, so each preimage
has exactly `#B` elements; the union over the `N` short multiples therefore has
cardinality at most `N * #B`. -/
theorem card_biUnion_shortMultiplePreimage_le {q k : ℕ} [Fact q.Prime] {N : ℕ}
    (hN1 : 1 ≤ N) (hNq : N ≤ q) (B : Finset (Fin (2*k) → ZMod q)) :
    ((Finset.Ioo 0 N).biUnion fun t => shortMultiplePreimage t B).card ≤ N * B.card := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hpre : ∀ t ∈ Finset.Ioo 0 N, (shortMultiplePreimage t B).card = B.card := by
    intro t ht
    rw [Finset.mem_Ioo] at ht
    obtain ⟨ht0, htN⟩ := ht
    have htq : t < q := lt_of_lt_of_le htN hNq
    have htne : (t : ZMod q) ≠ 0 := by
      intro h
      have hdvd : q ∣ t := (ZMod.natCast_eq_zero_iff t q).mp h
      have hle : q ≤ t := Nat.le_of_dvd ht0 hdvd
      omega
    have hinj : Function.Injective (fun b : Fin (2*k) → ZMod q => (t : ZMod q) • b) := by
      apply smul_right_injective
      intro h
      have hdvd : q ∣ t := (ZMod.natCast_eq_zero_iff t q).mp h
      have hle : q ≤ t := Nat.le_of_dvd ht0 hdvd
      omega
    refine Finset.card_bij
      (fun b (_ : b ∈ shortMultiplePreimage t B) => (t : ZMod q) • b) ?_ ?_ ?_
    · intro b hb
      rw [mem_shortMultiplePreimage] at hb
      rw [Nat.cast_smul_eq_nsmul]
      exact hb
    · intro b1 _ b2 _ heq
      exact hinj heq
    · intro y hy
      refine ⟨(t : ZMod q)⁻¹ • y, ?_, ?_⟩
      · rw [mem_shortMultiplePreimage]
        have hsm : t • ((t : ZMod q)⁻¹ • y) = y := by
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod q)]
          rw [smul_smul, mul_inv_cancel₀ htne, one_smul]
        rw [hsm]
        exact hy
      · rw [smul_smul, mul_inv_cancel₀ htne, one_smul]
  calc ((Finset.Ioo 0 N).biUnion fun t => shortMultiplePreimage t B).card
      ≤ (Finset.Ioo 0 N).card * B.card :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun t ht => (hpre t ht).le)
    _ = (N - 1) * B.card := by rw [Nat.card_Ioo, Nat.sub_zero]
    _ ≤ N * B.card := by
        rw [← Nat.sub_add_cancel hN1]
        exact Nat.mul_le_mul_right _ (Nat.le_add_right _ 1)

/-- **Existence of a short-multiple-avoiding dilation (generic box).**  Let `q`
be prime, `N ≤ q`, and let `B` be any finite family of grid vectors with
`N * #B < q ^ (2*k)`.  Then some `b : Fin (2*k) → ZMod q` avoids every
short-multiple preimage: `t • b ∉ B` for all `1 ≤ t < N`.  This is the finite
counting core of the good-direction argument, stated for an arbitrary box. -/
theorem exists_smul_notMem_of_card_mul_lt {q k : ℕ} [Fact q.Prime] {N : ℕ}
    (hN1 : 1 ≤ N) (hNq : N ≤ q) (B : Finset (Fin (2*k) → ZMod q))
    (hcard : N * B.card < q ^ (2*k)) :
    ∃ b : Fin (2*k) → ZMod q, ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ B := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hbound := card_biUnion_shortMultiplePreimage_le (k := k) hN1 hNq B
  have huniv : (Finset.univ : Finset (Fin (2*k) → ZMod q)).card = q ^ (2*k) := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hlt : ((Finset.Ioo 0 N).biUnion fun t => shortMultiplePreimage t B).card <
      (Finset.univ : Finset (Fin (2*k) → ZMod q)).card := by
    rw [huniv]
    exact hbound.trans_lt hcard
  obtain ⟨b, _, hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨b, ?_⟩
  intro t ht1 htN
  have htmem : t ∈ Finset.Ioo 0 N := Finset.mem_Ioo.mpr ⟨by omega, htN⟩
  have hnot : b ∉ shortMultiplePreimage t B := fun hb =>
    hbnot (Finset.mem_biUnion.mpr ⟨t, htmem, hb⟩)
  simpa only [mem_shortMultiplePreimage] using hnot

/-- **Existence of a short-multiple-avoiding dilation (structural box).**  The
box-shaped restatement of `exists_smul_notMem_of_card_mul_lt`: a
`ShortMultipleBox q k R` together with the scaled hypothesis
`N * (2*R - 1)^(2*k) < q ^ (2*k)` (and `N ≤ q`, `1 ≤ N`) yields a dilation `b`
avoiding every short-multiple preimage of the box carrier. -/
theorem ShortMultipleBox.exists_avoiding {q k R : ℕ} [Fact q.Prime] {N : ℕ}
    (box : ShortMultipleBox q k R) (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2*R - 1)^(2*k) < q ^ (2*k)) :
    ∃ b : Fin (2*k) → ZMod q, ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ box.carrier := by
  refine exists_smul_notMem_of_card_mul_lt hN1 hNq box.carrier ?_
  exact (Nat.mul_le_mul_left N box.card_le).trans_lt hscale

/-- **Injectivity of a translated short-multiple progression.**  If `0 ∈ B` and
`b` avoids the short-multiple preimages of `B`, then the affine map
`x ↦ a + x • b` is injective on `{0, 1, …, N-1}`: a collision would produce a
short multiple `t • b = 0 ∈ B` with `1 ≤ t < N`. -/
theorem injOn_translate_of_avoiding {q k : ℕ} {B : Finset (Fin (2*k) → ZMod q)}
    (hB0 : (0 : Fin (2*k) → ZMod q) ∈ B) {N : ℕ} {a b : Fin (2*k) → ZMod q}
    (hb : ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ B) :
    Set.InjOn (fun x : ℕ => a + x • b) (↑(Finset.range N) : Set ℕ) := by
  intro x hx y hy heq
  simp only [Finset.mem_coe, Finset.mem_range] at hx hy
  have hcancel : x • b = y • b := add_left_cancel heq
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exfalso
    have ht1 : 1 ≤ y - x := Nat.sub_pos_of_lt hxy
    have htN : y - x < N := by omega
    have hz : (y - x) • b = 0 := by
      have h0 : x • b + (y - x) • b = x • b + 0 := by
        rw [add_zero, ← add_nsmul, Nat.add_sub_of_le hxy.le, hcancel]
      exact add_left_cancel h0
    exact hb (y - x) ht1 htN (hz ▸ hB0)
  · exact hxy
  · exfalso
    have ht1 : 1 ≤ x - y := Nat.sub_pos_of_lt hyx
    have htN : x - y < N := by omega
    have hz : (x - y) • b = 0 := by
      have h0 : y • b + (x - y) • b = y • b + 0 := by
        rw [add_zero, ← add_nsmul, Nat.add_sub_of_le hyx.le, hcancel]
      exact add_left_cancel h0
    exact hb (x - y) ht1 htN (hz ▸ hB0)

/-- **Structural existence with injectivity.**  Combining `exists_avoiding` with
`injOn_translate_of_avoiding`, for any base point `a` there is a dilation `b`
that avoids all short-multiple preimages of the box and whose translated
progression `x ↦ a + x • b` is injective on `{0, 1, …, N-1}`. -/
theorem ShortMultipleBox.exists_avoiding_and_injOn {q k R : ℕ} [Fact q.Prime] {N : ℕ}
    (box : ShortMultipleBox q k R) (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2*R - 1)^(2*k) < q ^ (2*k)) (a : Fin (2*k) → ZMod q) :
    ∃ b : Fin (2*k) → ZMod q,
      (∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ box.carrier) ∧
        Set.InjOn (fun x : ℕ => a + x • b) (↑(Finset.range N) : Set ℕ) := by
  obtain ⟨b, hb⟩ := box.exists_avoiding hN1 hNq hscale
  exact ⟨b, hb, injOn_translate_of_avoiding box.zero_mem hb⟩

/-- **Cardinality form of the injectivity corollary.**  Under the hypotheses of
`injOn_translate_of_avoiding`, the translated progression
`{a + x • b | x < N}` is a set of exactly `N` distinct grid vectors. -/
theorem card_image_range_translate_of_avoiding {q k : ℕ}
    {B : Finset (Fin (2*k) → ZMod q)} (hB0 : (0 : Fin (2*k) → ZMod q) ∈ B)
    {N : ℕ} {a b : Fin (2*k) → ZMod q}
    (hb : ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ B) :
    ((Finset.range N).image fun x : ℕ => a + x • b).card = N :=
  (Finset.card_image_of_injOn (injOn_translate_of_avoiding hB0 hb)).trans (Finset.card_range N)

/-- **Unbundled box existence.**  The structural existence statement written out
over a raw `Finset`: a box that contains the origin, is negation stable, and has
cardinality at most `(2*R - 1)^(2*k)`, together with `N ≤ q`, `1 ≤ N` and
`N * (2*R - 1)^(2*k) < q ^ (2*k)`, admits a dilation avoiding every
short-multiple preimage of the box. -/
theorem exists_smul_notMem_of_box {q k R : ℕ} [Fact q.Prime] {N : ℕ}
    (B : Finset (Fin (2*k) → ZMod q)) (hB0 : (0 : Fin (2*k) → ZMod q) ∈ B)
    (hneg : ∀ b ∈ B, -b ∈ B) (hcard : B.card ≤ (2*R - 1)^(2*k))
    (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2*R - 1)^(2*k) < q ^ (2*k)) :
    ∃ b : Fin (2*k) → ZMod q, ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ B :=
  (ShortMultipleBox.mk B hB0 hneg hcard).exists_avoiding hN1 hNq hscale

/-- Ground truth: with `q = 5`, `k = 1`, `N = 2`, and the singleton box `{0}`,
the counting theorem produces a nonzero dilation vector, since
`2 * 1 = 2 < 25 = 5 ^ 2`. -/
example : ∃ b : Fin 2 → ZMod 5,
    ∀ t : ℕ, 1 ≤ t → t < 2 → t • b ∉ ({0} : Finset (Fin 2 → ZMod 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply exists_smul_notMem_of_card_mul_lt (q := 5) (k := 1) (N := 2)
  · norm_num
  · norm_num
  · rw [Finset.card_singleton]
    norm_num

#print axioms Erdos142.card_biUnion_shortMultiplePreimage_le
#print axioms Erdos142.exists_smul_notMem_of_card_mul_lt
#print axioms Erdos142.ShortMultipleBox.exists_avoiding
#print axioms Erdos142.injOn_translate_of_avoiding
#print axioms Erdos142.card_image_range_translate_of_avoiding
#print axioms Erdos142.exists_smul_notMem_of_box
#print axioms Erdos142.ShortMultipleBox.exists_avoiding_and_injOn

end Erdos142
