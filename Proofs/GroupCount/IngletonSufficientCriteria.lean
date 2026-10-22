/-
# Ingleton inequality: sufficient criteria

David A. Craven, *The Ingleton inequality holds for metacyclic groups and
fails for supersoluble groups*, arXiv:2505.22565, Section 2.

For a quadruple of subgroups, `H_I` denotes intersection over `I`. This file
proves the set-product cardinality formula and Lemma 2.1; the reduced-`H₁`
criterion (Lemma 2.4, `lem:reducesizeofH1`); the factor criterion
(Proposition 2.6, `prop:ingoffenderfact`); the cyclic-factor cases
(Corollary 2.7); and Lemma 2.8 (`lem:generalexclusions`) for trivial `H₁₂`
or subgroup set product `H₁H₂`, including the normal-factor and abelian
consequences. The abelian case is attributed there to Chan (2007).
The other trivial-intersection cases and the containment cases of Lemma 2.8
are not formalized.

The cyclic splitting step uses Bézout at the element level. For Lemma 2.8(3),
the proof bounds the set products `H₁₃H₂₃` and `H₁₄H₂₄` by the subgroups
`K ∩ H₃` and `K ∩ H₄`, where `K = H₁H₂`, before applying the subgroup order
inequality inside `K`. This avoids applying the subgroup order formula
directly to set products that need not be subgroups.
-/
import Mathlib

set_option autoImplicit false

open Pointwise

namespace Candidates.IngletonSufficientCriteria

variable {G : Type*} [Group G]

/-- The **Ingleton inequality** for a quadruple `(H₁, H₂, H₃, H₄)` of subgroups
(arXiv:2505.22565, Introduction):
`|H₁₂|·|H₁₃|·|H₁₄|·|H₂₃|·|H₂₄| ≤ |H₁|·|H₂|·|H₃₄|·|H₁₂₃|·|H₁₂₄|`,
where `H_I` is the intersection of the `H_i` with `i ∈ I`.  The quadruple is an
*Ingleton offender* exactly when this fails. -/
def Ingleton (H₁ H₂ H₃ H₄ : Subgroup G) : Prop :=
  Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
      Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) ≤
    Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
      Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)

/-! Examples for `Ingleton` in `C₂ = Multiplicative (ZMod 2)`:
for `(C₂, C₂, 1, 1)` the intersection side is `|H₁₂|·|H₁₃|·|H₁₄|·|H₂₃|·|H₂₄|
= 2·1·1·1·1` and the order side is `|H₁|·|H₂|·|H₃₄|·|H₁₂₃|·|H₁₂₄| = 2·2·1·1·1`;
for `(C₂, 1, C₂, C₂)` they are `1·2·2·1·1` and `2·1·2·1·1`. -/
example : Ingleton (⊤ : Subgroup (Multiplicative (ZMod 2))) ⊤ ⊥ ⊥ ↔
    2 * 1 * 1 * 1 * 1 ≤ 2 * 2 * 1 * 1 * 1 := by
  have h2 : Nat.card ↥(⊤ : Subgroup (Multiplicative (ZMod 2))) = 2 := by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card]; rfl
  unfold Ingleton
  simp only [inf_top_eq, inf_bot_eq]
  rw [Subgroup.card_bot, h2]

example : Ingleton (⊤ : Subgroup (Multiplicative (ZMod 2))) ⊥ ⊤ ⊤ ↔
    1 * 2 * 2 * 1 * 1 ≤ 2 * 1 * 2 * 1 * 1 := by
  have h2 : Nat.card ↥(⊤ : Subgroup (Multiplicative (ZMod 2))) = 2 := by
    rw [Subgroup.card_top, Nat.card_eq_fintype_card]; rfl
  unfold Ingleton
  simp only [inf_top_eq, inf_bot_eq]
  rw [Subgroup.card_bot, h2]

/-- **Product formula** `|AB|·|A ∩ B| = |A|·|B|` for subgroups `A, B` of a group,
where `AB` is the set product (not necessarily a subgroup).  Proved by
orbit-stabilizer for `A` acting on the left cosets `G ⧸ B`. -/
theorem card_mul_mul_card_inf (A B : Subgroup G) :
    Nat.card ((A : Set G) * B : Set G) * Nat.card ↥(A ⊓ B) =
      Nat.card A * Nat.card B := by
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient]
  have horb : MulAction.orbit A ((1 : G) : G ⧸ B) =
      ((A : Set G).image ((↑) : G → G ⧸ B)) := by
    ext q
    simp only [MulAction.mem_orbit_iff, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a, a.2, ?_⟩
      change ((a : G) : G ⧸ B) = (((a : G) * 1 : G) : G ⧸ B)
      rw [mul_one]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      change (((g : G) * 1 : G) : G ⧸ B) = ((g : G) : G ⧸ B)
      rw [mul_one]
  have hstab : MulAction.stabilizer A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (((a : G) * 1 : G) : G ⧸ B) = ((1 : G) : G ⧸ B) ↔ _
    rw [mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have hcard : Nat.card (B.subgroupOf A) = Nat.card ↥(A ⊓ B) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have key := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A ((1 : G) : G ⧸ B))
  rw [Nat.card_prod, horb, hstab, hcard] at key
  rw [← key]
  ring

/-- If the set product `AB` lies in a finite set `S`, then
`|A|·|B| ≤ |S|·|A ∩ B|`. -/
theorem card_mul_card_le_of_mul_subset [Finite G] (A B : Subgroup G) {S : Set G}
    (hS : (A : Set G) * B ⊆ S) :
    Nat.card A * Nat.card B ≤ Nat.card S * Nat.card ↥(A ⊓ B) := by
  rw [← card_mul_mul_card_inf]
  exact Nat.mul_le_mul_right _ (Nat.card_mono (Set.toFinite S) hS)

/-- **Lemma 2.1** of arXiv:2505.22565, in a monotone form: if `A, B ≤ X` and
`A ∩ B ≤ C` inside a finite group, then `|A|·|B| ≤ |X|·|C|`. -/
theorem card_mul_card_le_card_mul_card [Finite G] {A B X C : Subgroup G}
    (hA : A ≤ X) (hB : B ≤ X) (hC : A ⊓ B ≤ C) :
    Nat.card A * Nat.card B ≤ Nat.card X * Nat.card C := by
  have hsub : (A : Set G) * B ⊆ (X : Set G) :=
    Set.mul_subset_iff.mpr fun a ha b hb => X.mul_mem (hA ha) (hB hb)
  calc Nat.card A * Nat.card B ≤ Nat.card (X : Set G) * Nat.card ↥(A ⊓ B) :=
        card_mul_card_le_of_mul_subset A B hsub
    _ ≤ Nat.card X * Nat.card C :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hC)

/-- Every subgroup of a finite group has positive order. -/
theorem card_subgroup_pos [Finite G] (H : Subgroup G) : 0 < Nat.card H :=
  Nat.card_pos

/-- **Proposition 2.6** of arXiv:2505.22565: if `H₁₂ = H₁₂₃ H₁₂₄` (as sets),
then the quadruple `(H₁, H₂, H₃, H₄)` of subgroups of a finite group satisfies
the Ingleton inequality. -/
theorem ingleton_of_inf_eq_mul [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (h : ((H₁ ⊓ H₂ : Subgroup G) : Set G) =
      ((H₁ ⊓ H₂ ⊓ H₃ : Subgroup G) : Set G) * ((H₁ ⊓ H₂ ⊓ H₄ : Subgroup G) : Set G)) :
    Ingleton H₁ H₂ H₃ H₄ := by
  set P : Subgroup G := H₁ ⊓ H₃ ⊓ H₄ with hP
  set Q : Subgroup G := H₂ ⊓ H₃ ⊓ H₄ with hQ
  set R : Subgroup G := (H₁ ⊓ H₂ ⊓ H₃) ⊓ (H₁ ⊓ H₂ ⊓ H₄) with hR
  have i1 : Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) ≤ Nat.card H₁ * Nat.card P :=
    card_mul_card_le_card_mul_card inf_le_left inf_le_left
      (le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right))
  have i2 : Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) ≤ Nat.card H₂ * Nat.card Q :=
    card_mul_card_le_card_mul_card inf_le_left inf_le_left
      (le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right))
  have i3 : Nat.card P * Nat.card Q ≤ Nat.card ↥(H₃ ⊓ H₄) * Nat.card R := by
    refine card_mul_card_le_card_mul_card ?_ ?_ ?_ <;>
    · intro x hx
      simp only [hP, hQ, hR, Subgroup.mem_inf] at hx ⊢
      tauto
  have heq : Nat.card ↥(H₁ ⊓ H₂) * Nat.card R =
      Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) := by
    rw [← card_mul_mul_card_inf (H₁ ⊓ H₂ ⊓ H₃) (H₁ ⊓ H₂ ⊓ H₄), ← h]
    rfl
  have hpos : 0 < Nat.card P * Nat.card Q * Nat.card R :=
    Nat.mul_pos (Nat.mul_pos (card_subgroup_pos P) (card_subgroup_pos Q)) (card_subgroup_pos R)
  unfold Ingleton
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) * (Nat.card P * Nat.card Q * Nat.card R)
        = (Nat.card ↥(H₁ ⊓ H₂) * Nat.card R) *
            (Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄)) *
            (Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) * (Nat.card P * Nat.card Q) := by
          ring
      _ ≤ (Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) *
            (Nat.card H₁ * Nat.card P) * (Nat.card H₂ * Nat.card Q) *
            (Nat.card ↥(H₃ ⊓ H₄) * Nat.card R) := by
          rw [heq]
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl i1) i2) i3
      _ = Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) * (Nat.card P * Nat.card Q * Nat.card R) := by
          ring

/-- **Lemma 2.4** of arXiv:2505.22565 (`lem:reducesizeofH1`), contrapositive form:
if the Ingleton inequality holds for `(⟨H₁₃, H₁₄⟩, H₂, H₃, H₄)` then it holds for
`(H₁, H₂, H₃, H₄)`; equivalently, an offender stays an offender after replacing
`H₁` by `⟨H₁₃, H₁₄⟩`. -/
theorem ingleton_of_ingleton_sup_inf [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (h : Ingleton ((H₁ ⊓ H₃) ⊔ (H₁ ⊓ H₄)) H₂ H₃ H₄) : Ingleton H₁ H₂ H₃ H₄ := by
  set H₁' : Subgroup G := (H₁ ⊓ H₃) ⊔ (H₁ ⊓ H₄) with hH₁'
  have hle : H₁' ≤ H₁ := sup_le inf_le_left inf_le_left
  have e3 : H₁' ⊓ H₃ = H₁ ⊓ H₃ :=
    le_antisymm (inf_le_inf_right _ hle) (le_inf le_sup_left inf_le_right)
  have e4 : H₁' ⊓ H₄ = H₁ ⊓ H₄ :=
    le_antisymm (inf_le_inf_right _ hle) (le_inf le_sup_right inf_le_right)
  have e123 : H₁' ⊓ H₂ ⊓ H₃ = H₁ ⊓ H₂ ⊓ H₃ := by
    rw [inf_right_comm, e3, inf_right_comm]
  have e124 : H₁' ⊓ H₂ ⊓ H₄ = H₁ ⊓ H₂ ⊓ H₄ := by
    rw [inf_right_comm, e4, inf_right_comm]
  have key : Nat.card ↥(H₁ ⊓ H₂) * Nat.card H₁' ≤ Nat.card H₁ * Nat.card ↥(H₁' ⊓ H₂) :=
    card_mul_card_le_card_mul_card inf_le_left hle
      (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  unfold Ingleton at h ⊢
  rw [e3, e4, e123, e124] at h
  refine Nat.le_of_mul_le_mul_left ?_ (card_subgroup_pos H₁')
  calc Nat.card H₁' * (Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄))
        = (Nat.card ↥(H₁ ⊓ H₂) * Nat.card H₁') * (Nat.card ↥(H₁ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₄) * Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := by
          ring
      _ ≤ (Nat.card H₁ * Nat.card ↥(H₁' ⊓ H₂)) * (Nat.card ↥(H₁ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₄) * Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) :=
          Nat.mul_le_mul_right _ key
      _ = Nat.card H₁ * (Nat.card ↥(H₁' ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₄) * Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)) := by
          ring
      _ ≤ Nat.card H₁ * (Nat.card H₁' * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) :=
          Nat.mul_le_mul_left _ h
      _ = Nat.card H₁' * (Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) := by
          ring

/-- **Lemma 2.8(1)**, case `H₁₂ = 1` (arXiv:2505.22565): if `H₁ ∩ H₂` is trivial,
the Ingleton inequality holds.  Derived from Proposition 2.6 as in the paper. -/
theorem ingleton_of_inf_eq_bot [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (h : H₁ ⊓ H₂ = ⊥) : Ingleton H₁ H₂ H₃ H₄ := by
  apply ingleton_of_inf_eq_mul
  rw [h, bot_inf_eq, bot_inf_eq, Subgroup.coe_bot, Set.singleton_mul_singleton, mul_one]

/-- The set product `(H₁ ∩ H₃)(H₂ ∩ H₃)` lies in `K ∩ H₃` whenever `K = H₁H₂`
as sets. -/
theorem inf_mul_inf_subset {H₁ H₂ H₃ K : Subgroup G}
    (hK : (K : Set G) = (H₁ : Set G) * H₂) :
    ((H₁ ⊓ H₃ : Subgroup G) : Set G) * ((H₂ ⊓ H₃ : Subgroup G) : Set G) ⊆
      ((K ⊓ H₃ : Subgroup G) : Set G) := by
  refine Set.mul_subset_iff.mpr fun a ha b hb => ?_
  have ha' : a ∈ H₁ ∧ a ∈ H₃ := Subgroup.mem_inf.mp ha
  have hb' : b ∈ H₂ ∧ b ∈ H₃ := Subgroup.mem_inf.mp hb
  have hK' : a * b ∈ (K : Set G) := hK ▸ Set.mul_mem_mul ha'.1 hb'.1
  exact Subgroup.mem_inf.mpr ⟨hK', H₃.mul_mem ha'.2 hb'.2⟩

/-- Counting step of Lemma 2.8(3): if `K = H₁H₂` as sets then
`|H₁₃|·|H₂₃| ≤ |K ∩ H₃|·|H₁₂₃|`. -/
theorem card_inf_mul_card_inf_le [Finite G] {H₁ H₂ H₃ K : Subgroup G}
    (hK : (K : Set G) = (H₁ : Set G) * H₂) :
    Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₃) ≤
      Nat.card ↥(K ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) := by
  calc Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₃)
        ≤ Nat.card ((K ⊓ H₃ : Subgroup G) : Set G) * Nat.card ↥((H₁ ⊓ H₃) ⊓ (H₂ ⊓ H₃)) :=
          card_mul_card_le_of_mul_subset _ _ (inf_mul_inf_subset hK)
    _ ≤ Nat.card ↥(K ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) := by
          refine Nat.mul_le_mul_left _ (Subgroup.card_le_of_le ?_)
          intro x hx
          simp only [Subgroup.mem_inf] at hx ⊢
          tauto

/-- **Lemma 2.8(3)** of arXiv:2505.22565: if the set product `H₁H₂` is a subgroup
of the finite group `G`, then `(H₁, H₂, H₃, H₄)` satisfies the Ingleton
inequality. -/
theorem ingleton_of_mul_eq_subgroup [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (h : ∃ K : Subgroup G, (K : Set G) = (H₁ : Set G) * H₂) :
    Ingleton H₁ H₂ H₃ H₄ := by
  obtain ⟨K, hK⟩ := h
  have heqK : Nat.card K * Nat.card ↥(H₁ ⊓ H₂) = Nat.card H₁ * Nat.card H₂ := by
    rw [← card_mul_mul_card_inf H₁ H₂, ← hK]
    rfl
  have s3 := card_inf_mul_card_inf_le (H₃ := H₃) hK
  have s4 := card_inf_mul_card_inf_le (H₃ := H₄) hK
  have s34 : Nat.card ↥(K ⊓ H₃) * Nat.card ↥(K ⊓ H₄) ≤ Nat.card K * Nat.card ↥(H₃ ⊓ H₄) := by
    refine card_mul_card_le_card_mul_card inf_le_left inf_le_left ?_
    intro x hx
    simp only [Subgroup.mem_inf] at hx ⊢
    tauto
  unfold Ingleton
  refine Nat.le_of_mul_le_mul_left ?_ (card_subgroup_pos K)
  calc Nat.card K * (Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄))
        = (Nat.card K * Nat.card ↥(H₁ ⊓ H₂)) *
            (Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₃)) *
            (Nat.card ↥(H₁ ⊓ H₄) * Nat.card ↥(H₂ ⊓ H₄)) := by
          ring
      _ ≤ (Nat.card H₁ * Nat.card H₂) *
            (Nat.card ↥(K ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃)) *
            (Nat.card ↥(K ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) := by
          rw [heqK]
          exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl s3) s4
      _ = (Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) * (Nat.card ↥(K ⊓ H₃) * Nat.card ↥(K ⊓ H₄)) := by
          ring
      _ ≤ (Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) * (Nat.card K * Nat.card ↥(H₃ ⊓ H₄)) :=
          Nat.mul_le_mul_left _ s34
      _ = Nat.card K * (Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄)) := by
          ring

/-- **Lemma 2.8, consequence** (arXiv:2505.22565): if `H₁` is normal in the finite
group `G`, the Ingleton inequality holds for `(H₁, H₂, H₃, H₄)`. -/
theorem ingleton_of_normal_left [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G) [H₁.Normal] :
    Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_of_mul_eq_subgroup H₁ H₂ H₃ H₄ ⟨H₁ ⊔ H₂, Subgroup.normal_mul H₁ H₂⟩

/-- **Lemma 2.8, consequence** (arXiv:2505.22565): if `H₂` is normal in the finite
group `G`, the Ingleton inequality holds for `(H₁, H₂, H₃, H₄)`. -/
theorem ingleton_of_normal_right [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G) [H₂.Normal] :
    Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_of_mul_eq_subgroup H₁ H₂ H₃ H₄ ⟨H₁ ⊔ H₂, Subgroup.mul_normal H₁ H₂⟩

/-- **No abelian Ingleton violators** (Chan 2007; arXiv:2505.22565, Lemma 2.8,
consequence): every quadruple of subgroups of a finite commutative group
satisfies the Ingleton inequality. -/
theorem ingleton_of_commGroup {A : Type*} [CommGroup A] [Finite A]
    (H₁ H₂ H₃ H₄ : Subgroup A) : Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_of_normal_left H₁ H₂ H₃ H₄

/-- **Swap symmetry** (arXiv:2505.22565, before Lemma 2.8): the Ingleton
inequality is invariant under interchanging `H₁` and `H₂`. -/
theorem ingleton_swap_left [Finite G] {H₁ H₂ H₃ H₄ : Subgroup G}
    (h : Ingleton H₂ H₁ H₃ H₄) : Ingleton H₁ H₂ H₃ H₄ := by
  unfold Ingleton at h ⊢
  rw [inf_comm H₂ H₁] at h
  calc Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) *
          Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄)
        = Nat.card ↥(H₁ ⊓ H₂) * Nat.card ↥(H₂ ⊓ H₃) * Nat.card ↥(H₂ ⊓ H₄) *
            Nat.card ↥(H₁ ⊓ H₃) * Nat.card ↥(H₁ ⊓ H₄) := by
          ring
      _ ≤ Nat.card H₂ * Nat.card H₁ * Nat.card ↥(H₃ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) := h
      _ = Nat.card H₁ * Nat.card H₂ * Nat.card ↥(H₃ ⊓ H₄) * Nat.card ↥(H₁ ⊓ H₂ ⊓ H₃) *
            Nat.card ↥(H₁ ⊓ H₂ ⊓ H₄) := by
          ring

/-- In a finite cyclic group, an element `z` with `z ^ |S| = 1` lies in the
subgroup `S` (the elements of order dividing `|S|` number at most `|S|`). -/
theorem mem_of_pow_card_eq_one {X : Type*} [Group X] [Finite X] [IsCyclic X]
    (S : Subgroup X) {z : X} (hz : z ^ Nat.card S = 1) : z ∈ S := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  set F : Finset X := Finset.univ.filter (fun x : X => x ^ Nat.card S = 1) with hF
  have hsub : (S : Set X).toFinset ⊆ F := by
    intro x hx
    rw [Set.mem_toFinset, SetLike.mem_coe] at hx
    rw [hF, Finset.mem_filter]
    exact ⟨Finset.mem_univ x, congrArg Subtype.val (pow_card_eq_one' (G := S) (x := ⟨x, hx⟩))⟩
  have hle : F.card ≤ Nat.card S := IsCyclic.card_pow_eq_one_le Nat.card_pos
  have hcardS : (S : Set X).toFinset.card = Nat.card S := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have heq : (S : Set X).toFinset = F :=
    Finset.eq_of_subset_of_card_le hsub (hle.trans hcardS.ge)
  have hzF : z ∈ F := by
    rw [hF, Finset.mem_filter]
    exact ⟨Finset.mem_univ z, hz⟩
  rw [← heq, Set.mem_toFinset] at hzF
  exact hzF

/-- Relative form of `mem_of_pow_card_eq_one`: if `S ≤ H` with `H` cyclic, an
element `z ∈ H` with `z ^ |S| = 1` lies in `S`. -/
theorem mem_of_le_of_pow_card_eq_one [Finite G] {H S : Subgroup G}
    (hc : IsCyclic H) (hS : S ≤ H) {z : G} (hz : z ∈ H) (hpow : z ^ Nat.card S = 1) :
    z ∈ S := by
  have hcard : Nat.card (S.subgroupOf H) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have hz' : (⟨z, hz⟩ : H) ∈ S.subgroupOf H := by
    refine mem_of_pow_card_eq_one (S.subgroupOf H) ?_
    rw [hcard]
    exact Subtype.ext hpow
  exact Subgroup.mem_subgroupOf.mp hz'

/-- Distributivity step behind Corollary 2.7: inside a finite cyclic subgroup
`H`, every `y ∈ A ⊔ B` (with `A, B ≤ H`) splits as `y = yᵏ · yˡ` with `yᵏ ∈ A`
and `yˡ ∈ B`.  With `g = gcd(|A|, |B|)` and Bezout `u·|A|/g + v·|B|/g = 1`,
take `k = v·|B|/g`, `l = u·|A|/g`; then `y ^ (|A|·|B|/g) = 1`. -/
theorem exists_zpow_split [Finite G] {H A B : Subgroup G}
    (hc : IsCyclic H) (hA : A ≤ H) (hB : B ≤ H) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ k l : ℤ, y ^ k ∈ A ∧ y ^ l ∈ B ∧ y ^ k * y ^ l = y := by
  have hcomm : ∀ x ∈ H, ∀ w ∈ H, x * w = w * x := fun x hx w hw =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : H) ⟨w, hw⟩)
  set a := Nat.card A with ha
  set b := Nat.card B with hb
  set g := Nat.gcd a b with hg
  have hapos : 0 < a := Nat.card_pos
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b hapos
  set a' := a / g with ha'
  set b' := b / g with hb'
  have hcop : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hgpos
  have haa : a = g * a' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hbb : b = g * b' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  set N := a * b' with hN
  have hNb : N = b * a' := by rw [hN, haa, hbb]; ring
  let T : Subgroup G :=
    { carrier := {z | z ∈ H ∧ z ^ N = 1}
      mul_mem' := by
        rintro x w ⟨hx, hxN⟩ ⟨hw, hwN⟩
        refine ⟨H.mul_mem hx hw, ?_⟩
        rw [(Commute.mul_pow (hcomm x hx w hw) N), hxN, hwN, one_mul]
      one_mem' := ⟨H.one_mem, one_pow N⟩
      inv_mem' := by
        rintro x ⟨hx, hxN⟩
        exact ⟨H.inv_mem hx, by rw [inv_pow, hxN, inv_one]⟩ }
  have hAT : A ≤ T := by
    intro z hz
    refine ⟨hA hz, ?_⟩
    have h1 : z ^ a = 1 := congrArg Subtype.val (pow_card_eq_one' (G := A) (x := ⟨z, hz⟩))
    rw [hN, pow_mul, h1, one_pow]
  have hBT : B ≤ T := by
    intro z hz
    refine ⟨hB hz, ?_⟩
    have h1 : z ^ b = 1 := congrArg Subtype.val (pow_card_eq_one' (G := B) (x := ⟨z, hz⟩))
    rw [hNb, pow_mul, h1, one_pow]
  have hyT : y ∈ H ∧ y ^ N = 1 := sup_le hAT hBT hy
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨v * b', u * a', ?_, ?_, ?_⟩
  · refine mem_of_le_of_pow_card_eq_one hc hA (H.zpow_mem hyT.1 _) ?_
    rw [← ha, ← zpow_natCast, ← zpow_mul]
    have hexp : (v * (b' : ℤ)) * (a : ℤ) = (N : ℤ) * v := by rw [hN]; push_cast; ring
    rw [hexp, zpow_mul, zpow_natCast, hyT.2, one_zpow]
  · refine mem_of_le_of_pow_card_eq_one hc hB (H.zpow_mem hyT.1 _) ?_
    rw [← hb, ← zpow_natCast, ← zpow_mul]
    have hexp : (u * (a' : ℤ)) * (b : ℤ) = (N : ℤ) * u := by rw [hNb]; push_cast; ring
    rw [hexp, zpow_mul, zpow_natCast, hyT.2, one_zpow]
  · rw [← zpow_add, add_comm, huv, zpow_one]

/-- **Corollary 2.7** of arXiv:2505.22565 (`cor:H1notcyclic`), case `H₁`: if `H₁`
is cyclic, the quadruple `(H₁, H₂, H₃, H₄)` of subgroups of a finite group
satisfies the Ingleton inequality.  Route of the paper: reduce to
`H₁' = ⟨H₁₃, H₁₄⟩` (Lemma 2.4), then `H₁'₂ = H₁'₂₃ H₁'₂₄` by cyclicity and
Proposition 2.6 applies. -/
theorem ingleton_of_isCyclic_left [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (hc : IsCyclic H₁) : Ingleton H₁ H₂ H₃ H₄ := by
  apply ingleton_of_ingleton_sup_inf
  set H₁' : Subgroup G := (H₁ ⊓ H₃) ⊔ (H₁ ⊓ H₄) with hH₁'
  apply ingleton_of_inf_eq_mul
  apply Set.Subset.antisymm
  · intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hy
    obtain ⟨k, l, hk, hl, hkl⟩ := exists_zpow_split hc inf_le_left inf_le_left hy.1
    refine Set.mem_mul.mpr ⟨y ^ k, ?_, y ^ l, ?_, hkl⟩
    · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨H₁'.zpow_mem hy.1 k,
        H₂.zpow_mem hy.2 k⟩, (Subgroup.mem_inf.mp hk).2⟩
    · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨H₁'.zpow_mem hy.1 l,
        H₂.zpow_mem hy.2 l⟩, (Subgroup.mem_inf.mp hl).2⟩
  · refine Set.mul_subset_iff.mpr fun a ha b hb => ?_
    exact (H₁' ⊓ H₂).mul_mem (inf_le_left (α := Subgroup G) ha)
      (inf_le_left (α := Subgroup G) hb)

/-- **Corollary 2.7** of arXiv:2505.22565 (`cor:H1notcyclic`), case `H₂`: if `H₂`
is cyclic, the quadruple `(H₁, H₂, H₃, H₄)` of subgroups of a finite group
satisfies the Ingleton inequality. -/
theorem ingleton_of_isCyclic_right [Finite G] (H₁ H₂ H₃ H₄ : Subgroup G)
    (hc : IsCyclic H₂) : Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_swap_left (ingleton_of_isCyclic_left H₂ H₁ H₃ H₄ hc)

/-! Examples of the sufficient criteria. -/

/-- The hypothesis of Proposition 2.6 holds with `H₁ = ⊤`, `H₂ = ⊥`. -/
example (H₃ H₄ : Subgroup (Multiplicative (ZMod 6))) :
    (((⊤ ⊓ ⊥ : Subgroup (Multiplicative (ZMod 6)))) : Set (Multiplicative (ZMod 6))) =
      ((⊤ ⊓ ⊥ ⊓ H₃ : Subgroup (Multiplicative (ZMod 6))) : Set (Multiplicative (ZMod 6))) *
        ((⊤ ⊓ ⊥ ⊓ H₄ : Subgroup (Multiplicative (ZMod 6))) :
          Set (Multiplicative (ZMod 6))) := by
  rw [inf_bot_eq, bot_inf_eq, bot_inf_eq, Subgroup.coe_bot, Set.singleton_mul_singleton,
    mul_one]

/-- The hypothesis of Lemma 2.8(3) holds with `H₁ = H₂ = K = ⊤`. -/
example : ∃ K : Subgroup (Multiplicative (ZMod 6)),
    (K : Set (Multiplicative (ZMod 6))) =
      ((⊤ : Subgroup (Multiplicative (ZMod 6))) : Set (Multiplicative (ZMod 6))) *
        ((⊤ : Subgroup (Multiplicative (ZMod 6))) : Set (Multiplicative (ZMod 6))) :=
  ⟨⊤, by rw [Subgroup.coe_top, Set.univ_mul_univ]⟩

/-- The cyclic hypothesis of Corollary 2.7 holds for `⊤` in a cyclic group of order 6. -/
example : IsCyclic ↥(⊤ : Subgroup (Multiplicative (ZMod 6))) := inferInstance

/-- The commutative case applies to a nontrivial cyclic group of order 6. -/
example (H₁ H₂ H₃ H₄ : Subgroup (Multiplicative (ZMod 6))) : Ingleton H₁ H₂ H₃ H₄ :=
  ingleton_of_commGroup H₁ H₂ H₃ H₄

end Candidates.IngletonSufficientCriteria
