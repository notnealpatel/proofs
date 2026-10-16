import Combinatorics.PermutationEndpointOverlapTail
import Combinatorics.PermutationMixedEndpointBound
import Mathlib.Data.Fintype.CardEmbedding

set_option autoImplicit false

namespace PermutationEndpointBoundaryLower

open PermutationEndpointCounting PermutationMixedEndpointBound
open PermutationEndpointOverlapTail PermutationOverlapBound

attribute [local instance] Classical.propDecidable

private theorem exists_perm_mapping {A B : Type*} [Fintype A] [Fintype B]
    (a b : A ↪ B) : ∃ e : Equiv.Perm B, ∀ i, e (a i) = b i := by
  classical
  let e := (Equiv.ofInjective a a.injective).symm.trans (Equiv.ofInjective b b.injective)
  refine ⟨e.extendSubtype, ?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (a i) ⟨i, rfl⟩]
  change (e ⟨a i, _⟩).val = b i
  simp [e]

private theorem constant_fiber_card {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] (f : A → B)
    (hc : ∀ a b, Fintype.card {x // f x = a} = Fintype.card {x // f x = b})
    (P : B → Prop) :
    Fintype.card {x // P (f x)} * Fintype.card B =
      Fintype.card A * Fintype.card {b // P b} := by
  classical
  let b₀ := f (Classical.choice (inferInstance : Nonempty A))
  let c := Fintype.card {x // f x = b₀}
  have hfib (b : B) : Fintype.card {x // f x = b} = c := hc b b₀
  have hall : Fintype.card A = Fintype.card B * c := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  let e : (Σ b : {b // P b}, {x // f x = b.val}) ≃ {x // P (f x)} :=
    { toFun := fun x => ⟨x.2.val, x.2.property.symm ▸ x.1.property⟩
      invFun := fun x => ⟨⟨f x.val, x.property⟩, ⟨x.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨b, hb⟩, ⟨x, hx⟩⟩; cases hx; rfl
      right_inv := by intro x; rfl }
  have hsub : Fintype.card {x // P (f x)} = Fintype.card {b // P b} * c := by
    rw [← Fintype.card_congr e, Fintype.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hall, hsub]
  ring

private theorem remaining_value {n : ℕ} (p q m l : Fin n)
    (π : FixedTwo p q m l) (r : Fin n) (hp : r ≠ p) (hq : r ≠ q) :
    π.val r ≠ m ∧ π.val r ≠ l := by
  constructor
  · intro he
    exact hp (π.val.injective (he.trans π.property.1.symm))
  · intro he
    exact hq (π.val.injective (he.trans π.property.2.symm))

private noncomputable def restriction {n : ℕ} {D : Type*} (p q m l : Fin n)
    (d : D ↪ Fin n) (hp : ∀ i, d i ≠ p) (hq : ∀ i, d i ≠ q)
    (π : FixedTwo p q m l) : D ↪ {a : Fin n // a ≠ m ∧ a ≠ l} :=
  { toFun := fun i => ⟨π.val (d i), remaining_value p q m l π (d i) (hp i) (hq i)⟩
    inj' := by
      intro i j he
      exact d.injective (π.val.injective (congrArg Subtype.val he)) }

example {n : ℕ} {D : Type*} (p q m l : Fin n) (d : D ↪ Fin n)
    (hp : ∀ i, d i ≠ p) (hq : ∀ i, d i ≠ q) (π : FixedTwo p q m l) (i : D) :
    (restriction p q m l d hp hq π i).val = π.val (d i) := rfl

private theorem restriction_fibers {n : ℕ} {D : Type*} [Fintype D]
    (p q m l : Fin n) (d : D ↪ Fin n) (hp : ∀ i, d i ≠ p) (hq : ∀ i, d i ≠ q)
    (a b : D ↪ {a : Fin n // a ≠ m ∧ a ≠ l}) :
    Fintype.card {π // restriction p q m l d hp hq π = a} =
      Fintype.card {π // restriction p q m l d hp hq π = b} := by
  classical
  obtain ⟨e, he⟩ := exists_perm_mapping a b
  let σ : Equiv.Perm (Fin n) := e.subtypeCongr (Equiv.refl _)
  have hσm : σ m = m := by
    exact Equiv.Perm.subtypeCongr.right_apply e (Equiv.refl _) (by simp)
  have hσl : σ l = l := by
    exact Equiv.Perm.subtypeCongr.right_apply e (Equiv.refl _) (by simp)
  have hσa (i : D) : σ (a i).val = (b i).val := by
    change e.subtypeCongr (Equiv.refl _) (a i).val = _
    rw [Equiv.Perm.subtypeCongr.left_apply e (Equiv.refl _) (a i).property, he]
  let act (τ : Equiv.Perm (Fin n)) (hm : τ m = m) (hl : τ l = l)
      (π : FixedTwo p q m l) : FixedTwo p q m l :=
    ⟨π.val.trans τ, by
      constructor
      · change τ (π.val p) = m
        rw [π.property.1, hm]
      · change τ (π.val q) = l
        rw [π.property.2, hl]⟩
  have hσmi : σ.symm m = m := (σ.symm_apply_eq).2 hσm.symm
  have hσli : σ.symm l = l := (σ.symm_apply_eq).2 hσl.symm
  let f : {π // restriction p q m l d hp hq π = a} →
      {π // restriction p q m l d hp hq π = b} := fun π =>
    ⟨act σ hσm hσl π.val, by
      apply Function.Embedding.ext
      intro i
      apply Subtype.ext
      change σ (π.val.val (d i)) = (b i).val
      have hi := congrArg (fun z : D ↪ {a : Fin n // a ≠ m ∧ a ≠ l} => (z i).val) π.property
      change π.val.val (d i) = (a i).val at hi
      rw [hi, hσa]⟩
  let g : {π // restriction p q m l d hp hq π = b} →
      {π // restriction p q m l d hp hq π = a} := fun π =>
    ⟨act σ.symm hσmi hσli π.val, by
      apply Function.Embedding.ext
      intro i
      apply Subtype.ext
      change σ.symm (π.val.val (d i)) = (a i).val
      apply σ.injective
      rw [σ.apply_symm_apply, hσa]
      exact congrArg (fun z : D ↪ {a : Fin n // a ≠ m ∧ a ≠ l} => (z i).val) π.property⟩
  exact Fintype.card_congr
    { toFun := f
      invFun := g
      left_inv := by
        intro π
        apply Subtype.ext
        apply Subtype.ext
        apply Equiv.ext
        intro i
        exact σ.symm_apply_apply _
      right_inv := by
        intro π
        apply Subtype.ext
        apply Subtype.ext
        apply Equiv.ext
        intro i
        exact σ.apply_symm_apply _ }

set_option maxHeartbeats 800000 in
/-- Restriction to distinct unprescribed positions is uniformly distributed over
ordered injections into the remaining labels; no independence is assumed. -/
private theorem restriction_card {n : ℕ} {D : Type*} [Fintype D]
    (p q m l : Fin n) (hpq : p ≠ q) (hml : m ≠ l)
    (d : D ↪ Fin n) (hp : ∀ i, d i ≠ p) (hq : ∀ i, d i ≠ q)
    (P : (D ↪ {a : Fin n // a ≠ m ∧ a ≠ l}) → Prop) :
    Fintype.card {π : FixedTwo p q m l // P (restriction p q m l d hp hq π)} *
        (n - 2).descFactorial (Fintype.card D) =
      Fintype.card (FixedTwo p q m l) * Fintype.card {a // P a} := by
  classical
  letI : Nonempty (FixedTwo p q m l) := fixedTwo_nonempty p q m l hpq hml
  have hc : Fintype.card {a : Fin n // a ≠ m ∧ a ≠ l} = n - 2 := by
    rw [Fintype.card_of_subtype (Finset.univ \ {m, l}) (by simp)]
    simp [Finset.card_sdiff, hml]
  rw [← hc, ← Fintype.card_embedding_eq]
  apply constant_fiber_card (restriction p q m l d hp hq)
  intro a b
  simpa only [← Nat.card_eq_fintype_card] using restriction_fibers p q m l d hp hq a b

private theorem constrained_embedding_card {D A : Type*} [Fintype D] [Fintype A]
    (P : A → Prop) :
    Fintype.card {a : D ↪ A // ∀ i, P (a i)} =
      (Fintype.card {a // P a}).descFactorial (Fintype.card D) := by
  classical
  let e : {a : D ↪ A // ∀ i, P (a i)} ≃ (D ↪ {a // P a}) :=
    { toFun := fun a => ⟨fun i => ⟨a.val i, a.property i⟩, by
        intro i j he
        exact a.val.injective (congrArg Subtype.val he)⟩
      invFun := fun a => ⟨⟨fun i => (a i).val, by
        intro i j he
        exact a.injective (Subtype.ext he)⟩, fun i => (a i).property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq]

/-- Exact simultaneous label restrictions at any family of distinct positions
away from the fixed endpoints. -/
theorem prescribed_positions_card {n : ℕ} {D : Type*} [Fintype D]
    (p q m l : Fin n) (hpq : p ≠ q) (hml : m ≠ l)
    (d : D ↪ Fin n) (hp : ∀ i, d i ≠ p) (hq : ∀ i, d i ≠ q)
    (P : Fin n → Prop) :
    Fintype.card {π : FixedTwo p q m l // ∀ i, P (π.val (d i))} *
        (n - 2).descFactorial (Fintype.card D) =
      Fintype.card (FixedTwo p q m l) *
        (Fintype.card {a : {a : Fin n // a ≠ m ∧ a ≠ l} // P a.val}).descFactorial
          (Fintype.card D) := by
  classical
  have h := restriction_card p q m l hpq hml d hp hq (fun a => ∀ i, P (a i).val)
  have he : Fintype.card {a : D ↪ {a : Fin n // a ≠ m ∧ a ≠ l} // ∀ i, P (a i).val} =
      (Fintype.card {a : {a : Fin n // a ≠ m ∧ a ≠ l} // P a.val}).descFactorial
        (Fintype.card D) := by
    convert constrained_embedding_card (D := D)
      (fun a : {a : Fin n // a ≠ m ∧ a ≠ l} => P a.val) using 1
  simp only [← Nat.card_eq_fintype_card] at h he ⊢
  rw [he] at h
  exact h

/-- Ordered enumeration of the two disjoint interior boundary blocks, of total
size `2*K-4`, when `n ≥ 2*K-2` and `K ≥ 3`. -/
def boundaryEmbedding {n K : ℕ} (hK : 3 ≤ K) (hn : 2 * K - 2 ≤ n) :
    Fin (2 * K - 4) ↪ Fin n :=
  { toFun := fun i => ⟨if i.val < K - 2 then i.val + 1
      else n - K + 1 + (i.val - (K - 2)), by
        split_ifs <;> omega⟩
    inj' := by
      intro i j he
      have hv := congrArg Fin.val he
      dsimp at hv
      split_ifs at hv <;> apply Fin.ext <;> omega }

example : boundaryEmbedding (by decide : 3 ≤ 3) (by decide : 2 * 3 - 2 ≤ 4)
    (0 : Fin 2) = (1 : Fin 4) := rfl
example : boundaryEmbedding (by decide : 3 ≤ 3) (by decide : 2 * 3 - 2 ≤ 4)
    (1 : Fin 2) = (2 : Fin 4) := rfl

private theorem boundary_ne_zero {n K : ℕ} [NeZero n] (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (i : Fin (2 * K - 4)) :
    boundaryEmbedding hK hn i ≠ (0 : Fin n) := by
  intro he
  have hv := congrArg Fin.val he
  change (if i.val < K - 2 then i.val + 1 else n - K + 1 + (i.val - (K - 2))) = 0 at hv
  split_ifs at hv <;> omega

private theorem boundary_ne_last {n K : ℕ} (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q : Fin n) (hq : q.val + 1 = n)
    (i : Fin (2 * K - 4)) : boundaryEmbedding hK hn i ≠ q := by
  intro he
  have hv := congrArg Fin.val he
  change (if i.val < K - 2 then i.val + 1 else n - K + 1 + (i.val - (K - 2))) = q.val at hv
  split_ifs at hv <;> omega

private theorem boundary_covers {n K k : ℕ} (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (hk : 2 ≤ k) (hkK : k < K) :
    (∃ i, (boundaryEmbedding hK hn i).val = k - 1) ∧
      (∃ i, (boundaryEmbedding hK hn i).val = n - k) := by
  constructor
  · refine ⟨⟨k - 2, by omega⟩, ?_⟩
    change (if k - 2 < K - 2 then k - 2 + 1 else _) = k - 1
    rw [if_pos (by omega)]
    omega
  · refine ⟨⟨2 * K - k - 3, by omega⟩, ?_⟩
    change (if 2 * K - k - 3 < K - 2 then _ else _) = n - k
    rw [if_neg (by omega)]
    change n - K + 1 + (2 * K - k - 3 - (K - 2)) = n - k
    omega

private theorem remaining_pred_card {n : ℕ} (m l : Fin n) (P : Fin n → Prop)
    (hP : ∀ a, P a → a ≠ m ∧ a ≠ l) :
    Fintype.card {a : {a : Fin n // a ≠ m ∧ a ≠ l} // P a.val} =
      Fintype.card {a : Fin n // P a} := by
  classical
  exact Fintype.card_congr
    { toFun := fun a => ⟨a.val.val, a.property⟩
      invFun := fun a => ⟨⟨a.val, hP a.val a.property⟩, a.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }

private theorem upper_label_card {n : ℕ} (m l : Fin n) :
    Fintype.card {a : {a : Fin n // a ≠ m ∧ a ≠ l} // max m.val l.val < a.val.val} =
      n - 1 - max m.val l.val := by
  classical
  have hc := remaining_pred_card m l (fun a => max m.val l.val < a.val) (by
    intro a ha
    constructor <;> intro he <;> subst a <;> omega)
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc, Nat.card_eq_fintype_card]
  let M : Fin n := ⟨max m.val l.val, max_lt m.isLt l.isLt⟩
  rw [Fintype.card_of_subtype (Finset.Ioi M) (by
    intro a
    simp only [Finset.mem_Ioi, Fin.lt_def, M])]
  exact Fin.card_Ioi M

private theorem lower_label_card {n : ℕ} (m l : Fin n) :
    Fintype.card {a : {a : Fin n // a ≠ m ∧ a ≠ l} // a.val.val < min m.val l.val} =
      min m.val l.val := by
  classical
  have hc := remaining_pred_card m l (fun a => a.val < min m.val l.val) (by
    intro a ha
    constructor <;> intro he <;> subst a <;> omega)
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc, Nat.card_eq_fintype_card]
  let u : Fin n := ⟨min m.val l.val, lt_of_le_of_lt (min_le_left _ _) m.isLt⟩
  rw [Fintype.card_of_subtype (Finset.Iio u) (by
    intro a
    simp only [Finset.mem_Iio, Fin.lt_def, u])]
  exact Fin.card_Iio u

/-- Either all boundary labels exceed both anchors or all are below both anchors.
These are deterministic sufficient certificates, not independent coordinate events. -/
def BoundaryCertificate {n K : ℕ} [NeZero n] (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q m l : Fin n) (π : FixedTwo (0 : Fin n) q m l) : Prop :=
  (∀ i, max m.val l.val < (π.val (boundaryEmbedding hK hn i)).val) ∨
    (∀ i, (π.val (boundaryEmbedding hK hn i)).val < min m.val l.val)

example {n K : ℕ} [NeZero n] (hK : 3 ≤ K) (hn : 2 * K - 2 ≤ n)
    (q m l : Fin n) (π : FixedTwo (0 : Fin n) q m l) :
    BoundaryCertificate hK hn q m l π ↔
      (∀ i, max m.val l.val < (π.val (boundaryEmbedding hK hn i)).val) ∨
        (∀ i, (π.val (boundaryEmbedding hK hn i)).val < min m.val l.val) := Iff.rfl

/-- Each boundary certificate rules out every proper overlap of length below `K`. -/
theorem boundaryCertificate_not_overlap {n K : ℕ} [NeZero n] (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n)
    (π : FixedTwo (0 : Fin n) q m l) (hπ : BoundaryCertificate hK hn q m l π)
    (k : ℕ) (hk : 2 ≤ k) (hkK : k < K) (hkn : k < n) : ¬ Overlap hkn π.val := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := boundary_covers hK hn hk hkK
  intro hov
  have he0 : (⟨0, by omega⟩ : Fin n) = 0 := Fin.ext rfl
  have hea : (⟨k - 1, by omega⟩ : Fin n) = boundaryEmbedding hK hn a := Fin.ext ha.symm
  have heb : (⟨0 + (n - k), by omega⟩ : Fin n) = boundaryEmbedding hK hn b := by
    apply Fin.ext
    change 0 + (n - k) = (boundaryEmbedding hK hn b).val
    omega
  have heq : (⟨k - 1 + (n - k), by omega⟩ : Fin n) = q := by
    apply Fin.ext
    change k - 1 + (n - k) = q.val
    omega
  have hc := hov (⟨0, by omega⟩ : Fin k) (⟨k - 1, by omega⟩ : Fin k)
  change π.val ⟨0, by omega⟩ < π.val ⟨k - 1, by omega⟩ ↔
    π.val ⟨0 + (n - k), by omega⟩ < π.val ⟨k - 1 + (n - k), by omega⟩ at hc
  simp only [he0, hea, heb, heq, π.property.1, π.property.2] at hc
  rcases hπ with hhigh | hlow
  · have hma : m < π.val (boundaryEmbedding hK hn a) := by
      change m.val < _
      exact lt_of_le_of_lt (le_max_left _ _) (hhigh a)
    have hlb : l < π.val (boundaryEmbedding hK hn b) := by
      change l.val < _
      exact lt_of_le_of_lt (le_max_right _ _) (hhigh b)
    exact (not_lt_of_gt hlb) (hc.mp hma)
  · have ham : π.val (boundaryEmbedding hK hn a) < m := by
      change _ < m.val
      exact lt_of_lt_of_le (hlow a) (min_le_left _ _)
    have hbl : π.val (boundaryEmbedding hK hn b) < l := by
      change _ < l.val
      exact lt_of_lt_of_le (hlow b) (min_le_right _ _)
    exact (not_lt_of_gt ham) (hc.mpr hbl)

/-- The two disjoint boundary certificates have exactly the sum of the two
falling-factorial counts, cross-multiplied by the full restriction count. -/
theorem boundaryCertificate_card {n K : ℕ} [NeZero n] (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q : Fin n) (hq : q.val + 1 = n)
    (m l : Fin n) (hml : m ≠ l) :
    Fintype.card {π : FixedTwo (0 : Fin n) q m l // BoundaryCertificate hK hn q m l π} *
        (n - 2).descFactorial (2 * K - 4) =
      Fintype.card (FixedTwo (0 : Fin n) q m l) *
        ((n - 1 - max m.val l.val).descFactorial (2 * K - 4) +
          (min m.val l.val).descFactorial (2 * K - 4)) := by
  classical
  have hpq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = q.val at hv
    omega
  let A : FixedTwo (0 : Fin n) q m l → Prop :=
    fun π => ∀ i, max m.val l.val < (π.val (boundaryEmbedding hK hn i)).val
  let B : FixedTwo (0 : Fin n) q m l → Prop :=
    fun π => ∀ i, (π.val (boundaryEmbedding hK hn i)).val < min m.val l.val
  have hdis : Disjoint A B := by
    apply disjoint_iff.mpr
    funext π
    apply propext
    constructor
    · rintro ⟨hA, hB⟩
      let i : Fin (2 * K - 4) := ⟨0, by omega⟩
      have hAi := hA i
      have hBi := hB i
      change max m.val l.val < _ at hAi
      change _ < min m.val l.val at hBi
      omega
    · intro hf
      exact False.elim hf
  have hA := prescribed_positions_card 0 q m l hpq hml (boundaryEmbedding hK hn)
    (boundary_ne_zero hK hn) (boundary_ne_last hK hn q hq)
    (fun a => max m.val l.val < a.val)
  have hB := prescribed_positions_card 0 q m l hpq hml (boundaryEmbedding hK hn)
    (boundary_ne_zero hK hn) (boundary_ne_last hK hn q hq)
    (fun a => a.val < min m.val l.val)
  have hupper := upper_label_card m l
  have hlower := lower_label_card m l
  simp only [← Nat.card_eq_fintype_card] at hA hB hupper hlower
  simp only [hupper, Nat.card_fin] at hA
  simp only [hlower, Nat.card_fin] at hB
  have hunion := Fintype.card_subtype_or_disjoint A B hdis
  simp only [← Nat.card_eq_fintype_card] at hunion ⊢
  change Nat.card {π // A π ∨ B π} * _ = _
  rw [hunion, Nat.add_mul]
  change Nat.card {π // A π} * _ = _ at hA
  change Nat.card {π // B π} * _ = _ at hB
  rw [hA, hB, Nat.mul_add]

/-- Inside the actual endpoint fiber, a boundary-certified permutation which is
not an all-length avoider necessarily belongs to the actual long-overlap tail. -/
theorem boundaryCertificate_avoid_or_long {n K : ℕ} [NeZero n] (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n)
    (π : FixedTwo (0 : Fin n) q m l) (hπ : BoundaryCertificate hK hn q m l π) :
    (∀ (k : ℕ) (_hk : 2 ≤ k) (hkn : k < n), ¬ Overlap hkn π.val) ∨
      LongOverlapTwo K q m l π := by
  classical
  by_cases ha : ∀ (k : ℕ) (_hk : 2 ≤ k) (hkn : k < n), ¬ Overlap hkn π.val
  · exact Or.inl ha
  · right
    by_contra hlong
    apply ha
    intro k hk hkn hov
    by_cases hkK : k < K
    · exact boundaryCertificate_not_overlap hK hn q hq m l π hπ k hk hkK hkn hov
    · exact hlong ⟨k, by omega, hkn, hov⟩

private theorem certificate_card_le {n K : ℕ} [NeZero n] (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n) :
    Fintype.card {π : FixedTwo (0 : Fin n) q m l // BoundaryCertificate hK hn q m l π} ≤
      Fintype.card (AvoidTwo q m l) + (longOverlapTwoFinset K q m l).card := by
  classical
  let A : FixedTwo (0 : Fin n) q m l → Prop :=
    fun π => ∀ (k : ℕ) (_hk : 2 ≤ k) (hkn : k < n), ¬ Overlap hkn π.val
  let B : FixedTwo (0 : Fin n) q m l → Prop := LongOverlapTwo K q m l
  let inclusion : {π : FixedTwo (0 : Fin n) q m l // BoundaryCertificate hK hn q m l π} →
      {π // A π ∨ B π} := fun π =>
    ⟨π.val, boundaryCertificate_avoid_or_long hK hn q hq m l π.val π.property⟩
  have hinj : Function.Injective inclusion := by
    intro π ρ he
    apply Subtype.ext
    exact congrArg (fun x : {π // A π ∨ B π} => x.val) he
  have hc := (Fintype.card_le_of_injective inclusion hinj).trans (Fintype.card_subtype_or A B)
  let eA : {π // A π} ≃ AvoidTwo q m l :=
    { toFun := fun π => ⟨π.val.val, π.val.property, π.property⟩
      invFun := fun π => ⟨⟨π.val, π.property.1⟩, π.property.2⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  let eB : {π // B π} ≃ ↥(longOverlapTwoFinset K q m l) :=
    { toFun := fun π => ⟨π.val, (mem_longOverlapTwoFinset K q m l π.val).mpr π.property⟩
      invFun := fun π => ⟨π.val, (mem_longOverlapTwoFinset K q m l π.val).mp π.property⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  have hA := Fintype.card_congr eA
  have hB := (Fintype.card_congr eB).trans (Fintype.card_coe _)
  simp only [← Nat.card_eq_fintype_card] at hc hA hB ⊢
  rwa [hA, hB] at hc

/-- The actual all-length avoidance fraction in a distinct-endpoint fiber is at
least the sum of the upper and lower boundary certificate fractions, less the
actual uniform long-overlap tail majorant. All factorials are falling factorials
except the tail's ordinary factorial; boundary-zero numerators are included. -/
theorem avoidTwo_fraction_lower {n : ℕ} [NeZero n] (K : ℕ) (hK : 3 ≤ K)
    (hn : 2 * K - 2 ≤ n) (q : Fin n) (hq : q.val + 1 = n)
    (m l : Fin n) (hml : m ≠ l) :
    let s := 2 * K - 4
    let M := max m.val l.val
    let u := min m.val l.val
    ((n - 1 - M).descFactorial s : ℝ) / (n - 2).descFactorial s +
        ((u.descFactorial s : ℝ) / (n - 2).descFactorial s) -
        6 / (K / 3).factorial ≤
      (Fintype.card (AvoidTwo q m l) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q m l) := by
  classical
  dsimp only
  have hn3 : 3 ≤ n := by omega
  have hpq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l hpq hml
  have hF : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FixedTwo (0 : Fin n) q m l))
  have hD : (0 : ℝ) < (n - 2).descFactorial (2 * K - 4) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : 2 * K - 4 ≤ n - 2))
  have hid :
      (Fintype.card {π : FixedTwo (0 : Fin n) q m l // BoundaryCertificate hK hn q m l π} : ℝ) *
          (n - 2).descFactorial (2 * K - 4) =
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) *
          (((n - 1 - max m.val l.val).descFactorial (2 * K - 4) : ℝ) +
            (min m.val l.val).descFactorial (2 * K - 4)) := by
    exact_mod_cast boundaryCertificate_card hK hn q hq m l hml
  have heq :
      (Fintype.card {π : FixedTwo (0 : Fin n) q m l // BoundaryCertificate hK hn q m l π} : ℝ) /
          Fintype.card (FixedTwo (0 : Fin n) q m l) =
        ((n - 1 - max m.val l.val).descFactorial (2 * K - 4) : ℝ) /
            (n - 2).descFactorial (2 * K - 4) +
          ((min m.val l.val).descFactorial (2 * K - 4) : ℝ) /
            (n - 2).descFactorial (2 * K - 4) := by
    rw [← add_div]
    apply (div_eq_div_iff hF.ne' hD.ne').mpr
    simpa only [mul_comm] using hid
  have hc :
      (Fintype.card {π : FixedTwo (0 : Fin n) q m l // BoundaryCertificate hK hn q m l π} : ℝ) /
          Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
        (Fintype.card (AvoidTwo q m l) : ℝ) / Fintype.card (FixedTwo (0 : Fin n) q m l) +
          ((longOverlapTwoFinset K q m l).card : ℝ) /
            Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hF.le
    exact_mod_cast certificate_card_le hK hn q hq m l
  have htail := longOverlapTwo_fraction_le hn3 K hK q hq m l hml
  rw [heq] at hc
  linarith

example : 3 ≤ (3 : ℕ) ∧ 2 * 3 - 2 ≤ (4 : ℕ) ∧
    (3 : Fin 4).val + 1 = 4 ∧ (0 : Fin 4) ≠ 1 ∧
    Nonempty (FixedTwo (0 : Fin 4) 3 0 1) :=
  ⟨by decide, by decide, rfl, by decide,
    fixedTwo_nonempty 0 3 0 1 (by decide) (by decide)⟩

example : ∃ π : FixedTwo (0 : Fin 4) 3 0 1,
    BoundaryCertificate (by decide : 3 ≤ 3) (by decide : 2 * 3 - 2 ≤ 4) 3 0 1 π := by
  let π : FixedTwo (0 : Fin 4) 3 0 1 := ⟨Equiv.swap 1 3, by decide, by decide⟩
  refine ⟨π, Or.inl ?_⟩
  intro i
  fin_cases i <;> decide

end PermutationEndpointBoundaryLower
