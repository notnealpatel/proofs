import Combinatorics.PermutationSameEdgeLimit

set_option autoImplicit false

namespace PermutationEndpointZeroTwoExact

open PermutationOrderCounting PermutationEndpointCounting PermutationOverlapBound
open PermutationMixedEndpointBound

section

attribute [local instance] Classical.propDecidable

/-- Actual permutations with three prescribed position/label equations. -/
abbrev FixedThree {n : ℕ} (p q r m l v : Fin n) :=
  {π : Equiv.Perm (Fin n) // (π p = m ∧ π q = l) ∧ π r = v}

/-- Actual three-anchor permutations with matching orders on two blocks. -/
abbrev AgreementThree {n t : ℕ} (p q r m l v : Fin n) (a b : Fin t ↪ Fin n) :=
  {π : Equiv.Perm (Fin n) // ((π p = m ∧ π q = l) ∧ π r = v) ∧ SameOrder π a b}

example : Nonempty (FixedThree (0 : Fin 3) 2 1 0 2 1) :=
  ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, rfl⟩⟩

example : Nonempty (AgreementThree (0 : Fin 3) 2 1 0 2 1
    (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 3) Function.Embedding.ofIsEmpty) :=
  ⟨⟨Equiv.refl _, ⟨⟨rfl, rfl⟩, rfl⟩, by intro i; exact Fin.elim0 i⟩⟩

/-- Restrict the actual supported shuffle bijection to a third fixed label. -/
theorem card_agreementThree_mul_factorial {n t : ℕ} (p q r m l v : Fin n)
    (a b : Fin t ↪ Fin n) (hp : p ∉ Set.range a) (hq : q ∉ Set.range a)
    (hr : r ∉ Set.range a) (hab : Disjoint (Set.range a) (Set.range b)) :
    Fintype.card (AgreementThree p q r m l v a b) * Nat.factorial t =
      Fintype.card (FixedThree p q r m l v) := by
  let f : AgreementThree p q r m l v a b × Equiv.Perm (Fin t) →
      FixedThree p q r m l v := fun x =>
    ⟨(blockPerm a x.2).trans x.1.val, by
      simpa only [Equiv.trans_apply, blockPerm_apply_of_notMem a x.2 p hp,
        blockPerm_apply_of_notMem a x.2 q hq, blockPerm_apply_of_notMem a x.2 r hr]
        using x.1.property.1⟩
  have hbij := shuffleAgreementTwo_bijective p q m l a b hp hq hab
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨π, σ⟩ ⟨ρ, τ⟩ he
      have he' : shuffleAgreementTwo p q m l a b hp hq
          (⟨π.val, π.property.1.1, π.property.2⟩, σ) =
          shuffleAgreementTwo p q m l a b hp hq
          (⟨ρ.val, ρ.property.1.1, ρ.property.2⟩, τ) := by
        apply Subtype.ext
        exact congrArg (fun x : FixedThree p q r m l v => x.val) he
      have hi := hbij.1 he'
      exact Prod.ext (Subtype.ext (congrArg (fun x => x.1.val) hi))
        (congrArg (fun x : AgreementTwo p q m l a b × Equiv.Perm (Fin t) => x.2) hi)
    · intro γ
      obtain ⟨⟨π, σ⟩, he⟩ := hbij.2 ⟨γ.val, γ.property.1⟩
      have hr' : π.val r = v := by
        have hval := congrArg (fun x : FixedTwo p q m l => x.val r) he
        change π.val (blockPerm a σ r) = γ.val r at hval
        rw [blockPerm_apply_of_notMem a σ r hr] at hval
        exact hval.trans γ.property.2
      refine ⟨(⟨π.val, ⟨π.property.1, hr'⟩, π.property.2⟩, σ), ?_⟩
      apply Subtype.ext
      exact congrArg (fun x : FixedTwo p q m l => x.val) he
  simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
    using Fintype.card_of_bijective hf

/-- Fixing one remaining label at an interior position has exactly mass `1/(n-2)`.
This follows from the actual label-exchange bijection, not independence. -/
theorem card_fixedThree_mul {n : ℕ} (p q r m l v : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q) (hml : m ≠ l) (hvm : v ≠ m) (hvl : v ≠ l) :
    Fintype.card (FixedThree p q r m l v) * (n - 2) =
      Fintype.card (FixedTwo p q m l) := by
  classical
  have hc := marginal_card p q r m l hrp hrq (fun a => a = v)
  have hrem : Fintype.card {a : Fin n // a ≠ m ∧ a ≠ l} = n - 2 := by
    rw [Fintype.card_of_subtype (Finset.univ \ {m, l}) (by simp)]
    simp [Finset.card_sdiff, hml]
  have hv : Fintype.card {a : Fin n // (a ≠ m ∧ a ≠ l) ∧ a = v} = 1 := by
    rw [Fintype.card_of_subtype {v} (by intro a; simp; aesop)]
    simp
  have he : Fintype.card (FixedThree p q r m l v) =
      Fintype.card {π : FixedTwo p q m l // π.val r = v} := by
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨⟨π.val, π.property.1⟩, π.property.2⟩
      invFun := fun π => ⟨π.val.val, π.val.property, π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [← Nat.card_eq_fintype_card] at hc hrem hv he ⊢
  rw [hrem, hv, mul_one, ← he] at hc
  exact hc

/-- The length-`t` consecutive position block starting at `s`. -/
def segment {n : ℕ} (s t : ℕ) (h : s + t ≤ n) : Fin t ↪ Fin n :=
  ⟨fun i => ⟨i.val + s, by omega⟩, by
    intro i j he
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val he))⟩

example : (segment (n := 5) 2 3 (by decide) 1).val = 3 := rfl
example : Set.range (segment (n := 3) 0 0 (by decide)) = ∅ := by simp [segment]

/-- Removing a first coordinate which is minimal in each list preserves precisely
all the remaining comparison requirements. -/
theorem comparisons_iff_succ {n t : ℕ} (f g : Fin (t + 1) → Fin n)
    (hf : ∀ i : Fin t, f 0 < f i.succ) (hg : ∀ i : Fin t, g 0 < g i.succ) :
    (∀ i j, f i < f j ↔ g i < g j) ↔
      ∀ i j : Fin t, f i.succ < f j.succ ↔ g i.succ < g j.succ := by
  constructor
  · intro h i j
    exact h i.succ j.succ
  · intro h i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · exact iff_of_true (hf j) (hg j)
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact iff_of_false (not_lt_of_gt (hf i)) (not_lt_of_gt (hg i))
      · exact h i j

/-- Overlap is the adopted same-order notion on the actual prefix and suffix. -/
theorem overlap_iff_segments {n k : ℕ} (hkn : k < n) (π : Equiv.Perm (Fin n)) :
    Overlap hkn π ↔ SameOrder π (segment 0 k (by omega))
      (segment (n - k) k (by omega)) := by
  change (∀ i j : Fin k, _ ↔ _) ↔ (∀ i j : Fin k, _ ↔ _)
  rfl

/-- Labels at positions other than a prescribed zero position are positive. -/
theorem label_pos {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (h0 : π 0 = 0)
    (p : Fin n) (hp : p ≠ 0) : 0 < (π p).val := by
  have he : π p ≠ 0 := by
    intro he
    exact hp (π.injective (he.trans h0.symm))
  have hv : (π p).val ≠ 0 := by
    intro hv
    exact he (Fin.ext hv)
  omega

/-- In a zero/two endpoint overlap, the first suffix label is forced to be one. -/
theorem overlap_forces_one {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (π : Equiv.Perm (Fin n))
    (h0 : π 0 = 0) (h2 : π ⟨n - 1, by omega⟩ = ⟨2, by omega⟩)
    (hov : Overlap hkn π) : π ⟨n - k, by omega⟩ = ⟨1, by omega⟩ := by
  have hlast : 0 < (π ⟨k - 1, by omega⟩).val :=
    label_pos π h0 _ (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_zero] at hv; omega)
  have hc := (hov ⟨0, by omega⟩ ⟨k - 1, by omega⟩).mp
    (show π ⟨0, by omega⟩ < π ⟨k - 1, by omega⟩ by
      have hz : (⟨0, by omega⟩ : Fin n) = 0 := rfl
      rw [hz, h0]
      exact hlast)
  have hend : (⟨k - 1 + (n - k), by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    change k - 1 + (n - k) = n - 1
    omega
  simp only [Nat.zero_add] at hc
  rw [hend, h2] at hc
  have hpos := label_pos π h0 (⟨n - k, by omega⟩ : Fin n)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_zero] at hv; omega)
  apply Fin.ext
  have hc' : (π ⟨n - k, by omega⟩).val < 2 := hc
  change (π ⟨n - k, by omega⟩).val = 1
  omega

/-- A label away from the positions carrying zero and one exceeds one. -/
theorem label_one_lt {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (π : Equiv.Perm (Fin n)) (h0 : π 0 = 0) (r : Fin n)
    (h1 : π r = ⟨1, by omega⟩) (p : Fin n) (hp0 : p ≠ 0) (hpr : p ≠ r) :
    1 < (π p).val := by
  have hpos := label_pos π h0 p hp0
  have hne : (π p).val ≠ 1 := by
    intro he
    exact hpr (π.injective ((Fin.ext he).trans h1.symm))
  omega

/-- Once the suffix begins with one, deleting the two minimum first coordinates
is exactly equivalent to full prefix/suffix agreement. -/
theorem overlap_iff_tail_of_one {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (π : Equiv.Perm (Fin n)) (h0 : π 0 = 0)
    (h1 : π ⟨n - k, by omega⟩ = ⟨1, by omega⟩) :
    Overlap hkn π ↔ SameOrder π (segment 1 (k - 1) (by omega))
      (segment (n - k + 1) (k - 1) (by omega)) := by
  cases k with
  | zero => omega
  | succ t =>
    let f : Fin (t + 1) → Fin n := fun i => π ⟨i.val, by omega⟩
    let g : Fin (t + 1) → Fin n := fun i => π ⟨i.val + (n - (t + 1)), by omega⟩
    have hf : ∀ i : Fin t, f 0 < f i.succ := by
      intro i
      change π 0 < π ⟨i.val + 1, by omega⟩
      rw [h0]
      exact label_pos π h0 _ (by
        intro he
        have hv := congrArg Fin.val he
        simp at hv)
    have hg : ∀ i : Fin t, g 0 < g i.succ := by
      intro i
      dsimp only [g]
      simp only [Fin.val_zero, Nat.zero_add, Fin.val_succ]
      rw [h1]
      exact label_one_lt (by omega) π h0 _ h1 _
        (by intro he; have hv := congrArg Fin.val he; simp at hv)
        (by intro he; have hv := congrArg Fin.val he; simp at hv)
    have hc := comparisons_iff_succ f g hf hg
    convert hc using 1
    · rfl
    · simp only [SameOrder, segment, Function.Embedding.coeFn_mk, f, g,
        Fin.val_succ, Nat.add_assoc, Nat.add_comm]
      rfl

/-- Distinct overlap lengths are disjoint, since each determines the position of one. -/
theorem overlap_length_unique {n k j : ℕ} [NeZero n] (hn : 3 ≤ n)
    (hk : 2 ≤ k) (hkn : k < n) (hj : 2 ≤ j) (hjn : j < n)
    (π : Equiv.Perm (Fin n)) (h0 : π 0 = 0)
    (h2 : π ⟨n - 1, by omega⟩ = ⟨2, by omega⟩)
    (hkov : Overlap hkn π) (hjov : Overlap hjn π) : k = j := by
  have he := π.injective ((overlap_forces_one hn hk hkn π h0 h2 hkov).trans
    (overlap_forces_one hn hj hjn π h0 h2 hjov).symm)
  have hv := congrArg Fin.val he
  change n - k = n - j at hv
  omega

/-- A long overlap must have precisely one shared coordinate, carrying label one. -/
theorem long_overlap_size {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (hlong : n < 2 * k) (π : Equiv.Perm (Fin n))
    (h0 : π 0 = 0) (h2 : π ⟨n - 1, by omega⟩ = ⟨2, by omega⟩)
    (hov : Overlap hkn π) : n = 2 * k - 1 := by
  have h1 := overlap_forces_one hn hk hkn π h0 h2 hov
  by_contra hsize
  have hlastne : (⟨k - 1, by omega⟩ : Fin n) ≠ ⟨n - k, by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    change k - 1 = n - k at hv
    omega
  have hlast := label_one_lt (by omega) π h0 _ h1 (⟨k - 1, by omega⟩ : Fin n)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_zero] at hv; omega) hlastne
  have hc := (hov ⟨n - k, by omega⟩ ⟨k - 1, by omega⟩).mp
    (show π ⟨n - k, by omega⟩ < π ⟨k - 1, by omega⟩ by rw [h1]; exact hlast)
  have hend : (⟨k - 1 + (n - k), by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    change k - 1 + (n - k) = n - 1
    omega
  rw [hend, h2] at hc
  have hbig := label_one_lt (by omega) π h0 _ h1
    (⟨n - k + (n - k), by omega⟩ : Fin n)
    (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_zero] at hv; omega)
    (by intro he; have hv := congrArg Fin.val he
        change n - k + (n - k) = n - k at hv
        omega)
  have hc' : (π ⟨n - k + (n - k), by omega⟩).val < 2 := hc
  omega

/-- A last coordinate which is minimal in both lists may be deleted. -/
theorem comparisons_iff_castSucc {n t : ℕ} (f g : Fin (t + 1) → Fin n)
    (hf : ∀ i : Fin t, f (Fin.last t) < f i.castSucc)
    (hg : ∀ i : Fin t, g (Fin.last t) < g i.castSucc) :
    (∀ i j, f i < f j ↔ g i < g j) ↔
      ∀ i j : Fin t, f i.castSucc < f j.castSucc ↔ g i.castSucc < g j.castSucc := by
  constructor
  · intro h i j
    exact h i.castSucc j.castSucc
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · exact iff_of_true (hf j) (hg j)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · exact iff_of_false (not_lt_of_gt (hf i)) (not_lt_of_gt (hg i))
      · exact h i j

/-- Every label away from the positions carrying zero, one and two exceeds two. -/
theorem label_two_lt {n : ℕ} [NeZero n] (hn : 3 ≤ n) (π : Equiv.Perm (Fin n))
    (h0 : π 0 = 0) (r q : Fin n) (h1 : π r = ⟨1, by omega⟩)
    (h2 : π q = ⟨2, by omega⟩) (p : Fin n)
    (hp0 : p ≠ 0) (hpr : p ≠ r) (hpq : p ≠ q) : 2 < (π p).val := by
  have hgt := label_one_lt (by omega) π h0 r h1 p hp0 hpr
  have hne : (π p).val ≠ 2 := by
    intro he
    exact hpq (π.injective ((Fin.ext he).trans h2.symm))
  omega

/-- For the exceptional odd overlap, only the two disjoint middles must match
once their common center has label one. -/
theorem overlap_iff_middle_of_one {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (hsize : n = 2 * k - 1) (π : Equiv.Perm (Fin n))
    (h0 : π 0 = 0) (h1 : π ⟨n - k, by omega⟩ = ⟨1, by omega⟩)
    (h2 : π ⟨n - 1, by omega⟩ = ⟨2, by omega⟩) :
    Overlap hkn π ↔ SameOrder π (segment 1 (k - 2) (by omega))
      (segment (n - k + 1) (k - 2) (by omega)) := by
  rw [overlap_iff_tail_of_one hn hk hkn π h0 h1]
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
  have hcenter : n - (t + 2) = t + 1 := by omega
  let f : Fin (t + 1) → Fin n := fun i => π ⟨i.val + 1, by omega⟩
  let g : Fin (t + 1) → Fin n := fun i => π ⟨i.val + (n - (t + 2) + 1), by omega⟩
  have hf : ∀ i : Fin t, f (Fin.last t) < f i.castSucc := by
    intro i
    have hfend : f (Fin.last t) = ⟨1, by omega⟩ := by
      change π ⟨t + 1, by omega⟩ = _
      simpa only [hcenter] using h1
    rw [hfend]
    exact label_one_lt (by omega) π h0 _ h1 _
      (by intro he; have hv := congrArg Fin.val he; simp at hv)
      (by intro he; have hv := congrArg Fin.val he
          change i.val + 1 = n - (t + 2) at hv; omega)
  have hg : ∀ i : Fin t, g (Fin.last t) < g i.castSucc := by
    intro i
    have hgend : g (Fin.last t) = ⟨2, by omega⟩ := by
      have he : (⟨t + (n - (t + 2) + 1), by omega⟩ : Fin n) =
          ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        change t + (n - (t + 2) + 1) = n - 1
        omega
      change π ⟨t + (n - (t + 2) + 1), by omega⟩ = _
      rw [he, h2]
    rw [hgend]
    exact label_two_lt hn π h0 _ _ h1 h2 _
      (by intro he; have hv := congrArg Fin.val he
          change i.val + (n - (t + 2) + 1) = 0 at hv; omega)
      (by intro he; have hv := congrArg Fin.val he
          change i.val + (n - (t + 2) + 1) = n - (t + 2) at hv; omega)
      (by intro he; have hv := congrArg Fin.val he
          change i.val + (n - (t + 2) + 1) = n - 1 at hv; omega)
  have hc := comparisons_iff_castSucc f g hf hg
  convert hc using 1 <;>
    simp only [SameOrder, segment, f, g, Fin.val_castSucc] <;> rfl

/-- Translating an event into a supported three-anchor agreement gives its exact
cross-multiplied count in the original two-endpoint fiber. -/
theorem card_event_of_blocks {n k t : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (a b : Fin t ↪ Fin n)
    (ha0 : (0 : Fin n) ∉ Set.range a)
    (haq : (⟨n - 1, by omega⟩ : Fin n) ∉ Set.range a)
    (har : (⟨n - k, by omega⟩ : Fin n) ∉ Set.range a)
    (hab : Disjoint (Set.range a) (Set.range b))
    (hbridge : ∀ π : Equiv.Perm (Fin n), π 0 = 0 →
      π ⟨n - 1, by omega⟩ = ⟨2, by omega⟩ →
      π ⟨n - k, by omega⟩ = ⟨1, by omega⟩ →
      (Overlap hkn π ↔ SameOrder π a b)) :
    Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn
      (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) * Nat.factorial t * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
  have he : Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn
      (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) =
      Fintype.card (AgreementThree (0 : Fin n) ⟨n - 1, by omega⟩
        ⟨n - k, by omega⟩ 0 ⟨2, by omega⟩ ⟨1, by omega⟩ a b) := by
    apply Fintype.card_congr
    refine {
      toFun := fun π => ⟨π.val, ⟨π.property.1,
        overlap_forces_one hn hk hkn π.val π.property.1.1 π.property.1.2 π.property.2⟩,
        (hbridge π.val π.property.1.1 π.property.1.2
          (overlap_forces_one hn hk hkn π.val π.property.1.1 π.property.1.2 π.property.2)).mp
          π.property.2⟩
      invFun := fun π => ⟨π.val, π.property.1.1,
        (hbridge π.val π.property.1.1.1 π.property.1.1.2 π.property.1.2).mpr π.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he, card_agreementThree_mul_factorial _ _ _ _ _ _ a b ha0 haq har hab]
  apply card_fixedThree_mul
  · intro he
    have hv := congrArg Fin.val he
    simp at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    change n - k = n - 1 at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    simp at hv
  · intro he
    have hv := congrArg Fin.val he
    simp at hv
  · intro he
    have hv := congrArg Fin.val he
    simp at hv

/-- Exact short-overlap count: shuffle the entire prefix tail against the suffix
tail, including the forced minimum at its final coordinate. -/
theorem card_short_event {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (hshort : 2 * k ≤ n) :
    Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn
      (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) * Nat.factorial (k - 1) * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
  apply card_event_of_blocks hn hk hkn
    (segment 1 (k - 1) (by omega)) (segment (n - k + 1) (k - 1) (by omega))
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = 0 at hv
    omega
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - 1 at hv
    omega
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - k at hv
    omega
  · apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + (n - k + 1) = i.val + 1 at hv
    omega
  · intro π h0 _ h1
    exact overlap_iff_tail_of_one hn hk hkn π h0 h1

/-- Exact exceptional-overlap count: shuffle the two disjoint middles. This also
covers `n = 3`, when those middles are empty and their factorial is one. -/
theorem card_exceptional_event {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (hsize : n = 2 * k - 1) :
    Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn
      (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) * Nat.factorial (k - 2) * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
  apply card_event_of_blocks hn hk hkn
    (segment 1 (k - 2) (by omega)) (segment (n - k + 1) (k - 2) (by omega))
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = 0 at hv
    omega
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - 1 at hv
    omega
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - k at hv
    omega
  · apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + (n - k + 1) = i.val + 1 at hv
    omega
  · intro π h0 h2 h1
    exact overlap_iff_middle_of_one hn hk hkn hsize π h0 h1 h2

/-- The actual endpoint-zero/two overlap event at length `k`, viewed as a finset
inside its original two-anchor fiber. -/
noncomputable def eventFinset {n : ℕ} [NeZero n] (hn : 3 ≤ n) (k : ℕ) :
    Finset (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) :=
  Finset.univ.filter (fun π => ∃ hkn : k < n, Overlap hkn π.val)

/-- Membership uses the actual adopted overlap comparisons, with no replacement
probability space. -/
theorem mem_eventFinset {n : ℕ} [NeZero n] (hn : 3 ≤ n) (k : ℕ)
    (π : FixedTwo (0 : Fin n) ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.zero_lt_one⟩
      0 ⟨2, lt_of_lt_of_le (by decide : 2 < 3) hn⟩) :
    π ∈ eventFinset hn k ↔ ∃ hkn : k < n, Overlap hkn π.val := by
  simp [eventFinset]

/-- The finset event has precisely the cardinality of the adopted actual event subtype. -/
theorem card_eventFinset {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hkn : k < n) :
    (eventFinset hn k).card = Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn
      (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) := by
  classical
  rw [← Fintype.card_coe (eventFinset hn k)]
  apply Fintype.card_congr
  refine {
    toFun := fun π => ⟨π.val.val, π.val.property, (mem_eventFinset hn k π.val).mp π.property |>.choose_spec⟩
    invFun := fun π => ⟨⟨π.val, π.property.1⟩,
      (mem_eventFinset hn k _).mpr ⟨hkn, π.property.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Non-short and non-exceptional overlap events are empty. -/
theorem eventFinset_eq_empty {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k < n) (hlong : n < 2 * k) (hsize : n ≠ 2 * k - 1) :
    eventFinset hn k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro π hπ
  obtain ⟨_, hov⟩ := (mem_eventFinset hn k π).mp hπ
  exact hsize (long_overlap_size hn hk hkn hlong π.val π.property.1 π.property.2 hov)

/-- The full actual failure fraction is the sum of the disjoint actual overlap
fractions. No union bound replaces this equality. -/
theorem one_sub_F_eq_event_sum {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    1 - PermutationSameEdgeLimit.F n 0 2 =
      ∑ k ∈ Finset.Icc 2 (n - 1), (eventFinset hn k).card /
        (Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) : ℝ) := by
  classical
  let S := Finset.Icc 2 (n - 1)
  let B := S.biUnion (eventFinset hn)
  have hB : Fintype.card {π : FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩ //
      ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, Overlap hkn π.val} = B.card := by
    rw [← Fintype.card_coe B]
    apply Fintype.card_congr
    refine {
      toFun := fun π => ⟨π.val, ?_⟩
      invFun := fun π => ⟨π.val, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    · obtain ⟨k, hk, hkn, hov⟩ := π.property
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk, by omega⟩,
        (mem_eventFinset hn k _).mpr ⟨hkn, hov⟩⟩
    · obtain ⟨k, hk, hπ⟩ := Finset.mem_biUnion.mp π.property
      obtain ⟨hkn, hov⟩ := (mem_eventFinset hn k π.val).mp hπ
      exact ⟨k, (Finset.mem_Icc.mp hk).1, hkn, hov⟩
  have hd : (S : Set ℕ).PairwiseDisjoint (eventFinset hn) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro π hiπ hjπ
    obtain ⟨hin, hiov⟩ := (mem_eventFinset hn i π).mp hiπ
    obtain ⟨hjn, hjov⟩ := (mem_eventFinset hn j π).mp hjπ
    exact hij (overlap_length_unique hn (Finset.mem_Icc.mp hi).1 hin
      (Finset.mem_Icc.mp hj).1 hjn π.val π.property.1 π.property.2 hiov hjov)
  have hsum : B.card = ∑ k ∈ S, (eventFinset hn k).card := Finset.card_biUnion hd
  have hc := PermutationSameEdgeAvoidance.card_avoidTwo_add_card_overlap
    (⟨n - 1, by omega⟩ : Fin n) (0 : Fin n) ⟨2, by omega⟩
  rw [hB, hsum] at hc
  letI : Nonempty (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
    apply fixedTwo_nonempty
    · intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_zero] at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      simp at hv
  have hD : (Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) : ℝ) ≠ 0 := by
    norm_cast
    exact Fintype.card_pos.ne'
  have hcR : (Fintype.card (AvoidTwo (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) : ℝ) +
      ∑ k ∈ S, ((eventFinset hn k).card : ℝ) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
    exact_mod_cast hc
  rw [PermutationSameEdgeLimit.F_eq_actual (by omega) (by omega) (by omega) (by decide)]
  rw [← Finset.sum_div]
  have hnum : (Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) : ℝ) -
      Fintype.card (AvoidTwo (⟨n - 1, by omega⟩ : Fin n) 0 ⟨2, by omega⟩) =
      ∑ k ∈ S, ((eventFinset hn k).card : ℝ) := by linarith
  rw [← hnum, sub_div, div_self hD]
  have hz (h : 0 < n) : (⟨0, h⟩ : Fin n) = 0 := Fin.ext (by simp)
  simp only [hz]

/-- Passing an actual cross-multiplied count to its real fraction. -/
theorem event_fraction_of_count {n k t : ℕ} [NeZero n] (hn : 3 ≤ n)
    (hc : (eventFinset hn k).card * Nat.factorial t * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩)) :
    (eventFinset hn k).card /
        (Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) : ℝ) =
      (1 / (Nat.factorial t : ℝ)) / ((n : ℝ) - 2) := by
  letI : Nonempty (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
    apply fixedTwo_nonempty
    · intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_zero] at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      simp at hv
  have hD : (Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) : ℝ) ≠ 0 := by
    norm_cast
    exact Fintype.card_pos.ne'
  have hT : (Nat.factorial t : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have hN : (n : ℝ) - 2 ≠ 0 := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcR : ((eventFinset hn k).card : ℝ) * Nat.factorial t * ((n : ℝ) - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩) := by
    have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      norm_num
    rw [← hcast]
    exact_mod_cast hc
  apply (div_eq_div_iff hD hN).mpr
  rw [div_mul_eq_mul_div, one_mul]
  apply (eq_div_iff hT).mpr
  nlinarith [hcR]

/-- Exact finite failure formula for the actual uniform endpoint-zero/two
permutation experiment, including both parities and the boundary case `n = 3`. -/
theorem one_sub_F_zero_two {n : ℕ} (hn : 3 ≤ n) :
    1 - PermutationSameEdgeLimit.F n 0 2 =
      ((∑ k ∈ Finset.Icc 2 (n / 2), 1 / (Nat.factorial (k - 1) : ℝ)) +
        (if Odd n then 1 / (Nat.factorial ((n - 3) / 2) : ℝ) else 0)) /
          ((n : ℝ) - 2) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let D : ℝ := Fintype.card
    (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ 0 ⟨2, by omega⟩)
  let c : ℝ := 1 / (Nat.factorial ((n - 3) / 2) : ℝ)
  have hterm (k : ℕ) (hmem : k ∈ Finset.Icc 2 (n - 1)) :
      (eventFinset hn k).card / D =
        ((if k ≤ n / 2 then 1 / (Nat.factorial (k - 1) : ℝ) else 0) +
          (if Odd n ∧ k = n / 2 + 1 then c else 0)) / ((n : ℝ) - 2) := by
    have hk : 2 ≤ k := (Finset.mem_Icc.mp hmem).1
    have hkn : k < n := by have htop := (Finset.mem_Icc.mp hmem).2; omega
    have hpar : n = 2 * k - 1 ↔ Odd n ∧ k = n / 2 + 1 := by
      rw [Nat.odd_iff]
      omega
    by_cases hhalf : k ≤ n / 2
    · have hno : ¬ (Odd n ∧ k = n / 2 + 1) := by omega
      simp only [hhalf, if_pos, hno, if_false, add_zero]
      apply event_fraction_of_count hn
      rw [card_eventFinset hn hkn]
      exact card_short_event hn hk hkn (by omega)
    · by_cases hexc : Odd n ∧ k = n / 2 + 1
      · have hsize := hpar.mpr hexc
        have hfac : k - 2 = (n - 3) / 2 := by omega
        rw [if_neg hhalf, if_pos hexc, zero_add]
        dsimp only [c]
        apply event_fraction_of_count hn
        rw [card_eventFinset hn hkn, ← hfac]
        exact card_exceptional_event hn hk hkn hsize
      · have hsize : n ≠ 2 * k - 1 := fun he => hexc (hpar.mp he)
        rw [eventFinset_eq_empty hn hk hkn (by omega) hsize]
        simp [hhalf, hexc]
  have hshort : (∑ k ∈ Finset.Icc 2 (n - 1),
      if k ≤ n / 2 then 1 / (Nat.factorial (k - 1) : ℝ) else 0) =
      ∑ k ∈ Finset.Icc 2 (n / 2), 1 / (Nat.factorial (k - 1) : ℝ) := by
    rw [← Finset.sum_filter]
    have he : (Finset.Icc 2 (n - 1)).filter (fun k => k ≤ n / 2) = Finset.Icc 2 (n / 2) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [he]
  have hexc : (∑ k ∈ Finset.Icc 2 (n - 1),
      if Odd n ∧ k = n / 2 + 1 then c else 0) = if Odd n then c else 0 := by
    by_cases hodd : Odd n
    · have hmem : n / 2 + 1 ∈ Finset.Icc 2 (n - 1) := by
        rw [Finset.mem_Icc]
        constructor <;> omega
      simp [hodd, Finset.sum_ite_eq', hmem]
    · simp [hodd]
  rw [one_sub_F_eq_event_sum hn]
  change (∑ k ∈ Finset.Icc 2 (n - 1), (eventFinset hn k).card / D) = _
  calc
    _ = ((∑ k ∈ Finset.Icc 2 (n - 1),
          if k ≤ n / 2 then 1 / (Nat.factorial (k - 1) : ℝ) else 0) +
        (∑ k ∈ Finset.Icc 2 (n - 1),
          if Odd n ∧ k = n / 2 + 1 then c else 0)) / ((n : ℝ) - 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl hterm
    _ = _ := by rw [hshort, hexc]

/-- The smallest valid experiment fails with probability one. -/
theorem one_sub_F_three : 1 - PermutationSameEdgeLimit.F 3 0 2 = 1 := by
  have h := one_sub_F_zero_two (n := 3) (by decide)
  norm_num [Nat.odd_iff] at h
  linarith

/-- The first even-size experiment fails with probability one half. -/
theorem one_sub_F_four : 1 - PermutationSameEdgeLimit.F 4 0 2 = 1 / 2 := by
  have h := one_sub_F_zero_two (n := 4) (by decide)
  norm_num [Nat.odd_iff] at h
  exact h

/-- At size five the short and exceptional events together have probability two thirds. -/
theorem one_sub_F_five : 1 - PermutationSameEdgeLimit.F 5 0 2 = 2 / 3 := by
  have h := one_sub_F_zero_two (n := 5) (by decide)
  norm_num [Nat.odd_iff] at h
  exact h

end

example : ∃ π : Equiv.Perm (Fin 3), π 0 = 0 ∧ π 2 = 2 ∧
    Overlap (by decide : 2 < 3) π := by
  refine ⟨Equiv.refl _, rfl, rfl, ?_⟩
  unfold Overlap
  decide

example : ∃ π : Equiv.Perm (Fin 5), π 0 = 0 ∧ π 4 = 2 ∧
    Overlap (by decide : 2 < 5) π := by
  refine ⟨(Equiv.swap 1 3).trans (Equiv.swap 2 4), by decide, by decide, ?_⟩
  unfold Overlap
  decide

example : ∃ π : Equiv.Perm (Fin 5), π 0 = 0 ∧ π 4 = 2 ∧
    Overlap (by decide : 3 < 5) π := by
  refine ⟨((Equiv.swap 1 3).trans (Equiv.swap 1 2)).trans (Equiv.swap 2 4),
    by decide, by decide, ?_⟩
  unfold Overlap
  decide

end PermutationEndpointZeroTwoExact
