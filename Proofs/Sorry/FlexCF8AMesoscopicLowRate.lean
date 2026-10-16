import Combinatorics.PermutationLowEndpointEventBound
import Combinatorics.PermutationSameEdgeMovingLimit
set_option autoImplicit false
open PermutationOrderCounting PermutationEndpointCounting PermutationEndpointZeroTwoExact

namespace FlexCF8AMesoscopicLowRate

attribute [local instance] Classical.propDecidable

 theorem restricted_shuffle_count {n t : ℕ} (p q r a b c : Fin n)
    (u v : Fin t ↪ Fin n) (hp : p ∉ Set.range u) (hq : q ∉ Set.range u)
    (hr : r ∉ Set.range u) (huv : Disjoint (Set.range u) (Set.range v))
    (Q : Equiv.Perm (Fin n) → Prop)
    (hQ : ∀ (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin t)),
      Q ((blockPerm u σ).trans π) ↔ Q π) :
    Fintype.card {π : AgreementThree p q r a b c u v // Q π.val} * t.factorial =
      Fintype.card {π : FixedThree p q r a b c // Q π.val} := by
  classical
  let f : {π : AgreementThree p q r a b c u v // Q π.val} × Equiv.Perm (Fin t) →
      {π : FixedThree p q r a b c // Q π.val} := fun x =>
    ⟨⟨(blockPerm u x.2).trans x.1.val.val, by
      simpa only [Equiv.trans_apply, blockPerm_apply_of_notMem u x.2 p hp,
        blockPerm_apply_of_notMem u x.2 q hq, blockPerm_apply_of_notMem u x.2 r hr]
        using x.1.val.property.1⟩, (hQ _ _).mpr x.1.property⟩
  have hbij := shuffleAgreementTwo_bijective p q a b u v hp hq huv
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨π, σ⟩ ⟨ρ, τ⟩ he
      have he' : shuffleAgreementTwo p q a b u v hp hq
          (⟨π.val.val, π.val.property.1.1, π.val.property.2⟩, σ) =
          shuffleAgreementTwo p q a b u v hp hq
          (⟨ρ.val.val, ρ.val.property.1.1, ρ.val.property.2⟩, τ) := by
        apply Subtype.ext
        exact congrArg (fun x => x.val.val) he
      have hi := hbij.1 he'
      exact Prod.ext (Subtype.ext (Subtype.ext (congrArg (fun x => x.1.val) hi)))
        (congrArg (fun x : AgreementTwo p q a b u v × Equiv.Perm (Fin t) => x.2) hi)
    · intro γ
      obtain ⟨⟨π, σ⟩, he⟩ := hbij.2 ⟨γ.val.val, γ.val.property.1⟩
      have hr' : π.val r = c := by
        have hv := congrArg (fun x : FixedTwo p q a b => x.val r) he
        change π.val (blockPerm u σ r) = γ.val.val r at hv
        rw [blockPerm_apply_of_notMem u σ r hr] at hv
        exact hv.trans γ.val.property.2
      have hval : (blockPerm u σ).trans π.val = γ.val.val :=
        congrArg (fun x : FixedTwo p q a b => x.val) he
      have hgood : Q π.val := (hQ _ _).mp (hval.symm ▸ γ.property)
      refine ⟨(⟨⟨π.val, ⟨π.property.1, hr'⟩, π.property.2⟩, hgood⟩, σ), ?_⟩
      exact Subtype.ext (Subtype.ext hval)
  simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
    using Fintype.card_of_bijective hf

theorem high_invariant {n t : ℕ} (u v : Fin t ↪ Fin n) (q : Fin n) (M : ℕ)
    (hd : Disjoint (Set.range u) (Set.range v))
    (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin t)) :
    ((∀ i, M < (((blockPerm u σ).trans π) (u i)).val) ∧
      (∀ i, v i ≠ q → M < (((blockPerm u σ).trans π) (v i)).val)) ↔
    ((∀ i, M < (π (u i)).val) ∧ (∀ i, v i ≠ q → M < (π (v i)).val)) := by
  have hv (i : Fin t) : v i ∉ Set.range u := by
    rintro ⟨j, hj⟩
    exact Set.disjoint_left.mp hd ⟨j, hj⟩ ⟨i, rfl⟩
  simp only [Equiv.trans_apply, blockPerm_apply, blockPerm_apply_of_notMem u σ _ (hv _)]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨fun i => by simpa using h (σ.symm i), h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨fun i => h (σ i), h'⟩

theorem overlap_iff_high_suffix_witness {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (a b c : Fin n) (hcb : c < b)
    (π : Equiv.Perm (Fin n)) (ha : π 0 = a)
    (hb : π ⟨n - 1, by have := NeZero.pos n; omega⟩ = b)
    (hc : π ⟨n - k, by omega⟩ = c)
    (hu : ∀ i : Fin (k - 1), max a.val b.val <
      (π (PermutationEndpointZeroTwoExact.segment 1 (k - 1) (by omega) i)).val)
    (hv : ∀ i : Fin (k - 1),
      PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega) i ≠ ⟨n - 1, by have := NeZero.pos n; omega⟩ →
      max a.val b.val < (π (PermutationEndpointZeroTwoExact.segment (n - k + 1) (k - 1) (by omega) i)).val) :
    PermutationOverlapBound.Overlap hkn π ↔ SameOrder π
      (PermutationEndpointZeroTwoExact.segment 1 (k - 1) (by omega))
      (PermutationEndpointZeroTwoExact.segment (n - k + 1) (k - 1) (by omega)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  let f : Fin (t + 1) → Fin n := fun i => π ⟨i.val, by omega⟩
  let g : Fin (t + 1) → Fin n := fun i => π ⟨i.val + (n - (t + 1)), by omega⟩
  have hf : ∀ i : Fin t, f 0 < f i.succ := by
    intro i
    change π 0 < π ⟨i.val + 1, by omega⟩
    rw [ha]
    exact lt_of_le_of_lt (le_max_left _ _) (hu i)
  have hg : ∀ i : Fin t, g 0 < g i.succ := by
    intro i
    dsimp only [g]
    simp only [Fin.val_zero, Nat.zero_add, Fin.val_succ]
    rw [hc]
    have he : (⟨i.val + 1 + (n - (t + 1)), by omega⟩ : Fin n) =
        PermutationEndpointZeroTwoExact.segment (n - (t + 1) + 1) t (by omega) i := by
      apply Fin.ext
      change i.val + 1 + (n - (t + 1)) = i.val + (n - (t + 1) + 1)
      omega
    rw [he]
    by_cases hq : PermutationEndpointZeroTwoExact.segment (n := n) (n - (t + 1) + 1) t (by omega) i = ⟨n - 1, by have := NeZero.pos n; omega⟩
    · rw [hq, hb]
      exact hcb
    · exact lt_trans hcb (lt_of_le_of_lt (le_max_right _ _) (hv i hq))
  have hcomp := comparisons_iff_succ f g hf hg
  convert hcomp using 1
  · rfl
  · simp only [SameOrder, PermutationEndpointZeroTwoExact.segment, Function.Embedding.coeFn_mk, f, g,
      Fin.val_succ, Nat.add_assoc, Nat.add_comm]
    rfl

theorem global_high_invariant {n t : ℕ} (u : Fin t ↪ Fin n)
    (S : Finset (Fin n)) (r : Fin n) (M : ℕ)
    (hu : ∀ i, u i ∈ S) (hr : r ∉ Set.range u)
    (π : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin t)) :
    (∀ x ∈ S, x ≠ r → M < (((blockPerm u σ).trans π) x).val) ↔
      (∀ x ∈ S, x ≠ r → M < (π x).val) := by
  have forward (ρ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin t))
      (h : ∀ x ∈ S, x ≠ r → M < (ρ x).val) :
      ∀ x ∈ S, x ≠ r → M < (((blockPerm u τ).trans ρ) x).val := by
    intro x hx hxr
    by_cases hm : x ∈ Set.range u
    · obtain ⟨i, rfl⟩ := hm
      simp only [Equiv.trans_apply, blockPerm_apply]
      exact h (u (τ i)) (hu _) (fun he => hr ⟨τ i, he⟩)
    · simpa only [Equiv.trans_apply, blockPerm_apply_of_notMem u τ x hm] using h x hx hxr
  constructor
  · intro h x hx hxr
    have hh := forward ((blockPerm u σ).trans π) σ.symm h x hx hxr
    by_cases hm : x ∈ Set.range u
    · obtain ⟨i, rfl⟩ := hm
      simpa only [Equiv.trans_apply, blockPerm_apply, Equiv.apply_symm_apply] using hh
    · simpa only [Equiv.trans_apply,
        blockPerm_apply_of_notMem u σ.symm x hm,
        blockPerm_apply_of_notMem u σ x hm] using hh
  · exact forward π σ

theorem suffix_dominant_count {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (hshort : 2 * k ≤ n)
    (a b c : Fin n) (hcb : c < b) :
    let u := PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)
    let v := PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega)
    let Q := fun π : Equiv.Perm (Fin n) =>
      (∀ i, max a.val b.val < (π (u i)).val) ∧
      (∀ i, v i ≠ ⟨n - 1, by have := NeZero.pos n; omega⟩ → max a.val b.val < (π (v i)).val)
    Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n) a b //
      π.val ⟨n - k, by omega⟩ = c ∧ Q π.val} * (k - 1).factorial =
      Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨n - k, by omega⟩ a b c // Q π.val} := by
  classical
  let u := PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)
  let v := PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega)
  let q : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩
  let r : Fin n := ⟨n - k, by omega⟩
  let Q := fun π : Equiv.Perm (Fin n) =>
    (∀ i, max a.val b.val < (π (u i)).val) ∧
    (∀ i, v i ≠ q → max a.val b.val < (π (v i)).val)
  change Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} * (k - 1).factorial =
    Fintype.card {π : FixedThree (0 : Fin n) q r a b c // Q π.val}
  have hd : Disjoint (Set.range u) (Set.range v) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + (n - k + 1) = i.val + 1 at hv
    omega
  have h0 : (0 : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = 0 at hv
    omega
  have hq : q ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - 1 at hv
    omega
  have hr : r ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - k at hv
    omega
  have hbridge (π : Equiv.Perm (Fin n)) (ha : π 0 = a) (hb : π q = b)
      (hc : π r = c) (hgood : Q π) :
      PermutationOverlapBound.Overlap hkn π ↔ SameOrder π u v :=
    overlap_iff_high_suffix_witness hk hkn a b c hcb π ha hb hc hgood.1 hgood.2
  have he : Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} =
      Fintype.card {π : AgreementThree (0 : Fin n) q r a b c u v // Q π.val} := by
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨⟨π.val.val, ⟨π.val.property.1, π.property.1⟩,
        (hbridge π.val.val π.val.property.1.1 π.val.property.1.2
          π.property.1 π.property.2).mp π.val.property.2⟩, π.property.2⟩
      invFun := fun π => ⟨⟨π.val.val, π.val.property.1.1,
        (hbridge π.val.val π.val.property.1.1.1 π.val.property.1.1.2
          π.val.property.1.2 π.property).mpr π.val.property.2⟩,
        π.val.property.1.2, π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  simpa only [← Nat.card_eq_fintype_card] using
    restricted_shuffle_count 0 q r a b c u v h0 hq hr hd Q
      (fun π σ => high_invariant u v q (max a.val b.val) hd π σ)

example : 2 ≤ (2 : ℕ) ∧ 2 < (6 : ℕ) ∧ 2 * 2 ≤ (6 : ℕ) ∧
    (1 : Fin 6) < 2 ∧ Nonempty {π : FixedThree (0 : Fin 6) 5 4 0 2 1 //
      (∀ i : Fin 1, 2 < (π.val (PermutationEndpointZeroTwoExact.segment (n := 6) 1 1 (by decide) i)).val) ∧
      (∀ i : Fin 1, PermutationEndpointZeroTwoExact.segment (n := 6) 5 1 (by decide) i ≠ 5 →
        2 < (π.val (PermutationEndpointZeroTwoExact.segment (n := 6) 5 1 (by decide) i)).val)} := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨⟨⟨(Equiv.swap 1 4).trans (Equiv.swap 2 5), ?_, ?_⟩, ?_, ?_⟩⟩
  · decide
  · decide
  · intro i
    fin_cases i
    decide
  · intro i hi
    fin_cases i
    exact False.elim (hi rfl)

private theorem remainingThree {n : ℕ} (p q r s a b c : Fin n)
    (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r) (π : FixedThree p q r a b c) :
    (π.val s ≠ a ∧ π.val s ≠ b) ∧ π.val s ≠ c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h; exact hsp (π.val.injective (h.trans π.property.1.1.symm))
  · intro h; exact hsq (π.val.injective (h.trans π.property.1.2.symm))
  · intro h; exact hsr (π.val.injective (h.trans π.property.2.symm))

private noncomputable def exchangeThree {n : ℕ} (p q r s a b c : Fin n)
    (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r)
    (x : FixedThree p q r a b c × {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c}) :
    FixedThree p q r a b c × {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c} :=
  (⟨x.1.val.trans (Equiv.swap (x.1.val s) x.2.val), by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change Equiv.swap (x.1.val s) x.2.val (x.1.val p) = a
        rw [x.1.property.1.1]
        exact Equiv.swap_apply_of_ne_of_ne
          (remainingThree p q r s a b c hsp hsq hsr x.1).1.1.symm x.2.property.1.1.symm
      · change Equiv.swap (x.1.val s) x.2.val (x.1.val q) = b
        rw [x.1.property.1.2]
        exact Equiv.swap_apply_of_ne_of_ne
          (remainingThree p q r s a b c hsp hsq hsr x.1).1.2.symm x.2.property.1.2.symm
      · change Equiv.swap (x.1.val s) x.2.val (x.1.val r) = c
        rw [x.1.property.2]
        exact Equiv.swap_apply_of_ne_of_ne
          (remainingThree p q r s a b c hsp hsq hsr x.1).2.symm x.2.property.2.symm⟩,
    ⟨x.1.val s, remainingThree p q r s a b c hsp hsq hsr x.1⟩)

private theorem exchangeThree_value {n : ℕ} (p q r s a b c : Fin n)
    (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r)
    (x : FixedThree p q r a b c × {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c}) :
    (exchangeThree p q r s a b c hsp hsq hsr x).1.val s = x.2.val :=
  Equiv.swap_apply_left _ _

private theorem exchangeThree_involutive {n : ℕ} (p q r s a b c : Fin n)
    (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r) :
    Function.Involutive (exchangeThree p q r s a b c hsp hsq hsr) := by
  intro x
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    change Equiv.swap ((exchangeThree p q r s a b c hsp hsq hsr x).1.val s) (x.1.val s)
      (Equiv.swap (x.1.val s) x.2.val (x.1.val i)) = x.1.val i
    rw [exchangeThree_value, Equiv.swap_comm]
    exact Equiv.swap_apply_self _ _ _
  · apply Subtype.ext
    exact exchangeThree_value p q r s a b c hsp hsq hsr x

theorem marginalThree_card {n : ℕ} (p q r s a b c : Fin n)
    (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r) (P : Fin n → Prop) :
    Fintype.card {π : FixedThree p q r a b c // P (π.val s)} *
      Fintype.card {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c} =
    Fintype.card (FixedThree p q r a b c) *
      Fintype.card {d : Fin n // ((d ≠ a ∧ d ≠ b) ∧ d ≠ c) ∧ P d} := by
  classical
  let f := exchangeThree p q r s a b c hsp hsq hsr
  let e : ({π : FixedThree p q r a b c // P (π.val s)} ×
      {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c}) ≃
      (FixedThree p q r a b c × {d : Fin n // ((d ≠ a ∧ d ≠ b) ∧ d ≠ c) ∧ P d}) :=
    { toFun := fun x => ((f (x.1.val, x.2)).1,
        ⟨x.1.val.val s, remainingThree p q r s a b c hsp hsq hsr x.1.val, x.1.property⟩)
      invFun := fun y => (⟨(f (y.1, ⟨y.2.val, y.2.property.1⟩)).1, by
        change P ((exchangeThree p q r s a b c hsp hsq hsr _).1.val s)
        rw [exchangeThree_value]
        exact y.2.property.2⟩,
        (f (y.1, ⟨y.2.val, y.2.property.1⟩)).2)
      left_inv := by
        intro x
        have h := exchangeThree_involutive p q r s a b c hsp hsq hsr (x.1.val, x.2)
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · exact congrArg (fun z : FixedThree p q r a b c ×
            {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c} => z.2) h
      right_inv := by
        intro y
        have h := exchangeThree_involutive p q r s a b c hsp hsq hsr
          (y.1, ⟨y.2.val, y.2.property.1⟩)
        apply Prod.ext
        · exact congrArg (fun z : FixedThree p q r a b c ×
            {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c} => z.1) h
        · apply Subtype.ext
          exact congrArg (fun z => z.2.val) h }
  simpa only [Fintype.card_prod] using Fintype.card_congr e

theorem card_remainingThree {n : ℕ} (a b c : Fin n)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Fintype.card {d : Fin n // (d ≠ a ∧ d ≠ b) ∧ d ≠ c} = n - 3 := by
  classical
  rw [Fintype.card_of_subtype (Finset.univ \ {a, b, c}) (by intro d; simp [and_assoc])]
  simp [Finset.card_sdiff, hab, hca.symm, hcb.symm]

theorem card_remainingThree_low_le {n : ℕ} (a b c : Fin n) :
    Fintype.card {d : Fin n // ((d ≠ a ∧ d ≠ b) ∧ d ≠ c) ∧
      d.val ≤ max a.val b.val} ≤ max a.val b.val := by
  classical
  have hbound (x : Fin n)
      (h : ∀ d : Fin n, ((d ≠ a ∧ d ≠ b) ∧ d ≠ c) ∧ d.val ≤ max a.val b.val → d < x) :
      Fintype.card {d : Fin n // ((d ≠ a ∧ d ≠ b) ∧ d ≠ c) ∧
        d.val ≤ max a.val b.val} ≤ x.val := by
    have hi := Fintype.card_le_of_injective
      (fun d : {d : Fin n // ((d ≠ a ∧ d ≠ b) ∧ d ≠ c) ∧
        d.val ≤ max a.val b.val} => (⟨d.val, h d.val d.property⟩ : {d : Fin n // d < x}))
      (by intro d e he; exact Subtype.ext (congrArg (fun z : {d : Fin n // d < x} => z.val) he))
    have hc : Fintype.card {d : Fin n // d < x} = x.val := by
      rw [Fintype.card_of_subtype (Finset.Iio x) (by simp)]
      exact Fin.card_Iio x
    exact hc ▸ hi
  rcases le_total a b with hab | hba
  · have hv : a.val ≤ b.val := hab
    calc
      _ ≤ b.val := hbound b (by
        intro d hd
        have hdle : d ≤ b := by
          change d.val ≤ b.val
          simpa only [max_eq_right hv] using hd.2
        exact lt_of_le_of_ne hdle hd.1.1.2)
      _ = _ := (max_eq_right hv).symm
  · have hv : b.val ≤ a.val := hba
    calc
      _ ≤ a.val := hbound a (by
        intro d hd
        have hdle : d ≤ a := by
          change d.val ≤ a.val
          simpa only [max_eq_left hv] using hd.2
        exact lt_of_le_of_ne hdle hd.1.1.1)
      _ = _ := (max_eq_left hv).symm

theorem marginalThree_low_bound {n : ℕ} (p q r s a b c : Fin n)
    (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Fintype.card {π : FixedThree p q r a b c // (π.val s).val ≤ max a.val b.val} * (n - 3) ≤
      Fintype.card (FixedThree p q r a b c) * max a.val b.val := by
  have hm := marginalThree_card p q r s a b c hsp hsq hsr
    (fun d => d.val ≤ max a.val b.val)
  have hrem := card_remainingThree a b c hab hca hcb
  have hlo := card_remainingThree_low_le a b c
  simp only [← Nat.card_eq_fintype_card] at hm hrem hlo ⊢
  rw [← hrem, hm]
  exact Nat.mul_le_mul_left _ hlo

theorem triple_bad_union_bound {n : ℕ} {I : Type*} [Fintype I]
    (p q r a b c : Fin n) (s : I → Fin n)
    (hsp : ∀ i, s i ≠ p) (hsq : ∀ i, s i ≠ q) (hsr : ∀ i, s i ≠ r)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Fintype.card {π : FixedThree p q r a b c //
      ∃ i, (π.val (s i)).val ≤ max a.val b.val} * (n - 3) ≤
      Fintype.card I * Fintype.card (FixedThree p q r a b c) * max a.val b.val := by
  classical
  let B := {π : FixedThree p q r a b c // ∃ i, (π.val (s i)).val ≤ max a.val b.val}
  let f : B → Σ i : I, {π : FixedThree p q r a b c //
      (π.val (s i)).val ≤ max a.val b.val} := fun π =>
    ⟨π.property.choose, π.val, π.property.choose_spec⟩
  have hf : Function.Injective f := by
    intro π ρ he
    exact Subtype.ext (congrArg (fun z => z.2.val) he)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hc
  calc
    _ ≤ (∑ i : I, Fintype.card {π : FixedThree p q r a b c //
        (π.val (s i)).val ≤ max a.val b.val}) * (n - 3) :=
      Nat.mul_le_mul_right _ hc
    _ = ∑ i : I, Fintype.card {π : FixedThree p q r a b c //
        (π.val (s i)).val ≤ max a.val b.val} * (n - 3) := by rw [Finset.sum_mul]
    _ ≤ ∑ _i : I, Fintype.card (FixedThree p q r a b c) * max a.val b.val :=
      Finset.sum_le_sum (fun i _ => marginalThree_low_bound p q r (s i) a b c
        (hsp i) (hsq i) (hsr i) hab hca hcb)
    _ = _ := by simp [Nat.mul_assoc]

theorem suffix_bad_high_bound {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (hshort : 2 * k ≤ n)
    (a b c : Fin n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    let u := PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)
    let v := PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega)
    let Q := fun π : Equiv.Perm (Fin n) =>
      (∀ i, max a.val b.val < (π (u i)).val) ∧
      (∀ i, v i ≠ ⟨n - 1, by have := NeZero.pos n; omega⟩ → max a.val b.val < (π (v i)).val)
    Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨n - k, by omega⟩ a b c // ¬ Q π.val} * (n - 3) ≤
      (2 * k - 3) * Fintype.card (FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨n - k, by omega⟩ a b c) * max a.val b.val := by
  classical
  let u := PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)
  let v := PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega)
  let q : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩
  let r : Fin n := ⟨n - k, by omega⟩
  let Q := fun π : Equiv.Perm (Fin n) =>
    (∀ i, max a.val b.val < (π (u i)).val) ∧
    (∀ i, v i ≠ q → max a.val b.val < (π (v i)).val)
  let s : Fin (k - 1) ⊕ Fin (k - 2) → Fin n := Sum.elim u
    (PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 2) (by omega))
  change Fintype.card {π : FixedThree (0 : Fin n) q r a b c // ¬ Q π.val} * (n - 3) ≤ _
  have hbad (π : FixedThree (0 : Fin n) q r a b c) (h : ¬ Q π.val) :
      ∃ i, (π.val (s i)).val ≤ max a.val b.val := by
    simp only [Q, not_and_or, not_forall, not_lt] at h
    rcases h with ⟨i, hi⟩ | ⟨i, hne, hi⟩
    · exact ⟨Sum.inl i, hi⟩
    · have hi' : i.val < k - 2 := by
        have hneq : i.val ≠ k - 2 := by
          intro he
          apply hne
          apply Fin.ext
          change i.val + (n - k + 1) = n - 1
          omega
        omega
      exact ⟨Sum.inr ⟨i.val, hi'⟩, hi⟩
  have hc := Fintype.card_le_of_injective
    (fun π : {π : FixedThree (0 : Fin n) q r a b c // ¬ Q π.val} =>
      (⟨π.val, hbad π.val π.property⟩ : {π : FixedThree (0 : Fin n) q r a b c //
        ∃ i, (π.val (s i)).val ≤ max a.val b.val}))
    (by
      intro π ρ he
      apply Subtype.ext
      exact congrArg (fun z : {π : FixedThree (0 : Fin n) q r a b c //
        ∃ i, (π.val (s i)).val ≤ max a.val b.val} => z.val) he)
  have hs0 : ∀ i, s i ≠ (0 : Fin n) := by
    intro i
    cases i with
    | inl i => intro he; have hv := congrArg Fin.val he; change i.val + 1 = 0 at hv; omega
    | inr i => intro he; have hv := congrArg Fin.val he; change i.val + (n - k + 1) = 0 at hv; omega
  have hsq : ∀ i, s i ≠ q := by
    intro i
    cases i with
    | inl i => intro he; have hv := congrArg Fin.val he; change i.val + 1 = n - 1 at hv; omega
    | inr i => intro he; have hv := congrArg Fin.val he; change i.val + (n - k + 1) = n - 1 at hv; omega
  have hsr : ∀ i, s i ≠ r := by
    intro i
    cases i with
    | inl i => intro he; have hv := congrArg Fin.val he; change i.val + 1 = n - k at hv; omega
    | inr i => intro he; have hv := congrArg Fin.val he; change i.val + (n - k + 1) = n - k at hv; omega
  have hbound := triple_bad_union_bound (0 : Fin n) q r a b c s hs0 hsq hsr hab hca hcb
  have hcard : Fintype.card (Fin (k - 1) ⊕ Fin (k - 2)) = 2 * k - 3 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hcard] at hbound
  exact (Nat.mul_le_mul_right (n - 3) hc).trans hbound

theorem suffix_dominant_deficit {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (hshort : 2 * k ≤ n)
    (a b c : Fin n) (hab : a ≠ b) (hca : c ≠ a) (hcb : c < b) :
    let u := PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)
    let v := PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega)
    let Q := fun π : Equiv.Perm (Fin n) =>
      (∀ i, max a.val b.val < (π (u i)).val) ∧
      (∀ i, v i ≠ ⟨n - 1, by have := NeZero.pos n; omega⟩ → max a.val b.val < (π (v i)).val)
    let D := Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n) a b //
      π.val ⟨n - k, by omega⟩ = c ∧ Q π.val}
    let T := Fintype.card (FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨n - k, by omega⟩ a b c)
    D * (k - 1).factorial ≤ T ∧
      (T - D * (k - 1).factorial) * (n - 3) ≤ (2 * k - 3) * T * max a.val b.val := by
  classical
  dsimp only
  have he := suffix_dominant_count hk hkn hshort a b c hcb
  have hb := suffix_bad_high_bound hk hkn hshort a b c hab hca (ne_of_lt hcb)
  dsimp only at he hb
  rw [he]
  constructor
  · exact Fintype.card_subtype_le _
  · rw [Fintype.card_subtype_compl] at hb
    exact hb

theorem two_low_positions_bound {n : ℕ} (p q r s a b : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q) (hsp : s ≠ p) (hsq : s ≠ q)
    (hsr : s ≠ r) (hab : a ≠ b) :
    Fintype.card {π : FixedTwo p q a b //
      (π.val r).val ≤ max a.val b.val ∧ (π.val s).val ≤ max a.val b.val} *
      (n - 3) * (n - 2) ≤
      Fintype.card (FixedTwo p q a b) * max a.val b.val * max a.val b.val := by
  classical
  let L := {c : Fin n // (c ≠ a ∧ c ≠ b) ∧ c.val ≤ max a.val b.val}
  let B := {π : FixedTwo p q a b //
      (π.val r).val ≤ max a.val b.val ∧ (π.val s).val ≤ max a.val b.val}
  have hrem (π : FixedTwo p q a b) : π.val r ≠ a ∧ π.val r ≠ b := by
    constructor
    · intro h; exact hrp (π.val.injective (h.trans π.property.1.symm))
    · intro h; exact hrq (π.val.injective (h.trans π.property.2.symm))
  let f : B → Σ c : L, {π : FixedThree p q r a b c.val //
      (π.val s).val ≤ max a.val b.val} := fun π =>
    ⟨⟨π.val.val r, hrem π.val, π.property.1⟩,
      ⟨π.val.val, π.val.property, rfl⟩, π.property.2⟩
  have hf : Function.Injective f := by
    intro π ρ he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.2.val.val) he
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hc
  have hL : Fintype.card L ≤ max a.val b.val := by
    have hh (x : Fin n) (hx : ∀ c : L, c.val < x) : Fintype.card L ≤ x.val := by
      have hi := Fintype.card_le_of_injective
        (fun c : L => (⟨c.val, hx c⟩ : {d : Fin n // d < x}))
        (by intro c d he; exact Subtype.ext (congrArg (fun z : {d : Fin n // d < x} => z.val) he))
      have he : Fintype.card {d : Fin n // d < x} = x.val := by
        rw [Fintype.card_of_subtype (Finset.Iio x) (by simp)]
        exact Fin.card_Iio x
      exact he ▸ hi
    rcases le_total a b with ha | hb
    · have hm : max a.val b.val = b.val := max_eq_right ha
      calc
        _ ≤ b.val := hh b (fun c => lt_of_le_of_ne
          (show c.val ≤ b from by change c.val.val ≤ b.val; simpa only [hm] using c.property.2)
          c.property.1.2)
        _ = _ := hm.symm
    · have hm : max a.val b.val = a.val := max_eq_left hb
      calc
        _ ≤ a.val := hh a (fun c => lt_of_le_of_ne
          (show c.val ≤ a from by change c.val.val ≤ a.val; simpa only [hm] using c.property.2)
          c.property.1.1)
        _ = _ := hm.symm
  calc
    _ ≤ (∑ c : L, Fintype.card {π : FixedThree p q r a b c.val //
          (π.val s).val ≤ max a.val b.val}) * (n - 3) * (n - 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
    _ = (∑ c : L, Fintype.card {π : FixedThree p q r a b c.val //
          (π.val s).val ≤ max a.val b.val} * (n - 3)) * (n - 2) := by rw [Finset.sum_mul]
    _ ≤ (∑ c : L, Fintype.card (FixedThree p q r a b c.val) * max a.val b.val) * (n - 2) := by
      apply Nat.mul_le_mul_right
      exact Finset.sum_le_sum (fun c _ => marginalThree_low_bound p q r s a b c.val
        hsp hsq hsr hab c.property.1.1 c.property.1.2)
    _ = ∑ c : L, Fintype.card (FixedThree p q r a b c.val) * (n - 2) * max a.val b.val := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      exact Nat.mul_right_comm _ _ _
    _ = ∑ _c : L, Fintype.card (FixedTwo p q a b) * max a.val b.val := by
      apply Finset.sum_congr rfl
      intro c _
      rw [card_fixedThree_mul p q r a b c.val hrp hrq hab c.property.1.1 c.property.1.2]
    _ = Fintype.card L * (Fintype.card (FixedTwo p q a b) * max a.val b.val) := by simp
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right (Fintype.card (FixedTwo p q a b) * max a.val b.val) hL
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hh

theorem overlap_iff_high_prefix_witness {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (a b c : Fin n) (hca : c < a)
    (π : Equiv.Perm (Fin n)) (ha : π 0 = a)
    (hb : π ⟨n - 1, by have := NeZero.pos n; omega⟩ = b)
    (hc : π ⟨k - 1, by omega⟩ = c)
    (hu : ∀ i : Fin (k - 1),
      PermutationEndpointZeroTwoExact.segment (n := n) 0 (k - 1) (by omega) i ≠ 0 →
      max a.val b.val <
        (π (PermutationEndpointZeroTwoExact.segment 0 (k - 1) (by omega) i)).val)
    (hv : ∀ i : Fin (k - 1), max a.val b.val <
      (π (PermutationEndpointZeroTwoExact.segment (n - k) (k - 1) (by omega) i)).val) :
    PermutationOverlapBound.Overlap hkn π ↔ SameOrder π
      (PermutationEndpointZeroTwoExact.segment 0 (k - 1) (by omega))
      (PermutationEndpointZeroTwoExact.segment (n - k) (k - 1) (by omega)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  let f : Fin (t + 1) → Fin n := fun i => π ⟨i.val, by omega⟩
  let g : Fin (t + 1) → Fin n := fun i => π ⟨i.val + (n - (t + 1)), by omega⟩
  have hf : ∀ i : Fin t, f (Fin.last t) < f i.castSucc := by
    intro i
    change π ⟨t, by omega⟩ < π ⟨i.val, by omega⟩
    have hct : π ⟨t, by omega⟩ = c := by simpa only [Nat.add_sub_cancel] using hc
    rw [hct]
    by_cases hi : i.val = 0
    · have he : (⟨i.val, by omega⟩ : Fin n) = 0 := Fin.ext hi
      rw [he, ha]
      exact hca
    · have hne : PermutationEndpointZeroTwoExact.segment (n := n) 0 t (by omega) i ≠ 0 := by
        intro he
        apply hi
        have hh := congrArg Fin.val he
        simpa only [PermutationEndpointZeroTwoExact.segment, Function.Embedding.coeFn_mk,
          Nat.add_zero, Fin.val_zero] using hh
      have hh := hu i hne
      change max a.val b.val < (π ⟨i.val + 0, by omega⟩).val at hh
      simp only [Nat.add_zero] at hh
      exact lt_trans hca (lt_of_le_of_lt (le_max_left _ _) hh)
  have hg : ∀ i : Fin t, g (Fin.last t) < g i.castSucc := by
    intro i
    have he : (⟨t + (n - (t + 1)), by omega⟩ : Fin n) = ⟨n - 1, by have := NeZero.pos n; omega⟩ := by
      apply Fin.ext
      change t + (n - (t + 1)) = n - 1
      omega
    change π ⟨t + (n - (t + 1)), by omega⟩ < π ⟨i.val + (n - (t + 1)), by omega⟩
    rw [he, hb]
    exact lt_of_le_of_lt (le_max_right _ _) (hv i)
  have hcomp := comparisons_iff_castSucc f g hf hg
  convert hcomp using 1
  · rfl
  · simp only [SameOrder, PermutationEndpointZeroTwoExact.segment,
      Function.Embedding.coeFn_mk, f, g, Fin.val_castSucc, Nat.add_zero,
      Nat.add_sub_cancel]
    rfl

theorem prefix_dominant_count {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (hshort : 2 * k ≤ n)
    (a b c : Fin n) (hca : c < a) :
    let u := PermutationEndpointZeroTwoExact.segment (n := n) (n - k) (k - 1) (by omega)
    let v := PermutationEndpointZeroTwoExact.segment (n := n) 0 (k - 1) (by omega)
    let Q := fun π : Equiv.Perm (Fin n) =>
      (∀ i, max a.val b.val < (π (u i)).val) ∧
      (∀ i, v i ≠ 0 → max a.val b.val < (π (v i)).val)
    Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n) a b //
      π.val ⟨k - 1, by omega⟩ = c ∧ Q π.val} * (k - 1).factorial =
      Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨k - 1, by omega⟩ a b c // Q π.val} := by
  classical
  let u := PermutationEndpointZeroTwoExact.segment (n := n) (n - k) (k - 1) (by omega)
  let v := PermutationEndpointZeroTwoExact.segment (n := n) 0 (k - 1) (by omega)
  let q : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩
  let r : Fin n := ⟨k - 1, by omega⟩
  let Q := fun π : Equiv.Perm (Fin n) =>
    (∀ i, max a.val b.val < (π (u i)).val) ∧
    (∀ i, v i ≠ 0 → max a.val b.val < (π (v i)).val)
  change Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} * (k - 1).factorial =
    Fintype.card {π : FixedThree (0 : Fin n) q r a b c // Q π.val}
  have hd : Disjoint (Set.range u) (Set.range v) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + 0 = i.val + (n - k) at hv
    omega
  have h0 : (0 : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = 0 at hv
    omega
  have hq : q ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = n - 1 at hv
    omega
  have hr : r ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = k - 1 at hv
    omega
  have hbridge (π : Equiv.Perm (Fin n)) (ha : π 0 = a) (hb : π q = b)
      (hc : π r = c) (hgood : Q π) :
      PermutationOverlapBound.Overlap hkn π ↔ SameOrder π u v := by
    have hh := overlap_iff_high_prefix_witness hk hkn a b c hca π ha hb hc hgood.2 hgood.1
    exact hh.trans ⟨fun h i j => (h i j).symm, fun h i j => (h i j).symm⟩
  have he : Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} =
      Fintype.card {π : AgreementThree (0 : Fin n) q r a b c u v // Q π.val} := by
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨⟨π.val.val, ⟨π.val.property.1, π.property.1⟩,
        (hbridge π.val.val π.val.property.1.1 π.val.property.1.2
          π.property.1 π.property.2).mp π.val.property.2⟩, π.property.2⟩
      invFun := fun π => ⟨⟨π.val.val, π.val.property.1.1,
        (hbridge π.val.val π.val.property.1.1.1 π.val.property.1.1.2
          π.val.property.1.2 π.property).mpr π.val.property.2⟩,
        π.val.property.1.2, π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  simpa only [← Nat.card_eq_fintype_card] using
    restricted_shuffle_count 0 q r a b c u v h0 hq hr hd Q
      (fun π σ => high_invariant u v 0 (max a.val b.val) hd π σ)


theorem suffix_restricted_count {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (hshort : 2 * k ≤ n)
    (a b c : Fin n) (hcb : c < b)
    (Q : Equiv.Perm (Fin n) → Prop)
    (hQ : ∀ π σ, Q ((blockPerm
      (PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)) σ).trans π) ↔ Q π)
    (hlocal : ∀ π, Q π →
      (∀ i, max a.val b.val < (π (PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega) i)).val) ∧
      (∀ i, PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega) i ≠ ⟨n - 1, by have := NeZero.pos n; omega⟩ →
        max a.val b.val < (π (PermutationEndpointZeroTwoExact.segment (n - k + 1) (k - 1) (by omega) i)).val)) :
    Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n) a b //
      π.val ⟨n - k, by omega⟩ = c ∧ Q π.val} * (k - 1).factorial =
      Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨n - k, by omega⟩ a b c // Q π.val} := by
  classical
  let u := PermutationEndpointZeroTwoExact.segment (n := n) 1 (k - 1) (by omega)
  let v := PermutationEndpointZeroTwoExact.segment (n := n) (n - k + 1) (k - 1) (by omega)
  let q : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩
  let r : Fin n := ⟨n - k, by omega⟩
  change Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} * (k - 1).factorial =
    Fintype.card {π : FixedThree (0 : Fin n) q r a b c // Q π.val}
  have hd : Disjoint (Set.range u) (Set.range v) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + (n - k + 1) = i.val + 1 at hv
    omega
  have h0 : (0 : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = 0 at hv
    omega
  have hq : q ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - 1 at hv
    omega
  have hr : r ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + 1 = n - k at hv
    omega
  have hbridge (π : Equiv.Perm (Fin n)) (ha : π 0 = a) (hb : π q = b)
      (hc : π r = c) (hgood : Q π) :
      PermutationOverlapBound.Overlap hkn π ↔ SameOrder π u v :=
    overlap_iff_high_suffix_witness hk hkn a b c hcb π ha hb hc (hlocal π hgood).1 (hlocal π hgood).2
  have he : Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} =
      Fintype.card {π : AgreementThree (0 : Fin n) q r a b c u v // Q π.val} := by
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨⟨π.val.val, ⟨π.val.property.1, π.property.1⟩,
        (hbridge π.val.val π.val.property.1.1 π.val.property.1.2
          π.property.1 π.property.2).mp π.val.property.2⟩, π.property.2⟩
      invFun := fun π => ⟨⟨π.val.val, π.val.property.1.1,
        (hbridge π.val.val π.val.property.1.1.1 π.val.property.1.1.2
          π.val.property.1.2 π.property).mpr π.val.property.2⟩,
        π.val.property.1.2, π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  simpa only [← Nat.card_eq_fintype_card] using
    restricted_shuffle_count 0 q r a b c u v h0 hq hr hd Q
      hQ

theorem prefix_restricted_count {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkn : k < n) (hshort : 2 * k ≤ n)
    (a b c : Fin n) (hca : c < a)
    (Q : Equiv.Perm (Fin n) → Prop)
    (hQ : ∀ π σ, Q ((blockPerm
      (PermutationEndpointZeroTwoExact.segment (n := n) (n - k) (k - 1) (by omega)) σ).trans π) ↔ Q π)
    (hlocal : ∀ π, Q π →
      (∀ i, max a.val b.val < (π (PermutationEndpointZeroTwoExact.segment (n := n) (n - k) (k - 1) (by omega) i)).val) ∧
      (∀ i, PermutationEndpointZeroTwoExact.segment (n := n) 0 (k - 1) (by omega) i ≠ 0 →
        max a.val b.val < (π (PermutationEndpointZeroTwoExact.segment 0 (k - 1) (by omega) i)).val)) :
    Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n) a b //
      π.val ⟨k - 1, by omega⟩ = c ∧ Q π.val} * (k - 1).factorial =
      Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩
        ⟨k - 1, by omega⟩ a b c // Q π.val} := by
  classical
  let u := PermutationEndpointZeroTwoExact.segment (n := n) (n - k) (k - 1) (by omega)
  let v := PermutationEndpointZeroTwoExact.segment (n := n) 0 (k - 1) (by omega)
  let q : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩
  let r : Fin n := ⟨k - 1, by omega⟩
  change Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} * (k - 1).factorial =
    Fintype.card {π : FixedThree (0 : Fin n) q r a b c // Q π.val}
  have hd : Disjoint (Set.range u) (Set.range v) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + 0 = i.val + (n - k) at hv
    omega
  have h0 : (0 : Fin n) ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = 0 at hv
    omega
  have hq : q ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = n - 1 at hv
    omega
  have hr : r ∉ Set.range u := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val + (n - k) = k - 1 at hv
    omega
  have hbridge (π : Equiv.Perm (Fin n)) (ha : π 0 = a) (hb : π q = b)
      (hc : π r = c) (hgood : Q π) :
      PermutationOverlapBound.Overlap hkn π ↔ SameOrder π u v := by
    have hh := overlap_iff_high_prefix_witness hk hkn a b c hca π ha hb hc (hlocal π hgood).2 (hlocal π hgood).1
    exact hh.trans ⟨fun h i j => (h i j).symm, fun h i j => (h i j).symm⟩
  have he : Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
      π.val r = c ∧ Q π.val} =
      Fintype.card {π : AgreementThree (0 : Fin n) q r a b c u v // Q π.val} := by
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨⟨π.val.val, ⟨π.val.property.1, π.property.1⟩,
        (hbridge π.val.val π.val.property.1.1 π.val.property.1.2
          π.property.1 π.property.2).mp π.val.property.2⟩, π.property.2⟩
      invFun := fun π => ⟨⟨π.val.val, π.val.property.1.1,
        (hbridge π.val.val π.val.property.1.1.1 π.val.property.1.1.2
          π.val.property.1.2 π.property).mpr π.val.property.2⟩,
        π.val.property.1.2, π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  simpa only [← Nat.card_eq_fintype_card] using
    restricted_shuffle_count 0 q r a b c u v h0 hq hr hd Q
      hQ

theorem low_witness_two {n : ℕ} [NeZero n] (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (q : Fin n) (hq : q.val + 1 = n) (a b : Fin n) (π : PermutationEndpointOverlapBound.EventTwo hkn q a b) :
    π.val ⟨k - 1, by omega⟩ < a ∨ π.val ⟨n - k, by omega⟩ < b := by
  let x : Fin n := ⟨k - 1, by omega⟩
  have hx : x ≠ 0 := by intro h; have hv := congrArg Fin.val h; change k - 1 = 0 at hv; omega
  have hxa : π.val x ≠ a := by
    intro h
    exact hx (π.val.injective (h.trans π.property.1.1.symm))
  by_cases h : π.val x < a
  · exact Or.inl h
  · have ha : a < π.val x := lt_of_le_of_ne (le_of_not_gt h) hxa.symm
    have hc := (π.property.2 ⟨0, by omega⟩ ⟨k - 1, by omega⟩).mp
      (show π.val ⟨0, by omega⟩ < π.val ⟨k - 1, by omega⟩ by
        change π.val 0 < π.val x
        rw [π.property.1.1]
        exact ha)
    have hend : (⟨k - 1 + (n - k), by omega⟩ : Fin n) = q := by
      apply Fin.ext
      change k - 1 + (n - k) = q.val
      omega
    simpa only [Nat.zero_add, hend, π.property.1.2] using Or.inr hc


theorem two_low_union_bound {n : ℕ} {I : Type*} [Fintype I]
    (p q a b : Fin n) (r s : I → Fin n)
    (hrp : ∀ i, r i ≠ p) (hrq : ∀ i, r i ≠ q)
    (hsp : ∀ i, s i ≠ p) (hsq : ∀ i, s i ≠ q)
    (hsr : ∀ i, s i ≠ r i) (hab : a ≠ b) :
    Fintype.card {π : FixedTwo p q a b // ∃ i,
      (π.val (r i)).val ≤ max a.val b.val ∧ (π.val (s i)).val ≤ max a.val b.val} *
      (n - 3) * (n - 2) ≤
      Fintype.card I * Fintype.card (FixedTwo p q a b) * max a.val b.val * max a.val b.val := by
  classical
  let B := {π : FixedTwo p q a b // ∃ i,
      (π.val (r i)).val ≤ max a.val b.val ∧ (π.val (s i)).val ≤ max a.val b.val}
  let f : B → Σ i : I, {π : FixedTwo p q a b //
      (π.val (r i)).val ≤ max a.val b.val ∧ (π.val (s i)).val ≤ max a.val b.val} := fun π =>
    ⟨π.property.choose, π.val, π.property.choose_spec⟩
  have hf : Function.Injective f := by
    intro π ρ he
    exact Subtype.ext (congrArg (fun z => z.2.val) he)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hc
  calc
    _ ≤ (∑ i : I, Fintype.card {π : FixedTwo p q a b //
        (π.val (r i)).val ≤ max a.val b.val ∧ (π.val (s i)).val ≤ max a.val b.val}) * (n - 3) * (n - 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
    _ = ∑ i : I, Fintype.card {π : FixedTwo p q a b //
        (π.val (r i)).val ≤ max a.val b.val ∧ (π.val (s i)).val ≤ max a.val b.val} * (n - 3) * (n - 2) := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ _i : I, Fintype.card (FixedTwo p q a b) * max a.val b.val * max a.val b.val :=
      Finset.sum_le_sum (fun i _ => two_low_positions_bound p q (r i) (s i) a b
        (hrp i) (hrq i) (hsp i) (hsq i) (hsr i) hab)
    _ = _ := by simp [Nat.mul_assoc]

theorem global_bad_high_bound {n : ℕ} (p q r a b c : Fin n) (S : Finset (Fin n))
    (hSp : p ∉ S) (hSq : q ∉ S)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Fintype.card {π : FixedThree p q r a b c //
      ¬ (∀ x ∈ S, x ≠ r → max a.val b.val < (π.val x).val)} * (n - 3) ≤
      S.card * Fintype.card (FixedThree p q r a b c) * max a.val b.val := by
  classical
  let I := {x : Fin n // x ∈ S ∧ x ≠ r}
  have hc : Fintype.card I ≤ S.card := by
    have hh := Fintype.card_le_of_injective
      (fun x : I => (⟨x.val, x.property.1⟩ : S))
      (by intro x y he; exact Subtype.ext (congrArg (fun z : S => z.val) he))
    simpa using hh
  have he : Fintype.card {π : FixedThree p q r a b c //
      ¬ (∀ x ∈ S, x ≠ r → max a.val b.val < (π.val x).val)} =
      Fintype.card {π : FixedThree p q r a b c //
        ∃ i : I, (π.val i.val).val ≤ max a.val b.val} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro π
    simp only [not_forall, Classical.not_imp, not_lt]
    constructor
    · rintro ⟨x, hx, hxr, hh⟩
      exact ⟨⟨x, hx, hxr⟩, hh⟩
    · rintro ⟨x, hh⟩
      exact ⟨x.val, x.property.1, x.property.2, hh⟩
  rw [he]
  calc
    _ ≤ Fintype.card I * Fintype.card (FixedThree p q r a b c) * max a.val b.val :=
      triple_bad_union_bound p q r a b c Subtype.val
        (fun i hi => hSp (hi ▸ i.property.1))
        (fun i hi => hSq (hi ▸ i.property.1)) (fun i => i.property.2) hab hca hcb
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)

theorem isolated_union_sandwich {n : ℕ} {J : Type*} [Fintype J]
    (p q a b : Fin n) (S : Finset (Fin n)) (r : J → Fin n)
    (hr : Function.Injective r) (hrS : ∀ j, r j ∈ S)
    (U : FixedTwo p q a b → Prop) (R : J → FixedTwo p q a b → Prop)
    (hRU : ∀ j π, R j π → U π)
    (hRlow : ∀ j π, R j π → (π.val (r j)).val ≤ max a.val b.val)
    (hcover : ∀ π, U π → ∃ j, R j π) :
    let D := fun j => {π : FixedTwo p q a b // R j π ∧
      ∀ x ∈ S, x ≠ r j → max a.val b.val < (π.val x).val}
    let B := {π : FixedTwo p q a b // ∃ x ∈ S, ∃ y ∈ S,
      x ≠ y ∧ (π.val x).val ≤ max a.val b.val ∧ (π.val y).val ≤ max a.val b.val}
    (∑ j, Fintype.card (D j)) ≤ Fintype.card {π // U π} ∧
      Fintype.card {π // U π} ≤ (∑ j, Fintype.card (D j)) + Fintype.card B := by
  classical
  dsimp only
  let D := fun j => {π : FixedTwo p q a b // R j π ∧
    ∀ x ∈ S, x ≠ r j → max a.val b.val < (π.val x).val}
  let B := {π : FixedTwo p q a b // ∃ x ∈ S, ∃ y ∈ S,
    x ≠ y ∧ (π.val x).val ≤ max a.val b.val ∧ (π.val y).val ≤ max a.val b.val}
  let f : (Σ j, D j) → {π // U π} := fun z => ⟨z.2.val, hRU z.1 z.2.val z.2.property.1⟩
  have hf : Function.Injective f := by
    rintro ⟨i, π⟩ ⟨j, ρ⟩ he
    have hπρ : π.val = ρ.val := congrArg (fun z => z.val) he
    have hij : i = j := by
      apply hr
      by_contra hne
      have hlo := hRlow j ρ.val ρ.property.1
      have hhi := π.property.2 (r j) (hrS j) (Ne.symm hne)
      rw [hπρ] at hhi
      exact (not_lt_of_ge hlo) hhi
    subst j
    exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq (Subtype.ext hπρ)⟩
  have hdecomp (π : FixedTwo p q a b) (hU : U π) :
      (∃ z : Σ j, D j, z.2.val = π) ∨
        (∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
          (π.val x).val ≤ max a.val b.val ∧ (π.val y).val ≤ max a.val b.val) := by
    obtain ⟨j, hj⟩ := hcover π hU
    by_cases hg : ∀ x ∈ S, x ≠ r j → max a.val b.val < (π.val x).val
    · exact Or.inl ⟨⟨j, π, hj, hg⟩, rfl⟩
    · simp only [not_forall, Classical.not_imp, not_lt] at hg
      obtain ⟨x, hx, hxr, hlow⟩ := hg
      exact Or.inr ⟨x, hx, r j, hrS j, hxr, hlow, hRlow j π hj⟩
  let g : {π // U π} → (Σ j, D j) ⊕ B := fun π =>
    if h : ∃ z : Σ j, D j, z.2.val = π.val then Sum.inl h.choose
    else Sum.inr ⟨π.val, (hdecomp π.val π.property).resolve_left h⟩
  have hgval (π : {π // U π}) :
      Sum.elim (fun z : Σ j, D j => z.2.val) (fun z : B => z.val) (g π) = π.val := by
    dsimp only [g]
    split
    · rename_i h
      exact h.choose_spec
    · rfl
  have hg : Function.Injective g := by
    intro π ρ he
    apply Subtype.ext
    calc
      π.val = _ := (hgval π).symm
      _ = _ := congrArg (Sum.elim (fun z : Σ j, D j => z.2.val) (fun z : B => z.val)) he
      _ = ρ.val := hgval ρ
  constructor
  · simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective f hf
  · simpa only [Fintype.card_sum, Fintype.card_sigma] using Fintype.card_le_of_injective g hg

/-- Free positions in all prefix and suffix windows of length at most K. -/
def lowPositions (n K : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x => (1 ≤ x.val ∧ x.val < K) ∨
    (n - K ≤ x.val ∧ x.val + 1 < n))

example (n K : ℕ) (x : Fin n) : x ∈ lowPositions n K ↔
    (1 ≤ x.val ∧ x.val < K) ∨ (n - K ≤ x.val ∧ x.val + 1 < n) := by
  simp [lowPositions]

/-- The tagged boundary witness position for a short overlap. -/
def witnessPosition {n K : ℕ} (h : 2 * K ≤ n) :
    (Set.Icc (2 : ℕ) K ⊕ Set.Icc (2 : ℕ) K) → Fin n
  | Sum.inl k => ⟨k.val - 1, by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega⟩
  | Sum.inr k => ⟨n - k.val, by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega⟩

example {n K : ℕ} (h : 2 * K ≤ n) (k : Set.Icc (2 : ℕ) K) :
    (witnessPosition h (Sum.inl k)).val = k.val - 1 ∧
      (witnessPosition h (Sum.inr k)).val = n - k.val := ⟨rfl, rfl⟩

/-- All tagged witness positions are distinct when the two K-windows are disjoint. -/
theorem witnessPosition_injective {n K : ℕ} (h : 2 * K ≤ n) :
    Function.Injective (witnessPosition h) := by
  intro i j he
  have hv := congrArg Fin.val he
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      congr 1
      apply Subtype.ext
      have hi : 2 ≤ i.val ∧ i.val ≤ K := i.property
      have hj : 2 ≤ j.val ∧ j.val ≤ K := j.property
      change i.val - 1 = j.val - 1 at hv
      omega
    | inr j =>
      have hi : 2 ≤ i.val ∧ i.val ≤ K := i.property
      have hj : 2 ≤ j.val ∧ j.val ≤ K := j.property
      change i.val - 1 = n - j.val at hv
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hi : 2 ≤ i.val ∧ i.val ≤ K := i.property
      have hj : 2 ≤ j.val ∧ j.val ≤ K := j.property
      change n - i.val = j.val - 1 at hv
      omega
    | inr j =>
      congr 1
      apply Subtype.ext
      have hi : 2 ≤ i.val ∧ i.val ≤ K := i.property
      have hj : 2 ≤ j.val ∧ j.val ≤ K := j.property
      change n - i.val = n - j.val at hv
      omega

/-- Every short-length witness is a free position, with both anchors excluded. -/
theorem witnessPosition_mem {n K : ℕ} (h : 2 * K ≤ n)
    (j : Set.Icc (2 : ℕ) K ⊕ Set.Icc (2 : ℕ) K) :
    witnessPosition h j ∈ lowPositions n K := by
  cases j with
  | inl k =>
    have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property
    simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and, witnessPosition]
    exact Or.inl ⟨by omega, by omega⟩
  | inr k =>
    have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property
    simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and, witnessPosition]
    exact Or.inr ⟨by omega, by omega⟩

/-- Neither endpoint belongs to the free-position set for disjoint K-windows. -/
theorem lowPositions_anchors {n K : ℕ} [NeZero n] (h : 2 * K ≤ n) :
    (0 : Fin n) ∉ lowPositions n K ∧ (⟨n - 1, by have := NeZero.pos n; omega⟩ : Fin n) ∉ lowPositions n K := by
  have hn : 0 < n := NeZero.pos n
  simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]
  constructor <;> omega

/-- At most 2K free positions occur in the two short windows. -/
theorem card_lowPositions_le (n K : ℕ) : (lowPositions n K).card ≤ 2 * K := by
  classical
  let f : (lowPositions n K) → Fin K ⊕ Fin K := fun x =>
    if h : x.val.val < K then Sum.inl ⟨x.val.val, h⟩
    else Sum.inr ⟨n - 1 - x.val.val, by
      have hx := (Finset.mem_filter.mp x.property).2
      have hn := x.val.isLt
      omega⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Fin.ext
    have hx := x.val.isLt
    have hy := y.val.isLt
    dsimp only [f] at he
    split at he <;> split at he
    · have hh := congrArg (fun z : Fin K ⊕ Fin K => z.elim Fin.val Fin.val) he
      exact hh
    · contradiction
    · contradiction
    · have hh := congrArg (fun z : Fin K ⊕ Fin K => z.elim Fin.val Fin.val) he
      change n - 1 - x.val.val = n - 1 - y.val.val at hh
      omega
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_sum, two_mul] using hc

/-- The actual union of overlaps from length two through K in the endpoint fiber. -/
def shortUnion {n K : ℕ} [NeZero n] (h : 2 * K ≤ n) (a b : Fin n)
    (π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b) : Prop :=
  ∃ k : Set.Icc (2 : ℕ) K,
    PermutationOverlapBound.Overlap (by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega : k.val < n) π.val

example {n K : ℕ} [NeZero n] (h : 2 * K ≤ n) (a b : Fin n)
    (π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b) : shortUnion h a b π ↔
    ∃ k : Set.Icc (2 : ℕ) K,
      PermutationOverlapBound.Overlap (by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega : k.val < n) π.val := Iff.rfl

/-- A short overlap together with its tagged boundary low-label witness. -/
def taggedLowOverlap {n K : ℕ} [NeZero n] (h : 2 * K ≤ n) (a b : Fin n)
    (j : Set.Icc (2 : ℕ) K ⊕ Set.Icc (2 : ℕ) K)
    (π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b) : Prop :=
  match j with
  | Sum.inl k => PermutationOverlapBound.Overlap
      (by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega : k.val < n) π.val ∧
      π.val (witnessPosition h (Sum.inl k)) < a
  | Sum.inr k => PermutationOverlapBound.Overlap
      (by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega : k.val < n) π.val ∧
      π.val (witnessPosition h (Sum.inr k)) < b

example {n K : ℕ} [NeZero n] (h : 2 * K ≤ n) (a b : Fin n)
    (k : Set.Icc (2 : ℕ) K)
    (π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b) :
    taggedLowOverlap h a b (Sum.inl k) π ↔
      PermutationOverlapBound.Overlap (by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega : k.val < n) π.val ∧
        π.val (witnessPosition h (Sum.inl k)) < a := Iff.rfl

/-- The actual finite union is squeezed by disjoint isolated-low events and one global two-low error. -/
theorem actual_short_union_sandwich {n K : ℕ} [NeZero n]
    (h : 2 * K ≤ n) (a b : Fin n) :
    let S := lowPositions n K
    let D := fun j => {π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b //
      taggedLowOverlap h a b j π ∧
        ∀ x ∈ S, x ≠ witnessPosition h j → max a.val b.val < (π.val x).val}
    let B := {π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b //
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ (π.val x).val ≤ max a.val b.val ∧
        (π.val y).val ≤ max a.val b.val}
    (∑ j, Fintype.card (D j)) ≤ Fintype.card {π // shortUnion h a b π} ∧
      Fintype.card {π // shortUnion h a b π} ≤
        (∑ j, Fintype.card (D j)) + Fintype.card B := by
  apply isolated_union_sandwich (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b
    (lowPositions n K) (witnessPosition h) (witnessPosition_injective h)
    (witnessPosition_mem h) (shortUnion h a b) (taggedLowOverlap h a b)
  · intro j π hj
    cases j with
    | inl k => exact ⟨k, hj.1⟩
    | inr k => exact ⟨k, hj.1⟩
  · intro j π hj
    cases j with
    | inl k => exact le_trans hj.2.le (le_max_left _ _)
    | inr k => exact le_trans hj.2.le (le_max_right _ _)
  · intro π hπ
    obtain ⟨k, hk⟩ := hπ
    have hkn : k.val < n := by have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega
    have hw := low_witness_two k.val k.property.1 hkn ⟨n - 1, by have := NeZero.pos n; omega⟩
      (by simp only; omega) a b ⟨π.val, π.property, hk⟩
    rcases hw with hw | hw
    · exact ⟨Sum.inl k, hk, hw⟩
    · exact ⟨Sum.inr k, hk, hw⟩

/-- The global two-low residual is bounded by the square of the free-position count. -/
theorem global_two_low_bound {n : ℕ} (p q a b : Fin n) (S : Finset (Fin n))
    (hSp : p ∉ S) (hSq : q ∉ S) (hab : a ≠ b) :
    Fintype.card {π : FixedTwo p q a b // ∃ x ∈ S, ∃ y ∈ S,
      x ≠ y ∧ (π.val x).val ≤ max a.val b.val ∧ (π.val y).val ≤ max a.val b.val} *
      (n - 3) * (n - 2) ≤
      S.card * S.card * Fintype.card (FixedTwo p q a b) * max a.val b.val * max a.val b.val := by
  classical
  let I := {z : S × S // z.1.val ≠ z.2.val}
  have hc : Fintype.card I ≤ S.card * S.card := by
    have hh := Fintype.card_subtype_le (fun z : S × S => z.1.val ≠ z.2.val)
    simpa only [Fintype.card_prod, Fintype.card_coe] using hh
  have he : Fintype.card {π : FixedTwo p q a b // ∃ x ∈ S, ∃ y ∈ S,
      x ≠ y ∧ (π.val x).val ≤ max a.val b.val ∧ (π.val y).val ≤ max a.val b.val} =
      Fintype.card {π : FixedTwo p q a b // ∃ z : I,
        (π.val z.val.1.val).val ≤ max a.val b.val ∧
          (π.val z.val.2.val).val ≤ max a.val b.val} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro π
    constructor
    · rintro ⟨x, hx, y, hy, hxy, hlx, hly⟩
      exact ⟨⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩, hlx, hly⟩
    · rintro ⟨z, hlx, hly⟩
      exact ⟨z.val.1.val, z.val.1.property, z.val.2.val, z.val.2.property, z.property, hlx, hly⟩
  rw [he]
  calc
    _ ≤ Fintype.card I * Fintype.card (FixedTwo p q a b) * max a.val b.val * max a.val b.val :=
      two_low_union_bound p q a b (fun z : I => z.val.1.val) (fun z => z.val.2.val)
        (fun z he => hSp (he ▸ z.val.1.property))
        (fun z he => hSq (he ▸ z.val.1.property))
        (fun z he => hSp (he ▸ z.val.2.property))
        (fun z he => hSq (he ▸ z.val.2.property))
        (fun z => z.property.symm) hab
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))

/-- The suffix witness slice remains exactly countable after excluding all other short-window lows. -/
theorem suffix_global_count {n k K : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkK : k ≤ K) (hshort : 2 * K ≤ n) (hkn : k < n)
    (a b c : Fin n) (hcb : c < b) :
    let r : Fin n := ⟨n - k, by omega⟩
    let Q := fun π : Equiv.Perm (Fin n) =>
      ∀ x ∈ lowPositions n K, x ≠ r → max a.val b.val < (π x).val
    Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by omega⟩ : Fin n) a b // π.val r = c ∧ Q π.val} * (k - 1).factorial =
      Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by omega⟩ r a b c // Q π.val} := by
  classical
  dsimp only
  have hh := suffix_restricted_count hk hkn (by omega) a b c hcb
    (fun π => ∀ x ∈ lowPositions n K, x ≠ ⟨n - k, by omega⟩ →
      max a.val b.val < (π x).val)
  simp only [← Nat.card_eq_fintype_card] at hh ⊢
  apply hh
  · intro π σ
    apply global_high_invariant
    · intro i
      have hi := i.isLt
      simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      change (1 ≤ i.val + 1 ∧ i.val + 1 < K) ∨
          (n - K ≤ i.val + 1 ∧ i.val + 1 + 1 < n)
      exact Or.inl ⟨by omega, by omega⟩
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      have hit := i.isLt
      change i.val + 1 = n - k at hv
      omega
  · intro π hQ
    constructor
    · intro i
      have hi := i.isLt
      apply hQ
      · simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        change (1 ≤ i.val + 1 ∧ i.val + 1 < K) ∨
          (n - K ≤ i.val + 1 ∧ i.val + 1 + 1 < n)
        exact Or.inl ⟨by omega, by omega⟩
      · intro he
        have hv := congrArg Fin.val he
        change i.val + 1 = n - k at hv
        omega
    · intro i hne
      have hi := i.isLt
      have hneval : i.val + (n - k + 1) ≠ n - 1 := by
        intro he
        apply hne
        exact Fin.ext he
      apply hQ
      · simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        change (1 ≤ i.val + (n - k + 1) ∧ i.val + (n - k + 1) < K) ∨
          (n - K ≤ i.val + (n - k + 1) ∧ i.val + (n - k + 1) + 1 < n)
        exact Or.inr ⟨by omega, by omega⟩
      · intro he
        have hv := congrArg Fin.val he
        change i.val + (n - k + 1) = n - k at hv
        omega

/-- The prefix witness slice remains exactly countable after excluding all other short-window lows. -/
theorem prefix_global_count {n k K : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkK : k ≤ K) (hshort : 2 * K ≤ n) (hkn : k < n)
    (a b c : Fin n) (hca : c < a) :
    let r : Fin n := ⟨k - 1, by omega⟩
    let Q := fun π : Equiv.Perm (Fin n) =>
      ∀ x ∈ lowPositions n K, x ≠ r → max a.val b.val < (π x).val
    Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
        (⟨n - 1, by omega⟩ : Fin n) a b // π.val r = c ∧ Q π.val} * (k - 1).factorial =
      Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by omega⟩ r a b c // Q π.val} := by
  classical
  dsimp only
  have hh := prefix_restricted_count hk hkn (by omega) a b c hca
    (fun π => ∀ x ∈ lowPositions n K, x ≠ ⟨k - 1, by omega⟩ →
      max a.val b.val < (π x).val)
  simp only [← Nat.card_eq_fintype_card] at hh ⊢
  apply hh
  · intro π σ
    apply global_high_invariant
    · intro i
      have hi := i.isLt
      simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      change (1 ≤ i.val + (n - k) ∧ i.val + (n - k) < K) ∨
          (n - K ≤ i.val + (n - k) ∧ i.val + (n - k) + 1 < n)
      exact Or.inr ⟨by omega, by omega⟩
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      have hit := i.isLt
      change i.val + (n - k) = k - 1 at hv
      omega
  · intro π hQ
    constructor
    · intro i
      have hi := i.isLt
      apply hQ
      · simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        change (1 ≤ i.val + (n - k) ∧ i.val + (n - k) < K) ∨
          (n - K ≤ i.val + (n - k) ∧ i.val + (n - k) + 1 < n)
        exact Or.inr ⟨by omega, by omega⟩
      · intro he
        have hv := congrArg Fin.val he
        change i.val + (n - k) = k - 1 at hv
        omega
    · intro i hne
      have hi := i.isLt
      have hneval : i.val ≠ 0 := by
        intro he
        apply hne
        apply Fin.ext
        change i.val + 0 = 0
        omega
      apply hQ
      · simp only [lowPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        change (1 ≤ i.val + 0 ∧ i.val + 0 < K) ∨
          (n - K ≤ i.val + 0 ∧ i.val + 0 + 1 < n)
        exact Or.inl ⟨by omega, by omega⟩
      · intro he
        have hv := congrArg Fin.val he
        change i.val + 0 = k - 1 at hv
        omega

theorem card_label_slices {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (P : β → Prop) (Q : α → Prop) :
    Fintype.card {x : α // P (f x) ∧ Q x} =
      ∑ c : {c : β // P c}, Fintype.card {x : α // f x = c.val ∧ Q x} := by
  classical
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨⟨f x.val, x.property.1⟩, x.val, rfl, x.property.2⟩
    invFun := fun x => ⟨x.2.val, x.2.property.1.symm ▸ x.1.property, x.2.property.2⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨c, hc⟩, x, he, hx⟩; cases he; rfl }

theorem aggregate_dominant_bounds {I : Type*} [Fintype I]
    (D T G : I → ℕ) (f N H d M F : ℕ)
    (hDG : ∀ i, D i * f = G i)
    (hGT : ∀ i, G i ≤ T i)
    (hTN : ∀ i, T i * N = F)
    (hbad : ∀ i, (T i - G i) * H ≤ d * T i * M) :
    (∑ i, D i) * f * N ≤ Fintype.card I * F ∧
      (Fintype.card I * F - (∑ i, D i) * f * N) * H ≤
        d * (Fintype.card I * F) * M := by
  classical
  have hsum : (∑ i, D i) * f = ∑ i, G i := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => hDG i)
  have hT : (∑ i, T i) * N = Fintype.card I * F := by
    rw [Finset.sum_mul]
    simp only [hTN, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hGTsum : ∑ i, G i ≤ ∑ i, T i := Finset.sum_le_sum (fun i _ => hGT i)
  rw [hsum]
  constructor
  · rw [← hT]
    exact Nat.mul_le_mul_right _ hGTsum
  · rw [← hT, ← Nat.sub_mul, ← Finset.sum_tsub_distrib Finset.univ
      (fun i _ => hGT i), Finset.sum_mul, Finset.sum_mul]
    calc
      _ ≤ ∑ i, (d * T i * M) * N := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Nat.mul_right_comm] using Nat.mul_le_mul_right N (hbad i)
      _ = d * ((∑ i, T i) * N) * M := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl

/-- Summing the actual globally isolated slices gives the a+b−1 leading coefficient. -/
theorem global_dominant_sum_bounds {n k K : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hkK : k ≤ K) (hshort : 2 * K ≤ n) (hkn : k < n)
    (a b : Fin n) (hab : a ≠ b) :
    let W := {c : Fin n // c < a ∧ c ≠ b} ⊕ {c : Fin n // c < b ∧ c ≠ a}
    let r : W → Fin n := Sum.elim (fun _ => ⟨k - 1, by omega⟩) (fun _ => ⟨n - k, by omega⟩)
    let c : W → Fin n := Sum.elim Subtype.val Subtype.val
    let Q := fun w (π : Equiv.Perm (Fin n)) =>
      ∀ x ∈ lowPositions n K, x ≠ r w → max a.val b.val < (π x).val
    let C := ∑ w : W, Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
      (⟨n - 1, by omega⟩ : Fin n) a b // π.val (r w) = c w ∧ Q w π.val}
    let F := Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b)
    C * (k - 1).factorial * (n - 2) ≤ (a.val + b.val - 1) * F ∧
      ((a.val + b.val - 1) * F - C * (k - 1).factorial * (n - 2)) * (n - 3) ≤
        (lowPositions n K).card * ((a.val + b.val - 1) * F) * max a.val b.val := by
  classical
  dsimp only
  let W := {c : Fin n // c < a ∧ c ≠ b} ⊕ {c : Fin n // c < b ∧ c ≠ a}
  let r : W → Fin n := Sum.elim (fun _ => ⟨k - 1, by omega⟩) (fun _ => ⟨n - k, by omega⟩)
  let c : W → Fin n := Sum.elim Subtype.val Subtype.val
  let Q := fun w (π : Equiv.Perm (Fin n)) =>
    ∀ x ∈ lowPositions n K, x ≠ r w → max a.val b.val < (π x).val
  let D := fun w => Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn
    (⟨n - 1, by omega⟩ : Fin n) a b // π.val (r w) = c w ∧ Q w π.val}
  let T := fun w => Fintype.card (FixedThree (0 : Fin n) ⟨n - 1, by omega⟩ (r w) a b (c w))
  let G := fun w => Fintype.card {π : FixedThree (0 : Fin n) ⟨n - 1, by omega⟩ (r w) a b (c w) // Q w π.val}
  have hca (w : W) : c w ≠ a := by
    cases w with
    | inl w => exact ne_of_lt w.property.1
    | inr w => exact w.property.2
  have hcb (w : W) : c w ≠ b := by
    cases w with
    | inl w => exact w.property.2
    | inr w => exact ne_of_lt w.property.1
  have hDG (w : W) : D w * (k - 1).factorial = G w := by
    cases w with
    | inl w => exact prefix_global_count hk hkK hshort hkn a b w.val w.property.1
    | inr w => exact suffix_global_count hk hkK hshort hkn a b w.val w.property.1
  have hGT (w : W) : G w ≤ T w := Fintype.card_subtype_le _
  have hTN (w : W) : T w * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b) := by
    apply card_fixedThree_mul
    · cases w <;> intro he <;> have hv := congrArg Fin.val he <;>
        dsimp only [r, Sum.elim_inl, Sum.elim_inr, Fin.val_zero] at hv <;> omega
    · cases w <;> intro he <;> have hv := congrArg Fin.val he <;>
        dsimp only [r, Sum.elim_inl, Sum.elim_inr] at hv <;> omega
    · exact hab
    · exact hca w
    · exact hcb w
  have hbad (w : W) : (T w - G w) * (n - 3) ≤
      (lowPositions n K).card * T w * max a.val b.val := by
    have hb := global_bad_high_bound (0 : Fin n) ⟨n - 1, by omega⟩ (r w) a b (c w)
      (lowPositions n K) (lowPositions_anchors hshort).1 (lowPositions_anchors hshort).2 hab (hca w) (hcb w)
    rw [Fintype.card_subtype_compl] at hb
    exact hb
  have hh := aggregate_dominant_bounds D T G (k - 1).factorial (n - 2) (n - 3)
    (lowPositions n K).card (max a.val b.val)
    (Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b)) hDG hGT hTN hbad
  rw [PermutationLowEndpointEventBound.card_low_labels a b hab] at hh
  exact hh

/-- An isolated low event decomposes into its distinct prescribed label slices. -/
theorem card_isolated_label_slices {n k : ℕ} [NeZero n] (hkn : k < n)
    (q a b r x y : Fin n) (Q : Equiv.Perm (Fin n) → Prop)
    (hy : ∀ π : FixedTwo (0 : Fin n) q a b, π.val r ≠ y) :
    Fintype.card {π : FixedTwo (0 : Fin n) q a b //
      (PermutationOverlapBound.Overlap hkn π.val ∧ π.val r < x) ∧ Q π.val} =
      ∑ c : {c : Fin n // c < x ∧ c ≠ y},
        Fintype.card {π : PermutationEndpointOverlapBound.EventTwo hkn q a b //
          π.val r = c.val ∧ Q π.val} := by
  classical
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun := fun π => ⟨⟨π.val.val r, π.property.1.2, hy π.val⟩,
      ⟨π.val.val, π.val.property, π.property.1.1⟩, rfl, π.property.2⟩
    invFun := fun z => ⟨⟨z.2.val.val, z.2.val.property.1⟩,
      ⟨z.2.val.property.2, z.2.property.1.symm ▸ z.1.property.1⟩, z.2.property.2⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨c, hc⟩, ⟨π, hπ⟩, he, hQ⟩; cases he; rfl }

/-- The two actual isolated events at each short length have the correct combined leading coefficient. -/
theorem isolated_pair_bounds {n K : ℕ} [NeZero n] (hshort : 2 * K ≤ n)
    (a b : Fin n) (hab : a ≠ b) (k : Set.Icc (2 : ℕ) K) :
    let D := fun j => Fintype.card {π : FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b //
      taggedLowOverlap hshort a b j π ∧
        ∀ x ∈ lowPositions n K, x ≠ witnessPosition hshort j → max a.val b.val < (π.val x).val}
    let C := D (Sum.inl k) + D (Sum.inr k)
    let F := Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by have := NeZero.pos n; omega⟩ a b)
    C * (k.val - 1).factorial * (n - 2) ≤ (a.val + b.val - 1) * F ∧
      ((a.val + b.val - 1) * F - C * (k.val - 1).factorial * (n - 2)) * (n - 3) ≤
        (lowPositions n K).card * ((a.val + b.val - 1) * F) * max a.val b.val := by
  classical
  have hk : 2 ≤ k.val ∧ k.val ≤ K := k.property
  have hkn : k.val < n := by omega
  let q : Fin n := ⟨n - 1, by omega⟩
  let rp : Fin n := ⟨k.val - 1, by omega⟩
  let rs : Fin n := ⟨n - k.val, by omega⟩
  let Qp := fun π : Equiv.Perm (Fin n) => ∀ x ∈ lowPositions n K,
    x ≠ rp → max a.val b.val < (π x).val
  let Qs := fun π : Equiv.Perm (Fin n) => ∀ x ∈ lowPositions n K,
    x ≠ rs → max a.val b.val < (π x).val
  have hpre := card_isolated_label_slices hkn q a b rp a b Qp (by
    intro π he
    have hr := π.val.injective (he.trans π.property.2.symm)
    have hv := congrArg Fin.val hr
    change k.val - 1 = n - 1 at hv
    omega)
  have hsuf := card_isolated_label_slices hkn q a b rs b a Qs (by
    intro π he
    have hr := π.val.injective (he.trans π.property.1.symm)
    have hv := congrArg Fin.val hr
    change n - k.val = 0 at hv
    omega)
  have hh := global_dominant_sum_bounds hk.1 hk.2 hshort hkn a b hab
  simp only [← Nat.card_eq_fintype_card] at hpre hsuf hh ⊢
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hh
  rw [← hpre, ← hsuf] at hh
  exact hh

/-- Positive normalization converts the exact count deficit into a relative first-order error. -/
theorem normalized_count_bounds (C f N H A F d M t : ℝ)
    (hf : 0 < f) (hN : 0 < N) (hH : 0 < H) (hA : 0 < A) (hF : 0 < F)
    (ht : 0 ≤ t) (hupper : C * f * N ≤ A * F)
    (hbad : (A * F - C * f * N) * H ≤ d * (A * F) * M) :
    t / N * (1 / f) * (1 - d * M / H) ≤ t / A * (C / F) ∧
      t / A * (C / F) ≤ t / N * (1 / f) := by
  have hlow : A * F * (H - d * M) ≤ C * f * N * H := by nlinarith [hbad]
  have heC : t / A * (C / F) = t * C / (A * F) := by ring
  have heU : t / N * (1 / f) = t / (N * f) := by ring
  have heL : t / N * (1 / f) * (1 - d * M / H) =
      t * (H - d * M) / (N * f * H) := by
    field_simp
    <;> ring
  rw [heC, heL, heU]
  constructor
  · apply (div_le_div_iff₀ (mul_pos (mul_pos hN hf) hH) (mul_pos hA hF)).mpr
    have hh := mul_le_mul_of_nonneg_left hlow ht
    nlinarith only [hh]
  · apply (div_le_div_iff₀ (mul_pos hA hF) (mul_pos hN hf)).mpr
    have hh := mul_le_mul_of_nonneg_left hupper ht
    nlinarith only [hh]

/-- Each actual isolated length pair has a normalized error controlled by the global free-position low density. -/
theorem isolated_pair_normalized {n K : ℕ} [NeZero n] (hn : 4 ≤ n)
    (hshort : 2 * K ≤ n) (a b : Fin n) (hab : a ≠ b)
    (hA : 1 ≤ a.val + b.val - 1) (k : Set.Icc (2 : ℕ) K) :
    let D := fun j => Fintype.card {π : FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b //
      taggedLowOverlap hshort a b j π ∧
        ∀ x ∈ lowPositions n K, x ≠ witnessPosition hshort j → max a.val b.val < (π.val x).val}
    let C := D (Sum.inl k) + D (Sum.inr k)
    let F := Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b)
    let Z := (n : ℝ) / (a.val + b.val - 1 : ℕ) * ((C : ℝ) / F)
    let L := (n : ℝ) / (n - 2 : ℕ) * (1 / ((k.val - 1).factorial : ℝ))
    L * (1 - ((lowPositions n K).card : ℝ) * max a.val b.val / (n - 3 : ℕ)) ≤ Z ∧ Z ≤ L := by
  classical
  dsimp only
  let D := fun j => Fintype.card {π : FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b //
    taggedLowOverlap hshort a b j π ∧
      ∀ x ∈ lowPositions n K, x ≠ witnessPosition hshort j → max a.val b.val < (π.val x).val}
  let C := D (Sum.inl k) + D (Sum.inr k)
  let F := Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b)
  have hc := isolated_pair_bounds hshort a b hab k
  change C * (k.val - 1).factorial * (n - 2) ≤ (a.val + b.val - 1) * F ∧
    ((a.val + b.val - 1) * F - C * (k.val - 1).factorial * (n - 2)) * (n - 3) ≤
      (lowPositions n K).card * ((a.val + b.val - 1) * F) * max a.val b.val at hc
  have hupper : (C : ℝ) * (k.val - 1).factorial * (n - 2 : ℕ) ≤
      (a.val + b.val - 1 : ℕ) * (F : ℝ) := by exact_mod_cast hc.1
  have hbad : (((a.val + b.val - 1 : ℕ) : ℝ) * F -
      (C : ℝ) * (k.val - 1).factorial * (n - 2 : ℕ)) * (n - 3 : ℕ) ≤
      ((lowPositions n K).card : ℝ) * (((a.val + b.val - 1 : ℕ) : ℝ) * F) * max a.val b.val := by
    have hh : (((a.val + b.val - 1) * F - C * (k.val - 1).factorial * (n - 2)) * (n - 3) : ℕ) ≤
        (lowPositions n K).card * ((a.val + b.val - 1) * F) * max a.val b.val := hc.2
    have hcast : ((((a.val + b.val - 1) * F - C * (k.val - 1).factorial * (n - 2)) * (n - 3) : ℕ) : ℝ) ≤
        (((lowPositions n K).card * ((a.val + b.val - 1) * F) * max a.val b.val : ℕ) : ℝ) := by exact_mod_cast hh
    rw [Nat.cast_mul, Nat.cast_sub hc.1] at hcast
    simpa only [Nat.cast_mul] using hcast
  letI : Nonempty (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a b) :=
    fixedTwo_nonempty 0 ⟨n - 1, by omega⟩ a b
      (by intro he; have hv := congrArg Fin.val he; change 0 = n - 1 at hv; omega) hab
  have hF : (0 : ℝ) < F := by exact_mod_cast Fintype.card_pos
  simpa only [Nat.cast_max] using normalized_count_bounds C (k.val - 1).factorial (n - 2 : ℕ) (n - 3 : ℕ)
    (a.val + b.val - 1 : ℕ) F (lowPositions n K).card ((max a.val b.val : ℕ) : ℝ) n
    (by positivity) (by exact_mod_cast (show 0 < n - 2 by omega))
    (by exact_mod_cast (show 0 < n - 3 by omega))
    (by exact_mod_cast (show 0 < a.val + b.val - 1 by omega)) hF (by positivity) hupper hbad

open PermutationEndpointOverlapTail

/-- The actual full-F deficit lies between its finite short union and that union plus the actual long tail. -/
theorem actual_F_short_sandwich {n K : ℕ} [NeZero n]
    (hn : 2 ≤ n) (hshort : 2 * K ≤ n) (a b : Fin n) (hab : a ≠ b) :
    let q : Fin n := ⟨n - 1, by omega⟩
    let F := (Fintype.card (FixedTwo (0 : Fin n) q a b) : ℝ)
    let S := (Fintype.card {π // shortUnion hshort a b π} : ℝ) / F
    S ≤ 1 - PermutationSameEdgeLimit.F n a.val b.val ∧
      1 - PermutationSameEdgeLimit.F n a.val b.val ≤ S +
        ((longOverlapTwoFinset (K + 1) q a b).card : ℝ) / F := by
  classical
  let q : Fin n := ⟨n - 1, by omega⟩
  let E := fun π : FixedTwo (0 : Fin n) q a b =>
    ∃ k, 2 ≤ k ∧ ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val
  let L := LongOverlapTwo (K + 1) q a b
  have hlo : Fintype.card {π // shortUnion hshort a b π} ≤ Fintype.card {π // E π} := by
    apply Fintype.card_subtype_mono
    intro π hπ
    obtain ⟨k, hk⟩ := hπ
    exact ⟨k.val, k.property.1, by have hkp : 2 ≤ k.val ∧ k.val ≤ K := k.property; omega, hk⟩
  have hhi : Fintype.card {π // E π} ≤
      Fintype.card {π // shortUnion hshort a b π} + Fintype.card {π // L π} := by
    calc
      _ ≤ Fintype.card {π // shortUnion hshort a b π ∨ L π} := by
        apply Fintype.card_subtype_mono
        intro π hπ
        obtain ⟨k, hk2, hkn, hk⟩ := hπ
        by_cases hkK : k ≤ K
        · exact Or.inl ⟨⟨k, hk2, hkK⟩, hk⟩
        · exact Or.inr ⟨k, by omega, hkn, hk⟩
      _ ≤ _ := Fintype.card_subtype_or _ _
  have hL : Fintype.card {π // L π} = (longOverlapTwoFinset (K + 1) q a b).card := by
    apply Fintype.card_of_subtype
    intro π
    exact mem_longOverlapTwoFinset (K + 1) q a b π
  have habv : a.val ≠ b.val := by intro he; exact hab (Fin.ext he)
  letI := PermutationSameEdgeLimit.terminal_fiber_nonempty hn a.isLt b.isLt habv
  have hp : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q a b) := by
    exact_mod_cast Fintype.card_pos
  have he : 1 - PermutationSameEdgeLimit.F n a.val b.val =
      (Fintype.card {π // E π} : ℝ) / Fintype.card (FixedTwo (0 : Fin n) q a b) := by
    rw [PermutationSameEdgeLimit.F_eq_actual hn a.isLt b.isLt habv]
    apply (eq_div_iff hp.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hp.ne']
    have hc := PermutationSameEdgeAvoidance.card_avoidTwo_add_card_overlap q a b
    have hcr : (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) : ℝ) +
        Fintype.card {π // E π} = Fintype.card (FixedTwo (0 : Fin n) q a b) := by exact_mod_cast hc
    linarith
  dsimp only
  rw [he]
  constructor
  · apply div_le_div_of_nonneg_right _ hp.le
    exact_mod_cast hlo
  · rw [← add_div]
    apply div_le_div_of_nonneg_right _ hp.le
    rw [hL] at hhi
    exact_mod_cast hhi

/-- The shifted factorial weight inherited from one-low capture has a uniform vanishing tail. -/
theorem sum_shifted_factorial_tail (K N : ℕ) (hK : 6 ≤ K) :
    ∑ k ∈ Finset.Ico K N, (1 : ℝ) / (k / 3 - 1).factorial ≤
      6 / ((K - 3) / 3).factorial := by
  have he : (∑ k ∈ Finset.Ico K N, (1 : ℝ) / (k / 3 - 1).factorial) =
      ∑ j ∈ Finset.Ico (K - 3) (N - 3), (1 : ℝ) / (j / 3).factorial := by
    apply Finset.sum_bij (fun k _ => k - 3)
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk l hl he
      simp only [Finset.mem_Ico] at hk hl
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      refine ⟨j + 3, ?_, by omega⟩
      simp only [Finset.mem_Ico]
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hd : k / 3 - 1 = (k - 3) / 3 := by omega
      rw [hd]
  rw [he]
  exact PermutationEndpointOverlapTail.sum_Ico_le (K - 3) (N - 3) (by omega)

open PermutationEndpointOverlapTail

private noncomputable def overlapFinset {n : ℕ} [NeZero n] (q m l : Fin n) (k : ℕ) :
    Finset (FixedTwo (0 : Fin n) q m l) :=
  if hkn : k < n then Finset.univ.filter (fun π => PermutationOverlapBound.Overlap hkn π.val)
  else ∅

private theorem mem_overlapFinset {n : ℕ} [NeZero n] (q m l : Fin n) (k : ℕ)
    (π : FixedTwo (0 : Fin n) q m l) :
    π ∈ overlapFinset q m l k ↔
      ∃ hkn : k < n, PermutationOverlapBound.Overlap hkn π.val := by
  by_cases hkn : k < n <;> simp [overlapFinset, hkn]

private theorem card_overlapFinset {n : ℕ} [NeZero n] (q m l : Fin n) (k : ℕ)
    (hkn : k < n) :
    (overlapFinset q m l k).card =
      Fintype.card (PermutationEndpointOverlapBound.EventTwo hkn q m l) := by
  classical
  let e : (↥(overlapFinset q m l k)) ≃ PermutationEndpointOverlapBound.EventTwo hkn q m l :=
    { toFun := fun π => ⟨π.val.val, π.val.property,
        (mem_overlapFinset q m l k π.val).mp π.property |>.choose_spec⟩
      invFun := fun π => ⟨⟨π.val, π.property.1⟩,
        (mem_overlapFinset q m l k _).mpr ⟨hkn, π.property.2⟩⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

/-- Uniformly over every pair of distinct prescribed endpoint labels, the fraction
of actual permutations with any overlap in `[K,n)` is at most `6/(K/3)!`.
Only finite-union subadditivity is used, not independence. -/
theorem longOverlapTwo_fraction_le_low {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (K : ℕ) (hK : 6 ≤ K) (q : Fin n) (hq : q.val + 1 = n)
    (m l : Fin n) (hml : m ≠ l) :
    ((longOverlapTwoFinset K q m l).card : ℝ) /
      Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      (((m.val + l.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2)) *
        (6 / ((K - 3) / 3).factorial) := by
  classical
  have hpq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) := fixedTwo_nonempty 0 q m l hpq hml
  have hpos : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast Fintype.card_pos
  have hunion : longOverlapTwoFinset K q m l =
      @Finset.biUnion ℕ (FixedTwo (0 : Fin n) q m l)
        (Classical.decEq _) (Finset.Ico K n) (overlapFinset q m l) := by
    ext π
    simp only [mem_longOverlapTwoFinset, LongOverlapTwo, Finset.mem_biUnion,
      Finset.mem_Ico, mem_overlapFinset]
    constructor
    · rintro ⟨k, hk, hkn, hπ⟩
      exact ⟨k, ⟨hk, hkn⟩, hkn, hπ⟩
    · rintro ⟨k, ⟨hk, hkn⟩, _, hπ⟩
      exact ⟨k, hk, hkn, hπ⟩
  rw [hunion]
  have hcard : ((@Finset.biUnion ℕ (FixedTwo (0 : Fin n) q m l)
      (Classical.decEq _) (Finset.Ico K n) (overlapFinset q m l)).card : ℝ) ≤
      ∑ k ∈ Finset.Ico K n, ((overlapFinset q m l k).card : ℝ) := by
    exact_mod_cast (@Finset.card_biUnion_le ℕ (FixedTwo (0 : Fin n) q m l)
      (Classical.decEq _) (Finset.Ico K n) (overlapFinset q m l))
  calc
    _ ≤ (∑ k ∈ Finset.Ico K n, ((overlapFinset q m l k).card : ℝ)) /
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) :=
      div_le_div_of_nonneg_right hcard hpos.le
    _ = ∑ k ∈ Finset.Ico K n, (overlapFinset q m l k).card /
        (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.Ico K n,
        (((m.val + l.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2)) *
          ((1 : ℝ) / (k / 3 - 1).factorial) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := (Finset.mem_Ico.mp hk).2
      rw [card_overlapFinset q m l k hkn]
      have hb := PermutationLowEndpointEventBound.eventTwo_fraction_le k
        (by have := (Finset.mem_Ico.mp hk).1; omega) hkn q hq m l hml
      simpa only [div_mul_eq_div_div, div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc, mul_comm, mul_left_comm] using hb
    _ = (((m.val + l.val - 1 : ℕ) : ℝ) / ((n : ℝ) - 2)) *
        (∑ k ∈ Finset.Ico K n, (1 : ℝ) / (k / 3 - 1).factorial) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (sum_shifted_factorial_tail K n hK)
      have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)

open Filter Topology

/-- Sublinearity survives removal of the three anchors in the relative density denominator. -/
theorem tendsto_low_density (a b : ℕ → ℕ)
    (hsub : Tendsto (fun n => ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ((max (a n) (b n) : ℕ) : ℝ) / ((n - 3 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (3 : ℝ) / n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n => (((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ)) /
      (1 - (3 : ℝ) / n)) atTop (𝓝 0) := by
    convert hsub.div (tendsto_const_nhds.sub hinv) (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hnr : (3 : ℝ) < n := by exact_mod_cast (show 3 < n by omega)
  have hnz : (n : ℝ) ≠ 0 := by linarith
  have hden : (n : ℝ) - 3 ≠ 0 := by linarith
  rw [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_ofNat]
  field_simp
  <;> ring

/-- All validity and positivity conditions for the actual moving experiment follow eventually from the requested hypotheses. -/
theorem eventually_valid_moving_experiment (a b : ℕ → ℕ)
    (hab : ∀ᶠ n in atTop, a n ≠ b n)
    (hA : ∀ᶠ n in atTop, 1 ≤ a n + b n - 1)
    (hsub : Tendsto (fun n => ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 4 ≤ n ∧ a n < n ∧ b n < n ∧ a n ≠ b n ∧ 1 ≤ a n + b n - 1 := by
  filter_upwards [PermutationSameEdgeMovingLimit.eventually_valid a b hsub,
    hab, hA, eventually_ge_atTop 4] with n hv hd hpos hn
  exact ⟨hn, hv.2.1, hv.2.2, hd, hpos⟩

example : (∀ᶠ n : ℕ in atTop, (0 : ℕ) ≠ 2) ∧
    (∀ᶠ n : ℕ in atTop, 1 ≤ (0 : ℕ) + 2 - 1) ∧
    Tendsto (fun n : ℕ => ((max (0 : ℕ) 2 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  refine ⟨Eventually.of_forall (fun _ => by decide), Eventually.of_forall (fun _ => by decide), ?_⟩
  have ht : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using ht

/-- Intended full moving mesoscopic rate for the actual terminal avoidance fraction.
This is the sole unpaid theorem: the checked isolated pair bounds, finite-union
sandwich, global two-low bound and long-tail bound above have not yet been combined
into the normalized cutoff estimate and the two-stage limit yielding exp(1)-1.
The declaration deliberately retains an explicit sorry and depends on sorryAx. -/
theorem tendsto_F_moving_mesoscopic (a b : ℕ → ℕ)
    (hab : ∀ᶠ n in atTop, a n ≠ b n)
    (hA : ∀ᶠ n in atTop, 1 ≤ a n + b n - 1)
    (hsub : Tendsto (fun n => ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / ((a n + b n - 1 : ℕ) : ℝ) *
      (1 - PermutationSameEdgeLimit.F n (a n) (b n))) atTop (𝓝 (Real.exp 1 - 1)) := by
  sorry

end FlexCF8AMesoscopicLowRate
