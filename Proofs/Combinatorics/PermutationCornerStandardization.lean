import Combinatorics.PermutationEndpointZeroTwoExact
import Combinatorics.PermutationBoundaryStandardization

set_option autoImplicit false

namespace PermutationCornerStandardization

open PermutationEndpointZeroTwoExact PermutationOverlapBound

attribute [local instance] Classical.propDecidable

private theorem remaining_value {n : ℕ} (p q s t a r h : Fin n)
    (htp : t ≠ p) (htq : t ≠ q) (hts : t ≠ s)
    (π : FixedThree p q s a r h) :
    π.val t ≠ a ∧ π.val t ≠ r ∧ π.val t ≠ h := by
  exact ⟨fun he => htp (π.val.injective (he.trans π.property.1.1.symm)),
    fun he => htq (π.val.injective (he.trans π.property.1.2.symm)),
    fun he => hts (π.val.injective (he.trans π.property.2.symm))⟩

private noncomputable def exchange {n : ℕ} (p q s t a r h : Fin n)
    (htp : t ≠ p) (htq : t ≠ q) (hts : t ≠ s)
    (x : FixedThree p q s a r h × {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h}) :
    FixedThree p q s a r h × {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h} :=
  (⟨x.1.val.trans (Equiv.swap (x.1.val t) x.2.val), by
      have hv := remaining_value p q s t a r h htp htq hts x.1
      change (Equiv.swap _ _ (x.1.val p) = a ∧
        Equiv.swap _ _ (x.1.val q) = r) ∧ Equiv.swap _ _ (x.1.val s) = h
      rw [x.1.property.1.1, x.1.property.1.2, x.1.property.2]
      exact ⟨⟨Equiv.swap_apply_of_ne_of_ne hv.1.symm x.2.property.1.symm,
        Equiv.swap_apply_of_ne_of_ne hv.2.1.symm x.2.property.2.1.symm⟩,
        Equiv.swap_apply_of_ne_of_ne hv.2.2.symm x.2.property.2.2.symm⟩⟩,
    ⟨x.1.val t, remaining_value p q s t a r h htp htq hts x.1⟩)

example (π : FixedThree (0 : Fin 5) 1 4 1 0 4) :
    (exchange 0 1 4 2 1 0 4 (by decide) (by decide) (by decide)
      (π, ⟨3, by decide⟩)).2.val = π.val 2 := rfl

private theorem exchange_value {n : ℕ} (p q s t a r h : Fin n)
    (htp : t ≠ p) (htq : t ≠ q) (hts : t ≠ s)
    (x : FixedThree p q s a r h × {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h}) :
    (exchange p q s t a r h htp htq hts x).1.val t = x.2.val :=
  Equiv.swap_apply_left _ _

private theorem exchange_involutive {n : ℕ} (p q s t a r h : Fin n)
    (htp : t ≠ p) (htq : t ≠ q) (hts : t ≠ s) :
    Function.Involutive (exchange p q s t a r h htp htq hts) := by
  intro x
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    change Equiv.swap ((exchange p q s t a r h htp htq hts x).1.val t) (x.1.val t)
      (Equiv.swap (x.1.val t) x.2.val (x.1.val i)) = x.1.val i
    rw [exchange_value, Equiv.swap_comm]
    exact Equiv.swap_apply_self _ _ _
  · apply Subtype.ext
    exact exchange_value p q s t a r h htp htq hts x

/-- Under three fixed anchors, exchanging the observed fourth label with any
available label proves the exact uniform marginal for every label event. -/
theorem triple_marginal_card {n : ℕ} (p q s t a r h : Fin n)
    (htp : t ≠ p) (htq : t ≠ q) (hts : t ≠ s) (P : Fin n → Prop) :
    Nat.card {π : FixedThree p q s a r h // P (π.val t)} *
        Nat.card {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h} =
      Nat.card (FixedThree p q s a r h) *
        Nat.card {v : Fin n // (v ≠ a ∧ v ≠ r ∧ v ≠ h) ∧ P v} := by
  classical
  let f := exchange p q s t a r h htp htq hts
  let e : ({π : FixedThree p q s a r h // P (π.val t)} ×
      {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h}) ≃
      (FixedThree p q s a r h ×
        {v : Fin n // (v ≠ a ∧ v ≠ r ∧ v ≠ h) ∧ P v}) :=
    { toFun := fun x => ((f (x.1.val, x.2)).1,
        ⟨x.1.val.val t, remaining_value p q s t a r h htp htq hts x.1.val,
          x.1.property⟩)
      invFun := fun y => (⟨(f (y.1, ⟨y.2.val, y.2.property.1⟩)).1, by
        change P ((exchange p q s t a r h htp htq hts _).1.val t)
        rw [exchange_value]
        exact y.2.property.2⟩,
        (f (y.1, ⟨y.2.val, y.2.property.1⟩)).2)
      left_inv := by
        intro x
        have he := exchange_involutive p q s t a r h htp htq hts (x.1.val, x.2)
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst he
        · exact congrArg (fun z : FixedThree p q s a r h ×
            {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h} => z.2) he
      right_inv := by
        intro y
        have he := exchange_involutive p q s t a r h htp htq hts
          (y.1, ⟨y.2.val, y.2.property.1⟩)
        apply Prod.ext
        · exact congrArg (fun z : FixedThree p q s a r h ×
            {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h} => z.1) he
        · apply Subtype.ext
          exact congrArg (fun z => z.2.val) he }
  simpa only [Nat.card_prod] using Nat.card_congr e

/-- For distinct anchor labels, the fourth-label marginal has denominator `n-3`. -/
theorem triple_marginal_card_mul {n : ℕ} (p q s t a r h : Fin n)
    (htp : t ≠ p) (htq : t ≠ q) (hts : t ≠ s)
    (har : a ≠ r) (hah : a ≠ h) (hrh : r ≠ h) (P : Fin n → Prop) :
    Nat.card {π : FixedThree p q s a r h // P (π.val t)} * (n - 3) =
      Nat.card (FixedThree p q s a r h) *
        Nat.card {v : Fin n // (v ≠ a ∧ v ≠ r ∧ v ≠ h) ∧ P v} := by
  have hc : Nat.card {v : Fin n // v ≠ a ∧ v ≠ r ∧ v ≠ h} = n - 3 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.univ \ {a, r, h}) (by simp)]
    simp [Finset.card_sdiff, har, hah, hrh]
  simpa only [hc] using triple_marginal_card p q s t a r h htp htq hts P

example : Nonempty (FixedThree (0 : Fin 6) 1 5 1 0 5) :=
  ⟨⟨Equiv.swap 0 1, by decide⟩⟩

example : (2 : Fin 6) ≠ 0 ∧ (2 : Fin 6) ≠ 1 ∧ (2 : Fin 6) ≠ 5 ∧
    (1 : Fin 6) ≠ 0 ∧ (1 : Fin 6) ≠ 5 ∧ (0 : Fin 6) ≠ 5 := by decide

/-- Avoid every actual prefix/suffix overlap with inclusive lengths `L ≤ k ≤ K`.
The explicit `k < n` guard is automatic in the intended range `n ≥ 2*K`. -/
def AvoidThrough {n : ℕ} (L K : ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, L ≤ k → k ≤ K → ∀ hkn : k < n, ¬ Overlap hkn π

example : ¬ AvoidThrough 3 3 (Equiv.refl (Fin 6)) := by
  intro h
  apply h 3 (by decide) (by decide) (by decide)
  intro i j
  change i.val < j.val ↔ i.val + (6 - 3) < j.val + (6 - 3)
  omega

/-- The actual three-anchor avoidance fraction, with anchors at positions
zero, one, and last. The length guard makes these three positions distinct. -/
noncomputable def tripleFraction {n : ℕ} (hn : 3 ≤ n) (a r h : Fin n)
    (L K : ℕ) : ℝ :=
  (Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
    ⟨n - 1, by omega⟩ a r h // AvoidThrough L K π.val} : ℝ) /
    Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r h)

example {n : ℕ} (hn : 3 ≤ n) (a r h : Fin n) (L K : ℕ) :
    tripleFraction hn a r h L K =
      (Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r h // AvoidThrough L K π.val} : ℝ) /
      Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r h) := rfl

/-- The canonical fraction `C_K`: actual permutations of length `2*K`, fixed
at labels one, zero, and last, avoiding all overlaps `3 ≤ k ≤ K`. -/
noncomputable def canonicalFraction (K : ℕ) (hK : 3 ≤ K) : ℝ :=
  tripleFraction (n := 2 * K) (by omega) ⟨1, by omega⟩ ⟨0, by omega⟩
    ⟨2 * K - 1, by omega⟩ 3 K

example (K : ℕ) (hK : 3 ≤ K) : canonicalFraction K hK =
    tripleFraction (n := 2 * K) (by omega) ⟨1, by omega⟩ ⟨0, by omega⟩
      ⟨2 * K - 1, by omega⟩ 3 K := rfl

/-- The exact unpaid finite-consumer obligation, not an asserted theorem.
Both inclusive cutoffs, three and two, must obey the same undoubled bound.
All interval and length guards are part of this closed proposition. -/
def FiniteConsumer : Prop :=
  ∀ (K n a b r : ℕ) (hK : 3 ≤ K) (hn : 2 * K ≤ n)
    (hra : r < a) (hah : a < n - 1 - b)
    (hgood : 2 * K - 3 ≤ n - a - b - 2),
    ∀ L ∈ ({2, 3} : Finset ℕ),
      |tripleFraction (n := n) (by omega) ⟨a, by omega⟩ ⟨r, by omega⟩
          ⟨n - 1 - b, by omega⟩ L K - canonicalFraction K hK| ≤
        ((2 * K : ℝ) - 3) * ((a : ℝ) + b - 1) / ((n : ℝ) - 3)

example : 3 ≤ (3 : ℕ) ∧ 2 * 3 ≤ (6 : ℕ) ∧ (0 : ℕ) < 1 ∧
    (1 : ℕ) < 6 - 1 - 0 ∧ 2 * 3 - 3 ≤ (6 : ℕ) - 1 - 0 - 2 := by decide

private theorem bad_labels_card {n : ℕ} (a r h : Fin n) (hra : r < a) (hah : a < h) :
    Nat.card {v : Fin n // (v ≠ a ∧ v ≠ r ∧ v ≠ h) ∧ ¬ (a < v ∧ v < h)} =
      n - 3 - (h.val - a.val - 1) := by
  classical
  let A : Finset (Fin n) := Finset.univ \ {a, r, h}
  have hA : A.card = n - 3 := by
    simp [A, Finset.card_sdiff, ne_of_gt hra, ne_of_lt hah, ne_of_lt (hra.trans hah)]
  have hsub : Finset.Ioo a h ⊆ A := by
    intro v hv
    have hv' := Finset.mem_Ioo.mp hv
    simp only [A, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    exact ⟨ne_of_gt hv'.1, ne_of_gt (hra.trans hv'.1), ne_of_lt hv'.2⟩
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype (A \ Finset.Ioo a h) (by simp [A, and_assoc])]
  rw [Finset.card_sdiff_of_subset hsub, hA, Fin.card_Ioo]

private theorem bad_card_bound {n t : ℕ} (e : Fin t ↪ Fin n)
    (x y z : Fin t) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a r h : Fin n) (hra : r < a) (hah : a < h) :
    Nat.card {π : FixedThree (e x) (e y) (e z) a r h //
      ∃ i : Fin t, (i ≠ x ∧ i ≠ y ∧ i ≠ z) ∧ ¬ (a < π.val (e i) ∧ π.val (e i) < h)} *
        (n - 3) ≤ Nat.card (FixedThree (e x) (e y) (e z) a r h) *
          ((t - 3) * (n - 3 - (h.val - a.val - 1))) := by
  classical
  let I := {i : Fin t // i ≠ x ∧ i ≠ y ∧ i ≠ z}
  let X := FixedThree (e x) (e y) (e z) a r h
  let D := {π : X // ∃ i : Fin t,
    (i ≠ x ∧ i ≠ y ∧ i ≠ z) ∧ ¬ (a < π.val (e i) ∧ π.val (e i) < h)}
  let Y := Σ i : I, {π : X // ¬ (a < π.val (e i.val) ∧ π.val (e i.val) < h)}
  let f : D → Y := fun π =>
    ⟨⟨Classical.choose π.property, (Classical.choose_spec π.property).1⟩,
      ⟨π.val, (Classical.choose_spec π.property).2⟩⟩
  have hc : Nat.card D ≤ ∑ i : I,
      Nat.card {π : X // ¬ (a < π.val (e i.val) ∧ π.val (e i.val) < h)} := by
    simpa only [Y, Nat.card_sigma] using Nat.card_le_card_of_injective f (by
      intro π τ he
      exact Subtype.ext (congrArg (fun v : Y => v.2.val) he))
  have hI : Fintype.card I = t - 3 := by
    rw [Fintype.card_of_subtype (Finset.univ \ {x, y, z}) (by simp [I])]
    simp [Finset.card_sdiff, hxy, hxz, hyz]
  have hm (i : I) :
      Nat.card {π : X // ¬ (a < π.val (e i.val) ∧ π.val (e i.val) < h)} * (n - 3) =
        Nat.card X * (n - 3 - (h.val - a.val - 1)) := by
    rw [← bad_labels_card a r h hra hah]
    exact triple_marginal_card_mul (e x) (e y) (e z) (e i.val) a r h
      (fun he => i.property.1 (e.injective he))
      (fun he => i.property.2.1 (e.injective he))
      (fun he => i.property.2.2 (e.injective he))
      (ne_of_gt hra) (ne_of_lt hah) (ne_of_lt (hra.trans hah))
      (fun v => ¬ (a < v ∧ v < h))
  calc
    Nat.card D * (n - 3) ≤
        (∑ i : I, Nat.card {π : X // ¬ (a < π.val (e i.val) ∧ π.val (e i.val) < h)}) *
          (n - 3) := Nat.mul_le_mul_right _ hc
    _ = ∑ i : I, Nat.card X * (n - 3 - (h.val - a.val - 1)) := by
      rw [Finset.sum_mul]; simp only [hm]
    _ = Nat.card X * ((t - 3) * (n - 3 - (h.val - a.val - 1))) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hI]
      ring

open PermutationBoundaryStandardization PermutationOrderCounting

private theorem rank_anchor_values {n t : ℕ} (ht : 3 ≤ t)
    (e : Fin t ↪ Fin n) (x y z : Fin t)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a r h : Fin n) (hra : r < a) (hah : a < h)
    (π : FixedThree (e x) (e y) (e z) a r h)
    (hg : ∀ i : Fin t, i ≠ x → i ≠ y → i ≠ z →
      a < π.val (e i) ∧ π.val (e i) < h) :
    (standardize e π.val x = ⟨1, by omega⟩ ∧
      standardize e π.val y = ⟨0, by omega⟩) ∧
      standardize e π.val z = ⟨t - 1, by omega⟩ := by
  letI : NeZero t := ⟨by omega⟩
  let σ := standardize e π.val
  have hlow (i : Fin t) (hi : i ≠ y) : σ y < σ i := by
    apply (standardize_lt_iff e π.val y i).mpr
    rw [π.property.1.2]
    by_cases hix : i = x
    · subst i; rw [π.property.1.1]; exact hra
    by_cases hiz : i = z
    · subst i; rw [π.property.2]; exact hra.trans hah
    exact hra.trans (hg i hix hi hiz).1
  have hy : σ y = ⟨0, by omega⟩ := by
    obtain ⟨i, hi⟩ := σ.surjective ⟨0, by omega⟩
    by_cases hiy : i = y
    · simpa only [hiy] using hi
    have hc := hlow i hiy
    rw [hi] at hc
    exact False.elim (not_lt_of_ge (Fin.zero_le _) hc)
  have hbelow (i : Fin t) : σ i < σ x → i = y := by
    intro hi
    have hv := (standardize_lt_iff e π.val i x).mp hi
    rw [π.property.1.1] at hv
    by_contra hiy
    by_cases hix : i = x
    · subst i; rw [π.property.1.1] at hv; exact (lt_irrefl a) hv
    by_cases hiz : i = z
    · subst i; rw [π.property.2] at hv; exact (not_lt_of_gt hah) hv
    exact (not_lt_of_gt (hg i hix hiy hiz).1) hv
  have hx : σ x = ⟨1, by omega⟩ := by
    have hp := hlow x hxy
    rw [hy] at hp
    obtain ⟨i, hi⟩ := σ.surjective ⟨1, by omega⟩
    apply Fin.ext
    change (σ x).val = 1
    by_contra hne
    have hlt : σ i < σ x := by rw [hi]; change 1 < (σ x).val; change 0 < (σ x).val at hp; omega
    have hiy := hbelow i hlt
    have he := hi
    rw [hiy, hy] at he
    have he' := congrArg Fin.val he
    simp at he'
  have hhigh (i : Fin t) (hi : i ≠ z) : σ i < σ z := by
    apply (standardize_lt_iff e π.val i z).mpr
    rw [π.property.2]
    by_cases hix : i = x
    · subst i; rw [π.property.1.1]; exact hah
    by_cases hiy : i = y
    · subst i; rw [π.property.1.2]; exact hra.trans hah
    exact (hg i hix hiy hi).2
  have hz : σ z = ⟨t - 1, by omega⟩ := by
    obtain ⟨i, hi⟩ := σ.surjective ⟨t - 1, by omega⟩
    by_cases hiz : i = z
    · simpa only [hiz] using hi
    have hc := hhigh i hiz
    rw [hi] at hc
    have hv : t - 1 < (σ z).val := hc
    have hv' := (σ z).isLt
    omega
  exact ⟨⟨hx, hy⟩, hz⟩

private theorem card_tripleStandardize_fiber {n t : ℕ} (e : Fin t ↪ Fin n)
    (x y z : Fin t) (a r h : Fin n) (m l v : Fin t)
    (ρ σ : FixedThree x y z m l v) :
    Nat.card {π : FixedThree (e x) (e y) (e z) a r h // standardize e π.val = ρ.val} =
      Nat.card {π : FixedThree (e x) (e y) (e z) a r h // standardize e π.val = σ.val} := by
  classical
  suffices hle : ∀ ρ σ : FixedThree x y z m l v,
      Nat.card {π : FixedThree (e x) (e y) (e z) a r h // standardize e π.val = ρ.val} ≤
        Nat.card {π : FixedThree (e x) (e y) (e z) a r h // standardize e π.val = σ.val} from
    le_antisymm (hle ρ σ) (hle σ ρ)
  intro ρ σ
  let α := σ.val.trans ρ.val.symm
  have hfix (i : Fin t) (hi : ρ.val i = σ.val i) : α i = i := by
    change ρ.val.symm (σ.val i) = i
    rw [← hi, Equiv.symm_apply_apply]
  have hx : α x = x := hfix x (ρ.property.1.1.trans σ.property.1.1.symm)
  have hy : α y = y := hfix y (ρ.property.1.2.trans σ.property.1.2.symm)
  have hz : α z = z := hfix z (ρ.property.2.trans σ.property.2.symm)
  let f : {π : FixedThree (e x) (e y) (e z) a r h // standardize e π.val = ρ.val} →
      {π : FixedThree (e x) (e y) (e z) a r h // standardize e π.val = σ.val} := fun π =>
    ⟨⟨(blockPerm e α).trans π.val.val, by
      simpa only [Equiv.trans_apply, blockPerm_apply, hx, hy, hz] using π.val.property⟩, by
      rw [standardize_reorder, π.property]
      apply Equiv.ext
      intro i
      exact ρ.val.apply_symm_apply (σ.val i)⟩
  apply Nat.card_le_card_of_injective f
  intro π τ he
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hv := congrArg (fun u => u.val.val ((blockPerm e α).symm i)) he
  simpa only [f, Equiv.trans_apply, Equiv.apply_symm_apply] using hv

private theorem event_card_le {X : Type*} [Fintype X] (A B D : X → Prop)
    (h : ∀ x, A x → B x ∨ D x) :
    Nat.card {x // A x} ≤ Nat.card {x // B x} + Nat.card {x // D x} := by
  classical
  have hc := Nat.card_le_card_of_injective
    (fun x : {x // A x} => (⟨x.val, h x.val x.property⟩ : {x // B x ∨ D x}))
    (by intro x y he; exact Subtype.ext (congrArg (fun u : {x // B x ∨ D x} => u.val) he))
  have ho : Nat.card {x // B x ∨ D x} ≤ Nat.card {x // B x} + Nat.card {x // D x} := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_or B D
  exact hc.trans ho

private theorem fraction_bounds {X : Type*} [Fintype X] (P : X → Prop) :
    0 ≤ (Nat.card {x // P x} : ℝ) / Nat.card X ∧
      (Nat.card {x // P x} : ℝ) / Nat.card X ≤ 1 := by
  classical
  constructor
  · positivity
  · apply div_le_one_of_le₀
    · have hh : Nat.card {x // P x} ≤ Nat.card X := by
        simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le P
      exact_mod_cast hh
    · positivity

private theorem conditional_error {X : Type*} [Fintype X] [Nonempty X]
    (A G : X → Prop) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : (Nat.card {x // A x ∧ G x} : ℝ) = c * Nat.card {x // G x}) :
    |(Nat.card {x // A x} : ℝ) / Nat.card X - c| ≤
      (Nat.card {x // ¬ G x} : ℝ) / Nat.card X := by
  classical
  have hx : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩ : 0 < Nat.card X)
  have hpart : Nat.card {x // G x} + Nat.card {x // ¬ G x} = Nat.card X := by
    have hg := Fintype.card_subtype_le G
    have hd := Fintype.card_subtype_compl G
    simp only [Nat.card_eq_fintype_card]
    omega
  have hupper := event_card_le A (fun x => A x ∧ G x) (fun x => ¬ G x)
    (by intro x ha; by_cases hg : G x; exact Or.inl ⟨ha, hg⟩; exact Or.inr hg)
  have hlower : Nat.card {x // A x ∧ G x} ≤ Nat.card {x // A x} :=
    Nat.card_le_card_of_injective (fun x => (⟨x.val, x.property.1⟩ : {x // A x}))
      (by intro x y he; exact Subtype.ext (congrArg (fun u : {x // A x} => u.val) he))
  have hpR : (Nat.card {x // G x} : ℝ) + Nat.card {x // ¬ G x} = Nat.card X := by
    exact_mod_cast hpart
  have huR : (Nat.card {x // A x} : ℝ) ≤
      Nat.card {x // A x ∧ G x} + Nat.card {x // ¬ G x} := by exact_mod_cast hupper
  have hlR : (Nat.card {x // A x ∧ G x} : ℝ) ≤ Nat.card {x // A x} := by
    exact_mod_cast hlower
  rw [hc] at huR hlR
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_left₀ hx).mp
    have hmul := mul_le_mul_of_nonneg_right hc1
      (show (0 : ℝ) ≤ Nat.card {x // ¬ G x} by positivity)
    simp only [sub_mul, neg_mul, div_mul_cancel₀ _ hx.ne']
    nlinarith
  · apply (mul_le_mul_iff_left₀ hx).mp
    rw [sub_mul, div_mul_cancel₀ _ hx.ne', div_mul_cancel₀ _ hx.ne']
    have hmul := mul_nonneg hc0 (show (0 : ℝ) ≤ Nat.card {x // ¬ G x} by positivity)
    nlinarith

private theorem fraction_preimage_uniform_nat {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] (f : X → Y)
    (hu : ∀ y z, Nat.card {x // f x = y} = Nat.card {x // f x = z})
    (P : Y → Prop) :
    (Nat.card {x // P (f x)} : ℝ) / Nat.card X =
      (Nat.card {y // P y} : ℝ) / Nat.card Y := by
  classical
  have hu' (y z : Y) : Fintype.card {x // f x = y} = Fintype.card {x // f x = z} := by
    simpa only [Nat.card_eq_fintype_card] using hu y z
  simpa only [Nat.card_eq_fintype_card] using fraction_preimage_uniform f hu' P

private theorem restricted_fraction {n t : ℕ} (e : Fin t ↪ Fin n)
    (x y z : Fin t) (a r h : Fin n) (m l v : Fin t)
    (P : Equiv.Perm (Fin t) → Prop)
    (hg : Nonempty {π : FixedThree (e x) (e y) (e z) a r h //
      (standardize e π.val x = m ∧ standardize e π.val y = l) ∧
        standardize e π.val z = v}) :
    (Nat.card {π : FixedThree (e x) (e y) (e z) a r h //
      P (standardize e π.val) ∧
        ((standardize e π.val x = m ∧ standardize e π.val y = l) ∧
          standardize e π.val z = v)} : ℝ) =
      ((Nat.card {ρ : FixedThree x y z m l v // P ρ.val} : ℝ) /
        Nat.card (FixedThree x y z m l v)) *
      Nat.card {π : FixedThree (e x) (e y) (e z) a r h //
        (standardize e π.val x = m ∧ standardize e π.val y = l) ∧
          standardize e π.val z = v} := by
  classical
  let X := FixedThree (e x) (e y) (e z) a r h
  let G : X → Prop := fun π =>
    (standardize e π.val x = m ∧ standardize e π.val y = l) ∧ standardize e π.val z = v
  let Y := FixedThree x y z m l v
  let f : {π : X // G π} → Y := fun π => ⟨standardize e π.val.val, π.property⟩
  letI : Nonempty {π : X // G π} := hg
  have he (ρ : Y) : Nat.card {π // f π = ρ} =
      Nat.card {π : X // standardize e π.val = ρ.val} := by
    apply Nat.card_congr
    exact {
      toFun := fun π => ⟨π.val.val, congrArg Subtype.val π.property⟩
      invFun := fun π => ⟨⟨π.val, by change G π.val; dsimp only [G]; rw [π.property]; exact ρ.property⟩,
        Subtype.ext π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hu (ρ σ : Y) : Nat.card {π // f π = ρ} = Nat.card {π // f π = σ} := by
    rw [he, he]
    exact card_tripleStandardize_fiber e x y z a r h m l v ρ σ
  have hf :
      (Nat.card {π : {π : X // G π} // P (f π).val} : ℝ) /
        Nat.card {π : X // G π} =
      (Nat.card {ρ : Y // P ρ.val} : ℝ) / Nat.card Y :=
    fraction_preimage_uniform_nat (X := {π : X // G π}) (Y := Y) f hu
      (fun ρ : Y => P ρ.val)
  have hcard : Nat.card {π : {π : X // G π} // P (f π).val} =
      Nat.card {π : X // P (standardize e π.val) ∧ G π} := by
    apply Nat.card_congr
    exact {
      toFun := fun π => ⟨π.val.val, π.property, π.val.property⟩
      invFun := fun π => ⟨⟨π.val, π.property.2⟩, π.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcard] at hf
  have hp : (0 : ℝ) < Nat.card {π : X // G π} := by
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩ :
      0 < Nat.card {π : X // G π})
  exact (div_eq_iff hp.ne').mp hf

private theorem avoidThrough_standardize_iff (K n L : ℕ) (hK : 3 ≤ K)
    (hn : 2 * K ≤ n) (π : Equiv.Perm (Fin n)) :
    AvoidThrough L K (standardize (boundaryEmbedding (K + 1) n (by omega) (by omega)) π) ↔
      AvoidThrough L K π := by
  constructor
  · intro H k hk hkK hkn ho
    exact H k hk hkK (by omega)
      ((overlap_standardize_iff (K + 1) n (by omega) (by omega)
        (by omega) hkn (by omega) π).mpr ho)
  · intro H k hk hkK hkt ho
    exact H k hk hkK (by omega)
      ((overlap_standardize_iff (K + 1) n (by omega) (by omega)
        (by omega) (by omega) hkt π).mp ho)

private theorem canonical_no_overlap_two {t : ℕ} (ht : 4 ≤ t)
    (π : FixedThree (⟨0, by omega⟩ : Fin t) ⟨1, by omega⟩ ⟨t - 1, by omega⟩
      ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨t - 1, by omega⟩) :
    ¬ Overlap (by omega : 2 < t) π.val := by
  intro ho
  have hp : ¬ π.val ⟨0, by omega⟩ < π.val ⟨1, by omega⟩ := by
    rw [π.property.1.1, π.property.1.2]
    change ¬ (1 : ℕ) < 0
    omega
  have hs : π.val ⟨t - 2, by omega⟩ < π.val ⟨t - 1, by omega⟩ := by
    rw [π.property.2]
    have hne : π.val ⟨t - 2, by omega⟩ ≠ (⟨t - 1, by omega⟩ : Fin t) := by
      intro he
      have hv := congrArg Fin.val (π.val.injective (he.trans π.property.2.symm))
      change t - 2 = t - 1 at hv
      omega
    have hb := (π.val ⟨t - 2, by omega⟩).isLt
    have hnval : (π.val ⟨t - 2, by omega⟩).val ≠ t - 1 := by
      intro he
      apply hne
      exact Fin.ext he
    change (π.val ⟨t - 2, by omega⟩).val < t - 1
    omega
  apply hp
  apply (ho (⟨0, by decide⟩ : Fin 2) ⟨1, by decide⟩).mpr
  convert hs using 2 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

private theorem rank_anchors_iff_good {n t : ℕ} (ht : 3 ≤ t)
    (e : Fin t ↪ Fin n) (x y z : Fin t)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a r h : Fin n) (hra : r < a) (hah : a < h)
    (π : FixedThree (e x) (e y) (e z) a r h) :
    ((standardize e π.val x = ⟨1, by omega⟩ ∧
      standardize e π.val y = ⟨0, by omega⟩) ∧
      standardize e π.val z = ⟨t - 1, by omega⟩) ↔
    (∀ i : Fin t, i ≠ x → i ≠ y → i ≠ z →
      a < π.val (e i) ∧ π.val (e i) < h) := by
  constructor
  · intro hg i hix hiy hiz
    let σ := standardize e π.val
    have hne0 : σ i ≠ (⟨0, by omega⟩ : Fin t) := by
      intro he
      exact hiy (σ.injective (he.trans hg.1.2.symm))
    have hne1 : σ i ≠ (⟨1, by omega⟩ : Fin t) := by
      intro he
      exact hix (σ.injective (he.trans hg.1.1.symm))
    have hnelast : σ i ≠ (⟨t - 1, by omega⟩ : Fin t) := by
      intro he
      exact hiz (σ.injective (he.trans hg.2.symm))
    have hlo : σ x < σ i := by
      change (σ x).val < (σ i).val
      have hv0 : (σ i).val ≠ 0 := fun he => hne0 (Fin.ext he)
      have hv1 : (σ i).val ≠ 1 := fun he => hne1 (Fin.ext he)
      have hxval := congrArg Fin.val hg.1.1
      change (σ x).val = 1 at hxval
      omega
    have hhi : σ i < σ z := by
      change (σ i).val < (σ z).val
      have hv : (σ i).val ≠ t - 1 := fun he => hnelast (Fin.ext he)
      have hzval := congrArg Fin.val hg.2
      change (σ z).val = t - 1 at hzval
      have hb := (σ i).isLt
      omega
    have hlo' := (standardize_lt_iff e π.val x i).mp hlo
    have hhi' := (standardize_lt_iff e π.val i z).mp hhi
    rw [π.property.1.1] at hlo'
    rw [π.property.2] at hhi'
    exact ⟨hlo', hhi'⟩
  · exact rank_anchor_values ht e x y z hxy hxz hyz a r h hra hah π

private theorem fixedThree_nonempty {n : ℕ} (p q z a r h : Fin n)
    (hpq : p ≠ q) (hzp : z ≠ p) (hzq : z ≠ q)
    (har : a ≠ r) (hha : h ≠ a) (hhr : h ≠ r) :
    Nonempty (FixedThree p q z a r h) := by
  letI := PermutationEndpointCounting.fixedTwo_nonempty p q a r hpq har
  have hc := card_fixedThree_mul p q z a r h hzp hzq har hha hhr
  have hpos : 0 < Fintype.card (PermutationEndpointCounting.FixedTwo p q a r) :=
    Fintype.card_pos
  have hthree : 0 < Fintype.card (FixedThree p q z a r h) := by
    by_contra hn
    have hz : Fintype.card (FixedThree p q z a r h) = 0 := by omega
    rw [hz, zero_mul] at hc
    omega
  exact Fintype.card_pos_iff.mp hthree

private theorem good_nonempty_of_bad_fraction_lt_one {X : Type*} [Fintype X]
    [Nonempty X] (G : X → Prop)
    (hbad : (Nat.card {x // ¬ G x} : ℝ) / Nat.card X < 1) :
    Nonempty {x // G x} := by
  classical
  by_contra hn
  have hfalse : ∀ x, ¬ G x := by
    intro x hx
    exact hn ⟨⟨x, hx⟩⟩
  have hc : Nat.card {x // ¬ G x} = Nat.card X := by
    apply Nat.card_congr
    exact Equiv.subtypeUnivEquiv hfalse
  have hx : (Nat.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩ : 0 < Nat.card X).ne'
  rw [hc, div_self hx] at hbad
  exact lt_irrefl 1 hbad

private theorem standardize_error {n t : ℕ} (hn : 4 ≤ n) (ht : 3 ≤ t)
    (e : Fin t ↪ Fin n) (x y z : Fin t)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a r h : Fin n) (hra : r < a) (hah : a < h)
    (P : Equiv.Perm (Fin t) → Prop) :
    |(Nat.card {π : FixedThree (e x) (e y) (e z) a r h // P (standardize e π.val)} : ℝ) /
        Nat.card (FixedThree (e x) (e y) (e z) a r h) -
      (Nat.card {ρ : FixedThree x y z ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨t - 1, by omega⟩ // P ρ.val} : ℝ) /
        Nat.card (FixedThree x y z ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨t - 1, by omega⟩)| ≤
      ((t - 3 : ℕ) : ℝ) * (n - 3 - (h.val - a.val - 1) : ℕ) / (n - 3 : ℕ) := by
  classical
  let X := FixedThree (e x) (e y) (e z) a r h
  let Y := FixedThree x y z (⟨1, by omega⟩ : Fin t) ⟨0, by omega⟩ ⟨t - 1, by omega⟩
  let G : X → Prop := fun π =>
    (standardize e π.val x = ⟨1, by omega⟩ ∧ standardize e π.val y = ⟨0, by omega⟩) ∧
      standardize e π.val z = ⟨t - 1, by omega⟩
  let A : X → Prop := fun π => P (standardize e π.val)
  let c : ℝ := (Nat.card {ρ : Y // P ρ.val} : ℝ) / Nat.card Y
  let eps : ℝ := ((t - 3 : ℕ) : ℝ) * (n - 3 - (h.val - a.val - 1) : ℕ) / (n - 3 : ℕ)
  letI : Nonempty X := fixedThree_nonempty (e x) (e y) (e z) a r h
    (fun he => hxy (e.injective he)) (fun he => hxz (e.injective he).symm)
    (fun he => hyz (e.injective he).symm)
    (ne_of_gt hra) (ne_of_gt hah) (ne_of_gt (hra.trans hah))
  have hxpos : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩ : 0 < Nat.card X)
  have hdpos : (0 : ℝ) < (n - 3 : ℕ) := by exact_mod_cast (show 0 < n - 3 by omega)
  have hbad : (Nat.card {π : X // ¬ G π} : ℝ) / Nat.card X ≤ eps := by
    have hevent : Nat.card {π : X // ¬ G π} =
        Nat.card {π : X // ∃ i : Fin t, (i ≠ x ∧ i ≠ y ∧ i ≠ z) ∧
          ¬ (a < π.val (e i) ∧ π.val (e i) < h)} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro π
      change ¬ G π ↔ _
      dsimp only [G]
      rw [rank_anchors_iff_good ht e x y z hxy hxz hyz a r h hra hah π]
      simp only [not_forall, exists_prop, and_assoc]
    have hb := bad_card_bound e x y z hxy hxz hyz a r h hra hah
    rw [← hevent] at hb
    have hbR : (Nat.card {π : X // ¬ G π} : ℝ) * (n - 3 : ℕ) ≤
        (Nat.card X : ℝ) * (((t - 3 : ℕ) : ℝ) * (n - 3 - (h.val - a.val - 1) : ℕ)) := by
      exact_mod_cast hb
    apply (div_le_iff₀ hxpos).mpr
    dsimp only [eps]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdpos).mpr
    nlinarith [hbR]
  have hc := fraction_bounds (fun ρ : Y => P ρ.val)
  have ha := fraction_bounds A
  by_cases heps : 1 ≤ eps
  · change |(Nat.card {π : X // A π} : ℝ) / Nat.card X - c| ≤ eps
    apply le_trans (abs_le.mpr ⟨by dsimp only [c]; linarith [ha.1, hc.2],
      by dsimp only [c]; linarith [ha.2, hc.1]⟩) heps
  · have hg : Nonempty {π : X // G π} :=
      good_nonempty_of_bad_fraction_lt_one G (hbad.trans_lt (lt_of_not_ge heps))
    have hcond := restricted_fraction e x y z a r h
      ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨t - 1, by omega⟩ P hg
    exact (conditional_error A G c hc.1 hc.2 hcond).trans hbad

private theorem canonical_avoid_iff (K L : ℕ) (hK : 3 ≤ K)
    (hL : L ∈ ({2, 3} : Finset ℕ))
    (π : FixedThree (⟨0, by omega⟩ : Fin (2 * K)) ⟨1, by omega⟩ ⟨2 * K - 1, by omega⟩
      ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨2 * K - 1, by omega⟩) :
    AvoidThrough L K π.val ↔ AvoidThrough 3 K π.val := by
  have hcases : L = 2 ∨ L = 3 := by simpa using hL
  rcases hcases with rfl | rfl
  · constructor
    · intro H k hk hkK hkn
      exact H k (by omega) hkK hkn
    · intro H k hk hkK hkn
      by_cases hk2 : k = 2
      · subst k
        exact canonical_no_overlap_two (by omega) π
      · exact H k (by omega) hkK hkn
  · rfl

private theorem canonical_fraction_of_length (t K L : ℕ) (hK : 3 ≤ K)
    (ht : t = 2 * K) (hL : L ∈ ({2, 3} : Finset ℕ)) :
    (Nat.card {π : FixedThree (⟨0, by omega⟩ : Fin t) ⟨1, by omega⟩ ⟨t - 1, by omega⟩
      ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨t - 1, by omega⟩ // AvoidThrough L K π.val} : ℝ) /
      Nat.card (FixedThree (⟨0, by omega⟩ : Fin t) ⟨1, by omega⟩ ⟨t - 1, by omega⟩
        ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨t - 1, by omega⟩) = canonicalFraction K hK := by
  subst t
  unfold canonicalFraction tripleFraction
  simp only [← Nat.card_eq_fintype_card]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight (canonical_avoid_iff K L hK hL))

/-- Both inclusive avoidance cutoffs have the same finite corner error bound. -/
theorem finiteConsumer_proof : FiniteConsumer := by
  intro K n a b r hK hn hra hah hgood L hL
  let e := boundaryEmbedding (K + 1) n (by omega) (by omega)
  let x : Fin (2 * (K + 1) - 2) := ⟨0, by omega⟩
  let y : Fin (2 * (K + 1) - 2) := ⟨1, by omega⟩
  let z : Fin (2 * (K + 1) - 2) := ⟨2 * (K + 1) - 2 - 1, by omega⟩
  have hxy : x ≠ y := by intro he; have hv := congrArg Fin.val he; change 0 = 1 at hv; omega
  have hxz : x ≠ z := by intro he; have hv := congrArg Fin.val he; dsimp only [x, z] at hv; omega
  have hyz : y ≠ z := by intro he; have hv := congrArg Fin.val he; dsimp only [y, z] at hv; omega
  have he0 : e x = (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    change (if 0 < K + 1 - 1 then 0 else n - (K + 1 - 1) + (0 - (K + 1 - 1))) = 0
    rw [if_pos (by omega)]
  have he1 : e y = (⟨1, by omega⟩ : Fin n) := by
    apply Fin.ext
    change (if 1 < K + 1 - 1 then 1 else n - (K + 1 - 1) + (1 - (K + 1 - 1))) = 1
    rw [if_pos (by omega)]
  have hez : e z = (⟨n - 1, by omega⟩ : Fin n) := by
    apply Fin.ext
    change (if 2 * (K + 1) - 2 - 1 < K + 1 - 1 then 2 * (K + 1) - 2 - 1
      else n - (K + 1 - 1) + (2 * (K + 1) - 2 - 1 - (K + 1 - 1))) = n - 1
    rw [if_neg (by omega)]
    omega
  have H := standardize_error (by omega : 4 ≤ n) (by omega : 3 ≤ 2 * (K + 1) - 2)
    e x y z hxy hxz hyz (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩
    (by exact hra) (by exact hah) (AvoidThrough L K)
  have hnum : Nat.card {π : FixedThree (e x) (e y) (e z)
        (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ //
        AvoidThrough L K (standardize e π.val)} =
      Nat.card {π : FixedThree (e x) (e y) (e z)
        (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ // AvoidThrough L K π.val} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun π => avoidThrough_standardize_iff K n L hK hn π.val)
  rw [hnum] at H
  have hactual : Nat.card {π : FixedThree (e x) (e y) (e z)
      (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ // AvoidThrough L K π.val} =
      Nat.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩
        ⟨a, by omega⟩ ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ // AvoidThrough L K π.val} := by
    apply Nat.card_congr
    exact {
      toFun := fun π => ⟨⟨π.val.val, by simpa only [he0, he1, hez] using π.val.property⟩, π.property⟩
      invFun := fun π => ⟨⟨π.val.val, by simpa only [he0, he1, hez] using π.val.property⟩, π.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hactual] at H
  simp only [he0, he1, hez] at H
  have hcan := canonical_fraction_of_length (2 * (K + 1) - 2) K L hK (by omega) hL
  change (Nat.card {π : FixedThree x y z (⟨1, by omega⟩ : Fin (2 * (K + 1) - 2))
      ⟨0, by omega⟩ ⟨2 * (K + 1) - 2 - 1, by omega⟩ // AvoidThrough L K π.val} : ℝ) /
    Nat.card (FixedThree x y z (⟨1, by omega⟩ : Fin (2 * (K + 1) - 2))
      ⟨0, by omega⟩ ⟨2 * (K + 1) - 2 - 1, by omega⟩) = canonicalFraction K hK at hcan
  rw [hcan] at H
  have hb : n - 3 - (n - 1 - b - a - 1) = a + b - 1 := by omega
  have htR : ((2 * K - 3 : ℕ) : ℝ) = (2 * K : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
  have hbR : ((a + b - 1 : ℕ) : ℝ) = (a : ℝ) + b - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hnR : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  have ht : 2 * (K + 1) - 2 - 3 = 2 * K - 3 := by omega
  simp only [Fin.val_mk, hb, ht, htR, hbR, hnR] at H
  simpa only [tripleFraction, ← Nat.card_eq_fintype_card] using H

end PermutationCornerStandardization
