import Combinatorics.PermutationEndpointZeroTwoExact

set_option autoImplicit false

namespace PermutationLowEndpointEventBound

open PermutationOrderCounting PermutationOverlapBound PermutationEndpointCounting
open PermutationEndpointOverlapBound PermutationEndpointZeroTwoExact

attribute [local instance] Classical.propDecidable

/-- A common deletion removes any specified position from two disjoint captures. -/
theorem delete_capture {n m : ℕ} (hm : 1 ≤ m) (u v : Fin m ↪ Fin n)
    (hd : Disjoint (Set.range u) (Set.range v)) (p : Fin n) :
    ∃ e : Fin (m - 1) ↪ Fin m, (∀ i, u (e i) ≠ p) ∧ (∀ i, v (e i) ≠ p) := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hchoose : ∃ j : Fin (t + 1), ∀ i, u i = p ∨ v i = p → i = j := by
    by_cases hu : ∃ i, u i = p
    · obtain ⟨j, hj⟩ := hu
      refine ⟨j, fun i hi => ?_⟩
      rcases hi with hi | hi
      · exact u.injective (hi.trans hj.symm)
      · exact False.elim (Set.disjoint_left.mp hd ⟨j, hj⟩ ⟨i, hi⟩)
    · by_cases hv : ∃ i, v i = p
      · obtain ⟨j, hj⟩ := hv
        refine ⟨j, fun i hi => ?_⟩
        rcases hi with hi | hi
        · exact False.elim (hu ⟨i, hi⟩)
        · exact v.injective (hi.trans hj.symm)
      · exact ⟨0, fun i hi => False.elim (hi.elim (fun h => hu ⟨i, h⟩) (fun h => hv ⟨i, h⟩))⟩
  obtain ⟨j, hj⟩ := hchoose
  refine ⟨j.succAboveEmb, ?_, ?_⟩
  · intro i hi
    exact Fin.succAbove_ne j i (hj _ (Or.inl hi))
  · intro i hi
    exact Fin.succAbove_ne j i (hj _ (Or.inr hi))

/-- A slice with one prescribed interior label has the required n-scale bound. -/
theorem card_slice_mul_le {n : ℕ} [NeZero n] (k : ℕ) (hk : 3 ≤ k)
    (hkn : k < n) (q : Fin n) (hq : q.val + 1 = n) (a b : Fin n) (hab : a ≠ b)
    (p c : Fin n) (hp0 : p ≠ 0) (hpq : p ≠ q) (hca : c ≠ a) (hcb : c ≠ b) :
    Fintype.card {π : EventTwo hkn q a b // π.val p = c} *
      (n - 2) * Nat.factorial (k / 3 - 1) ≤ Fintype.card (FixedTwo (0 : Fin n) q a b) := by
  classical
  obtain ⟨u, v, hu0, _, huq, _, hd, hc⟩ := exists_capturing_blocks n k hk hkn q hq
  obtain ⟨e, he, _⟩ := delete_capture (by omega : 1 ≤ k / 3) u v hd p
  let u' := e.trans u
  let v' := e.trans v
  have h0 : (0 : Fin n) ∉ Set.range u' := by
    rintro ⟨i, hi⟩
    exact hu0 (e i) (congrArg Fin.val hi)
  have hq' : q ∉ Set.range u' := by
    rintro ⟨i, hi⟩
    exact huq (e i) hi
  have hp : p ∉ Set.range u' := by
    rintro ⟨i, hi⟩
    exact he i hi
  have hd' : Disjoint (Set.range u') (Set.range v') := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, hi⟩ ⟨j, hj⟩
    exact Set.disjoint_left.mp hd ⟨e i, hi⟩ ⟨e j, hj⟩
  let f : {π : EventTwo hkn q a b // π.val p = c} →
      AgreementThree 0 q p a b c u' v' := fun π =>
    ⟨π.val.val, ⟨π.val.property.1, π.property⟩,
      fun i j => hc π.val.val π.val.property.2 (e i) (e j)⟩
  have hf : Function.Injective f := by
    intro π ρ h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : AgreementThree 0 q p a b c u' v' => z.val) h))
  have hcount := Fintype.card_le_of_injective f hf
  have heq := card_agreementThree_mul_factorial 0 q p a b c u' v' h0 hq' hp hd'
  have hfix := card_fixedThree_mul 0 q p a b c hp0 hpq hab hca hcb
  calc
    _ ≤ Fintype.card (AgreementThree 0 q p a b c u' v') *
        Nat.factorial (k / 3 - 1) * (n - 2) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_le_mul_right (n - 2) (Nat.mul_le_mul_right (Nat.factorial (k / 3 - 1)) hcount)
    _ = _ := by rw [heq, hfix]

/-- The two tagged sets of possible low labels have total size a+b-1. -/
theorem card_low_labels {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Fintype.card ({c : Fin n // c < a ∧ c ≠ b} ⊕ {c : Fin n // c < b ∧ c ≠ a}) =
      a.val + b.val - 1 := by
  classical
  have hcard (x y : Fin n) : Fintype.card {c : Fin n // c < x ∧ c ≠ y} =
      ((Finset.Iio x).erase y).card := by
    apply Fintype.card_of_subtype
    intro c
    simp [and_comm]
  rw [Fintype.card_sum, hcard, hcard]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [Finset.erase_eq_of_notMem (by simpa using not_lt_of_ge h.le),
      Finset.card_erase_of_mem (by simpa using h), Fin.card_Iio, Fin.card_Iio]
    have hv : a.val < b.val := h
    omega
  · rw [Finset.card_erase_of_mem (by simpa using h),
      Finset.erase_eq_of_notMem (by simpa using not_lt_of_ge h.le), Fin.card_Iio, Fin.card_Iio]
    have hv : b.val < a.val := h
    omega

/-- Every overlap has a low label at one of its two interior boundary positions. -/
theorem low_witness {n : ℕ} [NeZero n] (k : ℕ) (hk : 3 ≤ k) (hkn : k < n)
    (q : Fin n) (hq : q.val + 1 = n) (a b : Fin n) (π : EventTwo hkn q a b) :
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

/-- The all-length single-event bound, cross-multiplied in natural cardinalities. -/
theorem card_eventTwo_mul_le {n : ℕ} [NeZero n] (k : ℕ) (hk : 3 ≤ k)
    (hkn : k < n) (q : Fin n) (hq : q.val + 1 = n) (a b : Fin n) (hab : a ≠ b) :
    Fintype.card (EventTwo hkn q a b) * (n - 2) * Nat.factorial (k / 3 - 1) ≤
      (a.val + b.val - 1) * Fintype.card (FixedTwo (0 : Fin n) q a b) := by
  classical
  let W := {c : Fin n // c < a ∧ c ≠ b} ⊕ {c : Fin n // c < b ∧ c ≠ a}
  let p : W → Fin n := fun w => Sum.elim (fun _ => ⟨k - 1, by omega⟩)
    (fun _ => ⟨n - k, by omega⟩) w
  let c : W → Fin n := fun w => Sum.elim Subtype.val Subtype.val w
  have hp0 (w : W) : p w ≠ 0 := by
    cases w <;> intro h <;> have hv := congrArg Fin.val h <;> dsimp [p] at hv <;> omega
  have hpq (w : W) : p w ≠ q := by
    cases w <;> intro h <;> have hv := congrArg Fin.val h <;> dsimp [p] at hv <;> omega
  have hca (w : W) : c w ≠ a := by
    cases w with
    | inl w => exact ne_of_lt w.property.1
    | inr w => exact w.property.2
  have hcb (w : W) : c w ≠ b := by
    cases w with
    | inl w => exact w.property.2
    | inr w => exact ne_of_lt w.property.1
  have hw (π : EventTwo hkn q a b) : ∃ w : W, π.val (p w) = c w := by
    have hne (r : Fin n) (hr : r ≠ 0) (hrq : r ≠ q) : π.val r ≠ a ∧ π.val r ≠ b := by
      constructor
      · intro h; exact hr (π.val.injective (h.trans π.property.1.1.symm))
      · intro h; exact hrq (π.val.injective (h.trans π.property.1.2.symm))
    rcases low_witness k hk hkn q hq a b π with h | h
    · refine ⟨Sum.inl ⟨π.val ⟨k - 1, by omega⟩, h, ?_⟩, rfl⟩
      exact (hne _ (by intro h; have hv := congrArg Fin.val h; change k - 1 = 0 at hv; omega)
        (by intro h; have hv := congrArg Fin.val h; change k - 1 = q.val at hv; omega)).2
    · refine ⟨Sum.inr ⟨π.val ⟨n - k, by omega⟩, h, ?_⟩, rfl⟩
      exact (hne _ (by intro h; have hv := congrArg Fin.val h; change n - k = 0 at hv; omega)
        (by intro h; have hv := congrArg Fin.val h; change n - k = q.val at hv; omega)).1
  let f : EventTwo hkn q a b → Σ w : W, {π : EventTwo hkn q a b // π.val (p w) = c w} :=
    fun π => ⟨(hw π).choose, π, (hw π).choose_spec⟩
  have hf : Function.Injective f := by
    intro π ρ h
    exact congrArg (fun z => z.2.val) h
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hc
  calc
    _ ≤ (∑ w : W, Fintype.card {π : EventTwo hkn q a b // π.val (p w) = c w}) *
        ((n - 2) * Nat.factorial (k / 3 - 1)) := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right ((n - 2) * Nat.factorial (k / 3 - 1)) hc
    _ = ∑ w : W, Fintype.card {π : EventTwo hkn q a b // π.val (p w) = c w} *
        (n - 2) * Nat.factorial (k / 3 - 1) := by rw [Finset.sum_mul]; simp only [Nat.mul_assoc]
    _ ≤ ∑ _w : W, Fintype.card (FixedTwo (0 : Fin n) q a b) :=
      Finset.sum_le_sum (fun w _ => card_slice_mul_le k hk hkn q hq a b hab (p w) (c w)
        (hp0 w) (hpq w) (hca w) (hcb w))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; rw [card_low_labels a b hab]

/-- The actual conditional all-length overlap probability has the n-scale bound,
including intersecting prefix and suffix blocks. -/
theorem eventTwo_fraction_le {n : ℕ} [NeZero n] (k : ℕ) (hk : 3 ≤ k)
    (hkn : k < n) (q : Fin n) (hq : q.val + 1 = n) (a b : Fin n) (hab : a ≠ b) :
    (Fintype.card (EventTwo hkn q a b) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q a b) ≤
      ((a.val + b.val - 1 : ℕ) : ℝ) /
        (((n : ℝ) - 2) * (Nat.factorial (k / 3 - 1) : ℝ)) := by
  have h0q : (0 : Fin n) ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q a b) := fixedTwo_nonempty 0 q a b h0q hab
  have hD : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q a b) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FixedTwo (0 : Fin n) q a b))
  have hN : (0 : ℝ) < (n : ℝ) - 2 := by
    have hn : (3 : ℝ) < n := by exact_mod_cast (show 3 < n by omega)
    linarith
  have hT : (0 : ℝ) < Nat.factorial (k / 3 - 1) := by
    exact_mod_cast Nat.factorial_pos (k / 3 - 1)
  apply (div_le_div_iff₀ hD (mul_pos hN hT)).mpr
  have hc := card_eventTwo_mul_le k hk hkn q hq a b hab
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have hcR : (Fintype.card (EventTwo hkn q a b) : ℝ) *
      ((n : ℝ) - 2) * (Nat.factorial (k / 3 - 1) : ℝ) ≤
      ((a.val + b.val - 1 : ℕ) : ℝ) * Fintype.card (FixedTwo (0 : Fin n) q a b) := by
    rw [← hcast]
    exact_mod_cast hc
  simpa only [mul_assoc] using hcR

example : 3 ≤ (3 : ℕ) ∧ 3 < (4 : ℕ) ∧
    (3 : Fin 4).val + 1 = 4 ∧ (0 : Fin 4) ≠ 3 ∧
    Nonempty (EventTwo (by decide : 3 < 4) (3 : Fin 4) 0 3) := by
  refine ⟨by decide, by decide, rfl, by decide, ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (4 - 3) < j.val + (4 - 3)
  omega

example : 3 ≤ (6 : ℕ) ∧ 6 < (7 : ℕ) ∧ 7 < 2 * (6 : ℕ) ∧
    (6 : Fin 7).val + 1 = 7 ∧ (0 : Fin 7) ≠ 6 ∧
    Nonempty (EventTwo (by decide : 6 < 7) (6 : Fin 7) 0 6) := by
  refine ⟨by decide, by decide, by decide, rfl, by decide,
    ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (7 - 6) < j.val + (7 - 6)
  omega

example : Nonempty (Fin (3 / 3)) ∧ IsEmpty (Fin (3 / 3 - 1)) := by
  constructor
  · change Nonempty (Fin 1)
    infer_instance
  · change IsEmpty (Fin 0)
    infer_instance

example : (1 : Fin 4) ≠ 0 ∧ (1 : Fin 4) ≠ 3 ∧
    (1 : Fin 4) ≠ 0 ∧ (1 : Fin 4) ≠ 3 ∧
    Nonempty {π : EventTwo (by decide : 3 < 4) (3 : Fin 4) 0 3 // π.val 1 = 1} := by
  refine ⟨by decide, by decide, by decide, by decide,
    ⟨⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩, rfl⟩⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (4 - 3) < j.val + (4 - 3)
  omega

end PermutationLowEndpointEventBound
