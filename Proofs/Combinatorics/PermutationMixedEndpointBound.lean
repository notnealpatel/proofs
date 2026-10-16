import Combinatorics.PermutationOverlapBound
import Combinatorics.PermutationEndpointCounting

set_option autoImplicit false

namespace PermutationMixedEndpointBound

open PermutationOverlapBound PermutationEndpointCounting

attribute [local instance] Classical.propDecidable

/-- Actual permutations with the prescribed endpoints and no overlap of any proper
length at least two. -/
abbrev AvoidTwo {n : ℕ} [NeZero n] (q m l : Fin n) :=
  {π : Equiv.Perm (Fin n) // (π 0 = m ∧ π q = l) ∧
    ∀ (k : ℕ) (_hk : 2 ≤ k) (hkn : k < n), ¬ Overlap hkn π}

example {n : ℕ} [NeZero n] (q m l : Fin n) (π : AvoidTwo q m l) :
    (π.val 0 = m ∧ π.val q = l) ∧
      ∀ (k : ℕ), 2 ≤ k → ∀ (hkn : k < n), ¬ Overlap hkn π.val := π.property

private theorem remaining_value {n : ℕ} (p q r m l : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q) (π : FixedTwo p q m l) :
    π.val r ≠ m ∧ π.val r ≠ l := by
  constructor
  · intro h
    exact hrp (π.val.injective (h.trans π.property.1.symm))
  · intro h
    exact hrq (π.val.injective (h.trans π.property.2.symm))

private noncomputable def exchange {n : ℕ} (p q r m l : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q)
    (x : FixedTwo p q m l × {a : Fin n // a ≠ m ∧ a ≠ l}) :
    FixedTwo p q m l × {a : Fin n // a ≠ m ∧ a ≠ l} :=
  (⟨x.1.val.trans (Equiv.swap (x.1.val r) x.2.val), by
      constructor
      · change Equiv.swap (x.1.val r) x.2.val (x.1.val p) = m
        rw [x.1.property.1]
        exact Equiv.swap_apply_of_ne_of_ne
          (remaining_value p q r m l hrp hrq x.1).1.symm x.2.property.1.symm
      · change Equiv.swap (x.1.val r) x.2.val (x.1.val q) = l
        rw [x.1.property.2]
        exact Equiv.swap_apply_of_ne_of_ne
          (remaining_value p q r m l hrp hrq x.1).2.symm x.2.property.2.symm⟩,
    ⟨x.1.val r, remaining_value p q r m l hrp hrq x.1⟩)

private theorem exchange_value {n : ℕ} (p q r m l : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q)
    (x : FixedTwo p q m l × {a : Fin n // a ≠ m ∧ a ≠ l}) :
    (exchange p q r m l hrp hrq x).1.val r = x.2.val := by
  exact Equiv.swap_apply_left _ _

private theorem exchange_involutive {n : ℕ} (p q r m l : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q) :
    Function.Involutive (exchange p q r m l hrp hrq) := by
  intro x
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    change Equiv.swap ((exchange p q r m l hrp hrq x).1.val r) (x.1.val r)
      (Equiv.swap (x.1.val r) x.2.val (x.1.val i)) = x.1.val i
    rw [exchange_value, Equiv.swap_comm]
    exact Equiv.swap_apply_self _ _ _
  · apply Subtype.ext
    exact exchange_value p q r m l hrp hrq x

/-- At any position distinct from the two prescribed positions, exchanging remaining
labels gives the exact marginal count for an arbitrary label predicate. -/
theorem marginal_card {n : ℕ} (p q r m l : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q) (P : Fin n → Prop) :
    Fintype.card {π : FixedTwo p q m l // P (π.val r)} *
      Fintype.card {a : Fin n // a ≠ m ∧ a ≠ l} =
    Fintype.card (FixedTwo p q m l) *
      Fintype.card {a : Fin n // (a ≠ m ∧ a ≠ l) ∧ P a} := by
  classical
  let f := exchange p q r m l hrp hrq
  let e : ({π : FixedTwo p q m l // P (π.val r)} ×
      {a : Fin n // a ≠ m ∧ a ≠ l}) ≃
      (FixedTwo p q m l × {a : Fin n // (a ≠ m ∧ a ≠ l) ∧ P a}) :=
    { toFun := fun x => ((f (x.1.val, x.2)).1,
        ⟨x.1.val.val r, remaining_value p q r m l hrp hrq x.1.val, x.1.property⟩)
      invFun := fun y => (⟨(f (y.1, ⟨y.2.val, y.2.property.1⟩)).1, by
        change P ((exchange p q r m l hrp hrq _).1.val r)
        rw [exchange_value]
        exact y.2.property.2⟩,
        (f (y.1, ⟨y.2.val, y.2.property.1⟩)).2)
      left_inv := by
        intro x
        have h := exchange_involutive p q r m l hrp hrq (x.1.val, x.2)
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · exact congrArg (fun z : FixedTwo p q m l ×
            {a : Fin n // a ≠ m ∧ a ≠ l} => z.2) h
      right_inv := by
        intro y
        have h := exchange_involutive p q r m l hrp hrq
          (y.1, ⟨y.2.val, y.2.property.1⟩)
        apply Prod.ext
        · exact congrArg (fun z : FixedTwo p q m l ×
            {a : Fin n // a ≠ m ∧ a ≠ l} => z.1) h
        · apply Subtype.ext
          exact congrArg (fun z => z.2.val) h }
  simpa only [Fintype.card_prod] using Fintype.card_congr e

private theorem card_remaining {n : ℕ} (m l : Fin n) (hml : m ≠ l) :
    Fintype.card {a : Fin n // a ≠ m ∧ a ≠ l} = n - 2 := by
  classical
  rw [Fintype.card_of_subtype (Finset.univ \ {m, l}) (by simp)]
  simp [Finset.card_sdiff, hml]

/-- A marginal event at an unprescribed position has count times `n - 2` at most
the fiber count times the number of labels satisfying its predicate. -/
theorem marginal_bound {n : ℕ} (p q r m l : Fin n)
    (hrp : r ≠ p) (hrq : r ≠ q) (hml : m ≠ l) (P : Fin n → Prop) :
    Fintype.card {π : FixedTwo p q m l // P (π.val r)} * (n - 2) ≤
      Fintype.card (FixedTwo p q m l) * Fintype.card {a : Fin n // P a} := by
  rw [← card_remaining m l hml, marginal_card p q r m l hrp hrq P]
  apply Nat.mul_le_mul_left
  exact Fintype.card_le_of_injective
    (fun a : {a : Fin n // (a ≠ m ∧ a ≠ l) ∧ P a} =>
      (⟨a.val, a.property.2⟩ : {a : Fin n // P a}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {a : Fin n // P a} => z.val) h)

private theorem card_lower {n : ℕ} (m : Fin n)
    [Fintype {a : Fin n // a < m}] :
    Fintype.card {a : Fin n // a < m} = m.val := by
  rw [Fintype.card_of_subtype (Finset.Iio m) (by simp)]
  exact Fin.card_Iio m

private theorem card_upper {n : ℕ} (l : Fin n)
    [Fintype {a : Fin n // l < a}] :
    Fintype.card {a : Fin n // l < a} = n - 1 - l.val := by
  rw [Fintype.card_of_subtype (Finset.Ioi l) (by simp)]
  exact Fin.card_Ioi l

private theorem overlap_two_of_increasing {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (q : Fin n) (hq : q.val + 1 = n) (π : Equiv.Perm (Fin n))
    (hX : π 0 < π ⟨1, by omega⟩)
    (hY : π ⟨n - 2, by omega⟩ < π q) : Overlap (by omega : 2 < n) π := by
  have he : (⟨1 + (n - 2), by omega⟩ : Fin n) = q := by
    apply Fin.ext
    change 1 + (n - 2) = q.val
    omega
  have hz : (⟨0, by omega⟩ : Fin n) = 0 := by
    apply Fin.ext
    simp
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Nat.zero_add]
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · change π ⟨0, by omega⟩ < π ⟨1, by omega⟩ ↔
      π ⟨n - 2, by omega⟩ < π ⟨1 + (n - 2), by omega⟩
    rw [hz, he]
    exact iff_of_true hX hY
  · change π ⟨1, by omega⟩ < π ⟨0, by omega⟩ ↔
      π ⟨1 + (n - 2), by omega⟩ < π ⟨n - 2, by omega⟩
    rw [hz, he]
    exact iff_of_false (not_lt_of_gt hX) (not_lt_of_gt hY)
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)

/-- All-length avoidance forces a low second label or a high penultimate label;
no independence of these two coordinates is asserted. -/
theorem avoidTwo_mem_union {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n) (π : AvoidTwo q m l) :
    π.val ⟨1, by omega⟩ < m ∨ l < π.val ⟨n - 2, by omega⟩ := by
  by_contra h
  have hXne : π.val ⟨1, by omega⟩ ≠ m := by
    intro he
    have hi := π.val.injective (he.trans π.property.1.1.symm)
    have hv := congrArg Fin.val hi
    change 1 = 0 at hv
    omega
  have hYne : π.val ⟨n - 2, by omega⟩ ≠ l := by
    intro he
    have hi := π.val.injective (he.trans π.property.1.2.symm)
    have hv := congrArg Fin.val hi
    change n - 2 = q.val at hv
    omega
  have hX : π.val 0 < π.val ⟨1, by omega⟩ := by
    rw [π.property.1.1]
    exact lt_of_le_of_ne (not_lt.mp (fun hX => h (Or.inl hX))) hXne.symm
  have hY : π.val ⟨n - 2, by omega⟩ < π.val q := by
    rw [π.property.1.2]
    exact lt_of_le_of_ne (not_lt.mp (fun hY => h (Or.inr hY))) hYne
  exact π.property.2 2 (by omega) (by omega)
    (overlap_two_of_increasing hn q hq π.val hX hY)

/-- The actual all-overlap avoiders in a two-endpoint fiber satisfy the finite
mixed-endpoint bound, cross-multiplied over natural cardinalities. -/
theorem card_avoidTwo_mul_le {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n) (hml : m ≠ l) :
    Fintype.card (AvoidTwo q m l) * (n - 2) ≤
      Fintype.card (FixedTwo (0 : Fin n) q m l) * (m.val + (n - 1 - l.val)) := by
  classical
  let r : Fin n := ⟨1, by omega⟩
  let s : Fin n := ⟨n - 2, by omega⟩
  have hr0 : r ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change 1 = (0 : Fin n).val at hv
    simp at hv
  have hrq : r ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 1 = q.val at hv
    omega
  have hs0 : s ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change n - 2 = (0 : Fin n).val at hv
    simp only [Fin.val_zero] at hv
    omega
  have hsq : s ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change n - 2 = q.val at hv
    omega
  let A : FixedTwo (0 : Fin n) q m l → Prop := fun π => π.val r < m
  let B : FixedTwo (0 : Fin n) q m l → Prop := fun π => l < π.val s
  let inclusion : AvoidTwo q m l → {π : FixedTwo (0 : Fin n) q m l // A π ∨ B π} :=
    fun π => ⟨⟨π.val, π.property.1⟩, avoidTwo_mem_union hn q hq m l π⟩
  have hinj : Function.Injective inclusion := by
    intro π ρ he
    apply Subtype.ext
    exact congrArg (fun z : {π : FixedTwo (0 : Fin n) q m l // A π ∨ B π} =>
      z.val.val) he
  have hc : Fintype.card (AvoidTwo q m l) ≤
      Fintype.card {π // A π} + Fintype.card {π // B π} :=
    (Fintype.card_le_of_injective inclusion hinj).trans (Fintype.card_subtype_or A B)
  have hA : Fintype.card {π // A π} * (n - 2) ≤
      Fintype.card (FixedTwo (0 : Fin n) q m l) * m.val := by
    have h := marginal_bound 0 q r m l hr0 hrq hml (fun a => a < m)
    rw [card_lower] at h
    convert h using 1
    congr 1
    exact @Fintype.card_congr {π // A π}
      {π : FixedTwo (0 : Fin n) q m l // π.val r < m} inferInstance
      (@Subtype.fintype _ _ (fun _ => Classical.propDecidable _) inferInstance)
      (Equiv.refl _)
  have hB : Fintype.card {π // B π} * (n - 2) ≤
      Fintype.card (FixedTwo (0 : Fin n) q m l) * (n - 1 - l.val) := by
    have h := marginal_bound 0 q s m l hs0 hsq hml (fun a => l < a)
    rw [card_upper] at h
    convert h using 1
    congr 1
    exact @Fintype.card_congr {π // B π}
      {π : FixedTwo (0 : Fin n) q m l // l < π.val s} inferInstance
      (@Subtype.fintype _ _ (fun _ => Classical.propDecidable _) inferInstance)
      (Equiv.refl _)
  calc
    Fintype.card (AvoidTwo q m l) * (n - 2) ≤
        (Fintype.card {π // A π} + Fintype.card {π // B π}) * (n - 2) :=
      Nat.mul_le_mul_right _ hc
    _ = Fintype.card {π // A π} * (n - 2) +
        Fintype.card {π // B π} * (n - 2) := Nat.add_mul _ _ _
    _ ≤ Fintype.card (FixedTwo (0 : Fin n) q m l) * m.val +
        Fintype.card (FixedTwo (0 : Fin n) q m l) * (n - 1 - l.val) :=
      Nat.add_le_add hA hB
    _ = _ := (Nat.mul_add _ _ _).symm

/-- In the actual uniform two-endpoint fiber, the fraction avoiding every proper
prefix/suffix overlap of length at least two is at most
`(m + (n - 1 - l))/(n - 2)`, with zero-based labels. -/
theorem avoidTwo_fraction_le {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n) (hml : m ≠ l) :
    (Fintype.card (AvoidTwo q m l) : ℝ) /
      Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      ((m.val : ℝ) + (n - 1 - l.val : ℕ)) / ((n : ℝ) - 2) := by
  have h0q : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) :=
    fixedTwo_nonempty 0 q m l h0q hml
  have hF : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FixedTwo (0 : Fin n) q m l))
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  apply (div_le_div_iff₀ hF hD).mpr
  have hc : (Fintype.card (AvoidTwo q m l) : ℝ) * ((n - 2 : ℕ) : ℝ) ≤
      (Fintype.card (FixedTwo (0 : Fin n) q m l) : ℝ) *
        ((m.val + (n - 1 - l.val) : ℕ) : ℝ) := by
    exact_mod_cast card_avoidTwo_mul_le hn q hq m l hml
  rw [hcast, Nat.cast_add] at hc
  simpa only [mul_comm] using hc

example : 3 ≤ (3 : ℕ) ∧ (2 : Fin 3).val + 1 = 3 ∧
    (0 : Fin 3) ≠ 2 ∧ Nonempty (FixedTwo (0 : Fin 3) 2 0 2) :=
  ⟨by decide, rfl, by decide, fixedTwo_nonempty 0 2 0 2 (by decide) (by decide)⟩

example : Fintype.card (AvoidTwo (2 : Fin 3) 0 2) = 0 := by
  have hc := card_avoidTwo_mul_le (by decide : 3 ≤ 3) (2 : Fin 3) rfl 0 2 (by decide)
  simpa using hc

end PermutationMixedEndpointBound
