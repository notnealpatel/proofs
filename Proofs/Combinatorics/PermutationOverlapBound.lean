import Combinatorics.OverlapDisjointBlocks
import Combinatorics.PermutationOrderCounting

set_option autoImplicit false

namespace PermutationOverlapBound

open PermutationOrderCounting

/-- Equality of the actual comparison orders of the length-`k` prefix and suffix. -/
def Overlap {n k : ℕ} (hkn : k < n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin k,
    π ⟨i.val, lt_trans i.isLt hkn⟩ < π ⟨j.val, lt_trans j.isLt hkn⟩ ↔
    π ⟨i.val + (n - k), by omega⟩ < π ⟨j.val + (n - k), by omega⟩

example : Overlap (by decide : 2 < 3) (Equiv.refl _) := by
  intro i j
  change i.val < j.val ↔ i.val + (3 - 2) < j.val + (3 - 2)
  omega

/-- The fixed-first overlap event, as an actual subtype of permutations. -/
abbrev Event {n k : ℕ} [NeZero n] (hkn : k < n) (m : Fin n) :=
  {π : Equiv.Perm (Fin n) // π 0 = m ∧ Overlap hkn π}

example : Nonempty (Event (by decide : 2 < 3) (0 : Fin 3)) := by
  refine ⟨⟨Equiv.refl _, rfl, ?_⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (3 - 2) < j.val + (3 - 2)
  omega

/-- A positive step has at most one multiple in the half-open interval `[t,t+d)`. -/
theorem shift_unique {t d r s : ℕ} (_hd : 0 < d)
    (hr : t ≤ r * d) (hr' : r * d < t + d)
    (hs : t ≤ s * d) (hs' : s * d < t + d) : r = s := by
  apply le_antisymm
  · by_contra h
    have hh : s + 1 ≤ r := by omega
    have hm := Nat.mul_le_mul_right d hh
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  · by_contra h
    have hh : r + 1 ≤ s := by omega
    have hm := Nat.mul_le_mul_right d hh
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega

/-- The separating multiple is the canonical ceiling shift `(t-1)/d+1`. -/
theorem shift_eq_canonical {t d r : ℕ} (ht : 1 ≤ t) (hd : 0 < d)
    (hr : t ≤ r * d) (hr' : r * d < t + d) :
    r = (t - 1) / d + 1 := by
  have hdivision : (t - 1) % d + ((t - 1) / d) * d = t - 1 := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (t - 1) d
  have hmod := Nat.mod_lt (t - 1) hd
  have hm : ((t - 1) / d + 1) * d = (t - 1) / d * d + d := by
    rw [Nat.add_mul, Nat.one_mul]
  apply shift_unique hd hr hr'
  · rw [hm]
    omega
  · rw [hm]
    omega

example : (1 : ℕ) = (1 - 1) / 1 + 1 :=
  shift_eq_canonical (by decide) (by decide) (by decide) (by decide)

/-- For every admissible window, one fixed pair of disjoint blocks away from zero
captures the overlap event; the block choice is independent of the permutation. -/
theorem exists_capturing_blocks (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    ∃ a b : Fin (k / 2) ↪ Fin n,
      (∀ i, (a i).val ≠ 0) ∧ (∀ i, (b i).val ≠ 0) ∧
      Disjoint (Set.range a) (Set.range b) ∧
      ∀ π : Equiv.Perm (Fin n), Overlap hkn π → SameOrder π a b := by
  obtain ⟨r, _, hr, hr', hlast, _⟩ :=
    OverlapDisjointBlocks.exists_disjoint_half_blocks (fun i : ℕ => i) n k hk hkn
      (by intro i j _ _; omega)
  let a : Fin (k / 2) ↪ Fin n := ⟨fun i => ⟨i.val + 1, by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega⟩
  let b : Fin (k / 2) ↪ Fin n :=
    ⟨fun i => ⟨i.val + 1 + r * (n - k), by omega⟩, by
      intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val hij
      dsimp at hv
      omega⟩
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro i
    change i.val + 1 ≠ 0
    omega
  · intro i
    change i.val + 1 + r * (n - k) ≠ 0
    omega
  · apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val + 1 + r * (n - k) = i.val + 1 at hv
    omega
  · intro π hπ
    let f : ℕ → Fin n := fun i => if hi : i < n then π ⟨i, hi⟩ else π ⟨0, by omega⟩
    have hf (i : ℕ) (hi : i < n) : f i = π ⟨i, hi⟩ := by simp [f, hi]
    have hshift : ∀ i j : ℕ, i < k → j < k →
        (f i < f j ↔ f (i + (n - k)) < f (j + (n - k))) := by
      intro i j hi hj
      rw [hf i (by omega), hf j (by omega), hf (i + (n - k)) (by omega),
        hf (j + (n - k)) (by omega)]
      exact hπ ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨s, _, hs, hs', _, hcomp⟩ :=
      OverlapDisjointBlocks.exists_disjoint_half_blocks f n k hk hkn hshift
    have hrs : r = s :=
      (shift_eq_canonical (by omega) (by omega) hr hr').trans
        (shift_eq_canonical (by omega) (by omega) hs hs').symm
    subst s
    intro i j
    have hij := hcomp i.val j.val i.isLt j.isLt
    rw [hf (i.val + 1) (by omega), hf (j.val + 1) (by omega),
      hf (i.val + 1 + r * (n - k)) (by omega),
      hf (j.val + 1 + r * (n - k)) (by omega)] at hij
    exact hij

attribute [local instance] Classical.propDecidable

/-- In every prescribed-first-label fiber, the overlap count times `(k/2)!`
is at most the whole fiber count, including windows longer than half the permutation. -/
theorem card_event_mul_factorial_le {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 2 ≤ k) (hkn : k < n) (m : Fin n) :
    Fintype.card (Event hkn m) * Nat.factorial (k / 2) ≤
      Fintype.card (FixedFirst (0 : Fin n) m) := by
  classical
  obtain ⟨a, b, ha, _, hab, hcapture⟩ := exists_capturing_blocks n k hk hkn
  have hp : (0 : Fin n) ∉ Set.range a := by
    rintro ⟨i, hi⟩
    exact ha i (congrArg Fin.val hi)
  let inclusion : Event hkn m → Agreement 0 m a b :=
    fun π => ⟨π.val, π.property.1, hcapture π.val π.property.2⟩
  have hinj : Function.Injective inclusion := by
    intro π ρ h
    apply Subtype.ext
    exact congrArg (fun x : Agreement 0 m a b => x.val) h
  have hc := Fintype.card_le_of_injective inclusion hinj
  calc
    Fintype.card (Event hkn m) * Nat.factorial (k / 2) ≤
        Fintype.card (Agreement 0 m a b) * Nat.factorial (k / 2) :=
      Nat.mul_le_mul_right _ hc
    _ = Fintype.card (FixedFirst (0 : Fin n) m) :=
      card_agreement_mul_factorial 0 m a b hp hab

/-- The conditional fraction of a single overlap event is at most `1/(k/2)!`.
The denominator is positive because every fixed-first fiber is inhabited. -/
theorem event_fraction_le {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 2 ≤ k) (hkn : k < n) (m : Fin n) :
    (Fintype.card (Event hkn m) : ℝ) / Fintype.card (FixedFirst (0 : Fin n) m) ≤
      1 / (Nat.factorial (k / 2) : ℝ) := by
  have hF : (0 : ℝ) < Fintype.card (FixedFirst (0 : Fin n) m) := by
    rw [card_fixedFirst]
    exact_mod_cast Nat.factorial_pos (n - 1)
  have hT : (0 : ℝ) < Nat.factorial (k / 2) := by
    exact_mod_cast Nat.factorial_pos (k / 2)
  apply (div_le_div_iff₀ hF hT).mpr
  have hc := card_event_mul_factorial_le k hk hkn m
  simpa only [one_mul] using (show
    (Fintype.card (Event hkn m) : ℝ) * Nat.factorial (k / 2) ≤
      Fintype.card (FixedFirst (0 : Fin n) m) by exact_mod_cast hc)

example : 2 ≤ (4 : ℕ) ∧ 4 < (5 : ℕ) ∧
    Nonempty (Event (by decide : 4 < 5) (0 : Fin 5)) := by
  refine ⟨by decide, by decide, ⟨⟨Equiv.refl _, rfl, ?_⟩⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (5 - 4) < j.val + (5 - 4)
  omega

end PermutationOverlapBound
