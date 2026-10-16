import Combinatorics.PermutationOverlapBound
import Combinatorics.PermutationEndpointCounting

set_option autoImplicit false

namespace PermutationEndpointOverlapBound

open PermutationOrderCounting PermutationOverlapBound PermutationEndpointCounting

/-- Actual permutations with both prescribed endpoint labels and prefix/suffix overlap. -/
abbrev EventTwo {n k : ℕ} [NeZero n] (hkn : k < n) (q m l : Fin n) :=
  {π : Equiv.Perm (Fin n) // (π 0 = m ∧ π q = l) ∧ Overlap hkn π}

example {n k : ℕ} [NeZero n] (hkn : k < n) (q m l : Fin n)
    (π : EventTwo hkn q m l) :
    (π.val 0 = m ∧ π.val q = l) ∧ Overlap hkn π.val := π.property

/-- For every admissible window, one fixed pair of disjoint blocks away from both endpoints
captures the overlap event; the block choice is independent of the permutation. -/
theorem exists_capturing_blocks (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n)
    (q : Fin n) (hq : q.val + 1 = n) :
    ∃ a b : Fin (k / 3) ↪ Fin n,
      (∀ i, (a i).val ≠ 0) ∧ (∀ i, (b i).val ≠ 0) ∧
      (∀ i, a i ≠ q) ∧ (∀ i, b i ≠ q) ∧
      Disjoint (Set.range a) (Set.range b) ∧
      ∀ π : Equiv.Perm (Fin n), Overlap hkn π → SameOrder π a b := by
  have ht : 1 ≤ k / 3 := by omega
  have hthree : 3 * (k / 3) ≤ k := by omega
  have htwo : 2 * (k / 3) ≤ k := by omega
  obtain ⟨r, _, hr, hr', hlast, _⟩ :=
    OverlapDisjointBlocks.exists_disjoint_blocks (fun i : ℕ => i) n k (k / 3) (by omega) hkn ht htwo
      (by intro i j _ _; omega)
  have hterminal : k / 3 + r * (n - k) + 1 < n := by omega
  let a : Fin (k / 3) ↪ Fin n := ⟨fun i => ⟨i.val + 1, by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega⟩
  let b : Fin (k / 3) ↪ Fin n :=
    ⟨fun i => ⟨i.val + 1 + r * (n - k), by omega⟩, by
      intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val hij
      dsimp at hv
      omega⟩
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change i.val + 1 ≠ 0
    omega
  · intro i
    change i.val + 1 + r * (n - k) ≠ 0
    omega
  · intro i hi
    have hv := congrArg Fin.val hi
    change i.val + 1 = q.val at hv
    omega
  · intro i hi
    have hv := congrArg Fin.val hi
    change i.val + 1 + r * (n - k) = q.val at hv
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
      OverlapDisjointBlocks.exists_disjoint_blocks f n k (k / 3) (by omega) hkn ht htwo hshift
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

/-- In an actual two-endpoint fiber, one overlap event has at most the fiber count
 divided by `(k/3)!`; this also holds when the prescribed labels coincide. -/
theorem card_eventTwo_mul_factorial_le {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 3 ≤ k) (hkn : k < n) (q : Fin n) (hq : q.val + 1 = n) (m l : Fin n) :
    Fintype.card (EventTwo hkn q m l) * Nat.factorial (k / 3) ≤
      Fintype.card (FixedTwo (0 : Fin n) q m l) := by
  classical
  obtain ⟨a, b, ha, _, haq, _, hab, hcapture⟩ := exists_capturing_blocks n k hk hkn q hq
  have hp : (0 : Fin n) ∉ Set.range a := by
    rintro ⟨i, hi⟩
    exact ha i (congrArg Fin.val hi)
  have hqa : q ∉ Set.range a := by
    rintro ⟨i, hi⟩
    exact haq i hi
  let inclusion : EventTwo hkn q m l → AgreementTwo 0 q m l a b :=
    fun π => ⟨π.val, π.property.1, hcapture π.val π.property.2⟩
  have hinj : Function.Injective inclusion := by
    intro π ρ h
    apply Subtype.ext
    exact congrArg (fun x : AgreementTwo 0 q m l a b => x.val) h
  have hc := Fintype.card_le_of_injective inclusion hinj
  calc
    Fintype.card (EventTwo hkn q m l) * Nat.factorial (k / 3) ≤
        Fintype.card (AgreementTwo 0 q m l a b) * Nat.factorial (k / 3) :=
      Nat.mul_le_mul_right _ hc
    _ = Fintype.card (FixedTwo (0 : Fin n) q m l) :=
      card_agreementTwo_mul_factorial 0 q m l a b hp hqa hab

/-- For distinct prescribed endpoint labels, the actual conditional overlap fraction
 is at most `1/(k/3)!`. The terminal position and zero are necessarily distinct. -/
theorem eventTwo_fraction_le {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 3 ≤ k) (hkn : k < n) (q : Fin n) (hq : q.val + 1 = n)
    (m l : Fin n) (hml : m ≠ l) :
    (Fintype.card (EventTwo hkn q m l) : ℝ) /
      Fintype.card (FixedTwo (0 : Fin n) q m l) ≤
      1 / (Nat.factorial (k / 3) : ℝ) := by
  have hpq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = q.val at hv
    omega
  letI : Nonempty (FixedTwo (0 : Fin n) q m l) :=
    fixedTwo_nonempty 0 q m l hpq hml
  have hF : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q m l) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (FixedTwo (0 : Fin n) q m l))
  have hT : (0 : ℝ) < Nat.factorial (k / 3) := by
    exact_mod_cast Nat.factorial_pos (k / 3)
  apply (div_le_div_iff₀ hF hT).mpr
  have hc := card_eventTwo_mul_factorial_le k hk hkn q hq m l
  simpa only [one_mul] using (show
    (Fintype.card (EventTwo hkn q m l) : ℝ) * Nat.factorial (k / 3) ≤
      Fintype.card (FixedTwo (0 : Fin n) q m l) by exact_mod_cast hc)

example : 3 ≤ (3 : ℕ) ∧ 3 < (4 : ℕ) ∧
    (3 : Fin 4).val + 1 = 4 ∧ (0 : Fin 4) ≠ 3 ∧
    Nonempty (EventTwo (by decide : 3 < 4) (3 : Fin 4) 0 3) := by
  refine ⟨by decide, by decide, rfl, by decide, ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (4 - 3) < j.val + (4 - 3)
  omega

example : 3 ≤ (6 : ℕ) ∧ 6 < (7 : ℕ) ∧ 7 < 2 * (6 : ℕ) ∧
    6 / 3 = (2 : ℕ) ∧ (6 : Fin 7).val + 1 = 7 ∧ (0 : Fin 7) ≠ 6 ∧
    Nonempty (EventTwo (by decide : 6 < 7) (6 : Fin 7) 0 6) := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, by decide,
    ⟨⟨Equiv.refl _, ⟨rfl, rfl⟩, ?_⟩⟩⟩
  intro i j
  change i.val < j.val ↔ i.val + (7 - 6) < j.val + (7 - 6)
  omega

end PermutationEndpointOverlapBound
