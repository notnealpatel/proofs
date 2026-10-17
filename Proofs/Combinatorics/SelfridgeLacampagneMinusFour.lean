import Combinatorics.SelfridgeLacampagne
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SelfridgeLacampagne

private theorem minusFour_btVal_not (L : List Bool) :
    btVal (L.map Bool.not) = -btVal L := by
  induction L with
  | nil => simp [btVal]
  | cons b t ih =>
    cases b <;>
      simp only [List.map_cons, Bool.not_false, Bool.not_true, btVal,
        Bool.false_eq_true, ↓reduceIte, ih] <;> ring

private theorem minusFour_btVal_append (L M : List Bool) :
    btVal (L ++ M) = btVal L + (3 : ℤ) ^ L.length * btVal M := by
  induction L with
  | nil => simp [btVal]
  | cons b t ih =>
    simp only [List.cons_append, btVal, List.length_cons, ih, pow_succ]
    ring

private theorem minusFour_words (n : ℕ) :
    ∃ V U : List Bool, V.length = 2 * n + 2 ∧ U.length = 2 * n + 2 ∧
      9 * btVal U + 4 * btVal V = 2 := by
  induction n with
  | zero => exact ⟨[false, false], [false, true], rfl, rfl, by decide⟩
  | succ n ih =>
    obtain ⟨V, U, hV, hU, hv⟩ := ih
    refine ⟨false :: false :: V.map Bool.not, true :: true :: U.map Bool.not,
      ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_map, hV]
      omega
    · simp only [List.length_cons, List.length_map, hU]
      omega
    · simp only [btVal, Bool.false_eq_true, ↓reduceIte, minusFour_btVal_not]
      linarith

private theorem minusFour_signed_words (n : ℕ) :
    ∃ L M : List Bool, L ≠ [] ∧ M ≠ [] ∧
      btVal M = ((3 : ℤ) ^ (2 * n + 4) - 4) * btVal L := by
  obtain ⟨V, U, hV, hU, hv⟩ := minusFour_words n
  let W : List Bool := true :: false :: U
  have hW : W.length = 2 * n + 4 := by
    simp only [W, List.length_cons, hU]
  have hw : btVal W = -4 * btVal V := by
    simp only [W, btVal, Bool.false_eq_true, ↓reduceIte]
    linarith
  refine ⟨V, W ++ V, ?_, ?_, ?_⟩
  · intro he
    simp only [he, List.length_nil] at hV
    omega
  · simp [W]
  · rw [minusFour_btVal_append, hw, hW]
    ring

private theorem minusFour_positive_words (n : ℕ) :
    ∃ L M : List Bool, L ≠ [] ∧ M ≠ [] ∧ 0 < btVal L ∧
      btVal M = ((3 : ℤ) ^ (2 * n + 4) - 4) * btVal L := by
  obtain ⟨L, M, hL, hM, hv⟩ := minusFour_signed_words n
  have hn := btVal_ne_zero L hL
  by_cases hp : 0 < btVal L
  · exact ⟨L, M, hL, hM, hp, hv⟩
  · refine ⟨L.map Bool.not, M.map Bool.not, ?_, ?_, ?_, ?_⟩
    · simpa using hL
    · simpa using hM
    · rw [minusFour_btVal_not]
      omega
    · rw [minusFour_btVal_not, minusFour_btVal_not, hv]
      ring

/-- Every even exponent at least two gives a ratio of two positive A147991 terms
with multiplier `3 ^ m - 4`, using natural subtraction. -/
theorem exists_memA147991_three_pow_sub_four_mul_of_even (m : ℕ)
    (hm : 2 ≤ m) (heven : Even m) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ MemA147991 a ∧ MemA147991 b ∧
      a = (3 ^ m - 4) * b := by
  by_cases hm2 : m = 2
  · subst m
    refine ⟨5, 1, by decide, by decide, ?_, ?_, by decide⟩
    · exact ⟨[false, false, true], by decide, by decide⟩
    · exact ⟨[true], by decide, by decide⟩
  obtain ⟨r, hr⟩ := heven
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m = 2 * n + 4 :=
    ⟨r - 2, by omega⟩
  obtain ⟨L, M, hL, hM, hp, hv⟩ := minusFour_positive_words n
  rw [← hn] at hv
  have hpow : 9 ≤ 3 ^ m := by
    calc
      9 = 3 ^ (2 : ℕ) := by decide
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by decide) hm
  have hk : (0 : ℤ) < 3 ^ m - 4 := by
    have hpowInt : (9 : ℤ) ≤ 3 ^ m := by exact_mod_cast hpow
    omega
  have hmp : 0 < btVal M := by rw [hv]; exact mul_pos hk hp
  let a : ℕ := (btVal M).toNat
  let b : ℕ := (btVal L).toNat
  have ha : (a : ℤ) = btVal M := Int.toNat_of_nonneg (le_of_lt hmp)
  have hb : (b : ℤ) = btVal L := Int.toNat_of_nonneg (le_of_lt hp)
  refine ⟨a, b, ?_, ?_, ⟨M, hM, ha.symm⟩, ⟨L, hL, hb.symm⟩, ?_⟩
  · omega
  · omega
  · have hc : (a : ℤ) = ((3 : ℤ) ^ m - 4) * (b : ℤ) := by
      rw [ha, hb]
      exact hv
    have hsub : ((3 ^ m - 4 : ℕ) : ℤ) = (3 : ℤ) ^ m - 4 := by
      rw [Nat.cast_sub (by omega : 4 ≤ 3 ^ m)]
      norm_cast
    apply Nat.cast_injective (R := ℤ)
    simpa only [Nat.cast_mul, hsub] using hc

example : 2 ≤ (2 : ℕ) ∧ Even (2 : ℕ) := by decide
example : 0 < (5 : ℕ) ∧ 0 < (1 : ℕ) ∧ MemA147991 5 ∧ MemA147991 1 ∧
    5 = (3 ^ 2 - 4) * 1 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · exact ⟨[false, false, true], by decide, by decide⟩
  · exact ⟨[true], by decide, by decide⟩
example : 2 ≤ (4 : ℕ) ∧ Even (4 : ℕ) := by decide
example : 0 < (308 : ℕ) ∧ 0 < (4 : ℕ) ∧ MemA147991 308 ∧ MemA147991 4 ∧
    308 = (3 ^ 4 - 4) * 4 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · exact ⟨[false, true, true, false, true, true], by decide, by decide⟩
  · exact ⟨[true, true], by decide, by decide⟩

end SelfridgeLacampagne
