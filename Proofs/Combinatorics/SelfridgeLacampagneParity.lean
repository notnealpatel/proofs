import Combinatorics.SelfridgeLacampagneFamilyCounterexample
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SelfridgeLacampagne

private theorem parity_btVal_not (L : List Bool) :
    btVal (L.map Bool.not) = -btVal L := by
  induction L with
  | nil => simp [btVal]
  | cons b t ih =>
    cases b <;>
      simp only [List.map_cons, Bool.not_false, Bool.not_true, btVal,
        Bool.false_eq_true, ↓reduceIte, ih] <;> ring

private theorem parity_btVal_append (L M : List Bool) :
    btVal (L ++ M) = btVal L + (3 : ℤ) ^ L.length * btVal M := by
  induction L with
  | nil => simp [btVal]
  | cons b t ih =>
    simp only [List.cons_append, btVal, List.length_cons, ih, pow_succ]
    ring

private theorem parity_words (n : ℕ) :
    ∃ V U : List Bool, V.length = 2 * n + 2 ∧ U.length = 2 * n + 2 ∧
      9 * btVal U = 4 * btVal V + 2 := by
  induction n with
  | zero => exact ⟨[true, true], [false, true], rfl, rfl, by decide⟩
  | succ n ih =>
    obtain ⟨V, U, hV, hU, hv⟩ := ih
    refine ⟨true :: true :: V.map Bool.not, true :: true :: U.map Bool.not,
      ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_map, hV]
      omega
    · simp only [List.length_cons, List.length_map, hU]
      omega
    · simp only [btVal, ↓reduceIte, parity_btVal_not]
      linarith

private theorem parity_signed_words (n : ℕ) :
    ∃ L M : List Bool, L ≠ [] ∧ M ≠ [] ∧
      btVal M = ((3 : ℤ) ^ (2 * n + 4) + 4) * btVal L := by
  obtain ⟨V, U, hV, hU, hv⟩ := parity_words n
  let W : List Bool := true :: false :: U
  have hW : W.length = 2 * n + 4 := by
    simp only [W, List.length_cons, hU]
  have hw : btVal W = 4 * btVal V := by
    simp only [W, btVal, Bool.false_eq_true, ↓reduceIte]
    linarith
  refine ⟨V, W ++ V, ?_, ?_, ?_⟩
  · intro he
    simp only [he, List.length_nil] at hV
    omega
  · simp [W]
  · rw [parity_btVal_append, hw, hW]
    ring

private theorem parity_positive_words (n : ℕ) :
    ∃ L M : List Bool, L ≠ [] ∧ M ≠ [] ∧ 0 < btVal L ∧
      btVal M = ((3 : ℤ) ^ (2 * n + 4) + 4) * btVal L := by
  obtain ⟨L, M, hL, hM, hv⟩ := parity_signed_words n
  have hn := btVal_ne_zero L hL
  by_cases hp : 0 < btVal L
  · exact ⟨L, M, hL, hM, hp, hv⟩
  · refine ⟨L.map Bool.not, M.map Bool.not, ?_, ?_, ?_, ?_⟩
    · simpa using hL
    · simpa using hM
    · rw [parity_btVal_not]
      omega
    · rw [parity_btVal_not, parity_btVal_not, hv]
      ring

/-- Every even exponent at least four gives a ratio of two positive A147991 terms. -/
theorem exists_memA147991_three_pow_add_four_mul_of_even (m : ℕ)
    (hm : 4 ≤ m) (heven : Even m) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ MemA147991 a ∧ MemA147991 b ∧
      a = (3 ^ m + 4) * b := by
  obtain ⟨r, hr⟩ := heven
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m = 2 * n + 4 :=
    ⟨r - 2, by omega⟩
  obtain ⟨L, M, hL, hM, hp, hv⟩ := parity_positive_words n
  rw [← hn] at hv
  have hk : (0 : ℤ) < 3 ^ m + 4 := by positivity
  have hmp : 0 < btVal M := by rw [hv]; exact mul_pos hk hp
  let a : ℕ := (btVal M).toNat
  let b : ℕ := (btVal L).toNat
  have ha : (a : ℤ) = btVal M := Int.toNat_of_nonneg (le_of_lt hmp)
  have hb : (b : ℤ) = btVal L := Int.toNat_of_nonneg (le_of_lt hp)
  refine ⟨a, b, ?_, ?_, ⟨M, hM, ha.symm⟩, ⟨L, hL, hb.symm⟩, ?_⟩
  · omega
  · omega
  · have hc : (a : ℤ) = ((3 : ℤ) ^ m + 4) * (b : ℤ) := by rw [ha, hb]; exact hv
    exact_mod_cast hc

/-- For exponents at least five, the Selfridge–Lacampagne family is obstructed exactly at odd exponents. -/
theorem isSLCounterexample_three_pow_add_four_iff_odd (m : ℕ) (hm : 5 ≤ m) :
    IsSLCounterexample (3 ^ m + 4) ↔ Odd m := by
  constructor
  · intro hc
    rcases Nat.even_or_odd m with heven | hodd
    · obtain ⟨a, b, _, _, ha, hb, hab⟩ :=
        exists_memA147991_three_pow_add_four_mul_of_even m (by omega) heven
      exact (hc.2.2 ⟨a, b, ha, hb, hab⟩).elim
    · exact hodd
  · exact isSLCounterexample_three_pow_add_four m hm

example : 4 ≤ (4 : ℕ) ∧ Even (4 : ℕ) := by decide
example : 0 < (340 : ℕ) ∧ 0 < (4 : ℕ) ∧ MemA147991 340 ∧ MemA147991 4 ∧
    340 = (3 ^ 4 + 4) * 4 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · exact ⟨[true, false, false, true, true, true], by decide, by decide⟩
  · exact ⟨[true, true], by decide, by decide⟩
example : 5 ≤ (5 : ℕ) ∧ Odd (5 : ℕ) := by decide

end SelfridgeLacampagne
