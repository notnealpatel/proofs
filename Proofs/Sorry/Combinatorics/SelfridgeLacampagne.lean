import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace SelfridgeLacampagne

/-- Little-endian balanced ternary with only the signs `+1` and `-1`. -/
def btVal : List Bool → ℤ
  | [] => 0
  | b :: t => (if b then 1 else -1) + 3 * btVal t

example : btVal [] = 0 := rfl
example : btVal [false, true] = 2 := by decide

/-- A natural number has a nonempty balanced ternary expansion without zero trits. -/
def MemA147991 (n : ℕ) : Prop := ∃ L : List Bool, L ≠ [] ∧ btVal L = (n : ℤ)

example : MemA147991 1 := ⟨[true], by decide, rfl⟩

/-- The set generated from `1` by the operations `3x-1` and `3x+1`. -/
inductive GenA147991 : ℤ → Prop
  | one : GenA147991 1
  | lo {x : ℤ} : GenA147991 x → GenA147991 (3 * x - 1)
  | hi {x : ℤ} : GenA147991 x → GenA147991 (3 * x + 1)

example : GenA147991 1 := .one

/-- Positive, nonmultiples of three that are not quotients of two A147991 terms. -/
def IsSLCounterexample (k : ℕ) : Prop :=
  0 < k ∧ ¬ (3 ∣ k) ∧ ¬ ∃ a b : ℕ, MemA147991 a ∧ MemA147991 b ∧ a = k * b

/-- A nonempty expansion has residue `1` or `-1` modulo three. -/
theorem btVal_mod_three (L : List Bool) (hL : L ≠ []) :
    btVal L % 3 = 1 ∨ btVal L % 3 = 2 := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons b t => cases b <;> simp only [btVal, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A nonempty expansion never has value zero. -/
theorem btVal_ne_zero (L : List Bool) (hL : L ≠ []) : btVal L ≠ 0 := by
  have hmod := btVal_mod_three L hL
  omega

/-- A nonempty expansion is not divisible by three. -/
theorem btVal_not_dvd_three (L : List Bool) (hL : L ≠ []) :
    ¬ (3 : ℤ) ∣ btVal L := by
  intro hd
  have hm := btVal_mod_three L hL
  have hz := Int.emod_eq_zero_of_dvd hd
  omega

/-- Every generated integer is positive. -/
theorem genA147991_pos {x : ℤ} (h : GenA147991 x) : 0 < x := by
  induction h with
  | one => omega
  | lo h ih => omega
  | hi h ih => omega

/-- Every generated integer has a nonempty sign expansion. -/
theorem genA147991_expansion {x : ℤ} (h : GenA147991 x) :
    ∃ L : List Bool, L ≠ [] ∧ btVal L = x := by
  induction h with
  | one => exact ⟨[true], by decide, rfl⟩
  | lo h ih =>
    obtain ⟨L, hL, hv⟩ := ih
    refine ⟨false :: L, List.cons_ne_nil _ _, ?_⟩
    simp only [btVal, Bool.false_eq_true, ↓reduceIte, hv]
    omega
  | hi h ih =>
    obtain ⟨L, hL, hv⟩ := ih
    refine ⟨true :: L, List.cons_ne_nil _ _, ?_⟩
    simp only [btVal, ↓reduceIte, hv]
    omega

/-- Every positive value of a sign expansion belongs to the generated set. -/
theorem genA147991_of_btVal_pos (L : List Bool) (h : 0 < btVal L) :
    GenA147991 (btVal L) := by
  induction L with
  | nil => simp [btVal] at h
  | cons b t ih =>
    by_cases ht : t = []
    · subst t
      cases b
      · simp [btVal] at h
      · exact GenA147991.one
    · have hne := btVal_ne_zero t ht
      have hp : 0 < btVal t := by
        cases b <;> simp only [btVal, Bool.false_eq_true, ↓reduceIte] at h <;> omega
      have hg := ih hp
      cases b
      · simpa [btVal, sub_eq_add_neg, add_comm] using GenA147991.lo hg
      · simpa [btVal, add_comm] using GenA147991.hi hg

/-- The expansion and generative characterizations agree for positive naturals. -/
theorem memA147991_iff_gen (n : ℕ) (hn : 0 < n) :
    MemA147991 n ↔ GenA147991 (n : ℤ) := by
  constructor
  · rintro ⟨L, hL, hv⟩
    have hp : 0 < btVal L := by omega
    simpa only [hv] using genA147991_of_btVal_pos L hp
  · exact genA147991_expansion

example : 0 < (1 : ℕ) ∧ MemA147991 1 ∧ GenA147991 (1 : ℤ) :=
  ⟨by decide, ⟨[true], by decide, rfl⟩, .one⟩

/-- Three cannot have a nonempty expansion without zero trits. -/
theorem three_not_memA147991 : ¬ MemA147991 3 := by
  rintro ⟨L, hL, hv⟩
  have hm := btVal_mod_three L hL
  omega

/-- Carries when both suffixes still have trits, including the initial zero. -/
private def RB : Finset ℤ :=
  let p : Finset ℤ := {44,46,48,50,60,62,66,68,82,98,102,104,110,116}
  insert 0 (p ∪ p.image (fun z => -z))

/-- Carries after the right expansion ends. -/
private def RL : Finset ℤ :=
  let p : Finset ℤ := {42,44,46,48,50,55,60,61,62,64,66,67,68,82,97,98,99,102,103,104,105,110,115,116,117,119,121,122,123}
  p ∪ p.image (fun z => -z)

/-- Carries after the left expansion ends. -/
private def RM : Finset ℤ :=
  let p : Finset ℤ := {3,6,8,12,15,17,21,23,27,33,35,37,39,44,46,48,50,60,62,66,68,82,98,102,104,110,116}
  p ∪ p.image (fun z => -z)

example : 0 ∈ RB ∧ 82 ∈ RB ∧ -82 ∈ RB := by decide
example : 42 ∈ RL ∧ -42 ∈ RL ∧ 0 ∉ RL := by decide
example : 3 ∈ RM ∧ -3 ∈ RM ∧ 0 ∉ RM := by decide

set_option maxRecDepth 10000 in
private theorem carry_inclusions : ∀ q ∈ RB, q ≠ 0 → q ∈ RL ∧ q ∈ RM := by decide

private theorem carry_nonzero : 0 ∉ RL ∧ 0 ∉ RM := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem carry_both : ∀ q ∈ RB, ∀ d e : Bool,
    3 ∣ q + 247 * (if d then 1 else -1) - (if e then 1 else -1) →
    (q + 247 * (if d then 1 else -1) - (if e then 1 else -1)) / 3 ∈ RB ∧
    (q + 247 * (if d then 1 else -1) - (if e then 1 else -1)) / 3 ≠ 0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem carry_left : ∀ q ∈ RL, ∀ d : Bool,
    3 ∣ q + 247 * (if d then 1 else -1) →
    (q + 247 * (if d then 1 else -1)) / 3 ∈ RL ∧
    (q + 247 * (if d then 1 else -1)) / 3 ≠ 0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem carry_right : ∀ q ∈ RM, ∀ e : Bool,
    3 ∣ q - (if e then 1 else -1) →
    (q - (if e then 1 else -1)) / 3 ∈ RM ∧
    (q - (if e then 1 else -1)) / 3 ≠ 0 := by decide

private theorem right_suffix_impossible (M : List Bool) :
    ∀ q ∈ RM, btVal M ≠ q := by
  induction M with
  | nil =>
    intro q hq heq
    have hz : q = 0 := by simpa [btVal] using heq.symm
    exact carry_nonzero.2 (hz ▸ hq)
  | cons e t ih =>
    intro q hq heq
    change (if e then 1 else -1) + 3 * btVal t = q at heq
    have hd : 3 ∣ q - (if e then 1 else -1) := ⟨btVal t, by omega⟩
    have hc := carry_right q hq e hd
    have hv := Int.ediv_mul_cancel hd
    exact ih _ hc.1 (by omega)

private theorem left_suffix_impossible (L : List Bool) :
    ∀ q ∈ RL, (0 : ℤ) ≠ 247 * btVal L + q := by
  induction L with
  | nil =>
    intro q hq heq
    have hz : q = 0 := by simpa [btVal] using heq.symm
    exact carry_nonzero.1 (hz ▸ hq)
  | cons d t ih =>
    intro q hq heq
    change 0 = 247 * ((if d then 1 else -1) + 3 * btVal t) + q at heq
    have hd : 3 ∣ q + 247 * (if d then 1 else -1) :=
      ⟨-247 * btVal t, by omega⟩
    have hc := carry_left q hq d hd
    have hv := Int.ediv_mul_cancel hd
    exact ih _ hc.1 (by omega)

private theorem both_suffix_impossible (L : List Bool) :
    ∀ (M : List Bool) q, q ∈ RB → q ≠ 0 → btVal M ≠ 247 * btVal L + q := by
  induction L with
  | nil =>
    intro M q hq hn heq
    have hc := carry_inclusions q hq hn
    exact right_suffix_impossible M q hc.2 (by simpa [btVal] using heq)
  | cons d t ih =>
    intro M q hq hn heq
    cases M with
    | nil =>
      have hc := carry_inclusions q hq hn
      exact left_suffix_impossible (d :: t) q hc.1 heq
    | cons e u =>
      change (if e then 1 else -1) + 3 * btVal u =
        247 * ((if d then 1 else -1) + 3 * btVal t) + q at heq
      have hd : 3 ∣ q + 247 * (if d then 1 else -1) - (if e then 1 else -1) :=
        ⟨btVal u - 247 * btVal t, by omega⟩
      have hc := carry_both q hq d e hd
      have hv := Int.ediv_mul_cancel hd
      exact ih u _ hc.1 hc.2 (by omega)

/-- No pair of nonempty sign expansions has values in ratio 247, of any length. -/
theorem btVal_ne_247_mul (L M : List Bool) (hL : L ≠ []) (hM : M ≠ []) :
    btVal M ≠ 247 * btVal L := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons d t =>
    cases M with
    | nil => exact (hM rfl).elim
    | cons e u =>
      intro heq
      change (if e then 1 else -1) + 3 * btVal u =
        247 * ((if d then 1 else -1) + 3 * btVal t) at heq
      have hd : 3 ∣ (0 : ℤ) + 247 * (if d then 1 else -1) - (if e then 1 else -1) :=
        ⟨btVal u - 247 * btVal t, by omega⟩
      have hzero : (0 : ℤ) ∈ RB := by decide
      have hc := carry_both 0 hzero d e hd
      have hv := Int.ediv_mul_cancel hd
      exact both_suffix_impossible t u _ hc.1 hc.2 (by omega)

example : ([true] : List Bool) ≠ [] ∧ ([false, true] : List Bool) ≠ [] := by decide

/-- The genuine, unbounded first counterexample to Selfridge–Lacampagne is 247. -/
theorem isSLCounterexample_247 : IsSLCounterexample 247 := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨a, b, ⟨M, hM, hvM⟩, ⟨L, hL, hvL⟩, hab⟩
  apply btVal_ne_247_mul L M hL hM
  rw [hvM, hvL, hab]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

example : IsSLCounterexample 247 := isSLCounterexample_247

/-- The original universal quotient conjecture is false, by its instance at 247. -/
theorem selfridgeLacampagne_false :
    ¬ ∀ k : ℕ, 0 < k → ¬ (3 ∣ k) → ∃ a b : ℕ, MemA147991 a ∧ MemA147991 b ∧ a = k * b := by
  intro h
  exact isSLCounterexample_247.2.2 (h 247 (by decide) (by decide))

/-- The archived length-14 assertion follows from the unbounded obstruction. -/
theorem no_small_witness_247 :
    ∀ L M : List Bool, L.length ≤ 14 → M.length ≤ 14 → 0 < btVal L →
      btVal M ≠ 247 * btVal L := by
  intro L M _ _ hp
  have hL : L ≠ [] := by
    intro heq
    simp [heq, btVal] at hp
  by_cases hM : M = []
  · subst M
    simp only [btVal]
    omega
  · exact btVal_ne_247_mul L M hL hM

example : ([true] : List Bool).length ≤ 14 ∧ 0 < btVal [true] := by decide

end SelfridgeLacampagne
