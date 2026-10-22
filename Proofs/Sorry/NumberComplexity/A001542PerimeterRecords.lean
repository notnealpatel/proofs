/-
# A001542 — Lee: record perimeters of Pythagorean triangles minimizing c/P

## OEIS source (retrieved with `oeis show A001542`, 2026-10-21)

```
NAME:     a(n) = 6*a(n-1) - a(n-2) for n > 1, a(0)=0 and a(1)=2.
TERMS:    0,2,12,70,408,2378,13860,80782,470832,2744210,15994428,93222358,...
COMMENT (the conjecture):
  Conjecture: Numbers k such that c/m < k for all natural a^2 + b^2 = c^2
  (Pythagorean triples), a < b < c and a+b+c = m. Numbers which
  correspondingly minimize c/m are A002939. - _Lorraine Lee_, Jan 31 2020
```

## Reading of the (garbled) conjecture line

The comment is garbled as written.  The precise reading adopted here (from
the triage) is: order the integer right triangles `a < b < c` by perimeter
`P = a + b + c`; call `P` a *record* if some triangle of perimeter `P` has
`c / P` strictly smaller than every triangle of strictly smaller perimeter.
Then the record perimeters are exactly `A001542(n)` for `n ≥ 2`:
`12, 70, 408, 2378, ...`, the perimeters of the triangles with `b - a = 1`.
Degenerate triangles are excluded by `0 < a` (with `a = 0` the "triangle"
`(0, 1, 1)` would make `P = 2 = A001542(1)` a vacuous record).  The companion
claim about A002939 (maximizing `c / P`) is not formalized here.

## Status

Triage: open (no proof in the entry or the literature found).  Exhaustive
enumeration of all triangles of perimeter `≤ 2 * 10^7` gives the records
`12, 70, 408, 2378, 13860, 80782, 470832, 2744210, 15994428`, matching
A001542.  This module proves the conjecture (`isRecordPerimeter_iff`).

## Proof outline

* `c P' < c' P ↔ (b - a) c' < (b' - a') c` (`ratio_lt_iff`), because
  `(a + b)^2 + (b - a)^2 = 2 c^2`; so records minimize `(b - a) / c`.
* A record witness is primitive (`coprime_of_isRecord`): the reduced triangle
  has smaller perimeter and the same ratio.
* A primitive triangle has `b - a = 1` or `b - a ≥ 7`
  (`leg_diff_of_coprime`, by reduction mod 4, 3, 5).
* `b - a = 1` triangles are exactly the Pell triangles (`descent`), whose
  perimeters are `A001542(j + 1)` (`perim_eq`).
* `b - a ≥ 7` cannot be a record (`no_record_of_seven_le`): beating the last
  Pell triangle `k` of smaller perimeter forces `c > 7 c_k`, hence a
  perimeter above the next Pell perimeter.
* Every Pell triangle `j ≥ 1` is a record (`isRecordPerimeter_pell`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001542PerimeterRecords

/-! ## Definition layer -/

/-- OEIS A001542, exactly as in the entry's NAME: `a(0) = 0`, `a(1) = 2`,
`a(n) = 6 a(n-1) - a(n-2)`.  The natural subtraction never truncates
(`a001542_rec`). -/
def a001542 : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => 6 * a001542 (n + 1) - a001542 n

example : a001542 0 = 0 := rfl
example : a001542 1 = 2 := rfl
example : a001542 2 = 12 := rfl
example : a001542 3 = 70 := rfl
example : a001542 4 = 408 := rfl
example : a001542 5 = 2378 := rfl
example : a001542 6 = 13860 := rfl
example : a001542 7 = 80782 := rfl
example : a001542 8 = 470832 := rfl
example : a001542 9 = 2744210 := rfl

/-- An integer right triangle with legs `0 < a < b` and hypotenuse `c`
(the entry's "a^2 + b^2 = c^2 (Pythagorean triples), a < b < c"; `b < c`
is automatic, `0 < a` excludes the degenerate `(0, b, b)`). -/
def IsPythTriangle (a b c : ℕ) : Prop := 0 < a ∧ a < b ∧ a ^ 2 + b ^ 2 = c ^ 2

example : IsPythTriangle 3 4 5 := by unfold IsPythTriangle; decide
example : IsPythTriangle 20 21 29 := by unfold IsPythTriangle; decide
example : IsPythTriangle 6 8 10 := by unfold IsPythTriangle; decide
example : ¬ IsPythTriangle 0 1 1 := by unfold IsPythTriangle; decide

/-- `P` is a record perimeter for minimizing `c / P`: some right triangle of
perimeter `P` has `c / P` strictly smaller than every right triangle of
strictly smaller perimeter.  All denominators are positive perimeters. -/
def IsRecordPerimeter (P : ℕ) : Prop :=
  ∃ a b c : ℕ, IsPythTriangle a b c ∧ a + b + c = P ∧
    ∀ a' b' c' : ℕ, IsPythTriangle a' b' c' → a' + b' + c' < P →
      (c : ℚ) / (P : ℚ) < (c' : ℚ) / ((a' + b' + c' : ℕ) : ℚ)

/-! ## Pell triangles `(A, A + 1, C)` -/

/-- Pairs `(A_j, C_j)` with `A_j^2 + (A_j + 1)^2 = C_j^2`, starting from the
degenerate `(0, 1)`: `(0,1), (3,5), (20,29), (119,169), ...`. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | j + 1 => (3 * (pellPair j).1 + 2 * (pellPair j).2 + 1,
      4 * (pellPair j).1 + 3 * (pellPair j).2 + 2)

/-- Shorter leg of the `j`-th Pell triangle. -/
def pellA (j : ℕ) : ℕ := (pellPair j).1

/-- Hypotenuse of the `j`-th Pell triangle. -/
def pellC (j : ℕ) : ℕ := (pellPair j).2

example : pellA 1 = 3 ∧ pellC 1 = 5 := ⟨rfl, rfl⟩
example : pellA 2 = 20 ∧ pellC 2 = 29 := ⟨rfl, rfl⟩
example : pellA 3 = 119 ∧ pellC 3 = 169 := ⟨rfl, rfl⟩

/-- `A_0 = 0`. -/
@[simp] theorem pellA_zero : pellA 0 = 0 := rfl

/-- `C_0 = 1`. -/
@[simp] theorem pellC_zero : pellC 0 = 1 := rfl

/-- Recurrence for the shorter leg. -/
theorem pellA_succ (j : ℕ) : pellA (j + 1) = 3 * pellA j + 2 * pellC j + 1 := rfl

/-- Recurrence for the hypotenuse. -/
theorem pellC_succ (j : ℕ) : pellC (j + 1) = 4 * pellA j + 3 * pellC j + 2 := rfl

/-- The Pell identity `(2 A_j + 1)^2 + 1 = 2 C_j^2`. -/
theorem pell_eq (j : ℕ) : (2 * pellA j + 1) ^ 2 + 1 = 2 * pellC j ^ 2 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pellA_succ, pellC_succ]; nlinarith [ih]

/-- A001542 is monotone step by step. -/
theorem a001542_le_succ (n : ℕ) : a001542 n ≤ a001542 (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [a001542]; omega

/-- The defining recurrence holds without truncation:
`a(n+2) + a(n) = 6 a(n+1)`. -/
theorem a001542_rec (n : ℕ) : a001542 (n + 2) + a001542 n = 6 * a001542 (n + 1) := by
  have hle := a001542_le_succ n
  rw [a001542]; omega

/-- The perimeter of the `j`-th Pell triangle is `A001542(j + 1)`. -/
theorem perim_eq (j : ℕ) : 2 * pellA j + 1 + pellC j = a001542 (j + 1) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | j + 2, ih =>
      have h1 := ih j (by omega)
      have h2 : 2 * pellA (j + 1) + 1 + pellC (j + 1) = a001542 (j + 2) :=
        ih (j + 1) (by omega)
      have hr : a001542 (j + 2 + 1) + a001542 (j + 1) = 6 * a001542 (j + 2) :=
        a001542_rec (j + 1)
      simp only [pellA_succ, pellC_succ] at h2 ⊢
      omega

/-- Descent for `s^2 - 2 c^2 = -1`: every natural solution is a Pell pair
`(2 A_j + 1, C_j)`. -/
theorem descent (c : ℕ) :
    ∀ s : ℕ, s ^ 2 + 1 = 2 * c ^ 2 → ∃ j, s = 2 * pellA j + 1 ∧ c = pellC j := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro s hs
    rcases Nat.lt_or_ge c 3 with hc | hc
    · interval_cases c
      · omega
      · have hs2 : s < 2 := by nlinarith
        interval_cases s
        · omega
        · exact ⟨0, rfl, rfl⟩
      · have hs3 : s < 3 := by nlinarith
        interval_cases s <;> omega
    · have h1 : 4 * c ≤ 3 * s := by nlinarith
      have h2 : 2 * s ≤ 3 * c := by nlinarith
      have h3 : c < s := by nlinarith
      obtain ⟨j, hj1, hj2⟩ := ih (3 * c - 2 * s) (by omega) (3 * s - 4 * c) (by
        zify [h1, h2]
        have hz : (s : ℤ) ^ 2 + 1 = 2 * (c : ℤ) ^ 2 := by exact_mod_cast hs
        linear_combination hz)
      refine ⟨j + 1, ?_, ?_⟩
      · rw [pellA_succ]; omega
      · rw [pellC_succ]; omega

/-- `j ≤ C_j`. -/
theorem le_pellC (j : ℕ) : j ≤ pellC j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pellC_succ]; omega

/-- `5 ≤ C_j` for `j ≥ 1`. -/
theorem five_le_pellC (j : ℕ) (hj : 1 ≤ j) : 5 ≤ pellC j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [pellC_succ]
  have hi := le_pellC i
  cases i with
  | zero => decide
  | succ i => omega

/-- For `j ≥ 1`, `(A_j, A_j + 1, C_j)` is a genuine right triangle. -/
theorem pellTriangle (j : ℕ) (hj : 1 ≤ j) :
    IsPythTriangle (pellA j) (pellA j + 1) (pellC j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
  refine ⟨by rw [pellA_succ]; omega, by omega, ?_⟩
  nlinarith [pell_eq (i + 1)]

/-! ## Comparing `c / P` -/

/-- `(a + b)^2 + (b - a)^2 = 2 c^2` for a right triangle `(a, a + d, c)`. -/
theorem sq_sum_identity {a d c : ℕ} (h : a ^ 2 + (a + d) ^ 2 = c ^ 2) :
    (2 * a + d) ^ 2 + d ^ 2 = 2 * c ^ 2 := by
  rw [← h]; ring

/-- Cross-multiplied comparison: `c P' < c' P ↔ d c' < d' c`, where `d, d'`
are the leg differences. -/
theorem mul_lt_iff {a d c a' d' c' : ℕ}
    (h : a ^ 2 + (a + d) ^ 2 = c ^ 2) (h' : a' ^ 2 + (a' + d') ^ 2 = c' ^ 2) :
    c * (a' + (a' + d') + c') < c' * (a + (a + d) + c) ↔ d * c' < d' * c := by
  have e : (2 * a + d) ^ 2 + d ^ 2 = 2 * c ^ 2 := sq_sum_identity h
  have e' : (2 * a' + d') ^ 2 + d' ^ 2 = 2 * c' ^ 2 := sq_sum_identity h'
  have e1 : (c * (2 * a' + d')) ^ 2 + (c * d') ^ 2 = 2 * (c * c') ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← mul_add, e']; ring
  have e2 : (c' * (2 * a + d)) ^ 2 + (c' * d) ^ 2 = 2 * (c * c') ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← mul_add, e]; ring
  have step1 : c * (a' + (a' + d') + c') < c' * (a + (a + d) + c) ↔
      c * (2 * a' + d') < c' * (2 * a + d) := by
    constructor <;> intro hlt <;> nlinarith
  rw [step1, ← Nat.pow_lt_pow_iff_left (n := 2) (by norm_num),
    ← Nat.pow_lt_pow_iff_left (a := d * c') (n := 2) (by norm_num)]
  constructor <;> intro hlt <;> nlinarith

/-- For right triangles, `c / P < c' / P'` iff `(b - a) c' < (b' - a') c`:
minimizing `c / P` is minimizing `(b - a) / c`. -/
theorem ratio_lt_iff {a b c a' b' c' : ℕ} (h : IsPythTriangle a b c)
    (h' : IsPythTriangle a' b' c') :
    (c : ℚ) / ((a + b + c : ℕ) : ℚ) < (c' : ℚ) / ((a' + b' + c' : ℕ) : ℚ) ↔
      (b - a) * c' < (b' - a') * c := by
  obtain ⟨ha, hab, he⟩ := h
  obtain ⟨ha', hab', he'⟩ := h'
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab.le
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hab'.le
  have hP : (0 : ℚ) < ((a + (a + d) + c : ℕ) : ℚ) := by positivity
  have hP' : (0 : ℚ) < ((a' + (a' + d') + c' : ℕ) : ℚ) := by positivity
  rw [div_lt_div_iff₀ hP hP', Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
    ← mul_lt_iff he he']
  exact_mod_cast Iff.rfl

/-! ## Pell perimeters are records -/

/-- For `j ≥ 1`, the perimeter `A001542(j + 1)` of the `j`-th Pell triangle is
a record. -/
theorem isRecordPerimeter_pell (j : ℕ) (hj : 1 ≤ j) :
    IsRecordPerimeter (a001542 (j + 1)) := by
  have hT := pellTriangle j hj
  have hper : pellA j + (pellA j + 1) + pellC j = a001542 (j + 1) := by
    rw [← perim_eq]; omega
  refine ⟨pellA j, pellA j + 1, pellC j, hT, hper, ?_⟩
  intro a' b' c' hT' hP'
  rw [← hper, ratio_lt_iff hT hT', Nat.add_sub_cancel_left, one_mul]
  obtain ⟨ha', hab', he'⟩ := hT'
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hab'.le
  rw [Nat.add_sub_cancel_left]
  have e := pell_eq j
  have e' := sq_sum_identity he'
  rcases Nat.lt_or_ge d' 2 with hd | hd
  · -- `d' = 1`: a smaller-perimeter Pell-type triangle has a smaller hypotenuse.
    have hd1 : d' = 1 := by omega
    subst hd1
    by_contra hc
    have hc' : pellC j ≤ c' := by omega
    have hlt : a' < pellA j := by omega
    have hsq : (2 * a' + 1) ^ 2 < (2 * pellA j + 1) ^ 2 :=
      Nat.pow_lt_pow_left (by omega) (by norm_num)
    nlinarith
  · -- `d' ≥ 2`: `2 c' < P' < P < 3 C_j`, so `c' < 2 C_j ≤ d' C_j`.
    have hsum : c' < a' + (a' + d') := by nlinarith
    have hS : 2 * pellA j + 1 < 2 * pellC j := by nlinarith
    nlinarith

/-! ## Every record is a Pell perimeter -/

/-- A record witness is primitive: otherwise the reduced triangle has smaller
perimeter and the same ratio `c / P`. -/
theorem coprime_of_isRecord {a b c : ℕ} (hT : IsPythTriangle a b c)
    (hR : ∀ a' b' c' : ℕ, IsPythTriangle a' b' c' → a' + b' + c' < a + b + c →
      (c : ℚ) / ((a + b + c : ℕ) : ℚ) < (c' : ℚ) / ((a' + b' + c' : ℕ) : ℚ)) :
    Nat.gcd a b = 1 := by
  obtain ⟨ha, hab, he⟩ := hT
  set g := Nat.gcd a b with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  by_contra hne
  have hg2 : 2 ≤ g := by omega
  obtain ⟨a₁, ha₁⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b₁, hb₁⟩ := Nat.gcd_dvd_right a b
  rw [← hg] at ha₁ hb₁
  have hgc2 : g ^ 2 ∣ c ^ 2 := ⟨a₁ ^ 2 + b₁ ^ 2, by rw [← he, ha₁, hb₁]; ring⟩
  obtain ⟨c₁, hc₁⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp hgc2
  have ha₁pos : 0 < a₁ := by
    rcases Nat.eq_zero_or_pos a₁ with h0 | h0
    · rw [h0, mul_zero] at ha₁; omega
    · exact h0
  have hab₁ : a₁ < b₁ := by
    rw [ha₁, hb₁] at hab; exact Nat.lt_of_mul_lt_mul_left hab
  have he₁ : a₁ ^ 2 + b₁ ^ 2 = c₁ ^ 2 := by
    have h2 : g ^ 2 * (a₁ ^ 2 + b₁ ^ 2) = g ^ 2 * c₁ ^ 2 := by
      rw [ha₁, hb₁, hc₁] at he; rw [← mul_pow, ← he]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hT₁ : IsPythTriangle a₁ b₁ c₁ := ⟨ha₁pos, hab₁, he₁⟩
  have hper : a₁ + b₁ + c₁ < a + b + c := by
    rw [ha₁, hb₁, hc₁]; nlinarith
  have hlt := hR a₁ b₁ c₁ hT₁ hper
  rw [ratio_lt_iff ⟨ha, hab, he⟩ hT₁, ha₁, hb₁, hc₁, ← Nat.mul_sub] at hlt
  have heq : g * (b₁ - a₁) * c₁ = (b₁ - a₁) * (g * c₁) := by ring
  omega

/-- Mod 4: `x^2 + (x + 2)^2 = y^2` forces `x` even. -/
theorem zmod4_two : ∀ x y : ZMod 4, x ^ 2 + (x + 2) ^ 2 = y ^ 2 → x.val % 2 = 0 := by
  decide

/-- Mod 4: `x^2 + (x + 4)^2 = y^2` forces `x` even. -/
theorem zmod4_four : ∀ x y : ZMod 4, x ^ 2 + (x + 4) ^ 2 = y ^ 2 → x.val % 2 = 0 := by
  decide

/-- Mod 4: `x^2 + (x + 6)^2 = y^2` forces `x` even. -/
theorem zmod4_six : ∀ x y : ZMod 4, x ^ 2 + (x + 6) ^ 2 = y ^ 2 → x.val % 2 = 0 := by
  decide

/-- Mod 3: `x^2 + (x + 3)^2 = y^2` forces `x = 0`. -/
theorem zmod3_three : ∀ x y : ZMod 3, x ^ 2 + (x + 3) ^ 2 = y ^ 2 → x.val = 0 := by
  decide

/-- Mod 5: `x^2 + (x + 5)^2 = y^2` forces `x = 0`. -/
theorem zmod5_five : ∀ x y : ZMod 5, x ^ 2 + (x + 5) ^ 2 = y ^ 2 → x.val = 0 := by
  decide

/-- Reduction of `a^2 + (a + d)^2 = c^2` into `ZMod n`. -/
theorem natCast_pyth (n : ℕ) {a d c : ℕ} (h : a ^ 2 + (a + d) ^ 2 = c ^ 2) :
    (a : ZMod n) ^ 2 + ((a : ZMod n) + (d : ZMod n)) ^ 2 = (c : ZMod n) ^ 2 := by
  exact_mod_cast congrArg (Nat.cast : ℕ → ZMod n) h

/-- In a primitive right triangle `(a, a + d, c)` with `d ≥ 1`, the leg
difference is `1` or at least `7`. -/
theorem leg_diff_of_coprime {a d c : ℕ} (h : a ^ 2 + (a + d) ^ 2 = c ^ 2)
    (hcop : Nat.gcd a (a + d) = 1) (hd : 1 ≤ d) : d = 1 ∨ 7 ≤ d := by
  by_contra hne
  have key : ∀ q : ℕ, q ∣ a → q ∣ d → q = 1 := by
    intro q hqa hqd
    have hq : q ∣ Nat.gcd a (a + d) := Nat.dvd_gcd hqa (dvd_add hqa hqd)
    rw [hcop] at hq
    exact Nat.dvd_one.mp hq
  have hd' : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl
  · have hx := zmod4_two _ _ (natCast_pyth 4 h)
    rw [ZMod.val_natCast] at hx
    have h2 := key 2 (by omega) (by norm_num); omega
  · have hx := zmod3_three _ _ (natCast_pyth 3 h)
    rw [ZMod.val_natCast] at hx
    have h3 := key 3 (by omega) (by norm_num); omega
  · have hx := zmod4_four _ _ (natCast_pyth 4 h)
    rw [ZMod.val_natCast] at hx
    have h2 := key 2 (by omega) (by norm_num); omega
  · have hx := zmod5_five _ _ (natCast_pyth 5 h)
    rw [ZMod.val_natCast] at hx
    have h5 := key 5 (by omega) (by norm_num); omega
  · have hx := zmod4_six _ _ (natCast_pyth 4 h)
    rw [ZMod.val_natCast] at hx
    have h2 := key 2 (by omega) (by norm_num); omega

/-- A right triangle `(a, a + d, c)` with `d ≥ 7` never witnesses a record:
beating the last Pell triangle `k` of smaller perimeter forces `c > 7 C_k`
and `5 (2a + d) ≥ 7 c`, so its perimeter exceeds the next Pell perimeter
`5 (2 A_k + 1) + 7 C_k < 14.5 C_k`. -/
theorem no_record_of_seven_le {a d c P : ℕ} (hT : IsPythTriangle a (a + d) c)
    (hP : a + (a + d) + c = P) (hd : 7 ≤ d)
    (hR : ∀ a' b' c' : ℕ, IsPythTriangle a' b' c' → a' + b' + c' < P →
      (c : ℚ) / (P : ℚ) < (c' : ℚ) / ((a' + b' + c' : ℕ) : ℚ)) : False := by
  have he := hT.2.2
  have hbc : a + d < c := by nlinarith [hT.1]
  have hex : ∃ m, P ≤ 2 * pellA m + 1 + pellC m :=
    ⟨P, by have hle := le_pellC P; omega⟩
  classical
  set m := Nat.find hex with hm
  have hmP : P ≤ 2 * pellA m + 1 + pellC m := Nat.find_spec hex
  have hm2 : 2 ≤ m := by
    by_contra hlt
    interval_cases m
    · rw [pellA_zero, pellC_zero] at hmP; omega
    · rw [pellA_succ, pellC_succ, pellA_zero, pellC_zero] at hmP; omega
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hkP : ¬ P ≤ 2 * pellA k + 1 + pellC k := Nat.find_min hex (by omega)
  have hTk := pellTriangle k hk1
  have hlt := hR (pellA k) (pellA k + 1) (pellC k) hTk (by omega)
  rw [← hP, ratio_lt_iff hT hTk, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
    one_mul] at hlt
  rw [hk, pellA_succ, pellC_succ] at hmP
  have hC5 := five_le_pellC k hk1
  have ek := pell_eq k
  have e := sq_sum_identity he
  have h5d : 5 * d < c := by nlinarith
  have h7C : 7 * pellC k < c := by nlinarith
  have hs : 7 * c ≤ 5 * (2 * a + d) := by
    have hsq : (7 * c) ^ 2 ≤ (5 * (2 * a + d)) ^ 2 := by nlinarith
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq
  have hS : 2 * (2 * pellA k + 1) < 3 * pellC k := by
    have hsq : (2 * (2 * pellA k + 1)) ^ 2 < (3 * pellC k) ^ 2 := by nlinarith
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp hsq
  omega

/-! ## The conjecture -/

/-- **Lee's conjecture (A001542, Lorraine Lee, Jan 31 2020), proved.**

Precise reading of the garbled comment "Numbers k such that c/m < k for all
natural a^2 + b^2 = c^2 (Pythagorean triples), a < b < c and a+b+c = m":
a perimeter `P` is a record for minimizing `c / P` over integer right
triangles `0 < a < b < c` (some triangle of perimeter `P` has `c / P` strictly
below every triangle of smaller perimeter) iff `P = A001542(n)` for some
`n ≥ 2`, i.e. `P ∈ {12, 70, 408, 2378, ...}`. -/
theorem isRecordPerimeter_iff (P : ℕ) :
    IsRecordPerimeter P ↔ ∃ n, 2 ≤ n ∧ P = a001542 n := by
  constructor
  · rintro ⟨a, b, c, hT, hP, hR⟩
    have hcop := coprime_of_isRecord hT (by rw [hP]; exact hR)
    obtain ⟨ha, hab, he⟩ := hT
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab.le
    rcases leg_diff_of_coprime he hcop (by omega) with rfl | hd
    · have e := sq_sum_identity he
      obtain ⟨j, hj1, hj2⟩ := descent c (2 * a + 1) (by omega)
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; rw [pellA_zero] at hj1; omega
        · exact h0
      refine ⟨j + 1, by omega, ?_⟩
      rw [← perim_eq, ← hP]; omega
    · exact (no_record_of_seven_le ⟨ha, hab, he⟩ hP hd hR).elim
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    exact isRecordPerimeter_pell j (by omega)

/-- The first record perimeter is `12`, attained by `(3, 4, 5)`
(non-vacuity of `IsRecordPerimeter`). -/
example : IsRecordPerimeter 12 := (isRecordPerimeter_iff 12).2 ⟨2, le_rfl, rfl⟩

/-- `30` (the perimeter of `(5, 12, 13)`) is not a record perimeter. -/
example : ¬ IsRecordPerimeter 30 := by
  rw [isRecordPerimeter_iff]
  rintro ⟨n, hn, h⟩
  have hmono : Monotone a001542 := monotone_nat_of_le_succ a001542_le_succ
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have hn2 : n = 2 := by omega
    subst hn2
    exact absurd h (by decide)
  · have h70 : a001542 3 ≤ a001542 n := hmono h3
    have h3v : a001542 3 = 70 := rfl
    omega

end Candidates.A001542PerimeterRecords
