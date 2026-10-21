/-
# A249265 — Barker's linear recurrence for the greedy Fibonacci-average sequence

## OEIS source (`oeis show A249265`, retrieved 2026-10-21)

```
NAME:     Sequence of distinct least nonnegative numbers such that the average
          of the first n terms is a Fibonacci number.
TERMS:    0,2,1,5,7,3,17,29,8,58,13,109,21,203,34,370,55,667,89,1189,144,2102,
          233,3689,377,6435,610,11166,987,19287,1597,33181,2584,56882,4181,
          97205,6765,165643,10946,281546,17711,477443,28657,807941,46368,
          1364590,75025,2300689,121393
COMMENT:  This is the same concept as A248982, but with a(1) = 0, the zeroth
          Fibonacci number.
FORMULA (the conjecture):
  Conjecture: a(n) = 2*a(n-2) + a(n-4) - 2*a(n-6) - a(n-8) for n > 15.
  - _Colin Barker_, Oct 24 2014
FORMULA (unattributed, unproved in the entry):
  For n > 5, a(2*n-3) = A000045(n).
```

## Status

Triage: open. No proof in the entry. Fried (arXiv:2410.07237, pp. 11-12)
treats the twin sequence A248982 and leaves its Fibonacci collision lemma
unproved; Le (arXiv:2509.26138) claimed it, but that paper was withdrawn.

## What this file proves (no `sorry`)

* `term_eq_closedForm`: the greedy sequence equals an explicit closed form;
* `a_two_mul_sub_three`: the entry's formula `a(2n-3) = F(n)` for `n > 5`;
* `a_two_mul`: `a(2j) = F(j+1) + 2j F(j)` for `j ≥ 4`;
* `barker`: Barker's conjecture for every `n > 15`;
* `a_first_terms`: all 49 listed terms.

The key step is the collision lemma `fib_ne_evenTerm`. For `i ≥ 1`,
`F(i+2) + 2(i+1)F(i+1)` is never Fibonacci. The proof uses `Nat.fib_add`
and the coprimality of `F(i)` and `F(i+1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A249265GreedyDistinctNonnegative

open Nat

/-- `Admissible l x` says that `x` may follow the terms `l` chosen so far: `x` is not
among them and the average of `l ++ [x]` is a Fibonacci number, i.e.
`l.sum + x = (l.length + 1) * fib k` for some `k` (so `fib 0 = 0` counts). -/
def Admissible (l : List ℕ) (x : ℕ) : Prop :=
  x ∉ l ∧ ∃ k, l.sum + x = (l.length + 1) * fib k

/-- Every finite list of chosen terms admits some admissible continuation, so the
greedy choice `Nat.find` is well defined. -/
theorem exists_admissible (l : List ℕ) : ∃ x, Admissible l x := by
  have hfib : 2 * l.sum + 1 ≤ fib (2 * l.sum + 3) :=
    Nat.fib_add_two_strictMono.id_le (2 * l.sum + 1)
  have hmul : fib (2 * l.sum + 3) ≤ (l.length + 1) * fib (2 * l.sum + 3) :=
    Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨(l.length + 1) * fib (2 * l.sum + 3) - l.sum, ?_, 2 * l.sum + 3, by omega⟩
  intro hmem
  have hle : (l.length + 1) * fib (2 * l.sum + 3) - l.sum ≤ l.sum := List.le_sum_of_mem hmem
  omega

open Classical in
/-- `prefixTerms n` is the list `[a(1), ..., a(n)]` of the first `n` greedy terms. -/
noncomputable def prefixTerms : ℕ → List ℕ
  | 0 => []
  | n + 1 => prefixTerms n ++ [Nat.find (exists_admissible (prefixTerms n))]

open Classical in
/-- `term n = a(n+1)`: the least nonnegative integer admissible after
`prefixTerms n` (0-indexed greedy term). -/
noncomputable def term (n : ℕ) : ℕ := Nat.find (exists_admissible (prefixTerms n))

/-- The OEIS sequence A249265 with its 1-based offset: `a n = term (n - 1)` for
`1 ≤ n`. (`a 0` is a junk value and is never used in the statements below.) -/
noncomputable def a (n : ℕ) : ℕ := term (n - 1)

/-- The prefix of length `n` lists the 0-indexed terms `term 0, ..., term (n-1)`. -/
theorem prefixTerms_eq (n : ℕ) : prefixTerms n = (List.range n).map term := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixTerms, List.range_succ, List.map_append, ← ih]; rfl

/-- `evenTerm i = F(i+2) + 2(i+1) F(i+1)`, the value of `a(2(i+1))`. -/
def evenTerm (i : ℕ) : ℕ := fib (i + 2) + 2 * (i + 1) * fib (i + 1)

/-- Explicit 0-indexed closed form of the sequence: the eight initial values, then
`F(i+2)` at index `2i` and `evenTerm i` at index `2i+1` (`i ≥ 4`). -/
def closedForm (n : ℕ) : ℕ :=
  if n < 8 then [0, 2, 1, 5, 7, 3, 17, 29].getD n 0
  else if n % 2 = 0 then fib (n / 2 + 2) else evenTerm (n / 2)

/-- The closed form at index `2i` (`i ≥ 4`) is `F(i+2)`. -/
theorem closedForm_two_mul {i : ℕ} (hi : 4 ≤ i) : closedForm (2 * i) = fib (i + 2) := by
  have h1 : ¬ 2 * i < 8 := by omega
  have h2 : 2 * i % 2 = 0 := by omega
  have h3 : 2 * i / 2 = i := by omega
  simp only [closedForm, h1, h2, h3, if_false, if_true]

/-- The closed form at index `2i+1` (`i ≥ 3`) is `evenTerm i`. -/
theorem closedForm_two_mul_add_one {i : ℕ} (hi : 3 ≤ i) :
    closedForm (2 * i + 1) = evenTerm i := by
  rcases (show i = 3 ∨ 4 ≤ i by omega) with h | h
  · subst h; decide
  have h1 : ¬ 2 * i + 1 < 8 := by omega
  have h2 : ¬ (2 * i + 1) % 2 = 0 := by omega
  have h3 : (2 * i + 1) / 2 = i := by omega
  simp only [closedForm, h1, h2, h3, if_false]

/-- `closedPrefix n` lists the first `n` values of `closedForm`. -/
def closedPrefix (n : ℕ) : List ℕ := (List.range n).map closedForm

/-- An integer strictly between consecutive Fibonacci numbers `F(b) < c < F(b+1)` is
not a Fibonacci number. -/
theorem fib_ne_of_between {b c : ℕ} (h1 : fib b < c) (h2 : c < fib (b + 1)) (m : ℕ) :
    fib m ≠ c := by
  intro hm
  subst hm
  have hlt : b < m := by
    by_contra h
    exact absurd (Nat.fib_mono (not_lt.mp h)) (not_le.mpr h1)
  exact absurd (Nat.fib_mono (Nat.succ_le_of_lt hlt)) (not_le.mpr h2)

/-- `2i + 3 ≤ F(i+2)` for `i ≥ 5`. -/
theorem two_mul_add_three_le_fib (i : ℕ) (hi : 5 ≤ i) : 2 * i + 3 ≤ fib (i + 2) := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ i hi ih =>
    have h1 : 2 ≤ fib (i + 1) := by
      calc 2 = fib 3 := by decide
      _ ≤ fib (i + 1) := Nat.fib_mono (by omega)
    have h2 : fib (i + 1 + 2) = fib (i + 1) + fib (i + 2) := Nat.fib_add_two
    omega

/-- **Collision lemma.** For `i ≥ 1`, `F(i+2) + 2(i+1) F(i+1)` is never a Fibonacci
number. (For `i = 0` the value `3 = F(4)` is Fibonacci.) -/
theorem fib_ne_evenTerm (i : ℕ) (hi : 1 ≤ i) (m : ℕ) : fib m ≠ evenTerm i := by
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i by omega) with h | h | h | h | hi5
  · subst h; exact fib_ne_of_between (b := 5) (by decide) (by decide) m
  · subst h; exact fib_ne_of_between (b := 7) (by decide) (by decide) m
  · subst h; exact fib_ne_of_between (b := 8) (by decide) (by decide) m
  · subst h; exact fib_ne_of_between (b := 10) (by decide) (by decide) m
  intro hm
  unfold evenTerm at hm
  have hpos : 0 < fib (i + 1) := fib_pos.mpr (by omega)
  have hipos : 0 < fib i := fib_pos.mpr (by omega)
  have h2 : fib (i + 2) = fib i + fib (i + 1) := fib_add_two
  have hm4 : i + 4 ≤ m := by
    by_contra h
    have hle : fib m ≤ fib (i + 3) := fib_mono (by omega)
    have h3 : fib (i + 3) = fib (i + 1) + fib (i + 2) := fib_add_two
    nlinarith
  obtain ⟨r, rfl⟩ : ∃ r, m = i + r + 1 := ⟨m - i - 1, by omega⟩
  have hr : 3 ≤ r := by omega
  rw [fib_add] at hm
  have hfr2 : 2 ≤ fib r := by
    calc 2 = fib 3 := by decide
    _ ≤ fib r := fib_mono hr
  rcases le_or_gt (i + 1) r with hri | hri
  · have hfr : fib (i + 1) ≤ fib r := fib_mono hri
    have hfr1 : fib (i + 2) ≤ fib (r + 1) := fib_mono (by omega)
    have hbig := two_mul_add_three_le_fib i hi5
    nlinarith
  · have hfr : fib r ≤ fib i := fib_mono (by omega)
    obtain ⟨d, hd⟩ : ∃ d, fib r = d + 1 := ⟨fib r - 1, by omega⟩
    have hsum : fib i * d + fib (i + 1) * fib (r + 1) = fib (i + 1) * (2 * i + 3) := by
      rw [hd, h2] at hm; nlinarith
    have hdvd : fib (i + 1) ∣ fib i * d := by
      have hall : fib (i + 1) ∣ fib i * d + fib (i + 1) * fib (r + 1) :=
        hsum ▸ dvd_mul_right _ _
      exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp hall
    have hd' : fib (i + 1) ∣ d := (fib_coprime_fib_succ i).symm.dvd_of_dvd_mul_left hdvd
    have hdpos : 0 < d := by omega
    have hle : fib (i + 1) ≤ d := Nat.le_of_dvd hdpos hd'
    have hmono : fib i ≤ fib (i + 1) := fib_le_fib_succ
    omega


/-- Appending one closed-form value to the prefix. -/
theorem closedPrefix_succ (n : ℕ) : closedPrefix (n + 1) = closedPrefix n ++ [closedForm n] := by
  simp [closedPrefix, List.range_succ]

/-- The prefix sum grows by the next closed-form value. -/
theorem closedPrefix_sum_succ (n : ℕ) : (closedPrefix (n + 1)).sum = (closedPrefix n).sum + closedForm n := by
  simp [closedPrefix_succ]

/-- The closed-form prefix of length `n` has length `n`. -/
theorem closedPrefix_length (n : ℕ) : (closedPrefix n).length = n := by simp [closedPrefix]

/-- Membership in the closed-form prefix. -/
theorem mem_closedPrefix {n x : ℕ} : x ∈ closedPrefix n ↔ ∃ j < n, closedForm j = x := by
  simp [closedPrefix]

/-- After `2i` terms (`i ≥ 4`) the sum is `2i F(i+2)`, so the average is `F(i+2)`. -/
theorem closedPrefix_sum_two_mul {i : ℕ} (hi : 4 ≤ i) : (closedPrefix (2 * i)).sum = 2 * i * fib (i + 2) := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ i hi ih =>
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, closedPrefix_sum_succ, closedPrefix_sum_succ, ih,
      closedForm_two_mul hi, closedForm_two_mul_add_one (by omega), evenTerm]
    have h : fib (i + 1 + 2) = fib (i + 1) + fib (i + 2) := fib_add_two
    rw [h]; ring

/-- After `2i+1` terms (`i ≥ 4`) the sum is `(2i+1) F(i+2)`. -/
theorem closedPrefix_sum_two_mul_add_one {i : ℕ} (hi : 4 ≤ i) :
    (closedPrefix (2 * i + 1)).sum = (2 * i + 1) * fib (i + 2) := by
  rw [closedPrefix_sum_succ, closedPrefix_sum_two_mul hi, closedForm_two_mul hi]; ring


/-- `F(k) < F(m)` forces `k < m`. -/
theorem lt_of_fib_lt {k m : ℕ} (h : fib k < fib m) : k < m := by
  by_contra h'
  exact absurd (fib_mono (not_lt.mp h')) (not_le.mpr h)

/-- `F(i+1) ≤ 2 F(i)` for `i ≥ 1`. -/
theorem fib_succ_le_two_mul {i : ℕ} (hi : 1 ≤ i) : fib (i + 1) ≤ 2 * fib i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h : fib (j + 1 + 1) = fib j + fib (j + 1) := fib_add_two
  have h2 : fib j ≤ fib (j + 1) := fib_le_fib_succ
  omega

/-- `evenTerm` is strictly increasing. -/
theorem evenTerm_lt_evenTerm {s t : ℕ} (h : s < t) : evenTerm s < evenTerm t := by
  have h1 : fib (s + 2) ≤ fib (t + 2) := fib_mono (by omega)
  have h2 : fib (s + 1) ≤ fib (t + 1) := fib_mono (by omega)
  have hpos : 0 < fib (s + 1) := fib_pos.mpr (by omega)
  unfold evenTerm
  nlinarith

/-- The eight initial values are at most `7`, or equal `17` or `29`. -/
theorem closedForm_lt_eight_cases :
    ∀ j < 8, closedForm j ≤ 7 ∨ closedForm j = 17 ∨ closedForm j = 29 := by
  decide

/-- At index `2i` (`i ≥ 4`) the candidate `F(i+2)` has not been used before. -/
theorem fib_notMem_closedPrefix_two_mul {i : ℕ} (hi : 4 ≤ i) : fib (i + 2) ∉ closedPrefix (2 * i) := by
  rw [mem_closedPrefix]
  rintro ⟨j, hj, hjeq⟩
  rcases lt_or_ge j 8 with h8 | h8
  · have h8f : 8 ≤ fib (i + 2) := by
      calc 8 = fib 6 := by decide
      _ ≤ fib (i + 2) := fib_mono (by omega)
    rcases closedForm_lt_eight_cases j h8 with h | h | h
    · omega
    · exact fib_ne_of_between (b := 7) (by decide) (by decide) (i + 2) (hjeq.symm.trans h)
    · exact fib_ne_of_between (b := 8) (by decide) (by decide) (i + 2) (hjeq.symm.trans h)
  · obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [closedForm_two_mul (by omega)] at hjeq
      have hlt : t < i := by omega
      exact absurd hjeq (Nat.fib_add_two_strictMono hlt).ne
    · rw [closedForm_two_mul_add_one (by omega)] at hjeq
      exact fib_ne_evenTerm t (by omega) (i + 2) hjeq.symm

/-- Every value among the first `2i+1` terms (`i ≥ 4`) is below `evenTerm i`. -/
theorem lt_evenTerm_of_mem {i x : ℕ} (hi : 4 ≤ i) (hx : x ∈ closedPrefix (2 * i + 1)) :
    x < evenTerm i := by
  rw [mem_closedPrefix] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have h4 : evenTerm 4 ≤ evenTerm i := by
    rcases eq_or_lt_of_le hi with h | h
    · rw [h]
    · exact (evenTerm_lt_evenTerm h).le
  have h58 : evenTerm 4 = 58 := by decide
  rcases lt_or_ge j 8 with h8 | h8
  · rcases closedForm_lt_eight_cases j h8 with h | h | h <;> omega
  · obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [closedForm_two_mul (by omega)]
      have hle : fib (t + 2) ≤ fib (i + 2) := fib_mono (by omega)
      have hpos : 0 < fib (i + 1) := fib_pos.mpr (by omega)
      unfold evenTerm
      nlinarith
    · rw [closedForm_two_mul_add_one (by omega)]
      exact evenTerm_lt_evenTerm (by omega)

/-- Greedy step at 0-indexed position `2i` (`i ≥ 4`): `F(i+2)` is admissible and
no smaller value is. -/
theorem step_two_mul {i : ℕ} (hi : 4 ≤ i) :
    Admissible (closedPrefix (2 * i)) (closedForm (2 * i)) ∧
      ∀ y < closedForm (2 * i), ¬ Admissible (closedPrefix (2 * i)) y := by
  rw [closedForm_two_mul hi]
  have hS := closedPrefix_sum_two_mul hi
  have hlen := closedPrefix_length (2 * i)
  refine ⟨⟨fib_notMem_closedPrefix_two_mul hi, i + 2, by rw [hS, hlen]; ring⟩, ?_⟩
  rintro y hy ⟨-, k, hk⟩
  rw [hS, hlen] at hk
  have hmul : (2 * i + 1) * fib k < (2 * i + 1) * fib (i + 2) := by nlinarith
  have hlt : fib k < fib (i + 2) := Nat.lt_of_mul_lt_mul_left hmul
  have hk' : k ≤ i + 1 := by
    have := lt_of_fib_lt hlt
    omega
  have hfk : fib k ≤ fib (i + 1) := fib_mono hk'
  have h2 : fib (i + 2) = fib i + fib (i + 1) := fib_add_two
  have h3 := fib_succ_le_two_mul (i := i) (by omega)
  have hpos : 0 < fib i := fib_pos.mpr (by omega)
  have hmk : (2 * i + 1) * fib k ≤ (2 * i + 1) * fib (i + 1) := Nat.mul_le_mul_left _ hfk
  have hi4 : 4 * fib i ≤ i * fib i := Nat.mul_le_mul_right _ hi
  nlinarith

/-- Greedy step at 0-indexed position `2i+1` (`i ≥ 4`): `evenTerm i` is admissible
and no smaller value is. -/
theorem step_two_mul_add_one {i : ℕ} (hi : 4 ≤ i) :
    Admissible (closedPrefix (2 * i + 1)) (closedForm (2 * i + 1)) ∧
      ∀ y < closedForm (2 * i + 1), ¬ Admissible (closedPrefix (2 * i + 1)) y := by
  rw [closedForm_two_mul_add_one (by omega)]
  have hS := closedPrefix_sum_two_mul_add_one hi
  have hlen := closedPrefix_length (2 * i + 1)
  have h3 : fib (i + 3) = fib (i + 1) + fib (i + 2) := fib_add_two
  refine ⟨⟨fun h => (lt_evenTerm_of_mem hi h).false, i + 3, ?_⟩, ?_⟩
  · rw [hS, hlen, evenTerm, h3]; ring
  rintro y hy ⟨hyL, k, hk⟩
  rw [hS, hlen] at hk
  have hmul : (2 * i + 1 + 1) * fib k < (2 * i + 1 + 1) * fib (i + 3) := by
    unfold evenTerm at hy
    rw [h3]
    nlinarith
  have hlt : fib k < fib (i + 3) := Nat.lt_of_mul_lt_mul_left hmul
  have hk' : k ≤ i + 2 := by
    have := lt_of_fib_lt hlt
    omega
  rcases (show k = i + 2 ∨ k ≤ i + 1 by omega) with rfl | hk1
  · apply hyL
    rw [mem_closedPrefix]
    refine ⟨2 * i, by omega, ?_⟩
    rw [closedForm_two_mul hi]
    nlinarith
  · have hfk : fib k ≤ fib (i + 1) := fib_mono hk1
    have h2 : fib (i + 2) = fib i + fib (i + 1) := fib_add_two
    have h3' := fib_succ_le_two_mul (i := i) (by omega)
    have hpos : 0 < fib i := fib_pos.mpr (by omega)
    have hmk : (2 * i + 1 + 1) * fib k ≤ (2 * i + 1 + 1) * fib (i + 1) :=
      Nat.mul_le_mul_left _ hfk
    have hi4 : 4 * fib i ≤ i * fib i := Nat.mul_le_mul_right _ hi
    nlinarith

/-- Finite check of the first eight greedy steps, with the Fibonacci index bounded
by `12` (justified in `step_lt_eight` since `F(12) = 144 > 100`). -/
theorem base_check : ∀ n < 8,
    ((closedPrefix n).sum + closedForm n ≤ 100 ∧ closedForm n ∉ closedPrefix n ∧
      ∃ k < 12, (closedPrefix n).sum + closedForm n = (n + 1) * fib k) ∧
    ∀ y < closedForm n, ¬ (y ∉ closedPrefix n ∧ ∃ k < 12, (closedPrefix n).sum + y = (n + 1) * fib k) := by
  decide

/-- Greedy steps at 0-indexed positions `n < 8`. -/
theorem step_lt_eight {n : ℕ} (hn : n < 8) :
    Admissible (closedPrefix n) (closedForm n) ∧ ∀ y < closedForm n, ¬ Admissible (closedPrefix n) y := by
  obtain ⟨⟨hbd, hnot, k, -, hk⟩, hmin⟩ := base_check n hn
  refine ⟨⟨hnot, k, by rw [closedPrefix_length]; exact hk⟩, ?_⟩
  rintro y hy ⟨hyL, k', hk'⟩
  rw [closedPrefix_length] at hk'
  refine hmin y hy ⟨hyL, k', ?_, hk'⟩
  by_contra hge
  have hf : fib 12 ≤ fib k' := fib_mono (not_lt.mp hge)
  have hf12 : fib 12 = 144 := by decide
  have hle : fib k' ≤ (n + 1) * fib k' := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- At every position `n`, `closedForm n` is the least value admissible after the
closed-form prefix of length `n`. -/
theorem closedForm_isLeast (n : ℕ) :
    Admissible (closedPrefix n) (closedForm n) ∧ ∀ y < closedForm n, ¬ Admissible (closedPrefix n) y := by
  rcases lt_or_ge n 8 with h | h
  · exact step_lt_eight h
  · obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact step_two_mul (by omega)
    · exact step_two_mul_add_one (by omega)

open Classical in
/-- The greedy sequence equals the closed form: `term n = closedForm n` for all `n`. -/
theorem term_eq_closedForm (n : ℕ) : term n = closedForm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hpre : prefixTerms n = closedPrefix n := by
      rw [prefixTerms_eq, closedPrefix]
      exact List.map_congr_left (fun j hj => ih j (List.mem_range.mp hj))
    unfold term
    rw [Nat.find_eq_iff, hpre]
    exact closedForm_isLeast n

/-- `a (n+1) = closedForm n`. -/
theorem a_succ (n : ℕ) : a (n + 1) = closedForm n := by
  rw [a, Nat.add_sub_cancel, term_eq_closedForm]

/-- Ground truth: `a(1), ..., a(49)` are exactly the 49 terms listed in the OEIS
entry A249265. -/
theorem a_first_terms : (List.range 49).map (fun n => a (n + 1)) =
    [0, 2, 1, 5, 7, 3, 17, 29, 8, 58, 13, 109, 21, 203, 34, 370, 55, 667, 89, 1189, 144, 2102,
      233, 3689, 377, 6435, 610, 11166, 987, 19287, 1597, 33181, 2584, 56882, 4181, 97205, 6765,
      165643, 10946, 281546, 17711, 477443, 28657, 807941, 46368, 1364590, 75025, 2300689,
      121393] := by
  simp only [a_succ]
  decide

/-- The entry's unproved formula line "For n > 5, a(2*n-3) = A000045(n)":
`a(2n-3) = F(n)` for `5 < n`. -/
theorem a_two_mul_sub_three (n : ℕ) (hn : 5 < n) : a (2 * n - 3) = fib n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show 2 * (m + 6) - 3 = 2 * (m + 4) + 1 by omega, a_succ, closedForm_two_mul (by omega)]

/-- Even positions: `a(2j) = F(j+1) + 2j F(j)` for `4 ≤ j`. -/
theorem a_two_mul (j : ℕ) (hj : 4 ≤ j) : a (2 * j) = fib (j + 1) + 2 * j * fib j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 4 := ⟨j - 4, by omega⟩
  rw [show 2 * (m + 4) = 2 * (m + 3) + 1 + 1 by omega, a_succ,
    closedForm_two_mul_add_one (by omega), evenTerm]
  ring

/-- **Barker's conjecture (A249265, Colin Barker, Oct 24 2014).** Verbatim:
"Conjecture: a(n) = 2*a(n-2) + a(n-4) - 2*a(n-6) - a(n-8) for n > 15."
Stated over `ℤ` (cast before subtracting); the guard `15 < n` keeps every index
`n - 8 ≥ 8` off the junk value `a 0`. -/
theorem barker (n : ℕ) (hn : 15 < n) :
    (a n : ℤ) = 2 * a (n - 2) + a (n - 4) - 2 * a (n - 6) - a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 16 := ⟨n - 16, by omega⟩
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * t + 16 = 2 * (t + 7) + 1 + 1 by omega,
      show 2 * (t + 7) + 1 + 1 - 2 = 2 * (t + 6) + 1 + 1 by omega,
      show 2 * (t + 7) + 1 + 1 - 4 = 2 * (t + 5) + 1 + 1 by omega,
      show 2 * (t + 7) + 1 + 1 - 6 = 2 * (t + 4) + 1 + 1 by omega,
      show 2 * (t + 7) + 1 + 1 - 8 = 2 * (t + 3) + 1 + 1 by omega]
    simp only [a_succ]
    rw [closedForm_two_mul_add_one (by omega), closedForm_two_mul_add_one (by omega),
      closedForm_two_mul_add_one (by omega), closedForm_two_mul_add_one (by omega),
      closedForm_two_mul_add_one (by omega)]
    simp only [evenTerm, Nat.fib_add_two]
    push_cast
    ring
  · rw [show 2 * t + 1 + 16 = 2 * (t + 8) + 1 by omega,
      show 2 * (t + 8) + 1 - 2 = 2 * (t + 7) + 1 by omega,
      show 2 * (t + 8) + 1 - 4 = 2 * (t + 6) + 1 by omega,
      show 2 * (t + 8) + 1 - 6 = 2 * (t + 5) + 1 by omega,
      show 2 * (t + 8) + 1 - 8 = 2 * (t + 4) + 1 by omega]
    simp only [a_succ]
    rw [closedForm_two_mul (by omega), closedForm_two_mul (by omega),
      closedForm_two_mul (by omega), closedForm_two_mul (by omega),
      closedForm_two_mul (by omega)]
    simp only [Nat.fib_add_two]
    push_cast
    ring

end Candidates.A249265GreedyDistinctNonnegative
