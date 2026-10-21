/-
# A195609 — Shevelev: gaps, runs and first terms for `Σ O(i) = O(n)O(n+1)/4`

## OEIS source (retrieved with `oeis show A195609` and the live entry, 2026-10-21)

```
NAME:     Numbers n such that Sum_{i=1..n} A(i) = A(n)*A(n+1)/4,
          where A(n) = A000069(n).
OFFSET:   1
AUTHOR:   Vladimir Shevelev, Sep 21 2011
TERMS:    3,4,5,9,15,16,17,23,27,28,29,33,39,43,44,45,51,52,53,57,63,64,65,
          71,75,76,77,83,84,85,89,95,99,100,101,105,111,112,113,119,123,124,
          125,129,135,139,140,141,147,148,149,153,159,163,164,165,169,175,176
COMMENT (the conjecture; no separate signature, so it is Shevelev's,
         Sep 21 2011):
  Conjectures: 1) there are only 3 different first differences 1,4,6; 2) the
  sequence contains either isolated series of terms, e.g., {9},{23},{33},
  {39},..., or series of 3 consecutive integers, e.g., {3,4,5}, {15,16,17},
  etc.; 3)the first terms m of every series satisfy the condition
  A(m+1)-A(m-1)=5, where A(n)=A000069(n).
A000069:  Odious numbers: numbers with an odd number of 1's in their binary
          expansion.  1,2,4,7,8,11,13,14,...  (offset 1)
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell.  Re-validated here (Python, exact integers, 2026-10-21): the
characterisation below, the gap set `{1, 4, 6}`, the run lengths `{1, 3}` and
claim 3 for every series start hold for `n ≤ 10^6`.

## Result of this module

All three conjectures are proved, with no remaining `sorry`.  The argument
mirrors `Candidates.A195608TakeSumEvil`, with the Thue–Morse value replaced by
the evil indicator `e(k) = 1 - t(k)`.

* `odious_succ`: `O(k+1) = 2k + e(k)` (exactly one of `2k`, `2k+1` is odious).
* `isTerm_succ_iff`: `n = k + 1` is a term iff `k` is even with `e(k) = 0`, or
  `k` is odd with `e(k) = 1` and `e(k+1) = 0`.
* Reading this modulo `4` (`e(2j) = e(j)`, `e(2j+1) = 1 - e(j)`): `4j+1` is a
  term iff `e(j) = 0`; `4j+2` never is; `4j+3` iff `e(j) = 1`; `4j+4` iff
  `e(j) = 1` and `e(j+1) = 0`.  The three claims follow by case analysis.

Claim 3 needs no extra guard: `1` is not a term (`e(0) = 1`), so every term
`m` satisfies `3 ≤ m` and `m - 1` is a genuine index of A000069.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A195609SameThreeStructural

/-! ## Definition layer -/

/-- A natural number is *odious* (A000069) if its binary expansion has an odd
number of `1`s. -/
def IsOdious (k : ℕ) : Prop := Odd ((Nat.digits 2 k).count 1)

/-- Odiousness is decidable (parity of a digit count). -/
instance : DecidablePred IsOdious := fun k =>
  inferInstanceAs (Decidable (Odd ((Nat.digits 2 k).count 1)))

/-- `odious n = A000069(n)`, the `n`-th odious number with OEIS offset `1`
(`odious 1 = 1`).  `Nat.nth` is `0`-indexed, hence `n - 1`; the value at `n = 0`
is junk and is never used by the statements below. -/
noncomputable def odious (n : ℕ) : ℕ := Nat.nth IsOdious (n - 1)

/-- `IsTerm n` says `n` belongs to A195609: `n ≥ 1` and
`Σ_{i=1..n} A(i) = A(n) A(n+1) / 4`, stated without division as
`4 · Σ_{i=1..n} A(i) = A(n) A(n+1)` (equivalent over `ℚ`). -/
def IsTerm (n : ℕ) : Prop :=
  1 ≤ n ∧ 4 * ∑ i ∈ Finset.Icc 1 n, odious i = odious n * odious (n + 1)

/-- The evil indicator `e(k) = 1 - t(k)`: `1` if the binary expansion of `k`
has an even number of `1`s, else `0` (one minus the Thue–Morse sequence
A010060). -/
def ev (k : ℕ) : ℕ := ((Nat.digits 2 k).count 1 + 1) % 2

/-! ## Recurrences for the evil indicator -/

/-- `e(k) ∈ {0, 1}`, as a bound. -/
theorem ev_le_one (k : ℕ) : ev k ≤ 1 := by
  unfold ev; omega

/-- `e(k) ∈ {0, 1}`. -/
theorem ev_eq_zero_or_one (k : ℕ) : ev k = 0 ∨ ev k = 1 :=
  Nat.le_one_iff_eq_zero_or_eq_one.mp (ev_le_one k)

/-- A number is odious iff its evil indicator is `0`. -/
theorem isOdious_iff_ev_eq_zero (k : ℕ) : IsOdious k ↔ ev k = 0 := by
  unfold IsOdious ev; rw [Nat.odd_iff]; omega

/-- `e(2k) = e(k)`. -/
theorem ev_two_mul (k : ℕ) : ev (2 * k) = ev k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold ev
    rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, h2, List.count_cons]
    simp

/-- `e(2k+1) = 1 - e(k)`, stated without subtraction. -/
theorem ev_two_mul_add_one (k : ℕ) : ev (2 * k + 1) + ev k = 1 := by
  unfold ev
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.count_cons]
  simp only [beq_self_eq_true, if_true]
  omega

/-- `e(4j) = e(j)`. -/
theorem ev_four_mul (j : ℕ) : ev (4 * j) = ev j := by
  rw [show 4 * j = 2 * (2 * j) by ring, ev_two_mul, ev_two_mul]

/-- `e(4j+1) = 1 - e(j)`. -/
theorem ev_four_mul_add_one (j : ℕ) : ev (4 * j + 1) + ev j = 1 := by
  rw [show 4 * j + 1 = 2 * (2 * j) + 1 by ring, ← ev_two_mul j]
  exact ev_two_mul_add_one (2 * j)

/-- `e(4j+2) = 1 - e(j)`. -/
theorem ev_four_mul_add_two (j : ℕ) : ev (4 * j + 2) + ev j = 1 := by
  rw [show 4 * j + 2 = 2 * (2 * j + 1) by ring, ev_two_mul]
  exact ev_two_mul_add_one j

/-- `e(4j+3) = e(j)`. -/
theorem ev_four_mul_add_three (j : ℕ) : ev (4 * j + 3) = ev j := by
  have h1 := ev_two_mul_add_one (2 * j + 1)
  have h2 := ev_two_mul_add_one j
  rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring] at h1
  omega

/-! ## Odious numbers in closed form -/

/-- Exactly one of `2k`, `2k+1` is odious, so there are `k` odious numbers
below `2k`. -/
theorem count_isOdious_two_mul (k : ℕ) : Nat.count IsOdious (2 * k) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum := ev_two_mul_add_one k
    have hd := ev_two_mul k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, ih]
    simp only [isOdious_iff_ev_eq_zero]
    rcases ev_eq_zero_or_one k with h | h
    · rw [hd, h, if_pos rfl, if_neg (by omega)]
    · rw [hd, h, if_neg (by omega), if_pos (by omega)]

/-- The `k`-th odious number (`0`-indexed) is `2k + e(k)`. -/
theorem nth_isOdious (k : ℕ) : Nat.nth IsOdious k = 2 * k + ev k := by
  have hsum := ev_two_mul_add_one k
  have hd := ev_two_mul k
  rcases ev_eq_zero_or_one k with h | h
  · have hod : IsOdious (2 * k) := (isOdious_iff_ev_eq_zero _).mpr (by rw [hd, h])
    have hc := Nat.nth_count hod
    rw [count_isOdious_two_mul] at hc
    rw [hc, h]; rfl
  · have hod : IsOdious (2 * k + 1) := (isOdious_iff_ev_eq_zero _).mpr (by omega)
    have hc := Nat.nth_count hod
    rw [Nat.count_succ, count_isOdious_two_mul, if_neg (by
      rw [isOdious_iff_ev_eq_zero, hd, h]; omega)] at hc
    rw [Nat.add_zero] at hc
    rw [hc, h]

/-- `A000069(k+1) = 2k + e(k)`. -/
theorem odious_succ (k : ℕ) : odious (k + 1) = 2 * k + ev k := by
  unfold odious; rw [Nat.add_sub_cancel, nth_isOdious]

/-- `Σ_{i<2j} e(i) = j`. -/
theorem sum_ev_two_mul (j : ℕ) : ∑ i ∈ Finset.range (2 * j), ev i = j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have hsum := ev_two_mul_add_one j
    rw [ev_two_mul]; omega

/-- `Σ_{i=1..k+1} A(i) = k(k+1) + Σ_{i≤k} e(i)`. -/
theorem sum_odious (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 (k + 1), odious i = k * (k + 1) + ∑ i ∈ Finset.range (k + 1), ev i := by
  induction k with
  | zero => simp [odious_succ (0 : ℕ)]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (k + 1), odious_succ]
    ring

/-! ## Characterisation of the terms -/

/-- **Characterisation.** `k + 1` is a term of A195609 iff either `k` is even
and `e(k) = 0`, or `k` is odd, `e(k) = 1` and `e(k+1) = 0`. -/
theorem isTerm_succ_iff (k : ℕ) :
    IsTerm (k + 1) ↔ (Even k ∧ ev k = 0) ∨ (Odd k ∧ ev k = 1 ∧ ev (k + 1) = 0) := by
  unfold IsTerm
  rw [sum_odious, odious_succ k, odious_succ (k + 1)]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hT : ∑ i ∈ Finset.range (2 * j + 1), ev i = j + ev j := by
      rw [Finset.sum_range_succ, sum_ev_two_mul, ev_two_mul]
    have hodd := ev_two_mul_add_one j
    have hev : Even (2 * j) := even_two_mul j
    have hnodd : ¬ Odd (2 * j) := Nat.not_odd_iff_even.mpr hev
    rw [hT, ev_two_mul]
    rcases ev_eq_zero_or_one j with ha | ha
    · rw [ha] at hodd ⊢
      rw [show ev (2 * j + 1) = 1 by omega]
      simp only [hev, hnodd, true_and, false_and, or_false, iff_true]
      constructor
      · omega
      · ring
    · rw [ha] at hodd ⊢
      rw [show ev (2 * j + 1) = 0 by omega]
      simp only [hnodd, false_and, or_false, one_ne_zero, and_false, iff_false, not_and]
      intro _ h
      ring_nf at h
      omega
  · have hT : ∑ i ∈ Finset.range (2 * j + 1 + 1), ev i = j + 1 := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, sum_ev_two_mul]
    have hodd : Odd (2 * j + 1) := odd_two_mul_add_one j
    have hnev : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr hodd
    rw [hT, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, ev_two_mul]
    simp only [hodd, hnev, true_and, false_and, false_or]
    rcases ev_eq_zero_or_one (2 * j + 1) with hb | hb <;>
      rcases ev_eq_zero_or_one (j + 1) with hc | hc <;>
      · rw [hb, hc]
        constructor
        · rintro ⟨-, h⟩
          ring_nf at h
          omega
        · rintro ⟨h1, h2⟩
          refine ⟨by omega, ?_⟩
          first
          | omega
          | ring

/-- `4j + 1` is a term iff `e(j) = 0`. -/
theorem isTerm_iff_of_eq_four_mul_add_one {n j : ℕ} (h : n = 4 * j + 1) :
    IsTerm n ↔ ev j = 0 := by
  subst h
  rw [isTerm_succ_iff, ev_four_mul]
  have hev : Even (4 * j) := ⟨2 * j, by ring⟩
  have hnodd : ¬ Odd (4 * j) := Nat.not_odd_iff_even.mpr hev
  simp only [hev, hnodd, true_and, false_and, or_false]

/-- `4j + 2` is never a term. -/
theorem not_isTerm_of_eq_four_mul_add_two {n j : ℕ} (h : n = 4 * j + 2) : ¬ IsTerm n := by
  subst h
  rw [show 4 * j + 2 = (4 * j + 1) + 1 by ring, isTerm_succ_iff,
    show 4 * j + 1 + 1 = 4 * j + 2 by ring]
  have h1 := ev_four_mul_add_one j
  have h2 := ev_four_mul_add_two j
  have hodd : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
  have hnev : ¬ Even (4 * j + 1) := Nat.not_even_iff_odd.mpr hodd
  simp only [hnev, false_and, false_or, not_and]
  omega

/-- `4j + 3` is a term iff `e(j) = 1`. -/
theorem isTerm_iff_of_eq_four_mul_add_three {n j : ℕ} (h : n = 4 * j + 3) :
    IsTerm n ↔ ev j = 1 := by
  subst h
  rw [show 4 * j + 3 = (4 * j + 2) + 1 by ring, isTerm_succ_iff]
  have h2 := ev_four_mul_add_two j
  have hev : Even (4 * j + 2) := ⟨2 * j + 1, by ring⟩
  have hnodd : ¬ Odd (4 * j + 2) := Nat.not_odd_iff_even.mpr hev
  simp only [hev, hnodd, true_and, false_and, or_false]
  omega

/-- `4j + 4` is a term iff `e(j) = 1` and `e(j+1) = 0`. -/
theorem isTerm_iff_of_eq_four_mul_add_four {n j : ℕ} (h : n = 4 * j + 4) :
    IsTerm n ↔ ev j = 1 ∧ ev (j + 1) = 0 := by
  subst h
  rw [show 4 * j + 4 = (4 * j + 3) + 1 by ring, isTerm_succ_iff,
    show 4 * j + 3 + 1 = 4 * (j + 1) by ring, ev_four_mul, ev_four_mul_add_three]
  have hodd : Odd (4 * j + 3) := ⟨2 * j + 1, by ring⟩
  have hnev : ¬ Even (4 * j + 3) := Nat.not_even_iff_odd.mpr hodd
  simp only [hodd, hnev, true_and, false_and, false_or]

/-- Every term is `4j + r` with `r ∈ {1, 3, 4}`. -/
theorem exists_four_mul_add_of_isTerm {n : ℕ} (hn : IsTerm n) :
    ∃ j, n = 4 * j + 1 ∨ n = 4 * j + 3 ∨ n = 4 * j + 4 := by
  obtain ⟨j, hj⟩ : ∃ j, n = 4 * j + 1 ∨ n = 4 * j + 2 ∨ n = 4 * j + 3 ∨ n = 4 * j + 4 :=
    ⟨(n - 1) / 4, by have := hn.1; omega⟩
  rcases hj with hj | hj | hj | hj
  · exact ⟨j, Or.inl hj⟩
  · exact absurd hn (not_isTerm_of_eq_four_mul_add_two hj)
  · exact ⟨j, Or.inr (Or.inl hj)⟩
  · exact ⟨j, Or.inr (Or.inr hj)⟩

/-- If `0 < d`, `a + d` is a term, no `a + e` with `0 < e < d` is a term, and `b` is the
next term after `a`, then `b = a + d`. -/
theorem eq_add_of_next {a b d : ℕ} (hd0 : 0 < d) (hab : a < b) (hb : IsTerm b)
    (hgap : ∀ c, a < c → c < b → ¬ IsTerm c) (hd : IsTerm (a + d))
    (hlt : ∀ e, 0 < e → e < d → ¬ IsTerm (a + e)) : b = a + d := by
  rcases lt_trichotomy b (a + d) with h | h | h
  · exact absurd (show IsTerm (a + (b - a)) by rw [Nat.add_sub_cancel' hab.le]; exact hb)
      (hlt (b - a) (by omega) (by omega))
  · exact h
  · exact absurd hd (hgap (a + d) (by omega) h)

/-! ## The conjectures -/

/-- **Conjecture 1 (Shevelev, A195609, Sep 21 2011).** "there are only 3
different first differences 1,4,6": if `a < b` are consecutive terms of
A195609 (no term strictly between them), then `b - a ∈ {1, 4, 6}`. -/
theorem gap_mem (a b : ℕ) (ha : IsTerm a) (hb : IsTerm b) (hab : a < b)
    (hgap : ∀ c, a < c → c < b → ¬ IsTerm c) :
    b = a + 1 ∨ b = a + 4 ∨ b = a + 6 := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm ha
  · have hj0 : ev j = 0 := (isTerm_iff_of_eq_four_mul_add_one hj).mp ha
    rcases ev_eq_zero_or_one (j + 1) with hj1 | hj1
    · right; left
      refine eq_add_of_next (by norm_num) hab hb hgap
        ((isTerm_iff_of_eq_four_mul_add_one (j := j + 1) (by omega)).mpr hj1) ?_
      intro e he1 he2
      interval_cases e
      · exact not_isTerm_of_eq_four_mul_add_two (j := j) (by omega)
      · rw [isTerm_iff_of_eq_four_mul_add_three (j := j) (by omega)]; omega
      · rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
    · right; right
      refine eq_add_of_next (by norm_num) hab hb hgap
        ((isTerm_iff_of_eq_four_mul_add_three (j := j + 1) (by omega)).mpr hj1) ?_
      intro e he1 he2
      interval_cases e
      · exact not_isTerm_of_eq_four_mul_add_two (j := j) (by omega)
      · rw [isTerm_iff_of_eq_four_mul_add_three (j := j) (by omega)]; omega
      · rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
      · rw [isTerm_iff_of_eq_four_mul_add_one (j := j + 1) (by omega)]; omega
      · exact not_isTerm_of_eq_four_mul_add_two (j := j + 1) (by omega)
  · have hj1 : ev j = 1 := (isTerm_iff_of_eq_four_mul_add_three hj).mp ha
    rcases ev_eq_zero_or_one (j + 1) with hj2 | hj2
    · left
      exact eq_add_of_next (by norm_num) hab hb hgap
        ((isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)).mpr ⟨hj1, hj2⟩)
        (fun e he1 he2 => absurd he2 (by omega))
    · right; left
      refine eq_add_of_next (by norm_num) hab hb hgap
        ((isTerm_iff_of_eq_four_mul_add_three (j := j + 1) (by omega)).mpr hj2) ?_
      intro e he1 he2
      interval_cases e
      · rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
      · rw [isTerm_iff_of_eq_four_mul_add_one (j := j + 1) (by omega)]; omega
      · exact not_isTerm_of_eq_four_mul_add_two (j := j + 1) (by omega)
  · have hj12 := (isTerm_iff_of_eq_four_mul_add_four hj).mp ha
    left
    exact eq_add_of_next (by norm_num) hab hb hgap
      ((isTerm_iff_of_eq_four_mul_add_one (j := j + 1) (by omega)).mpr hj12.2)
      (fun e he1 he2 => absurd he2 (by omega))

/-- **Conjecture 2 (Shevelev, A195609, Sep 21 2011).** "the sequence contains
either isolated series of terms ... or series of 3 consecutive integers": every
maximal block of consecutive terms has length `1` or `3`.  Stated for a block
starting at `m + 1` (so `m` is not a term; the case `m = 0` is harmless, as `1`
is not a term): either `m + 2` is not a term, or `m + 2`, `m + 3` are terms
and `m + 4` is not. -/
theorem run_length (m : ℕ) (hm : ¬ IsTerm m) (hm1 : IsTerm (m + 1)) :
    ¬ IsTerm (m + 2) ∨ (IsTerm (m + 2) ∧ IsTerm (m + 3) ∧ ¬ IsTerm (m + 4)) := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm hm1
  · left
    exact not_isTerm_of_eq_four_mul_add_two (j := j) (by omega)
  · have hj1 : ev j = 1 := (isTerm_iff_of_eq_four_mul_add_three hj).mp hm1
    rcases ev_eq_zero_or_one (j + 1) with hj2 | hj2
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
      · rw [isTerm_iff_of_eq_four_mul_add_one (j := j + 1) (by omega)]; omega
      · exact not_isTerm_of_eq_four_mul_add_two (j := j + 1) (by omega)
    · left
      rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
  · have hj12 := (isTerm_iff_of_eq_four_mul_add_four hj).mp hm1
    exact absurd ((isTerm_iff_of_eq_four_mul_add_three (j := j) (by omega)).mpr hj12.1) hm

/-- `e(0) = 1`: `0` is evil. -/
theorem ev_zero : ev 0 = 1 := rfl

/-- Every term of A195609 is at least `3` (`1` and `2` are not terms). -/
theorem three_le_of_isTerm {m : ℕ} (hm : IsTerm m) : 3 ≤ m := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm hm
  · have hj0 : ev j = 0 := (isTerm_iff_of_eq_four_mul_add_one hj).mp hm
    have hj : j ≠ 0 := by rintro rfl; rw [ev_zero] at hj0; omega
    omega
  · omega
  · omega

/-- **Conjecture 3 (Shevelev, A195609, Sep 21 2011).** "the first terms m of
every series satisfy the condition A(m+1)-A(m-1)=5, where A(n)=A000069(n)":
if `m` is a term and `m - 1` is not, then `A(m+1) - A(m-1) = 5`.
No guard is needed: every term satisfies `3 ≤ m` (`three_le_of_isTerm`), so
`m - 1` is a genuine index of A000069. -/
theorem first_term_odious_sub (m : ℕ) (hm : IsTerm m) (hprev : ¬ IsTerm (m - 1)) :
    (odious (m + 1) : ℤ) - odious (m - 1) = 5 := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm hm
  · have hj0 : ev j = 0 := (isTerm_iff_of_eq_four_mul_add_one hj).mp hm
    have hj_ne : j ≠ 0 := by rintro rfl; rw [ev_zero] at hj0; omega
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : ev i = 0 := by
      have hn := hprev
      rw [isTerm_iff_of_eq_four_mul_add_four (j := i) (by omega)] at hn
      have hle := ev_le_one i
      omega
    rw [hj, show 4 * (i + 1) + 1 - 1 = (4 * i + 3) + 1 by omega, odious_succ, odious_succ,
      ev_four_mul_add_three]
    have h1 := ev_four_mul_add_one (i + 1)
    push_cast
    omega
  · have hj1 : ev j = 1 := (isTerm_iff_of_eq_four_mul_add_three hj).mp hm
    rw [hj, show 4 * j + 3 - 1 = (4 * j + 1) + 1 by omega, odious_succ, odious_succ]
    have h1 := ev_four_mul_add_one j
    have h3 := ev_four_mul_add_three j
    push_cast
    omega
  · have hj12 := (isTerm_iff_of_eq_four_mul_add_four hj).mp hm
    exact absurd
      ((isTerm_iff_of_eq_four_mul_add_three (n := m - 1) (j := j) (by omega)).mpr hj12.1) hprev

/-! ## Sanity layer -/

-- Ground truth for `odious` against the A000069 data `1, 2, 4, 7, 8, 11, 13, 14`.
example : odious 1 = 1 ∧ odious 2 = 2 ∧ odious 3 = 4 ∧ odious 4 = 7 ∧ odious 5 = 8 ∧
    odious 6 = 11 ∧ odious 7 = 13 ∧ odious 8 = 14 := by
  simp only [odious_succ (0 : ℕ), show (2 : ℕ) = 1 + 1 from rfl, odious_succ]
  decide

-- Ground truth for `IsTerm` against the A195609 data: the terms `≤ 49` are
-- exactly `3, 4, 5, 9, 15, 16, 17, 23, 27, 28, 29, 33, 39, 43, 44, 45`.
example : ∀ k < 49, (IsTerm (k + 1) ↔
    k + 1 ∈ ({3, 4, 5, 9, 15, 16, 17, 23, 27, 28, 29, 33, 39, 43, 44, 45} :
      Finset ℕ)) := by
  intro k hk
  rw [isTerm_succ_iff]
  revert k
  decide

-- Non-vacuity: each gap `4`, `6`, `1` of conjecture 1 occurs (`5 → 9`,
-- `9 → 15`, `3 → 4`), the hypotheses of conjecture 2 hold at `m = 2` (block
-- `{3, 4, 5}`) and `m = 8` (block `{9}`), and conjecture 3 applies at `m = 3`
-- and `m = 9`.
example : IsTerm 3 ∧ IsTerm 4 ∧ IsTerm 5 ∧ IsTerm 9 ∧ IsTerm 15 ∧ ¬ IsTerm 2 ∧
    ¬ IsTerm 8 := by
  refine ⟨(isTerm_succ_iff 2).mpr (by decide), (isTerm_succ_iff 3).mpr (by decide),
    (isTerm_succ_iff 4).mpr (by decide), (isTerm_succ_iff 8).mpr (by decide),
    (isTerm_succ_iff 14).mpr (by decide), (isTerm_succ_iff 1).not.mpr (by decide),
    (isTerm_succ_iff 7).not.mpr (by decide)⟩

end Candidates.A195609SameThreeStructural
