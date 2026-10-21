/-
# A195608 — Shevelev: gaps, runs and first terms for `Σ E(i) = E(n)E(n+1)/4`

## OEIS source (retrieved with `oeis show A195608` and the live entry, 2026-10-21)

```
NAME:     Numbers n such that Sum_{i=1..n} A(i) = A(n)*A(n+1)/4,
          where A(n) = A001969(n).
OFFSET:   1
AUTHOR:   Vladimir Shevelev, Sep 21 2011
TERMS:    1,7,11,12,13,19,20,21,25,31,35,36,37,41,47,48,49,55,59,60,61,67,68,
          69,73,79,80,81,87,91,92,93,97,103,107,108,109,115,116,117,121,127,
          131,132,133,137,143,144,145,151,155,156,157,161,167,171,172,173,179
COMMENT (the conjecture; no separate signature, so it is Shevelev's,
         Sep 21 2011):
  Conjectures: 1) there are only 3 different first differences 1,4,6; 2) the
  sequence contains either isolated series of terms, e.g., {1},{7},{25},
  {31},..., or series of 3 consecutive integers, e.g., {11,12,13},
  {19,20,21}, etc.; 3)the first terms m of every series satisfy the condition
  A(m+1)-A(m-1)=5, where A(n)=A001969(n).
A001969:  Evil numbers: nonnegative integers with an even number of 1's in
          their binary expansion.  0,3,5,6,9,10,12,15,...  (offset 1)
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell.  Re-validated here (Python, exact integers, 2026-10-21): the
characterisation below, the gap set `{1, 4, 6}`, the run lengths `{1, 3}` and
claim 3 for every series start `m > 1` all hold for `n ≤ 400000`.

## Result of this module

All three conjectures are proved, with no remaining `sorry`.

* `evil_succ`: `E(k+1) = 2k + t(k)`, with `t` the Thue–Morse sequence
  (exactly one of `2k`, `2k+1` is evil).
* `isTerm_succ_iff`: `n = k + 1` is a term iff `k` is even with `t(k) = 0`, or
  `k` is odd with `t(k) = 1` and `t(k+1) = 0`.
* Reading this modulo `4` (`t(2j) = t(j)`, `t(2j+1) = 1 - t(j)`): `4j+1` is a
  term iff `t(j) = 0`; `4j+2` never is; `4j+3` iff `t(j) = 1`; `4j+4` iff
  `t(j) = 1` and `t(j+1) = 0`.  The three claims follow by case analysis.

Claim 3 is stated for every series start `m` with `1 < m` (isolated terms and
runs of three alike).  The guard is necessary: `m = 1` starts the series `{1}`
and `A(0)` is outside the offset of A001969.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A195608TakeSumEvil

/-! ## Definition layer -/

/-- A natural number is *evil* (A001969) if its binary expansion has an even
number of `1`s. -/
def IsEvil (k : ℕ) : Prop := Even ((Nat.digits 2 k).count 1)

/-- Evilness is decidable (parity of a digit count). -/
instance : DecidablePred IsEvil := fun k =>
  inferInstanceAs (Decidable (Even ((Nat.digits 2 k).count 1)))

/-- `evil n = A001969(n)`, the `n`-th evil number with OEIS offset `1`
(`evil 1 = 0`).  `Nat.nth` is `0`-indexed, hence `n - 1`; the value at `n = 0`
is junk and is never used by the statements below. -/
noncomputable def evil (n : ℕ) : ℕ := Nat.nth IsEvil (n - 1)

/-- `IsTerm n` says `n` belongs to A195608: `n ≥ 1` and
`Σ_{i=1..n} A(i) = A(n) A(n+1) / 4`, stated without division as
`4 · Σ_{i=1..n} A(i) = A(n) A(n+1)` (equivalent over `ℚ`). -/
def IsTerm (n : ℕ) : Prop :=
  1 ≤ n ∧ 4 * ∑ i ∈ Finset.Icc 1 n, evil i = evil n * evil (n + 1)

/-- The Thue–Morse sequence `t(k)`: parity of the number of `1`s in the binary
expansion of `k` (A010060). -/
def tm (k : ℕ) : ℕ := (Nat.digits 2 k).count 1 % 2

/-! ## Thue–Morse recurrences -/

/-- `t(k) ∈ {0, 1}`, as a bound. -/
theorem tm_le_one (k : ℕ) : tm k ≤ 1 := by
  unfold tm; omega

/-- `t(k) ∈ {0, 1}`. -/
theorem tm_eq_zero_or_one (k : ℕ) : tm k = 0 ∨ tm k = 1 :=
  Nat.le_one_iff_eq_zero_or_eq_one.mp (tm_le_one k)

/-- A number is evil iff its Thue–Morse value is `0`. -/
theorem isEvil_iff_tm_eq_zero (k : ℕ) : IsEvil k ↔ tm k = 0 := by
  unfold IsEvil tm; exact Nat.even_iff

/-- `t(2k) = t(k)`. -/
theorem tm_two_mul (k : ℕ) : tm (2 * k) = tm k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold tm
    rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, h2, List.count_cons]
    simp

/-- `t(2k+1) = 1 - t(k)`, stated without subtraction. -/
theorem tm_two_mul_add_one (k : ℕ) : tm (2 * k + 1) + tm k = 1 := by
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.count_cons]
  simp only [beq_self_eq_true, if_true]
  omega

/-- `t(4j) = t(j)`. -/
theorem tm_four_mul (j : ℕ) : tm (4 * j) = tm j := by
  rw [show 4 * j = 2 * (2 * j) by ring, tm_two_mul, tm_two_mul]

/-- `t(4j+1) = 1 - t(j)`. -/
theorem tm_four_mul_add_one (j : ℕ) : tm (4 * j + 1) + tm j = 1 := by
  rw [show 4 * j + 1 = 2 * (2 * j) + 1 by ring, ← tm_two_mul j]
  exact tm_two_mul_add_one (2 * j)

/-- `t(4j+2) = 1 - t(j)`. -/
theorem tm_four_mul_add_two (j : ℕ) : tm (4 * j + 2) + tm j = 1 := by
  rw [show 4 * j + 2 = 2 * (2 * j + 1) by ring, tm_two_mul]
  exact tm_two_mul_add_one j

/-- `t(4j+3) = t(j)`. -/
theorem tm_four_mul_add_three (j : ℕ) : tm (4 * j + 3) = tm j := by
  have h1 := tm_two_mul_add_one (2 * j + 1)
  have h2 := tm_two_mul_add_one j
  rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring] at h1
  omega

/-! ## Evil numbers in closed form -/

/-- Exactly one of `2k`, `2k+1` is evil, so there are `k` evil numbers below
`2k`. -/
theorem count_isEvil_two_mul (k : ℕ) : Nat.count IsEvil (2 * k) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum := tm_two_mul_add_one k
    have hd := tm_two_mul k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, ih]
    simp only [isEvil_iff_tm_eq_zero]
    rcases tm_eq_zero_or_one k with h | h
    · rw [hd, h, if_pos rfl, if_neg (by omega)]
    · rw [hd, h, if_neg (by omega), if_pos (by omega)]

/-- The `k`-th evil number (`0`-indexed) is `2k + t(k)`. -/
theorem nth_isEvil (k : ℕ) : Nat.nth IsEvil k = 2 * k + tm k := by
  have hsum := tm_two_mul_add_one k
  have hd := tm_two_mul k
  rcases tm_eq_zero_or_one k with h | h
  · have hev : IsEvil (2 * k) := (isEvil_iff_tm_eq_zero _).mpr (by rw [hd, h])
    have hc := Nat.nth_count hev
    rw [count_isEvil_two_mul] at hc
    rw [hc, h]; rfl
  · have hev : IsEvil (2 * k + 1) := (isEvil_iff_tm_eq_zero _).mpr (by omega)
    have hc := Nat.nth_count hev
    rw [Nat.count_succ, count_isEvil_two_mul, if_neg (by
      rw [isEvil_iff_tm_eq_zero, hd, h]; omega)] at hc
    rw [Nat.add_zero] at hc
    rw [hc, h]

/-- `A001969(k+1) = 2k + t(k)`. -/
theorem evil_succ (k : ℕ) : evil (k + 1) = 2 * k + tm k := by
  unfold evil; rw [Nat.add_sub_cancel, nth_isEvil]

/-- `Σ_{i<2j} t(i) = j`. -/
theorem sum_tm_two_mul (j : ℕ) : ∑ i ∈ Finset.range (2 * j), tm i = j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have hsum := tm_two_mul_add_one j
    rw [tm_two_mul]; omega

/-- `Σ_{i=1..k+1} A(i) = k(k+1) + Σ_{i≤k} t(i)`. -/
theorem sum_evil (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 (k + 1), evil i = k * (k + 1) + ∑ i ∈ Finset.range (k + 1), tm i := by
  induction k with
  | zero => simp [evil_succ (0 : ℕ)]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (k + 1), evil_succ]
    ring

/-! ## Characterisation of the terms -/

/-- **Characterisation.** `k + 1` is a term of A195608 iff either `k` is even
and `t(k) = 0`, or `k` is odd, `t(k) = 1` and `t(k+1) = 0`. -/
theorem isTerm_succ_iff (k : ℕ) :
    IsTerm (k + 1) ↔ (Even k ∧ tm k = 0) ∨ (Odd k ∧ tm k = 1 ∧ tm (k + 1) = 0) := by
  unfold IsTerm
  rw [sum_evil, evil_succ k, evil_succ (k + 1)]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hT : ∑ i ∈ Finset.range (2 * j + 1), tm i = j + tm j := by
      rw [Finset.sum_range_succ, sum_tm_two_mul, tm_two_mul]
    have hodd := tm_two_mul_add_one j
    have hev : Even (2 * j) := even_two_mul j
    have hnodd : ¬ Odd (2 * j) := Nat.not_odd_iff_even.mpr hev
    rw [hT, tm_two_mul]
    rcases tm_eq_zero_or_one j with ha | ha
    · rw [ha] at hodd ⊢
      rw [show tm (2 * j + 1) = 1 by omega]
      simp only [hev, hnodd, true_and, false_and, or_false, iff_true]
      constructor
      · omega
      · ring
    · rw [ha] at hodd ⊢
      rw [show tm (2 * j + 1) = 0 by omega]
      simp only [hnodd, false_and, or_false, one_ne_zero, and_false, iff_false, not_and]
      intro _ h
      ring_nf at h
      omega
  · have hT : ∑ i ∈ Finset.range (2 * j + 1 + 1), tm i = j + 1 := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, sum_tm_two_mul]
    have hodd : Odd (2 * j + 1) := odd_two_mul_add_one j
    have hnev : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr hodd
    rw [hT, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, tm_two_mul]
    simp only [hodd, hnev, true_and, false_and, false_or]
    rcases tm_eq_zero_or_one (2 * j + 1) with hb | hb <;>
      rcases tm_eq_zero_or_one (j + 1) with hc | hc <;>
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

/-- `4j + 1` is a term iff `t(j) = 0`. -/
theorem isTerm_iff_of_eq_four_mul_add_one {n j : ℕ} (h : n = 4 * j + 1) :
    IsTerm n ↔ tm j = 0 := by
  subst h
  rw [isTerm_succ_iff, tm_four_mul]
  have hev : Even (4 * j) := ⟨2 * j, by ring⟩
  have hnodd : ¬ Odd (4 * j) := Nat.not_odd_iff_even.mpr hev
  simp only [hev, hnodd, true_and, false_and, or_false]

/-- `4j + 2` is never a term. -/
theorem not_isTerm_of_eq_four_mul_add_two {n j : ℕ} (h : n = 4 * j + 2) : ¬ IsTerm n := by
  subst h
  rw [show 4 * j + 2 = (4 * j + 1) + 1 by ring, isTerm_succ_iff,
    show 4 * j + 1 + 1 = 4 * j + 2 by ring]
  have h1 := tm_four_mul_add_one j
  have h2 := tm_four_mul_add_two j
  have hodd : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
  have hnev : ¬ Even (4 * j + 1) := Nat.not_even_iff_odd.mpr hodd
  simp only [hnev, false_and, false_or, not_and]
  omega

/-- `4j + 3` is a term iff `t(j) = 1`. -/
theorem isTerm_iff_of_eq_four_mul_add_three {n j : ℕ} (h : n = 4 * j + 3) :
    IsTerm n ↔ tm j = 1 := by
  subst h
  rw [show 4 * j + 3 = (4 * j + 2) + 1 by ring, isTerm_succ_iff]
  have h2 := tm_four_mul_add_two j
  have hev : Even (4 * j + 2) := ⟨2 * j + 1, by ring⟩
  have hnodd : ¬ Odd (4 * j + 2) := Nat.not_odd_iff_even.mpr hev
  simp only [hev, hnodd, true_and, false_and, or_false]
  omega

/-- `4j + 4` is a term iff `t(j) = 1` and `t(j+1) = 0`. -/
theorem isTerm_iff_of_eq_four_mul_add_four {n j : ℕ} (h : n = 4 * j + 4) :
    IsTerm n ↔ tm j = 1 ∧ tm (j + 1) = 0 := by
  subst h
  rw [show 4 * j + 4 = (4 * j + 3) + 1 by ring, isTerm_succ_iff,
    show 4 * j + 3 + 1 = 4 * (j + 1) by ring, tm_four_mul, tm_four_mul_add_three]
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

/-- **Conjecture 1 (Shevelev, A195608, Sep 21 2011).** "there are only 3
different first differences 1,4,6": if `a < b` are consecutive terms of
A195608 (no term strictly between them), then `b - a ∈ {1, 4, 6}`. -/
theorem gap_mem (a b : ℕ) (ha : IsTerm a) (hb : IsTerm b) (hab : a < b)
    (hgap : ∀ c, a < c → c < b → ¬ IsTerm c) :
    b = a + 1 ∨ b = a + 4 ∨ b = a + 6 := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm ha
  · have hj0 : tm j = 0 := (isTerm_iff_of_eq_four_mul_add_one hj).mp ha
    rcases tm_eq_zero_or_one (j + 1) with hj1 | hj1
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
  · have hj1 : tm j = 1 := (isTerm_iff_of_eq_four_mul_add_three hj).mp ha
    rcases tm_eq_zero_or_one (j + 1) with hj2 | hj2
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

/-- **Conjecture 2 (Shevelev, A195608, Sep 21 2011).** "the sequence contains
either isolated series of terms ... or series of 3 consecutive integers": every
maximal block of consecutive terms has length `1` or `3`.  Stated for a block
starting at `m + 1` (so `m` is not a term; `m = 0` covers the block `{1}`):
either `m + 2` is not a term, or `m + 2`, `m + 3` are terms and `m + 4` is
not. -/
theorem run_length (m : ℕ) (hm : ¬ IsTerm m) (hm1 : IsTerm (m + 1)) :
    ¬ IsTerm (m + 2) ∨ (IsTerm (m + 2) ∧ IsTerm (m + 3) ∧ ¬ IsTerm (m + 4)) := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm hm1
  · left
    exact not_isTerm_of_eq_four_mul_add_two (j := j) (by omega)
  · have hj1 : tm j = 1 := (isTerm_iff_of_eq_four_mul_add_three hj).mp hm1
    rcases tm_eq_zero_or_one (j + 1) with hj2 | hj2
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
      · rw [isTerm_iff_of_eq_four_mul_add_one (j := j + 1) (by omega)]; omega
      · exact not_isTerm_of_eq_four_mul_add_two (j := j + 1) (by omega)
    · left
      rw [isTerm_iff_of_eq_four_mul_add_four (j := j) (by omega)]; omega
  · have hj12 := (isTerm_iff_of_eq_four_mul_add_four hj).mp hm1
    exact absurd ((isTerm_iff_of_eq_four_mul_add_three (j := j) (by omega)).mpr hj12.1) hm

/-- **Conjecture 3 (Shevelev, A195608, Sep 21 2011).** "the first terms m of
every series satisfy the condition A(m+1)-A(m-1)=5, where A(n)=A001969(n)":
if `m` is a term, `m - 1` is not, and `1 < m`, then `A(m+1) - A(m-1) = 5`.
The guard `1 < m` excludes the series `{1}`, for which `A(0)` is undefined;
`m - 1` is a genuine predecessor under it. -/
theorem first_term_evil_sub (m : ℕ) (hm1 : 1 < m) (hm : IsTerm m) (hprev : ¬ IsTerm (m - 1)) :
    (evil (m + 1) : ℤ) - evil (m - 1) = 5 := by
  obtain ⟨j, hj | hj | hj⟩ := exists_four_mul_add_of_isTerm hm
  · have hj0 : tm j = 0 := (isTerm_iff_of_eq_four_mul_add_one hj).mp hm
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : tm i = 0 := by
      have hn := hprev
      rw [isTerm_iff_of_eq_four_mul_add_four (j := i) (by omega)] at hn
      have hle := tm_le_one i
      omega
    rw [hj, show 4 * (i + 1) + 1 - 1 = (4 * i + 3) + 1 by omega, evil_succ, evil_succ,
      tm_four_mul_add_three]
    have h1 := tm_four_mul_add_one (i + 1)
    push_cast
    omega
  · have hj1 : tm j = 1 := (isTerm_iff_of_eq_four_mul_add_three hj).mp hm
    rw [hj, show 4 * j + 3 - 1 = (4 * j + 1) + 1 by omega, evil_succ, evil_succ]
    have h1 := tm_four_mul_add_one j
    have h3 := tm_four_mul_add_three j
    push_cast
    omega
  · have hj12 := (isTerm_iff_of_eq_four_mul_add_four hj).mp hm
    exact absurd
      ((isTerm_iff_of_eq_four_mul_add_three (n := m - 1) (j := j) (by omega)).mpr hj12.1) hprev

/-! ## Sanity layer -/

-- Ground truth for `evil` against the A001969 data `0, 3, 5, 6, 9, 10, 12, 15`.
example : evil 1 = 0 ∧ evil 2 = 3 ∧ evil 3 = 5 ∧ evil 4 = 6 ∧ evil 5 = 9 ∧
    evil 6 = 10 ∧ evil 7 = 12 ∧ evil 8 = 15 := by
  simp only [evil_succ (0 : ℕ), show (2 : ℕ) = 1 + 1 from rfl, evil_succ]
  decide

-- Ground truth for `IsTerm` against the A195608 data: the terms `≤ 49` are
-- exactly `1, 7, 11, 12, 13, 19, 20, 21, 25, 31, 35, 36, 37, 41, 47, 48, 49`.
example : ∀ k < 49, (IsTerm (k + 1) ↔
    k + 1 ∈ ({1, 7, 11, 12, 13, 19, 20, 21, 25, 31, 35, 36, 37, 41, 47, 48, 49} :
      Finset ℕ)) := by
  intro k hk
  rw [isTerm_succ_iff]
  revert k
  decide

-- Non-vacuity: each gap `6`, `4`, `1` of conjecture 1 occurs (`1 → 7`,
-- `7 → 11`, `11 → 12`), the hypotheses of conjecture 2 hold at `m = 0` and
-- `m = 10`, and conjecture 3 applies at `m = 7` and `m = 11`.
example : IsTerm 1 ∧ IsTerm 7 ∧ IsTerm 11 ∧ IsTerm 12 ∧ ¬ IsTerm 0 ∧ ¬ IsTerm 10 ∧
    ¬ IsTerm 6 := by
  refine ⟨(isTerm_succ_iff 0).mpr (by decide), (isTerm_succ_iff 6).mpr (by decide),
    (isTerm_succ_iff 10).mpr (by decide), (isTerm_succ_iff 11).mpr (by decide),
    fun h => absurd h.1 (by norm_num), (isTerm_succ_iff 9).not.mpr (by decide),
    (isTerm_succ_iff 5).not.mpr (by decide)⟩

-- The guard `1 < m` of conjecture 3 is load-bearing in this encoding:
-- `{1}` is a series, and with the junk value `evil 0 = 0` the difference is `3`.
example : (evil 2 : ℤ) - evil 0 = 3 := by
  have h2 : evil 2 = 3 := by rw [show (2 : ℕ) = 1 + 1 from rfl, evil_succ]; decide
  have h0 : evil 0 = 0 := by unfold evil; rw [Nat.zero_sub, nth_isEvil]; decide
  rw [h2, h0]; norm_num

end Candidates.A195608TakeSumEvil
