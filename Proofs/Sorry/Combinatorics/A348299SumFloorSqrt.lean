/-
# A348299 — zeros of the partial sums of `(-1)^⌊k(√2-1)⌋`

## OEIS source (retrieved 2026-10-21 with `oeis show A348299`; author line from
the live entry https://oeis.org/A348299)

```
NAME:     Indices of 0 in A348295: numbers m such that
          Sum_{k=1..m} (-1)^(floor(k*(sqrt(2)-1))) = Sum_{k=1..m} (-1)^A097508(k) = 0.
TERMS:    0,4,24,28,140,144,164,168,816,820,840,844,956,960,980,984,4756,4760,
          4780,4784,4896,4900,4920,4924,5572,5576,5596,5600,5712,5716,5736,5740,...
COMMENT:  Conjecture: sequence is infinite.
COMMENT:  Conjecture: all terms are divisible by 4. There are no counterexamples
          <= 10^9.
FORMULA:  Conjectured explicit formula: if the binary expansion of n-1 is
          n-1 = 2^(e_0) + 2^(e_1) + ... + 2^(e_k), then
          a(n) = 4*(A001109(1+(e_0)) + A001109(1+(e_1)) + ... + A001109(1+(e_k))).
AUTHOR:   Jianing Song, Oct 10 2021
```

## Status

Triage: open (no proof in the entry; the triage found no treatment of A348299
in the literature).  Related: Putnam 2020 B6 (`S ≥ 0`), and Adamczewski
(arXiv:2608.11941) on the unboundedness of A348295 via the Pell floor-shift
identity.  This module proves both comment conjectures and the explicit
formula, the latter in the equivalent Pell form `4 * A001109(i) = 2 * P(2i)`.

## Proof outline

With `P` the Pell numbers and `H = P(n+1) + P(n)` the companion
(`H² - 2 P(n+1)² = (-1)^(n+1)`), a Farey-neighbour argument gives the integer
floor-shift `⌊(P(n+1)+i)√2⌋ = H + ⌊i√2⌋` for `1 ≤ i < P(n+2)`.  Hence
`S(P(n+1) + j) = S(P(n+1)) + (-1)^n S(j)` for `j < P(n+2)`, so
`S(P(2t)) = 2t`, `S(P(2t+1)) = 1`, `0 ≤ S(j) ≤ n` on `[0, P(n+1))`, and the
zeros in `[P(n+1), P(n+2))` are exactly `2 P(n+1) + z` with `n` odd,
`z < P(n)` a zero.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A348299SumFloorSqrt

/-! ## Definitions mirroring the entry -/

/-- The sign `(-1)^⌊k(√2-1)⌋` (the summand of A348295).  The floor is taken as a
natural-number floor, which agrees with the integer floor since `k(√2-1) ≥ 0`. -/
noncomputable def eps (k : ℕ) : ℤ := (-1) ^ ⌊(k : ℝ) * (Real.sqrt 2 - 1)⌋₊

/-- `S(m) = Σ_{k=1..m} (-1)^⌊k(√2-1)⌋`, the sequence A348295 (with `S 0 = 0`). -/
noncomputable def S (m : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 m, eps k

/-- Pell numbers A000129: `P 0 = 0`, `P 1 = 1`, `P (n+2) = 2 P (n+1) + P n`. -/
def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * pell (n + 1) + pell n

/-- Integer form of the sign, as in the entry's PARI program:
`(-1)^(isqrt(2k²) - k)`. -/
def epsN (k : ℕ) : ℤ := (-1) ^ (Nat.sqrt (2 * k ^ 2) - k)

/-- Integer form of `S`: `SN m = Σ_{k<m} epsN (k+1)`. -/
def SN (m : ℕ) : ℤ := ∑ k ∈ Finset.range m, epsN (k + 1)

/-! ## Bridge from the real floor to `Nat.sqrt` -/

/-- `⌊k(√2-1)⌋ = isqrt(2k²) - k`. -/
theorem floor_eq (k : ℕ) : ⌊(k : ℝ) * (Real.sqrt 2 - 1)⌋₊ = Nat.sqrt (2 * k ^ 2) - k := by
  have hsq : Real.sqrt ((2 * k ^ 2 : ℕ) : ℝ) = Real.sqrt 2 * k := by
    push_cast
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hle : k ≤ Nat.sqrt (2 * k ^ 2) := Nat.le_sqrt.2 (by nlinarith)
  have hreal : (k : ℝ) ≤ Real.sqrt ((2 * k ^ 2 : ℕ) : ℝ) :=
    le_trans (by exact_mod_cast hle) Real.nat_sqrt_le_real_sqrt
  have hx : (k : ℝ) * (Real.sqrt 2 - 1) = Real.sqrt ((2 * k ^ 2 : ℕ) : ℝ) - k := by
    rw [hsq]; ring
  have hadd := Nat.floor_add_natCast (sub_nonneg.2 hreal) k
  rw [sub_add_cancel, Real.nat_floor_real_sqrt_eq_nat_sqrt] at hadd
  rw [hx]
  omega

/-- The real-floor sign agrees with the integer sign. -/
theorem eps_eq (k : ℕ) : eps k = epsN k := by
  rw [eps, epsN, floor_eq]

/-- The real-floor partial sum agrees with the integer partial sum. -/
theorem S_eq (m : ℕ) : S m = SN m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [S, Finset.sum_Icc_succ_top (by omega), ← S, ih, eps_eq]
    simp only [SN, Finset.sum_range_succ]

/-! ## Ground truth -/

example : (List.range 9).map pell = [0, 1, 2, 5, 12, 29, 70, 169, 408] := by decide

/-- The first four terms of A348299 are exactly the zeros of `S` below `30`. -/
example : ∀ m < 30, (SN m = 0 ↔ m = 0 ∨ m = 4 ∨ m = 24 ∨ m = 28) := by
  intro m hm
  interval_cases m <;> norm_num [SN, epsN, Finset.sum_range_succ]

example : S 24 = 0 := by rw [S_eq]; norm_num [SN, epsN, Finset.sum_range_succ]

example : eps 3 = -1 := by rw [eps_eq]; norm_num [epsN]

/-! ## Pell numbers -/

/-- The Pell recurrence. -/
theorem pell_succ_succ (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := rfl

/-- `P (n+1) ≥ 1`. -/
theorem pell_pos (n : ℕ) : 0 < pell (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [pell_succ_succ]; omega

/-- `P n ≤ P (n+1)`. -/
theorem pell_le_succ (n : ℕ) : pell n ≤ pell (n + 1) := by
  cases n with
  | zero => decide
  | succ n => rw [pell_succ_succ]; omega

/-- Pell numbers are monotone. -/
theorem pell_mono : Monotone pell := monotone_nat_of_le_succ pell_le_succ

/-- `P (n+1) < P (n+2)`. -/
theorem pell_lt_succ (n : ℕ) : pell (n + 1) < pell (n + 2) := by
  have hpos := pell_pos n
  rw [pell_succ_succ]; omega

/-- `n + 1 ≤ P (n+1)`. -/
theorem succ_le_pell (n : ℕ) : n + 1 ≤ pell (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hlt := pell_lt_succ n
    show n + 1 + 1 ≤ pell (n + 2)
    omega

/-- `P n ≡ n (mod 2)`. -/
theorem pell_mod_two (n : ℕ) : pell n % 2 = n % 2 := by
  have key : ∀ n, pell n % 2 = n % 2 ∧ pell (n + 1) % 2 = (n + 1) % 2 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [pell_succ_succ]; omega
  exact (key n).1

/-- `(-1)^(P n) = (-1)^n`. -/
theorem neg_one_pow_pell (n : ℕ) : (-1 : ℤ) ^ pell n = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, pell_mod_two, ← neg_one_pow_eq_pow_mod_two]

/-- The Pell identity `(P(n+1) + P n)² - 2 P(n+1)² = (-1)^(n+1)`. -/
theorem pell_identity (n : ℕ) :
    ((pell (n + 1) : ℤ) + pell n) ^ 2 - 2 * (pell (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [pell]
  | succ n ih =>
    rw [pell_succ_succ, pow_succ]
    push_cast
    linear_combination (-1 : ℤ) * ih

/-! ## The floor-shift identity -/

/-- `r² ≠ 2 i²` for `i ≥ 1` (irrationality of `√2`). -/
theorem mul_self_ne_two_mul (r i : ℕ) (hi : 1 ≤ i) : r * r ≠ 2 * i ^ 2 := by
  intro h
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hsqrt : Real.sqrt 2 = (r : ℝ) / i := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    have hR : (r : ℝ) * r = 2 * (i : ℝ) ^ 2 := by exact_mod_cast h
    field_simp
    linarith
  exact irrational_sqrt_two ⟨(r : ℚ) / i, by push_cast; rw [hsqrt]⟩

/-- Farey core, Pell sign `+1`: if `H² = 2P² + 1`, `1 ≤ i < P + H` and
`r = ⌊i√2⌋`, then `H + r = ⌊(P+i)√2⌋`. -/
theorem core_plus (P H i r : ℤ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hpell : H ^ 2 = 2 * P ^ 2 + 1)
    (hi1 : 1 ≤ i) (hi : i < P + H) (hr0 : 0 ≤ r) (h1 : r ^ 2 < 2 * i ^ 2)
    (h2 : 2 * i ^ 2 < (r + 1) ^ 2) :
    (H + r) ^ 2 ≤ 2 * (P + i) ^ 2 ∧ 2 * (P + i) ^ 2 < (H + r + 1) ^ 2 := by
  have hPr : P * r < H * i := by
    have hsq : (P * r) ^ 2 < (H * i) ^ 2 := by nlinarith
    have habs := abs_lt_of_sq_lt_sq' hsq (by positivity); linarith [habs.2]
  have hfarey : r * H ≤ 2 * P * i := by
    by_contra hcon
    rw [not_le] at hcon
    have hid : i = H * (H * i - P * r) + P * (r * H - 2 * P * i) := by
      linear_combination (-i) * hpell
    nlinarith
  have hup : 2 * P * i < H * (r + 1) := by
    have hsq : (2 * P * i) ^ 2 < (H * (r + 1)) ^ 2 := by nlinarith
    have habs := abs_lt_of_sq_lt_sq' hsq (by positivity); linarith [habs.2]
  constructor <;> nlinarith

/-- Farey core, Pell sign `-1`: if `H² + 1 = 2P²`, `1 ≤ i < P + H` and
`r = ⌊i√2⌋`, then `H + r = ⌊(P+i)√2⌋`. -/
theorem core_minus (P H i r : ℤ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hpell : H ^ 2 + 1 = 2 * P ^ 2)
    (hi1 : 1 ≤ i) (hi : i < P + H) (hr0 : 0 ≤ r) (h1 : r ^ 2 < 2 * i ^ 2)
    (h2 : 2 * i ^ 2 < (r + 1) ^ 2) :
    (H + r) ^ 2 ≤ 2 * (P + i) ^ 2 ∧ 2 * (P + i) ^ 2 < (H + r + 1) ^ 2 := by
  have hlow : H * r < 2 * P * i := by
    have hsq : (H * r) ^ 2 < (2 * P * i) ^ 2 := by nlinarith
    have habs := abs_lt_of_sq_lt_sq' hsq (by positivity); linarith [habs.2]
  have hHi : H * i < P * (r + 1) := by
    have hsq : (H * i) ^ 2 < (P * (r + 1)) ^ 2 := by nlinarith
    have habs := abs_lt_of_sq_lt_sq' hsq (by positivity); linarith [habs.2]
  have hfarey : 2 * P * i ≤ H * (r + 1) := by
    by_contra hcon
    rw [not_le] at hcon
    have hid : i = P * (2 * P * i - H * (r + 1)) + H * (P * (r + 1) - H * i) := by
      linear_combination i * hpell
    nlinarith
  have hstrict : 2 * P * i < H * (r + 1) ∨ 2 ≤ (r + 1) ^ 2 - 2 * i ^ 2 := by
    rcases hfarey.lt_or_eq with h | h
    · exact Or.inl h
    · right
      by_contra hc
      have hB : (r + 1) ^ 2 = 2 * i ^ 2 + 1 := by omega
      have hsq : (2 * P * i) ^ 2 = (H * (r + 1)) ^ 2 := by rw [h]
      have hpar : 2 * P ^ 2 = 2 * i ^ 2 + 1 := by nlinarith
      omega
  constructor
  · nlinarith
  · rcases hstrict with h | h <;> nlinarith

/-- Integer floor-shift: `isqrt(2(P(n+1)+i)²) = P(n+1) + P(n) + isqrt(2i²)` for
`1 ≤ i < P(n+2)`, i.e. `⌊(P(n+1)+i)√2⌋ = H(n+1) + ⌊i√2⌋`. -/
theorem sqrt_shift (n i : ℕ) (hi1 : 1 ≤ i) (hi : i < pell (n + 2)) :
    Nat.sqrt (2 * (pell (n + 1) + i) ^ 2) = (pell (n + 1) + pell n) + Nat.sqrt (2 * i ^ 2) := by
  have hr1 := Nat.sqrt_le (2 * i ^ 2)
  have hr2 := Nat.lt_succ_sqrt (2 * i ^ 2)
  have hne := mul_self_ne_two_mul (Nat.sqrt (2 * i ^ 2)) i hi1
  have hP := pell_pos n
  have hrec := pell_succ_succ n
  have hid := pell_identity n
  set r := Nat.sqrt (2 * i ^ 2) with hr
  set P := pell (n + 1) with hPdef
  set Q := pell n with hQdef
  have h1 : (r : ℤ) ^ 2 < 2 * (i : ℤ) ^ 2 := by
    have hlt : r * r < 2 * i ^ 2 := lt_of_le_of_ne hr1 hne
    have hZ : ((r * r : ℕ) : ℤ) < ((2 * i ^ 2 : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at hZ; nlinarith
  have h2 : 2 * (i : ℤ) ^ 2 < ((r : ℤ) + 1) ^ 2 := by
    have hZ : ((2 * i ^ 2 : ℕ) : ℤ) < ((Nat.succ r * Nat.succ r : ℕ) : ℤ) := by exact_mod_cast hr2
    push_cast at hZ; nlinarith
  have key : ((P : ℤ) + Q + r) ^ 2 ≤ 2 * ((P : ℤ) + i) ^ 2 ∧
      2 * ((P : ℤ) + i) ^ 2 < ((P : ℤ) + Q + r + 1) ^ 2 := by
    have hi' : (i : ℤ) < P + (P + Q) := by
      have : i < P + (P + Q) := by omega
      exact_mod_cast this
    rcases Nat.even_or_odd n with hn | hn
    · have hsign : (-1 : ℤ) ^ (n + 1) = -1 := by rw [pow_succ, hn.neg_one_pow]; norm_num
      exact core_minus P (P + Q) i r (by exact_mod_cast hP) (by omega) (by linarith)
        (by exact_mod_cast hi1) hi' (by positivity) h1 h2
    · have hsign : (-1 : ℤ) ^ (n + 1) = 1 := by rw [pow_succ, hn.neg_one_pow]; norm_num
      exact core_plus P (P + Q) i r (by exact_mod_cast hP) (by omega) (by linarith)
        (by exact_mod_cast hi1) hi' (by positivity) h1 h2
  symm
  rw [Nat.eq_sqrt]
  constructor
  · have hk := key.1
    have hZ : (((P + Q + r) * (P + Q + r) : ℕ) : ℤ) ≤ ((2 * (P + i) ^ 2 : ℕ) : ℤ) := by
      push_cast; nlinarith
    exact_mod_cast hZ
  · have hk := key.2
    have hZ : ((2 * (P + i) ^ 2 : ℕ) : ℤ) < (((P + Q + r + 1) * (P + Q + r + 1) : ℕ) : ℤ) := by
      push_cast; nlinarith
    exact_mod_cast hZ

/-- Sign shift: `epsN (P(n+1) + i) = (-1)^n epsN i` for `1 ≤ i < P(n+2)`. -/
theorem epsN_shift (n i : ℕ) (hi1 : 1 ≤ i) (hi : i < pell (n + 2)) :
    epsN (pell (n + 1) + i) = (-1) ^ n * epsN i := by
  have hs := sqrt_shift n i hi1 hi
  have hle : i ≤ Nat.sqrt (2 * i ^ 2) := Nat.le_sqrt.2 (by nlinarith)
  have hexp : Nat.sqrt (2 * (pell (n + 1) + i) ^ 2) - (pell (n + 1) + i) =
      pell n + (Nat.sqrt (2 * i ^ 2) - i) := by omega
  rw [epsN, epsN, hexp, pow_add, neg_one_pow_pell]

/-- `SN (m+1) = SN m + epsN (m+1)`. -/
theorem SN_succ (m : ℕ) : SN (m + 1) = SN m + epsN (m + 1) := Finset.sum_range_succ _ _

/-- Block shift: `S(P(n+1) + j) = S(P(n+1)) + (-1)^n S(j)` for `j < P(n+2)`. -/
theorem SN_shift (n j : ℕ) (hj : j < pell (n + 2)) :
    SN (pell (n + 1) + j) = SN (pell (n + 1)) + (-1) ^ n * SN j := by
  induction j with
  | zero => simp [SN]
  | succ j ih =>
    rw [← add_assoc, SN_succ, ih (by omega), add_assoc (pell (n + 1)) j 1,
      epsN_shift n (j + 1) (by omega) hj, SN_succ]
    ring

/-- The values at Pell numbers: `S(P(2t)) = 2t` and `S(P(2t+1)) = 1`. -/
theorem SN_pell (t : ℕ) : SN (pell (2 * t)) = 2 * t ∧ SN (pell (2 * t + 1)) = 1 := by
  have hrec : ∀ n, SN (pell (n + 2)) =
      SN (pell (n + 1)) + (-1) ^ n * (SN (pell (n + 1)) + (-1) ^ n * SN (pell n)) := by
    intro n
    have hP := pell_pos n
    have hsplit : pell (n + 2) = pell (n + 1) + (pell (n + 1) + pell n) := by
      rw [pell_succ_succ]; ring
    rw [hsplit, SN_shift n _ (by rw [pell_succ_succ]; omega),
      SN_shift n _ (by rw [pell_succ_succ]; omega)]
  induction t with
  | zero => exact ⟨rfl, by norm_num [SN, epsN, pell]⟩
  | succ t ih =>
    have heven : SN (pell (2 * (t + 1))) = 2 * (t + 1 : ℕ) := by
      have h := hrec (2 * t)
      rw [show 2 * t + 2 = 2 * (t + 1) by ring, ih.1, ih.2,
        (even_two_mul t).neg_one_pow] at h
      rw [h]; push_cast; ring
    refine ⟨heven, ?_⟩
    have h := hrec (2 * t + 1)
    rw [show 2 * t + 1 + 2 = 2 * (t + 1) + 1 by ring, show 2 * t + 1 + 1 = 2 * (t + 1) by ring,
      heven, ih.2, (odd_two_mul_add_one t).neg_one_pow] at h
    rw [h]; ring

/-- `S(P(n+1))` and the shift sign, packaged by parity of `n`. -/
theorem SN_pell_succ_cases (n : ℕ) :
    (Even n ∧ SN (pell (n + 1)) = 1 ∧ (-1 : ℤ) ^ n = 1) ∨
      (Odd n ∧ SN (pell (n + 1)) = (n : ℤ) + 1 ∧ (-1 : ℤ) ^ n = -1) := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · exact Or.inl ⟨even_two_mul t, (SN_pell t).2, (even_two_mul t).neg_one_pow⟩
  · refine Or.inr ⟨odd_two_mul_add_one t, ?_, (odd_two_mul_add_one t).neg_one_pow⟩
    rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, (SN_pell (t + 1)).1]
    push_cast; ring

/-! ## Bounds `0 ≤ S ≤ n` on `[0, P(n+1))` -/

/-- `0 ≤ S(j) ≤ n` for all `j < P(n+1)`. -/
theorem SN_bounds (n : ℕ) : ∀ j < pell (n + 1), 0 ≤ SN j ∧ SN j ≤ n := by
  have key : ∀ n, (∀ j < pell (n + 1), 0 ≤ SN j ∧ SN j ≤ n) ∧
      (∀ j < pell (n + 2), 0 ≤ SN j ∧ SN j ≤ (n + 1 : ℕ)) := by
    intro n
    induction n with
    | zero =>
      have hp1 : pell 1 = 1 := rfl
      have hp2 : pell 2 = 2 := rfl
      have hS0 : SN 0 = 0 := Finset.sum_range_zero _
      have hS1 : SN 1 = 1 := (SN_pell 0).2
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · have hj1 : j < 1 := hj
        obtain rfl : j = 0 := by omega
        rw [hS0]
        exact ⟨le_refl 0, le_refl 0⟩
      · have hj2 : j < 2 := hj
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · rw [hS0]
          exact ⟨le_refl 0, by norm_num⟩
        · rw [hS1]
          exact ⟨zero_le_one, le_refl 1⟩
    | succ n ih =>
      have ih2 : ∀ j < pell (n + 2), 0 ≤ SN j ∧ SN j ≤ (n : ℤ) + 1 := fun j hj => by
        have hb := ih.2 j hj; push_cast at hb; exact hb
      have ih1 : ∀ j < pell (n + 1), 0 ≤ SN j ∧ SN j ≤ (n : ℤ) := ih.1
      refine ⟨ih.2, ?_⟩
      show ∀ j < pell (n + 3), 0 ≤ SN j ∧ SN j ≤ ((n + 2 : ℕ) : ℤ)
      push_cast
      intro j hj
      have hrec : pell (n + 3) = 2 * pell (n + 2) + pell (n + 1) := pell_succ_succ (n + 1)
      by_cases hlt : j < pell (n + 2)
      · obtain ⟨h0, h1⟩ := ih2 j hlt
        exact ⟨h0, by linarith⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = pell (n + 2) + j' := ⟨j - pell (n + 2), by omega⟩
      have hj' : j' < pell (n + 3) := by omega
      rw [SN_shift (n + 1) j' hj']
      by_cases hlt' : j' < pell (n + 2)
      · obtain ⟨h0, h1⟩ := ih2 j' hlt'
        rcases SN_pell_succ_cases (n + 1) with ⟨_, ha, hs⟩ | ⟨_, ha, hs⟩
        · rw [ha, hs]; constructor <;> linarith
        · rw [ha, hs]; push_cast; constructor <;> linarith
      obtain ⟨z, rfl⟩ : ∃ z, j' = pell (n + 2) + z := ⟨j' - pell (n + 2), by omega⟩
      have hz : z < pell (n + 1) := by omega
      have hz3 : z < pell (n + 3) := by omega
      rw [SN_shift (n + 1) z hz3]
      obtain ⟨h0, h1⟩ := ih1 z hz
      rcases SN_pell_succ_cases (n + 1) with ⟨_, ha, hs⟩ | ⟨_, ha, hs⟩
      · rw [ha, hs]; constructor <;> linarith
      · rw [ha, hs]; push_cast; constructor <;> linarith
  exact (key n).1

/-- `S(j) ≥ 0` for all `j` (Putnam 2020 B6). -/
theorem SN_nonneg (j : ℕ) : 0 ≤ SN j :=
  (SN_bounds j j (by have := succ_le_pell j; omega)).1

/-! ## Location of the zeros -/

/-- Every `m ≥ 1` lies in a Pell block `[P(n+1), P(n+2))`. -/
theorem exists_block (m : ℕ) (hm : 1 ≤ m) : ∃ n, pell (n + 1) ≤ m ∧ m < pell (n + 2) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨0, by decide, by decide⟩
  | succ m _ ih =>
    obtain ⟨n, h1, h2⟩ := ih
    by_cases hlt : m + 1 < pell (n + 2)
    · exact ⟨n, by omega, hlt⟩
    · have h3 : pell (n + 2) < pell (n + 3) := pell_lt_succ (n + 1)
      refine ⟨n + 1, ?_, ?_⟩
      · show pell (n + 2) ≤ m + 1
        omega
      · show m + 1 < pell (n + 3)
        omega

/-- A zero in the block `[P(n+1), P(n+2))` forces `n` odd and has the form
`2 P(n+1) + z` with `z < P(n)` a zero. -/
theorem zero_in_block (n m : ℕ) (h1 : pell (n + 1) ≤ m) (h2 : m < pell (n + 2))
    (hz : SN m = 0) : Odd n ∧ ∃ z, z < pell n ∧ m = 2 * pell (n + 1) + z ∧ SN z = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = pell (n + 1) + j := ⟨m - pell (n + 1), by omega⟩
  have hrec := pell_succ_succ n
  rw [SN_shift n j (by omega)] at hz
  rcases SN_pell_succ_cases n with ⟨_, ha, hs⟩ | ⟨hodd, ha, hs⟩
  · rw [ha, hs] at hz
    have := SN_nonneg j
    exact absurd hz (by linarith)
  · rw [ha, hs] at hz
    refine ⟨hodd, ?_⟩
    by_cases hlt : j < pell (n + 1)
    · have hb := (SN_bounds n j hlt).2
      exact absurd hz (by linarith)
    obtain ⟨z, rfl⟩ : ∃ z, j = pell (n + 1) + z := ⟨j - pell (n + 1), by omega⟩
    have hzlt : z < pell n := by omega
    rw [SN_shift n z (by omega), ha, hs] at hz
    exact ⟨z, hzlt, by ring, by linarith⟩

/-- Conversely, for odd `n` and a zero `z < P(n)`, `2 P(n+1) + z` is a zero. -/
theorem zero_of_zero (n z : ℕ) (hn : Odd n) (hz : z < pell n) (h0 : SN z = 0) :
    SN (2 * pell (n + 1) + z) = 0 := by
  have hrec := pell_succ_succ n
  rw [two_mul, add_assoc, SN_shift n _ (by omega), SN_shift n z (by omega), h0,
    hn.neg_one_pow]
  ring

/-! ## The conjectures -/

/-- **A348299, first comment conjecture (Jianing Song, Oct 10 2021).**
"Conjecture: sequence is infinite."  The set of `m` with
`Σ_{k=1..m} (-1)^⌊k(√2-1)⌋ = 0` is infinite; indeed every `2 P(2t)` (`t ≥ 1`)
is a zero. -/
theorem zeros_infinite : {m : ℕ | S m = 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun t => 2 * pell (2 * t + 2)) ?_ ?_
  · intro a b hab
    have hmono : StrictMono (fun t => pell (2 * t + 2)) := by
      refine strictMono_nat_of_lt_succ fun t => ?_
      have h1 : pell (2 * t + 2) < pell (2 * t + 3) := pell_lt_succ (2 * t + 1)
      have h2 : pell (2 * t + 3) < pell (2 * t + 4) := pell_lt_succ (2 * t + 2)
      show pell (2 * t + 2) < pell (2 * (t + 1) + 2)
      rw [show 2 * (t + 1) + 2 = 2 * t + 4 by ring]
      omega
    exact hmono.injective (by simpa using hab)
  · intro t
    simp only [Set.mem_ofPred_eq, S_eq]
    exact zero_of_zero (2 * t + 1) 0 (odd_two_mul_add_one t) (pell_pos _) rfl

/-- **A348299, second comment conjecture (Jianing Song, Oct 10 2021).**
"Conjecture: all terms are divisible by 4."  If
`Σ_{k=1..m} (-1)^⌊k(√2-1)⌋ = 0` then `4 ∣ m`. -/
theorem four_dvd_of_S_eq_zero (m : ℕ) (hm : S m = 0) : 4 ∣ m := by
  rw [S_eq] at hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact dvd_zero 4
    obtain ⟨n, h1, h2⟩ := exists_block m hpos
    obtain ⟨hodd, z, hz, rfl, hz0⟩ := zero_in_block n m h1 h2 hm
    have hzm : z < 2 * pell (n + 1) + z := by have := pell_pos n; omega
    have h4z := ih z hzm hz0
    have hpar := pell_mod_two (n + 1)
    obtain ⟨t, rfl⟩ := hodd
    have h2P : 2 ∣ pell (2 * t + 1 + 1) := by omega
    exact dvd_add (by simpa [mul_comm] using Nat.mul_dvd_mul_left 2 h2P) h4z

/-- `Σ_{i<s} 2 P(2(i+1)) + 1 = P(2s+1)`. -/
theorem sum_pell_even (s : ℕ) : ∑ i ∈ Finset.range s, 2 * pell (2 * (i + 1)) + 1 = pell (2 * s + 1) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Finset.sum_range_succ, show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by ring, pell_succ_succ,
      show 2 * s + 1 + 1 = 2 * (s + 1) by ring]
    omega

/-- **A348299, conjectured explicit formula (Jianing Song, Oct 10 2021).**
`Σ_{k=1..m} (-1)^⌊k(√2-1)⌋ = 0` iff `m = Σ_{i ∈ F} 2 P(2(i+1))` for a finite set
`F` of naturals, where `P` is the Pell sequence.  Since `2 P(2i) = 4 A001109(i)`,
this is the entry's formula `a(n) = 4 Σ_j A001109(1 + e_j)` over the binary
digits `e_j` of `n - 1`. -/
theorem S_eq_zero_iff (m : ℕ) :
    S m = 0 ↔ ∃ F : Finset ℕ, m = ∑ i ∈ F, 2 * pell (2 * (i + 1)) := by
  rw [S_eq]
  constructor
  · intro hm
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · exact ⟨∅, rfl⟩
      obtain ⟨n, h1, h2⟩ := exists_block m hpos
      obtain ⟨hodd, z, hz, rfl, hz0⟩ := zero_in_block n m h1 h2 hm
      have hzm : z < 2 * pell (n + 1) + z := by have := pell_pos n; omega
      obtain ⟨F, hF⟩ := ih z hzm hz0
      obtain ⟨a, rfl⟩ := hodd
      have hsub : ∀ x ∈ F, x < a := by
        intro x hx
        by_contra hxa
        rw [not_lt] at hxa
        have hle : 2 * pell (2 * (x + 1)) ≤ z :=
          hF ▸ Finset.single_le_sum (f := fun i => 2 * pell (2 * (i + 1)))
            (fun _ _ => Nat.zero_le _) hx
        have hmono : pell (2 * a + 1) ≤ pell (2 * (x + 1)) := pell_mono (by omega)
        have := pell_pos (2 * a)
        omega
      have hnot : a ∉ F := fun ha => lt_irrefl a (hsub a ha)
      refine ⟨insert a F, ?_⟩
      rw [Finset.sum_insert hnot, ← hF, show 2 * a + 1 + 1 = 2 * (a + 1) by ring]
  · rintro ⟨F, rfl⟩
    induction F using Finset.induction_on_max with
    | empty => rfl
    | insert a F hlt ih =>
      have hnot : a ∉ F := fun ha => lt_irrefl a (hlt a ha)
      rw [Finset.sum_insert hnot]
      have hsum : ∑ i ∈ F, 2 * pell (2 * (i + 1)) < pell (2 * a + 1) := by
        have hsub : F ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (hlt x hx)
        have hle := Finset.sum_le_sum_of_subset (f := fun i => 2 * pell (2 * (i + 1))) hsub
        have := sum_pell_even a
        omega
      have h := zero_of_zero (2 * a + 1) _ (odd_two_mul_add_one a) hsum ih
      rwa [show 2 * a + 1 + 1 = 2 * (a + 1) by ring] at h

end Candidates.A348299SumFloorSqrt
