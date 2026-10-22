/-
# Block frequencies `01`/`10` in the base-3/2 Thue–Morse word (and `01` in Dekking's `t'`)

## Source

J. Cassaigne, B. Espinoza, M. Rigo, M. Stipulanti, *Symbols frequencies in the
Thue–Morse word in base 3/2 and related conjectures*, arXiv:2602.21895.
Recorded 2026-10-21.

* Table `tab:base32expansions` (Section 1.3): the first 27 letters of
  `t_{3/2}`, the parity of the base-3/2 sum of digits.
* Proposition `pro:ytop` (Section 2): `Δ(t_{3/2})` is the `(9,4)`-Toeplitz word
  `T(01?0?10??)`; its proof derives `y_{3n} = 0`, `y_{3n+1} = ¬y_{2n}` and
  `y_{3n+2} = ¬y_{2n+1}` for `y = Δ(t_{3/2})`.
* Lemma `lem:morphic_image` (Section 1.4): Dekking's `t'` (OEIS A357448, the
  fixed point of the 2-block substitution `00, 01 ↦ 010`, `10, 11 ↦ 101`)
  equals `φ(t_{3/2})` with `φ : 0 ↦ 010, 1 ↦ 101`.
* Section 4, concluding remarks, verbatim:
  "Experiments show that in this word, the frequencies of 0 and 3 are equal
  to 3/10 whereas those of 1 and 2 are equal to 2/10. This would mean that
  the frequencies of 00 and 11 (resp., 01 and 10) in t_{3/2} are equal to
  3/10 (resp., 2/10)." and, for Dekking's word, under the assumption that
  the frequencies exist in `t_{3/2}`,
  "freq_{t'}(01) = 1/3 (freq(0) + freq(1) + freq(01)) = 1/3 + 2/30 = 4/10."
  OEIS A357448 records Dekking's conjecture `mu[01] = 4/10`.

## Status

The paper reports the 2-block frequencies only as experiments; it proves
only the letter frequencies `1/2` (by 2-adic harmonic analysis).  This file
proves unconditionally, by an elementary discrepancy argument from the
recurrences of `pro:ytop`, that:

* the density of positions `n` with `t n ≠ t (n+1)` is `2/5`;
* the factors `01` and `10` of `t_{3/2}` each have frequency `1/5`;
* the factor `01` of Dekking's `t'` has frequency `2/5`.

The `00`/`11` frequencies `3/10` need the paper's letter-frequency theorem and
are not treated here.

## Definitions

`t32` is defined by the recurrences `t 0 = 0`, `t (3n) = t (2n)`,
`t (3n+1) = t (2n)`, `t (3n+2) = t (2n+1) + 1` (the 2-block substitution
`ab ↦ a a (b+1)`); the ground-truth example checks it against the paper's
table for `n ≤ 26`.  `tDek` is defined by Dekking's 2-block substitution
`ab ↦ a (a+1) a`, i.e. `t' (3n) = t' (2n)`, `t' (3n+1) = t' (2n) + 1`,
`t' (3n+2) = t' (2n)`, and is checked against the paper's printed prefix.
A *frequency* of a pattern is the limit of the proportion of starting
positions `n < N` at which it occurs.

## Proof idea

With `S N` the number of `n < N` with `t n ≠ t (n+1)`, the recurrences give
`S (3N) + S (2N) = 2N`, so `E N = 5 S N - 2 N` satisfies `E (3N) = -E (2N)`
and `|E (N+1) - E N| ≤ 3`; hence `|E n| ≤ 12 log₂ n + 12` and `S N / N → 2/5`.
In a binary word the counts of `01` and `10` differ by the last letter, so
each is `S/2 + O(1)`.  For `t'`, a prefix of length `3q` contains exactly
`q + #01(t_{3/2}, q)` occurrences of `01`.
-/
import Mathlib

set_option autoImplicit false

namespace BlockFrequenciesBaseThue

open Filter Topology

/-! ## The base-3/2 Thue–Morse word -/

/-- The Thue–Morse word `t_{3/2}` in base `3/2`, as a function `ℕ → ZMod 2`, given by
`t 0 = 0`, `t (3n) = t (2n)`, `t (3n+1) = t (2n)`, `t (3n+2) = t (2n+1) + 1`
(arXiv:2602.21895, Section 1.3). -/
def t32 : ℕ → ZMod 2
  | 0 => 0
  | m + 1 =>
    if (m + 1) % 3 = 2 then t32 (2 * ((m + 1) / 3) + 1) + 1 else t32 (2 * ((m + 1) / 3))
decreasing_by all_goals omega

/-- Ground truth: the first 27 letters agree with Table `tab:base32expansions`. -/
example : (List.range 27).map t32 =
    [0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0] := by
  decide +kernel

/-- `t_{3/2}(0) = 0`. -/
theorem t32_zero : t32 0 = 0 := by rw [t32]

/-- `t_{3/2}(3n) = t_{3/2}(2n)`. -/
theorem t32_three_mul (n : ℕ) : t32 (3 * n) = t32 (2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · obtain ⟨m, hm⟩ : ∃ m, 3 * n = m + 1 := ⟨3 * n - 1, by omega⟩
    rw [hm, t32, if_neg (by omega)]
    congr 2
    omega

/-- `t_{3/2}(3n+1) = t_{3/2}(2n)`. -/
theorem t32_three_mul_add_one (n : ℕ) : t32 (3 * n + 1) = t32 (2 * n) := by
  rw [t32, if_neg (by omega)]
  congr 2
  omega

/-- `t_{3/2}(3n+2) = t_{3/2}(2n+1) + 1`. -/
theorem t32_three_mul_add_two (n : ℕ) : t32 (3 * n + 2) = t32 (2 * n + 1) + 1 := by
  rw [show 3 * n + 2 = (3 * n + 1) + 1 by ring, t32, if_pos (by omega)]
  congr 3
  omega

/-! ## The difference sequence and its discrepancy -/

/-- `flipInd n = 1` if `t_{3/2}(n) ≠ t_{3/2}(n+1)` (the letter `y_n` of `Δ(t_{3/2})`),
and `0` otherwise. -/
def flipInd (n : ℕ) : ℕ := if t32 n ≠ t32 (n + 1) then 1 else 0

/-- `y_{3n} = 0` (proof of Proposition `pro:ytop`). -/
theorem flipInd_three_mul (n : ℕ) : flipInd (3 * n) = 0 := by
  simp [flipInd, t32_three_mul, t32_three_mul_add_one]

/-- `y_{3n+1} = 1 - y_{2n}` (proof of Proposition `pro:ytop`). -/
theorem flipInd_three_mul_add_one (n : ℕ) : flipInd (3 * n + 1) = 1 - flipInd (2 * n) := by
  have key : ∀ a b : ZMod 2,
      (if a ≠ b + 1 then 1 else 0 : ℕ) = 1 - (if a ≠ b then 1 else 0) := by
    decide
  simp only [flipInd]
  rw [t32_three_mul_add_one, show 3 * n + 1 + 1 = 3 * n + 2 by ring, t32_three_mul_add_two]
  exact key _ _

/-- `y_{3n+2} = 1 - y_{2n+1}` (proof of Proposition `pro:ytop`). -/
theorem flipInd_three_mul_add_two (n : ℕ) :
    flipInd (3 * n + 2) = 1 - flipInd (2 * n + 1) := by
  have key : ∀ a b : ZMod 2,
      (if a + 1 ≠ b then 1 else 0 : ℕ) = 1 - (if a ≠ b then 1 else 0) := by
    decide
  simp only [flipInd]
  rw [t32_three_mul_add_two, show 3 * n + 2 + 1 = 3 * (n + 1) by ring, t32_three_mul,
    show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
  exact key _ _

/-- `flipInd` is an indicator. -/
theorem flipInd_le_one (n : ℕ) : flipInd n ≤ 1 := by
  unfold flipInd
  split_ifs <;> omega

/-- `flipCount N` is the number of `n < N` with `t_{3/2}(n) ≠ t_{3/2}(n+1)`. -/
def flipCount (N : ℕ) : ℕ := ∑ n ∈ Finset.range N, flipInd n

/-- `flipCount` is the cardinality of the filtered range. -/
theorem flipCount_eq_card (N : ℕ) :
    flipCount N = ((Finset.range N).filter (fun n => t32 n ≠ t32 (n + 1))).card := by
  rw [Finset.card_filter]
  rfl

/-- The self-similarity `S(3N) + S(2N) = 2N` of the change count. -/
theorem flipCount_three_mul_add (N : ℕ) : flipCount (3 * N) + flipCount (2 * N) = 2 * N := by
  induction N with
  | zero => simp [flipCount]
  | succ N ih =>
    have h3 : flipCount (3 * (N + 1)) =
        flipCount (3 * N) + flipInd (3 * N) + flipInd (3 * N + 1) + flipInd (3 * N + 2) := by
      simp only [flipCount, show 3 * (N + 1) = 3 * N + 2 + 1 by ring, Finset.sum_range_succ]
    have h2 : flipCount (2 * (N + 1)) =
        flipCount (2 * N) + flipInd (2 * N) + flipInd (2 * N + 1) := by
      simp only [flipCount, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ]
    rw [h3, h2, flipInd_three_mul, flipInd_three_mul_add_one, flipInd_three_mul_add_two]
    have h0 := flipInd_le_one (2 * N)
    have h1 := flipInd_le_one (2 * N + 1)
    omega

/-- The discrepancy `E N = 5 S N - 2 N` of the change count from density `2/5`. -/
def disc (N : ℕ) : ℤ := 5 * (flipCount N : ℤ) - 2 * N

/-- `E (3N) = - E (2N)`. -/
theorem disc_three_mul (N : ℕ) : disc (3 * N) = - disc (2 * N) := by
  have h := flipCount_three_mul_add N
  simp only [disc]
  push_cast
  omega

/-- The discrepancy moves by at most `3` per step. -/
theorem abs_disc_add_le (a k : ℕ) : |disc (a + k)| ≤ |disc a| + 3 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : flipCount (a + (k + 1)) = flipCount (a + k) + flipInd (a + k) := by
      simp only [flipCount, ← add_assoc, Finset.sum_range_succ]
    have h1 := flipInd_le_one (a + k)
    have hstep : |disc (a + (k + 1)) - disc (a + k)| ≤ 3 := by
      simp only [disc, hs]
      push_cast
      rw [abs_le]
      constructor <;> omega
    have htri := abs_sub_abs_le_abs_sub (disc (a + (k + 1))) (disc (a + k))
    push_cast
    linarith

/-- Logarithmic discrepancy bound `|5 S n - 2 n| ≤ 12 ⌊log₂ n⌋ + 12`. -/
theorem abs_disc_le_log (n : ℕ) : |disc n| ≤ 12 * (Nat.log 2 n : ℤ) + 12 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [disc, flipCount]
    set q := n / 3 with hq
    set q' := (2 * q) / 3 with hq'
    have hA : |disc n| ≤ |disc (2 * q)| + 6 := by
      have h := abs_disc_add_le (3 * q) (n % 3)
      rw [show 3 * q + n % 3 = n by omega, disc_three_mul, abs_neg] at h
      have hr : (n % 3 : ℤ) ≤ 2 := by omega
      push_cast at h
      linarith
    have hB : |disc (2 * q)| ≤ |disc (2 * q')| + 6 := by
      have h := abs_disc_add_le (3 * q') ((2 * q) % 3)
      rw [show 3 * q' + (2 * q) % 3 = 2 * q by omega, disc_three_mul, abs_neg] at h
      have hr : ((2 * q) % 3 : ℤ) ≤ 2 := by omega
      push_cast at h
      linarith
    rcases Nat.eq_zero_or_pos q' with h0 | hpos
    · have hd0 : disc 0 = 0 := by simp [disc, flipCount]
      rw [h0, mul_zero, hd0, abs_zero] at hB
      have hl : (0 : ℤ) ≤ Nat.log 2 n := by positivity
      linarith
    · have ihm := ih (2 * q') (by omega)
      have hlog : Nat.log 2 (2 * q') + 1 ≤ Nat.log 2 n := by
        rw [← Nat.log_mul_base (by norm_num) (by omega)]
        exact Nat.log_mono_right (by omega)
      have hlogZ : ((Nat.log 2 (2 * q') : ℕ) : ℤ) + 1 ≤ Nat.log 2 n := by exact_mod_cast hlog
      linarith

/-! ## From a logarithmic discrepancy to a frequency -/

/-- If `|a f n - b n| ≤ 12 ⌊log₂ n⌋ + C` for all `n`, then `f n / n → b / a`. -/
theorem tendsto_freq_of_abs_le_log (f : ℕ → ℕ) (a b : ℕ) (ha : 0 < a) (C : ℤ)
    (h : ∀ n, |(a : ℤ) * f n - b * n| ≤ 12 * (Nat.log 2 n : ℤ) + C) :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 ((b : ℝ) / a)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h1.congr (fun n => ?_)
    simp
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hbound : Tendsto (fun n : ℕ => 12 / Real.log 2 * (Real.log n / n) + |(C : ℝ)| * (1 / n))
      atTop (𝓝 0) := by
    simpa using (hlog.const_mul (12 / Real.log 2)).add (hinv.const_mul |(C : ℝ)|)
  have hD : Tendsto (fun n : ℕ => (((a : ℤ) * f n - b * n : ℤ) : ℝ) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnl : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.log n / Real.log 2 := by
      have hle := Real.natLog_le_logb n 2
      simpa [Real.logb] using hle
    have hn' : ((|(a : ℤ) * f n - b * n| : ℤ) : ℝ) ≤ 12 * (Nat.log 2 n : ℝ) + C := by
      exact_mod_cast h n
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have hC : (C : ℝ) ≤ |(C : ℝ)| := le_abs_self _
    have e1 : (12 / Real.log 2 * (Real.log n / n) + |(C : ℝ)| * (1 / n)) * n
        = 12 * (Real.log n / Real.log 2) + |(C : ℝ)| := by
      field_simp
    rw [e1]
    push_cast at hn' ⊢
    linarith
  have hD' := hD.const_mul (1 / (a : ℝ))
  have hconst : Tendsto (fun _ : ℕ => (b : ℝ) / a) atTop (𝓝 ((b : ℝ) / a)) :=
    tendsto_const_nhds
  have hsum := hconst.add hD'
  rw [mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  push_cast
  field_simp
  ring

/-! ## Main results for `t_{3/2}` -/

/-- **Density of changes.** The proportion of `n < N` with `t_{3/2}(n) ≠ t_{3/2}(n+1)`
tends to `2/5`; equivalently the letter `1` of `Δ(t_{3/2})` has frequency `2/5`
(arXiv:2602.21895, consequence of Proposition `pro:ytop`). -/
theorem tendsto_density_change :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => t32 n ≠ t32 (n + 1))).card : ℝ) / N)
      atTop (𝓝 (2 / 5)) := by
  have h := tendsto_freq_of_abs_le_log flipCount 5 2 (by norm_num) 12 (fun n => by
    have hb := abs_disc_le_log n
    simpa [disc] using hb)
  simp_rw [← flipCount_eq_card]
  norm_num at h
  exact h

/-! ## Counting the factors `01` and `10` -/

/-- Number of occurrences of the factor `01` in the word `w` starting at positions `n < N`. -/
def count01 (w : ℕ → ZMod 2) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => w n = 0 ∧ w (n + 1) = 1)).card

/-- Number of occurrences of the factor `10` in the word `w` starting at positions `n < N`. -/
def count10 (w : ℕ → ZMod 2) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => w n = 1 ∧ w (n + 1) = 0)).card

/-- In a binary word, `#01 + #10` is the number of changes and `#01 - #10` telescopes to
`w N - w 0` (as integers `0, 1`). -/
theorem count01_count10 (w : ℕ → ZMod 2) (N : ℕ) :
    count01 w N + count10 w N = ((Finset.range N).filter (fun n => w n ≠ w (n + 1))).card ∧
      (count01 w N : ℤ) - count10 w N = ((w N).val : ℤ) - (w 0).val := by
  have hadd : ∀ a b : ZMod 2,
      (if a = 0 ∧ b = 1 then 1 else 0 : ℕ) + (if a = 1 ∧ b = 0 then 1 else 0) =
        if a ≠ b then 1 else 0 := by
    decide
  have hsub : ∀ a b : ZMod 2,
      ((if a = 0 ∧ b = 1 then 1 else 0 : ℕ) : ℤ) - ((if a = 1 ∧ b = 0 then 1 else 0 : ℕ) : ℤ) =
        (b.val : ℤ) - a.val := by
    decide
  simp only [count01, count10, Finset.card_filter]
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · rw [← ih1, ← hadd (w N) (w (N + 1))]
      ring
    · push_cast at ih2 ⊢
      have hs := hsub (w N) (w (N + 1))
      push_cast at hs
      linarith

/-- **Frequency of `01` in `t_{3/2}`.** The proportion of `n < N` at which the factor `01`
occurs in `t_{3/2}` tends to `1/5` (stated as an experimental observation in the concluding
remarks of arXiv:2602.21895). -/
theorem tendsto_freq01 :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => t32 n = 0 ∧ t32 (n + 1) = 1)).card : ℝ) / N)
      atTop (𝓝 (1 / 5)) := by
  have h := tendsto_freq_of_abs_le_log (count01 t32) 10 2 (by norm_num) 17 (fun n => by
    obtain ⟨h1, h2⟩ := count01_count10 t32 n
    rw [← flipCount_eq_card] at h1
    have hb := abs_disc_le_log n
    have hv : (t32 n).val < 2 := ZMod.val_lt _
    rw [t32_zero, ZMod.val_zero] at h2
    simp only [disc] at hb
    rw [abs_le] at hb ⊢
    push_cast at h2 ⊢
    constructor <;> omega)
  norm_num at h
  exact h

/-- **Frequency of `10` in `t_{3/2}`.** The proportion of `n < N` at which the factor `10`
occurs in `t_{3/2}` tends to `1/5` (stated as an experimental observation in the concluding
remarks of arXiv:2602.21895). -/
theorem tendsto_freq10 :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => t32 n = 1 ∧ t32 (n + 1) = 0)).card : ℝ) / N)
      atTop (𝓝 (1 / 5)) := by
  have h := tendsto_freq_of_abs_le_log (count10 t32) 10 2 (by norm_num) 17 (fun n => by
    obtain ⟨h1, h2⟩ := count01_count10 t32 n
    rw [← flipCount_eq_card] at h1
    have hb := abs_disc_le_log n
    have hv : (t32 n).val < 2 := ZMod.val_lt _
    rw [t32_zero, ZMod.val_zero] at h2
    simp only [disc] at hb
    rw [abs_le] at hb ⊢
    push_cast at h2 ⊢
    constructor <;> omega)
  norm_num at h
  exact h

/-! ## Dekking's word `t'` -/

/-- Dekking's word `t'` (OEIS A357448): the fixed point starting with `0` of the 2-block
substitution `00, 01 ↦ 010`, `10, 11 ↦ 101`, i.e. `t' (3n) = t' (2n)`,
`t' (3n+1) = t' (2n) + 1`, `t' (3n+2) = t' (2n)` (arXiv:2602.21895, Section 1.4). -/
def tDek : ℕ → ZMod 2
  | 0 => 0
  | m + 1 =>
    if (m + 1) % 3 = 1 then tDek (2 * ((m + 1) / 3)) + 1 else tDek (2 * ((m + 1) / 3))
decreasing_by all_goals omega

/-- Ground truth: the prefix `0100101011011010101011011` of `t'` printed in the paper. -/
example : (List.range 25).map tDek =
    [0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1] := by
  decide +kernel

/-- Ground truth: the first 60 terms of OEIS A357448. -/
example : (List.range 60).map tDek =
    [0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
     1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] := by
  decide +kernel

/-- `t' (3n) = t' (2n)`. -/
theorem tDek_three_mul (n : ℕ) : tDek (3 * n) = tDek (2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · obtain ⟨m, hm⟩ : ∃ m, 3 * n = m + 1 := ⟨3 * n - 1, by omega⟩
    rw [hm, tDek, if_neg (by omega)]
    congr 2
    omega

/-- `t' (3n+1) = t' (2n) + 1`. -/
theorem tDek_three_mul_add_one (n : ℕ) : tDek (3 * n + 1) = tDek (2 * n) + 1 := by
  rw [tDek, if_pos (by omega)]
  congr 3
  omega

/-- `t' (3n+2) = t' (2n)`. -/
theorem tDek_three_mul_add_two (n : ℕ) : tDek (3 * n + 2) = tDek (2 * n) := by
  rw [show 3 * n + 2 = (3 * n + 1) + 1 by ring, tDek, if_neg (by omega)]
  congr 2
  omega

/-- Lemma `lem:morphic_image` of arXiv:2602.21895: `t' = φ(t_{3/2})` with
`φ : 0 ↦ 010, 1 ↦ 101`, i.e. `t' (3n) = t (n)`, `t' (3n+1) = t (n) + 1`,
`t' (3n+2) = t (n)`. -/
theorem tDek_eq_phi_t32 (n : ℕ) :
    tDek (3 * n) = t32 n ∧ tDek (3 * n + 1) = t32 n + 1 ∧ tDek (3 * n + 2) = t32 n := by
  have hmain : ∀ n, tDek (3 * n) = t32 n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [mul_zero, t32_zero, tDek]
      rw [tDek_three_mul]
      obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, n = 3 * m ∨ n = 3 * m + 1 ∨ n = 3 * m + 2 :=
        ⟨n / 3, by omega⟩
      · rw [show 2 * (3 * m) = 3 * (2 * m) by ring, ih (2 * m) (by omega), t32_three_mul]
      · rw [show 2 * (3 * m + 1) = 3 * (2 * m) + 2 by ring, tDek_three_mul_add_two,
          ← tDek_three_mul, ih (2 * m) (by omega), t32_three_mul_add_one]
      · rw [show 2 * (3 * m + 2) = 3 * (2 * m + 1) + 1 by ring, tDek_three_mul_add_one,
          ← tDek_three_mul, ih (2 * m + 1) (by omega), t32_three_mul_add_two]
  refine ⟨hmain n, ?_, ?_⟩
  · rw [tDek_three_mul_add_one, ← tDek_three_mul, hmain]
  · rw [tDek_three_mul_add_two, ← tDek_three_mul, hmain]

/-- A prefix of `t'` of length `3q` contains `q + #01(t_{3/2}, q)` occurrences of `01`. -/
theorem count01_tDek_three_mul (q : ℕ) : count01 tDek (3 * q) = q + count01 t32 q := by
  have key : ∀ a b : ZMod 2,
      (if a = 0 ∧ a + 1 = 1 then 1 else 0 : ℕ) + (if a + 1 = 0 ∧ a = 1 then 1 else 0) +
        (if a = 0 ∧ b = 1 then 1 else 0) = 1 + (if a = 0 ∧ b = 1 then 1 else 0) := by
    decide
  simp only [count01, Finset.card_filter]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 2 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show 3 * q + 2 + 1 = 3 * (q + 1) by ring, show 3 * q + 1 + 1 = 3 * q + 2 by ring]
    obtain ⟨h0, h1, h2⟩ := tDek_eq_phi_t32 q
    obtain ⟨h0', -, -⟩ := tDek_eq_phi_t32 (q + 1)
    rw [h0, h1, h2, h0']
    have hk := key (t32 q) (t32 (q + 1))
    omega

/-- Counting a pattern over a further `k` positions adds at most `k` occurrences. -/
theorem count01_add_le (w : ℕ → ZMod 2) (a k : ℕ) :
    count01 w a ≤ count01 w (a + k) ∧ count01 w (a + k) ≤ count01 w a + k := by
  simp only [count01, Finset.card_filter]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_range_succ]
    have hle : (if w (a + k) = 0 ∧ w (a + k + 1) = 1 then 1 else 0 : ℕ) ≤ 1 := by
      split_ifs <;> omega
    omega

/-- **Frequency of `01` in Dekking's `t'`.** The proportion of `n < N` at which the factor
`01` occurs in `t'` (OEIS A357448) tends to `2/5`; this is the value conjectured by Dekking
and derived in arXiv:2602.21895 (concluding remarks) under the assumption that the
frequencies of `t_{3/2}` exist. -/
theorem tendsto_freq01_tDek :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => tDek n = 0 ∧ tDek (n + 1) = 1)).card : ℝ) / N)
      atTop (𝓝 (2 / 5)) := by
  have h := tendsto_freq_of_abs_le_log (count01 tDek) 10 4 (by norm_num) 45 (fun n => by
    set q := n / 3 with hq
    obtain ⟨hlo, hhi⟩ := count01_add_le tDek (3 * q) (n % 3)
    rw [show 3 * q + n % 3 = n by omega, count01_tDek_three_mul] at hlo hhi
    obtain ⟨h1, h2⟩ := count01_count10 t32 q
    rw [← flipCount_eq_card] at h1
    have hb := abs_disc_le_log q
    have hv : (t32 q).val < 2 := ZMod.val_lt _
    rw [t32_zero, ZMod.val_zero] at h2
    have hlog : Nat.log 2 q ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
    have hlogZ : ((Nat.log 2 q : ℕ) : ℤ) ≤ Nat.log 2 n := by exact_mod_cast hlog
    simp only [disc] at hb
    rw [abs_le] at hb ⊢
    push_cast at h2 ⊢
    constructor <;> omega)
  norm_num at h
  exact h

end BlockFrequenciesBaseThue
