/-
# A294425 — Kimberling: the coupled complementary recurrence has golden-ratio growth

## OEIS source (retrieved with `oeis show A294425` and the live `%`-format entry, 2026-10-21)

```
NAME:     Solution of the complementary equation
          a(n) = a(n-1) + a(n-2) + 2*b(n-1) - b(n-2) - 1,
          where a(0) = 1, a(1) = 3, b(0) = 2, b(1) = 4.
TERMS:    1,3,9,17,32,56,96,163,270,445,728,1187,1930,3133,5082,8234,13336,
          21591,34949,56563,91536,148124,239686,387837,627551,1015417,1642998,
          2658446,4301478,6959958,11261471,18221465,29482973,47704476,77187488,
          124892004,202079533
KEYWORDS: nonn,easy
AUTHOR:   _Clark Kimberling_, Nov 01 2017
COMMENT:  The complementary sequences a() and b() are uniquely determined by the
          titular equation and initial values.  See A294414 for a guide to
          related sequences.
COMMENT (the conjecture, entry author's, Nov 01 2017):
          Conjecture: a(n)/a(n-1) -> (1 + sqrt(5))/2, the golden ratio.
PROGRAM (Mathematica, the definition mirrored below):
  mex := First[Complement[Range[1, Max[#1] + 1], #1]] &;
  a[0] = 1; a[1] = 3; b[0] = 2; b[1] = 4;
  a[n_] := a[n] = a[n - 1] + a[n - 2] + 2*b[n - 1] - b[n - 2] - 1;
  b[n_] := b[n] = mex[Flatten[Table[Join[{a[n]}, {a[i], b[i]}], {i, 0, n - 1}]]];
```

## Status

Triage: open.  The entry and the A294414 guide state the limit as a
conjecture; the triage's web search found no proof.  The same conjecture
recurs in about 170 Kimberling complementary-equation entries.

This module proves it (`a294425_ratio_tendsto_goldenRatio`), through a
generic bridge (`tendsto_ratio_goldenRatio_of_linear_forcing`): a real
sequence that is Fibonacci up to a linearly bounded forcing term and grows at
least geometrically has consecutive ratios tending to the golden ratio.

## Definition layer

`mex l` is the least positive integer not in `l`, exactly the Mathematica
`mex`.  `hist n` stores `[a (n+1), …, a 0]` and `[b (n+1), …, b 0]`; one step
appends `a (n+2)` by the recurrence and then `b (n+2)` as the `mex` of
`a 0, …, a (n+2), b 0, …, b (n+1)`, as in the Mathematica program.  The
recurrence's `ℕ` subtraction never truncates (`a_add_two_cast`).
-/
import Mathlib

set_option autoImplicit false

open Filter Topology

namespace Candidates.A294425Recurrence

/-! ## Definitions -/

/-- `mexFrom f m l` scans `m, m+1, …` for at most `f` steps and returns the first value
not in `l` (or `m + f` if the fuel runs out). -/
def mexFrom : ℕ → ℕ → List ℕ → ℕ
  | 0, m, _ => m
  | f + 1, m, l => if m ∈ l then mexFrom f (m + 1) l else m

/-- The least positive integer not in `l` (the Mathematica `mex` of the entry);
the fuel `l.length + 1` suffices by `mex_not_mem`. -/
def mex (l : List ℕ) : ℕ := mexFrom (l.length + 1) 1 l

/-- `hist n = ([a (n+1), …, a 0], [b (n+1), …, b 0])`: the joint history of the
complementary pair, newest first. -/
def hist : ℕ → List ℕ × List ℕ
  | 0 => ([3, 1], [4, 2])
  | n + 1 =>
    let as := (hist n).1
    let bs := (hist n).2
    let a2 := as.headD 0 + as.tail.headD 0 + 2 * bs.headD 0 - bs.tail.headD 0 - 1
    (a2 :: as, mex (a2 :: as ++ bs) :: bs)

/-- A294425: `a 0 = 1`, `a 1 = 3`, `a n = a(n-1) + a(n-2) + 2 b(n-1) - b(n-2) - 1`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => (hist n).1.headD 0

/-- The complementary sequence: `b 0 = 2`, `b 1 = 4`, and for `n ≥ 2`, `b n` is the least
positive integer not among `a 0, …, a n, b 0, …, b (n-1)`. -/
def b : ℕ → ℕ
  | 0 => 2
  | n + 1 => (hist n).2.headD 0

/-! ## Ground truth: all 37 listed terms of A294425, and the first `b` values -/

example : (List.range 37).map a =
    [1, 3, 9, 17, 32, 56, 96, 163, 270, 445, 728, 1187, 1930, 3133, 5082, 8234, 13336, 21591,
      34949, 56563, 91536, 148124, 239686, 387837, 627551, 1015417, 1642998, 2658446, 4301478,
      6959958, 11261471, 18221465, 29482973, 47704476, 77187488, 124892004, 202079533] := by
  decide

example : (List.range 12).map b = [2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15] := by decide

/-! ## `mex` API -/

/-- Specification of the bounded upward scan `mexFrom`. -/
theorem mexFrom_spec (l : List ℕ) : ∀ (f m : ℕ),
    m ≤ mexFrom f m l ∧ mexFrom f m l ≤ m + f ∧
    (∀ k, m ≤ k → k < mexFrom f m l → k ∈ l) ∧
    (mexFrom f m l ∉ l ∨ mexFrom f m l = m + f) := by
  intro f
  induction f with
  | zero =>
    intro m
    refine ⟨le_rfl, Nat.le_add_right m 0, fun k h1 h2 => ?_, Or.inr rfl⟩
    rw [mexFrom] at h2
    omega
  | succ f ih =>
    intro m
    by_cases hm : m ∈ l
    · obtain ⟨h1, h2, h3, h4⟩ := ih (m + 1)
      rw [mexFrom, if_pos hm]
      refine ⟨by omega, by omega, fun k hk hk' => ?_, h4.imp id fun h => by omega⟩
      rcases Nat.eq_or_lt_of_le hk with rfl | hk
      · exact hm
      · exact h3 k hk hk'
    · rw [mexFrom, if_neg hm]
      exact ⟨le_rfl, by omega, fun k hk hk' => by omega, Or.inl hm⟩

/-- `mex l` is positive. -/
theorem one_le_mex (l : List ℕ) : 1 ≤ mex l := (mexFrom_spec l _ 1).1

/-- Pigeonhole: `mex l ≤ l.length + 1`. -/
theorem mex_le (l : List ℕ) : mex l ≤ l.length + 1 := by
  by_contra h
  obtain ⟨-, -, h3, -⟩ := mexFrom_spec l (l.length + 1) 1
  have hsub : Finset.Ico 1 (l.length + 2) ⊆ l.toFinset := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [List.mem_toFinset]
    exact h3 k hk.1 (by unfold mex at h; omega)
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have hlen := List.toFinset_card_le l
  omega

/-- Every positive integer below `mex l` lies in `l`. -/
theorem mem_of_lt_mex {l : List ℕ} {k : ℕ} (hk1 : 1 ≤ k) (hk : k < mex l) : k ∈ l :=
  (mexFrom_spec l _ 1).2.2.1 k hk1 hk

/-- `mex l` is not in `l`. -/
theorem mex_not_mem (l : List ℕ) : mex l ∉ l := by
  rcases (mexFrom_spec l (l.length + 1) 1).2.2.2 with h | h
  · exact h
  · have hle := mex_le l
    unfold mex at hle
    omega

/-- If `l ⊆ l'` and `mex l ∈ l'`, then `mex l < mex l'`. -/
theorem mex_lt_mex {l l' : List ℕ} (hsub : ∀ x ∈ l, x ∈ l') (hmem : mex l ∈ l') :
    mex l < mex l' := by
  by_contra h
  have hne : mex l' ≠ mex l := fun heq => mex_not_mem l' (heq ▸ hmem)
  have hlt : mex l' < mex l := lt_of_le_of_ne (not_lt.mp h) hne
  exact mex_not_mem l' (hsub _ (mem_of_lt_mex (one_le_mex l') hlt))

/-! ## The recurrences -/

/-- One step of the history extends the `a`-list by `a (n+2)`. -/
theorem hist_fst_succ (n : ℕ) : (hist (n + 1)).1 = a (n + 2) :: (hist n).1 := rfl

/-- One step of the history extends the `b`-list by `b (n+2)`. -/
theorem hist_snd_succ (n : ℕ) : (hist (n + 1)).2 = b (n + 2) :: (hist n).2 := rfl

/-- The second entry of the `a`-history `hist n` is `a n`. -/
theorem hist_fst_tail_headD (n : ℕ) : (hist n).1.tail.headD 0 = a n := by
  cases n with
  | zero => rfl
  | succ n => rw [hist_fst_succ]; rfl

/-- The second entry of the `b`-history `hist n` is `b n`. -/
theorem hist_snd_tail_headD (n : ℕ) : (hist n).2.tail.headD 0 = b n := by
  cases n with
  | zero => rfl
  | succ n => rw [hist_snd_succ]; rfl

/-- The defining recurrence of A294425 (in `ℕ`; see `a_add_two_cast` for the untruncated form). -/
theorem a_add_two (n : ℕ) : a (n + 2) = a (n + 1) + a n + 2 * b (n + 1) - b n - 1 := by
  rw [← hist_fst_tail_headD n, ← hist_snd_tail_headD n]
  rfl

/-- `b (n+2)` is the `mex` of `a 0, …, a (n+2), b 0, …, b (n+1)`. -/
theorem b_add_two (n : ℕ) : b (n + 2) = mex (a (n + 2) :: (hist n).1 ++ (hist n).2) := rfl

/-- Both histories in `hist n` have length `n + 2`. -/
theorem hist_length (n : ℕ) : (hist n).1.length = n + 2 ∧ (hist n).2.length = n + 2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [hist_fst_succ, hist_snd_succ, List.length_cons, List.length_cons, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- Linear bound: `b n ≤ 2n + 2`. -/
theorem b_le (n : ℕ) : b n ≤ 2 * n + 2 := by
  match n with
  | 0 => decide
  | 1 => decide
  | n + 2 =>
    rw [b_add_two]
    refine (mex_le _).trans ?_
    simp only [List.length_cons, List.length_append, (hist_length n).1, (hist_length n).2]
    omega

/-- `b` is strictly increasing. -/
theorem b_lt_succ (n : ℕ) : b n < b (n + 1) := by
  match n with
  | 0 => decide
  | 1 => decide
  | n + 2 =>
    rw [b_add_two (n + 1), b_add_two n, hist_fst_succ, hist_snd_succ]
    apply mex_lt_mex
    · intro x hx
      simp only [List.mem_cons, List.mem_append] at hx ⊢
      tauto
    · rw [← b_add_two]
      simp

/-- The recurrence holds over `ℝ` without truncation:
`a (n+2) - a (n+1) - a n = 2 b (n+1) - b n - 1`. -/
theorem a_add_two_cast (n : ℕ) :
    (a (n + 2) : ℝ) - a (n + 1) - a n = 2 * (b (n + 1) : ℝ) - b n - 1 := by
  have hb := b_lt_succ n
  have hrec := a_add_two n
  have hnat : a (n + 2) + b n + 1 = a (n + 1) + a n + 2 * b (n + 1) := by omega
  have hreal : (a (n + 2) : ℝ) + b n + 1 = a (n + 1) + a n + 2 * b (n + 1) := by
    exact_mod_cast hnat
  linarith

/-- The forcing term `a (n+2) - a (n+1) - a n` is linearly bounded. -/
theorem abs_forcing_le (n : ℕ) :
    |(a (n + 2) : ℝ) - a (n + 1) - a n| ≤ 8 * ((n : ℝ) + 1) := by
  rw [a_add_two_cast]
  have hb : (b n : ℝ) + 1 ≤ b (n + 1) := by exact_mod_cast b_lt_succ n
  have hb' : (b (n + 1) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) + 2 := by exact_mod_cast b_le (n + 1)
  have hb0 : (0 : ℝ) ≤ b n := Nat.cast_nonneg _
  push_cast at hb'
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Geometric growth: `φ ^ n ≤ a n`. -/
theorem goldenRatio_pow_le_a (n : ℕ) : Real.goldenRatio ^ n ≤ a n := by
  have key : ∀ n, Real.goldenRatio ^ n ≤ a n ∧ Real.goldenRatio ^ (n + 1) ≤ a (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [a], ?_⟩
      have h2 := Real.goldenRatio_lt_two
      have h3 : (a 1 : ℝ) = 3 := by norm_num [a, hist]
      rw [zero_add, pow_one, h3]
      linarith
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hb : (b n : ℝ) + 1 ≤ b (n + 1) := by exact_mod_cast b_lt_succ n
      have hb0 : (0 : ℝ) ≤ b n := Nat.cast_nonneg _
      have hrec := a_add_two_cast n
      have hpow : Real.goldenRatio ^ (n + 2) =
          Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
        rw [← Real.goldenRatio_pow_sub_goldenRatio_pow n]
        ring
      rw [show n + 1 + 1 = n + 2 by rfl, hpow]
      linarith [ih.1, ih.2]
  exact (key n).1

/-! ## Generic bridge: Fibonacci recurrence with linear forcing -/

/-- If `|a (n+2) - a (n+1) - a n| ≤ C (n+1)`, then `|a (n+1) - φ a n| ≤ K (n+1)` for some `K`.
Proof: `u n = a (n+1) - φ a n` satisfies `u (n+1) = ψ u n + (forcing)` with `|ψ| ≤ 2/3`. -/
theorem abs_sub_le_of_linear_forcing (a : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ n, |a (n + 2) - a (n + 1) - a n| ≤ C * (n + 1)) :
    ∃ K : ℝ, ∀ n, |a (n + 1) - Real.goldenRatio * a n| ≤ K * (n + 1) := by
  have hC : 0 ≤ C := by
    have h0 := hrec 0
    simp only [Nat.cast_zero, zero_add, mul_one] at h0
    exact (abs_nonneg _).trans h0
  have hψ : |Real.goldenConj| ≤ 2 / 3 := by
    rw [abs_of_neg Real.goldenConj_neg, ← Real.one_sub_goldenConj, neg_sub]
    have h1 := Real.goldenRatio_sq
    have h2 := Real.one_lt_goldenRatio
    nlinarith
  set K : ℝ := max |a 1 - Real.goldenRatio * a 0| (3 * C) with hK
  refine ⟨K, fun n => ?_⟩
  induction n with
  | zero => simp [hK]
  | succ n ih =>
    have hstep : a (n + 1 + 1) - Real.goldenRatio * a (n + 1) =
        Real.goldenConj * (a (n + 1) - Real.goldenRatio * a n) +
          (a (n + 2) - a (n + 1) - a n) := by
      have h1 : Real.goldenConj * Real.goldenRatio = -1 := Real.goldenConj_mul_goldenRatio
      have h2 : 1 - Real.goldenRatio = Real.goldenConj := Real.one_sub_goldenConj
      linear_combination (a n) * h1 + (a (n + 1)) * h2
    have hK3 : 3 * C ≤ K := le_max_right _ _
    have hn : (0 : ℝ) ≤ n + 1 := by positivity
    have hKn : 0 ≤ K * (n + 1) := (abs_nonneg _).trans ih
    rw [hstep]
    calc |Real.goldenConj * (a (n + 1) - Real.goldenRatio * a n) +
            (a (n + 2) - a (n + 1) - a n)|
        ≤ |Real.goldenConj| * |a (n + 1) - Real.goldenRatio * a n| + C * (n + 1) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
          exact add_le_add le_rfl (hrec n)
      _ ≤ 2 / 3 * (K * (n + 1)) + C * (n + 1) := by
          gcongr
      _ ≤ K * ((n + 1 : ℕ) + 1) := by
          push_cast
          nlinarith

/-- **Generic bridge.** A real sequence with `|a (n+2) - a (n+1) - a n| ≤ C (n+1)` and
`r ^ n ≤ a n` for some `r > 1` has `a (n+1) / a n → φ`. -/
theorem tendsto_ratio_goldenRatio_of_linear_forcing (a : ℕ → ℝ) (C r : ℝ) (hr : 1 < r)
    (hrec : ∀ n, |a (n + 2) - a (n + 1) - a n| ≤ C * (n + 1)) (hgrow : ∀ n, r ^ n ≤ a n) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 Real.goldenRatio) := by
  obtain ⟨K, hK⟩ := abs_sub_le_of_linear_forcing a C hrec
  have hrpos : ∀ n : ℕ, 0 < r ^ n := fun n => pow_pos (by linarith) n
  have hapos : ∀ n, 0 < a n := fun n => (hrpos n).trans_le (hgrow n)
  have hbound : Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h2 : Tendsto (fun n : ℕ => 1 / r ^ n) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hr)
    have h3 := (h1.add h2).const_mul K
    rw [add_zero, mul_zero] at h3
    refine h3.congr fun n => ?_
    rw [pow_one]
    field_simp
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun n => ?_) hbound
  have hK0 : 0 ≤ K * ((n : ℝ) + 1) := (abs_nonneg _).trans (hK n)
  have hrw : a (n + 1) / a n - Real.goldenRatio = (a (n + 1) - Real.goldenRatio * a n) / a n := by
    field_simp [(hapos n).ne']
  rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos (hapos n)]
  calc |a (n + 1) - Real.goldenRatio * a n| / a n ≤ K * ((n : ℝ) + 1) / a n :=
        div_le_div_of_nonneg_right (hK n) (hapos n).le
    _ ≤ K * ((n : ℝ) + 1) / r ^ n := div_le_div_of_nonneg_left hK0 (hrpos n) (hgrow n)

/-! ## The conjecture -/

/-- **Kimberling's conjecture for A294425 (Clark Kimberling, Nov 01 2017).**

Verbatim: "Conjecture: a(n)/a(n-1) -> (1 + sqrt(5))/2, the golden ratio."

Stated with the index shifted by one, `a (n+1) / a n → (1 + √5)/2`, which avoids `ℕ`
subtraction in the index and is the same limit statement.  Every `a n` is positive
(`goldenRatio_pow_le_a`), so the real division is never the junk `x / 0`. -/
theorem a294425_ratio_tendsto_goldenRatio :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 ((1 + √5) / 2)) :=
  tendsto_ratio_goldenRatio_of_linear_forcing (fun n => (a n : ℝ)) 8 Real.goldenRatio
    Real.one_lt_goldenRatio abs_forcing_le goldenRatio_pow_le_a

end Candidates.A294425Recurrence
