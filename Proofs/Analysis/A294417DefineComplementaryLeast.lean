/-
# A294417: golden-ratio growth for the joint mex recursion

OEIS A294417 (Clark Kimberling, 2017-10-31) describes complementary
sequences satisfying `a(n) = a(n-1)+a(n-2)+b(n-1)+b(n-2)-n`, with
`a(0)=1`, `a(1)=3`, `b(0)=2`, and `b(1)=4`. Its conjecture is
`a(n)/a(n-1) → (1+√5)/2`.

This file uses the entry's finite-prefix mex rule: `b(n)` is the least
positive integer absent from `a(0), …, a(n)` and `b(0), …, b(n-1)`.
`b_isLeast` proves that rule, and `conjecture_A294417` gives the ratio
limit for the explicit joint recursion. Global range complementarity and
uniqueness are not separate formal theorems here.

The bounds `n+2 ≤ b(n) ≤ 2n+2` control the forcing term and remove natural
subtraction truncation in the recurrence. With `φ = (1+√5)/2`, the error
`e(n) = a(n+1)-φa(n)` satisfies a contracting recurrence, giving
`|e(n)| ≤ 9(n+1)` and `|a(n+1)/a(n)-φ| ≤ 18/n` for `n ≥ 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A294417DefineComplementaryLeast

open Real Filter Topology

/-! ## The `mex` operator

The Mathematica `mex` returns the least positive integer not in its argument.
`mex` below computes it by a fuel-bounded upward search from `1`, so that the
examples can be evaluated by reduction; `mex_not_mem`, `one_le_mex` and
`mem_of_lt_mex` show it is exactly the least positive integer not in the list. -/

/-- Upward search: starting from `k`, return the first value not in `l`,
giving up (returning the current value) after `fuel` steps. -/
def mexAux (l : List ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | f + 1, k => if k ∈ l then mexAux l f (k + 1) else k

/-- The least positive integer not in `l` (fuel `l.length + 1` always suffices,
see `mex_not_mem`). -/
def mex (l : List ℕ) : ℕ := mexAux l (l.length + 1) 1

/-- Invariant of the upward search: the result is at least the start, every
value from the start up to the result is in `l`, and the result is either
absent from `l` or the search ran out of fuel. -/
theorem mexAux_spec (l : List ℕ) (f k : ℕ) :
    k ≤ mexAux l f k ∧ (∀ j, k ≤ j → j < mexAux l f k → j ∈ l) ∧
      (mexAux l f k ∉ l ∨ mexAux l f k = k + f) := by
  induction f generalizing k with
  | zero => exact ⟨le_rfl, fun j h1 h2 => by simp only [mexAux] at h2; omega, Or.inr rfl⟩
  | succ f ih =>
    by_cases hk : k ∈ l
    · obtain ⟨h1, h2, h3⟩ := ih (k + 1)
      simp only [mexAux, hk, if_true]
      refine ⟨by omega, fun j hj1 hj2 => ?_, h3.imp id (fun h => by omega)⟩
      rcases Nat.eq_or_lt_of_le hj1 with hj | hj
      · exact hj ▸ hk
      · exact h2 j hj hj2
    · rw [mexAux, if_neg hk]
      exact ⟨le_rfl, fun j h1 h2 => by omega, Or.inl hk⟩

/-- `mex l` is positive. -/
theorem one_le_mex (l : List ℕ) : 1 ≤ mex l := (mexAux_spec l _ 1).1

/-- Every positive integer below `mex l` lies in `l`. -/
theorem mem_of_lt_mex (l : List ℕ) {j : ℕ} (hj : 0 < j) (hlt : j < mex l) : j ∈ l :=
  (mexAux_spec l _ 1).2.1 j hj hlt

/-- Pigeonhole: `mex l ≤ l.length + 1`. -/
theorem mex_le_length_add_one (l : List ℕ) : mex l ≤ l.length + 1 := by
  have hsub : Finset.Ico 1 (mex l) ⊆ l.toFinset := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact List.mem_toFinset.mpr (mem_of_lt_mex l (by omega) hj.2)
  have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le l)
  rw [Nat.card_Ico] at hcard
  omega

/-- `mex l` is not in `l` (the fuel never runs out). -/
theorem mex_not_mem (l : List ℕ) : mex l ∉ l := by
  rcases (mexAux_spec l _ 1).2.2 with h | h
  · exact h
  · have hle := mex_le_length_add_one l
    unfold mex at hle
    omega

/-- `mex l` is the least positive integer not in `l`. -/
theorem mex_isLeast (l : List ℕ) : IsLeast {k : ℕ | 0 < k ∧ k ∉ l} (mex l) :=
  ⟨⟨one_le_mex l, mex_not_mem l⟩, fun k hk => by
    by_contra hlt
    rw [not_le] at hlt
    exact hk.2 (mem_of_lt_mex l hk.1 hlt)⟩

/-- `mex` is monotone under list inclusion. -/
theorem mex_mono {l l' : List ℕ} (h : l ⊆ l') : mex l ≤ mex l' := by
  by_contra hlt
  rw [not_le] at hlt
  exact mex_not_mem l' (h (mem_of_lt_mex l (one_le_mex l') hlt))

example : mex [1, 2, 3, 5] = 4 := by decide
example : mex [] = 1 := by decide

/-! ## The sequences `a` (A294417) and `b`

`state n = ((a n, b n), (a (n+1), b (n+1)), used)` where `used` lists every
`a i` and `b i` with `i ≤ n + 1`.  One `step` computes
`a (n+2) = a(n+1) + a n + b(n+1) + b n - (n+2)` and then
`b (n+2) = mex (a (n+2) :: used)`, exactly as in the entry's Mathematica
program.  The natural-number subtraction never truncates
(`a_add_two_add`), and `b` is the least positive integer not yet used
(`b_isLeast`). -/

/-- One step of the joint recursion (see the section comment). -/
def step (n : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ) × List ℕ) : (ℕ × ℕ) × (ℕ × ℕ) × List ℕ :=
  let a2 := s.2.1.1 + s.1.1 + s.2.1.2 + s.1.2 - (n + 2)
  let b2 := mex (a2 :: s.2.2)
  (s.2.1, (a2, b2), b2 :: a2 :: s.2.2)

/-- The state `((a n, b n), (a (n+1), b (n+1)), used values)`. -/
def state : ℕ → (ℕ × ℕ) × (ℕ × ℕ) × List ℕ
  | 0 => ((1, 2), (3, 4), [4, 3, 2, 1])
  | n + 1 => step n (state n)

/-- A294417: `a 0 = 1`, `a 1 = 3`,
`a n = a(n-1) + a(n-2) + b(n-1) + b(n-2) - n`. -/
def a (n : ℕ) : ℕ := (state n).1.1

/-- The complement `b`: `b 0 = 2`, `b 1 = 4`, and `b n` is the least positive
integer not among `a 0, …, a n, b 0, …, b (n-1)`. -/
def b (n : ℕ) : ℕ := (state n).1.2

/-- The values used before `b (n+2)` is chosen, apart from `a (n+2)`:
all `a i`, `b i` with `i ≤ n + 1`. -/
def used (n : ℕ) : List ℕ := (state n).2.2

example : (List.range 36).map a =
    [1, 3, 8, 17, 32, 57, 99, 168, 280, 462, 757, 1235, 2009, 3262, 5291, 8575, 13889,
      22488, 36402, 58916, 95345, 154289, 249663, 403982, 653676, 1057690, 1711399,
      2769123, 4480558, 7249719, 11730316, 18980075, 30710432, 49690549, 80401024,
      130091617] := by decide
example : (List.range 12).map b = [2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15] := by decide

/-- The recurrence as computed (natural-number subtraction; see `a_add_two_add`). -/
theorem a_add_two (n : ℕ) : a (n + 2) = a (n + 1) + a n + b (n + 1) + b n - (n + 2) := rfl

/-- `b (n+2)` is the `mex` of `a (n+2)` and all earlier values. -/
theorem b_add_two (n : ℕ) : b (n + 2) = mex (a (n + 2) :: used n) := rfl

/-- The initial used list. -/
theorem used_zero : used 0 = [b 1, a 1, b 0, a 0] := rfl

/-- The used list grows by `a (n+2)` and `b (n+2)`. -/
theorem used_succ (n : ℕ) : used (n + 1) = b (n + 2) :: a (n + 2) :: used n := rfl

/-- `used n` consists exactly of the `a i`, `b i` with `i ≤ n + 1`. -/
theorem mem_used (n x : ℕ) : x ∈ used n ↔ ∃ i ≤ n + 1, a i = x ∨ b i = x := by
  induction n with
  | zero =>
    rw [used_zero]
    constructor
    · intro hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h
      · exact ⟨1, le_rfl, Or.inr h.symm⟩
      · exact ⟨1, le_rfl, Or.inl h.symm⟩
      · exact ⟨0, Nat.zero_le _, Or.inr h.symm⟩
      · exact ⟨0, Nat.zero_le _, Or.inl h.symm⟩
    · rintro ⟨i, hi, h⟩
      interval_cases i <;> rcases h with h | h <;> simp [h]
  | succ n ih =>
    rw [used_succ, List.mem_cons, List.mem_cons, ih]
    constructor
    · rintro (h | h | ⟨i, hi, h⟩)
      · exact ⟨n + 2, le_rfl, Or.inr h.symm⟩
      · exact ⟨n + 2, le_rfl, Or.inl h.symm⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · rcases h with h | h
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨i, by omega, h⟩)

/-- `used n` has `2n + 4` entries. -/
theorem length_used (n : ℕ) : (used n).length = 2 * n + 4 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [used_succ, List.length_cons, List.length_cons, ih]; ring

/-- `b n` is the least positive integer different from
`a 0, …, a n` and `b 0, …, b (n-1)` (for `n = 0, 1` this checks the given
initial values `b 0 = 2`, `b 1 = 4`). -/
theorem b_isLeast (n : ℕ) :
    IsLeast {k : ℕ | 0 < k ∧ (∀ i ≤ n, a i ≠ k) ∧ ∀ i < n, b i ≠ k} (b n) := by
  rcases n with _ | _ | n
  · refine ⟨⟨by decide, fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
      fun k hk => ?_⟩
    · obtain rfl : i = 0 := by omega
      decide
    · have h0 : a 0 ≠ k := hk.2.1 0 le_rfl
      have hk0 : 0 < k := hk.1
      change 1 ≠ k at h0
      change 2 ≤ k
      omega
  · refine ⟨⟨by decide, fun i hi => ?_, fun i hi => ?_⟩, fun k hk => ?_⟩
    · interval_cases i <;> decide
    · interval_cases i; decide
    · have h0 : a 0 ≠ k := hk.2.1 0 (Nat.zero_le _)
      have h1 : a 1 ≠ k := hk.2.1 1 le_rfl
      have h2 : b 0 ≠ k := hk.2.2 0 Nat.one_pos
      have hk0 : 0 < k := hk.1
      change 1 ≠ k at h0
      change 3 ≠ k at h1
      change 2 ≠ k at h2
      change 4 ≤ k
      omega
  · have hmem : ∀ x, x ∈ a (n + 2) :: used n ↔
        (∃ i ≤ n + 2, a i = x) ∨ ∃ i < n + 2, b i = x := by
      intro x
      rw [List.mem_cons, mem_used]
      constructor
      · rintro (h | ⟨i, hi, h | h⟩)
        · exact Or.inl ⟨n + 2, le_rfl, h.symm⟩
        · exact Or.inl ⟨i, by omega, h⟩
        · exact Or.inr ⟨i, by omega, h⟩
      · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
        · rcases Nat.eq_or_lt_of_le hi with rfl | hlt
          · exact Or.inl h.symm
          · exact Or.inr ⟨i, by omega, Or.inl h⟩
        · exact Or.inr ⟨i, by omega, Or.inr h⟩
    have hset : {k : ℕ | 0 < k ∧ (∀ i ≤ n + 2, a i ≠ k) ∧ ∀ i < n + 2, b i ≠ k} =
        {k : ℕ | 0 < k ∧ k ∉ a (n + 2) :: used n} := by
      ext k
      simp only [Set.mem_ofPred_eq, hmem k, not_or, not_exists, not_and]
    rw [hset, b_add_two]
    exact mex_isLeast _

/-! ## Elementary growth bounds -/

/-- `b` increases at every step. -/
theorem b_lt_b_succ (n : ℕ) : b n < b (n + 1) := by
  rcases n with _ | _ | n
  · decide
  · decide
  · have hne : b (n + 3) ≠ b (n + 2) := by
      intro h
      apply mex_not_mem (a (n + 3) :: used (n + 1))
      rw [← b_add_two, h, used_succ]
      simp
    have hle : b (n + 2) ≤ b (n + 3) := by
      rw [b_add_two, b_add_two, used_succ]
      apply mex_mono
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      tauto
    show b (n + 2) < b (n + 3)
    omega

/-- `b` is strictly increasing. -/
theorem b_strictMono : StrictMono b := strictMono_nat_of_lt_succ b_lt_b_succ

/-- Lower bound `n + 2 ≤ b n`. -/
theorem add_two_le_b (n : ℕ) : n + 2 ≤ b n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hlt := b_lt_b_succ n
    omega

/-- Upper bound `b n ≤ 2n + 2` (pigeonhole on the used values). -/
theorem b_le (n : ℕ) : b n ≤ 2 * n + 2 := by
  rcases n with _ | _ | n
  · decide
  · decide
  · rw [b_add_two]
    have h := mex_le_length_add_one (a (n + 2) :: used n)
    rw [List.length_cons, length_used] at h
    omega

/-- The defining recurrence without truncation:
`a (n+2) + (n+2) = a (n+1) + a n + b (n+1) + b n`. -/
theorem a_add_two_add (n : ℕ) : a (n + 2) + (n + 2) = a (n + 1) + a n + b (n + 1) + b n := by
  have h1 := add_two_le_b n
  rw [a_add_two]
  omega

/-- Quadratic lower bound `n² ≤ a n`. -/
theorem sq_le_a (n : ℕ) : n ^ 2 ≤ a n := by
  have key : ∀ m, (m + 3) ^ 2 ≤ a (m + 3) ∧ (m + 4) ^ 2 ≤ a (m + 4) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have h : a (m + 5) + (m + 5) = a (m + 4) + a (m + 3) + b (m + 4) + b (m + 3) :=
        a_add_two_add (m + 3)
      have hb := add_two_le_b (m + 4)
      have hrec : a (m + 4) + a (m + 3) ≤ a (m + 5) := by omega
      have h1 := ih.1
      have h2 := ih.2
      show (m + 5) ^ 2 ≤ a (m + 5)
      nlinarith
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · exact (key n).1

/-- `a n` is positive, so the ratio `a (n+1) / a n` is never a division by zero. -/
theorem a_pos (n : ℕ) : 0 < a n := by
  rcases n with _ | n
  · decide
  · have hsq := sq_le_a (n + 1)
    have hpos : 0 < (n + 1) ^ 2 := by positivity
    omega

/-! ## The error term `a (n+1) - φ a n` -/

/-- The error `a (n+1) - φ · a n`. -/
noncomputable def err (n : ℕ) : ℝ := (a (n + 1) : ℝ) - goldenRatio * a n

/-- `φ < 5/3`, so `|1 - φ| ≤ 2/3`. -/
theorem goldenRatio_lt_five_thirds : goldenRatio < 5 / 3 := by
  have hs : √5 < 7 / 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [goldenRatio]
  linarith

/-- The error recursion `e (n+1) = (1 - φ) e n + (b (n+1) + b n - (n+2))`. -/
theorem err_succ (n : ℕ) :
    err (n + 1) = (1 - goldenRatio) * err n + ((b (n + 1) : ℝ) + b n - (n + 2)) := by
  have h : (a (n + 2) : ℝ) + (n + 2) = a (n + 1) + a n + b (n + 1) + b n := by
    exact_mod_cast a_add_two_add n
  have hsq := Real.goldenRatio_sq
  unfold err
  linear_combination h - (a n : ℝ) * hsq

/-- Linear bound on the error: `|e n| ≤ 9 (n + 1)`. -/
theorem abs_err_le (n : ℕ) : |err n| ≤ 9 * ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    have h1 := Real.one_lt_goldenRatio
    have h2 := Real.goldenRatio_lt_two
    have h0 : err 0 = 3 - goldenRatio := by
      simp only [err]
      norm_num [show a 1 = 3 from rfl, show a 0 = 1 from rfl]
    rw [h0, abs_le]
    constructor <;> push_cast <;> linarith
  | succ n ih =>
    have h1 := Real.one_lt_goldenRatio
    have h2 := goldenRatio_lt_five_thirds
    have hb1 : (b (n + 1) : ℝ) ≤ 2 * (n + 1) + 2 := by exact_mod_cast b_le (n + 1)
    have hb0 : (b n : ℝ) ≤ 2 * n + 2 := by exact_mod_cast b_le n
    have hbl : (n : ℝ) + 2 ≤ b n := by exact_mod_cast add_two_le_b n
    have hbl1 : 0 ≤ (b (n + 1) : ℝ) := Nat.cast_nonneg _
    have hc : |1 - goldenRatio| ≤ 2 / 3 := by
      rw [abs_le]; constructor <;> linarith
    have hmul : |(1 - goldenRatio) * err n| ≤ 2 / 3 * (9 * ((n : ℝ) + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hc ih (abs_nonneg _) (by norm_num)
    have hF : |(b (n + 1) : ℝ) + b n - (n + 2)| ≤ 3 * (n : ℝ) + 4 := by
      rw [abs_le]; constructor <;> linarith
    rw [err_succ]
    calc |(1 - goldenRatio) * err n + ((b (n + 1) : ℝ) + b n - (n + 2))|
        ≤ |(1 - goldenRatio) * err n| + |(b (n + 1) : ℝ) + b n - (n + 2)| := abs_add_le _ _
      _ ≤ 2 / 3 * (9 * ((n : ℝ) + 1)) + (3 * (n : ℝ) + 4) := add_le_add hmul hF
      _ ≤ 9 * (((n + 1 : ℕ) : ℝ) + 1) := by push_cast; linarith

/-- `a (n+1) / a n - φ = e n / a n`. -/
theorem ratio_sub_goldenRatio (n : ℕ) :
    (a (n + 1) : ℝ) / a n - goldenRatio = err n / a n := by
  have hpos : (0 : ℝ) < a n := by exact_mod_cast a_pos n
  unfold err
  field_simp

/-- Quantitative convergence: `|a (n+1) / a n - φ| ≤ 18 / n` for `1 ≤ n`. -/
theorem abs_ratio_sub_le (n : ℕ) (hn : 1 ≤ n) :
    |(a (n + 1) : ℝ) / a n - goldenRatio| ≤ 18 / n := by
  have hpos : (0 : ℝ) < a n := by exact_mod_cast a_pos n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (n : ℝ) ^ 2 ≤ a n := by exact_mod_cast sq_le_a n
  have he := abs_err_le n
  rw [ratio_sub_goldenRatio, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by linarith)]
  calc |err n| * n ≤ 9 * ((n : ℝ) + 1) * n := by gcongr
    _ ≤ 18 * (n : ℝ) ^ 2 := by nlinarith
    _ ≤ 18 * a n := by gcongr

/-! ## The conjecture -/

/-- The ratio limit in Kimberling's conjecture (OEIS A294417, 2017-10-31),
for the explicit joint mex recursion, with the index shifted by one:
`a(n+1)/a(n) → (1+√5)/2`. Positivity of every denominator is `a_pos`;
`abs_ratio_sub_le` bounds the error by `18/n` for `n ≥ 1`. -/
theorem conjecture_A294417 :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 ((1 + √5) / 2)) := by
  rw [← goldenRatio, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat 18)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  exact abs_ratio_sub_le n hn

end Candidates.A294417DefineComplementaryLeast
