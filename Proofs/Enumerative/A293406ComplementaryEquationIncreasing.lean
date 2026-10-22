/-
# A complementary sequence with limiting ratio φ (A293406)

Source: Clark Kimberling's OEIS A293406 entry (Oct 29 2017), using its
Mathematica mex program. The initial values are `a(0)=1`, `a(1)=3`,
`b(0)=2`, `b(1)=4`; the recurrence is `a(n)=a(n-1)+a(n-2)+b(n-1)+1`.
The complement's least-unused-value property is proved.
The positive sequence satisfies `a(n+1)/a(n) → φ`, with error at most
`12/(n+1)`. The proof bounds `b(n)` linearly and `a(n)` quadratically,
then applies the contracting recurrence for `a(n+1)-φ a(n)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A293406ComplementaryEquationIncreasing

/-- Bounded search for the least `k' ≥ k` not in `l`, giving up after `fuel` steps
(returning `k + fuel` in that case). -/
def mexAux (l : List ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k => if k ∈ l then mexAux l fuel (k + 1) else k

/-- The least positive integer not in `l` (Mathematica `mex` of the entry);
`mex_not_mem`, `mex_pos` and `mem_of_lt_mex` prove it is exactly that. -/
def mex (l : List ℕ) : ℕ := mexAux l l.length 1

/-- The joint state after step `n`: `(a n, a (n+1), b (n+1), L)` where `L` lists
`a 0, …, a (n+1)` and `b 0, …, b (n+1)`. -/
def st : ℕ → ℕ × ℕ × ℕ × List ℕ
  | 0 => (1, 3, 4, [4, 3, 2, 1])
  | n + 1 =>
    let s := st n
    let a' := s.2.1 + s.1 + s.2.2.1 + 1
    let b' := mex (a' :: s.2.2.2)
    (s.2.1, a', b', b' :: a' :: s.2.2.2)

/-- A293406: `a(0) = 1, a(1) = 3`, `a(n) = a(n-1) + a(n-2) + b(n-1) + 1`. -/
def a (n : ℕ) : ℕ := (st n).1

/-- The complement `b`: `b(0) = 2, b(1) = 4`, and `b(n)` is the least positive
integer not among `a(0..n), b(0..n-1)`. -/
def b : ℕ → ℕ
  | 0 => 2
  | n + 1 => (st n).2.2.1

/-- The first 20 listed terms of A293406. -/
example : (List.range 20).map a =
    [1, 3, 9, 18, 34, 60, 103, 174, 289, 476, 779, 1270, 2065, 3352, 5435, 8807, 14263,
      23092, 37378, 60494] := by decide

/-- The first 12 terms of the complement `b` (Mathematica program). -/
example : (List.range 12).map b = [2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15] := by decide


/-! ## The bounded `mex` search -/

/-- The bounded search returns at most `k + fuel`. -/
theorem mexAux_le (l : List ℕ) : ∀ (fuel k : ℕ), mexAux l fuel k ≤ k + fuel
  | 0, k => by simp [mexAux]
  | fuel + 1, k => by
    unfold mexAux
    split_ifs
    · have h := mexAux_le l fuel (k + 1)
      omega
    · omega

/-- The bounded search returns at least its starting point `k`. -/
theorem le_mexAux (l : List ℕ) : ∀ (fuel k : ℕ), k ≤ mexAux l fuel k
  | 0, k => by simp [mexAux]
  | fuel + 1, k => by
    unfold mexAux
    split_ifs
    · have h := le_mexAux l fuel (k + 1)
      omega
    · exact le_rfl

/-- Every `j` with `k ≤ j` below the search result lies in `l`. -/
theorem mem_of_lt_mexAux (l : List ℕ) :
    ∀ (fuel k j : ℕ), k ≤ j → j < mexAux l fuel k → j ∈ l
  | 0, k, j, hkj, hj => by simp only [mexAux] at hj; omega
  | fuel + 1, k, j, hkj, hj => by
    unfold mexAux at hj
    split_ifs at hj with hk
    · rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
      · exact hk
      · exact mem_of_lt_mexAux l fuel (k + 1) j hlt hj
    · omega

/-- If the search result lies in `l`, the fuel was exhausted. -/
theorem mexAux_eq_of_mem (l : List ℕ) :
    ∀ (fuel k : ℕ), mexAux l fuel k ∈ l → mexAux l fuel k = k + fuel
  | 0, k, _ => by simp [mexAux]
  | fuel + 1, k, h => by
    unfold mexAux at h ⊢
    split_ifs at h ⊢ with hk
    · have := mexAux_eq_of_mem l fuel (k + 1) h
      omega
    · exact absurd h hk


/-- `mex l` is positive. -/
theorem mex_pos (l : List ℕ) : 0 < mex l := le_mexAux l l.length 1

/-- Pigeonhole bound: `mex l ≤ l.length + 1`. -/
theorem mex_le (l : List ℕ) : mex l ≤ l.length + 1 := by
  have h := mexAux_le l l.length 1
  rw [mex]
  omega

/-- Every positive integer below `mex l` lies in `l`. -/
theorem mem_of_lt_mex (l : List ℕ) (j : ℕ) (hj0 : 0 < j) (hj : j < mex l) : j ∈ l :=
  mem_of_lt_mexAux l l.length 1 j hj0 hj

/-- `mex l` is not in `l` (pigeonhole). -/
theorem mex_not_mem (l : List ℕ) : mex l ∉ l := by
  intro hmem
  have heq : mex l = 1 + l.length := mexAux_eq_of_mem l l.length 1 hmem
  have hsub : Finset.Icc 1 (l.length + 1) ⊆ l.toFinset := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [List.mem_toFinset]
    rcases Nat.eq_or_lt_of_le hj.2 with hjeq | hjlt
    · rw [hjeq, add_comm, ← heq]
      exact hmem
    · exact mem_of_lt_mex l j hj.1 (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have := List.toFinset_card_le l
  omega


/-! ## Unfolding the state -/

/-- `a (n + 1)` is the second component of the state at step `n`. -/
theorem a_succ (n : ℕ) : a (n + 1) = (st n).2.1 := rfl

/-- `b (n + 1)` is the third component of the state at step `n`. -/
theorem b_succ (n : ℕ) : b (n + 1) = (st n).2.2.1 := rfl

/-- Initial value `a(0) = 1`. -/
theorem a_zero : a 0 = 1 := rfl

/-- Initial value `a(1) = 3`. -/
theorem a_one : a 1 = 3 := rfl

/-- Initial value `b(0) = 2`. -/
theorem b_zero : b 0 = 2 := rfl

/-- Initial value `b(1) = 4`. -/
theorem b_one : b 1 = 4 := rfl

/-- The defining recurrence `a(n) = a(n-1) + a(n-2) + b(n-1) + 1`, for `n + 2`. -/
theorem a_add_two (n : ℕ) : a (n + 2) = a (n + 1) + a n + b (n + 1) + 1 := rfl

/-- The recorded list after step `n` has `2n + 4` entries. -/
theorem st_length (n : ℕ) : (st n).2.2.2.length = 2 * n + 4 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (_ :: _ :: (st n).2.2.2).length = _
    simp only [List.length_cons, ih]
    ring

/-- The recorded list after step `n` holds exactly `a 0..a (n+1)` and `b 0..b (n+1)`. -/
theorem mem_st_iff (n x : ℕ) :
    x ∈ (st n).2.2.2 ↔ ∃ i ≤ n + 1, a i = x ∨ b i = x := by
  induction n with
  | zero =>
    change x ∈ [4, 3, 2, 1] ↔ _
    constructor
    · intro hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, le_rfl, Or.inr rfl⟩
      · exact ⟨1, le_rfl, Or.inl rfl⟩
      · exact ⟨0, Nat.zero_le 1, Or.inr rfl⟩
      · exact ⟨0, Nat.zero_le 1, Or.inl rfl⟩
    · rintro ⟨i, hi, h⟩
      interval_cases i <;> rcases h with rfl | rfl <;> decide
  | succ n ih =>
    change x ∈ b (n + 2) :: a (n + 2) :: (st n).2.2.2 ↔ _
    rw [List.mem_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | rfl | ⟨i, hi, h⟩)
      · exact ⟨n + 2, le_rfl, Or.inr rfl⟩
      · exact ⟨n + 2, le_rfl, Or.inl rfl⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · rcases h with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨i, by omega, h⟩)

/-- `b (n + 2)` is the `mex` of `a (n + 2)` together with the recorded list. -/
theorem b_add_two (n : ℕ) : b (n + 2) = mex (a (n + 2) :: (st n).2.2.2) := rfl


/-- Fidelity of `b` to the entry: `b n` is the least positive integer different from
`a 0, …, a n` and `b 0, …, b (n-1)` (for `n = 0, 1` this agrees with the given initial
values `b(0) = 2`, `b(1) = 4`). -/
theorem b_isLeast (n : ℕ) :
    IsLeast {k : ℕ | 0 < k ∧ (∀ i ≤ n, a i ≠ k) ∧ ∀ i < n, b i ≠ k} (b n) := by
  match n with
  | 0 =>
    refine ⟨⟨by decide, fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, ?_⟩
    · obtain rfl : i = 0 := by omega
      decide
    · rintro k ⟨hk0, hka, -⟩
      have h1 := hka 0 le_rfl
      rw [a_zero] at h1
      rw [b_zero]
      omega
  | 1 =>
    refine ⟨⟨by decide, fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · interval_cases i <;> decide
    · obtain rfl : i = 0 := by omega
      decide
    · rintro k ⟨hk0, hka, hkb⟩
      have h0 := hka 0 (by omega)
      have h1 := hka 1 le_rfl
      have h2 := hkb 0 (by omega)
      rw [a_zero] at h0
      rw [a_one] at h1
      rw [b_zero] at h2
      rw [b_one]
      omega
  | n + 2 =>
    have hmem : ∀ x, x ∈ a (n + 2) :: (st n).2.2.2 ↔
        (∃ i ≤ n + 2, a i = x) ∨ ∃ i < n + 2, b i = x := by
      intro x
      rw [List.mem_cons, mem_st_iff]
      constructor
      · rintro (rfl | ⟨i, hi, h | h⟩)
        · exact Or.inl ⟨n + 2, le_rfl, rfl⟩
        · exact Or.inl ⟨i, by omega, h⟩
        · exact Or.inr ⟨i, by omega, h⟩
      · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
        · rcases Nat.eq_or_lt_of_le hi with rfl | hlt
          · exact Or.inl h.symm
          · exact Or.inr ⟨i, by omega, Or.inl h⟩
        · exact Or.inr ⟨i, by omega, Or.inr h⟩
    rw [b_add_two]
    refine ⟨⟨mex_pos _, fun i hi h => ?_, fun i hi h => ?_⟩, ?_⟩
    · exact mex_not_mem _ ((hmem _).2 (Or.inl ⟨i, hi, h⟩))
    · exact mex_not_mem _ ((hmem _).2 (Or.inr ⟨i, hi, h⟩))
    · rintro k ⟨hk0, hka, hkb⟩
      by_contra hlt
      rw [not_le] at hlt
      rcases (hmem k).1 (mem_of_lt_mex _ k hk0 hlt) with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
      · exact hka i hi h
      · exact hkb i hi h


/-! ## Growth estimates -/

/-- Pigeonhole bound on the complement: `b n ≤ 2n + 2`. -/
theorem b_le (n : ℕ) : b n ≤ 2 * n + 2 := by
  match n with
  | 0 => decide
  | 1 => decide
  | n + 2 =>
    rw [b_add_two]
    have h := mex_le (a (n + 2) :: (st n).2.2.2)
    rw [List.length_cons, st_length] at h
    omega

/-- Quadratic lower bound `(n + 1)^2 ≤ 2 a(n)`. -/
theorem sq_le_two_mul_a (n : ℕ) : (n + 1) ^ 2 ≤ 2 * a n := by
  suffices h : (n + 1) ^ 2 ≤ 2 * a n ∧ (n + 2) ^ 2 ≤ 2 * a (n + 1) from h.1
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hrec := a_add_two n
    have hb : 0 < b (n + 1) := (b_isLeast (n + 1)).1.1
    obtain ⟨h1, h2⟩ := ih
    rw [hrec]
    nlinarith

/-- `|ψ| < 2/3` for the golden conjugate. -/
theorem abs_goldenConj_lt : |Real.goldenConj| < 2 / 3 := by
  have hs : √5 < 7 / 3 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hneg : Real.goldenConj < 0 := Real.goldenConj_neg
  rw [abs_of_neg hneg, Real.goldenConj]
  linarith

/-- The error `e n = a(n+1) - φ a(n)` satisfies `e (n+1) = ψ e n + b(n+1) + 1`. -/
theorem err_succ (n : ℕ) :
    (a (n + 2) : ℝ) - Real.goldenRatio * a (n + 1) =
      Real.goldenConj * ((a (n + 1) : ℝ) - Real.goldenRatio * a n) + ((b (n + 1) : ℝ) + 1) := by
  have hrec : (a (n + 2) : ℝ) = a (n + 1) + a n + b (n + 1) + 1 := by
    rw [a_add_two]
    push_cast
    ring
  have hsum : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
  have hprod : Real.goldenConj * Real.goldenRatio = -1 := Real.goldenConj_mul_goldenRatio
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [hrec]
  linear_combination (-(a (n + 1) : ℝ)) * hsum - (a n : ℝ) * hprod - ((a n : ℝ) / 2) * h5

/-- Linear bound on the error: `|a(n+1) - φ a(n)| ≤ 6 (n + 1)`. -/
theorem abs_err_le (n : ℕ) :
    |(a (n + 1) : ℝ) - Real.goldenRatio * a n| ≤ 6 * ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    have h1 := Real.one_lt_goldenRatio
    have h2 := Real.goldenRatio_lt_two
    rw [a_one, a_zero, abs_le]
    push_cast
    constructor <;> linarith
  | succ n ih =>
    rw [err_succ]
    have hb : (b (n + 1) : ℝ) ≤ 2 * ((n : ℝ) + 1) + 2 := by
      have := b_le (n + 1)
      exact_mod_cast this
    have hb0 : (0 : ℝ) ≤ b (n + 1) := Nat.cast_nonneg _
    have hψ := abs_goldenConj_lt
    have hmul : |Real.goldenConj * ((a (n + 1) : ℝ) - Real.goldenRatio * a n)| ≤
        2 / 3 * (6 * ((n : ℝ) + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hψ.le ih (abs_nonneg _) (by norm_num)
    calc |Real.goldenConj * ((a (n + 1) : ℝ) - Real.goldenRatio * a n) + ((b (n + 1) : ℝ) + 1)|
        ≤ |Real.goldenConj * ((a (n + 1) : ℝ) - Real.goldenRatio * a n)| +
            |(b (n + 1) : ℝ) + 1| := abs_add_le _ _
      _ ≤ 2 / 3 * (6 * ((n : ℝ) + 1)) + (2 * ((n : ℝ) + 1) + 3) := by
          rw [abs_of_nonneg (show (0 : ℝ) ≤ (b (n + 1) : ℝ) + 1 by linarith)]
          linarith
      _ ≤ 6 * (((n + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          linarith


/-- `a n` is positive. -/
theorem a_pos (n : ℕ) : 0 < a n := by
  have h := sq_le_two_mul_a n
  have : 0 < (n + 1) ^ 2 := by positivity
  omega

/-- Quantitative form: `|a(n+1)/a(n) - φ| ≤ 12 / (n + 1)`. -/
theorem abs_ratio_sub_le (n : ℕ) :
    |(a (n + 1) : ℝ) / a n - Real.goldenRatio| ≤ 12 / ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < a n := by exact_mod_cast a_pos n
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ 2 * a n := by exact_mod_cast sq_le_two_mul_a n
  have herr := abs_err_le n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have heq : (a (n + 1) : ℝ) / a n - Real.goldenRatio =
      ((a (n + 1) : ℝ) - Real.goldenRatio * a n) / a n := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hn]
  calc |(a (n + 1) : ℝ) - Real.goldenRatio * a n| * ((n : ℝ) + 1)
      ≤ 6 * ((n : ℝ) + 1) * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right herr hn.le
    _ = 6 * ((n : ℝ) + 1) ^ 2 := by ring
    _ ≤ 12 * a n := by linarith

/-- **Kimberling's conjecture (A293406, Clark Kimberling, Oct 29 2017).**
For the complementary equation `a(n) = a(n-1) + a(n-2) + b(n-1) + 1` with
`a(0) = 1, a(1) = 3, b(0) = 2, b(1) = 4` and `b` the increasing complement of `a`,
`a(n)/a(n-1) → (1 + √5)/2`, the golden ratio. Stated with the index shifted by one:
`a(n+1)/a(n) → φ`; `a n > 0` (`a_pos`) so the division is never the junk value. -/
theorem ratio_tendsto_goldenRatio :
    Filter.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) Filter.atTop
      (nhds Real.goldenRatio) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun n : ℕ => 12 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (12 : ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => abs_ratio_sub_le n) hlim

end Candidates.A293406ComplementaryEquationIncreasing
