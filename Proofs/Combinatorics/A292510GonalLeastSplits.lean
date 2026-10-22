/-
# A292510 — least k for which the first k n-gonal numbers split evenly

OEIS A292510, Seiichi Manyama (2017): for `5 < n`, the least positive `k`
for which the first `k` n-gonal numbers split into equal-sum sets is `7`.
Writing `P(n,m) = (n-2) C(m,2) + m`, each subset of `{1,…,k}` gives a
linear condition in `n`. For `k ≤ 6`, the at most `2^6` cases rule out a
split when `5 < n`; the entry supplies the split for `k = 7`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A292510GonalLeastSplits

/-! ## Definitions -/

/-- The `m`-th `n`-gonal number `P(n,m) = ((n-2)m^2 - (n-4)m)/2`, computed in `ℤ`.
The numerator is always even (see `P_eq`), so the integer division is exact. -/
def P (n m : ℕ) : ℤ := (((n : ℤ) - 2) * (m : ℤ) ^ 2 - ((n : ℤ) - 4) * m) / 2

/-- `Splits n k`: the set `{P(n,1), …, P(n,k)}` can be partitioned into two parts with
equal sums, i.e. some `S ⊆ {1, …, k}` has `∑_{m ∈ S} P(n,m) = ∑_{m ∉ S} P(n,m)`.
(For `n ≥ 3` the values `P(n,m)`, `m ≥ 1`, are distinct and positive, so splitting the
index set is the same as splitting the value set, and for `k ≥ 1` neither part can be
empty.) -/
def Splits (n k : ℕ) : Prop :=
  ∃ S ⊆ Finset.Icc 1 k, ∑ m ∈ S, P n m = ∑ m ∈ Finset.Icc 1 k \ S, P n m

/-! ## Examples for `P` -/

/-- Triangular numbers (`n = 3`). -/
example : (List.range 6).map (fun m => P 3 (m + 1)) = [1, 3, 6, 10, 15, 21] := by decide

/-- Squares (`n = 4`). -/
example : (List.range 6).map (fun m => P 4 (m + 1)) = [1, 4, 9, 16, 25, 36] := by decide

/-- Pentagonal numbers (`n = 5`, A000326). -/
example : (List.range 6).map (fun m => P 5 (m + 1)) = [1, 5, 12, 22, 35, 51] := by decide

/-- Hexagonal numbers (`n = 6`, A000384). -/
example : (List.range 6).map (fun m => P 6 (m + 1)) = [1, 6, 15, 28, 45, 66] := by decide

/-! ## Helper lemmas -/

/-- Closed form without division: `P(n,m) = (n-2)·C(m,2) + m`. -/
theorem P_eq (n m : ℕ) : P n m = ((n : ℤ) - 2) * (m.choose 2 : ℕ) + m := by
  have hN : m.choose 2 * 2 = m * (m - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self m).two_dvd
  rcases m with _ | m
  · simp [P]
  · have hZ : (((m + 1).choose 2 : ℕ) : ℤ) * 2 = ((m : ℤ) + 1) * m := by
      rw [Nat.add_sub_cancel] at hN
      exact_mod_cast hN
    unfold P
    apply Int.ediv_eq_of_eq_mul_left (by norm_num)
    push_cast
    linear_combination (-((n : ℤ) - 2)) * hZ

/-- An equal split by `S ⊆ {1, …, k}` means twice the `S`-part (written as an
indicator sum over `{1, …, k}`) equals the total. -/
theorem two_mul_sum_of_splits {n k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 k)
    (h : ∑ m ∈ S, P n m = ∑ m ∈ Finset.Icc 1 k \ S, P n m) :
    2 * ∑ m ∈ Finset.Icc 1 k, (if m ∈ S then P n m else 0) = ∑ m ∈ Finset.Icc 1 k, P n m := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS,
    ← Finset.sum_sdiff hS, ← h]
  ring

/-- Lower-bound engine: for `1 ≤ k ≤ 6` and `n ≥ 3` there is no equal split, except
possibly for `n = 3, k ∈ {4,5,6}` and `n = 5, k = 6`, which the hypotheses exclude.
Each of the at most `2^6` subsets gives a linear condition in `n` refuted by `omega`. -/
theorem not_splits_aux {n k : ℕ} (hn : 3 ≤ n) (hk1 : 1 ≤ k) (hk6 : k ≤ 6)
    (h3 : n = 3 → k ≤ 3) (h5 : n = 5 → k ≤ 5) : ¬ Splits n k := by
  rintro ⟨S, hS, h⟩
  have h2 := two_mul_sum_of_splits hS h
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel] at h2
  interval_cases k
  all_goals
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, P_eq] at h2
    norm_num [Nat.choose_two_right] at h2
    split_ifs at h2 <;> omega

/-- For `6 ≤ n` (indeed for `4 ≤ n`, `n ≠ 5`) no `k` with `1 ≤ k ≤ 6` splits. -/
theorem not_splits_of_le_six {n k : ℕ} (hn : 5 < n) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) :
    ¬ Splits n k :=
  not_splits_aux (by omega) hk1 hk6 (by omega) (by omega)

/-- The entry's upper bound: `P(n,1) + P(n,2) + P(n,4) + P(n,7) = P(n,3) + P(n,5) + P(n,6)`,
so `{P(n,1), …, P(n,7)}` splits for every `n`. -/
theorem splits_seven (n : ℕ) : Splits n 7 := by
  refine ⟨{1, 2, 4, 7}, by decide, ?_⟩
  rw [show Finset.Icc 1 7 \ {1, 2, 4, 7} = {3, 5, 6} by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  simp only [P_eq]
  norm_num [Nat.choose_two_right]
  ring

/-! ## Sequence examples: `a(3) = 4`, `a(4) = 7`, `a(5) = 6` -/

/-- `a(3) = 4`: `1 + 3 + 6 = 10`. -/
example : IsLeast {k : ℕ | 1 ≤ k ∧ Splits 3 k} 4 := by
  refine ⟨⟨by norm_num, {4}, by decide, by decide⟩, ?_⟩
  rintro k ⟨hk1, hk⟩
  by_contra hlt
  exact not_splits_aux le_rfl hk1 (by omega) (fun _ => by omega) (by omega) hk

/-- `a(4) = 7`. -/
example : IsLeast {k : ℕ | 1 ≤ k ∧ Splits 4 k} 7 := by
  refine ⟨⟨by norm_num, splits_seven 4⟩, ?_⟩
  rintro k ⟨hk1, hk⟩
  by_contra hlt
  exact not_splits_aux (by norm_num) hk1 (by omega) (by omega) (by omega) hk

/-- `a(5) = 6`: `12 + 51 = 1 + 5 + 22 + 35`. -/
example : IsLeast {k : ℕ | 1 ≤ k ∧ Splits 5 k} 6 := by
  refine ⟨⟨by norm_num, {3, 6}, by decide, by decide⟩, ?_⟩
  rintro k ⟨hk1, hk⟩
  by_contra hlt
  exact not_splits_aux (by norm_num) hk1 (by omega) (by omega) (fun _ => by omega) hk

/-! ## The conjecture -/

/-- **Conjecture of A292510 (Seiichi Manyama, Sep 17 2017): `a(n) = 7` for `n > 5`.**

Here `a(n)` is the smallest `k ≥ 1` such
that `{P(n,1), …, P(n,k)}` (with `P(n,m)` the `m`-th `n`-gonal number) can be partitioned
into two sets with equal sums.  Stated as: for every `n > 5`, `7` is the least element of
`{k | 1 ≤ k ∧ Splits n k}`. -/
theorem a292510_eq_seven {n : ℕ} (hn : 5 < n) : IsLeast {k : ℕ | 1 ≤ k ∧ Splits n k} 7 := by
  refine ⟨⟨by norm_num, splits_seven n⟩, ?_⟩
  rintro k ⟨hk1, hk⟩
  by_contra hlt
  exact not_splits_of_le_six hn hk1 (by omega) hk

end Candidates.A292510GonalLeastSplits
