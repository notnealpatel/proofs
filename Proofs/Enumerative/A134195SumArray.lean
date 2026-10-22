/-
Antidiagonal sums and partial sums (OEIS A134195; Sean A. Irvine, Jul 14 2022).

For the A126885 array T(n,k)=n T(n,k-1)+k with T(n,1)=1,
 ∑_{n=0}^s T(n,s-n+1)=∑_{j=0}^s A104879(j) for every natural s.
A104879 is defined by the entry's explicit formula
1+j+∑_{k=2}^{j+1}(k^(j-k+1)-1)/(k-1), not by a separate bijection to
its sum-of-powers-triangle interpretation. Geometric sums identify the
first difference of the antidiagonal sums with that formula.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A134195SumArray

open Finset

/-! ## Definitions -/

/-- The square array A126885: `T(n, 1) = 1` and `T(n, k) = n * T(n, k-1) + k`
for `k ≥ 2` (`n ≥ 0`, `k ≥ 1`).  The value `T n 0 = 0` is a convenience seed:
it makes the single recurrence `T n (k+1) = n * T n k + (k+1)` reproduce
`T n 1 = 1`, and it is never used by the statements below at `k = 0`. -/
def T : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 => n * T n k + (k + 1)

/-- A104879, by the entry's formula
`a(j) = 1 + j + Sum_{k=2..j+1} (k^(j-k+1) - 1)/(k-1)`.
The exponent is written `j + 1 - k`, not `j - k + 1`: in `ℕ` the latter parses as
`(j - k) + 1` and gives the junk value `1` instead of `0` at `k = j + 1`.  On the
summation range `2 ≤ k ≤ j + 1` every truncated operation is then off its junk
value: `j + 1 - k` is the integer `j - k + 1 ≥ 0`, `k ^ _ ≥ 1`, `k - 1 ≥ 1`, and
the division is exact (`a104879_dvd`). -/
def a104879 (j : ℕ) : ℕ :=
  1 + j + ∑ k ∈ Icc 2 (j + 1), (k ^ (j + 1 - k) - 1) / (k - 1)

/-- A134195: the sum of the `s`-th antidiagonal of A126885,
`Sum_{n=0..s} T(n, s-n+1)`. -/
def a134195 (s : ℕ) : ℕ :=
  ∑ n ∈ range (s + 1), T n (s - n + 1)

/-! ## Examples -/

-- The first four ascending antidiagonals of A126885: 1; 1,2; 1,3,3; 1,4,6,4.
example : T 0 1 = 1 ∧ T 1 1 = 1 ∧ T 0 2 = 2 ∧ T 2 1 = 1 ∧ T 1 2 = 3 ∧ T 0 3 = 3 ∧
    T 3 1 = 1 ∧ T 2 2 = 4 ∧ T 1 3 = 6 ∧ T 0 4 = 4 := by decide

-- Later terms of A126885: T(2,4) = 26, T(3,4) = 58, T(4,4) = 112.
example : T 2 4 = 26 ∧ T 3 4 = 58 ∧ T 4 4 = 112 := by decide

-- The first terms of A104879: 1, 2, 4, 8, 17, 40, 106, 316.
example : (List.range 8).map a104879 = [1, 2, 4, 8, 17, 40, 106, 316] := by decide

-- The first terms of A134195: 1, 3, 7, 15, 32, 72, 178, 494.
example : (List.range 8).map a134195 = [1, 3, 7, 15, 32, 72, 178, 494] := by decide

/-! ## Proof -/

/-- The division in the A104879 formula is exact: `k - 1 ∣ k ^ m - 1`. -/
theorem a104879_dvd (k m : ℕ) : k - 1 ∣ k ^ m - 1 :=
  Nat.sub_one_dvd_pow_sub_one k m

/-- The geometric sum `G(n, m) = Sum_{i<m} n^i`. -/
def G (n m : ℕ) : ℕ := ∑ i ∈ range m, n ^ i

/-- Horner step for the geometric sum: `G(n, m+1) = 1 + n * G(n, m)`. -/
theorem G_succ (n m : ℕ) : G n (m + 1) = 1 + n * G n m := by
  unfold G
  rw [sum_range_succ', mul_sum]
  simp only [pow_succ', pow_zero]
  ring

/-- The first difference of a row of A126885 is a geometric sum:
`T(n, k+1) = T(n, k) + G(n, k+1)`. -/
theorem T_succ_eq (n k : ℕ) : T n (k + 1) = T n k + G n (k + 1) := by
  induction k with
  | zero => simp [T, G]
  | succ k ih =>
    have hT : T n (k + 1 + 1) = n * T n (k + 1) + (k + 1 + 1) := rfl
    have hT' : T n (k + 1) = n * T n k + (k + 1) := rfl
    rw [hT, G_succ n (k + 1)]
    nth_rw 1 [ih]
    rw [hT']
    ring

/-- A104879 as a full antidiagonal sum of geometric sums:
`A104879(j) = Sum_{k=0..j+1} G(k, j+1-k)`. -/
theorem a104879_eq_sum_G (j : ℕ) :
    a104879 j = ∑ k ∈ range (j + 2), G k (j + 1 - k) := by
  have hIcc : Icc 2 (j + 1) = Ico 2 (2 + j) := by
    ext x
    simp only [mem_Icc, mem_Ico]
    omega
  have hshift : ∑ k ∈ Icc 2 (j + 1), (k ^ (j + 1 - k) - 1) / (k - 1) =
      ∑ k ∈ range j, G (k + 2) (j + 1 - (k + 2)) := by
    rw [hIcc, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine sum_congr rfl fun k _ => ?_
    rw [G, Nat.geomSum_eq (by omega : 2 ≤ k + 2), add_comm 2 k]
  have hG0 : G 0 (j + 1) = 1 := by
    rw [G_succ, zero_mul, add_zero]
  have hG1 : G 1 j = j := by simp [G]
  rw [a104879, hshift, sum_range_succ', sum_range_succ']
  simp only [Nat.sub_zero, zero_add]
  rw [hG0, Nat.add_sub_cancel, hG1]
  ring

/-- The first difference of the antidiagonal sums is A104879:
`a134195 (s + 1) = a134195 s + A104879 (s + 1)`. -/
theorem a134195_succ (s : ℕ) : a134195 (s + 1) = a134195 s + a104879 (s + 1) := by
  have hsplit : ∀ n ∈ range (s + 2), T n (s + 1 - n + 1) =
      T n (s + 1 - n) + G n (s + 1 - n + 1) := fun n _ => T_succ_eq n (s + 1 - n)
  have hT : ∑ n ∈ range (s + 2), T n (s + 1 - n) = a134195 s := by
    rw [sum_range_succ, Nat.sub_self]
    have hT0 : T (s + 1) 0 = 0 := rfl
    rw [hT0, add_zero, a134195]
    refine sum_congr rfl fun n hn => ?_
    have hns : n < s + 1 := mem_range.mp hn
    congr 1
    omega
  have hG : ∑ n ∈ range (s + 2), G n (s + 1 - n + 1) = a104879 (s + 1) := by
    rw [a104879_eq_sum_G, sum_range_succ _ (s + 1 + 1), Nat.sub_self]
    have hG0 : G (s + 1 + 1) 0 = 0 := by simp [G]
    rw [hG0, add_zero]
    refine sum_congr rfl fun n hn => ?_
    have hns : n < s + 2 := mem_range.mp hn
    congr 1
    omega
  rw [a134195, sum_congr rfl hsplit, sum_add_distrib, hT, hG]

/-! ## The conjecture -/

/-- The antidiagonal sums of A126885 are the partial sums of the
formula-defined A104879, for every natural diagonal index `s`. -/
theorem a134195_eq_sum_a104879 (s : ℕ) :
    ∑ n ∈ range (s + 1), T n (s - n + 1) = ∑ j ∈ range (s + 1), a104879 j := by
  induction s with
  | zero => decide
  | succ s ih =>
    have hstep := a134195_succ s
    rw [a134195, a134195, ih] at hstep
    rw [hstep, sum_range_succ _ (s + 1)]

end Candidates.A134195SumArray
