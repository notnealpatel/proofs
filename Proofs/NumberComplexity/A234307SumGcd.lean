/-
# A234307 — Bala: an alternating gcd-sum formula for `Σ gcd(2n-i, i)`

Peter Bala's conjecture in OEIS A234307 (2024), where
`a(n) = Σ_{i=1}^n gcd(2n-i,i)`.

The alternating-sum identity follows without Pillai's function: with `L = Σ_{i=1}^{n} gcd(i, 2n)` (which equals `a(n)`
because `gcd(2n-i, i) = gcd(2n, i)`) and `O = Σ_{j<n} gcd(2j+1, 2n)`,

* the even terms of the alternating sum give `2 Σ_{j=1}^{2n} gcd(j, 4n)
  = 2 (2L + O)`;
* the odd terms give `Σ_{j<2n} gcd(2j+1, 2n) = 2 O`, because an odd number
  has the same gcd with `8n`, `4n` and `2n`, and `j ↦ j + n` shifts `2j+1` by
  `2n`;

so the alternating sum equals `4L + 2O - 2O = 4L`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A234307SumGcd

open Finset

/-- OEIS A234307: `a(n) = Σ_{i=1}^{n} gcd(2n - i, i)`.  The natural-number
subtraction `2n - i` is never truncated because `i ≤ n ≤ 2n`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Icc 1 n, Nat.gcd (2 * n - i) i

/-! ## Examples against the OEIS DATA line `1, 3, 6, 8, 11, 17, 16, 20, 27, 31` -/

example : a 1 = 1 := by decide
example : a 2 = 3 := by decide
example : a 3 = 6 := by decide
example : a 4 = 8 := by decide
example : a 5 = 11 := by decide
example : a 6 = 17 := by decide
example : a 7 = 16 := by decide
example : a 8 = 20 := by decide
example : a 9 = 27 := by decide
example : a 10 = 31 := by decide

/-- Bala's right-hand side without the factor `1/4`:
`Σ_{k=1}^{4n} (-1)^k gcd(k, 8n)`, as an integer. -/
def balaSum (n : ℕ) : ℤ := ∑ k ∈ Icc 1 (4 * n), (-1 : ℤ) ^ k * (Nat.gcd k (8 * n) : ℤ)

example : balaSum 1 = 4 := by decide
example : balaSum 2 = 12 := by decide
example : balaSum 3 = 24 := by decide

/-! ## Helper lemmas -/

/-- A sum over `Icc 1 N` is the shifted sum over `range N`. -/
lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Icc 1 N, f k = ∑ k ∈ range N, f (k + 1) := by
  have hIcc : Icc 1 N = Ico 1 (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  rw [Nat.add_comm]

/-- Pairing consecutive terms: `Σ_{k<2m} f k = Σ_{j<m} (f (2j) + f (2j+1))`. -/
lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ range (2 * m), f k = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- An odd number has the same gcd with `2x` as with `x`. -/
lemma gcd_odd_two_mul (j x : ℕ) : Nat.gcd (2 * j + 1) (2 * x) = Nat.gcd (2 * j + 1) x := by
  have hcop : Nat.Coprime 2 (2 * j + 1) := by
    rw [Nat.coprime_two_left]
    exact odd_two_mul_add_one j
  exact Nat.Coprime.gcd_mul_left_cancel_right x hcop

/-- The entry's summand simplifies: `gcd(2n - i, i) = gcd(i, 2n)` for `i ≤ 2n`,
so `a(n) = Σ_{i<n} gcd(i+1, 2n)`. -/
lemma a_eq_sum_range (n : ℕ) :
    a n = ∑ i ∈ range n, Nat.gcd (i + 1) (2 * n) := by
  rw [a, sum_Icc_one_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i + 1 ≤ 2 * n := by
    have := Finset.mem_range.mp hi
    omega
  rw [Nat.gcd_sub_self_left hle, Nat.gcd_comm]

/-- The odd terms over a doubled range: `Σ_{j<2n} gcd(2j+1, 2n) = 2 Σ_{j<n} gcd(2j+1, 2n)`,
since `2(n+j)+1 = (2j+1) + 2n`. -/
lemma sum_odd_gcd_two_mul (n : ℕ) :
    ∑ j ∈ range (2 * n), Nat.gcd (2 * j + 1) (2 * n) =
      2 * ∑ j ∈ range n, Nat.gcd (2 * j + 1) (2 * n) := by
  rw [two_mul n, Finset.sum_range_add, ← two_mul n, two_mul (∑ j ∈ range n, _)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * (n + j) + 1 = 2 * j + 1 + 2 * n by ring, Nat.gcd_add_self_left]

/-- Splitting `Σ_{j=1}^{2n} gcd(j, 4n)` by parity:
it equals `2 Σ_{i<n} gcd(i+1, 2n) + Σ_{i<n} gcd(2i+1, 2n)`. -/
lemma sum_gcd_four_mul (n : ℕ) :
    ∑ j ∈ range (2 * n), Nat.gcd (j + 1) (4 * n) =
      2 * ∑ i ∈ range n, Nat.gcd (i + 1) (2 * n) +
        ∑ i ∈ range n, Nat.gcd (2 * i + 1) (2 * n) := by
  rw [sum_range_two_mul, Finset.sum_add_distrib, Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, show 4 * n = 2 * (2 * n) by ring,
      Nat.gcd_mul_left]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show 4 * n = 2 * (2 * n) by ring, gcd_odd_two_mul]

/-- The alternating sum, paired: `Σ_{k=1}^{4n} (-1)^k gcd(k, 8n)
= 2 Σ_{j<2n} gcd(j+1, 4n) - Σ_{j<2n} gcd(2j+1, 2n)`. -/
lemma balaSum_eq (n : ℕ) :
    balaSum n = 2 * ((∑ j ∈ range (2 * n), Nat.gcd (j + 1) (4 * n) : ℕ) : ℤ) -
      ((∑ j ∈ range (2 * n), Nat.gcd (2 * j + 1) (2 * n) : ℕ) : ℤ) := by
  rw [balaSum, sum_Icc_one_eq_sum_range, show 4 * n = 2 * (2 * n) by ring, sum_range_two_mul,
    Nat.cast_sum, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hodd : Nat.gcd (2 * j + 1) (8 * n) = Nat.gcd (2 * j + 1) (2 * n) := by
    rw [show 8 * n = 2 * (2 * (2 * n)) by ring, gcd_odd_two_mul, gcd_odd_two_mul]
  have heven : Nat.gcd (2 * j + 1 + 1) (8 * n) = 2 * Nat.gcd (j + 1) (2 * (2 * n)) := by
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, show 8 * n = 2 * (2 * (2 * n)) by ring,
      Nat.gcd_mul_left]
  have hneg : (-1 : ℤ) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  have hpos : (-1 : ℤ) ^ (2 * j + 1 + 1) = 1 := by
    rw [pow_succ, hneg]
    norm_num
  rw [hodd, heven, hneg, hpos]
  push_cast
  ring

/-! ## The conjecture -/

/-- Bala's conjecture (OEIS A234307, 2024), with the denominator cleared:
for `n ≥ 1`, `4 Σ_{i=1}^n gcd(2n-i,i) = Σ_{k=1}^{4n} (-1)^k gcd(k,8n)`. -/
theorem four_mul_a_eq_balaSum (n : ℕ) (_hn : 1 ≤ n) : 4 * (a n : ℤ) = balaSum n := by
  rw [balaSum_eq, sum_gcd_four_mul, sum_odd_gcd_two_mul, a_eq_sum_range]
  push_cast
  ring

/-- Bala's conjecture (OEIS A234307, 2024), over `ℚ`: for `n ≥ 1`,
`a(n) = (1/4) Σ_{k=1}^{4n} (-1)^k gcd(k,8n)`. -/
theorem a_eq_quarter_alternating_gcd_sum (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (1 / 4) * ∑ k ∈ Icc 1 (4 * n), (-1 : ℚ) ^ k * (Nat.gcd k (8 * n) : ℚ) := by
  have hZ := four_mul_a_eq_balaSum n hn
  have hQ : (4 : ℚ) * (a n : ℚ) = ((balaSum n : ℤ) : ℚ) := by exact_mod_cast hZ
  rw [balaSum] at hQ
  push_cast at hQ
  rw [← hQ]
  ring

end Candidates.A234307SumGcd
