/-
# A073642 — Yanev: `2·a(n) = 3·Σ v₂(k) − Σ v₂(k)²`

## OEIS source (retrieved with `oeis show A073642`, 2026-10-21)

```
NAME:     Replace 2^k in the binary representation of n with k (i.e., if
          n = 2^b + 2^c + 2^d + ... then a(n) = b + c + d + ...).
TERMS:    0,0,1,1,2,2,3,3,3,3,4,4,5,5,6,6,4,4,5,5,6,6,7,7,7,7,8,8,9,9,10,10,
          5,5,6,6,7,7,8,8,8,8,9,9,10,10,11,11,9,9,10,10,11,11,12,12,...
KEYWORDS: easy,nonn,base
FORMULA (the conjecture):
  Conjecture: a(n) = (3*A011371(n) - Sum_{k=1..n} A007814(k)^2)/2 for n > 0.
  - _Velin Yanev_, Sep 09 2017
```

Here `A011371(n) = Σ_{k=1..n} v₂(k)` (the 2-adic valuation of `n!`) and
`A007814(k) = v₂(k)`.  The statement below writes `A011371(n)` as that sum
and clears the denominator, working in `ℤ` so the subtraction is genuine.

## Status

Triage: open (the entry leaves the formula as a conjecture; no proof found in
the entry or literature by the triage).  Numerically re-checked for all
`1 ≤ n ≤ 400000` (Python, 2026-10-21).  Proved below, sorry-free.

## Proof idea

With `c(n)` the binary digit sum, `P(n) = Σ_{k≤n} v₂(k)` and
`F(n) = Σ_{k≤n} (3 v₂(k) − v₂(k)²)`, the even/odd recursions are
`a(2m) = a(m) + c(m)`, `a(2m+1) = a(2m)`, `F(2m) = F(m) + 2m − 2P(m)`,
`F(2m+1) = F(2m)`, and Legendre's `P(m) + c(m) = m`.  Hence
`F(2m) = F(m) + 2c(m)` and `2a = F` follows by even/odd recursion on `n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A073642Yanev

/-! ## Definition layer -/

/-- OEIS A073642: if `n = Σ b_i 2^i` in binary, then `a(n) = Σ i · b_i`,
the sum of the positions of the `1`-bits of `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n.size, if n.testBit i then i else 0

-- Ground truth: the first 34 terms of the OEIS DATA line.
example : (List.range 34).map a =
    [0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6, 6, 4, 4, 5, 5, 6, 6, 7, 7,
      7, 7, 8, 8, 9, 9, 10, 10, 5, 5] := by
  decide

/-- Weighted bit sum: `Σ_{i : bit i of n is 1} f i`, over the binary length of
`n`.  `a = bitSum id`, and `bitSum (fun _ => 1)` is the binary digit sum. -/
def bitSum (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n.size, if n.testBit i then f i else 0

-- Ground truth: the binary digit sum of `11 = 1011₂` is `3`.
example : bitSum (fun _ => 1) 11 = 3 := by decide

/-- Sum of `g (v₂ k)` over `1 ≤ k ≤ n`. -/
def vSum (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, g (padicValNat 2 k)

-- Ground truth: `vSum` with `g = id` at `n = 0` is the empty sum.
example : vSum (fun v => (v : ℤ)) 0 = 0 := by simp [vSum]

/-! ## Bit-sum recursions -/

/-- `a` is the weighted bit sum with weight `i ↦ i`. -/
theorem a_eq_bitSum (n : ℕ) : a n = bitSum (fun i => i) n := rfl

/-- The bit sum may be taken over any range `N` with `n < 2 ^ N`. -/
theorem bitSum_eq_of_lt (f : ℕ → ℕ) {n N : ℕ} (h : n < 2 ^ N) :
    bitSum f n = ∑ i ∈ Finset.range N, if n.testBit i then f i else 0 := by
  have hsize : n.size ≤ N := Nat.size_le.mpr h
  refine Finset.sum_subset (Finset.range_subset_range.mpr hsize) ?_
  intro i _ hi
  have hlt : n < 2 ^ i := by
    have hi' : n.size ≤ i := by simpa using hi
    exact Nat.size_le.mp hi'
  simp [Nat.testBit_eq_false_of_lt hlt]

/-- Doubling shifts every bit position up by one. -/
theorem bitSum_two_mul (f : ℕ → ℕ) (m : ℕ) :
    bitSum f (2 * m) = bitSum (fun i => f (i + 1)) m := by
  have hm : m < 2 ^ m.size := Nat.lt_size_self m
  have h2m : 2 * m < 2 ^ (m.size + 1) := by rw [pow_succ]; omega
  rw [bitSum_eq_of_lt f h2m, bitSum_eq_of_lt _ hm, Finset.sum_range_succ']
  have hdiv : 2 * m / 2 = m := by omega
  have h0 : (2 * m).testBit 0 = false := by simp [Nat.testBit_zero]
  simp only [Nat.testBit_succ, hdiv, h0, Bool.false_eq_true, if_false, add_zero]

/-- `2m + 1` has the shifted bits of `m` plus bit `0`. -/
theorem bitSum_two_mul_add_one (f : ℕ → ℕ) (m : ℕ) :
    bitSum f (2 * m + 1) = bitSum (fun i => f (i + 1)) m + f 0 := by
  have hm : m < 2 ^ m.size := Nat.lt_size_self m
  have h2m : 2 * m + 1 < 2 ^ (m.size + 1) := by rw [pow_succ]; omega
  rw [bitSum_eq_of_lt f h2m, bitSum_eq_of_lt _ hm, Finset.sum_range_succ']
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have h0 : (2 * m + 1).testBit 0 = true := by simp [Nat.testBit_zero]
  simp only [Nat.testBit_succ, hdiv, h0, if_true]

/-- The bit sum is additive in the weight. -/
theorem bitSum_add (f h : ℕ → ℕ) (n : ℕ) :
    bitSum (fun i => f i + h i) n = bitSum f n + bitSum h n := by
  unfold bitSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-! ## Valuation-sum recursions -/

/-- Odd `2m + 1` contributes `g 0 = 0`. -/
theorem vSum_two_mul_add_one (g : ℕ → ℤ) (hg : g 0 = 0) (m : ℕ) :
    vSum g (2 * m + 1) = vSum g (2 * m) := by
  unfold vSum
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hv : padicValNat 2 (2 * m + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  rw [hv, hg, add_zero]

/-- Up to `2m`, only the even `k = 2j` contribute, with `v₂(2j) = v₂(j) + 1`. -/
theorem vSum_two_mul (g : ℕ → ℤ) (hg : g 0 = 0) (m : ℕ) :
    vSum g (2 * m) = ∑ j ∈ Finset.Icc 1 m, g (padicValNat 2 j + 1) := by
  induction m with
  | zero => simp [vSum]
  | succ m ih =>
    have hsplit : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [hsplit, vSum, Finset.sum_Icc_succ_top (by omega), ← vSum,
      vSum_two_mul_add_one g hg, ih, Finset.sum_Icc_succ_top (by omega)]
    have hv : padicValNat 2 (2 * m + 1 + 1) = padicValNat 2 (m + 1) + 1 := by
      rw [← hsplit, padicValNat.mul (by norm_num) (by omega), padicValNat_self]
      ring
    rw [hv]

/-- Legendre for `p = 2`: `Σ_{k ≤ n} v₂(k) + (binary digit sum of n) = n`. -/
theorem vSum_id_add_digitSum (n : ℕ) :
    vSum (fun v => (v : ℤ)) n + (bitSum (fun _ => 1) n : ℤ) = n := by
  induction n using Nat.evenOddRec with
  | h0 => simp [vSum, bitSum]
  | h_even m ih =>
    rw [vSum_two_mul _ (by simp), bitSum_two_mul]
    have hsum : ∑ j ∈ Finset.Icc 1 m, ((padicValNat 2 j + 1 : ℕ) : ℤ)
        = vSum (fun v => (v : ℤ)) m + m := by
      simp only [Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib, vSum,
        Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
        mul_one]
    rw [hsum]
    push_cast
    linarith
  | h_odd m ih =>
    rw [vSum_two_mul_add_one _ (by simp), vSum_two_mul _ (by simp),
      bitSum_two_mul_add_one]
    have hsum : ∑ j ∈ Finset.Icc 1 m, ((padicValNat 2 j + 1 : ℕ) : ℤ)
        = vSum (fun v => (v : ℤ)) m + m := by
      simp only [Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib, vSum,
        Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
        mul_one]
    rw [hsum]
    push_cast
    linarith

/-- Even step: if `2 a(m) = F(m)` then `2 a(2m) = F(2m)`, where
`F = vSum (3v − v²)`; uses `F(2m) = F(m) + 2m − 2P(m)` and Legendre. -/
theorem two_mul_a_two_mul_of (m : ℕ)
    (ih : (2 * a m : ℤ) = vSum (fun v => 3 * (v : ℤ) - (v : ℤ) ^ 2) m) :
    (2 * a (2 * m) : ℤ) = vSum (fun v => 3 * (v : ℤ) - (v : ℤ) ^ 2) (2 * m) := by
  have hstep : vSum (fun v => 3 * (v : ℤ) - (v : ℤ) ^ 2) (2 * m)
      = vSum (fun v => 3 * (v : ℤ) - (v : ℤ) ^ 2) m
        + 2 * m - 2 * vSum (fun v => (v : ℤ)) m := by
    rw [vSum_two_mul _ (by simp)]
    simp only [vSum, Nat.cast_add, Nat.cast_one, Finset.mul_sum]
    rw [show (2 * (m : ℤ)) = ∑ _j ∈ Finset.Icc 1 m, (2 : ℤ) by simp [mul_comm],
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hleg := vSum_id_add_digitSum m
  rw [hstep, a_eq_bitSum, bitSum_two_mul, bitSum_add, ← a_eq_bitSum]
  push_cast
  linarith

/-- `a(2m + 1) = a(2m)`: bit `0` has weight `0`. -/
theorem a_two_mul_add_one (m : ℕ) : a (2 * m + 1) = a (2 * m) := by
  rw [a_eq_bitSum, a_eq_bitSum, bitSum_two_mul_add_one, bitSum_two_mul,
    add_zero]

/-- The cleared identity `2 a(n) = Σ_{k ≤ n} (3 v₂(k) − v₂(k)²)`, for all `n`. -/
theorem two_mul_a_eq_vSum (n : ℕ) :
    (2 * a n : ℤ) = vSum (fun v => 3 * (v : ℤ) - (v : ℤ) ^ 2) n := by
  induction n using Nat.evenOddRec with
  | h0 => simp [vSum, a]
  | h_even m ih => exact two_mul_a_two_mul_of m ih
  | h_odd m ih =>
    rw [vSum_two_mul_add_one _ (by simp), a_two_mul_add_one]
    exact two_mul_a_two_mul_of m ih

/-! ## The conjecture -/

/-- **Yanev's formula (A073642, Velin Yanev, Sep 09 2017), proved.**

Verbatim: "Conjecture: a(n) = (3*A011371(n) - Sum_{k=1..n} A007814(k)^2)/2 for
n > 0."  With `A011371(n) = Σ_{k=1..n} v₂(k)` and `A007814(k) = v₂(k)`, the
cleared form is `2·a(n) = 3·Σ_{k=1..n} v₂(k) − Σ_{k=1..n} v₂(k)²`, stated in
`ℤ` so the subtraction is not truncated.  (The identity also holds at `n = 0`;
the guard `0 < n` is kept from the source.) -/
theorem yanev (n : ℕ) (_hn : 0 < n) :
    (2 * a n : ℤ) = 3 * ∑ k ∈ Finset.Icc 1 n, (padicValNat 2 k : ℤ)
      - ∑ k ∈ Finset.Icc 1 n, (padicValNat 2 k : ℤ) ^ 2 := by
  rw [two_mul_a_eq_vSum, vSum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The source's division form: `a(n) = (3·Σ v₂(k) − Σ v₂(k)²) / 2` in `ℤ`,
for `n > 0`; the numerator is even, so the division is exact. -/
theorem yanev_div (n : ℕ) (hn : 0 < n) :
    (a n : ℤ) = (3 * ∑ k ∈ Finset.Icc 1 n, (padicValNat 2 k : ℤ)
      - ∑ k ∈ Finset.Icc 1 n, (padicValNat 2 k : ℤ) ^ 2) / 2 := by
  rw [← yanev n hn]
  omega

-- Non-vacuity: the hypotheses are satisfiable, e.g. at `n = 12` with `a 12 = 5`.
example : a 12 = 5 := by decide
example : (2 * a 12 : ℤ) = 3 * ∑ k ∈ Finset.Icc 1 12, (padicValNat 2 k : ℤ)
    - ∑ k ∈ Finset.Icc 1 12, (padicValNat 2 k : ℤ) ^ 2 := yanev 12 (by norm_num)

end Candidates.A073642Yanev
