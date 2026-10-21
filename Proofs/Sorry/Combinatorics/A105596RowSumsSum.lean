/-
# A105596 — alternating self-convolution of the row sums A105595

## OEIS source (retrieved with `oeis show A105596`, 2026-10-21)

```
NAME:     a(n) = Sum_{k=0..n} A105595(k)*(-1)^k*A105595(n-k) (interpolated zeros
          suppressed).
TERMS:    1,5,13,17,25,25,33,21,9,-15,-23,-3,-11,-31,-47,-35,5,-47,-83,-75,...
COMMENT (the conjecture; unsigned and undated in the entry):
  Conjecture : a(2n)=1 mod 4 for all n, a(2n+1)=0 for all n.
PROGRAM (Maple, R. J. Mathar, Nov 28 2014):
  A105596 := proc(n) add(A105595(k)*(-1)^k*A105595(2*n-k),k=0..2*n) ; end proc:
```

Underlying entries (same retrieval date):

```
A105594 NAME:    Triangle read by rows: abs(A103447)*A047999 mod 2.
A105594 FORMULA: T(n, k) = mod(Sum_{j=0..n}(abs(mu(binomial(n,j)))*mod(binomial(j,k),2)), 2).
A105595 NAME:    Row sums of number triangle A105594.
A105595 COMMENT: Every term is odd. [...] - _Bing Gao_, Sep 22 2026
```

The conjecture's indices refer to the *unsuppressed* sequence
`c(n) = Sum_{k=0..n} (-1)^k b(k) b(n-k)` with `b = A105595`; the listed terms
are `c(2n)`, and the program confirms this reading.

## Status

Triage: proved-elsewhere.  The vanishing of `c(2m+1)` is the antisymmetry of
the summand under `k ↦ n - k`; the congruence `c(2m) ≡ 1 (mod 4)` follows from
the oddness of every `b(k)`, which Bing Gao proved in A105595 (Sep 2026).  This
module re-proves both, including the oddness of `b`, from the defining formula.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A105596RowSumsSum

open Finset

/-! ## Definition layer -/

/-- **A105594**: `T(n, k) = (Sum_{j=0..n} |mu(binomial(n, j))| * (binomial(j, k) mod 2)) mod 2`,
the entry's formula verbatim, with `mu` Mathlib's `ArithmeticFunction.moebius`. -/
def T (n k : ℕ) : ℕ :=
  (∑ j ∈ range (n + 1), (ArithmeticFunction.moebius (n.choose j)).natAbs * (j.choose k % 2)) % 2

/-- **A105595**: the `n`-th row sum `Sum_{k=0..n} T(n, k)` of A105594. -/
def b (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), T n k

/-- The unsuppressed alternating self-convolution `c(n) = Sum_{k=0..n} (-1)^k b(k) b(n-k)`;
the OEIS sequence A105596 lists `c(2n)`.  The index `n - k` is never truncated since `k ≤ n`. -/
def c (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (-1) ^ k * (b k : ℤ) * (b (n - k) : ℤ)

/-! ### Ground truth against the listed terms -/

/-- The first six rows of A105594: `1; 0,1; 1,1,1; 0,0,0,1; 1,0,1,0,1; 0,1,0,1,0,1`. -/
example : (List.range 6).map (fun n => (List.range (n + 1)).map (T n)) =
    [[1], [0, 1], [1, 1, 1], [0, 0, 0, 1], [1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1]] := by
  decide +kernel

/-- The first sixteen terms of A105595. -/
example : (List.range 16).map b = [1, 1, 3, 1, 3, 3, 3, 1, 3, 3, 3, 3, 3, 7, 3, 9] := by
  decide +kernel

/-- The first six terms of A105596, `c(0), c(2), ..., c(10)`. -/
example : (List.range 6).map (fun n => c (2 * n)) = [1, 5, 13, 17, 25, 25] := by
  decide +kernel

/-- The suppressed odd-index values `c(1), c(3), c(5)` are zero. -/
example : (List.range 3).map (fun n => c (2 * n + 1)) = [0, 0, 0] := by
  decide +kernel

/-! ## Oddness of A105595 (Bing Gao's argument) -/

/-- For `j ≤ n`, summing `binomial(j, k)` over `k ≤ n` gives `2 ^ j`. -/
theorem sum_range_choose_of_le {j n : ℕ} (hjn : j ≤ n) :
    ∑ k ∈ range (n + 1), j.choose k = 2 ^ j := by
  rw [← Nat.sum_range_choose j]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- Every term of A105595 is odd: modulo `2`, the row sum collapses to
`Sum_j |mu(binomial(n, j))| * 2 ^ j ≡ |mu(1)| = 1`. -/
theorem b_odd (n : ℕ) : Odd (b n) := by
  rw [← ZMod.natCast_eq_one_iff_odd]
  have hT : ∀ k, ((T n k : ℕ) : ZMod 2) =
      ∑ j ∈ range (n + 1),
        ((ArithmeticFunction.moebius (n.choose j)).natAbs : ZMod 2) * ((j.choose k : ℕ) : ZMod 2) := by
    intro k
    rw [T, ZMod.natCast_mod]
    push_cast
    simp only [ZMod.natCast_mod]
  have hswap : ((b n : ℕ) : ZMod 2) =
      ∑ j ∈ range (n + 1),
        ((ArithmeticFunction.moebius (n.choose j)).natAbs : ZMod 2) * ((2 : ZMod 2) ^ j) := by
    rw [b, Nat.cast_sum]
    simp only [hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.mul_sum]
    congr 1
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Nat.cast_sum, sum_range_choose_of_le hjn]
    push_cast
    rfl
  rw [hswap, Finset.sum_range_succ']
  have hzero : ∀ i ∈ range n,
      ((ArithmeticFunction.moebius (n.choose (i + 1))).natAbs : ZMod 2) * ((2 : ZMod 2) ^ (i + 1))
        = 0 := by
    intro i _
    rw [pow_succ]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, mul_zero, mul_zero]
  rw [Finset.sum_eq_zero hzero]
  simp

/-! ## The odd-index vanishing -/

/-- For odd `n`, the alternating convolution `Sum_{k=0..n} (-1)^k f(k) f(n-k)` vanishes,
since the summand changes sign under `k ↦ n - k`. -/
theorem alt_conv_odd_eq_zero (f : ℕ → ℤ) (m : ℕ) :
    ∑ k ∈ range (2 * m + 1 + 1), (-1) ^ k * f k * f (2 * m + 1 - k) = 0 := by
  set n := 2 * m + 1 with hn
  set S := ∑ k ∈ range (n + 1), (-1) ^ k * f k * f (n - k) with hS
  have hrefl : S = ∑ k ∈ range (n + 1), (-1) ^ (n - k) * f (n - k) * f (n - (n - k)) := by
    rw [hS, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
  have hneg : S = -S := by
    nth_rewrite 1 [hrefl]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n - (n - k) = k := by omega
    have hsign : ((-1 : ℤ) ^ (n - k)) * (-1) ^ k = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hkn, hn, pow_succ, pow_mul]
      norm_num
    have hsign' : ((-1 : ℤ) ^ (n - k)) = -(-1) ^ k := by
      have hsq : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      linear_combination (-1 : ℤ) ^ k * hsign - (-1 : ℤ) ^ (n - k) * hsq
    rw [hsub, hsign']
    ring
  linarith

/-! ## The even-index congruence -/

/-- An odd integer is `2 r + 1` in `ZMod 4` for some `r`. -/
theorem odd_cast_zmod_four {x : ℤ} (hx : Odd x) : ∃ r : ZMod 4, (x : ZMod 4) = 2 * r + 1 := by
  obtain ⟨r, hr⟩ := hx
  exact ⟨r, by rw [hr]; push_cast; ring⟩

/-- In `ZMod 4`, `(-1) ^ k = 1 + 2 k`. -/
theorem neg_one_pow_zmod_four (k : ℕ) : ((-1 : ZMod 4) ^ k) = 1 + 2 * (k : ZMod 4) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    have key : ∀ t : ZMod 4, (1 + 2 * t) * (-1) = 1 + 2 * (t + 1) := by decide
    exact key _

/-- Gauss: `Sum_{k=0..2m} k = m (2m + 1)`. -/
theorem sum_range_id_two_mul_add_one (m : ℕ) :
    ∑ k ∈ range (2 * m + 1), k = m * (2 * m + 1) := by
  have h := Finset.sum_range_id_mul_two (2 * m + 1)
  have h' : (2 * m + 1) * (2 * m + 1 - 1) = m * (2 * m + 1) * 2 := by
    rw [Nat.add_sub_cancel]
    ring
  rw [h'] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

/-- If every `f k` is odd, then `Sum_{k=0..2m} (-1)^k f(k) f(2m-k) ≡ 1 (mod 4)`.
Termwise, `(-1)^k f(k) f(2m-k) ≡ f(k) + f(2m-k) - 1 + 2k (mod 4)`; summing gives
`2 (2m+1) - (2m+1) + 2 m (2m+1) = (2m+1)^2 ≡ 1`. -/
theorem alt_conv_even_mod_four (f : ℕ → ℤ) (hf : ∀ k, Odd (f k)) (m : ℕ) :
    (∑ k ∈ range (2 * m + 1), (-1) ^ k * f k * f (2 * m - k)) % 4 = 1 := by
  have h4 : (4 : ZMod 4) = 0 := rfl
  have hterm : ∀ k, (((-1) ^ k * f k * f (2 * m - k) : ℤ) : ZMod 4) =
      (f k : ZMod 4) + (f (2 * m - k) : ZMod 4) - 1 + 2 * (k : ZMod 4) := by
    intro k
    obtain ⟨r, hr⟩ := odd_cast_zmod_four (hf k)
    obtain ⟨s, hs⟩ := odd_cast_zmod_four (hf (2 * m - k))
    push_cast
    rw [hr, hs, neg_one_pow_zmod_four]
    linear_combination (r * s + (k : ZMod 4) * (r + s) + 2 * (k : ZMod 4) * r * s) * h4
  have htwo : ∀ k, 2 * (f k : ZMod 4) = 2 := by
    intro k
    obtain ⟨r, hr⟩ := odd_cast_zmod_four (hf k)
    rw [hr]
    linear_combination r * h4
  have hrefl : ∑ k ∈ range (2 * m + 1), (f (2 * m - k) : ZMod 4) =
      ∑ k ∈ range (2 * m + 1), (f k : ZMod 4) := by
    rw [← Finset.sum_range_reflect (fun k => (f k : ZMod 4)) (2 * m + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 3
  have hsumf : 2 * ∑ k ∈ range (2 * m + 1), (f k : ZMod 4) = 2 * ((2 * m + 1 : ℕ) : ZMod 4) := by
    rw [Finset.mul_sum]
    simp only [htwo, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hgauss : ∑ k ∈ range (2 * m + 1), (k : ZMod 4) = ((m * (2 * m + 1) : ℕ) : ZMod 4) := by
    rw [← sum_range_id_two_mul_add_one, Nat.cast_sum]
  have hcast : (((∑ k ∈ range (2 * m + 1), (-1) ^ k * f k * f (2 * m - k)) : ℤ) : ZMod 4) = 1 := by
    rw [Int.cast_sum]
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, hrefl,
      ← Finset.mul_sum, hgauss]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hsumf' : ∑ k ∈ range (2 * m + 1), (f k : ZMod 4) + ∑ k ∈ range (2 * m + 1), (f k : ZMod 4)
        = 2 * ((2 * m + 1 : ℕ) : ZMod 4) := by
      rw [← hsumf]
      ring
    rw [hsumf']
    push_cast
    linear_combination ((m : ZMod 4) ^ 2 + (m : ZMod 4)) * h4
  have hval := ZMod.val_intCast (n := 4)
    (∑ k ∈ range (2 * m + 1), (-1) ^ k * f k * f (2 * m - k))
  rw [hcast] at hval
  have hone : (((1 : ZMod 4).val : ℕ) : ℤ) = 1 := rfl
  rw [hone] at hval
  exact_mod_cast hval.symm

/-! ## The conjecture -/

/-- **A105596 conjecture** (OEIS comment, unsigned and undated): with `b = A105595`
(row sums of A105594) and `c(n) = Sum_{k=0..n} (-1)^k b(k) b(n-k)`, for every `m ≥ 0`
`c(2m+1) = 0` and `c(2m) ≡ 1 (mod 4)`; i.e. the listed terms `a(m) = c(2m)` of A105596
are all `≡ 1 (mod 4)` and the suppressed interpolated terms all vanish.
Triage status: proved elsewhere (the congruence rests on Bing Gao's 2026 proof in A105595
that every `b(k)` is odd, re-proved here as `b_odd`). -/
theorem conjecture (m : ℕ) : c (2 * m + 1) = 0 ∧ c (2 * m) % 4 = 1 := by
  refine ⟨?_, ?_⟩
  · exact alt_conv_odd_eq_zero (fun k => (b k : ℤ)) m
  · refine alt_conv_even_mod_four (fun k => (b k : ℤ)) (fun k => ?_) m
    exact (b_odd k).natCast

end Candidates.A105596RowSumsSum
