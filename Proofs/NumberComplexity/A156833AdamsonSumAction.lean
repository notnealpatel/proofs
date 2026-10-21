/-
# A156833 — Adamson: the action of A156348 on `[1,2,3,...]`, Möbius-inverted, detects primes

## OEIS source (re-pulled with `oeis show A156833` and the live `%`-lines, 2026-10-21)

```
NAME:     A054525 * A156348 * [1,2,3,...].
TERMS:    1,2,3,6,5,16,7,24,24,38,11,103,13,68,127,144,17,261,19,404,291,152,23,
          994,370,206,540,1093,29,2195,31,1584,943,338,2543,4808,37,416,1479,
          7371,41,7929,43,4691,8976,596,47,18876,6510,11035,3091
KEYWORDS: nonn
COMMENT (the conjecture):
  Conjecture: for n>1, a(n) = n iff n is prime.
AUTHOR:   _Gary W. Adamson_, Feb 16 2009 (the conjecture is part of the
          original submission; the comment line carries no separate signature)
EXTENSIONS: Extended beyond a(14) by _R. J. Mathar_, Mar 03 2013
PROGRAM (Mathematica, Alcover, Oct 15 2023):
  A054525[n_, k_] := If[Divisible[n, k], MoebiusMu[n/k], 0];
  A156348[n_, k_] := Which[k < 1 || k > n, 0, Mod[n, k] == 0,
                           Binomial[n/k - 2 + k, k - 1], True, 0];
  T[n_, k_] := Sum[A054525[n, j]*A156348[j, k], {j, k, n}];
  a[n_] := Sum[T[n, k]*k, {k, 1, n}];
```

Unfolding the matrix product, `b(d) = ∑_{k ∣ d} k · C(d/k + k - 2, k - 1)` is the
action of A156348 on `[1,2,3,...]` and `a(n) = ∑_{d ∣ n} μ(n/d) · b(d)`.

## Status

Triage (2026-10-21): open — no proof in the entry or the literature as far as
the triage could tell.  Computation (this campaign): the definitions below
reproduce the 51 listed terms and `a(n) = n ↔ n` prime holds for
`2 ≤ n ≤ 6000`, with `a(n) > n` at every composite `n` in that range.

## Proof (formalized below)

Reindexing `d = k·e` gives `a(n) = ∑_{k ∣ n} k · g_k(n/k)` with
`g_k(m) = ∑_{e ∣ m} μ(m/e) C(e + k - 2, k - 1)`.  Then `g_1(m) = [m = 1]`,
`g_k(1) = 1`, and for `k = n + 1 ≥ 2`,
`n! · g_k(m) = ∑_i c_i J_i(m)` where `c_i ≥ 0` are the coefficients of the
rising factorial `X(X+1)⋯(X+n-1)` and `J_i = μ * id^i` are Jordan totients,
which are multiplicative with `J_i(p^(c+1)) = p^((c+1)i) - p^(ci) ≥ 1`.
Since `c_0 = 0` and `∑ c_i = n!`, `g_k(m) ≥ 1`.  For prime `p` only `k = 1`
and `k = p` contribute, giving `a(p) = 0 + p`; a composite `n` has a divisor
`1 < k < n` contributing `k · g_k(n/k) ≥ k > 0` on top of the `k = n` term `n`.
-/
import Mathlib

set_option autoImplicit false

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace Candidates.A156833AdamsonSumAction

/-! ## Definition layer -/

/-- `b d = ∑_{k ∣ d} k · C(d/k + k - 2, k - 1)`: the action of the triangle A156348
(`T(d, k) = C(d/k + k - 2, k - 1)` when `k ∣ d`, else `0`) on `[1,2,3,...]`.
For `k ∣ d` with `d ≠ 0` we have `1 ≤ k` and `1 ≤ d / k`, so neither natural
subtraction truncates. -/
def b (d : ℕ) : ℕ := ∑ k ∈ d.divisors, k * (d / k + k - 2).choose (k - 1)

/-- A156833: `a n = ∑_{d ∣ n} μ(n/d) · b d`, i.e. the Möbius matrix A054525
applied to `b`. -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, μ (n / d) * (b d : ℤ)

/-- Ground truth: the first twelve values of `b`. -/
example :
    (List.range 12).map (fun i => b (i + 1)) = [1, 3, 4, 9, 6, 22, 8, 33, 28, 46, 12, 131] := by
  decide +kernel

/-- Ground truth: the 51 listed terms of A156833. -/
example : (List.range 51).map (fun i => a (i + 1)) =
    [1, 2, 3, 6, 5, 16, 7, 24, 24, 38, 11, 103, 13, 68, 127, 144, 17, 261, 19, 404, 291, 152,
      23, 994, 370, 206, 540, 1093, 29, 2195, 31, 1584, 943, 338, 2543, 4808, 37, 416, 1479,
      7371, 41, 7929, 43, 4691, 8976, 596, 47, 18876, 6510, 11035, 3091] := by
  decide +kernel

/-! ## Inner Möbius transforms -/

/-- `g k m = ∑_{e ∣ m} μ(m/e) · C(e + k - 2, k - 1)`: the Möbius transform in `m`
of the `k`-th column of A156348, so that `a n = ∑_{k ∣ n} k · g k (n / k)`. -/
def g (k m : ℕ) : ℤ := ∑ e ∈ m.divisors, μ (m / e) * ((e + k - 2).choose (k - 1) : ℤ)

/-- The Jordan totient `J_j(m) = ∑_{e ∣ m} μ(m/e) · e^j`. -/
def jordan (j m : ℕ) : ℤ := ∑ e ∈ m.divisors, μ (m / e) * (e : ℤ) ^ j

/-- `jordan j` is the Dirichlet convolution `μ * id^j`. -/
theorem jordan_eq_moebius_mul (j m : ℕ) :
    jordan j m = (μ * ((pow j : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) m := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun x y => μ x * ((pow j : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) y)]
  refine sum_congr rfl fun e he => ?_
  have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
  rw [natCoe_apply, pow_apply]
  simp [he0]

/-- `jordan j` is multiplicative. -/
theorem isMultiplicative_jordan (j : ℕ) :
    (μ * ((pow j : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)).IsMultiplicative :=
  isMultiplicative_moebius.mul isMultiplicative_pow.natCast

/-- `J_j(p^(c+1)) = (p^(c+1))^j - (p^c)^j` for a prime `p`. -/
theorem jordan_prime_pow_succ (j : ℕ) {p : ℕ} (hp : p.Prime) (c : ℕ) :
    jordan j (p ^ (c + 1)) = ((p : ℤ) ^ (c + 1)) ^ j - ((p : ℤ) ^ c) ^ j := by
  unfold jordan
  rw [Nat.sum_divisors_prime_pow hp, sum_range_succ, sum_range_succ]
  have hzero : ∑ x ∈ range c, μ (p ^ (c + 1) / p ^ x) * ((p ^ x : ℕ) : ℤ) ^ j = 0 := by
    refine sum_eq_zero fun x hx => ?_
    have hxc : x < c := mem_range.mp hx
    rw [Nat.pow_div (by omega) hp.pos, moebius_apply_prime_pow hp (by omega),
      if_neg (by omega), zero_mul]
  rw [hzero, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos,
    show c + 1 - c = 1 by omega, Nat.sub_self, pow_one, pow_zero, moebius_apply_prime hp,
    moebius_apply_one]
  push_cast
  ring

/-- For `1 ≤ j` and `m ≠ 0`, the Jordan totient satisfies `1 ≤ J_j(m)`. -/
theorem one_le_jordan {j m : ℕ} (hj : 1 ≤ j) (hm : m ≠ 0) : 1 ≤ jordan j m := by
  rw [jordan_eq_moebius_mul, (isMultiplicative_jordan j).multiplicative_factorization _ hm,
    Finsupp.prod]
  refine prod_induction _ (fun x => 1 ≤ x) (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    le_rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  obtain ⟨c, hc⟩ : ∃ c, m.factorization p = c + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  rw [hc, ← jordan_eq_moebius_mul, jordan_prime_pow_succ j hpp c]
  have hlt : (p ^ c) ^ j < (p ^ (c + 1)) ^ j :=
    Nat.pow_lt_pow_left (Nat.pow_lt_pow_right hpp.one_lt (lt_add_one c)) (by omega)
  have hlt' : ((p : ℤ) ^ c) ^ j < ((p : ℤ) ^ (c + 1)) ^ j := by exact_mod_cast hlt
  linarith

/-- `g 1 m = J_0(m) = [m = 1]`; in particular `g 1 m = 0` for `1 < m`. -/
theorem g_one_left {m : ℕ} (hm : 1 < m) : g 1 m = 0 := by
  have hg : g 1 m = jordan 0 m := by
    unfold g jordan
    refine sum_congr rfl fun e _ => ?_
    simp
  rw [hg, jordan_eq_moebius_mul, pow_zero_eq_zeta, moebius_mul_coe_zeta,
    one_apply_ne (by omega)]

/-- `g k 1 = 1` for `1 ≤ k`. -/
theorem g_one_right {k : ℕ} (hk : 1 ≤ k) : g k 1 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp [g, show 1 + (n + 1) - 2 = n by omega]

/-- The rising-factorial expansion: for `m ≠ 0`,
`n! · g (n+1) m = ∑_{i ≤ n} c_i · J_i(m)` with `c_i` the (natural-number)
coefficients of the Pochhammer polynomial `X (X+1) ⋯ (X+n-1)`. -/
theorem factorial_mul_g_succ (n m : ℕ) :
    (n.factorial : ℤ) * g (n + 1) m =
      ∑ i ∈ range (n + 1), ((ascPochhammer ℕ n).coeff i : ℤ) * jordan i m := by
  unfold g jordan
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e he => ?_
  have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
  have key : ((n.factorial * (e + n - 1).choose n : ℕ) : ℤ) =
      ∑ i ∈ range (n + 1), ((ascPochhammer ℕ n).coeff i : ℤ) * (e : ℤ) ^ i := by
    rw [← Nat.ascFactorial_eq_factorial_mul_choose', ← ascPochhammer_nat_eq_ascFactorial,
      Polynomial.eval_eq_sum_range' (n := n + 1) (by rw [ascPochhammer_natDegree]; omega)]
    push_cast
    rfl
  rw [show e + (n + 1) - 2 = e + n - 1 by omega, Nat.add_sub_cancel]
  calc (n.factorial : ℤ) * (μ (m / e) * ((e + n - 1).choose n : ℤ))
      = μ (m / e) * ((n.factorial * (e + n - 1).choose n : ℕ) : ℤ) := by push_cast; ring
    _ = _ := by rw [key, mul_sum]; refine sum_congr rfl fun i _ => by ring

/-- For `2 ≤ k` and `m ≠ 0`, `1 ≤ g k m`. -/
theorem one_le_g {k m : ℕ} (hk : 2 ≤ k) (hm : m ≠ 0) : 1 ≤ g k m := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  have hdeg : (ascPochhammer ℕ n).natDegree < n + 1 := by
    rw [ascPochhammer_natDegree]; omega
  have hcoeff_sum : ∑ i ∈ range (n + 1), ((ascPochhammer ℕ n).coeff i : ℤ) =
      (n.factorial : ℤ) := by
    have h1 := ascPochhammer_eval_one ℕ n
    rw [Polynomial.eval_eq_sum_range' hdeg] at h1
    simp only [one_pow, mul_one] at h1
    exact_mod_cast h1
  have hcoeff_zero : (ascPochhammer ℕ n).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ascPochhammer_eval_zero, if_neg hn]
  have hlow : (n.factorial : ℤ) ≤ (n.factorial : ℤ) * g (n + 1) m := by
    rw [factorial_mul_g_succ, ← hcoeff_sum]
    refine sum_le_sum fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hcoeff_zero]
    · exact le_mul_of_one_le_right (by positivity) (one_le_jordan hi hm)
  have hfac : (0 : ℤ) < n.factorial := by exact_mod_cast n.factorial_pos
  nlinarith

/-! ## Reindexing `d = k · e` -/

/-- Swapping the order of summation over `k ∣ d ∣ n` (with `d = k · e`):
`a n = ∑_{k ∣ n} k · g k (n / k)`. -/
theorem a_eq_sum_g (n : ℕ) : a n = ∑ k ∈ n.divisors, (k : ℤ) * g k (n / k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a]
  unfold a b g
  push_cast
  simp_rw [mul_sum]
  rw [sum_sigma', sum_sigma']
  symm
  refine sum_bij' (fun y _ => ⟨y.1 * y.2, y.1⟩) (fun x _ => ⟨x.2, x.1 / x.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, e⟩ hy
    simp only [mem_sigma, Nat.mem_divisors] at hy ⊢
    obtain ⟨⟨hk, -⟩, he, -⟩ := hy
    have hke : k * e ∣ n := Nat.mul_dvd_of_dvd_div hk he
    exact ⟨⟨hke, hn.ne'⟩, dvd_mul_right k e, (Nat.pos_of_dvd_of_pos hke hn).ne'⟩
  · rintro ⟨d, k⟩ hx
    simp only [mem_sigma, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hd, -⟩, hk, -⟩ := hx
    exact ⟨⟨hk.trans hd, hn.ne'⟩, Nat.div_dvd_div hk hd,
      (Nat.div_pos (Nat.le_of_dvd hn (hk.trans hd))
        (Nat.pos_of_dvd_of_pos hk (Nat.pos_of_dvd_of_pos hd hn))).ne'⟩
  · rintro ⟨k, e⟩ hy
    simp only [mem_sigma, Nat.mem_divisors] at hy
    have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hy.1.1 hn
    simp [Nat.mul_div_cancel_left e hk0]
  · rintro ⟨d, k⟩ hx
    simp only [mem_sigma, Nat.mem_divisors] at hx
    simp [Nat.mul_div_cancel' hx.2.1]
  · rintro ⟨k, e⟩ hy
    simp only [mem_sigma, Nat.mem_divisors] at hy
    have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hy.1.1 hn
    simp only [Nat.mul_div_cancel_left e hk0, Nat.div_div_eq_div_mul]
    ring

/-! ## The conjecture -/

/-- Every summand of `a_eq_sum_g` is nonnegative: `0 ≤ g k m` for `1 ≤ k` and `m ≠ 0`. -/
theorem g_nonneg {k m : ℕ} (hk : 1 ≤ k) (hm : m ≠ 0) : 0 ≤ g k m := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · obtain rfl : m = 1 := by omega
      rw [g_one_right le_rfl]; norm_num
    · rw [g_one_left hm2]
  · exact zero_le_one.trans (one_le_g hk2 hm)

/-- `a p = p` for every prime `p`. -/
theorem a_prime {p : ℕ} (hp : p.Prime) : a p = p := by
  rw [a_eq_sum_g, hp.divisors, sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos,
    g_one_left hp.one_lt, g_one_right hp.one_lt.le]
  ring

/-- Strengthened converse: `n < a n` for every composite `n` (i.e. `1 < n`, not prime). -/
theorem lt_a_of_not_prime {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) : (n : ℤ) < a n := by
  obtain ⟨k, hkn, hk2, hklt⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
  have hn0 : n ≠ 0 := by omega
  have hsub : ({k, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact Nat.mem_divisors.mpr ⟨hkn, hn0⟩
    · rw [mem_singleton.mp hx]; exact Nat.mem_divisors_self n hn0
  have hnonneg : ∀ i ∈ n.divisors, i ∉ ({k, n} : Finset ℕ) → 0 ≤ (i : ℤ) * g i (n / i) := by
    intro i hi _
    have hin := Nat.mem_divisors.mp hi
    have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hin.1 (by omega)
    exact mul_nonneg (by positivity)
      (g_nonneg hi0 (Nat.div_pos (Nat.le_of_dvd (by omega) hin.1) hi0).ne')
  have hle := sum_le_sum_of_subset_of_nonneg hsub hnonneg
  rw [sum_pair hklt.ne, Nat.div_self (by omega), g_one_right (by omega)] at hle
  have hgk : 1 ≤ g k (n / k) :=
    one_le_g hk2 (Nat.div_pos hklt.le (by omega)).ne'
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [a_eq_sum_g]
  nlinarith

/-- **Adamson's conjecture (A156833, Gary W. Adamson, Feb 16 2009).**

Verbatim: "Conjecture: for n>1, a(n) = n iff n is prime."  Here
`a n = ∑_{d ∣ n} μ(n/d) · b d` with `b d = ∑_{k ∣ d} k · C(d/k + k - 2, k - 1)`
(the action of A156348 on `[1,2,3,...]`).  The guard `1 < n` is from the source:
`a 1 = 1` but `1` is not prime. -/
theorem a_eq_self_iff_prime (n : ℕ) (hn : 1 < n) : a n = n ↔ n.Prime := by
  refine ⟨fun h => ?_, a_prime⟩
  by_contra hnp
  have hlt := lt_a_of_not_prime hn hnp
  rw [h] at hlt
  exact lt_irrefl _ hlt

end Candidates.A156833AdamsonSumAction
