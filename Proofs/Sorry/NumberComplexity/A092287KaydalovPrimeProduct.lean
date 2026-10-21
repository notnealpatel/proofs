/-
# A092287 — Kaydalov: prime factorization of the rectangular gcd product

## OEIS source (retrieved with `oeis show A092287`, 2026-10-21)

```
NAME:     a(n) = Product_{j=1..n} Product_{k=1..n} gcd(j,k).
TERMS:    1,1,2,6,96,480,414720,2903040,5945425920,4334215495680,...
COMMENT (Bala's square case):
  Conjecture: Let p be a prime and let ordp(n,p) denote the exponent of the
  highest power of p that divides n. [...] Then we conjecture that the prime
  factorization of a(n) is given by the formula: ordp(a(n),p) =
  (floor(n/p))^2 + (floor(n/p^2))^2 + (floor(n/p^3))^2 + .... [...]
  - _Peter Bala_, Apr 16 2007
COMMENT:
  The conjecture is correct. - _Charles R Greathouse IV_, Apr 02 2013
COMMENT (the target conjecture):
  Conjecture: For a product over a rectangle, f(n,m) = Product_{j=1..n}
  Product_{k=1..m} gcd(j,k), a factorization similar to the one given above
  for the square case takes place: ordp(f(n,m),p) = floor(n/p)*floor(m/p) +
  floor(n/p^2)*floor(m/p^2) + .... By way of directly computing the values of
  f(n,m), it can be verified that the conjecture holds at least for all
  1 <= m <= n <= 200. - _Andrey Kaydalov_, Mar 11 2019
```

## Status

Triage: open (no printed proof in the entry; Greathouse marked only the square
case "correct", without a proof).  Re-validated computationally on
2026-10-21 for all `1 ≤ n, m ≤ 70` and every prime `p < 60` (83300 cases), and
by direct factorization of `f(n,m)` for `1 ≤ n, m ≤ 24`.

This file proves the conjecture (`kaydalov_padicValNat_eq_sum`) with the
standard Legendre-type double counting:
`v_p(gcd(j,k)) = #{e ≥ 1 : p^e ∣ j ∧ p^e ∣ k}`, then swapping the sums and
counting multiples of `p^e` in `[1, n]` and `[1, m]`.

The infinite sum `Σ_{e ≥ 1}` is represented by its partial sums over
`Finset.Ico 1 b` for any `b` with `n < p ^ b`; all terms with `e ≥ b` vanish
because `n / p ^ e = 0`, exactly as in Mathlib's Legendre formula
`Nat.Prime.multiplicity_factorial`.  The hypotheses `n, m ≥ 1` of the comment
are dropped: at `n = 0` or `m = 0` both sides are `0`, so the proved statement
is the stated one for all `n m : ℕ`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A092287KaydalovPrimeProduct

open Finset

/-! ## Definition layer -/

/-- Kaydalov's rectangular product
`f(n,m) = Product_{j=1..n} Product_{k=1..m} gcd(j,k)`. -/
def rectGcdProd (n m : ℕ) : ℕ :=
  ∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 m, Nat.gcd j k

/-- The sequence A092287: `a(n) = Product_{j=1..n} Product_{k=1..n} gcd(j,k)`,
the square case of `rectGcdProd`. -/
def a (n : ℕ) : ℕ :=
  rectGcdProd n n

-- Ground truth: the first eight DATA terms `1, 1, 2, 6, 96, 480, 414720, 2903040`.
example : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 6 ∧ a 4 = 96 ∧ a 5 = 480 ∧
    a 6 = 414720 ∧ a 7 = 2903040 := by
  decide

-- Ground truth for a genuinely rectangular value (computed independently in
-- Python): `f(4,6) = f(6,4) = 1152 = 2^7 * 3^2` and `f(3,8) = 144`.
example : rectGcdProd 4 6 = 1152 ∧ rectGcdProd 6 4 = 1152 ∧ rectGcdProd 3 8 = 144 := by
  decide

/-! ## Helper lemmas -/

/-- For `x ≠ 0` with `x < p ^ b`, the `p`-adic valuation of `x` counts the
exponents `e ∈ [1, b)` with `p ^ e ∣ x`. -/
theorem padicValNat_eq_card_Ico_filter {p x b : ℕ} (hp : p.Prime) (hx : x ≠ 0)
    (hxb : x < p ^ b) :
    padicValNat p x = #{e ∈ Ico 1 b | p ^ e ∣ x} := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hvb : padicValNat p x < b := by
    have hle : p ^ padicValNat p x ≤ x :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hx) pow_padicValNat_dvd
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle hxb)
  have hfilter : ({e ∈ Ico 1 b | p ^ e ∣ x} : Finset ℕ) =
      Ico 1 (padicValNat p x + 1) := by
    ext e
    simp only [mem_filter, mem_Ico, padicValNat_dvd_iff_le hx]
    omega
  rw [hfilter, Nat.card_Ico]
  omega

/-- The number of multiples of `d` in `[1, N]`, written as a sum of indicators,
is `N / d`. -/
theorem sum_Icc_indicator_dvd (d N : ℕ) :
    ∑ j ∈ Icc 1 N, (if d ∣ j then 1 else 0) = N / d := by
  have hIcc : Icc 1 N = Ioc 0 N := by
    ext x
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [← Finset.card_filter, ← Nat.Ioc_filter_dvd_card_eq_div, hIcc]

/-- The `p`-adic valuation of `rectGcdProd n m` is the double sum of the
valuations of the factors `gcd(j,k)`. -/
theorem padicValNat_rectGcdProd_eq_sum_sum (p n m : ℕ) (hp : p.Prime) :
    padicValNat p (rectGcdProd n m)
      = ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 m, padicValNat p (Nat.gcd j k) := by
  have hne : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by
    intro j hj k _
    simp only [mem_Icc] at hj
    exact Nat.gcd_ne_zero_left (by omega)
  have hrow : ∀ j ∈ Icc 1 n, ∏ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := fun j hj =>
    Finset.prod_ne_zero_iff.mpr (hne j hj)
  rw [rectGcdProd, ← Nat.factorization_def _ hp, Nat.factorization_prod hrow,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.factorization_prod (hne j hj), Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ => Nat.factorization_def _ hp

/-! ## The conjecture -/

/-- **Kaydalov's conjecture (A092287, Andrey Kaydalov, Mar 11 2019), proved.**

Verbatim: "For a product over a rectangle, f(n,m) = Product_{j=1..n}
Product_{k=1..m} gcd(j,k), [...] ordp(f(n,m),p) = floor(n/p)*floor(m/p) +
floor(n/p^2)*floor(m/p^2) + ...."

For every prime `p` and every cutoff `b` with `n < p ^ b` (beyond which every
term `⌊n/p^e⌋⌊m/p^e⌋` vanishes), `v_p(f(n,m)) = Σ_{e=1}^{b-1} ⌊n/p^e⌋⌊m/p^e⌋`.
Holds for all `n m : ℕ` (the source's `n, m ≥ 1` is not needed). -/
theorem kaydalov_padicValNat_eq_sum (p n m b : ℕ) (hp : p.Prime) (hnb : n < p ^ b) :
    padicValNat p (rectGcdProd n m) = ∑ e ∈ Ico 1 b, (n / p ^ e) * (m / p ^ e) := by
  have hcount : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 m, padicValNat p (Nat.gcd j k)
      = ∑ e ∈ Ico 1 b, (if p ^ e ∣ j then 1 else 0) * (if p ^ e ∣ k then 1 else 0) := by
    intro j hj k _
    simp only [mem_Icc] at hj
    have hg0 : Nat.gcd j k ≠ 0 := Nat.gcd_ne_zero_left (by omega)
    have hgb : Nat.gcd j k < p ^ b :=
      lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left j k)) (by omega)
    rw [padicValNat_eq_card_Ico_filter hp hg0 hgb, Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Nat.dvd_gcd_iff]
    split_ifs <;> simp_all
  rw [padicValNat_rectGcdProd_eq_sum_sum p n m hp,
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl (hcount j hj)]
  calc ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 m, ∑ e ∈ Ico 1 b,
          (if p ^ e ∣ j then 1 else 0) * (if p ^ e ∣ k then 1 else 0)
      = ∑ j ∈ Icc 1 n, ∑ e ∈ Ico 1 b, ∑ k ∈ Icc 1 m,
          (if p ^ e ∣ j then 1 else 0) * (if p ^ e ∣ k then 1 else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ e ∈ Ico 1 b, ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 m,
          (if p ^ e ∣ j then 1 else 0) * (if p ^ e ∣ k then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ e ∈ Ico 1 b, (n / p ^ e) * (m / p ^ e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← sum_Icc_indicator_dvd (p ^ e) n, ← sum_Icc_indicator_dvd (p ^ e) m,
          Finset.sum_mul_sum]

/-- Kaydalov's formula with the canonical cutoff `b = n + 1` (no free bound):
`v_p(f(n,m)) = Σ_{e=1}^{n} ⌊n/p^e⌋⌊m/p^e⌋` for every prime `p`. -/
theorem kaydalov_padicValNat_eq_sum_Ico_succ (p n m : ℕ) (hp : p.Prime) :
    padicValNat p (rectGcdProd n m) = ∑ e ∈ Ico 1 (n + 1), (n / p ^ e) * (m / p ^ e) := by
  have hn : n < p ^ (n + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ n))
  exact kaydalov_padicValNat_eq_sum p n m (n + 1) hp hn

/-- **Bala's square case (A092287, Peter Bala, Apr 16 2007)**, recovered as a
corollary: `v_p(a(n)) = Σ_{e ≥ 1} ⌊n/p^e⌋^2`, with the sum cut at any `b` with
`n < p ^ b`. -/
theorem bala_padicValNat_eq_sum (p n b : ℕ) (hp : p.Prime) (hnb : n < p ^ b) :
    padicValNat p (a n) = ∑ e ∈ Ico 1 b, (n / p ^ e) ^ 2 := by
  rw [a, kaydalov_padicValNat_eq_sum p n n b hp hnb]
  exact Finset.sum_congr rfl fun e _ => (sq (n / p ^ e)).symm

/-! ## Sanity layer -/

-- Non-vacuity: the hypotheses are jointly satisfiable (`p = 2`, `n = 4`,
-- `b = 3`, `4 < 2^3`), and both sides are checked independently of the
-- theorem at the rectangular instance `f(4,6) = 1152 = 2^7 * 3^2`:
-- `v_2(1152) = 7 = 2*3 + 1*1` and `v_3(1152) = 2 = 1*2`.
example : (4 : ℕ) < 2 ^ 3 ∧ Nat.Prime 2 := ⟨by norm_num, Nat.prime_two⟩

example : padicValNat 2 1152 = 7 ∧ ∑ e ∈ Ico 1 3, (4 / 2 ^ e) * (6 / 2 ^ e) = 7 := by
  refine ⟨?_, by decide⟩
  rw [show (1152 : ℕ) = 2 ^ 7 * 9 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

example : padicValNat 3 1152 = 2 ∧ ∑ e ∈ Ico 1 2, (4 / 3 ^ e) * (6 / 3 ^ e) = 2 := by
  refine ⟨?_, by decide⟩
  rw [show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end Candidates.A092287KaydalovPrimeProduct
