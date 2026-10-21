/-
# A367865 — Yanev: a radical-sum formula for `Σ_{d|n} d φ(d) μ(d)²`

## OEIS source (`oeis show A367865`, live entry https://oeis.org/A367865,
## retrieved 2026-10-21)

```
NAME:     a(n) = Sum_{d|n} d * phi(d) * mu(d)^2.
TERMS:    1,3,7,3,21,21,43,3,7,63,111,21,157,129,147,3,273,21,343,63,301,
          333,507,21,21,471,7,129,813,441,931,3,777,819,903,21,1333,1029,
          1099,63,1641,903,1807,333,147,1521,2163,21,43,63,1911,471,2757,
          21,2331,129,2401,2439
KEYWORDS: nonn,easy,mult
COMMENT:
  Inverse Möbius transform of n * phi(n) * mu(n)^2.
FORMULA:
  Multiplicative with a(p^e) = p^2 - p + 1. - _Amiram Eldar_, Dec 04 2023
FORMULA (the conjecture):
  Conjecture: a(n) = (rad(n)/n) * Sum_{k=1..n} rad(n*k)/rad(k), where rad
  is A007947. - _Velin Yanev_, Sep 14 2025
XREFS:
  Cf. A000010 (phi), A007947 (rad), A008966 (mu^2), A202535.
```

## Status

Triage status: open.  The entry gives no proof of Yanev's formula and the
triage found none in the literature; no novelty claim is made beyond that
search.  Computational re-validation (Python, exact rationals): the
identity holds for every `1 ≤ n ≤ 1500` (with `rad(n k)` computed
directly for `n ≤ 300`).

## Result in this file

The conjecture is proved (`yanev_conjecture`).  Proof outline.
1. Both sides are products over the primes of `n`: for any `g`,
   `Σ_{d | n, d squarefree} Π_{p | d} g(p) = Π_{p | n} (1 + g(p))`
   (`sum_squarefree_divisors_prod`).
2. Left side: for squarefree `d`, `μ(d)² = 1` and `d φ(d) = Π_{p|d} p(p-1)`,
   so `a(n) = Π_{p | n} (1 + p(p - 1))` (`a_eq_prod`).
3. Right side: `rad(n k) rad(gcd(n,k)) = rad(n) rad(k)` (`rad_mul_mul_rad_gcd`)
   and `1 / rad(m) = Σ_{d | m, d squarefree} Π_{p | d} (1/p - 1)`
   (`one_div_rad_eq_sum`); exchanging the sums over `k` and `d` and counting
   the multiples of `d` in `[1, n]` gives
   `rad(n)² Σ_{d | n, d squarefree} Π_{p | d} (1/p - 1)/p
     = Π_{p | n} p² (1 + (1/p - 1)/p) = Π_{p | n} (p² - p + 1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A367865Rad

open Finset

/-! ## Definitions -/

/-- The radical `rad(n)` (OEIS A007947): the product of the distinct primes
dividing `n` (so `rad 1 = 1`). -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- OEIS A367865: `a(n) = Σ_{d | n} d · φ(d) · μ(d)²`, as an integer. -/
def a (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) * (Nat.totient d : ℤ) * (ArithmeticFunction.moebius d) ^ 2

/-! ## Ground truth -/

example : rad 1 = 1 := by decide +kernel
example : rad 12 = 6 := by decide +kernel
example : rad 30 = 30 := by decide +kernel

/-- The first twelve listed terms `1,3,7,3,21,21,43,3,7,63,111,21`. -/
example : (List.range 12).map (fun i => a (i + 1)) = [1, 3, 7, 3, 21, 21, 43, 3, 7, 63, 111, 21] := by
  decide +kernel

/-! ## Helper lemmas -/

/-- Sum over the squarefree divisors of a multiplicative-on-primes product:
`Σ_{d | n, d squarefree} Π_{p | d} g(p) = Π_{p | n} (1 + g(p))` for `n ≠ 0`. -/
theorem sum_squarefree_divisors_prod (n : ℕ) (hn : n ≠ 0) (g : ℕ → ℚ) :
    ∑ d ∈ n.divisors with Squarefree d, ∏ p ∈ d.primeFactors, g p
      = ∏ p ∈ n.primeFactors, (1 + g p) := by
  rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq, Finset.prod_one_add]
  have hfs : (↑n.primeFactorsList : Multiset ℕ).toFinset = n.primeFactors := by
    rw [List.toFinset_coe, Nat.toFinset_factors]
  rw [hfs]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hprod : i.val.prod = ∏ p ∈ i, p := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  have hprime : ∀ p ∈ i, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hi hp)
  rw [hprod, Nat.primeFactors_prod hprime]

/-- The radical is positive. -/
theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- The radical, cast to `ℚ`, is the product of the prime factors in `ℚ`. -/
theorem cast_rad (n : ℕ) : (rad n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) := by
  rw [rad, Nat.cast_prod]

/-- For squarefree `d`, `d · φ(d) = Π_{p | d} p (p - 1)` in `ℚ`. -/
theorem mul_totient_of_squarefree (d : ℕ) (hd : Squarefree d) :
    (d : ℚ) * (Nat.totient d : ℚ) = ∏ p ∈ d.primeFactors, ((p : ℚ) * ((p : ℚ) - 1)) := by
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd
  have hd0 : d ≠ 0 := hd.ne_zero
  have htot : Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors d
    rw [hprod, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h
  have hcast : (Nat.totient d : ℚ) = ∏ p ∈ d.primeFactors, ((p : ℚ) - 1) := by
    rw [htot, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hdcast : (d : ℚ) = ∏ p ∈ d.primeFactors, (p : ℚ) := by
    rw [← cast_rad, rad, hprod]
  rw [hcast, hdcast, ← Finset.prod_mul_distrib]

/-- Left side in product form: `a(n) = Π_{p | n} (1 + p (p - 1))` for `n ≠ 0`. -/
theorem a_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (a n : ℚ) = ∏ p ∈ n.primeFactors, (1 + (p : ℚ) * ((p : ℚ) - 1)) := by
  rw [← sum_squarefree_divisors_prod n hn]
  have hfilter : ∑ d ∈ n.divisors with Squarefree d,
      (d : ℚ) * (Nat.totient d : ℚ) * ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2
      = ∑ d ∈ n.divisors,
      (d : ℚ) * (Nat.totient d : ℚ) * ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2 := by
    refine Finset.sum_filter_of_ne fun d _ hne => ?_
    by_contra hsq
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq] at hne
    simp at hne
  rw [a]
  push_cast
  rw [← hfilter]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hsq : Squarefree d := (Finset.mem_filter.mp hd).2
  have hmu : ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hmu, mul_one, mul_totient_of_squarefree d hsq]

/-- `rad(n k) · rad(gcd(n, k)) = rad(n) · rad(k)` for nonzero `n, k`. -/
theorem rad_mul_mul_rad_gcd (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    rad (n * k) * rad (Nat.gcd n k) = rad n * rad k := by
  unfold rad
  rw [Nat.primeFactors_mul hn hk, Nat.primeFactors_gcd hn hk, Finset.prod_union_inter]

/-- `1 / rad(m) = Σ_{d | m, d squarefree} Π_{p | d} (1/p - 1)` for `m ≠ 0`. -/
theorem one_div_rad_eq_sum (m : ℕ) (hm : m ≠ 0) :
    (1 : ℚ) / rad m
      = ∑ d ∈ m.divisors with Squarefree d, ∏ p ∈ d.primeFactors, ((1 : ℚ) / p - 1) := by
  rw [sum_squarefree_divisors_prod m hm, cast_rad]
  simp only [add_sub_cancel, Finset.prod_div_distrib, Finset.prod_const_one]

/-- Exchange of summation: for `n ≠ 0`,
`Σ_{k=1}^{n} 1 / rad(gcd(n, k)) = Σ_{d | n, d squarefree} (Π_{p | d} (1/p - 1)) · (n / d)`. -/
theorem sum_Icc_one_div_rad_gcd (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / rad (Nat.gcd n k)
      = ∑ d ∈ n.divisors with Squarefree d,
          (∏ p ∈ d.primeFactors, ((1 : ℚ) / p - 1)) * ((n : ℚ) / d) := by
  set G : ℕ → ℚ := fun d => ∏ p ∈ d.primeFactors, ((1 : ℚ) / p - 1) with hG
  have hk : ∀ k ∈ Finset.Icc 1 n, (1 : ℚ) / rad (Nat.gcd n k)
      = ∑ d ∈ n.divisors with Squarefree d, if d ∣ k then G d else 0 := by
    intro k _
    rw [one_div_rad_eq_sum _ (Nat.gcd_ne_zero_left hn), ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨fun ⟨⟨⟨h1, h2⟩, _⟩, h3⟩ => ⟨⟨⟨h1, hn⟩, h3⟩, h2⟩,
      fun ⟨⟨⟨h1, _⟩, h3⟩, h2⟩ => ⟨⟨⟨h1, h2⟩, Nat.gcd_ne_zero_left hn⟩, h3⟩⟩
  rw [Finset.sum_congr rfl hk, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_zero_of_dvd_ne_zero hn hdn)
  have hcard : #{k ∈ Finset.Icc 1 n | d ∣ k} = n / d := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div n d]
    rfl
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_div hdn hd0, mul_comm]

/-- Each summand on the right: `rad(n k) / rad(k) = rad(n) · (1 / rad(gcd(n, k)))`. -/
theorem rad_mul_div_rad (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    (rad (n * k) : ℚ) / rad k = rad n * (1 / rad (Nat.gcd n k)) := by
  have h := rad_mul_mul_rad_gcd n k hn hk
  have hq : (rad (n * k) : ℚ) * rad (Nat.gcd n k) = rad n * rad k := by
    exact_mod_cast h
  have hk0 : (rad k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (rad_pos k).ne'
  have hg0 : (rad (Nat.gcd n k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (rad_pos _).ne'
  field_simp
  linear_combination hq

/-! ## The conjecture -/

/-- **Yanev's conjecture (A367865, Velin Yanev, Sep 14 2025).**

Verbatim: "Conjecture: a(n) = (rad(n)/n) * Sum_{k=1..n} rad(n*k)/rad(k), where
rad is A007947."  Here `a(n) = Σ_{d | n} d φ(d) μ(d)²` and the identity is
taken in `ℚ` for every `n ≥ 1` (the entry's offset). -/
theorem yanev_conjecture (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (rad n : ℚ) / n * ∑ k ∈ Finset.Icc 1 n, (rad (n * k) : ℚ) / rad k := by
  have hn0 : n ≠ 0 := hn.ne'
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hsum : ∑ k ∈ Finset.Icc 1 n, (rad (n * k) : ℚ) / rad k
      = rad n * ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / rad (Nat.gcd n k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    exact rad_mul_div_rad n k hn0 hk0
  have hterm : ∀ d ∈ n.divisors.filter Squarefree,
      (∏ p ∈ d.primeFactors, ((1 : ℚ) / p - 1)) * ((n : ℚ) / d)
        = n * ∏ p ∈ d.primeFactors, (((1 : ℚ) / p - 1) / p) := by
    intro d hd
    have hsq : Squarefree d := (Finset.mem_filter.mp hd).2
    have hdcast : (d : ℚ) = ∏ p ∈ d.primeFactors, (p : ℚ) := by
      rw [← cast_rad, rad, Nat.prod_primeFactors_of_squarefree hsq]
    rw [Finset.prod_div_distrib, ← hdcast]
    ring
  rw [hsum, sum_Icc_one_div_rad_gcd n hn0, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_squarefree_divisors_prod n hn0, a_eq_prod n hn0, cast_rad]
  field_simp
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  field_simp
  ring

/-- Non-vacuity: the hypothesis `0 < n` is met at `n = 1`, the entry's offset. -/
example : (a 1 : ℚ) = (rad 1 : ℚ) / 1 * ∑ k ∈ Finset.Icc 1 1, (rad (1 * k) : ℚ) / rad k :=
  yanev_conjecture 1 Nat.one_pos

end Candidates.A367865Rad
