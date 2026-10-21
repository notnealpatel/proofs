/-
# A129364 — `∏_{k ≤ n} (⌊n/k⌋!)^k` divides `∏_{j,k ≤ n} gcd(j,k)`

## OEIS source (re-pulled with `oeis show A129364`, A092287, A066841, A129365;
## author line checked on https://oeis.org/A129364; retrieved 2026-10-21)

```
A129364
NAME:     a(n) = Product_{k = 1..n} A066841(k).
AUTHOR:   Peter Bala, Apr 11 2007
TERMS:    1,2,6,96,480,207360,1451520,2972712960,722369249280,... (offset 1)
FORMULA:  a(n) = Product_{k = 1..n} Product_{d|k} d^(k/d).
FORMULA:  a(n) = Product_{k = 1..n} ((floor(n/k))!)^k.
COMMENT (the conjecture, unattributed in the entry):
  Conjecture: a(n) divides A092287(n) for all n - see comments in A129365.

A066841   a(n) = Product{k|n} k^(n/k); terms 1,2,3,16,5,432,7,2048,...
A092287   a(n) = Product_{j=1..n} Product_{k=1..n} gcd(j,k);
          terms (offset 0) 1,1,2,6,96,480,414720,2903040,...
A129365   a(n) = A092287(n)/A129364(n); terms 1,1,1,1,1,2,2,2,6,48,...
```

Task form of the conjecture: for all `n ≥ 1`,
`Product_{k=1..n} (floor(n/k)!)^k` divides `Product_{j,k<=n} gcd(j,k)` (A092287).

## Literature status (triage)

Proved elsewhere: Adamczewski, arXiv:2608.11941 (cited in A129365, Aug 2026),
with Lean proofs in `epoch-research/LeanOpenProblems-results`
(`oeis_a129365_conjecture_B/_C/_D`).  The self-contained argument below is
the standard Legendre-type valuation count and was written independently here.

## Proof (kernel-checked below)

Fix a prime `p` and `B = n + 1`.  For `q = p^i`:

* Legendre: `v_p((n/k)!) = ∑_{i<B} (n/k)/p^i`, and `(n/k)/q = (n/q)/k`, so
  `v_p(LHS) = ∑_i ∑_{k ≤ n} k · ((n/q)/k)`.
* `v_p(gcd(j,k)) = #{i < B : p^i ∣ j ∧ p^i ∣ k}`, so
  `v_p(RHS) = ∑_i #{(j,k) ≤ n : q ∣ j, q ∣ k} = ∑_i (n/q)^2`.
* With `N = n/q ≤ n`: `k · (N/k) ≤ N` for `k ≤ N` and `N/k = 0` for `k > N`,
  so `∑_{k ≤ n} k · (N/k) ≤ N^2`.

Computational re-validation (python, exact integers): divisibility holds for
all `1 ≤ n ≤ 300`, and the floor formula reproduces the listed A129364 terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A129364ProductFloorDivides

open Finset

/-! ## Definition layer -/

/-- OEIS A066841: `a(k) = ∏_{d ∣ k} d^(k/d)`, product over the positive divisors of `k`. -/
def a066841 (k : ℕ) : ℕ := ∏ d ∈ k.divisors, d ^ (k / d)

/-- OEIS A129364 (entry NAME): `a(n) = ∏_{k=1..n} A066841(k)`. -/
def a129364 (n : ℕ) : ℕ := ∏ k ∈ Icc 1 n, a066841 k

/-- OEIS A092287: `a(n) = ∏_{j=1..n} ∏_{k=1..n} gcd(j,k)`. -/
def a092287 (n : ℕ) : ℕ := ∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, Nat.gcd j k

/-! ### Ground truth against the listed terms -/

example : (List.range 9).map a066841 = [1, 1, 2, 3, 16, 5, 432, 7, 2048] := by decide

example : (List.range 7).map a129364 = [1, 1, 2, 6, 96, 480, 207360] := by decide

example : (List.range 7).map a092287 = [1, 1, 2, 6, 96, 480, 414720] := by decide

/-- Non-vacuity witness: at `n = 6` the quotient is `A129365(6) = 2`. -/
example : a092287 6 = 2 * a129364 6 := by decide

/-! ## Counting lemmas -/

/-- `Icc 1 n = Ioc 0 n` on `ℕ`. -/
theorem Icc_one_eq_Ioc_zero (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- For `N ≤ n`, `∑_{k=1..n} k · ⌊N/k⌋ ≤ N²`: each term with `k ≤ N` is at most `N`, and
the terms with `k > N` vanish. -/
theorem sum_mul_div_le (N n : ℕ) (hN : N ≤ n) : ∑ k ∈ Icc 1 n, k * (N / k) ≤ N * N := by
  have hsplit : ∑ k ∈ Icc 1 n, k * (N / k)
      = ∑ k ∈ Ioc 0 N, k * (N / k) + ∑ k ∈ Ioc N n, k * (N / k) := by
    rw [Icc_one_eq_Ioc_zero, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hN]
  have htail : ∑ k ∈ Ioc N n, k * (N / k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ioc] at hk
    rw [Nat.div_eq_of_lt hk.1, mul_zero]
  have hhead : ∑ k ∈ Ioc 0 N, k * (N / k) ≤ ∑ _k ∈ Ioc 0 N, N :=
    Finset.sum_le_sum fun k _ => Nat.mul_div_le N k
  rw [hsplit, htail, add_zero]
  simpa using hhead

/-- The number of pairs `(j, k) ∈ [1, n]²` with `q ∣ j` and `q ∣ k` is `⌊n/q⌋²`. -/
theorem sum_sum_dvd_and (q n : ℕ) :
    ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (if q ∣ j ∧ q ∣ k then 1 else 0) = (n / q) * (n / q) := by
  have hcard : ∑ j ∈ Icc 1 n, (if q ∣ j then 1 else 0) = n / q := by
    rw [Finset.sum_boole, Nat.cast_id, Icc_one_eq_Ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]
  simp_rw [ite_and, ← hcard, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-! ## `p`-adic valuations of both sides -/

/-- Legendre count for the left side: for a prime `p`,
`v_p(∏_{k=1..n} (⌊n/k⌋!)^k) = ∑_{1 ≤ i ≤ n} ∑_{k=1..n} k · ⌊⌊n/p^i⌋/k⌋`. -/
theorem factorization_prod_factorial_pow (n p : ℕ) (hp : p.Prime) :
    (∏ k ∈ Icc 1 n, (n / k).factorial ^ k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), ∑ k ∈ Icc 1 n, k * (n / p ^ i / k) := by
  rw [Nat.factorization_prod fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _),
    Finsupp.finsetSum_apply]
  have hterm : ∀ k ∈ Icc 1 n, ((n / k).factorial ^ k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), k * (n / p ^ i / k) := by
    intro k _
    have hlog : Nat.log p (n / k) < n + 1 :=
      Nat.lt_succ_of_le ((Nat.log_le_self p (n / k)).trans (Nat.div_le_self n k))
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_factorial hp hlog, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k (p ^ i)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]

/-- Valuation of the gcd product: for a prime `p`,
`v_p(∏_{j,k ≤ n} gcd(j,k)) = ∑_{1 ≤ i ≤ n} ⌊n/p^i⌋²`. -/
theorem factorization_prod_gcd (n p : ℕ) (hp : p.Prime) :
    (∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, Nat.gcd j k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i) := by
  have hne : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := fun j hj k _ =>
    (Nat.gcd_pos_of_pos_left k (Finset.mem_Icc.mp hj).1).ne'
  have hterm : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 n, (Nat.gcd j k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
    intro j hj k hk
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hb : Nat.gcd j k < p ^ (n + 1) :=
      ((Nat.gcd_le_left k (Finset.mem_Icc.mp hj).1).trans hjn).trans_lt
        ((Nat.lt_succ_self n).trans (Nat.lt_pow_self hp.one_lt))
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.pos_of_ne_zero (hne j hj k hk)) hb,
      Finset.card_filter]
    simp_rw [Nat.dvd_gcd_iff]
  rw [Nat.factorization_prod fun j hj => Finset.prod_ne_zero_iff.mpr (hne j hj),
    Finsupp.finsetSum_apply]
  have hrow : ∀ j ∈ Icc 1 n, (∏ k ∈ Icc 1 n, Nat.gcd j k).factorization p
      = ∑ k ∈ Icc 1 n, ∑ i ∈ Ico 1 (n + 1), (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
    intro j hj
    rw [Nat.factorization_prod (hne j hj), Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl (hterm j hj)
  rw [Finset.sum_congr rfl hrow]
  calc ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, ∑ i ∈ Ico 1 (n + 1),
          (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0)
      = ∑ j ∈ Icc 1 n, ∑ i ∈ Ico 1 (n + 1), ∑ k ∈ Icc 1 n,
          (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i ∈ Ico 1 (n + 1), ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
          (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := Finset.sum_comm
    _ = ∑ i ∈ Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i) :=
        Finset.sum_congr rfl fun i _ => sum_sum_dvd_and (p ^ i) n

/-! ## The floor formula for A129364 -/

/-- `((n+1)/k)! = (n/k)! · ((n+1)/k)` if `k ∣ n + 1`, and `= (n/k)!` otherwise. -/
theorem factorial_succ_div (n k : ℕ) :
    ((n + 1) / k).factorial = (n / k).factorial * (if k ∣ n + 1 then (n + 1) / k else 1) := by
  split_ifs with hk
  · have hq : (n + 1) / k = n / k + 1 := by rw [Nat.succ_div, if_pos hk]
    rw [hq, Nat.factorial_succ, mul_comm]
  · rw [Nat.succ_div, if_neg hk, add_zero, mul_one]

/-- The divisors of `m` inside `[1, m]` are exactly `m.divisors`. -/
theorem filter_Icc_dvd_eq_divisors (m : ℕ) : {k ∈ Icc 1 m | k ∣ m} = m.divisors := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hk1, _⟩, hkm⟩
    exact ⟨hkm, by omega⟩
  · rintro ⟨hkm, hm⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hkm (Nat.pos_of_ne_zero hm), Nat.le_of_dvd
      (Nat.pos_of_ne_zero hm) hkm⟩, hkm⟩

/-- One step of the floor product: passing from `n` to `n + 1` multiplies
`∏_{k} (⌊n/k⌋!)^k` by `A066841(n+1) = ∏_{d ∣ n+1} d^((n+1)/d)`. -/
theorem prod_floor_succ (n : ℕ) :
    ∏ k ∈ Icc 1 (n + 1), ((n + 1) / k).factorial ^ k
      = (∏ k ∈ Icc 1 n, (n / k).factorial ^ k) * ∏ d ∈ (n + 1).divisors, d ^ ((n + 1) / d) := by
  have hext : ∏ k ∈ Icc 1 (n + 1), (n / k).factorial ^ k
      = ∏ k ∈ Icc 1 n, (n / k).factorial ^ k := by
    rw [Finset.prod_Icc_succ_top (by omega), Nat.div_eq_of_lt (Nat.lt_succ_self n),
      Nat.factorial_zero, one_pow, mul_one]
  have hdiv : ∏ k ∈ Icc 1 (n + 1), (if k ∣ n + 1 then (n + 1) / k else 1) ^ k
      = ∏ d ∈ (n + 1).divisors, d ^ ((n + 1) / d) := by
    have hite : ∀ k ∈ Icc 1 (n + 1), (if k ∣ n + 1 then (n + 1) / k else 1) ^ k
        = if k ∣ n + 1 then ((n + 1) / k) ^ k else 1 := fun k _ => by
      split_ifs <;> simp
    rw [Finset.prod_congr rfl hite, ← Finset.prod_filter, filter_Icc_dvd_eq_divisors,
      ← Nat.prod_div_divisors (n + 1) fun d => d ^ ((n + 1) / d)]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Nat.div_div_self (Nat.mem_divisors.mp hk).1 (Nat.succ_ne_zero n)]
  simp_rw [factorial_succ_div n, mul_pow]
  rw [Finset.prod_mul_distrib, hext, hdiv]

/-- The entry's second formula: `A129364(n) = ∏_{k=1..n} (⌊n/k⌋!)^k`. -/
theorem a129364_eq_prod_factorial_pow (n : ℕ) :
    a129364 n = ∏ k ∈ Icc 1 n, (n / k).factorial ^ k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [a129364, Finset.prod_Icc_succ_top (by omega), ← a129364, ih, prod_floor_succ, a066841]

/-! ## The conjecture -/

/-- **A129364 conjecture (comment in A129364; see A129365), floor form.**

Verbatim (task form): "For all n >= 1, Product_{k=1..n} (floor(n/k)!)^k divides
Product_{j,k<=n} gcd(j,k) (A092287)."

Proved here for every `n : ℕ`; the case `n = 0` (outside the conjecture's range) is the
trivial `1 ∣ 1`.  Proof: compare `p`-adic valuations,
`∑_i ∑_k k · ⌊⌊n/p^i⌋/k⌋ ≤ ∑_i ⌊n/p^i⌋²`. -/
theorem prod_factorial_pow_dvd_prod_gcd (n : ℕ) :
    (∏ k ∈ Icc 1 n, (n / k).factorial ^ k) ∣ ∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, Nat.gcd j k := by
  have hL : (∏ k ∈ Icc 1 n, (n / k).factorial ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)
  have hR : (∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 n, Nat.gcd j k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => Finset.prod_ne_zero_iff.mpr fun k _ =>
      (Nat.gcd_pos_of_pos_left k (Finset.mem_Icc.mp hj).1).ne'
  refine (Nat.factorization_prime_le_iff_dvd hL hR).mp fun p hp => ?_
  rw [factorization_prod_factorial_pow n p hp, factorization_prod_gcd n p hp]
  exact Finset.sum_le_sum fun i _ => sum_mul_div_le (n / p ^ i) n (Nat.div_le_self n (p ^ i))

/-- **A129364 conjecture (entry form): `A129364(n) ∣ A092287(n)` for all `n`.**

Verbatim: "Conjecture: a(n) divides A092287(n) for all n - see comments in A129365."
(A129364, entry by Peter Bala, Apr 11 2007; the comment is unattributed.)  Here
`a129364` is the entry's NAME definition `∏_{k=1..n} A066841(k)`, bridged to the floor form
by `a129364_eq_prod_factorial_pow`. -/
theorem a129364_dvd_a092287 (n : ℕ) : a129364 n ∣ a092287 n := by
  rw [a129364_eq_prod_factorial_pow, a092287]
  exact prod_factorial_pow_dvd_prod_gcd n

end Candidates.A129364ProductFloorDivides
