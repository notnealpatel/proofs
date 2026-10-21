/-
# A364883 — Wilson's conjectures on the Fermat-quotient divisibility index

## OEIS source (retrieved 2026-10-21 with `oeis show A364883` and the live
## entry `https://oeis.org/A364883/internal`)

```
NAME:     Consider the Fermat quotient for base n: Fq(n,k) = (n^(p - 1) - 1)/p,
          where p = prime(k), for k >= 1. a(n) is the least k >= 1 such that
          Fq(n,j) is divisible by n^2 - 1 for all j >= k.
OFFSET:   2
TERMS:    3,3,4,4,5,5,5,4,6,6,7,7,7,5,8,8,9,9,9,6,10,10,10,7,7,7,11,11,12,12,
          12,8,8,8,13,13,13,9,14,14,15,15,15,10,16,16,16,5,8,8,17,17,17,6,9,
          11,18,18,19,19,19,12,7,7,20,20,20,10,21,21,22,22,22,13,9,9,23,23,23
AUTHOR:   Robert G. Wilson v, Aug 17 2023
COMMENT (the conjecture; the entry gives no separate attribution or date, so
         it is the author's, Robert G. Wilson v, Aug 17 2023):
  Conjecture: numbers appear in the sequence only a finite number of times.
  Terms appear in runs of length 1, 2, or 3, never more. The first time a
  term k appears is when the index is even. The terms appear for the first
  time in their natural order.
PROGRAM (Mathematica, the reading of "divisible" used here):
  ... While[p = Prime@ k; PowerMod[n, p - 1, (n^2 - 1)*p] == 1, k--]; ++k] ...
```

## Status

Triage: open (no proof in the entry or the literature found).

This module proves the closed form `a(n) = π(P(n^3 - n)) + 1`, where `P` is the
greatest prime factor (`a_eq`), and from it three of the four printed claims
outright: runs have length at most 3 (`no_run_of_four`), every first
appearance is at an even index (`even_of_isFirstOccurrence`), and first
appearances come in increasing order of value (`lt_of_isFirstOccurrence`).

The remaining claim, that each value occurs only finitely often, is reduced
(`finite_occurrences`) to Størmer's theorem for three consecutive smooth
integers (`stormer_consecutive_triples`), which is the single `sorry`.  That
theorem is classical (C. Størmer, 1897; via Pell equations) but not available
in Mathlib.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A364883PrintedValueOccurs

/-! ## Definition layer -/

/-- `FqDivisible n p`: the Fermat quotient `(n^(p-1) - 1)/p` is an integer divisible by
`n^2 - 1`, i.e. `p * (n^2 - 1) ∣ n^(p-1) - 1` (computed in `ℤ`, so no truncated
subtraction occurs).  This is exactly the Mathematica test
`PowerMod[n, p - 1, (n^2 - 1)*p] == 1` of the entry. -/
def FqDivisible (n p : ℕ) : Prop :=
  ((p : ℤ) * ((n : ℤ) ^ 2 - 1)) ∣ (n : ℤ) ^ (p - 1) - 1

/-- `primeAt k = prime(k)`, the `k`-th prime, one-indexed (`primeAt 1 = 2`); only used at
`k ≥ 1`. -/
noncomputable def primeAt (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A364883: `a n` is the least `k ≥ 1` such that `FqDivisible n (prime j)` for all
`j ≥ k`.  The entry has offset `2`; for `n ≥ 2` the set is nonempty (`a_eq`). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ ∀ j, k ≤ j → FqDivisible n (primeAt j)}

/-- The product `(n - 1) n (n + 1) = n^3 - n` (for `n ≥ 1`). -/
def N (n : ℕ) : ℕ := (n - 1) * n * (n + 1)

/-- The greatest prime factor of `N n = n^3 - n` (`0` if there is none). -/
def gpf (n : ℕ) : ℕ := (N n).primeFactors.sup id

/-! ## The bad primes are exactly the divisors of `n^3 - n` -/

/-- `N n` cast to `ℤ` is `n (n^2 - 1)`. -/
theorem N_cast (n : ℕ) (hn : 1 ≤ n) : ((N n : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) ^ 2 - 1) := by
  simp only [N]
  push_cast [Nat.cast_sub hn]
  ring

/-- If `p ∣ n` the Fermat quotient is not an integer. -/
theorem not_fqDivisible_of_dvd_n (n p : ℕ) (hp : p.Prime) (hdvd : (p : ℤ) ∣ (n : ℤ)) :
    ¬ FqDivisible n p := by
  intro h
  have h1 : (p : ℤ) ∣ (n : ℤ) ^ (p - 1) - 1 := dvd_trans (dvd_mul_right _ _) h
  have h2 : (p : ℤ) ∣ (n : ℤ) ^ (p - 1) :=
    dvd_pow hdvd (by have := hp.two_le; omega)
  have h3 : (p : ℤ) ∣ 1 := by
    have h4 := dvd_sub h2 h1
    simpa using h4
  have h5 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
  have := hp.one_lt
  omega

/-- `p = 2` never works: `2 (n^2 - 1) ∤ n - 1` for `n ≥ 2`. -/
theorem not_fqDivisible_two (n : ℕ) (hn : 2 ≤ n) : ¬ FqDivisible n 2 := by
  intro h
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℤ) < (n : ℤ) ^ (2 - 1) - 1 := by
    norm_num; omega
  have hle := Int.le_of_dvd hpos h
  norm_num at hle
  nlinarith

/-- For an odd prime `p ∣ n^2 - 1`: writing `n^(p-1) - 1 = (n^2 - 1) S` with
`S = ∑_{i < (p-1)/2} n^(2i) ≡ (p-1)/2 (mod p)`, the prime `p` does not divide `S`. -/
theorem not_fqDivisible_of_dvd_sq_sub_one (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ (n : ℤ) ^ 2 - 1) : ¬ FqDivisible n p := by
  intro h
  unfold FqDivisible at h
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hpm : p - 1 = 2 * k := by omega
  have hm0 : 0 < k := by have := hp.two_le; omega
  set x : ℤ := (n : ℤ) ^ 2 with hx
  have hx1 : x - 1 ≠ 0 := by
    have h4 : (4 : ℤ) ≤ x := by
      have : (2 : ℤ) ≤ n := by exact_mod_cast hn
      nlinarith
    omega
  have hpow : (n : ℤ) ^ (p - 1) - 1 = (∑ i ∈ Finset.range k, x ^ i) * (x - 1) := by
    rw [geom_sum_mul, hpm, pow_mul]
  rw [hpow, mul_comm (p : ℤ), mul_comm (∑ i ∈ Finset.range k, x ^ i)] at h
  have hS : (p : ℤ) ∣ ∑ i ∈ Finset.range k, x ^ i := (mul_dvd_mul_iff_left hx1).mp h
  have hxz : ((x : ℤ) : ZMod p) = 1 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at hz ⊢
    linear_combination hz
  have hSz : ((∑ i ∈ Finset.range k, x ^ i : ℤ) : ZMod p) = (k : ZMod p) := by
    push_cast
    rw [hxz]
    simp
  have h0 : ((k : ℕ) : ZMod p) = 0 := by
    rw [← hSz]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hS
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact absurd (Nat.le_of_dvd hm0 h0) (by omega)

/-- If `p ∤ n (n^2 - 1)`, Fermat's little theorem and `n^2 - 1 ∣ n^(p-1) - 1` give the
divisibility. -/
theorem fqDivisible_of_not_dvd (n p : ℕ) (hp : p.Prime)
    (hnot : ¬ (p : ℤ) ∣ (n : ℤ) * ((n : ℤ) ^ 2 - 1)) : FqDivisible n p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpn : ¬ (p : ℤ) ∣ (n : ℤ) := fun h => hnot (dvd_mul_of_dvd_left h _)
  have hpn2 : ¬ (p : ℤ) ∣ (n : ℤ) ^ 2 - 1 := fun h => hnot (dvd_mul_of_dvd_right h _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hnot
    have heven : Even ((n : ℤ) * ((n : ℤ) ^ 2 - 1)) := by
      rcases Int.even_or_odd (n : ℤ) with he | ho
      · exact he.mul_right _
      · have hsq : Even ((n : ℤ) ^ 2 - 1) := ho.pow.sub_odd odd_one
        exact hsq.mul_left _
    exact even_iff_two_dvd.mp heven
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hpm : p - 1 = 2 * k := by omega
  have hferm : (p : ℤ) ∣ (n : ℤ) ^ (p - 1) - 1 := by
    have hcop : IsCoprime (n : ℤ) (p : ℤ) :=
      ((hpZ.coprime_iff_not_dvd).mpr hpn).symm
    exact (Int.ModEq.pow_card_sub_one_eq_one hp hcop).symm.dvd
  have hsq : ((n : ℤ) ^ 2 - 1) ∣ (n : ℤ) ^ (p - 1) - 1 := by
    rw [hpm, pow_mul]
    simpa using sub_dvd_pow_sub_pow ((n : ℤ) ^ 2) 1 k
  exact ((hpZ.coprime_iff_not_dvd).mpr hpn2).mul_dvd hferm hsq

/-- **Key lemma.** For `n ≥ 2` and a prime `p`, the Fermat quotient `Fq(n,p)` is an integer
divisible by `n^2 - 1` iff `p ∤ n^3 - n`. -/
theorem fqDivisible_iff (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    FqDivisible n p ↔ ¬ p ∣ N n := by
  have hcast : (p ∣ N n) ↔ (p : ℤ) ∣ (n : ℤ) * ((n : ℤ) ^ 2 - 1) := by
    rw [← N_cast n (by omega), Int.natCast_dvd_natCast]
  rw [hcast]
  constructor
  · intro h hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd hdvd with h1 | h1
    · exact not_fqDivisible_of_dvd_n n p hp h1 h
    · by_cases hp2 : p = 2
      · subst hp2
        exact not_fqDivisible_two n hn h
      · exact not_fqDivisible_of_dvd_sq_sub_one n p hn hp hp2 h1 h
  · exact fqDivisible_of_not_dvd n p hp

/-! ## The greatest prime factor of `n^3 - n` -/

/-- A prime divides `N n` iff it divides one of `n - 1`, `n`, `n + 1`. -/
theorem dvd_N_iff (n q : ℕ) (hq : q.Prime) :
    q ∣ N n ↔ q ∣ n - 1 ∨ q ∣ n ∨ q ∣ n + 1 := by
  simp only [N, hq.dvd_mul, or_assoc]

/-- `N n ≠ 0` for `n ≥ 2`. -/
theorem N_ne_zero (n : ℕ) (hn : 2 ≤ n) : N n ≠ 0 := by
  simp only [N]
  have h1 : n - 1 ≠ 0 := by omega
  positivity

/-- `3 ∣ N n`. -/
theorem three_dvd_N (n : ℕ) : 3 ∣ N n := by
  have h3 : 3 ∣ n - 1 ∨ 3 ∣ n ∨ 3 ∣ n + 1 := by omega
  exact (dvd_N_iff n 3 Nat.prime_three).mpr h3

/-- Every prime factor of `N n` is at most `gpf n`. -/
theorem le_gpf (n q : ℕ) (hn : 2 ≤ n) (hq : q.Prime) (hd : q ∣ N n) : q ≤ gpf n := by
  have hmem : q ∈ (N n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hd, N_ne_zero n hn⟩
  exact Finset.le_sup (f := id) hmem

/-- `gpf n` is a prime factor of `N n` for `n ≥ 2`. -/
theorem gpf_prime_dvd (n : ℕ) (hn : 2 ≤ n) : (gpf n).Prime ∧ gpf n ∣ N n := by
  have hne : (N n).primeFactors.Nonempty :=
    ⟨3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, three_dvd_N n, N_ne_zero n hn⟩⟩
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  obtain ⟨hip, hid, -⟩ := Nat.mem_primeFactors.mp hi
  simp only [gpf, hsup, id]
  exact ⟨hip, hid⟩

/-- `3 ≤ gpf n` for `n ≥ 2`. -/
theorem three_le_gpf (n : ℕ) (hn : 2 ≤ n) : 3 ≤ gpf n :=
  le_gpf n 3 hn Nat.prime_three (three_dvd_N n)

/-- `gpf n ≤ n + 1`. -/
theorem gpf_le (n : ℕ) (hn : 2 ≤ n) : gpf n ≤ n + 1 := by
  obtain ⟨hp, hd⟩ := gpf_prime_dvd n hn
  rcases (dvd_N_iff n _ hp).mp hd with h | h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · have := Nat.le_of_dvd (by omega) h; omega
  · exact Nat.le_of_dvd (by omega) h

/-- `gpf (q - 1) = q` for a prime `q ≥ 3`. -/
theorem gpf_pred_prime (q : ℕ) (hq : q.Prime) (hq3 : 3 ≤ q) : gpf (q - 1) = q := by
  have hn : 2 ≤ q - 1 := by omega
  apply le_antisymm
  · have := gpf_le (q - 1) hn; omega
  · apply le_gpf (q - 1) q hn hq
    exact (dvd_N_iff (q - 1) q hq).mpr (Or.inr (Or.inr (by rw [Nat.sub_add_cancel (by omega)])))

/-! ## The closed form `a(n) = π(gpf(n^3 - n)) + 1` -/

/-- **Closed form.** For `n ≥ 2`, `a n = #{primes < P} + 2 = π(P) + 1`, where `P = gpf n` is
the greatest prime factor of `n^3 - n`. -/
theorem a_eq (n : ℕ) (hn : 2 ≤ n) : a n = Nat.count Nat.Prime (gpf n) + 2 := by
  obtain ⟨hPp, hPd⟩ := gpf_prime_dvd n hn
  set c := Nat.count Nat.Prime (gpf n) with hc
  have hnth : Nat.nth Nat.Prime c = gpf n := Nat.nth_count hPp
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by omega, fun j hj => ?_⟩
    have hlt : gpf n < primeAt j := by
      rw [← hnth, primeAt]
      exact (Nat.nth_lt_nth hinf).mpr (by omega)
    have hprime : (primeAt j).Prime := Nat.prime_nth_prime _
    rw [fqDivisible_iff n _ hn hprime]
    intro hd
    have := le_gpf n _ hn hprime hd
    omega
  · rintro k ⟨hk1, hk⟩
    by_contra hlt
    have hfq := hk (c + 1) (by omega)
    rw [primeAt, Nat.add_sub_cancel, hnth, fqDivisible_iff n _ hn hPp] at hfq
    exact hfq hPd

/-- Comparison of values reduces to comparison of greatest prime factors. -/
theorem a_lt_a_iff (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : a n < a m ↔ gpf n < gpf m := by
  rw [a_eq n hn, a_eq m hm]
  constructor
  · intro h
    by_contra hle
    have := Nat.count_monotone Nat.Prime (not_lt.mp hle)
    omega
  · intro h
    have := Nat.count_strict_mono (gpf_prime_dvd n hn).1 h
    omega

/-- Equality of values reduces to equality of greatest prime factors. -/
theorem a_eq_a_iff (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : a n = a m ↔ gpf n = gpf m := by
  constructor
  · intro h
    rcases lt_trichotomy (gpf n) (gpf m) with hlt | heq | hgt
    · have := (a_lt_a_iff n m hn hm).mpr hlt; omega
    · exact heq
    · have := (a_lt_a_iff m n hm hn).mpr hgt; omega
  · intro h
    rw [a_eq n hn, a_eq m hm, h]

/-! ## Ground truth: the first listed terms -/

example : a 2 = 3 ∧ a 3 = 3 ∧ a 4 = 4 ∧ a 5 = 4 ∧ a 6 = 5 ∧ a 7 = 5 ∧ a 8 = 5 ∧
    a 9 = 4 ∧ a 10 = 6 ∧ a 11 = 6 ∧ a 12 = 7 ∧ a 13 = 7 ∧ a 14 = 7 ∧ a 15 = 5 ∧
    a 16 = 8 := by
  simp only [a_eq _ (by norm_num : 2 ≤ 2), a_eq _ (by norm_num : 2 ≤ 3),
    a_eq _ (by norm_num : 2 ≤ 4), a_eq _ (by norm_num : 2 ≤ 5), a_eq _ (by norm_num : 2 ≤ 6),
    a_eq _ (by norm_num : 2 ≤ 7), a_eq _ (by norm_num : 2 ≤ 8), a_eq _ (by norm_num : 2 ≤ 9),
    a_eq _ (by norm_num : 2 ≤ 10), a_eq _ (by norm_num : 2 ≤ 11),
    a_eq _ (by norm_num : 2 ≤ 12), a_eq _ (by norm_num : 2 ≤ 13),
    a_eq _ (by norm_num : 2 ≤ 14), a_eq _ (by norm_num : 2 ≤ 15),
    a_eq _ (by norm_num : 2 ≤ 16)]
  have hP : [gpf 2, gpf 3, gpf 4, gpf 5, gpf 6, gpf 7, gpf 8, gpf 9, gpf 10, gpf 11, gpf 12,
      gpf 13, gpf 14, gpf 15, gpf 16] = [3, 3, 5, 5, 7, 7, 7, 5, 11, 11, 13, 13, 13, 7, 17] := by
    simp [gpf, N, ← Nat.toFinset_factors, Nat.primeFactorsList_ofNat]
  simp only [List.cons.injEq, and_true] at hP
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hP
  rw [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  decide

/-! ## Runs have length at most 3 -/

/-- If a prime divides two numbers `x < y`, it is at most `y - x`. -/
theorem le_sub_of_dvd_of_dvd (q x y : ℕ) (hx : q ∣ x) (hy : q ∣ y) (hxy : x < y) :
    q ≤ y - x :=
  Nat.le_of_dvd (by omega) (Nat.dvd_sub hy hx)

/-- No positive integer `r ≡ 5 (mod 6)` has all its prime factors `≤ 3`. -/
theorem not_three_smooth (r : ℕ) (hr : r % 6 = 5) (h : r.minFac ≤ 3) : False := by
  have hr1 : r ≠ 1 := by omega
  have hmp : r.minFac.Prime := Nat.minFac_prime hr1
  have hmd : r.minFac ∣ r := Nat.minFac_dvd r
  have h2 := hmp.two_le
  interval_cases hm : r.minFac
  · omega
  · omega

/-- **Runs of length at most 3** (Wilson's second claim). For `n ≥ 2` it is impossible that
`a n = a (n+1) = a (n+2) = a (n+3)`. -/
theorem no_run_of_four (n : ℕ) (hn : 2 ≤ n) :
    ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2) ∧ a (n + 2) = a (n + 3)) := by
  rintro ⟨h01, h12, h23⟩
  rw [a_eq_a_iff _ _ hn (by omega)] at h01
  rw [a_eq_a_iff _ _ (by omega) (by omega)] at h12 h23
  obtain ⟨q, hg0⟩ : ∃ q, gpf n = q := ⟨_, rfl⟩
  have hg1 : gpf (n + 1) = q := h01.symm.trans hg0
  have hg2 : gpf (n + 2) = q := h12.symm.trans hg1
  have hg3 : gpf (n + 3) = q := h23.symm.trans hg2
  have hqp : q.Prime := hg0 ▸ (gpf_prime_dvd n hn).1
  have hqd : q ∣ N n := hg0 ▸ (gpf_prime_dvd n hn).2
  have hd1 : q ∣ N (n + 1) := hg1 ▸ (gpf_prime_dvd (n + 1) (by omega)).2
  have hd2 : q ∣ N (n + 2) := hg2 ▸ (gpf_prime_dvd (n + 2) (by omega)).2
  have hd3 : q ∣ N (n + 3) := hg3 ▸ (gpf_prime_dvd (n + 3) (by omega)).2
  have hq3 : 3 ≤ q := hg0 ▸ three_le_gpf n hn
  rw [dvd_N_iff _ _ hqp] at hqd hd1 hd2 hd3
  simp only [Nat.add_sub_cancel] at hd1 hd2 hd3
  -- the windows `{n-1,n,n+1}` and `{n+2,n+3,n+4}` are disjoint and within distance 5
  have hq5 : q ≤ 5 := by
    have key : ∀ x y, q ∣ x → q ∣ y → x < y → y ≤ x + 5 → q ≤ 5 := by
      intro x y hx hy hxy hyx
      have := le_sub_of_dvd_of_dvd q x y hx hy hxy
      omega
    rcases hqd with h | h | h <;> rcases hd3 with h' | h' | h' <;>
      exact key _ _ h (by simpa only [add_assoc] using h') (by omega) (by omega)
  -- the windows of `n, n+1, n+2, n+3` all have greatest prime factor `q`
  have hwin : ∀ i, i ≤ 3 → ∀ r, n + i - 1 ≤ r → r ≤ n + i + 1 → 2 ≤ r → r.minFac ≤ q := by
    intro i hi r hr1 hr2 hr
    have hgi : gpf (n + i) = q := by
      interval_cases i
      · exact hg0
      · exact hg1
      · exact hg2
      · exact hg3
    rw [← hgi]
    apply le_gpf (n + i) _ (by omega) (Nat.minFac_prime (by omega))
    rw [dvd_N_iff _ _ (Nat.minFac_prime (by omega))]
    have hmd := Nat.minFac_dvd r
    rcases (by omega : r = n + i - 1 ∨ r = n + i ∨ r = n + i + 1) with e | e | e
    · exact Or.inl (e ▸ hmd)
    · exact Or.inr (Or.inl (e ▸ hmd))
    · exact Or.inr (Or.inr (e ▸ hmd))
  interval_cases q
  · -- `q = 3`: all of `n - 1, …, n + 4` are `3`-smooth; one of them is `≡ 5 (mod 6)`
    have hr : ∃ r, n - 1 ≤ r ∧ r ≤ n + 4 ∧ r % 6 = 5 := ⟨n - 1 + (5 - (n - 1) % 6) % 6,
      by omega, by omega, by omega⟩
    obtain ⟨r, hr1, hr2, hr6⟩ := hr
    rcases (by omega : r ≤ n + 1 ∨ r = n + 2 ∨ r = n + 3 ∨ r = n + 4) with e | e | e | e
    · exact not_three_smooth r hr6 (hwin 0 (by omega) r (by omega) (by omega) (by omega))
    · exact not_three_smooth r hr6 (hwin 1 (by omega) r (by omega) (by omega) (by omega))
    · exact not_three_smooth r hr6 (hwin 2 (by omega) r (by omega) (by omega) (by omega))
    · exact not_three_smooth r hr6 (hwin 3 (by omega) r (by omega) (by omega) (by omega))
  · exact absurd hqp (by norm_num)
  · -- `q = 5`: the outer windows force `5 ∣ n - 1`, and then the window of `n + 1` fails
    omega

/-- Runs of length exactly 3 occur: `a 6 = a 7 = a 8 = 5` (and `a 5 = 4 ≠ 5`, `a 9 = 4 ≠ 5`),
so the bound of `no_run_of_four` is attained. -/
example : a 5 ≠ a 6 ∧ a 6 = a 7 ∧ a 7 = a 8 ∧ a 8 ≠ a 9 := by
  simp only [ne_eq, a_eq_a_iff _ _ (by norm_num : 2 ≤ 5) (by norm_num : 2 ≤ 6),
    a_eq_a_iff _ _ (by norm_num : 2 ≤ 6) (by norm_num : 2 ≤ 7),
    a_eq_a_iff _ _ (by norm_num : 2 ≤ 7) (by norm_num : 2 ≤ 8),
    a_eq_a_iff _ _ (by norm_num : 2 ≤ 8) (by norm_num : 2 ≤ 9)]
  simp [gpf, N, ← Nat.toFinset_factors, Nat.primeFactorsList_ofNat]

/-! ## First appearances -/

/-- `IsFirstOccurrence n`: index `n ≥ 2` is the first index (from the offset `2`) at which the
value `a n` appears. -/
def IsFirstOccurrence (n : ℕ) : Prop := 2 ≤ n ∧ ∀ m, 2 ≤ m → m < n → a m ≠ a n

/-- At a first occurrence the greatest prime factor of `n^3 - n` is `n + 1`. -/
theorem gpf_eq_of_isFirstOccurrence (n : ℕ) (h : IsFirstOccurrence n) : gpf n = n + 1 := by
  obtain ⟨hn, hfirst⟩ := h
  obtain ⟨hqp, -⟩ := gpf_prime_dvd n hn
  have hq3 := three_le_gpf n hn
  have hle := gpf_le n hn
  by_contra hne
  have hlt : gpf n - 1 < n := by omega
  apply hfirst (gpf n - 1) (by omega) hlt
  rw [a_eq_a_iff _ _ (by omega) hn, gpf_pred_prime _ hqp hq3]

/-- **First appearances at even indices** (Wilson's third claim): the first index at which
any value appears is even. -/
theorem even_of_isFirstOccurrence (n : ℕ) (h : IsFirstOccurrence n) : Even n := by
  have hg := gpf_eq_of_isFirstOccurrence n h
  obtain ⟨hqp, -⟩ := gpf_prime_dvd n h.1
  have hq3 := three_le_gpf n h.1
  have hodd : Odd (n + 1) := hg ▸ hqp.odd_of_ne_two (by omega)
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact absurd hodd (Nat.not_odd_iff_even.mpr ho.add_one)

/-- **First appearances in natural order** (Wilson's fourth claim): if the values first
appearing at `n` and at `m` satisfy `a n < a m`, then `n < m`. -/
theorem lt_of_isFirstOccurrence (n m : ℕ) (hn : IsFirstOccurrence n)
    (hm : IsFirstOccurrence m) (hlt : a n < a m) : n < m := by
  rw [a_lt_a_iff n m hn.1 hm.1, gpf_eq_of_isFirstOccurrence n hn,
    gpf_eq_of_isFirstOccurrence m hm] at hlt
  omega

/-- Non-vacuity of the first-occurrence hypotheses: index `10` (value `a 10 = 6`) is a first
occurrence, so `even_of_isFirstOccurrence` and `lt_of_isFirstOccurrence` apply to more than
the trivial index `2`. -/
example : IsFirstOccurrence 10 := by
  refine ⟨by norm_num, fun m hm hlt => ?_⟩
  rw [ne_eq, a_eq_a_iff _ _ hm (by norm_num)]
  have h10 : gpf 10 = 11 := gpf_pred_prime 11 (by norm_num) (by norm_num)
  have hle := gpf_le m hm
  omega

/-! ## Finiteness of each value, reduced to Størmer's theorem -/

/-- **Størmer's theorem for three consecutive integers** (C. Størmer, 1897): for every bound
`B`, only finitely many `n` have all prime factors of `(n - 1) n (n + 1)` at most `B`.

This is the single residual of the module.  It is classical (reduce to finitely many Pell
equations `x^2 - D y^2 = 1` with `D` squarefree and `B`-smooth, and show a `B`-smooth `y`
can occur only among the first few solutions) but is not in Mathlib. -/
theorem stormer_consecutive_triples (B : ℕ) :
    {n : ℕ | 2 ≤ n ∧ ∀ p : ℕ, p.Prime → p ∣ (n - 1) * n * (n + 1) → p ≤ B}.Finite := by
  -- Exact remaining goal: the displayed statement (Størmer's theorem for consecutive
  -- triples).  No proof attempted beyond this reduction.
  sorry

/-- **Each value occurs finitely often** (Wilson's first claim), conditional only on
`stormer_consecutive_triples`. -/
theorem finite_occurrences (v : ℕ) : {n : ℕ | 2 ≤ n ∧ a n = v}.Finite := by
  apply (stormer_consecutive_triples (Nat.nth Nat.Prime (v - 2))).subset
  rintro n ⟨hn, hv⟩
  refine ⟨hn, fun p hp hd => ?_⟩
  have hc : Nat.count Nat.Prime (gpf n) = v - 2 := by
    rw [a_eq n hn] at hv
    omega
  have hg : Nat.nth Nat.Prime (v - 2) = gpf n := hc ▸ Nat.nth_count (gpf_prime_dvd n hn).1
  rw [hg]
  exact le_gpf n p hn hp hd

/-! ## The conjecture -/

/-- **Wilson's conjecture (A364883, Robert G. Wilson v, Aug 17 2023).**

Verbatim: "Conjecture: numbers appear in the sequence only a finite number of times. Terms
appear in runs of length 1, 2, or 3, never more. The first time a term k appears is when the
index is even. The terms appear for the first time in their natural order."

Formalized over the offset `n ≥ 2` as the conjunction of
1. every value `v` is taken at only finitely many indices `n ≥ 2`;
2. no four consecutive terms are equal;
3. every first-occurrence index is even;
4. first occurrences are ordered like their values.

Parts 2–4 are proved here unconditionally; part 1 depends on the residual
`stormer_consecutive_triples`. -/
theorem conjecture :
    (∀ v : ℕ, {n : ℕ | 2 ≤ n ∧ a n = v}.Finite) ∧
    (∀ n : ℕ, 2 ≤ n → ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2) ∧ a (n + 2) = a (n + 3))) ∧
    (∀ n : ℕ, IsFirstOccurrence n → Even n) ∧
    (∀ n m : ℕ, IsFirstOccurrence n → IsFirstOccurrence m → a n < a m → n < m) :=
  ⟨finite_occurrences, no_run_of_four, even_of_isFirstOccurrence, lt_of_isFirstOccurrence⟩

end Candidates.A364883PrintedValueOccurs
