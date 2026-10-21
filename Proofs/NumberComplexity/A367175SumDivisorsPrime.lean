/-
# A367175 — Luschny: `a(k) ∣ sigma(k)` exactly for `k ∈ {1, 2, 3, 6, 14, 15, 35}`

## OEIS source (retrieved with `oeis show A367175` and https://oeis.org/A367175, 2026-10-21)

```
NAME:     a(n) = Sum_{d|n} (-1)^[d is prime] * d, where [] denotes the Iverson
          bracket.
TERMS:    1,-1,-2,3,-4,2,-6,11,7,4,-10,18,-12,6,8,27,-16,29,-18,28,12,10,-22,
          50,21,12,34,38,-28,52,-30,59,20,16,24,81,-36,18,24,76,-40,72,-42,58,
          62,22,-46,114,43,79,32,68,-52,110,40,102,36,28,-58,148,-60,30
OFFSET:   1
KEYWORDS: sign
AUTHOR:   _Peter Luschny_, Nov 08 2023
FORMULA:  sigma(n) - a(n) = 2 * A008472(n).
FORMULA (the conjecture; no separate attribution, entry author Peter Luschny,
         Nov 08 2023):
  Conjecture: {k: a(k) divides sigma(k)} = {1, 2, 3, 6, 14, 15, 35}.
```

## Status

Triage: open (the live entry lists it as a conjecture with no proof or
reference; none found in the literature). Divisibility is in `ℤ` (`a(k)` is
negative at primes). This module proves the conjecture in full.

Computation (Python, exact integers, sieve): the set
`{k ≤ 3·10^6 : a(k) ∣ sigma(k)}` is exactly `{1, 2, 3, 6, 14, 15, 35}`.

Proof outline. `sigma = a + 2 sopf`, so `a ∣ sigma ↔ a ∣ 2 sopf`. At a prime
`p`, `a = 1 - p` and `p - 1 ∣ 2`. For composite `k`, `sigma ≥ 1 + k + sopf` and
`sopf ≤ k`, so `0 < a`, `a ≤ 2 sopf` and `k + 1 ≤ 3 sopf`. If a prime `P ≥ 5`
divides `k = P m`, then `sopf ≤ P + m`; `m ≥ 4` bounds `k ≤ 77`, while
`m ∈ {2, 3}` gives `P - 1 ∣ 6` resp. `2P - 2 ∣ 8`. Otherwise `sopf ≤ 5`.
Every case gives `k < 78`, and `decide` settles `k < 78`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A367175SumDivisorsPrime

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Definitions -/

/-- OEIS A367175: `a(n) = Σ_{d ∣ n} (-1)^[d is prime] · d`, valued in `ℤ`. -/
def a (k : ℕ) : ℤ := ∑ d ∈ k.divisors, (if d.Prime then -1 else 1) * (d : ℤ)

/-- OEIS A008472: the sum of the distinct primes dividing `n` (`sopf`). -/
def sopf (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

/-- Ground truth: the first 30 listed terms of A367175 (offset 1). -/
example : (List.range 30).map (fun n => a (n + 1)) =
    [1, -1, -2, 3, -4, 2, -6, 11, 7, 4, -10, 18, -12, 6, 8, 27, -16, 29, -18, 28,
     12, 10, -22, 50, 21, 12, 34, 38, -28, 52] := by
  decide

/-- Ground truth: the first terms of A008472 (`sopf`, offset 1). -/
example : (List.range 12).map (fun n => sopf (n + 1)) =
    [0, 2, 3, 2, 5, 5, 7, 2, 3, 7, 11, 5] := by
  simp only [sopf, Nat.primeFactors_eq_to_filter_divisors_prime]
  decide

/-- Ground truth: `σ₁` agrees with A000203 on its first terms. -/
example : (List.range 8).map (fun n => σ 1 (n + 1)) = [1, 3, 4, 7, 6, 12, 8, 15] := by
  decide

/-- Non-vacuity of both sides: `a 35 = 24` divides `σ₁(35) = 48`, while
`a 4 = 3` does not divide `σ₁(4) = 7`. -/
example : a 35 ∣ (σ 1 35 : ℤ) ∧ ¬ a 4 ∣ (σ 1 4 : ℤ) := by
  decide

/-! ## Helper lemmas -/

/-- The entry's formula `sigma(n) - a(n) = 2 * A008472(n)`, in the form
`a k = σ₁(k) - 2 * sopf k` over `ℤ` (valid for every `k`, including `k = 0`). -/
theorem a_eq (k : ℕ) : a k = (σ 1 k : ℤ) - 2 * (sopf k : ℤ) := by
  have hterm : ∀ d : ℕ, (if d.Prime then -1 else 1) * (d : ℤ)
      = (d : ℤ) - 2 * (if d.Prime then (d : ℤ) else 0) := by
    intro d
    split_ifs <;> ring
  rw [a, Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_filter, ← Nat.primeFactors_eq_to_filter_divisors_prime,
    sigma_one_apply, sopf]
  push_cast
  rfl

/-- A finite set of naturals, each at least `2`, has sum at most its product. -/
theorem sum_le_prod_of_two_le (s : Finset ℕ) (hs : ∀ x ∈ s, 2 ≤ x) :
    ∑ x ∈ s, x ≤ ∏ x ∈ s, x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hx2 : 2 ≤ x := hs x (Finset.mem_insert_self x t)
    have ih' := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    rcases t.eq_empty_or_nonempty with ht | ht
    · subst ht; simp
    · have hp : 2 ≤ ∏ y ∈ t, y := by
        obtain ⟨y, hy⟩ := ht
        have h1 : y ≤ ∏ y ∈ t, y := by
          calc y ≤ ∑ z ∈ t, z := Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hy
            _ ≤ _ := ih'
        exact (hs y (Finset.mem_insert_of_mem hy)).trans h1
      nlinarith

/-- For `n ≠ 0`, the sum of the distinct prime factors of `n` is at most `n`. -/
theorem sopf_le (n : ℕ) (hn : n ≠ 0) : sopf n ≤ n :=
  calc sopf n ≤ ∏ p ∈ n.primeFactors, p :=
        sum_le_prod_of_two_le _ (fun _ hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- For composite `k` (`2 ≤ k`, not prime), the divisors `1`, `k` and the prime
factors of `k` are distinct, so `1 + k + sopf k ≤ σ₁(k)`. -/
theorem sigma_ge (k : ℕ) (hk : 2 ≤ k) (hkp : ¬ k.Prime) : 1 + k + sopf k ≤ σ 1 k := by
  have hk0 : k ≠ 0 := by omega
  have hdisj : Disjoint ({1, k} : Finset ℕ) k.primeFactors := by
    rw [Finset.disjoint_left]
    intro x hx hxp
    have hxprime := Nat.prime_of_mem_primeFactors hxp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.not_prime_one hxprime
    · exact hkp hxprime
  have hsub : ({1, k} : Finset ℕ) ∪ k.primeFactors ⊆ k.divisors := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hk0]
    · exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hx, hk0⟩
  have h1k : (1 : ℕ) ≠ k := by omega
  calc 1 + k + sopf k = ∑ x ∈ ({1, k} : Finset ℕ) ∪ k.primeFactors, x := by
        rw [Finset.sum_union hdisj, Finset.sum_pair h1k, sopf]
    _ ≤ ∑ x ∈ k.divisors, x := Finset.sum_le_sum_of_subset hsub
    _ = σ 1 k := (sigma_one_apply k).symm

/-- For a prime `P` and `m ≠ 0`, `sopf (P * m) ≤ P + sopf m`. -/
theorem sopf_mul_le (P m : ℕ) (hP : P.Prime) (hm : m ≠ 0) : sopf (P * m) ≤ P + sopf m := by
  rw [sopf, Nat.primeFactors_mul hP.ne_zero hm, hP.primeFactors]
  calc ∑ x ∈ {P} ∪ m.primeFactors, x ≤ ∑ x ∈ {P}, x + ∑ x ∈ m.primeFactors, x := by
        rw [← Finset.sum_union_inter]; exact Nat.le_add_right _ _
    _ = P + sopf m := by rw [Finset.sum_singleton, sopf]

/-- For distinct primes `q ≠ P`: `σ₁(q P) = (q + 1)(P + 1)` and `sopf (q P) = q + P`. -/
theorem family (q P : ℕ) (hq : q.Prime) (hP : P.Prime) (hqP : q ≠ P) :
    σ 1 (q * P) = (q + 1) * (P + 1) ∧ sopf (q * P) = q + P := by
  have hcop : Nat.Coprime q P := (Nat.coprime_primes hq hP).mpr hqP
  constructor
  · rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
    have h1 := sigma_one_apply_prime_pow (i := 1) hq
    have h2 := sigma_one_apply_prime_pow (i := 1) hP
    simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero] at h1 h2
    rw [h1, h2]; ring
  · rw [sopf, Nat.primeFactors_mul hq.ne_zero hP.ne_zero, hq.primeFactors, hP.primeFactors]
    rw [Finset.sum_union (Finset.disjoint_singleton.mpr hqP)]
    simp

/-- If `p` is prime and `a p ∣ σ₁(p)` then `p ≤ 3` (here `a p = 1 - p` and
`σ₁(p) = p + 1`, so `p - 1 ∣ 2`). -/
theorem prime_case (p : ℕ) (hp : p.Prime) (h : a p ∣ (σ 1 p : ℤ)) : p ≤ 3 := by
  have hσ : σ 1 p = p + 1 := by
    have h1 := sigma_one_apply_prime_pow (i := 1) hp
    simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero] at h1
    rw [h1]; ring
  have hs : sopf p = p := by rw [sopf, hp.primeFactors, Finset.sum_singleton]
  rw [a_eq, hσ, hs] at h
  push_cast at h
  have h2 : ((p : ℤ) - 1) ∣ 2 := by
    obtain ⟨c, hc⟩ := h
    exact ⟨-c - 1, by linear_combination hc⟩
  have hle := Int.le_of_dvd (by norm_num) h2
  omega

/-- For composite `k` with `a k ∣ σ₁(k)`: `a k` is positive, `a k ∣ 2 sopf k`, and
hence `k + 1 ≤ 3 sopf k`. -/
theorem composite_bound (k : ℕ) (hk : 2 ≤ k) (hkp : ¬ k.Prime)
    (h : a k ∣ (σ 1 k : ℤ)) : k + 1 ≤ 3 * sopf k ∧ a k ∣ 2 * (sopf k : ℤ) ∧ 0 < a k := by
  have hσ := sigma_ge k hk hkp
  have hs := sopf_le k (by omega)
  have ha : 0 < a k := by rw [a_eq]; omega
  have h2 : a k ∣ 2 * (sopf k : ℤ) := by
    obtain ⟨c, hc⟩ := h
    have hak := a_eq k
    exact ⟨c - 1, by linear_combination hak + hc⟩
  have hpos : 0 < sopf k := by
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
    have hmem : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpk, by omega⟩
    exact lt_of_lt_of_le hp.pos (Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hmem)
  have hle := Int.le_of_dvd (by positivity) h2
  rw [a_eq] at hle
  refine ⟨?_, h2, ha⟩
  have : (σ 1 k : ℤ) ≤ 4 * sopf k := by linarith
  omega

/-- The two unbounded families: for `q ∈ {2, 3}` and a prime `P ≥ 5`,
`a (q P) ∣ 2 sopf (q P)` forces `q P ≤ 15` (`P - 1 ∣ 6`, resp. `2P - 2 ∣ 8`). -/
theorem family_bound (q P : ℕ) (hq : q = 2 ∨ q = 3) (hP : P.Prime) (hP5 : 5 ≤ P)
    (h : a (q * P) ∣ 2 * (sopf (q * P) : ℤ)) : q * P ≤ 15 := by
  have hqp : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  have hqP : q ≠ P := by omega
  obtain ⟨hσ, hs⟩ := family q P hqp hP hqP
  rw [a_eq, hσ, hs] at h
  push_cast at h
  rcases hq with rfl | rfl
  · have h6 : ((P : ℤ) - 1) ∣ 6 := by
      obtain ⟨c, hc⟩ := h
      exact ⟨c - 2, by linear_combination hc⟩
    have hle := Int.le_of_dvd (by norm_num) h6
    omega
  · have h8 : (2 * (P : ℤ) - 2) ∣ 8 := by
      obtain ⟨c, hc⟩ := h
      exact ⟨c - 1, by linear_combination hc⟩
    have hle := Int.le_of_dvd (by norm_num) h8
    omega

/-- If every prime factor of `k` is below `5`, then `sopf k ≤ 2 + 3 = 5`. -/
theorem sopf_le_five (k : ℕ) (hk : ∀ P, P.Prime → P ∣ k → P < 5) : sopf k ≤ 5 := by
  have hsub : k.primeFactors ⊆ {2, 3} := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp5 := hk p hpp (Nat.dvd_of_mem_primeFactors hp)
    have hp2 := hpp.two_le
    interval_cases p
    · simp
    · simp
    · norm_num at hpp
  calc sopf k ≤ ∑ x ∈ ({2, 3} : Finset ℕ), x :=
        Finset.sum_le_sum_of_subset hsub
    _ = 5 := by decide

/-- Load-bearing reduction: every `k ≥ 1` with `a k ∣ σ₁(k)` satisfies `k < 78`. -/
theorem lt_78_of_dvd (k : ℕ) (hk : 0 < k) (h : a k ∣ (σ 1 k : ℤ)) : k < 78 := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · omega
  by_cases hkp : k.Prime
  · have := prime_case k hkp h
    omega
  obtain ⟨h3, hdvd, -⟩ := composite_bound k hk2 hkp h
  by_cases hbig : ∃ P, P.Prime ∧ 5 ≤ P ∧ P ∣ k
  · obtain ⟨P, hP, hP5, hPk⟩ := hbig
    obtain ⟨m, rfl⟩ := hPk
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hm1 : m ≠ 1 := by rintro rfl; exact hkp (by simpa using hP)
    have hsm := sopf_mul_le P m hP hm0
    have hsm' := sopf_le m hm0
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · have hq : m = 2 ∨ m = 3 := by omega
      rw [mul_comm] at hdvd ⊢
      have := family_bound m P hq hP hP5 hdvd
      omega
    · have hle : P * m + 1 ≤ 3 * (P + m) := by omega
      have hP11 : P ≤ 11 := by nlinarith
      have hm7 : m ≤ 7 := by nlinarith
      have : P * m ≤ 11 * 7 := Nat.mul_le_mul hP11 hm7
      omega
  · push Not at hbig
    have h5 := sopf_le_five k (fun P hP hPk => by
      by_contra hc
      exact absurd (hbig P hP (by omega)) (by simpa using hPk))
    omega

/-- Finite check: for `0 < k < 78`, `a k ∣ σ₁(k)` iff `k ∈ {1, 2, 3, 6, 14, 15, 35}`. -/
theorem dvd_iff_of_lt_78 :
    ∀ k < 78, 0 < k → (a k ∣ (σ 1 k : ℤ) ↔ k ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ)) := by
  decide

/-! ## The conjecture -/

/-- **A367175 conjecture (entry FORMULA line, Peter Luschny, Nov 08 2023).**

Verbatim: "Conjecture: {k: a(k) divides sigma(k)} = {1, 2, 3, 6, 14, 15, 35}."

For every `k ≥ 1`, `a(k) = Σ_{d ∣ k} (-1)^[d prime] d` divides `σ₁(k)` in `ℤ`
if and only if `k ∈ {1, 2, 3, 6, 14, 15, 35}`. The guard `0 < k` is the entry's
offset (`a 0 = 0` and `σ₁(0) = 0` are junk values). -/
theorem a_dvd_sigma_iff (k : ℕ) (hk : 0 < k) :
    a k ∣ (σ 1 k : ℤ) ↔ k ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ) := by
  constructor
  · intro h
    exact (dvd_iff_of_lt_78 k (lt_78_of_dvd k hk h) hk).mp h
  · intro hmem
    have hlt : k < 78 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact (dvd_iff_of_lt_78 k hlt hk).mpr hmem

end Candidates.A367175SumDivisorsPrime
