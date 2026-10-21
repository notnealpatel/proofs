/-
# A128059 — Aktar: denominator of an lcm-weighted Bernoulli fractional-part sum

## OEIS source (retrieved with `oeis show A128059`, 2026-10-21)

```
NAME:     a(n) = numerator((2*n-1)^2/(2*(2*n)!)).
TERMS:    1,1,3,5,7,1,11,13,1,17,19,1,23,1,1,29,31,1,1,37,1,41,43,1,47,1,1,53,
          1,1,59,61,1,1,67,1,71,73,1,1,79,1,83,1,1,89,1,1,1,97,1,101,103,1,107,
          109,1,113,1,1,1,1,1,1,127
KEYWORDS: easy,nonn
OFFSET:   0 (the Maple program lists a(0), a(1), ... = 1, 1, 3, ...)
FORMULA (the conjecture, verbatim):
  Conjecture: a(n) = denominator(f(n-1)) with f(n) =
  lcm(2,3,4,5,...,n)*(Sum_{k=0..n} frac(Bernoulli(2*k))*binomial(n+k,k)).
  - _Yalcin Aktar_, Jul 23 2008
```

## Status

Triage: open — the entry records the identity as a 2008 conjecture with no
proof, and the triage found no proof in the literature.  Exact rational
computation agrees for `n = 1..120` (triage `n ≤ 59`, re-validated here to
`n ≤ 120` in Sage).

## Formalization choices

* `frac x` is `Int.fract x = x - ⌊x⌋` (the entry's "frac").
* `Bernoulli(2k)` is Mathlib's `bernoulli (2 * k)`; the `B₁` sign convention
  never enters, since only even indices occur.
* `lcm(2,3,...,n)` is `(Finset.Icc 1 n).lcm id`; including `1` changes nothing
  and the empty case (`n ≤ 1`) is `1`, as for the empty lcm in the entry.
* The conjecture is about `n ≥ 1` (it evaluates `f (n - 1)`); the guard
  `1 ≤ n` keeps the natural-number subtraction off its junk value.

## Proof (complete, kernel-checked below)

By von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`),
`frac(B_{2k}) ≡ -∑_{p prime, (p-1) ∣ 2k} 1/p (mod ℤ)`, so
`f(m) ≡ -∑_k ∑_p L·C(m+k,k)/p (mod ℤ)` with `L = lcm(1..m)`.  For every
prime `p ≠ 2m+1` in the sum, `p ∣ L·C(m+k,k)`: either `p ≤ m` and `p ∣ L`,
or `m < p ≤ m + k` and `p ∣ C(m+k,k)` (`Nat.Prime.dvd_choose_add`).  The
only surviving term is `k = m`, `p = 2m+1` (when prime), whose numerator
`L·C(2m,m)` is prime to `2m+1`.  Hence `den f(m) = 2m+1` if `2m+1` is prime
and `1` otherwise, which is also the value of `numerator((2m+1)^2/(2(2m+2)!))`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A128059BernoulliFrac

open Finset

/-! ## Definition layer -/

/-- `lcm(1, 2, …, m)`; the empty lcm (`m = 0`) is `1`. -/
def lcmUpTo (m : ℕ) : ℕ := (Finset.Icc 1 m).lcm id

/-- Aktar's `f(m) = lcm(2,…,m) · ∑_{k=0}^{m} frac(B_{2k}) · C(m+k, k)`. -/
noncomputable def f (m : ℕ) : ℚ :=
  (lcmUpTo m : ℚ) * ∑ k ∈ Finset.range (m + 1),
    Int.fract (bernoulli (2 * k)) * ((m + k).choose k : ℚ)

/-- OEIS A128059: `a(n) = numerator((2n-1)^2 / (2·(2n)!))`, computed in `ℚ`
(the subtraction `2n - 1` is taken in `ℚ`, so `a 0 = numerator(1/2) = 1`). -/
def a (n : ℕ) : ℤ := (((2 * n : ℚ) - 1) ^ 2 / (2 * (2 * n).factorial)).num

/-! ## Ground truth -/

-- The DATA line, `a(0..11)`.
example : (List.range 12).map a = [1, 1, 3, 5, 7, 1, 11, 13, 1, 17, 19, 1] := by
  decide +kernel

example : lcmUpTo 4 = 12 := by decide

-- `f(0) = 0`, `f(1) = 1/3`, `f(2) = 63/5`: denominators `1, 3, 5 = a(1), a(2), a(3)`.
example : f 0 = 0 := by simp [f, lcmUpTo]

example : f 1 = 1 / 3 := by
  simp only [f, lcmUpTo, Icc_self, lcm_singleton, id_eq, normalize_eq, Nat.cast_one,
    Nat.reduceAdd, sum_range_succ, range_one, sum_singleton, mul_zero, bernoulli_zero,
    Int.fract_one, add_zero, Nat.choose_succ_self_right, zero_add, mul_one, bernoulli_two,
    Nat.cast_ofNat, one_mul, one_div]
  norm_num [Int.fract]

example : f 2 = 63 / 5 := by
  have h4 : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  have hl : lcmUpTo 2 = 2 := by decide
  simp only [f, hl, Nat.cast_ofNat, Nat.reduceAdd, sum_range_succ, range_one, sum_singleton,
    mul_zero, bernoulli_zero, Int.fract_one, Nat.choose, Nat.cast_one, mul_one, bernoulli_two,
    add_zero, zero_add, Nat.reduceMul, h4]
  norm_num [Int.fract]

/-! ## Helper lemmas -/

/-- The von Staudt–Clausen primes for index `2k`: primes `p < 2k + 2` with
`(p - 1) ∣ 2k` (exactly the index set of `Bernoulli.vonStaudt_clausen`). -/
def vscPrimes (k : ℕ) : Finset ℕ :=
  (range (2 * k + 2)).filter fun p ↦ p.Prime ∧ (p - 1) ∣ 2 * k

/-- von Staudt–Clausen, fractional-part form:
`frac(B_{2k}) = J - ∑_{p ∈ vscPrimes k} 1/p` for some integer `J`. -/
theorem exists_fract_bernoulli_eq (k : ℕ) :
    ∃ J : ℤ, Int.fract (bernoulli (2 * k)) = J - ∑ p ∈ vscPrimes k, (1 : ℚ) / p := by
  obtain ⟨I, hI⟩ := Bernoulli.vonStaudt_clausen k
  refine ⟨I - ⌊bernoulli (2 * k)⌋, ?_⟩
  rw [Int.fract, vscPrimes, Int.cast_sub, hI]
  ring

/-- Every von Staudt–Clausen prime `p ≠ 2m+1` of an index `k ≤ m` divides
`lcm(1..m) · C(m+k, k)`. -/
theorem prime_dvd_lcmUpTo_mul_choose {m k p : ℕ} (hk : k ≤ m) (hp : p ∈ vscPrimes k)
    (hne : p ≠ 2 * m + 1) : p ∣ lcmUpTo m * (m + k).choose k := by
  simp only [vscPrimes, mem_filter, mem_range] at hp
  obtain ⟨hlt, hprime, hdvd⟩ := hp
  have hp2 := hprime.two_le
  by_cases hpm : p ≤ m
  · exact Dvd.dvd.mul_right
      (Finset.dvd_lcm (s := Icc 1 m) (f := id) (mem_Icc.mpr ⟨by omega, hpm⟩)) _
  · push Not at hpm
    obtain ⟨c, hc⟩ := hdvd
    have hle : p ≤ k + m := by
      rcases Nat.lt_trichotomy c 1 with hc0 | rfl | hc2
      · have : c = 0 := by omega
        subst this
        omega
      · omega
      · have : (p - 1) * 2 ≤ (p - 1) * c := Nat.mul_le_mul_left _ hc2
        omega
    have hchoose : p ∣ (k + m).choose k :=
      hprime.dvd_choose_add (by omega) hpm hle
    rw [add_comm m k]
    exact Dvd.dvd.mul_left hchoose _

/-- `lcm(1..m)` divides `m!`. -/
theorem lcmUpTo_dvd_factorial (m : ℕ) : lcmUpTo m ∣ m.factorial :=
  Finset.lcm_dvd fun _ hi ↦ Nat.dvd_factorial (mem_Icc.mp hi).1 (mem_Icc.mp hi).2

/-- If `2m+1` is prime it does not divide `lcm(1..m) · C(2m, m)`. -/
theorem not_dvd_lcmUpTo_mul_centralBinom {m : ℕ} (hq : (2 * m + 1).Prime) :
    ¬ (2 * m + 1) ∣ lcmUpTo m * (m + m).choose m := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
  · have := (hq.dvd_factorial).mp ((h1.trans (lcmUpTo_dvd_factorial m)))
    omega
  · have hfac : (m + m).choose m ∣ (m + m).factorial :=
      ⟨m.factorial * (m + m - m).factorial, by
        rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial (by omega)]⟩
    have := (hq.dvd_factorial).mp (h2.trans hfac)
    omega

/-- The `2m+1` from von Staudt–Clausen occurs for an index `k ≤ m` exactly when
`k = m` and `2m+1` is prime. -/
theorem mem_vscPrimes_two_mul_add_one_iff {m k : ℕ} (hk : k ≤ m) :
    2 * m + 1 ∈ vscPrimes k ↔ k = m ∧ (2 * m + 1).Prime := by
  simp only [vscPrimes, mem_filter, mem_range, Nat.add_sub_cancel]
  constructor
  · rintro ⟨hlt, hq, _⟩
    exact ⟨by omega, hq⟩
  · rintro ⟨rfl, hq⟩
    exact ⟨by omega, hq, dvd_rfl⟩

/-- The surviving non-integral term: `lcm(1..m)·C(2m,m)/(2m+1)` when `2m+1` is
prime, and `0` otherwise. -/
noncomputable def special (m : ℕ) : ℚ :=
  if (2 * m + 1).Prime then
    ((lcmUpTo m * (m + m).choose m : ℕ) : ℚ) / ((2 * m + 1 : ℕ) : ℚ)
  else 0

/-- **Load-bearing decomposition.** `f(m) ≡ -special(m) (mod ℤ)`. -/
theorem exists_int_f_eq_sub_special (m : ℕ) : ∃ z : ℤ, f m = z - special m := by
  choose J hJ using exists_fract_bernoulli_eq
  set L := lcmUpTo m with hL
  set g : ℕ → ℚ := fun k ↦ ((L * (m + k).choose k : ℕ) : ℚ) with hg
  let R : Subring ℚ := (Int.castRingHom ℚ).range
  have hexp : f m = (∑ k ∈ range (m + 1), (L : ℚ) * J k * ((m + k).choose k : ℚ)) -
      ∑ k ∈ range (m + 1), ∑ p ∈ vscPrimes k, g k / p := by
    rw [f, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hJ k, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [hg, Nat.cast_mul]
      ring
  have hsplit : ∀ k p : ℕ, g k / p =
      (if p = 2 * m + 1 then g k / p else 0) + (if p = 2 * m + 1 then 0 else g k / p) := by
    intro k p
    split_ifs <;> simp
  have hint : (∑ k ∈ range (m + 1), ∑ p ∈ vscPrimes k,
      (if p = 2 * m + 1 then 0 else g k / p)) ∈ R := by
    refine Subring.sum_mem _ fun k hk ↦ Subring.sum_mem _ fun p hp ↦ ?_
    split_ifs with hne
    · exact R.zero_mem
    · have hkm : k ≤ m := by simp only [mem_range] at hk; omega
      have hd := prime_dvd_lcmUpTo_mul_choose hkm hp hne
      have hp0 : (p : ℚ) ≠ 0 := by
        have := (mem_filter.mp hp).2.1.ne_zero
        exact_mod_cast this
      refine ⟨((L * (m + k).choose k / p : ℕ) : ℤ), ?_⟩
      simp only [eq_intCast, Int.cast_natCast, hg]
      rw [Nat.cast_div hd hp0]
  have hspec : (∑ k ∈ range (m + 1), ∑ p ∈ vscPrimes k,
      (if p = 2 * m + 1 then g k / p else 0)) = special m := by
    have hinner : ∀ k ∈ range (m + 1), (∑ p ∈ vscPrimes k,
        (if p = 2 * m + 1 then g k / p else 0)) =
        if k = m ∧ (2 * m + 1).Prime then g m / ((2 * m + 1 : ℕ) : ℚ) else 0 := by
      intro k hk
      have hkm : k ≤ m := by simp only [mem_range] at hk; omega
      have hiff := mem_vscPrimes_two_mul_add_one_iff hkm
      rw [Finset.sum_ite_eq']
      by_cases h : k = m ∧ (2 * m + 1).Prime
      · rw [if_pos (hiff.mpr h), if_pos h, h.1]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    rw [Finset.sum_congr rfl hinner, special]
    by_cases hq : (2 * m + 1).Prime
    · simp only [hq, and_true, if_true]
      rw [Finset.sum_ite_eq']
      simp [hg, hL]
    · simp [hq]
  obtain ⟨w, hw⟩ := hint
  simp only [eq_intCast] at hw
  refine ⟨(∑ k ∈ range (m + 1), (L : ℤ) * J k * ((m + k).choose k : ℤ)) - w, ?_⟩
  rw [hexp, ← hspec]
  have hsum : (∑ k ∈ range (m + 1), ∑ p ∈ vscPrimes k, g k / p) =
      (∑ k ∈ range (m + 1), ∑ p ∈ vscPrimes k, (if p = 2 * m + 1 then g k / p else 0)) +
      (∑ k ∈ range (m + 1), ∑ p ∈ vscPrimes k, (if p = 2 * m + 1 then 0 else g k / p)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ hsplit k p
  rw [hsum, ← hw]
  push_cast
  ring

/-- `den f(m) = 2m+1` if `2m+1` is prime, and `1` otherwise. -/
theorem den_f (m : ℕ) : (f m).den = if (2 * m + 1).Prime then 2 * m + 1 else 1 := by
  obtain ⟨z, hz⟩ := exists_int_f_eq_sub_special m
  rw [hz, Rat.intCast_sub_den, special]
  split_ifs with hq
  · have hcop : Nat.Coprime (lcmUpTo m * (m + m).choose m) (2 * m + 1) :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr
        (not_dvd_lcmUpTo_mul_centralBinom hq))
    have h := Rat.den_div_eq_of_coprime (a := ((lcmUpTo m * (m + m).choose m : ℕ) : ℤ))
      (b := ((2 * m + 1 : ℕ) : ℤ)) (by positivity)
      (by simp only [Int.natAbs_natCast]; exact hcop)
    push_cast at h ⊢
    exact_mod_cast h
  · simp

/-- A composite `q > 4` divides `(q - 1)!`. -/
theorem dvd_factorial_pred_of_not_prime {q : ℕ} (hq : ¬ q.Prime) (h4 : 4 < q) :
    q ∣ (q - 1).factorial := by
  set a := q.minFac with ha
  have hq1 : q ≠ 1 := by omega
  have haprime : a.Prime := Nat.minFac_prime hq1
  have ha2 := haprime.two_le
  set b := q / a with hb
  have hab : a * b = q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
  have hsq : a ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hq
  have hale : a ≤ b := by
    rw [sq, ← hab] at hsq
    exact Nat.le_of_mul_le_mul_left hsq (by omega)
  have hblt : b < q := Nat.div_lt_self (by omega) (by omega)
  rcases Nat.lt_or_ge a b with hlt | hge
  · -- `a < b < q`: `a·b ∣ b! ∣ (q-1)!`.
    have h1 : a ∣ (b - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    have h2 : a * b ∣ b.factorial := by
      rw [← Nat.mul_factorial_pred (by omega : b ≠ 0), mul_comm b]
      exact Nat.mul_dvd_mul_right h1 b
    rw [← hab]
    exact h2.trans (Nat.factorial_dvd_factorial (by omega))
  · -- `q = a²` with `a ≥ 3`: `a·a ∣ a·(2a) ∣ (2a)! ∣ (q-1)!`.
    have hab' : b = a := le_antisymm hge hale
    rw [hab'] at hab
    have ha3 : 3 ≤ a := by
      by_contra hcon
      have : a = 2 := by omega
      rw [this] at hab
      omega
    have h2a : 2 * a ≤ a * a - 1 := by
      have : 3 * a ≤ a * a := Nat.mul_le_mul_right a ha3
      omega
    have h1 : a ∣ (2 * a - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    have h2 : a * (2 * a) ∣ (2 * a).factorial := by
      rw [← Nat.mul_factorial_pred (by omega : 2 * a ≠ 0), mul_comm (2 * a)]
      exact Nat.mul_dvd_mul_right h1 _
    have h3 : a * a ∣ a * (2 * a) := Nat.mul_dvd_mul_left a (Dvd.intro_left 2 rfl)
    rw [← hab]
    exact h3.trans (h2.trans (Nat.factorial_dvd_factorial h2a))

/-- The OEIS formula evaluated: `a(m+1) = 2m+1` if `2m+1` is prime, else `1`. -/
theorem a_succ (m : ℕ) : a (m + 1) = if (2 * m + 1).Prime then 2 * m + 1 else 1 := by
  have hcast : 2 * ((m + 1 : ℕ) : ℚ) - 1 = ((2 * m + 1 : ℕ) : ℚ) := by push_cast; ring
  have hfac : (2 * (m + 1)).factorial = (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  unfold a
  rw [hcast, hfac]
  split_ifs with hq
  · have hq3 : 3 ≤ 2 * m + 1 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact absurd hq Nat.not_prime_one
      · omega
    have hndvd : ¬ (2 * m + 1) ∣ 2 * ((2 * m + 2) * (2 * m).factorial) := by
      intro h
      rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1
        omega
      rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
      · have h3 : (2 * m + 1) ∣ 1 := (Nat.dvd_add_right (dvd_refl (2 * m + 1))).mp
          (by rwa [show 2 * m + 2 = 2 * m + 1 + 1 by ring] at h2)
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have := (hq.dvd_factorial).mp h2
        omega
    have hcop : Nat.Coprime (2 * m + 1) (2 * ((2 * m + 2) * (2 * m).factorial)) :=
      (Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd
    have hrw : (((2 * m + 1 : ℕ) : ℚ) ^ 2 /
        (2 * (((2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) : ℕ) : ℚ))) =
        (((2 * m + 1 : ℕ) : ℤ) : ℚ) /
          (((2 * ((2 * m + 2) * (2 * m).factorial) : ℕ) : ℤ) : ℚ) := by
      push_cast
      field_simp
    rw [hrw, Rat.num_div_eq_of_coprime (by positivity)
      (by simp only [Int.natAbs_natCast]; exact hcop)]
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · norm_num
      · exact absurd Nat.prime_three hq
    · obtain ⟨t, ht⟩ := dvd_factorial_pred_of_not_prime hq (by omega)
      rw [show 2 * m + 1 - 1 = 2 * m by omega] at ht
      have hrw : (((2 * m + 1 : ℕ) : ℚ) ^ 2 /
          (2 * (((2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) : ℕ) : ℚ))) =
          ((1 : ℤ) : ℚ) / (((2 * ((2 * m + 2) * t)) : ℕ) : ℤ) := by
        rw [ht]
        push_cast
        field_simp
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | h
        · exact absurd ht (by simp [Nat.factorial_ne_zero])
        · exact h
      have hden : (0 : ℤ) < ((2 * ((2 * m + 2) * t) : ℕ) : ℤ) :=
        Int.natCast_pos.mpr (Nat.mul_pos two_pos (Nat.mul_pos (by omega) ht0))
      rw [hrw, Rat.num_div_eq_of_coprime hden (by simp)]
      rfl

/-! ## The conjecture -/

/-- **Aktar's conjecture (A128059, Yalcin Aktar, Jul 23 2008), proved.**

Verbatim: "Conjecture: a(n) = denominator(f(n-1)) with f(n) =
lcm(2,3,4,5,...,n)*(Sum_{k=0..n} frac(Bernoulli(2*k))*binomial(n+k,k))."

For every `n ≥ 1`, the denominator of
`f(n-1) = lcm(1..n-1) · ∑_{k=0}^{n-1} frac(B_{2k}) · C(n-1+k, k)` equals
`a(n) = numerator((2n-1)^2 / (2·(2n)!))`.  The guard `1 ≤ n` keeps `n - 1`
off its truncated value (`n = 0` is outside the conjecture). -/
theorem aktar_conjecture (n : ℕ) (hn : 1 ≤ n) : ((f (n - 1)).den : ℤ) = a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, den_f, a_succ]

/-- Closed form of the denominator (the triage's equivalent form): for `n ≥ 1`,
`denominator(f(n-1)) = 2n-1` if `2n-1` is prime and `1` otherwise. -/
theorem den_f_pred (n : ℕ) (hn : 1 ≤ n) :
    (f (n - 1)).den = if (2 * n - 1).Prime then 2 * n - 1 else 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, den_f, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]

-- Non-vacuity: the hypothesis `1 ≤ n` is met at `n = 3`, where the common value is `5`.
example : ((f (3 - 1)).den : ℤ) = a 3 ∧ a 3 = 5 :=
  ⟨aktar_conjecture 3 (by norm_num), by decide +kernel⟩

end Candidates.A128059BernoulliFrac
