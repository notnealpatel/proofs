/-
# A000961 — radical criterion for the Ordowski–Resta power-sum congruence

## OEIS source (retrieved with `oeis show A000961`, 2026-10-21)

```
NAME:     Powers of primes. Alternatively, 1 and the prime powers
          (p^k, p prime, k >= 1).
TERMS:    1,2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,
          53,59,61,64,67,71,73,79,81,83,89,97,101,103,107,109,113,121,125,...
KEYWORDS: nonn,easy,core,nice
COMMENT (the conjecture):
  Conjecture: these are numbers m such that Sum_{k=0..m-1} k^phi(m) ==
  phi(m) (mod m), where phi(m) = A000010(m). - _Thomas Ordowski_ and
  _Giovanni Resta_, Jul 25 2018
```

## Target (triage `A000961-partial`)

A reduction of the Ordowski–Resta conjecture: for `m ≥ 2`,
`∑_{k<m} k^φ(m) ≡ φ(m) (mod m)` iff every prime `p ∣ m` divides
`rad(m)/p + φ(rad m)` (equivalently `rad m ∣ φ(rad m) + ∑_{p ∣ m} rad(m)/p`).
Consequences: (i) every prime power satisfies the congruence; (ii) no even
non-prime-power does; (iii) no `m` with `2 ≤ ω(m) ≤ 8` does.  Hence any
counterexample is odd with at least nine distinct prime factors.

## Status

Triage status: open (no proof of the reduction located in the entry or the
literature by the triage).  This module proves the reduction and all three
consequences with no `sorry`.  The Ordowski–Resta conjecture itself (that no
non-prime-power `m ≥ 2` satisfies the congruence) remains OPEN and is not
stated as a theorem here; in the vocabulary of this file it reads
`∀ m, 2 ≤ m → PowerSumCongr m → IsPrimePow m`.  The proved residual form is
`odd_and_nine_le_card_of_powerSumCongr`.

## Proof outline

For `q = p^a ∥ m`: units `k` give `k^φ(m) ≡ 1 (mod q)` and multiples of `p`
give `0` (as `a ≤ φ(m)`), so the sum is `≡ #{k < m : p ∤ k} = (m/p)(p-1)`.
Writing `m = p^a n`, the congruence modulo `q` reduces to `p ∣ n - φ(n)`, and
the identity `φ(n)·rad(n) = n·φ(rad n)` turns this into
`p ∣ rad(m)/p + φ(rad m)`.  For (iii): the criterion gives
`rad m ∣ ∑ rad(m)/p + φ(rad m)`, i.e. `∑ 1/p + ∏(1 - 1/p)` is an integer; it
exceeds `1` once `ω(m) ≥ 2`, so `∑ 1/p ≥ 1`, while at most eight odd primes
have reciprocal sum at most `1/3 + 1/5 + ⋯ + 1/23 < 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A000961PowerSumRadical

open Finset

/-- The radical `rad m = ∏_{p ∣ m} p` (product of the distinct prime factors). -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- The Ordowski–Resta congruence `∑_{k=0}^{m-1} k^φ(m) ≡ φ(m) (mod m)`. -/
def PowerSumCongr (m : ℕ) : Prop :=
  ∑ k ∈ range m, k ^ m.totient ≡ m.totient [MOD m]

/-- `PowerSumCongr` is decidable (it is a congruence of natural numbers). -/
instance (m : ℕ) : Decidable (PowerSumCongr m) := by
  unfold PowerSumCongr; infer_instance

/-- The radical criterion: every prime `p ∣ m` divides `rad m / p + φ (rad m)`. -/
def RadicalCriterion (m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, p ∣ rad m / p + (rad m).totient

/-! ## Ground truth -/

example : rad 12 = 6 := by
  simp only [rad, Nat.primeFactors, Nat.primeFactorsList_ofNat]; decide

example : rad 360 = 30 := by
  simp only [rad, Nat.primeFactors, Nat.primeFactorsList_ofNat]; decide

/-- The congruence selects exactly the listed terms `2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19,
23, 25, 27, 29, 31, 32` of A000961 among `2 ≤ m ≤ 32`. -/
example : (List.range 33).filter (fun m => 2 ≤ m ∧ PowerSumCongr m) =
    [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32] := by
  decide

/-- Local evaluation of a power modulo a prime power. -/
theorem cast_pow_eq_ite {p a e : ℕ} (k : ℕ) (hp : p.Prime) (ha : a ≤ e)
    (he : (p ^ a).totient ∣ e) :
    ((k : ZMod (p ^ a)) ^ e) = if p ∣ k then 0 else 1 := by
  split_ifs with hk
  · rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact (pow_dvd_pow_of_dvd hk a).trans (pow_dvd_pow k ha)
  · obtain ⟨c, rfl⟩ := he
    have hcop : k.Coprime (p ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk))
    rw [← Nat.cast_pow, pow_mul, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    simpa using (Nat.ModEq.pow_totient hcop).pow c

/-- Exactly `c` of the numbers `0, …, p c - 1` are multiples of `p`. -/
theorem card_filter_dvd_range {p : ℕ} (c : ℕ) (hp : 0 < p) :
    #{k ∈ range (p * c) | p ∣ k} = c := by
  have hset : {k ∈ range (p * c) | p ∣ k} =
      (range c).map ⟨(p * ·), mul_right_injective₀ hp.ne'⟩ := by
    ext k
    simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hk, j, rfl⟩
      exact ⟨j, (Nat.mul_lt_mul_left hp).mp hk, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hj hp, dvd_mul_right p j⟩
  rw [hset, card_map, card_range]

/-- The exponent of `p` in `m` is at most `φ m`. -/
theorem factorization_le_totient {m p : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    m.factorization p ≤ m.totient := by
  rcases Nat.eq_zero_or_pos (m.factorization p) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hdvd : (p ^ m.factorization p).totient ∣ m.totient :=
    Nat.totient_dvd_of_dvd (Nat.ordProj_dvd m p)
  have hle : (p ^ m.factorization p).totient ≤ m.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)) hdvd
  rw [Nat.totient_prime_pow hp hpos] at hle
  have h1 : m.factorization p - 1 < p ^ (m.factorization p - 1) := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ (m.factorization p - 1) ≤ p ^ (m.factorization p - 1) * (p - 1) :=
    Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hp.one_lt)
  omega

/-- Local power sum: modulo `p ^ v_p(m)`, `∑_{k<m} k^φ(m) ≡ (m/p)(p-1)`. -/
theorem sum_pow_modEq_local {m p : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hpm : p ∣ m) :
    ∑ k ∈ range m, k ^ m.totient ≡ m / p * (p - 1) [MOD p ^ m.factorization p] := by
  have ha : m.factorization p ≤ m.totient := factorization_le_totient hp hm
  have he : (p ^ m.factorization p).totient ∣ m.totient :=
    Nat.totient_dvd_of_dvd (Nat.ordProj_dvd m p)
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  simp_rw [cast_pow_eq_ite _ hp ha he]
  rw [Finset.sum_ite, sum_const_zero, sum_const, nsmul_one, zero_add]
  rw [← Nat.cast_mul]
  congr 1
  obtain ⟨c, rfl⟩ := hpm
  have hcard := card_filter_add_card_filter_not (s := range (p * c)) (fun k => p ∣ k)
  rw [card_filter_dvd_range c hp.pos, card_range] at hcard
  rw [Nat.mul_div_cancel_left c hp.pos, Nat.mul_sub_one]
  have hpc : c * p = p * c := Nat.mul_comm c p
  omega

/-- Chinese remainder step: a congruence modulo `m ≠ 0` holds iff it holds modulo
every prime-power part `p ^ v_p(m)`. -/
theorem modEq_iff_forall_primeFactors {m a b : ℕ} (hm : m ≠ 0) :
    a ≡ b [MOD m] ↔ ∀ p ∈ m.primeFactors, a ≡ b [MOD p ^ m.factorization p] := by
  constructor
  · intro h p _
    exact Nat.ModEq.of_dvd (Nat.ordProj_dvd m p) h
  · intro h
    simp_rw [Nat.modEq_iff_dvd] at h ⊢
    rw [Nat.prod_primeFactors_pow_factorization hm]
    push_cast
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      simp only [Function.onFun]
      rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.isCoprime_iff_coprime]
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq) hpq
    · intro p hp
      exact_mod_cast h p hp

/-- `rad n` is positive. -/
theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- The totient of the radical: `φ (rad n) = ∏_{p ∣ n} (p - 1)`. -/
theorem totient_rad (n : ℕ) : (rad n).totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  have hpf : (rad n).primeFactors = n.primeFactors :=
    Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp
  have h := Nat.totient_mul_prod_primeFactors (rad n)
  rw [hpf] at h
  change (rad n).totient * rad n = rad n * _ at h
  rw [Nat.mul_comm (rad n)] at h
  exact Nat.eq_of_mul_eq_mul_right (rad_pos n) h

/-- `φ n · rad n = n · φ (rad n)`. -/
theorem totient_mul_rad (n : ℕ) : n.totient * rad n = n * (rad n).totient := by
  rw [totient_rad]
  exact Nat.totient_mul_prod_primeFactors n

/-- Splitting off the `p`-part: if `m = p^a n` with `p ∤ n`, `a ≠ 0`, then
`rad m = p · rad n`. -/
theorem rad_mul_prime_pow {p a n : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) : rad (p ^ a * n) = p * rad n := by
  have hpf : (p ^ a * n).primeFactors = insert p n.primeFactors := by
    rw [Nat.primeFactors_mul (pow_ne_zero a hp.ne_zero) hn, Nat.primeFactors_prime_pow ha hp]
    rfl
  have hnot : p ∉ n.primeFactors := fun h => hpn (Nat.dvd_of_mem_primeFactors h)
  unfold rad
  rw [hpf, prod_insert hnot]

/-- Arithmetic core: modulo `p ^ v_p(m)`, `(m/p)(p-1) ≡ φ m` iff
`p ∣ rad m / p + φ (rad m)`. -/
theorem modEq_local_iff {m p : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hpm : p ∣ m) :
    m / p * (p - 1) ≡ m.totient [MOD p ^ m.factorization p] ↔
      p ∣ rad m / p + (rad m).totient := by
  haveI := Fact.mk hp
  set a := m.factorization p with ha_def
  set n := m / p ^ a with hn_def
  have ha : 0 < a := hp.factorization_pos_of_dvd hm hpm
  have hmn : m = p ^ a * n := (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hcop : p.Coprime n := Nat.coprime_ordCompl hp hm
  have hpn : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hn0 : n ≠ 0 := fun h => hm (by rw [hmn, h, mul_zero])
  have hpa : p ^ a = p ^ (a - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel ha]
  -- the left-hand side
  have hφm : m.totient = p ^ (a - 1) * ((p - 1) * n.totient) := by
    rw [hmn, Nat.totient_mul (Nat.Coprime.pow_left a hcop), Nat.totient_prime_pow hp ha]
    ring
  have hmp : m / p * (p - 1) = p ^ (a - 1) * ((p - 1) * n) := by
    have : m = p * (p ^ (a - 1) * n) := by rw [hmn, hpa]; ring
    rw [this, Nat.mul_div_cancel_left _ hp.pos]
    ring
  have hlhs : m / p * (p - 1) ≡ m.totient [MOD p ^ a] ↔ (n : ZMod p) = n.totient := by
    rw [hmp, hφm, hpa, Nat.ModEq.mul_left_cancel_iff' (pow_ne_zero _ hp.ne_zero),
      ZMod.natCast_eq_natCast_iff]
    constructor
    · intro h
      have hg : Nat.gcd p (p - 1) = 1 := by
        have := (Nat.coprime_self_sub_right hp.one_lt.le).mpr (Nat.coprime_one_right p)
        simpa using this
      exact Nat.ModEq.cancel_left_of_coprime hg h
    · intro h
      exact Nat.ModEq.mul_left _ h
  -- the right-hand side
  have hrad : rad m = p * rad n := by rw [hmn]; exact rad_mul_prime_pow hp ha.ne' hn0 hpn
  have hradcop : p.Coprime (rad n) :=
    Nat.Coprime.coprime_dvd_right (Nat.prod_primeFactors_dvd n) hcop
  have hrhs : p ∣ rad m / p + (rad m).totient ↔ (rad n : ZMod p) = (rad n).totient := by
    rw [hrad, Nat.mul_div_cancel_left _ hp.pos, Nat.totient_mul hradcop,
      Nat.totient_prime hp, ← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hp.one_lt.le, ZMod.natCast_self]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  rw [hlhs, hrhs]
  -- the identity φ n · rad n = n · φ (rad n), read in the field `ZMod p`
  have hid : (n.totient : ZMod p) * rad n = n * (rad n).totient := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) (totient_mul_rad n)
  have hN : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hR : (rad n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hradcop
  constructor
  · intro h
    rw [← h] at hid
    exact mul_left_cancel₀ hN hid
  · intro h
    rw [← h] at hid
    exact (mul_right_cancel₀ hR hid).symm

/-- **Radical criterion.** For every `m`, `∑_{k<m} k^φ(m) ≡ φ(m) (mod m)` iff every
prime `p ∣ m` divides `rad m / p + φ (rad m)`. -/
theorem powerSumCongr_iff_radicalCriterion (m : ℕ) :
    PowerSumCongr m ↔ RadicalCriterion m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [PowerSumCongr, RadicalCriterion]
  unfold PowerSumCongr RadicalCriterion
  rw [modEq_iff_forall_primeFactors hm.ne']
  refine forall₂_congr fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpm := Nat.dvd_of_mem_primeFactors hp
  have hloc := sum_pow_modEq_local hpp hm.ne' hpm
  rw [← modEq_local_iff hpp hm.ne' hpm]
  exact ⟨fun h => hloc.symm.trans h, fun h => hloc.trans h⟩

/-! ## Consequence (i): prime powers -/

/-- Every prime power satisfies the radical criterion. -/
theorem radicalCriterion_of_isPrimePow {m : ℕ} (h : IsPrimePow m) : RadicalCriterion m := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp h
  have hpf : (p ^ k).primeFactors = {p} := Nat.primeFactors_prime_pow hk.ne' hp
  have hrad : rad (p ^ k) = p := by simp only [rad, hpf, prod_singleton]
  intro q hq
  rw [hpf, mem_singleton] at hq
  subst hq
  rw [hrad, Nat.div_self hp.pos, Nat.totient_prime hp, Nat.add_sub_cancel' hp.one_lt.le]

/-- **Consequence (i).** Every prime power `m` satisfies
`∑_{k<m} k^φ(m) ≡ φ(m) (mod m)`. -/
theorem powerSumCongr_of_isPrimePow {m : ℕ} (h : IsPrimePow m) : PowerSumCongr m :=
  (powerSumCongr_iff_radicalCriterion m).mpr (radicalCriterion_of_isPrimePow h)

/-! ## Consequence (ii): even non-prime-powers -/

/-- A number `m ≥ 2` that is not a prime power has at least two distinct prime factors. -/
theorem two_le_card_primeFactors {m : ℕ} (h2 : 2 ≤ m) (hpp : ¬ IsPrimePow m) :
    2 ≤ #m.primeFactors := by
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have h1 : #m.primeFactors ≠ 1 := fun h => hpp (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  have h0 : 0 < #m.primeFactors := card_pos.mpr hne
  omega

/-- An even `m ≥ 2` that is not a prime power fails the radical criterion at `p = 2`:
`rad m / 2` is odd while `φ (rad m)` is even. -/
theorem not_radicalCriterion_of_even {m : ℕ} (h2 : 2 ≤ m) (heven : Even m)
    (hpp : ¬ IsPrimePow m) : ¬ RadicalCriterion m := by
  intro hc
  have h2m : 2 ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp heven, by omega⟩
  obtain ⟨q, hq, hq2⟩ := exists_mem_ne (two_le_card_primeFactors h2 hpp) 2
  set s := ∏ ℓ ∈ m.primeFactors.erase 2, ℓ with hs_def
  have hr : rad m = 2 * s := (mul_prod_erase _ _ h2m).symm
  have hsodd : ¬ 2 ∣ s := by
    rw [hs_def, Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨ℓ, hℓ, hdvd⟩
    have hℓp := Nat.prime_of_mem_primeFactors (mem_of_mem_erase hℓ)
    exact ne_of_mem_erase hℓ ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓp).mp hdvd).symm
  have hqs : q ≤ s := by
    have hqmem : q ∈ m.primeFactors.erase 2 := mem_erase.mpr ⟨hq2, hq⟩
    have hspos : 0 < s := prod_pos fun ℓ hℓ =>
      (Nat.prime_of_mem_primeFactors (mem_of_mem_erase hℓ)).pos
    exact Nat.le_of_dvd hspos (dvd_prod_of_mem _ hqmem)
  have hq3 : 3 ≤ q := by
    have := (Nat.prime_of_mem_primeFactors hq).two_le
    omega
  have hφ : 2 ∣ (rad m).totient := even_iff_two_dvd.mp (Nat.totient_even (by omega))
  have hdiv : rad m / 2 = s := by rw [hr, Nat.mul_div_cancel_left _ two_pos]
  have hcrit := hc 2 h2m
  rw [hdiv, Nat.dvd_add_left hφ] at hcrit
  exact hsodd hcrit

/-- **Consequence (ii).** No even `m ≥ 2` that is not a prime power satisfies
`∑_{k<m} k^φ(m) ≡ φ(m) (mod m)`. -/
theorem not_powerSumCongr_of_even {m : ℕ} (h2 : 2 ≤ m) (heven : Even m)
    (hpp : ¬ IsPrimePow m) : ¬ PowerSumCongr m := by
  rw [powerSumCongr_iff_radicalCriterion]
  exact not_radicalCriterion_of_even h2 heven hpp

/-! ## Consequence (iii): at least nine prime factors -/

/-- For `S` a finite set of integers `≥ 1`, `1 ≤ ∑ 1/p + ∏ (1 - 1/p)`. -/
theorem one_le_sum_inv_add_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p) :
    1 ≤ ∑ p ∈ S, (1 / p : ℚ) + ∏ p ∈ S, (1 - 1 / p : ℚ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih fun p hp => hS p (mem_insert_of_mem hp)
    have hle : ∏ p ∈ s, (1 - 1 / p : ℚ) ≤ 1 := by
      apply prod_le_one
      · intro p hp
        have : (1 : ℚ) ≤ p := by exact_mod_cast hS p (mem_insert_of_mem hp)
        rw [sub_nonneg]; exact div_le_one_of_le₀ this (by positivity)
      · intro p _
        have : (0 : ℚ) ≤ 1 / p := by positivity
        linarith
    have ha0 : (0 : ℚ) ≤ 1 / a := by positivity
    have hkey : 1 / (a : ℚ) + ∑ p ∈ s, (1 / p : ℚ) + (1 - 1 / a) * ∏ p ∈ s, (1 - 1 / p : ℚ) =
        (∑ p ∈ s, (1 / p : ℚ) + ∏ p ∈ s, (1 - 1 / p : ℚ)) +
          1 / a * (1 - ∏ p ∈ s, (1 - 1 / p : ℚ)) := by ring
    rw [hkey]
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hle)]

/-- For `S` a set of integers `≥ 2` with at least two elements,
`1 < ∑ 1/p + ∏ (1 - 1/p)` (strict Weierstrass-type inequality). -/
theorem one_lt_sum_inv_add_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (hcard : 2 ≤ #S) :
    1 < ∑ p ∈ S, (1 / p : ℚ) + ∏ p ∈ S, (1 - 1 / p : ℚ) := by
  obtain ⟨a, ha⟩ : S.Nonempty := card_pos.mp (by omega)
  set s := S.erase a with hs_def
  have hsS : ∀ p ∈ s, p ∈ S := fun p hp => mem_of_mem_erase hp
  obtain ⟨b, hb⟩ : s.Nonempty := card_pos.mp (by rw [hs_def, card_erase_of_mem ha]; omega)
  rw [← insert_erase ha, sum_insert (notMem_erase a S), prod_insert (notMem_erase a S)]
  have hfac : ∀ p ∈ S, (0 : ℚ) ≤ 1 - 1 / p ∧ (1 : ℚ) - 1 / p ≤ 1 := by
    intro p hp
    have h1 : (1 : ℚ) ≤ p := by exact_mod_cast (by have := hS p hp; omega : 1 ≤ p)
    have h0 : (0 : ℚ) ≤ 1 / p := by positivity
    exact ⟨sub_nonneg.mpr (div_le_one_of_le₀ h1 (by positivity)), by linarith⟩
  have hge := one_le_sum_inv_add_prod s fun p hp => by have := hS p (hsS p hp); omega
  have hrest : ∏ p ∈ s.erase b, (1 - 1 / p : ℚ) ≤ 1 :=
    prod_le_one (fun p hp => (hfac p (hsS p (mem_of_mem_erase hp))).1)
      (fun p hp => (hfac p (hsS p (mem_of_mem_erase hp))).2)
  have hrest0 : 0 ≤ ∏ p ∈ s.erase b, (1 - 1 / p : ℚ) :=
    prod_nonneg fun p hp => (hfac p (hsS p (mem_of_mem_erase hp))).1
  have hb0 : (0 : ℚ) < 1 / b := by
    have := hS b (hsS b hb); positivity
  have hlt : ∏ p ∈ s, (1 - 1 / p : ℚ) < 1 := by
    rw [← mul_prod_erase s _ hb]
    nlinarith [(hfac b (hsS b hb)).1]
  have ha0 : (0 : ℚ) < 1 / a := by
    have := hS a ha; positivity
  have hkey : 1 / (a : ℚ) + ∑ p ∈ s, (1 / p : ℚ) + (1 - 1 / a) * ∏ p ∈ s, (1 - 1 / p : ℚ) =
      (∑ p ∈ s, (1 / p : ℚ) + ∏ p ∈ s, (1 - 1 / p : ℚ)) +
        1 / a * (1 - ∏ p ∈ s, (1 - 1 / p : ℚ)) := by ring
  rw [hkey]
  nlinarith [mul_pos ha0 (sub_pos.mpr hlt)]

/-- Clearing denominators: for a finite set `S` of primes with product `r`,
`r · (∑ 1/p + ∏ (1 - 1/p)) = ∑ r/p + ∏ (p - 1)`. -/
theorem cast_sum_div_add_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((∑ p ∈ S, (∏ q ∈ S, q) / p + ∏ p ∈ S, (p - 1) : ℕ) : ℚ) =
      (∏ q ∈ S, q : ℕ) * (∑ p ∈ S, (1 / p : ℚ) + ∏ p ∈ S, (1 - 1 / p : ℚ)) := by
  rw [mul_add, mul_sum]
  push_cast
  congr 1
  · refine sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    rw [Nat.cast_div (dvd_prod_of_mem _ hp) hp0]
    push_cast
    field_simp
  · rw [← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    rw [Nat.cast_sub (hS p hp).one_lt.le]
    field_simp
    push_cast
    ring

/-- Under the radical criterion, `rad m ∣ ∑_{p ∣ m} rad m / p + φ (rad m)`. -/
theorem rad_dvd_of_radicalCriterion {m : ℕ} (hc : RadicalCriterion m) :
    rad m ∣ ∑ p ∈ m.primeFactors, rad m / p + (rad m).totient := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).prime
  · intro p hp
    rw [← add_sum_erase _ _ hp, add_assoc, add_comm (∑ q ∈ _, _), ← add_assoc]
    refine dvd_add (hc p hp) (dvd_sum fun q hq => ?_)
    have hqm : q ∈ m.primeFactors := mem_of_mem_erase hq
    have hq0 : 0 < q := (Nat.prime_of_mem_primeFactors hqm).pos
    have hdiv : rad m / q = ∏ ℓ ∈ m.primeFactors.erase q, ℓ := by
      unfold rad
      rw [← mul_prod_erase _ _ hqm, Nat.mul_div_cancel_left _ hq0]
    rw [hdiv]
    exact dvd_prod_of_mem _ (mem_erase.mpr ⟨(ne_of_mem_erase hq).symm, hp⟩)

/-- The eight odd primes `3, 5, …, 23` have reciprocal sum `< 1`. -/
theorem sum_inv_first_odd_primes_lt_one :
    ∑ q ∈ ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), (1 / q : ℚ) < 1 := by
  norm_num

/-- An odd prime not among `3, 5, …, 23` is at least `29`. -/
theorem twentynine_le_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : p ∉ ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ)) : 29 ≤ p := by
  by_contra hlt
  rw [not_le] at hlt
  interval_cases p <;> simp_all <;> norm_num at hp

/-- Any set of at most eight odd primes has reciprocal sum `< 1`. -/
theorem sum_inv_lt_one_of_card_le_eight (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hcard : #P ≤ 8) : ∑ p ∈ P, (1 / p : ℚ) < 1 := by
  set Q : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23} with hQ_def
  have hQcard : #Q = 8 := by rw [hQ_def]; rfl
  have hQle : ∀ q ∈ Q, q ≤ 23 := by
    intro q hq; rw [hQ_def] at hq; simp only [mem_insert, mem_singleton] at hq; omega
  have hbig : ∀ p ∈ P \ Q, 29 ≤ p := by
    intro p hp
    rw [mem_sdiff] at hp
    exact twentynine_le_of_prime (hP p hp.1).1 (hP p hp.1).2 hp.2
  have hcd : #(P \ Q) ≤ #(Q \ P) := by
    have h1 := card_sdiff_add_card_inter P Q
    have h2 := card_sdiff_add_card_inter Q P
    rw [inter_comm] at h2
    omega
  have hlow : ∑ p ∈ P \ Q, (1 / p : ℚ) ≤ #(P \ Q) • (1 / 29 : ℚ) := by
    apply sum_le_card_nsmul
    intro p hp
    have : (29 : ℚ) ≤ p := by exact_mod_cast hbig p hp
    exact one_div_le_one_div_of_le (by norm_num) this
  have hhigh : #(Q \ P) • (1 / 29 : ℚ) ≤ ∑ q ∈ Q \ P, (1 / q : ℚ) := by
    apply card_nsmul_le_sum
    intro q hq
    have hqQ := (mem_sdiff.mp hq).1
    have hq0 : (0 : ℚ) < q := by
      have : q ≠ 0 := by rw [hQ_def] at hqQ; simp only [mem_insert, mem_singleton] at hqQ; omega
      exact_mod_cast Nat.pos_of_ne_zero this
    have : (q : ℚ) ≤ 29 := by exact_mod_cast (by have := hQle q hqQ; omega : q ≤ 29)
    exact one_div_le_one_div_of_le hq0 this
  have hmid : #(P \ Q) • (1 / 29 : ℚ) ≤ #(Q \ P) • (1 / 29 : ℚ) := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    gcongr
  have hsplitP := sum_inter_add_sum_sdiff P Q (fun p => (1 / p : ℚ))
  have hsplitQ := sum_inter_add_sum_sdiff Q P (fun p => (1 / p : ℚ))
  rw [inter_comm] at hsplitQ
  have hQsum := sum_inv_first_odd_primes_lt_one
  rw [← hQ_def] at hQsum
  linarith

/-- Under the radical criterion, an `m ≥ 2` that is not a prime power is odd and has
at least nine distinct prime factors. -/
theorem odd_and_nine_le_card_of_radicalCriterion {m : ℕ} (h2 : 2 ≤ m) (hpp : ¬ IsPrimePow m)
    (hc : RadicalCriterion m) : Odd m ∧ 9 ≤ #m.primeFactors := by
  have hodd : Odd m := by
    rcases Nat.even_or_odd m with he | ho
    · exact absurd hc (not_radicalCriterion_of_even h2 he hpp)
    · exact ho
  refine ⟨hodd, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set S := m.primeFactors with hS_def
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hS2 : ∀ p ∈ S, p ≠ 2 := by
    intro p hp hp2
    rw [hp2] at hp
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have hcard2 : 2 ≤ #S := two_le_card_primeFactors h2 hpp
  -- integrality of `∑ 1/p + ∏ (1 - 1/p)`
  obtain ⟨K, hK⟩ := rad_dvd_of_radicalCriterion hc
  have hG := cast_sum_div_add_prod S hSprime
  rw [← totient_rad] at hG
  change ((∑ p ∈ S, rad m / p + (rad m).totient : ℕ) : ℚ) = (rad m : ℕ) * _ at hG
  rw [hK] at hG
  push_cast at hG
  have hr0 : (rad m : ℚ) ≠ 0 := by exact_mod_cast (rad_pos m).ne'
  have hGK := mul_left_cancel₀ hr0 hG
  -- the value exceeds `1`, hence is at least `2`
  have h1 := one_lt_sum_inv_add_prod S (fun p hp => (hSprime p hp).two_le) hcard2
  rw [← hGK] at h1
  have hK2 : (2 : ℚ) ≤ K := by
    have hK1 : 1 < K := by exact_mod_cast h1
    exact_mod_cast hK1
  have hprod : ∏ p ∈ S, (1 - 1 / p : ℚ) ≤ 1 := by
    apply prod_le_one
    · intro p hp
      have : (1 : ℚ) ≤ p := by exact_mod_cast (hSprime p hp).one_lt.le
      exact sub_nonneg.mpr (div_le_one_of_le₀ this (by positivity))
    · intro p _
      have : (0 : ℚ) ≤ 1 / p := by positivity
      linarith
  -- so `∑ 1/p ≥ 1`, impossible for at most eight odd primes
  have hsum := sum_inv_lt_one_of_card_le_eight S (fun p hp => ⟨hSprime p hp, hS2 p hp⟩)
    (by omega)
  linarith

/-- **Consequence (iii) and the reduction.** If `m ≥ 2` is not a prime power and
`∑_{k<m} k^φ(m) ≡ φ(m) (mod m)`, then `m` is odd and has at least nine distinct prime
factors. Equivalently, any counterexample to the Ordowski–Resta conjecture for A000961
is odd with `ω(m) ≥ 9`. -/
theorem odd_and_nine_le_card_of_powerSumCongr {m : ℕ} (h2 : 2 ≤ m) (hpp : ¬ IsPrimePow m)
    (hc : PowerSumCongr m) : Odd m ∧ 9 ≤ #m.primeFactors :=
  odd_and_nine_le_card_of_radicalCriterion h2 hpp ((powerSumCongr_iff_radicalCriterion m).mp hc)

/-- **Consequence (iii), as stated.** No `m` with between two and eight distinct prime
factors satisfies `∑_{k<m} k^φ(m) ≡ φ(m) (mod m)`. -/
theorem not_powerSumCongr_of_card_primeFactors {m : ℕ} (hlo : 2 ≤ #m.primeFactors)
    (hhi : #m.primeFactors ≤ 8) : ¬ PowerSumCongr m := by
  intro hc
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hlo
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hlo
  have hpp : ¬ IsPrimePow m := fun h => by
    rw [isPrimePow_iff_card_primeFactors_eq_one] at h
    omega
  have := (odd_and_nine_le_card_of_powerSumCongr (by omega) hpp hc).2
  omega

/-! ## Non-vacuity of the hypotheses -/

/-- `m = 6` jointly satisfies the hypotheses of `not_powerSumCongr_of_even`. -/
example : 2 ≤ 6 ∧ Even 6 ∧ ¬ IsPrimePow 6 := by
  refine ⟨by norm_num, by decide, ?_⟩
  rw [isPrimePow_iff_card_primeFactors_eq_one]
  simp only [Nat.primeFactors, Nat.primeFactorsList_ofNat]
  decide

/-- `m = 15` (two prime factors) is excluded by `not_powerSumCongr_of_card_primeFactors`. -/
example : ¬ PowerSumCongr 15 := by
  apply not_powerSumCongr_of_card_primeFactors <;>
    simp only [Nat.primeFactors, Nat.primeFactorsList_ofNat] <;> decide

end Candidates.A000961PowerSumRadical
