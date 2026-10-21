/-
# A354139 — least block length `m` with `n ∣ (k+1)^n + ⋯ + (k+m)^n` for all `k`

## OEIS source (`oeis show A354139`, live entry checked 2026-10-21)

```
NAME:     a(n) is the least positive integer m such that
          (k+1)^n + (k+2)^n + ... + (k+m)^n == 0 (mod n) for every positive
          integer k.
TERMS:    1,4,3,8,5,36,7,16,3,20,11,72,13,28,15,32,17,108,19,200,21,44,23,144,
          5,52,3,56,29,180,31,64,33,68,35,216,37,76,39,400,41,1764,43,88,15,92,
          47,288,7,20,51,104,53,324,55,112,57,116,59,1800,61,124,21,128,65,396,
          67,136,69,140,71
COMMENT:  a(n) divides n * A007947(n).
FORMULA:  a(2^t) = 2^(t+1) for integers t>0.
          a(n) = A007947(n) for odd integers n.
          Conjecture: a(n) = A007947(n) * A193267(n).
AUTHOR:   Dimitrios T. Tambakos, May 18 2022
```

The conjecture line carries no separate attribution or date in the entry; it
belongs to the entry as authored by Dimitrios T. Tambakos (May 18 2022).

`A007947(n)` is the squarefree kernel `rad n = ∏_{p ∣ n} p`.  `A193267` is
"the number 1 alternating with the numbers A006953/A002445"; its entry carries
Peter Luschny's characterization (Mar 12 2018): "a(n) is the product over all
prime powers p^e, where p^e is the highest power of p dividing n and p-1
divides n."  This module uses Luschny's characterization as the definition of
`a193267`; the bridge to the Bernoulli-denominator definition (von
Staudt–Clausen) is *not* formalized here and is a disclosed, unpaid link.

## Status

Triage (2026-10-21): open — no proof in the entry or found in the
literature (a search with no match is not evidence of novelty).
Computation: brute force over `n = 1..200` reproduces every listed term and
agrees with `rad n * a193267 n` (Python, this campaign; earlier triage to 300).

This module proves the conjecture (in Luschny's form) for every `n ≥ 1`.

## Proof outline

Fix `p ^ e ∥ n` and work in `ZMod (p ^ e)`.
1. `j ^ n` modulo `p ^ e` depends only on `j mod p` (`dvd_sub_pow_of_dvd_sub`).
2. Comparing the windows starting at `k = p - 1` and `k = p` forces `p ∣ m`.
3. For `m = p t`, the window sum is `t · T` with `T = ∑_{i<p} i ^ n`.
4. If `(p - 1) ∣ n` then `T = p - 1` (Euler), so `p ^ e ∣ window ↔ p ^ (e+1) ∣ m`.
5. Otherwise some unit `u` of `ZMod p` has `u ^ n ≠ 1`
   (`FiniteField.sum_pow_units`), and reindexing by `u` gives `T = 0`.
6. Coprime prime powers assemble the local conditions into
   `rad n * a193267 n ∣ m`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A354139LeastSumRad

open Finset

/-! ## Definitions -/

/-- `rad n` (OEIS A007947): the product of the distinct primes dividing `n`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- `a193267 n` (OEIS A193267, Luschny's characterization): the product of the
prime powers `p ^ e ∥ n` with `(p - 1) ∣ n`. -/
def a193267 (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors with (p - 1) ∣ n, p ^ n.factorization p

/-! ## Ground truth -/

/-- `rad` agrees with the first terms of A007947. -/
theorem rad_values :
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].map rad = [1, 2, 3, 2, 5, 6, 7, 2, 3, 10, 11, 6] := by
  simp only [List.map_cons, List.map_nil, rad, ← Nat.toFinset_factors,
    Nat.primeFactorsList_ofNat]
  decide

/-- `a193267` agrees with the first terms of A193267 (offset 1). -/
theorem a193267_values :
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].map a193267 = [1, 2, 1, 4, 1, 6, 1, 8, 1, 2, 1, 12] := by
  simp only [List.map_cons, List.map_nil, a193267, ← Nat.toFinset_factors,
    ← Nat.primeFactorsList_count_eq, Nat.primeFactorsList_ofNat]
  decide

/-- `rad n * a193267 n` reproduces the first 24 listed terms of A354139. -/
theorem rad_mul_a193267_values :
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
      21, 22, 23, 24].map (fun n => rad n * a193267 n)
      = [1, 4, 3, 8, 5, 36, 7, 16, 3, 20, 11, 72, 13, 28, 15, 32, 17, 108, 19, 200,
         21, 44, 23, 144] := by
  simp only [List.map_cons, List.map_nil, rad, a193267, ← Nat.toFinset_factors,
    ← Nat.primeFactorsList_count_eq, Nat.primeFactorsList_ofNat]
  decide

/-- `rad n * a193267 n` at the larger listed terms `n = 42, 60`. -/
theorem rad_mul_a193267_values_large :
    [42, 60].map (fun n => rad n * a193267 n) = [1764, 1800] := by
  simp only [List.map_cons, List.map_nil, rad, a193267, ← Nat.toFinset_factors,
    ← Nat.primeFactorsList_count_eq, Nat.primeFactorsList_ofNat]
  decide

/-! ## Local analysis at a prime power `p ^ e ∣ n` -/

/-- In `ZMod (p ^ e)`, elements congruent modulo `p` have equal `p ^ (e-1)`-th powers. -/
theorem pow_eq_of_dvd_sub {p e : ℕ} (he : 1 ≤ e) {x y : ZMod (p ^ e)}
    (h : (p : ZMod (p ^ e)) ∣ x - y) : x ^ p ^ (e - 1) = y ^ p ^ (e - 1) := by
  have hd := dvd_sub_pow_of_dvd_sub h (e - 1)
  rw [Nat.sub_add_cancel he] at hd
  have h0 : ((p : ZMod (p ^ e)) ^ e) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h0, zero_dvd_iff, sub_eq_zero] at hd
  exact hd

/-- If `p ^ e ∣ n` and `a ≡ b [MOD p]`, then `a ^ n = b ^ n` in `ZMod (p ^ e)`. -/
theorem natCast_pow_eq_of_modEq {p e n : ℕ} (he : 1 ≤ e) (hpe : p ^ e ∣ n) {a b : ℕ}
    (hab : a ≡ b [MOD p]) : ((a : ZMod (p ^ e))) ^ n = ((b : ZMod (p ^ e))) ^ n := by
  obtain ⟨c, hc⟩ : p ^ (e - 1) ∣ n := (pow_dvd_pow p (Nat.sub_le e 1)).trans hpe
  have hdvd : (p : ZMod (p ^ e)) ∣ (b : ZMod (p ^ e)) - (a : ZMod (p ^ e)) := by
    have hz : (p : ℤ) ∣ (b : ℤ) - (a : ℤ) := (Nat.modEq_iff_dvd).1 hab
    have := map_dvd (Int.castRingHom (ZMod (p ^ e))) hz
    simpa using this
  rw [hc, pow_mul, pow_mul, pow_eq_of_dvd_sub he hdvd]

/-- A window of `p` consecutive `n`-th powers has the same sum in `ZMod (p ^ e)` for
every start `c`. -/
theorem sum_window {p e n : ℕ} (he : 1 ≤ e) (hpe : p ^ e ∣ n) (c : ℕ) :
    ∑ i ∈ range p, ((c + i : ℕ) : ZMod (p ^ e)) ^ n
      = ∑ i ∈ range p, ((i : ℕ) : ZMod (p ^ e)) ^ n := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun i => ((c + i : ℕ) : ZMod (p ^ e)) ^ n) p
    have h2 := Finset.sum_range_succ' (fun i => ((c + i : ℕ) : ZMod (p ^ e)) ^ n) p
    have hper : ((c + p : ℕ) : ZMod (p ^ e)) ^ n = ((c + 0 : ℕ) : ZMod (p ^ e)) ^ n :=
      natCast_pow_eq_of_modEq he hpe (by simp [Nat.ModEq])
    rw [h1, hper] at h2
    have h3 := add_right_cancel h2
    rw [h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_right_comm, Nat.add_assoc]

/-- A window of `p * t` consecutive `n`-th powers is `t` times one period sum in
`ZMod (p ^ e)`. -/
theorem sum_block {p e n : ℕ} (he : 1 ≤ e) (hpe : p ^ e ∣ n) (c t : ℕ) :
    ∑ i ∈ range (p * t), ((c + i : ℕ) : ZMod (p ^ e)) ^ n
      = (t : ZMod (p ^ e)) * ∑ i ∈ range p, ((i : ℕ) : ZMod (p ^ e)) ^ n := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hw := sum_window he hpe (c + p * t)
    rw [← hw]
    rw [Nat.cast_succ, add_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_assoc]

/-- If `(p - 1) ∣ n`, `p ^ e ∣ n` and `p ∤ j`, then `j ^ n = 1` in `ZMod (p ^ e)` (Euler). -/
theorem natCast_pow_eq_one {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hpe : p ^ e ∣ n)
    (hpn : (p - 1) ∣ n) {j : ℕ} (hj : ¬ p ∣ j) : ((j : ZMod (p ^ e))) ^ n = 1 := by
  have hcop : Nat.Coprime j (p ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_comm).1 ((hp.coprime_iff_not_dvd).2 hj))
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have htot : Nat.totient (p ^ e) ∣ n := by
    rw [Nat.totient_prime_pow hp (by omega)]
    have hc : Nat.Coprime (p ^ (e - 1)) (p - 1) :=
      Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).2
        (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos one_pos)))
    exact hc.mul_dvd_of_dvd_of_dvd ((pow_dvd_pow p (Nat.sub_le e 1)).trans hpe) hpn
  obtain ⟨c, hc⟩ := htot
  have hu := ZMod.pow_totient (ZMod.unitOfCoprime j hcop)
  have hu' : ((j : ZMod (p ^ e))) ^ Nat.totient (p ^ e) = 1 := by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at hu
    exact hu
  rw [hc, pow_mul, hu', one_pow]

/-- If `(p - 1) ∣ n` then the period sum `∑_{i<p} i ^ n` is `p - 1` in `ZMod (p ^ e)`. -/
theorem sum_period_of_dvd {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hpe : p ^ e ∣ n)
    (hn : 0 < n) (hpn : (p - 1) ∣ n) :
    ∑ i ∈ range p, ((i : ℕ) : ZMod (p ^ e)) ^ n = ((p - 1 : ℕ) : ZMod (p ^ e)) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  rw [show range p = range (q + 1) by rw [hq], Finset.sum_range_succ',
    show p - 1 = q by omega]
  have hterm : ∀ i ∈ range q, ((i + 1 : ℕ) : ZMod (p ^ e)) ^ n = 1 := by
    intro i hi
    refine natCast_pow_eq_one hp he hpe hpn ?_
    rw [Finset.mem_range] at hi
    exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) (by omega)
  rw [Finset.sum_congr rfl hterm]
  simp [zero_pow hn.ne']

/-- If `(p - 1) ∤ n` then some unit `u` of `ZMod p` has `u ^ n ≠ 1`. -/
theorem exists_unit_pow_ne_one {p n : ℕ} (hp : p.Prime) (hpn : ¬ (p - 1) ∣ n) :
    ∃ u : (ZMod p)ˣ, (u : ZMod p) ^ n ≠ 1 := by
  haveI := Fact.mk hp
  by_contra h
  push Not at h
  have hs := FiniteField.sum_pow_units (ZMod p) n
  rw [ZMod.card, if_neg hpn, Finset.sum_congr rfl (fun u _ => h u), Finset.sum_const,
    Finset.card_univ, ZMod.card_units, nsmul_one] at hs
  have hdvd : p ∣ p - 1 := (ZMod.natCast_eq_zero_iff (p - 1) p).1 hs
  exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos one_pos) hdvd

/-- A sum over `range p` equals the sum over `ZMod p` through `ZMod.val`. -/
theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p] (f : ℕ → M) :
    ∑ i ∈ range p, f i = ∑ x : ZMod p, f x.val := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a ha; rw [ZMod.val_cast_of_lt (Finset.mem_range.1 ha)]

/-- An element of `ZMod (p ^ e)` whose reduction modulo `p` is nonzero is a unit. -/
theorem isUnit_of_castHom_ne_zero {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (w : ZMod (p ^ e))
    (hw : ZMod.castHom (dvd_pow_self p (by omega : e ≠ 0)) (ZMod p) w ≠ 0) : IsUnit w := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val w] at hw ⊢
  rw [map_natCast] at hw
  rw [ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right e ((Nat.coprime_comm).1 ((hp.coprime_iff_not_dvd).2 ?_))
  intro hd
  exact hw ((ZMod.natCast_eq_zero_iff _ _).2 hd)

/-- If `(p - 1) ∤ n` and `p ^ e ∣ n`, then `∑_{i<p} i ^ n = 0` in `ZMod (p ^ e)`. -/
theorem sum_period_eq_zero {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hpe : p ^ e ∣ n)
    (hpn : ¬ (p - 1) ∣ n) :
    ∑ i ∈ range p, ((i : ℕ) : ZMod (p ^ e)) ^ n = 0 := by
  haveI := Fact.mk hp
  obtain ⟨u, hu⟩ := exists_unit_pow_ne_one hp hpn
  rw [sum_range_eq_sum_zmod p (fun i => ((i : ℕ) : ZMod (p ^ e)) ^ n)]
  set a : ℕ := (u : ZMod p).val with ha
  have hmul : ∀ x : ZMod p, ((((u : ZMod p) * x).val : ℕ) : ZMod (p ^ e)) ^ n
      = ((a : ZMod (p ^ e))) ^ n * (((x.val : ℕ) : ZMod (p ^ e))) ^ n := by
    intro x
    rw [ZMod.val_mul, natCast_pow_eq_of_modEq he hpe (Nat.mod_modEq _ _), Nat.cast_mul, mul_pow]
  have hperm := Equiv.sum_comp (Units.mulLeft u) (fun x : ZMod p => ((x.val : ℕ) : ZMod (p ^ e)) ^ n)
  simp only [Units.mulLeft_apply, hmul] at hperm
  rw [← Finset.mul_sum] at hperm
  have hzero : ((a : ZMod (p ^ e)) ^ n - 1) * ∑ x : ZMod p, ((x.val : ℕ) : ZMod (p ^ e)) ^ n = 0 := by
    rw [sub_mul, one_mul, hperm, sub_self]
  have hunit : IsUnit ((a : ZMod (p ^ e)) ^ n - 1) := by
    refine isUnit_of_castHom_ne_zero hp he _ ?_
    rw [map_sub, map_pow, map_natCast, map_one, ha, ZMod.natCast_zmod_val]
    exact sub_ne_zero.2 hu
  exact hunit.mul_right_eq_zero.1 hzero

/-- Reindex `∑_{i=1}^{m} (k+i)^n` as `∑_{i<m} (k+1+i)^n`. -/
theorem sum_Icc_eq_sum_range (k m n : ℕ) :
    ∑ i ∈ Icc 1 m, (k + i) ^ n = ∑ i ∈ range m, (k + 1 + i) ^ n := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_assoc]

/-- Sliding a window of length `m` by one: `S(c) + (c+m)^n = c^n + S(c+1)`. -/
theorem sum_shift (c m n : ℕ) :
    ∑ i ∈ range m, (c + i) ^ n + (c + m) ^ n = c ^ n + ∑ i ∈ range m, (c + 1 + i) ^ n := by
  rw [← Finset.sum_range_succ, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_right_comm, Nat.add_assoc]

/-- For `m = p * t`, the window sum `∑_{i=1}^{m} (k+i)^n` is `t * ∑_{i<p} i^n` in
`ZMod (p ^ e)`. -/
theorem natCast_sum_eq {p e n : ℕ} (he : 1 ≤ e) (hpe : p ^ e ∣ n) (k t : ℕ) :
    (((∑ i ∈ Icc 1 (p * t), (k + i) ^ n : ℕ)) : ZMod (p ^ e))
      = (t : ZMod (p ^ e)) * ∑ i ∈ range p, ((i : ℕ) : ZMod (p ^ e)) ^ n := by
  rw [sum_Icc_eq_sum_range, Nat.cast_sum, ← sum_block he hpe (k + 1) t]
  simp only [Nat.cast_pow]

/-- If `p ^ e` (`e ≥ 1`, `p ^ e ∣ n`) divides every window sum of length `m`, then `p ∣ m`. -/
theorem dvd_of_forall_dvd {p e n m : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hpe : p ^ e ∣ n)
    (hn : 0 < n) (h : ∀ k, 0 < k → p ^ e ∣ ∑ i ∈ Icc 1 m, (k + i) ^ n) : p ∣ m := by
  have h1 := h (p - 1) (Nat.sub_pos_of_lt hp.one_lt)
  have h2 := h p hp.pos
  rw [sum_Icc_eq_sum_range, Nat.sub_add_cancel hp.one_lt.le] at h1
  rw [sum_Icc_eq_sum_range] at h2
  have hen : e ≤ n := by
    have hle : p ^ e ≤ n := Nat.le_of_dvd hn hpe
    have hlt : e < p ^ e := Nat.lt_pow_self hp.one_lt
    omega
  have hpn : p ^ e ∣ p ^ n := pow_dvd_pow p hen
  have hshift := sum_shift p m n
  have h3 : p ^ e ∣ ∑ i ∈ range m, (p + i) ^ n + (p + m) ^ n := by
    rw [hshift]; exact dvd_add hpn h2
  have h4 : p ^ e ∣ (p + m) ^ n := (Nat.dvd_add_right h1).1 h3
  have h5 : p ∣ (p + m) ^ n := (dvd_pow_self p (by omega : e ≠ 0)).trans h4
  exact (Nat.dvd_add_right (dvd_refl p)).1 (hp.dvd_of_dvd_pow h5)

/-- Local criterion: for `p ^ e ∣ n` with `e ≥ 1`, `p ^ e` divides every window sum of
length `m` iff `p ∣ m` and, when `(p - 1) ∣ n`, also `p ^ (e + 1) ∣ m`. -/
theorem forall_dvd_iff {p e n m : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hpe : p ^ e ∣ n)
    (hn : 0 < n) :
    (∀ k, 0 < k → p ^ e ∣ ∑ i ∈ Icc 1 m, (k + i) ^ n) ↔
      p ∣ m ∧ ((p - 1) ∣ n → p ^ (e + 1) ∣ m) := by
  have hcop : Nat.Coprime (p ^ e) (p - 1) :=
    Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).2
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos one_pos)))
  constructor
  · intro h
    have hpm := dvd_of_forall_dvd hp he hpe hn h
    refine ⟨hpm, fun hpn => ?_⟩
    obtain ⟨t, rfl⟩ := hpm
    have h1 := h 1 one_pos
    rw [← ZMod.natCast_eq_zero_iff, natCast_sum_eq he hpe, sum_period_of_dvd hp he hpe hn hpn,
      ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h1
    have ht : p ^ e ∣ t := hcop.dvd_of_dvd_mul_right h1
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left p ht
  · rintro ⟨hpm, hpn⟩ k _
    obtain ⟨t, rfl⟩ := hpm
    rw [← ZMod.natCast_eq_zero_iff, natCast_sum_eq he hpe]
    by_cases hd : (p - 1) ∣ n
    · have ht : p ^ e ∣ t := by
        have h1 := hpn hd
        rw [pow_succ'] at h1
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      rw [(ZMod.natCast_eq_zero_iff _ _).2 ht, zero_mul]
    · rw [sum_period_eq_zero hp he hpe hd, mul_zero]

/-! ## Assembly over the prime factors of `n` -/

/-- A product of powers of distinct primes divides `m` iff each factor does. -/
theorem prod_pow_dvd_iff (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (g : ℕ → ℕ) (m : ℕ) :
    (∏ p ∈ s, p ^ g p) ∣ m ↔ ∀ p ∈ s, p ^ g p ∣ m := by
  refine ⟨fun h p hp => (Finset.dvd_prod_of_mem _ hp).trans h, fun h => ?_⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime (a ^ g a) (∏ p ∈ s, p ^ g p) :=
      Nat.Coprime.prod_right fun q hq =>
        Nat.coprime_pow_primes _ _ (hs a (Finset.mem_insert_self a s))
          (hs q (Finset.mem_insert_of_mem hq)) (fun hEq => ha (hEq ▸ hq))
    exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_insert_self a s))
      (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
        (fun p hp => h p (Finset.mem_insert_of_mem hp)))

/-- `rad n * a193267 n` as a product of prime powers over the prime factors of `n`. -/
theorem rad_mul_a193267_eq (n : ℕ) :
    rad n * a193267 n = ∏ p ∈ n.primeFactors,
      p ^ (if (p - 1) ∣ n then n.factorization p + 1 else 1) := by
  rw [rad, a193267, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  split_ifs <;> simp [pow_succ']

/-- `n` is the product of `p ^ v_p(n)` over its prime factors. -/
theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rfl

/-- Global criterion: for `n ≥ 1`, `n` divides every window sum of length `m` iff
`rad n * a193267 n ∣ m`. -/
theorem forall_dvd_iff_dvd {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (∀ k, 0 < k → n ∣ ∑ i ∈ Icc 1 m, (k + i) ^ n) ↔ rad n * a193267 n ∣ m := by
  rw [rad_mul_a193267_eq, prod_pow_dvd_iff _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  have hloc : ∀ p ∈ n.primeFactors,
      ((∀ k, 0 < k → p ^ n.factorization p ∣ ∑ i ∈ Icc 1 m, (k + i) ^ n) ↔
        p ^ (if (p - 1) ∣ n then n.factorization p + 1 else 1) ∣ m) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have he : 1 ≤ n.factorization p :=
      hpp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)
    rw [forall_dvd_iff hpp he (Nat.ordProj_dvd n p) hn]
    split_ifs with hd
    · constructor
      · rintro ⟨_, h2⟩; exact h2 hd
      · intro h
        exact ⟨(dvd_pow_self p (by omega)).trans h, fun _ => h⟩
    · simp only [pow_one]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hd⟩⟩
  constructor
  · intro h p hp
    exact (hloc p hp).1 fun k hk => (Nat.ordProj_dvd n p).trans (h k hk)
  · intro h k hk
    have hprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) ∣
        ∑ i ∈ Icc 1 m, (k + i) ^ n :=
      (prod_pow_dvd_iff _ (fun p hp => Nat.prime_of_mem_primeFactors hp) _ _).2
        fun p hp => (hloc p hp).2 (h p hp) k hk
    rwa [prod_primeFactors_pow_factorization hn.ne'] at hprod

/-! ## The conjecture -/

/-- **A354139 conjecture (OEIS A354139, FORMULA line, entry by Dimitrios T. Tambakos,
May 18 2022).**  Verbatim: "Conjecture: a(n) = A007947(n) * A193267(n)."

Formal reading: for every `n ≥ 1`, the least positive `m` such that
`n ∣ (k+1)^n + ⋯ + (k+m)^n` for every positive integer `k` is
`rad n * a193267 n`, where `a193267` is Luschny's characterization of A193267
(product of `p ^ e ∥ n` with `(p - 1) ∣ n`). -/
theorem a354139_conjecture (n : ℕ) (hn : 0 < n) :
    IsLeast {m : ℕ | 0 < m ∧ ∀ k : ℕ, 0 < k → n ∣ ∑ i ∈ Icc 1 m, (k + i) ^ n}
      (rad n * a193267 n) := by
  have hpos : 0 < rad n * a193267 n := by
    rw [rad_mul_a193267_eq]
    exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  refine ⟨⟨hpos, (forall_dvd_iff_dvd hn _).2 dvd_rfl⟩, ?_⟩
  rintro m ⟨hm, h⟩
  exact Nat.le_of_dvd hm ((forall_dvd_iff_dvd hn m).1 h)

end Candidates.A354139LeastSumRad
