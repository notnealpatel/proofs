/-
# A097406 — largest primitive prime factor of 2^n - 1 is ≡ 1 (mod n)

## OEIS source (pulled with `oeis show A097406`, retrieved 2026-10-21)

```
NAME:     Largest primitive prime factor of 2^n-1, or a(n) = 1 if no such
          prime exists.
TERMS:    1,3,7,5,31,1,127,17,73,11,89,13,8191,43,151,257,131071,19,524287,41,
          337,683,178481,241,1801,2731,262657,113,2089,331,2147483647,65537,...
COMMENT:  By Zsigmondy's theorem, a(n) > 1 except for n = 1 or 6.
COMMENT (the conjectures):
  Conjectures: (1) For every n the highest unique prime factor is of the form
  kn+1. The values for k are in A097407. (2) For each composite n many factors
  of the form kn+1 occur intermittently but always singly in any cofactor
  pair. (3) For each prime n every factor is of the form kn+1.
COMMENT:  A prime factor of 2^n-1 is called primitive if it does not divide
          2^r-1 for any r<n, cf. A086251.
COMMENT:  a(n) is the greatest prime such that the multiplicative order of 2
          mod a(n) equals n, or a(n)=1 if no such prime exists.
          - _Jianing Song_, Oct 23 2019
```

The conjecture comment carries no author/date line in the entry (it belongs
to the original submission of the sequence).  Conjecture (2) is vague and is
not formalized.

## Status

Triage: proved-elsewhere.  Both (1) and (3) are classical: a primitive prime
factor `p` of `2^n - 1` has `ord_p(2) = n`, so `n ∣ p - 1` by Fermat; for
prime `n`, every prime `p ∣ 2^n - 1` has `ord_p(2) ∣ n` and `ord_p(2) ≠ 1`,
hence `ord_p(2) = n`.  Computationally re-checked (Sage, all primitive prime
factors and all prime factors for prime `n`) for `1 ≤ n ≤ 90`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A097406LargestPrimitivePrime

/-! ## Definition layer -/

/-- The primitive prime factors of `2 ^ n - 1`: the primes dividing `2 ^ n - 1`
that divide no `2 ^ r - 1` with `1 ≤ r < n` (OEIS A097406, third comment). -/
def primitivePrimeFactors (n : ℕ) : Finset ℕ :=
  (2 ^ n - 1).primeFactors.filter fun p => ∀ r ∈ Finset.Ico 1 n, ¬ p ∣ 2 ^ r - 1

/-- OEIS A097406: the largest primitive prime factor of `2 ^ n - 1`, or `1` if no
such prime exists. -/
def a (n : ℕ) : ℕ :=
  if h : (primitivePrimeFactors n).Nonempty then (primitivePrimeFactors n).max' h else 1

/-- If the primitive prime factors of `2 ^ n - 1` form the singleton `{q}`,
then `a n = q`. -/
theorem a_eq_of_primitivePrimeFactors_eq_singleton {n q : ℕ}
    (h : primitivePrimeFactors n = {q}) : a n = q := by
  rw [a, dif_pos (by rw [h]; exact Finset.singleton_nonempty q)]
  simp only [h, Finset.max'_singleton]

/-- If `2 ^ n - 1` has no primitive prime factor, then `a n = 1`. -/
theorem a_eq_one_of_primitivePrimeFactors_eq_empty {n : ℕ}
    (h : primitivePrimeFactors n = ∅) : a n = 1 := by
  rw [a, dif_neg (by rw [h]; exact Finset.not_nonempty_empty)]

/-! ### Ground truth against the listed terms `1, 3, _, 5, 31, 1, _, 17, ..., 89, 13` -/

example : a 1 = 1 := by
  apply a_eq_one_of_primitivePrimeFactors_eq_empty
  rw [primitivePrimeFactors, show (2 ^ 1 - 1 : ℕ) = 1 from rfl, Nat.primeFactors_one]
  rfl

example : a 2 = 3 := by
  apply a_eq_of_primitivePrimeFactors_eq_singleton
  rw [primitivePrimeFactors, show (2 ^ 2 - 1 : ℕ) = 3 from rfl]
  unfold Nat.primeFactors
  simp only [Nat.primeFactorsList_ofNat]
  decide

example : a 4 = 5 := by
  apply a_eq_of_primitivePrimeFactors_eq_singleton
  rw [primitivePrimeFactors, show (2 ^ 4 - 1 : ℕ) = 15 from rfl]
  unfold Nat.primeFactors
  simp only [Nat.primeFactorsList_ofNat]
  decide

example : a 5 = 31 := by
  apply a_eq_of_primitivePrimeFactors_eq_singleton
  rw [primitivePrimeFactors, show (2 ^ 5 - 1 : ℕ) = 31 from rfl]
  unfold Nat.primeFactors
  simp only [Nat.primeFactorsList_ofNat]
  decide

example : a 6 = 1 := by
  apply a_eq_one_of_primitivePrimeFactors_eq_empty
  rw [primitivePrimeFactors, show (2 ^ 6 - 1 : ℕ) = 63 from rfl]
  unfold Nat.primeFactors
  simp only [Nat.primeFactorsList_ofNat]
  decide

example : a 8 = 17 := by
  apply a_eq_of_primitivePrimeFactors_eq_singleton
  rw [primitivePrimeFactors, show (2 ^ 8 - 1 : ℕ) = 255 from rfl]
  unfold Nat.primeFactors
  simp only [Nat.primeFactorsList_ofNat]
  decide

example : a 11 = 89 := by
  have h : primitivePrimeFactors 11 = {23, 89} := by
    rw [primitivePrimeFactors, show (2 ^ 11 - 1 : ℕ) = 2047 from rfl]
    unfold Nat.primeFactors
    simp only [Nat.primeFactorsList_ofNat]
    decide
  rw [a, dif_pos (by rw [h]; exact Finset.insert_nonempty 23 {89})]
  simp only [h]
  rfl

example : a 12 = 13 := by
  apply a_eq_of_primitivePrimeFactors_eq_singleton
  rw [primitivePrimeFactors, show (2 ^ 12 - 1 : ℕ) = 4095 from rfl]
  unfold Nat.primeFactors
  simp only [Nat.primeFactorsList_ofNat]
  decide

/-! ## Multiplicative-order bridge -/

/-- `p ∣ 2 ^ m - 1` iff `2 ^ m = 1` in `ZMod p`. -/
theorem dvd_two_pow_sub_one_iff (p m : ℕ) :
    p ∣ 2 ^ m - 1 ↔ (2 : ZMod p) ^ m = 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, sub_eq_zero]
  push_cast
  rfl

/-- Jianing Song's characterization (A097406 comment, Oct 23 2019): for `0 < n`,
`p` is a primitive prime factor of `2 ^ n - 1` iff `p` is prime and the
multiplicative order of `2` modulo `p` is `n`. -/
theorem mem_primitivePrimeFactors_iff {n p : ℕ} (hn : 0 < n) :
    p ∈ primitivePrimeFactors n ↔ p.Prime ∧ orderOf (2 : ZMod p) = n := by
  have hne : 2 ^ n - 1 ≠ 0 := by
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  simp only [primitivePrimeFactors, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hp, hdvd, -⟩, hprim⟩
    refine ⟨hp, ?_⟩
    have hpow : (2 : ZMod p) ^ n = 1 := (dvd_two_pow_sub_one_iff p n).mp hdvd
    have hord_dvd : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one hpow
    have hord_pos : 0 < orderOf (2 : ZMod p) := Nat.pos_of_dvd_of_pos hord_dvd hn
    have hord_le : orderOf (2 : ZMod p) ≤ n := Nat.le_of_dvd hn hord_dvd
    by_contra hne_ord
    have hlt : orderOf (2 : ZMod p) < n := lt_of_le_of_ne hord_le hne_ord
    exact hprim (orderOf (2 : ZMod p)) ⟨hord_pos, hlt⟩
      ((dvd_two_pow_sub_one_iff p _).mpr (pow_orderOf_eq_one 2))
  · rintro ⟨hp, hord⟩
    have hpow : (2 : ZMod p) ^ n = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one 2
    refine ⟨⟨hp, (dvd_two_pow_sub_one_iff p n).mpr hpow, hne⟩, ?_⟩
    rintro r ⟨hr1, hrn⟩ hdvd
    have hnr : n ∣ r :=
      hord ▸ orderOf_dvd_of_pow_eq_one ((dvd_two_pow_sub_one_iff p r).mp hdvd)
    exact absurd (Nat.le_of_dvd hr1 hnr) (not_le.mpr hrn)

/-- If the multiplicative order of `2` modulo the prime `p` is `n > 0`, then
`p ≡ 1 (mod n)` (Fermat's little theorem plus Lagrange). -/
theorem modEq_one_of_orderOf_two_eq {n p : ℕ} [Fact p.Prime] (hn : 0 < n)
    (hord : orderOf (2 : ZMod p) = n) : p ≡ 1 [MOD n] := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_eq_zero_iff'.mpr] at hord
    · exact (Nat.ne_of_gt hn) hord.symm
    · intro k hk h0k
      rw [zero_pow (Nat.ne_of_gt hk)] at h0k
      exact zero_ne_one h0k
  have hdvd : n ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one h2
  exact ((Nat.modEq_iff_dvd' (Fact.out : p.Prime).one_le).mpr hdvd).symm

/-! ## The conjectures -/

/-- Every primitive prime factor `p` of `2 ^ n - 1` (with `0 < n`) satisfies
`p ≡ 1 (mod n)`. -/
theorem modEq_one_of_mem_primitivePrimeFactors {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ primitivePrimeFactors n) : p ≡ 1 [MOD n] := by
  obtain ⟨hprime, hord⟩ := (mem_primitivePrimeFactors_iff hn).mp hp
  haveI : Fact p.Prime := ⟨hprime⟩
  exact modEq_one_of_orderOf_two_eq hn hord

/-- **A097406 conjecture (1)** (original submission; no author/date line).

Verbatim: "(1) For every n the highest unique prime factor is of the form kn+1."
Here "highest unique prime factor" is the largest primitive prime factor `a n`
of `2 ^ n - 1`.  For every `n ≥ 1`, `a n ≡ 1 (mod n)`.  When no primitive prime
factor exists (`n = 1, 6`, by Zsigmondy) the entry sets `a n = 1`, which is
trivially `≡ 1`; non-vacuity is witnessed by `a 5 = 31`, `a 11 = 89` above. -/
theorem a_modEq_one (n : ℕ) (hn : 0 < n) : a n ≡ 1 [MOD n] := by
  unfold a
  split_ifs with h
  · exact modEq_one_of_mem_primitivePrimeFactors hn (Finset.max'_mem _ h)
  · exact Nat.ModEq.refl 1

/-- **A097406 conjecture (3)** (original submission; no author/date line).

Verbatim: "(3) For each prime n every factor is of the form kn+1."
For prime `n`, every prime factor `p` of `2 ^ n - 1` satisfies `p ≡ 1 (mod n)`. -/
theorem modEq_one_of_prime_dvd_two_pow_sub_one {n p : ℕ} (hn : n.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ n - 1) : p ≡ 1 [MOD n] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : (2 : ZMod p) ^ n = 1 := (dvd_two_pow_sub_one_iff p n).mp hdvd
  have hord_dvd : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have hord : orderOf (2 : ZMod p) = n := by
    rcases hn.eq_one_or_self_of_dvd _ hord_dvd with h1 | hself
    · exfalso
      have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
      have h10 : (1 : ZMod p) = 0 := by linear_combination h21
      exact one_ne_zero h10
    · exact hself
  exact modEq_one_of_orderOf_two_eq hn.pos hord

end Candidates.A097406LargestPrimitivePrime
