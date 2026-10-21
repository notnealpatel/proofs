/-
# A254748 — twin-prime averages have no superdivisor

## OEIS source (retrieved with `oeis show A254748`, 2026-10-21)

```
NAME:     Numbers without superdivisors: numbers n such that n/k + n fails to
          divide at least one of (n/k)^(n/k) + n, (n/k)^n + n/k or
          n^(n/k) + n/k for any divisor k of n.
TERMS:    2,4,6,8,12,14,16,18,20,24,26,28,30,32,38,40,42,44,48,50,52,54,56,
          60,62,64,66,68,72,74,80,84,86,88,90,92,96,98,100,102,...
COMMENT (the conjecture, unsigned; attributed to the entry author
         Juri-Stepan Gerasimov, Feb 07 2015, per the live AUTHOR line):
  Conjecture: Average of twin prime pairs (A014574) are zerosuperdivisor
  numbers.
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Computation (Python, bounded): no twin-prime average below
`3 * 10^6` and no even `n ≤ 2.5 * 10^6` with `n - 1` prime has a superdivisor.

This module proves the conjecture, in the stronger form found by the triage:
every even `n` with `n - 1` prime has no superdivisor.  Only the second
divisibility condition `(n/k + n) ∣ (n/k)^n + n/k` is used (plus the first one
at the single exceptional case `n = 4`).

Informal argument.  Write `n = k * d` (`d = n / k`), `p = n - 1` prime.  Then
`n/k + n = d * (k + 1)` and the second condition becomes
`k + 1 ∣ d ^ p + 1`.  Take a prime `r ∣ k + 1`.  If `r = 2` then `k` is odd,
so `d` is even and `d ^ p + 1` is odd: impossible.  So `r` is odd, which forces
`k ≥ 2`, `d ≥ 2`, and (except for `k = d = 2`) `r ≤ k + 1 < p`.  In `ZMod r`,
`d ^ (2p) = 1` and `d ^ (r - 1) = 1`, and `gcd (2p) (r - 1) ∣ 2` because
`p` is coprime to `r - 1`.  Hence `d ^ 2 = 1`, so `d = d ^ p = -1` (`p` odd).
Also `k = -1`, so `n = k d = 1` and `r ∣ n - 1 = p` with `1 < r < p`:
contradiction.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A254748CommentBothPrime

/-- `k` is a *superdivisor* of `n` (A254748): `k ∣ n` and `n/k + n` divides each
of `(n/k)^(n/k) + n`, `(n/k)^n + n/k` and `n^(n/k) + n/k`. -/
def IsSuperdivisor (n k : ℕ) : Prop :=
  k ∣ n ∧ (n / k + n) ∣ (n / k) ^ (n / k) + n ∧ (n / k + n) ∣ (n / k) ^ n + n / k ∧
    (n / k + n) ∣ n ^ (n / k) + n / k

instance (n k : ℕ) : Decidable (IsSuperdivisor n k) := by
  unfold IsSuperdivisor; infer_instance

/-- Membership in A254748: `n` is a positive integer without superdivisors. -/
def InA254748 (n : ℕ) : Prop := 0 < n ∧ ∀ k : ℕ, ¬ IsSuperdivisor n k

/-- For positive `n`, membership in A254748 only needs to be checked over the
(finite) set of divisors of `n`. -/
theorem inA254748_iff_divisors {n : ℕ} (hn : 0 < n) :
    InA254748 n ↔ ∀ k ∈ n.divisors, ¬ IsSuperdivisor n k := by
  constructor
  · rintro ⟨-, h⟩ k -
    exact h k
  · intro h
    refine ⟨hn, fun k hk => h k ?_ hk⟩
    exact Nat.mem_divisors.2 ⟨hk.1, hn.ne'⟩

instance : DecidablePred InA254748 := fun n =>
  if hn : 0 < n then decidable_of_iff _ (inA254748_iff_divisors hn).symm
  else isFalse (fun h => hn h.1)

/-! ## Ground truth -/

example : InA254748 2 := by decide
example : InA254748 4 := by decide
example : InA254748 12 := by decide
example : ¬ InA254748 10 := by decide
example : ¬ InA254748 1 := by decide

/-- The first terms of A254748 up to `56`, as listed in the entry. -/
example : (Finset.range 57).filter InA254748 =
    {2, 4, 6, 8, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32, 38, 40, 42, 44, 48, 50, 52, 54, 56} := by
  decide

/-! ## Proof -/

/-- The second superdivisor condition, written with `n = k * d`, reduces to
`k + 1 ∣ d ^ (k * d - 1) + 1`. -/
theorem succ_dvd_of_second_condition {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (h : (d + k * d) ∣ d ^ (k * d) + d) : (k + 1) ∣ d ^ (k * d - 1) + 1 := by
  have hn : 0 < k * d := Nat.mul_pos hk hd
  have h1 : d + k * d = d * (k + 1) := by ring
  have h2 : d ^ (k * d) + d = d * (d ^ (k * d - 1) + 1) := by
    conv_lhs => rw [show k * d = (k * d - 1) + 1 by omega]
    ring
  rw [h1, h2] at h
  exact Nat.dvd_of_mul_dvd_mul_left hd h

/-- Core lemma: if `k * d` is even, `k * d - 1` is prime and
`k + 1 ∣ d ^ (k * d - 1) + 1`, then `k = 2` and `d = 2`. -/
theorem eq_two_of_succ_dvd {k d : ℕ} (he : Even (k * d)) (hp : (k * d - 1).Prime)
    (h : (k + 1) ∣ d ^ (k * d - 1) + 1) : k = 2 ∧ d = 2 := by
  set p := k * d - 1 with hp_def
  have hp2 : 2 ≤ p := hp.two_le
  have hpos : 3 ≤ k * d := by omega
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  obtain ⟨r, hr, hrk⟩ := Nat.exists_prime_and_dvd (show k + 1 ≠ 1 by omega)
  have hrd : r ∣ d ^ p + 1 := hrk.trans h
  -- `r` is odd
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hkodd : ¬ Even k := by
      rw [Nat.not_even_iff_odd]
      exact Nat.odd_iff.2 (by omega)
    have hdeven : Even d := by
      rcases (Nat.even_mul.1 he) with h' | h'
      · exact absurd h' hkodd
      · exact h'
    have : Even (d ^ p) := (Nat.even_pow' (by omega)).2 hdeven
    have h3 : Odd (d ^ p + 1) := this.add_one
    exact (Nat.not_even_iff_odd.2 h3) (even_iff_two_dvd.2 hrd)
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  -- `p` is odd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h' | h'
    · exfalso
      obtain ⟨t, ht⟩ := he
      omega
    · exact h'
  haveI : Fact r.Prime := ⟨hr⟩
  have hdZ : ((d : ZMod r)) ^ p = -1 := by
    have : ((d ^ p + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrd
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hkZ : ((k : ZMod r)) = -1 := by
    have : ((k + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrk
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hd0 : (d : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hdZ
    have : (1 : ZMod r) = 0 := by
      have := congrArg (fun x => -x) hdZ
      simpa using this.symm
    exact one_ne_zero this
  -- exclude the exceptional case, then `r < p`
  by_contra hne
  have hd1 : d ≠ 1 := by
    rintro rfl
    have : r ∣ 2 := by simpa using hrd
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
    exact hr2 this
  have hrp : r < p := by
    have hrle : r ≤ k + 1 := Nat.le_of_dvd (by omega) hrk
    have hk2 : 2 ≤ k := by omega
    have hd2 : 2 ≤ d := by omega
    have : k + 3 ≤ k * d := by
      rcases Nat.lt_or_ge 2 d with h3 | h3
      · nlinarith
      · have hd2' : d = 2 := by omega
        subst hd2'
        have : k ≠ 2 := fun hk' => hne ⟨hk', rfl⟩
        omega
    omega
  -- `d ^ 2 = 1` in `ZMod r`
  have hcop : Nat.Coprime p (r - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2p : ((d : ZMod r)) ^ (2 * p) = 1 := by
    rw [pow_mul', hdZ]; norm_num
  have hferm : ((d : ZMod r)) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hd0
  have hg : ((d : ZMod r)) ^ (Nat.gcd (2 * p) (r - 1)) = 1 :=
    pow_gcd_eq_one.2 ⟨h2p, hferm⟩
  rw [Nat.Coprime.gcd_mul_right_cancel 2 hcop] at hg
  have hsq : ((d : ZMod r)) ^ 2 = 1 := by
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left 2 (r - 1)
    rw [ht, pow_mul, hg, one_pow]
  have hdm1 : (d : ZMod r) = -1 := by
    rw [pow_eq_pow_mod p hsq, hpodd, pow_one] at hdZ
    exact hdZ
  -- so `r ∣ k * d - 1 = p`
  have hrp' : r ∣ p := by
    rw [← ZMod.natCast_eq_zero_iff, hp_def, Nat.cast_sub (by omega)]
    push_cast
    rw [hkZ, hdm1]
    ring
  rcases hp.eq_one_or_self_of_dvd r hrp' with h' | h'
  · omega
  · omega

/-- **Stronger form (triage).** If `n` is even and `n - 1` is prime, then `n`
has no superdivisor. -/
theorem not_isSuperdivisor_of_even_of_prime_sub_one {n : ℕ} (he : Even n)
    (hp : (n - 1).Prime) (k : ℕ) : ¬ IsSuperdivisor n k := by
  rintro ⟨⟨d, rfl⟩, h1, h2, -⟩
  have hpos : 3 ≤ k * d := by have := hp.two_le; omega
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hdiv : k * d / k = d := Nat.mul_div_cancel_left d hk
  rw [hdiv] at h1 h2
  obtain ⟨rfl, rfl⟩ := eq_two_of_succ_dvd he hp (succ_dvd_of_second_condition hk hd h2)
  revert h1
  decide

/-- Every even `n ≥ 2` with `n - 1` prime lies in A254748. -/
theorem inA254748_of_even_of_prime_sub_one {n : ℕ} (he : Even n) (hp : (n - 1).Prime) :
    InA254748 n :=
  ⟨by have := hp.two_le; omega, not_isSuperdivisor_of_even_of_prime_sub_one he hp⟩

/-- **A254748 comment conjecture (Juri-Stepan Gerasimov, Feb 07 2015).** "Average of twin
prime pairs (A014574) are zerosuperdivisor numbers": if `n - 1` and `n + 1` are
both prime, then `n` has no superdivisor, i.e. `n ∈ A254748`. -/
theorem twin_prime_average_inA254748 {n : ℕ} (hm : (n - 1).Prime) (hpl : (n + 1).Prime) :
    InA254748 n := by
  have he : Even n := by
    rcases hm.eq_two_or_odd with h | h
    · exfalso
      have hn : n + 1 = 4 := by omega
      rw [hn] at hpl
      exact absurd hpl (by decide)
    · have := hm.two_le
      rw [Nat.even_iff]
      omega
  exact inA254748_of_even_of_prime_sub_one he hm

/-- Non-vacuity: `4 = (3 + 5) / 2` satisfies the hypotheses of
`twin_prime_average_inA254748`. -/
example : (4 - 1).Prime ∧ (4 + 1).Prime := by norm_num

end Candidates.A254748CommentBothPrime
