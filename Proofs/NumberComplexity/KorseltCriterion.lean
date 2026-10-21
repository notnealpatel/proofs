/-
# Korselt's criterion for Carmichael numbers

## Classical source

A. Korselt, "Problème chinois", L'Intermédiaire des Mathématiciens 6 (1899),
142–143.  Restated as Theorem 3.4.6 in R. Crandall and C. Pomerance,
*Prime Numbers: A Computational Perspective* (2nd ed., Springer 2005).

## Informal statement (verbatim from the target spec)

A composite n > 1 satisfies a^n ≡ a (mod n) for every integer a if and only if
n is squarefree and p - 1 divides n - 1 for every prime p | n.

Such composite n are the Carmichael numbers: 561, 1105, 1729, 2465, 2821, ...

## Mathlib status (checked 2026-10-21)

`Mathlib/NumberTheory/FermatPsp.lean` defines base-`b` Fermat pseudoprimes and
remarks that Carmichael numbers are "not yet defined"; there is no all-bases
predicate and no Korselt criterion.  `ArithmeticFunction.carmichael` is the
Carmichael lambda function, a different notion.

Date: 2026-10-21.
-/
import Mathlib

set_option autoImplicit false

namespace NumberComplexity.Korselt

/-- A Carmichael number is a composite `n > 1` such that `a ^ n ≡ a (mod n)` for
every integer `a`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℤ, a ^ n ≡ a [ZMOD n]

/-- Ground truth: `561 = 3 · 11 · 17` satisfies Korselt's condition
(squarefree, and `2, 10, 16` all divide `560`). -/
example : (561 : ℕ) = 3 * 11 * 17 ∧ 2 ∣ 560 ∧ 10 ∣ 560 ∧ 16 ∣ 560 := by decide

/-- Ground truth: `4` is not a Carmichael number, since `2 ^ 4 = 16 ≢ 2 (mod 4)`. -/
example : ¬ IsCarmichael 4 := by
  rintro ⟨-, -, h⟩
  have h2 := h 2
  revert h2
  decide

/-- Fermat step: if `p` is prime and `p - 1 ∣ n - 1` with `0 < n`, then `x ^ n = x`
for every `x : ZMod p`. -/
theorem zmod_pow_eq_self_of_sub_one_dvd {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    (h : p - 1 ∣ n - 1) (x : ZMod p) : x ^ n = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_pow hn.ne'
  · obtain ⟨k, hk⟩ := h
    have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    calc x ^ n = x ^ (n - 1) * x := by rw [← pow_succ, ← hn']
      _ = (x ^ (p - 1)) ^ k * x := by rw [hk, pow_mul]
      _ = x := by rw [ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

/-- Korselt, sufficiency: if `n > 1` is squarefree and `p - 1 ∣ n - 1` for every
prime `p ∣ n`, then `a ^ n ≡ a (mod n)` for every integer `a`. -/
theorem pow_modEq_self_of_korselt {n : ℕ} (hn : 1 < n) (hsq : Squarefree n)
    (hdvd : ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1) (a : ℤ) : a ^ n ≡ a [ZMOD n] := by
  rw [Int.modEq_iff_dvd, Int.natCast_dvd]
  have key : (∏ p ∈ n.primeFactors, p) ∣ (a - a ^ n).natAbs := by
    refine Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) ?_
    intro p hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [zmod_pow_eq_self_of_sub_one_dvd (by omega) (hdvd p hp), sub_self]
  rwa [Nat.prod_primeFactors_of_squarefree hsq] at key

/-- Korselt, necessity of squarefreeness: if `1 < n` and `a ^ n ≡ a (mod n)` for
every integer `a`, then `n` is squarefree. -/
theorem squarefree_of_forall_pow_modEq {n : ℕ} (hn : 1 < n)
    (h : ∀ a : ℤ, a ^ n ≡ a [ZMOD n]) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hdiv : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) - (p : ℤ) ^ n :=
    (Int.natCast_dvd_natCast.mpr hpp).trans (Int.modEq_iff_dvd.mp (h p))
  have hpow : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) ^ n := by
    have hn2 : n = (n - 2) + 2 := by omega
    rw [hn2, pow_add, sq]
    push_cast
    exact Dvd.intro_left _ rfl
  have hp1 : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) := by
    simpa using dvd_add hdiv hpow
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : (p : ℤ) ∣ 1 := by
    push_cast at hp1
    rw [← mul_dvd_mul_iff_left hp0, mul_one]
    exact hp1
  have : p ∣ 1 := by exact_mod_cast h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- Korselt, necessity of the divisibility condition: if `1 < n` and
`a ^ n ≡ a (mod n)` for every integer `a`, then `p - 1 ∣ n - 1` for each prime
`p ∣ n`. -/
theorem sub_one_dvd_of_forall_pow_modEq {n : ℕ} (hn : 1 < n)
    (h : ∀ a : ℤ, a ^ n ≡ a [ZMOD n]) : ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1 := by
  intro p hp
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hpn : (p : ℤ) ∣ n := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors hp)
  have hfix : ∀ x : ZMod p, x ^ n = x := by
    intro x
    have h0 : (((x.val : ℤ) - (x.val : ℤ) ^ n : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hpn.trans (Int.modEq_iff_dvd.mp (h _)))
    push_cast at h0
    rw [ZMod.natCast_zmod_val] at h0
    exact (sub_eq_zero.mp h0).symm
  have hunit : ∀ u : (ZMod p)ˣ, u ^ (n - 1) = 1 := by
    intro u
    have hn' : n = (n - 1) + 1 := by omega
    have hu := hfix u
    rw [hn', pow_succ] at hu
    have hu' : ((u ^ (n - 1) : (ZMod p)ˣ) : ZMod p) * u = 1 * u := by
      push_cast
      rw [one_mul]
      exact hu
    exact Units.ext (mul_right_cancel₀ u.ne_zero hu')
  have hexp := Monoid.exponent_dvd_of_forall_pow_eq_one hunit
  rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at hexp

/-- **Korselt's criterion** (all `n > 1`, prime or not): `a ^ n ≡ a (mod n)` holds
for every integer `a` iff `n` is squarefree and `p - 1 ∣ n - 1` for every prime
`p ∣ n`. -/
theorem forall_pow_modEq_iff_korselt {n : ℕ} (hn : 1 < n) :
    (∀ a : ℤ, a ^ n ≡ a [ZMOD n]) ↔
      Squarefree n ∧ ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1 :=
  ⟨fun h => ⟨squarefree_of_forall_pow_modEq hn h, sub_one_dvd_of_forall_pow_modEq hn h⟩,
    fun ⟨hsq, hdvd⟩ => pow_modEq_self_of_korselt hn hsq hdvd⟩

/-- **Korselt's criterion for Carmichael numbers** (Korselt 1899): a composite
`n > 1` satisfies `a ^ n ≡ a (mod n)` for every integer `a` iff `n` is squarefree
and `p - 1 ∣ n - 1` for every prime `p ∣ n`. -/
theorem isCarmichael_iff_korselt {n : ℕ} :
    IsCarmichael n ↔
      1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1 := by
  constructor
  · rintro ⟨hn, hnp, h⟩
    exact ⟨hn, hnp, (forall_pow_modEq_iff_korselt hn).mp h⟩
  · rintro ⟨hn, hnp, hk⟩
    exact ⟨hn, hnp, (forall_pow_modEq_iff_korselt hn).mpr hk⟩

/-- Non-vacuity: `561 = 3 · 11 · 17` is a Carmichael number, obtained from
Korselt's criterion. -/
example : IsCarmichael 561 := by
  have h561 : (561 : ℕ) = 3 * 11 * 17 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  have hsq : Squarefree (561 : ℕ) := by
    rw [h561, Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, ⟨by norm_num, h3.squarefree, h11.squarefree⟩, h17.squarefree⟩
  have hpf : Nat.primeFactors 561 = {3, 11, 17} := by
    rw [h561, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      h3.primeFactors, h11.primeFactors, h17.primeFactors]
    rfl
  refine isCarmichael_iff_korselt.mpr ⟨by norm_num, by norm_num, hsq, ?_⟩
  rw [hpf]
  decide

end NumberComplexity.Korselt
