/-
# A001122 — Ordowski: primitive root `2` via `2^k + 3` and `2^m + 5`

## OEIS source (retrieved with `oeis show A001122`, 2026-10-21)

```
NAME:     Primes with primitive root 2.
TERMS:    3,5,11,13,19,29,37,53,59,61,67,83,101,107,131,139,149,163,173,179,
          181,197,211,227,269,293,317,347,349,373,379,389,419,421,443,461,...
COMMENT (the conjecture):
  Conjecture: for a prime p > 5, p has primitive root 2 iff p == +-3 (mod 8)
  divides 2^k + 3 for some k < p - 1 and divides 2^m + 5 for some m < p - 1.
  It seems that all primes of the form 2^k + 3 for k <> 2 (A057732) have
  primitive root 2. - _Thomas Ordowski_, Nov 27 2023
```

No later comment in the entry retracts or corrects the conjecture (the only
later comment, Jules Beauchamp, Jun 16 2026, gives an unrelated
characterization).

## Status

**False.** This module refutes the main characterization (the "iff").  The
"if" direction fails; the smallest counterexample is `p = 643`:

* `643 ≡ 3 (mod 8)`;
* `643 ∣ 2^68 + 3` and `643 ∣ 2^168 + 5`, with `68, 168 < 642`;
* but `2^214 ≡ 1 (mod 643)`, so `ord_643(2) = 214 = 642 / 3` and `2` is not a
  primitive root.

The "only if" direction is true and is proved below as
`ordowski_only_if`; it is the corrected form of the claim.

Computational evidence (Python, exhaustive over primes `7 ≤ p < 700`): `643`
is the only prime in that range on which the two sides of the "iff" differ;
the triage's Sage run found 81 counterexamples below `10^5`
(`643, 997, 1597, 5197, …`).

The side remark ("all primes of the form 2^k + 3 for k <> 2 have primitive
root 2") is stated separately as `SideConjecture`; it is an Artin-type claim,
it is not refuted here, and it is left open.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001122Refutation

/-! ## Definition layer -/

/-- Membership in A001122: `p` is a prime with primitive root `2`, i.e. the
multiplicative order of `2` modulo `p` is `p - 1`.  For a prime `p` the
subtraction `p - 1` is the honest value since `2 ≤ p`. -/
def InA001122 (p : ℕ) : Prop :=
  p.Prime ∧ orderOf (2 : ZMod p) = p - 1

/-! ## Ground truth -/

-- `3` is the first term: `2` has order `2` modulo `3`.
example : InA001122 3 := by
  refine ⟨Nat.prime_three, ?_⟩
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

-- `5` is the second term.
example : InA001122 5 := by
  refine ⟨Nat.prime_five, ?_⟩
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

-- `11` is the third term.
example : InA001122 11 := by
  refine ⟨by norm_num, ?_⟩
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

-- `7` is a prime skipped by the sequence: `2^3 = 8 ≡ 1 (mod 7)`.
example : ¬ InA001122 7 := by
  rintro ⟨-, h⟩
  have hdvd : orderOf (2 : ZMod 7) ∣ 3 := orderOf_dvd_of_pow_eq_one (by decide)
  rw [h] at hdvd
  norm_num at hdvd

/-! ## The conjecture -/

/-- **Ordowski's characterization (A001122, Thomas Ordowski, Nov 27 2023).**

Verbatim: "Conjecture: for a prime p > 5, p has primitive root 2 iff
p == +-3 (mod 8) divides 2^k + 3 for some k < p - 1 and divides 2^m + 5 for
some m < p - 1."

Formally: for every prime `p` with `5 < p`, `2` has order `p - 1` modulo `p`
if and only if `p % 8 ∈ {3, 5}`, `p ∣ 2^k + 3` for some `k < p - 1`, and
`p ∣ 2^m + 5` for some `m < p - 1`. -/
def Conjecture : Prop :=
  ∀ p : ℕ, p.Prime → 5 < p →
    (orderOf (2 : ZMod p) = p - 1 ↔
      ((p % 8 = 3 ∨ p % 8 = 5) ∧ (∃ k < p - 1, p ∣ 2 ^ k + 3) ∧
        ∃ m < p - 1, p ∣ 2 ^ m + 5))

/-- **Ordowski's side remark (A001122, same comment), not addressed here.**

Verbatim: "It seems that all primes of the form 2^k + 3 for k <> 2 (A057732)
have primitive root 2."  This is an Artin-type statement and is open; it is
recorded only so that the whole comment is formalized. -/
def SideConjecture : Prop :=
  ∀ k : ℕ, k ≠ 2 → (2 ^ k + 3).Prime → InA001122 (2 ^ k + 3)

-- The side remark is non-vacuous: `k = 1` gives the prime `5 = 2 + 3`.
example : (2 ^ 1 + 3).Prime := by norm_num

/-! ## The counterexample `p = 643` -/

/-- `2^214 ≡ 1 (mod 643)`. -/
theorem two_pow_214_zmod_643 : (2 : ZMod 643) ^ 214 = 1 := by
  have hmod : 2 ^ 214 ≡ 1 [MOD 643] := by decide
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hcast
  exact hcast

/-- `2` is not a primitive root modulo `643`: its order divides `214`. -/
theorem orderOf_two_zmod_643_ne : orderOf (2 : ZMod 643) ≠ 643 - 1 := by
  intro h
  have hdvd : orderOf (2 : ZMod 643) ∣ 214 := orderOf_dvd_of_pow_eq_one two_pow_214_zmod_643
  rw [h] at hdvd
  norm_num at hdvd

/-- `643` satisfies every condition on the right-hand side of Ordowski's
characterization: `643 ≡ 3 (mod 8)`, `643 ∣ 2^68 + 3`, `643 ∣ 2^168 + 5`. -/
theorem rhs_643 :
    (643 % 8 = 3 ∨ 643 % 8 = 5) ∧ (∃ k < 643 - 1, 643 ∣ 2 ^ k + 3) ∧
      ∃ m < 643 - 1, 643 ∣ 2 ^ m + 5 :=
  ⟨Or.inl (by norm_num), ⟨68, by norm_num, by norm_num⟩, ⟨168, by norm_num, by norm_num⟩⟩

/-- **Ordowski's characterization is false.**  Counterexample: `p = 643`, a
prime `≡ 3 (mod 8)` dividing `2^68 + 3` and `2^168 + 5`, at which `2` has
order `214 ≠ 642`.  Only the "if" direction fails; the "only if" direction
holds (`ordowski_only_if`), so the author probably intended the one-way
necessary condition, or overlooked primes at which `2` has small index but
`-3` and `-5` still lie in the subgroup generated by `2`. -/
theorem ordowski_false : ¬ Conjecture := by
  intro hconj
  have hprime : Nat.Prime 643 := by norm_num
  exact orderOf_two_zmod_643_ne ((hconj 643 hprime (by norm_num)).mpr rhs_643)

/-! ## The corrected form: the "only if" direction -/

/-- In `ZMod p`, an element of order `p - 1` hits every nonzero residue with an
exponent `k < p - 1`. -/
theorem exists_pow_eq_of_orderOf_eq {p : ℕ} [Fact p.Prime] {x y : ZMod p}
    (hx : orderOf x = p - 1) (hy : y ≠ 0) : ∃ k < p - 1, x ^ k = y := by
  classical
  set S : Finset (ZMod p) := (Finset.range (p - 1)).image (fun k => x ^ k) with hS
  have hinj : Set.InjOn (fun k => x ^ k) (Finset.range (p - 1) : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ Set.Iio (orderOf x) := by
      rw [hx]
      simpa using ha
    have hb' : b ∈ Set.Iio (orderOf x) := by
      rw [hx]
      simpa using hb
    exact pow_injOn_Iio_orderOf ha' hb' hab
  have hcardS : S.card = p - 1 := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hx0 : x ≠ 0 := by
    intro h0
    have hp := (Fact.out : p.Prime).two_le
    have hord : orderOf (0 : ZMod p) = 0 := orderOf_eq_zero_iff'.mpr fun n hn => by
      rw [zero_pow hn.ne']
      exact zero_ne_one
    rw [h0, hord] at hx
    omega
  have hsub : S ⊆ Finset.univ.erase 0 := by
    intro z hz
    rw [hS, Finset.mem_image] at hz
    obtain ⟨k, -, rfl⟩ := hz
    exact Finset.mem_erase.mpr ⟨pow_ne_zero k hx0, Finset.mem_univ _⟩
  have hcardT : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have heq : S = Finset.univ.erase 0 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardS, hcardT])
  have hyS : y ∈ S := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩
  rw [hS, Finset.mem_image] at hyS
  obtain ⟨k, hk, hky⟩ := hyS
  exact ⟨k, Finset.mem_range.mp hk, hky⟩

/-- For a prime `p > 5` with primitive root `2` and `c ∈ {3, 5}` (any `c` with
`0 < c < p`), some `2^k + c` with `k < p - 1` is divisible by `p`. -/
theorem exists_dvd_two_pow_add {p : ℕ} (hp : p.Prime) (h2 : orderOf (2 : ZMod p) = p - 1)
    (c : ℕ) (hc0 : 0 < c) (hcp : c < p) : ∃ k < p - 1, p ∣ 2 ^ k + c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcne : (c : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hc0 hcp
  obtain ⟨k, hk, hpow⟩ := exists_pow_eq_of_orderOf_eq h2 (neg_ne_zero.mpr hcne)
  refine ⟨k, hk, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hpow, neg_add_cancel]

/-- If `2` is a primitive root modulo an odd prime `p`, then `2` is not a
square modulo `p`, so `p ≡ ±3 (mod 8)`. -/
theorem mod_eight_of_orderOf_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : orderOf (2 : ZMod p) = p - 1) : p % 8 = 3 ∨ p % 8 = 5 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  by_contra hmod
  have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp2).mpr (by omega)
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h20 : (2 : ZMod p) ≠ 0 := by
      have hcast : ((2 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
      simpa using hcast
    exact h20 (by simpa using hr)
  have hhalf : (2 : ZMod p) ^ ((p - 1) / 2) = 1 := by
    have hp1 : p - 1 = 2 * ((p - 1) / 2) := by omega
    rw [hr, ← sq, ← pow_mul, ← hp1]
    exact ZMod.pow_card_sub_one_eq_one hr0
  have hdvd : orderOf (2 : ZMod p) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one hhalf
  rw [h2] at hdvd
  have hpos : 0 < (p - 1) / 2 := by
    have := hp.two_le
    omega
  have hle := Nat.le_of_dvd hpos hdvd
  omega

/-- **The true half of Ordowski's characterization ("only if").**  If `p > 5`
is a prime with primitive root `2`, then `p ≡ ±3 (mod 8)`, `p ∣ 2^k + 3` for
some `k < p - 1`, and `p ∣ 2^m + 5` for some `m < p - 1`. -/
theorem ordowski_only_if (p : ℕ) (hp : p.Prime) (h5 : 5 < p)
    (h2 : orderOf (2 : ZMod p) = p - 1) :
    (p % 8 = 3 ∨ p % 8 = 5) ∧ (∃ k < p - 1, p ∣ 2 ^ k + 3) ∧
      ∃ m < p - 1, p ∣ 2 ^ m + 5 :=
  ⟨mod_eight_of_orderOf_two hp (by omega) h2,
    exists_dvd_two_pow_add hp h2 3 (by norm_num) (by omega),
    exists_dvd_two_pow_add hp h2 5 (by norm_num) (by omega)⟩

-- The corrected form is non-vacuous: `11` is a prime `> 5` with primitive root `2`.
example : (11 : ℕ).Prime ∧ 5 < 11 ∧ orderOf (2 : ZMod 11) = 11 - 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

end Candidates.A001122Refutation
