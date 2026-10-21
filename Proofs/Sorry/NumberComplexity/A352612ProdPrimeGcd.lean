/-
# A352612 — Beisel: `a(n) ≡ -1 (mod n)` for odd `n` forces a prime power

## OEIS source (retrieved with `oeis show A352612`, author line from
## https://oeis.org/A352612/internal, 2026-10-21)

```
NAME:     (n-1)*prod(-p^2 where 2 <= p <= n-2 is prime and relatively prime
          to n)*prod(k where both k and (n-k) are composite and relatively
          prime to n) (mod n).
OFFSET:   1,3
TERMS:    0,1,2,3,4,5,4,7,4,9,10,11,4,9,11,1,16,17,4,1,17,17,22,23,4,1,26,1,
          28,29,4,17,29,25,1,25,36,11,35,39,40,25,4,7,41,27,46,23,4,31,1,23,
          52,1,51,55,1,49,58,1,4,37,59,55,1,49,66,33,65,31,70,25,4
COMMENT:  The convention for the empty product here is 1. The second product
          exists for all numbers greater than 210. See A141098.
COMMENT (the conjecture):
          Conjecture: For odd n, if a(n) == -1 (mod n) then n must be a prime
          power.
PROGRAM:  (PARI) a(n)= {prod_p=1; prod_r=1; for(k=2, n-2, if(gcd(k,n)==1,
          if(isprime(k), prod_p=prod_p*k*(n-k); ); if(!isprime(k) &&
          !isprime(n-k), prod_r=prod_r*k; );); ); (-prod_p*prod_r)%n; }
AUTHOR:   Craig J. Beisel, Mar 23 2022 (the conjecture comment is unsigned and
          belongs to the original submission).
```

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell).  This module proves it.

## Argument

Pairing `k ↔ n - k` on the totatives in `[2, n-2]` (no fixed point since `n`
is odd) and using `p (n - p) ≡ -p²` shows
`a(n) ≡ W(n) · (2 (n-2))^[n-2 prime] (mod n)`, where `W(n)` is the product of
all totatives of `n` (for odd `n` two primes can sum to `n` only if one is `2`).
For odd `n` that is not a prime power, `n = m₁ m₂` with coprime odd
`m₁, m₂ ≥ 3`; through the Chinese remainder theorem the product of all units of
`ZMod n` projects to `(∏ units mod mᵢ)^φ(m_j)`, a square of an element of
order `≤ 2`, so `W(n) = 1`.  Hence `a(n) ∈ {1, -4}` and `a(n) = -1` would force
`n ∣ 2` or `n ∣ 3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A352612ProdPrimeGcd

/-! ## Definitions -/

/-- **A352612.** `a(n) = (n-1) · ∏_{p prime, 2 ≤ p ≤ n-2, gcd(p,n)=1} (-p²) ·
∏_{k ∈ [2, n-2], gcd(k,n)=1, k and n-k composite} k`, read in `ZMod n`.
On `k ∈ [2, n-2]` both `k ≥ 2` and `n - k ≥ 2`, so "not prime" is "composite";
the `ℕ` subtractions `n - 2` and `n - k` are only evaluated where they are
genuine (for `n < 4` the index range is empty, matching the source). -/
def a (n : ℕ) : ZMod n :=
  ((n : ZMod n) - 1) *
    (∏ p ∈ (Finset.Icc 2 (n - 2)).filter (fun p => p.Prime ∧ Nat.Coprime p n),
      -((p : ZMod n) ^ 2)) *
    ∏ k ∈ (Finset.Icc 2 (n - 2)).filter
        (fun k => ¬k.Prime ∧ ¬(n - k).Prime ∧ Nat.Coprime k n),
      (k : ZMod n)

/-! Ground truth against the listed terms (offset 1). -/

example : (a 1).val = 0 := by decide
example : (a 2).val = 1 := by decide
example : (a 5).val = 4 := by decide
example : (a 7).val = 4 := by decide
example : (a 9).val = 4 := by decide
example : (a 15).val = 11 := by decide
example : (a 16).val = 1 := by decide
example : (a 21).val = 17 := by decide
example : (a 25).val = 4 := by decide

/-- Satisfiability of the hypotheses of the conjecture: `n = 5` is odd,
`1 < 5`, and `a 5 = -1` in `ZMod 5`. -/
example : Odd 5 ∧ 1 < 5 ∧ a 5 = -1 := ⟨by decide, by decide, by decide⟩

/-- The product of all totatives `k ∈ [0, n)` of `n`, read in `ZMod n`
(Gauss's generalization of Wilson's product). -/
def totientProd (n : ℕ) : ZMod n :=
  ∏ k ∈ (Finset.range n).filter (fun k => Nat.Coprime k n), (k : ZMod n)

example : totientProd 9 = -1 := by decide
example : totientProd 15 = 1 := by decide

/-- The totatives of `n` in `[2, n-2]`. -/
def midTotatives (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (n - 2)).filter (fun k => Nat.Coprime k n)

example : midTotatives 9 = {2, 4, 5, 7} := by decide

/-- The factor contributed by `k` to the two products of `a n`: `-k²` when
`k` is prime, `k` when `k` and `n - k` are both not prime, and `1` otherwise. -/
def termFactor (n k : ℕ) : ZMod n :=
  if k.Prime then -((k : ZMod n) ^ 2) else if ¬(n - k).Prime then (k : ZMod n) else 1

/-- The excess factor of a pair `{k, n-k}` of primes: `k (n-k)` when `k = 2`
and `n - 2` is prime, and `1` otherwise. -/
def primePairFactor (n k : ℕ) : ZMod n :=
  if k = 2 ∧ (n - 2).Prime then (k : ZMod n) * ((n - k : ℕ) : ZMod n) else 1

/-! ## Generalized Wilson product -/

/-- In a finite commutative group the product of all elements squares to `1`. -/
theorem prod_univ_sq_eq_one {G : Type*} [CommGroup G] [Fintype G] :
    (∏ g : G, g) ^ 2 = 1 := by
  have hinv : (∏ g : G, g) = (∏ g : G, g)⁻¹ := by
    calc (∏ g : G, g) = ∏ g : G, ((Equiv.inv G) g)⁻¹ := by simp
      _ = ∏ g : G, g⁻¹ := Equiv.prod_comp (Equiv.inv G) (fun g => g⁻¹)
      _ = (∏ g : G, g)⁻¹ := Finset.prod_inv_distrib _
  rw [sq]
  nth_rewrite 1 [hinv]
  exact inv_mul_cancel _

/-- The product of all elements of `A × B` is
`((∏ A)^|B|, (∏ B)^|A|)`. -/
theorem prod_univ_prod_type {A B : Type*} [CommGroup A] [CommGroup B] [Fintype A]
    [Fintype B] :
    (∏ x : A × B, x) = ((∏ a : A, a) ^ Fintype.card B, (∏ b : B, b) ^ Fintype.card A) := by
  ext
  · rw [Prod.fst_prod, Fintype.prod_prod_type]
    simp [Finset.prod_pow]
  · rw [Prod.snd_prod, Fintype.prod_prod_type, Finset.prod_comm]
    simp [Finset.prod_pow]

/-- For coprime `m₁, m₂ > 2` the product of all units of `ZMod (m₁ m₂)` is `1`. -/
theorem prod_units_zmod_eq_one {m₁ m₂ : ℕ} (hco : Nat.Coprime m₁ m₂) (h1 : 2 < m₁)
    (h2 : 2 < m₂) :
    haveI : NeZero (m₁ * m₂) := ⟨by positivity⟩
    (∏ u : (ZMod (m₁ * m₂))ˣ, u) = 1 := by
  haveI : NeZero (m₁ * m₂) := ⟨by positivity⟩
  haveI : NeZero m₁ := ⟨by omega⟩
  haveI : NeZero m₂ := ⟨by omega⟩
  let e : (ZMod (m₁ * m₂))ˣ ≃* (ZMod m₁)ˣ × (ZMod m₂)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hco).toMulEquiv).trans MulEquiv.prodUnits
  apply e.injective
  rw [map_prod, map_one,
    show (∏ u, e u) = ∏ y, y from Equiv.prod_comp e.toEquiv (fun y => y),
    prod_univ_prod_type, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient]
  obtain ⟨k₁, hk₁⟩ := Nat.totient_even h1
  obtain ⟨k₂, hk₂⟩ := Nat.totient_even h2
  rw [hk₁, hk₂, ← two_mul, ← two_mul, pow_mul, pow_mul, prod_univ_sq_eq_one,
    prod_univ_sq_eq_one, one_pow, one_pow, Prod.mk_one_one]

/-- `totientProd n` is the value in `ZMod n` of the product of all units. -/
theorem totientProd_eq_prod_units (n : ℕ) [NeZero n] :
    totientProd n = ((∏ u : (ZMod n)ˣ, u : (ZMod n)ˣ) : ZMod n) := by
  rw [totientProd, Units.coe_prod]
  refine Finset.prod_bij' (fun k hk => ZMod.unitOfCoprime k (Finset.mem_filter.1 hk).2)
    (fun u _ => (u : ZMod n).val) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro u _
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩
  · intro k hk
    exact ZMod.val_cast_of_lt (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
  · intro u _
    exact Units.ext (by simp)
  · intro k hk
    simp

/-- A number `n > 1` that is not a prime power splits as a product of two
coprime factors, both `> 1`. -/
theorem exists_coprime_split {n : ℕ} (hn : 1 < n) (hpp : ¬IsPrimePow n) :
    ∃ m₁ m₂ : ℕ, Nat.Coprime m₁ m₂ ∧ 1 < m₁ ∧ 1 < m₂ ∧ m₁ * m₂ = n := by
  set p := n.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hn0 : n ≠ 0 := by omega
  have hfac : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
  refine ⟨p ^ n.factorization p, n / p ^ n.factorization p,
    (Nat.coprime_ordCompl hp hn0).pow_left _, Nat.one_lt_pow hfac.ne' hp.one_lt, ?_,
    Nat.ordProj_mul_ordCompl_eq_self n p⟩
  by_contra hle
  have hpos : 0 < n / p ^ n.factorization p := Nat.ordCompl_pos p hn0
  have h1 : n / p ^ n.factorization p = 1 := by omega
  have hn' : p ^ n.factorization p = n := by
    have hself := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [h1, mul_one] at hself
    exact hself
  exact hpp (hn' ▸ hp.isPrimePow.pow hfac.ne')

/-- **Gauss–Wilson for odd non-prime-powers.** If `n > 1` is odd and not a
prime power, the product of the totatives of `n` is `1` modulo `n`. -/
theorem totientProd_eq_one {n : ℕ} (hodd : Odd n) (hn : 1 < n) (hpp : ¬IsPrimePow n) :
    totientProd n = 1 := by
  obtain ⟨m₁, m₂, hco, h1, h2, rfl⟩ := exists_coprime_split hn hpp
  haveI : NeZero (m₁ * m₂) := ⟨by positivity⟩
  have hodd₁ : Odd m₁ := (Nat.odd_mul.1 hodd).1
  have hodd₂ : Odd m₂ := (Nat.odd_mul.1 hodd).2
  have h1' : 2 < m₁ := by obtain ⟨t, rfl⟩ := hodd₁; omega
  have h2' : 2 < m₂ := by obtain ⟨t, rfl⟩ := hodd₂; omega
  rw [totientProd_eq_prod_units, prod_units_zmod_eq_one hco h1' h2', Units.val_one]

/-! ## Pairing `k ↔ n - k` -/

/-- For odd `n`, a product over the totatives in `[2, n-2]` is the product over
the lower half `2k < n` of the paired factors `F k · F (n - k)`. -/
theorem prod_midTotatives_pair {M : Type*} [CommMonoid M] {n : ℕ} (hn : Odd n)
    (F : ℕ → M) :
    ∏ k ∈ midTotatives n, F k =
      ∏ k ∈ (midTotatives n).filter (fun k => 2 * k < n), (F k * F (n - k)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (midTotatives n) (fun k => 2 * k < n),
    Finset.prod_mul_distrib]
  congr 1
  obtain ⟨m, rfl⟩ := hn
  apply Finset.prod_nbij' (fun k => 2 * m + 1 - k) (fun k => 2 * m + 1 - k)
  · intro k hk
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨⟨by omega, by omega⟩, (Nat.coprime_self_sub_left (by omega)).2 hk.1.2⟩, by omega⟩
  · intro k hk
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨⟨by omega, by omega⟩, (Nat.coprime_self_sub_left (by omega)).2 hk.1.2⟩, by omega⟩
  · intro k hk
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc] at hk
    omega
  · intro k hk
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc] at hk
    omega
  · intro k hk
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc] at hk
    congr 1
    omega

/-- `a n` as `(n - 1)` times a single product of `termFactor` over the
totatives in `[2, n-2]`. -/
theorem a_eq_prod_termFactor (n : ℕ) :
    a n = ((n : ZMod n) - 1) * ∏ k ∈ midTotatives n, termFactor n k := by
  rw [a, mul_assoc, midTotatives, Finset.prod_filter, Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold termFactor
  split_ifs <;> simp_all

/-- For odd `n` and a lower-half totative `k`, the pair `{k, n-k}` contributes
`k (n-k)` times the excess `primePairFactor n k`; a pair of primes summing to
odd `n` must contain `2`. -/
theorem termFactor_mul_termFactor {n k : ℕ} (hodd : Odd n)
    (hk : k ∈ (midTotatives n).filter (fun k => 2 * k < n)) :
    termFactor n k * termFactor n (n - k) =
      (k : ZMod n) * ((n - k : ℕ) : ZMod n) * primePairFactor n k := by
  simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc] at hk
  have hnk : n - (n - k) = k := by omega
  have hx : ((n - k : ℕ) : ZMod n) = -(k : ZMod n) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
  unfold termFactor primePairFactor
  rw [hnk]
  by_cases hp : k.Prime <;> by_cases hq : (n - k).Prime
  · -- both prime: parity forces `k = 2`
    have hk2 : k = 2 := by
      rcases hp.eq_two_or_odd' with h | h
      · exact h
      · rcases hq.eq_two_or_odd' with h' | h'
        · omega
        · exfalso
          have heven : Even n := by
            have hsum := h.add_odd h'
            rwa [Nat.add_sub_cancel' (by omega)] at hsum
          exact (Nat.not_even_iff_odd.2 hodd) heven
    subst hk2
    simp only [hp, hq, if_true, and_self]
    rw [hx]
    ring
  · have hc : ¬(k = 2 ∧ (n - 2).Prime) := fun h => hq (h.1 ▸ h.2)
    simp only [hp, hq, hc, if_true, if_false, not_true_eq_false, not_false_eq_true]
    rw [hx]
    ring
  · have hc : ¬(k = 2 ∧ (n - 2).Prime) := fun h => hp (h.1 ▸ Nat.prime_two)
    simp only [hp, hq, hc, if_true, if_false, not_true_eq_false, not_false_eq_true]
    rw [hx]
    ring
  · have hc : ¬(k = 2 ∧ (n - 2).Prime) := fun h => hp (h.1 ▸ Nat.prime_two)
    simp only [hp, hq, hc, if_true, if_false, not_false_eq_true]
    rw [hx]
    ring

/-- For odd `n ≥ 5` the excess factors multiply to `2 (n-2)` if `n - 2` is
prime and to `1` otherwise. -/
theorem prod_primePairFactor {n : ℕ} (hodd : Odd n) (hn : 5 ≤ n) :
    ∏ k ∈ (midTotatives n).filter (fun k => 2 * k < n), primePairFactor n k =
      if (n - 2).Prime then 2 * ((n - 2 : ℕ) : ZMod n) else 1 := by
  have hc : ∀ k, primePairFactor n k =
      if 2 = k then (if (n - 2).Prime then 2 * ((n - 2 : ℕ) : ZMod n) else 1) else 1 := by
    intro k
    unfold primePairFactor
    by_cases hk : k = 2
    · subst hk
      simp
    · simp [hk, Ne.symm hk]
  have h2 : 2 ∈ (midTotatives n).filter (fun k => 2 * k < n) := by
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨le_rfl, by omega⟩, Nat.coprime_two_left.2 hodd⟩, by omega⟩
  simp_rw [hc]
  rw [Finset.prod_ite_eq, if_pos h2]

/-- For `n ≥ 3` the totatives of `n` are `1`, `n - 1` and those in `[2, n-2]`. -/
theorem totientProd_eq_mul_prod_midTotatives {n : ℕ} (hn : 3 ≤ n) :
    totientProd n = ((n : ZMod n) - 1) * ∏ k ∈ midTotatives n, (k : ZMod n) := by
  have hset : (Finset.range n).filter (fun k => Nat.Coprime k n) =
      insert 1 (insert (n - 1) (midTotatives n)) := by
    ext k
    simp only [midTotatives, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_Icc]
    constructor
    · rintro ⟨hk, hco⟩
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [Nat.coprime_zero_left] at hco
        omega
      · omega
    · rintro (rfl | rfl | ⟨⟨h1, h2⟩, hco⟩)
      · exact ⟨by omega, Nat.coprime_one_left n⟩
      · exact ⟨by omega, (Nat.coprime_self_sub_left (by omega)).2 (Nat.coprime_one_left n)⟩
      · exact ⟨by omega, hco⟩
  have h1 : 1 ∉ insert (n - 1) (midTotatives n) := by
    simp only [midTotatives, Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
    omega
  have h2 : n - 1 ∉ midTotatives n := by
    simp only [midTotatives, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [totientProd, hset, Finset.prod_insert h1, Finset.prod_insert h2, Nat.cast_one, one_mul,
    Nat.cast_sub (by omega), Nat.cast_one]

/-- **Closed form.** For odd `n ≥ 5`,
`a(n) ≡ W(n) · (2 (n-2))^[n-2 prime] (mod n)`, with `W(n)` the product of the
totatives of `n`. -/
theorem a_eq_totientProd_mul {n : ℕ} (hodd : Odd n) (hn : 5 ≤ n) :
    a n = totientProd n * (if (n - 2).Prime then 2 * ((n - 2 : ℕ) : ZMod n) else 1) := by
  have hpair : ∏ k ∈ midTotatives n, termFactor n k =
      (∏ k ∈ midTotatives n, (k : ZMod n)) *
        ∏ k ∈ (midTotatives n).filter (fun k => 2 * k < n), primePairFactor n k := by
    rw [prod_midTotatives_pair hodd, prod_midTotatives_pair hodd (fun k => (k : ZMod n)),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k hk => termFactor_mul_termFactor hodd hk
  rw [a_eq_prod_termFactor, hpair, prod_primePairFactor hodd hn,
    totientProd_eq_mul_prod_midTotatives (by omega), mul_assoc]

/-! ## The conjecture -/

/-- **Beisel's conjecture (A352612, Craig J. Beisel, Mar 23 2022).**

Verbatim: "Conjecture: For odd n, if a(n) == -1 (mod n) then n must be a prime
power."  Stated for odd `n > 1` (for `n = 1` the ring `ZMod 1` is trivial and
`1` is not a prime power; the triage statement excludes it).  Proved here: for
odd `n` that is not a prime power, `a(n) ∈ {1, -4}` modulo `n`. -/
theorem isPrimePow_of_a_eq_neg_one {n : ℕ} (hodd : Odd n) (hn : 1 < n) (ha : a n = -1) :
    IsPrimePow n := by
  by_contra hpp
  obtain ⟨m₁, m₂, -, h1, h2, hmn⟩ := exists_coprime_split hn hpp
  have hodd₁ : Odd m₁ := (Nat.odd_mul.1 (hmn ▸ hodd)).1
  have hodd₂ : Odd m₂ := (Nat.odd_mul.1 (hmn ▸ hodd)).2
  have h1' : 3 ≤ m₁ := by obtain ⟨t, rfl⟩ := hodd₁; omega
  have h2' : 3 ≤ m₂ := by obtain ⟨t, rfl⟩ := hodd₂; omega
  have hn9 : 9 ≤ n := hmn ▸ Nat.mul_le_mul h1' h2'
  rw [a_eq_totientProd_mul hodd (by omega), totientProd_eq_one hodd hn hpp, one_mul] at ha
  split_ifs at ha with hprime
  · -- `2 (n - 2) ≡ -4 ≡ -1` would give `n ∣ 3`
    have hx : ((n - 2 : ℕ) : ZMod n) = -2 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, Nat.cast_ofNat]
    rw [hx] at ha
    have h3 : ((3 : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination -ha
    rw [ZMod.natCast_eq_zero_iff] at h3
    have hle := Nat.le_of_dvd (by norm_num) h3
    omega
  · -- `1 ≡ -1` would give `n ∣ 2`
    have h2z : ((2 : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination ha
    rw [ZMod.natCast_eq_zero_iff] at h2z
    have hle := Nat.le_of_dvd (by norm_num) h2z
    omega

end Candidates.A352612ProdPrimeGcd
