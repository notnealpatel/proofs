/-
# A004982 — Bala: `a(p n) ≡ a(n) (mod p^2)` for primes `p ≡ 1 (mod 4)`

## OEIS source (retrieved with `oeis show A004982`, 2026-10-21)

```
NAME:     a(n) = (2^n/n!) * Product_{k=0..n-1} (4*k + 3).
TERMS:    1,6,42,308,2310,17556,134596,1038312,8046918,62587140,488179692,...
KEYWORDS: nonn,easy
FORMULA:  G.f.: (1 - 8*x)^(-3/4).
FORMULA:  D-finite with recurrence: n*a(n) + 2*(-4*n+1)*a(n-1) = 0.
          - _R. J. Mathar_, Jan 16 2020
COMMENT (the conjecture):
  Conjecture: a(p*n) = a(n) (mod p^2) for prime p == 1 (mod 4) and all
  positive integers n. Cf. A004981. - _Peter Bala_, Dec 22 2019
```

## Status

Triage: open (the entry records no proof; none was found in the literature by
the triage).  Computation (`timeout 300 python3`, 2026-10-21): no failure for
primes `p ≡ 1 (mod 4)` below `700` with `p n ≤ 9000`; the core congruence
`2^(p-1) ∏' (4j+3) ≡ (p-1)! (mod p^2)` holds for every such `p < 3000`.

This module proves the conjecture (`bala_conjecture`), sorry-free.

## Proof

Write `∏'` for a product with the multiples of `p` dropped (`skip`).  For
`p ≡ 1 (mod 4)` the multiples of `p` among `4k+3`, `k < p n`, are exactly
`p (4t+3)`, `t < n`, and the multiples of `p` in `[1, p n]` are `p t`,
`t ≤ n`.  Hence `a(p n) X = a(n) (2^(p-1))^n Y` exactly, where `X`, `Y` are the
products over the `n` length-`p` blocks of `∏' (j+1)` and `∏' (4j+3)`.

* **Block shift.** Each block is congruent modulo `p^2` to the block at `0`:
  shifting a full residue system of non-multiples by a multiple of `p`
  changes the product by `1 + p t ∑ x⁻¹`, and `∑ x⁻¹ ≡ 0 (mod p)`.
* **Core.** With `Q_r = ∏_{j<p}' (4j+r)` and `X₀ = ∏_{j<p}' (j+1)`: splitting
  `[1, 4p]` by parity gives `X₀^4 ≡ 4^(p-1) X₀^2 Q₁ Q₃`; the reflection
  `m ↦ 4p - m` gives `Q₁ ≡ Q₃`; so `(2^(p-1) Q₃)^2 ≡ X₀^2 (mod p^2)`, and
  `2^(p-1) Q₃ ≡ X₀ (mod p)` fixes the sign.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A004982ProdPrimePeter

/-- **A004982.** `a n = 2 ^ n * ∏_{k=0}^{n-1} (4k+3) / n!`, verbatim from the
entry's NAME; the division is exact (`factorial_dvd`). -/
def a (n : ℕ) : ℕ := 2 ^ n * (∏ k ∈ Finset.range n, (4 * k + 3)) / n.factorial

-- Ground truth: the first ten terms of the OEIS DATA line.
example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9] =
    [1, 6, 42, 308, 2310, 17556, 134596, 1038312, 8046918, 62587140] := by decide

/-- If `2 ^ v ∣ n!` with `n ≠ 0`, then `v ≤ n` (Legendre: `v₂(n!) < n`). -/
theorem two_pow_le_of_dvd_factorial {n v : ℕ} (hn : n ≠ 0) (h : 2 ^ v ∣ n.factorial) :
    v ≤ n := by
  have h1 := Nat.emultiplicity_two_factorial_lt hn
  have h2 : (v : ℕ∞) ≤ emultiplicity 2 n.factorial := le_emultiplicity_of_pow_dvd h
  have : (v : ℕ∞) < n := lt_of_le_of_lt h2 h1
  exact_mod_cast this.le

/-- The defining division of A004982 is exact: `n! ∣ 2 ^ n * ∏_{k<n} (4k+3)`. -/
theorem factorial_dvd (n : ℕ) :
    n.factorial ∣ 2 ^ n * ∏ k ∈ Finset.range n, (4 * k + 3) := by
  obtain ⟨v, m, hm, hfac⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.factorial_ne_zero n)
  rw [hfac]
  apply Nat.mul_dvd_mul
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.factorial_zero] at hfac
      have : 2 ^ v = 1 := Nat.eq_one_of_mul_eq_one_right hfac.symm
      simp [this]
    · exact Nat.pow_dvd_pow 2 (two_pow_le_of_dvd_factorial hn.ne' (Dvd.intro m hfac.symm))
  · have hcop : Nat.Coprime 4 m := by
      have : Nat.Coprime 2 m := (Nat.coprime_two_left).2 hm
      exact Nat.Coprime.pow_left 2 this
    set u : (ZMod m)ˣ := ZMod.unitOfCoprime 4 hcop with hu
    set c : ℕ := ((u⁻¹ : (ZMod m)ˣ) : ZMod m).val with hc
    have h4c : ((4 * c : ℕ) : ZMod m) = 1 := by
      have hm0 : NeZero m := ⟨by rintro rfl; simp at hm⟩
      rw [Nat.cast_mul, hc, ZMod.natCast_zmod_val]
      have : ((4 : ℕ) : ZMod m) = u := rfl
      rw [this, Units.mul_inv]
    have hdvd : m ∣ (3 * c).ascFactorial n :=
      (Dvd.intro_left _ hfac.symm).trans (Nat.factorial_dvd_ascFactorial _ _)
    rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
    rw [Nat.ascFactorial_eq_prod_range] at hdvd
    have hkey : ((∏ k ∈ Finset.range n, (4 * k + 3) : ℕ) : ZMod m) * (c : ZMod m) ^ n =
        ((∏ i ∈ Finset.range n, (3 * c + i) : ℕ) : ZMod m) := by
      push_cast
      rw [show (c : ZMod m) ^ n = ∏ _x ∈ Finset.range n, (c : ZMod m) by simp,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have h4c' : (4 : ZMod m) * c = 1 := by exact_mod_cast h4c
      linear_combination (k : ZMod m) * h4c'
    rw [hdvd] at hkey
    have hcu : IsUnit (c : ZMod m) := by
      have hm0 : NeZero m := ⟨by rintro rfl; simp at hm⟩
      rw [hc, ZMod.natCast_zmod_val]; exact Units.isUnit _
    exact (hcu.pow n).mul_left_eq_zero.mp hkey

open Finset

/-- If `ε ^ 2 = 0` then `∏ (1 + ε z_i) = 1 + ε ∑ z_i`. -/
theorem prod_one_add_mul_of_sq_eq_zero {R : Type*} [CommRing R] (ε : R) (hε : ε ^ 2 = 0)
    (S : Finset ℕ) (z : ℕ → R) : ∏ i ∈ S, (1 + ε * z i) = 1 + ε * ∑ i ∈ S, z i := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [prod_insert hj, sum_insert hj, ih]
    linear_combination (z j * ∑ i ∈ S, z i) * hε

/-- If `p ∣ N` then `p * N` vanishes in `ZMod (p ^ 2)`. -/
theorem natCast_prime_mul_eq_zero {p : ℕ} {N : ℕ} (h : p ∣ N) :
    ((p * N : ℕ) : ZMod (p ^ 2)) = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨q, by ring⟩

/-- **Shift lemma.** If the reciprocals of the `x i` modulo `p` sum to zero, then
shifting every non-multiple `x i` of `p` by `p * t` leaves the product of the
non-multiples unchanged modulo `p ^ 2`. -/
theorem prod_shift_eq {p : ℕ} [Fact p.Prime] (S : Finset ℕ) (x : ℕ → ℕ) (t : ZMod (p ^ 2))
    (hsum : ∑ i ∈ S, ((x i : ZMod p))⁻¹ = 0) :
    ∏ i ∈ S, (if p ∣ x i then (1 : ZMod (p ^ 2)) else
        (x i : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * t) =
      ∏ i ∈ S, (if p ∣ x i then (1 : ZMod (p ^ 2)) else (x i : ZMod (p ^ 2))) := by
  set y : ℕ → ℕ := fun i => (((x i : ZMod p))⁻¹).val with hy
  have hpt : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hterm : ∀ i ∈ S, (if p ∣ x i then (1 : ZMod (p ^ 2)) else
      (x i : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * t) =
      (if p ∣ x i then (1 : ZMod (p ^ 2)) else (x i : ZMod (p ^ 2))) *
        (1 + (p : ZMod (p ^ 2)) * (t * (y i : ZMod (p ^ 2)))) := by
    intro i _
    by_cases hdvd : p ∣ x i
    · have h0 : ((x i : ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      simp [hdvd, hy, h0]
    · simp only [hdvd, if_false]
      have hne : ((x i : ZMod p)) ≠ 0 := fun h => hdvd ((ZMod.natCast_eq_zero_iff _ _).1 h)
      have hinv : ((x i * y i : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_mul, hy]
        simp only [ZMod.natCast_val, ZMod.cast_id', id]
        exact mul_inv_cancel₀ hne
      have hmod : x i * y i % p = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' (x i * y i) 1 p).1 (by simpa using hinv)
        rw [this, Nat.one_mod_eq_one.mpr (Fact.out : p.Prime).one_lt.ne']
      have hdecomp : x i * y i = p * (x i * y i / p) + 1 := by
        have := Nat.div_add_mod (x i * y i) p
        omega
      have hR : ((x i : ZMod (p ^ 2))) * (y i : ZMod (p ^ 2)) =
          (p : ZMod (p ^ 2)) * ((x i * y i / p : ℕ) : ZMod (p ^ 2)) + 1 := by
        have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) hdecomp
        push_cast at this
        exact this
      linear_combination (-((p : ZMod (p ^ 2)) * t)) * hR -
        (t * ((x i * y i / p : ℕ) : ZMod (p ^ 2))) * hpt
  rw [prod_congr rfl hterm, prod_mul_distrib, prod_one_add_mul_of_sq_eq_zero _ hpt]
  have hdiv : p ∣ ∑ i ∈ S, y i := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    rw [← hsum]
    refine sum_congr rfl fun i _ => ?_
    simp [hy]
  have hz : (p : ZMod (p ^ 2)) * ∑ i ∈ S, t * (y i : ZMod (p ^ 2)) = 0 := by
    rw [← mul_sum, mul_left_comm]
    have := natCast_prime_mul_eq_zero (p := p) hdiv
    push_cast at this
    rw [this, mul_zero]
  rw [hz, add_zero, mul_one]

/-- For `p ∤ d`, `j ↦ d j + g` (`j < p`) is a bijection onto `ZMod p`. -/
theorem prod_range_affine_eq {M : Type*} [CommMonoid M] {p : ℕ} [Fact p.Prime] (d g : ℕ)
    (hd : (d : ZMod p) ≠ 0) (F : ZMod p → M) :
    ∏ j ∈ range p, F ((d * j + g : ℕ) : ZMod p) = ∏ x : ZMod p, F x := by
  refine prod_nbij' (fun j => ((d * j + g : ℕ) : ZMod p))
    (fun x => ((x - g) * (d : ZMod p)⁻¹).val) (fun _ _ => mem_univ _) ?_ ?_ ?_ ?_
  · intro x _
    exact mem_range.2 (ZMod.val_lt _)
  · intro j hj
    have hjp : j < p := mem_range.1 hj
    push_cast
    rw [show ((d : ZMod p) * j + g - g) * (d : ZMod p)⁻¹ = j by field_simp; ring]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjp]
  · intro x _
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    ring
  · intro j _
    rfl

/-- For an odd prime `p`, the elements of `ZMod p` sum to zero. -/
theorem sum_univ_zmod_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ x : ZMod p, x = 0 := by
  have hneg : ∑ x : ZMod p, x = ∑ x : ZMod p, -x :=
    (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => by simp)).symm
  rw [sum_neg_distrib] at hneg
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  have : (2 : ZMod p) * ∑ x : ZMod p, x = 0 := by linear_combination hneg
  exact (mul_eq_zero.1 this).resolve_left h2

/-- For an odd prime `p` and `p ∤ d`, `∑_{j<p} (d j + g)⁻¹ = 0` in `ZMod p`
(with `0⁻¹ = 0`). -/
theorem sum_range_affine_inv_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (d g : ℕ)
    (hd : (d : ZMod p) ≠ 0) :
    ∑ j ∈ range p, ((d * j + g : ℕ) : ZMod p)⁻¹ = 0 := by
  have h := prod_range_affine_eq (M := Multiplicative (ZMod p)) d g hd
    (fun x => Multiplicative.ofAdd x⁻¹)
  have h' : ∑ j ∈ range p, ((d * j + g : ℕ) : ZMod p)⁻¹ = ∑ x : ZMod p, x⁻¹ := by
    simpa using congrArg Multiplicative.toAdd h
  rw [h', Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x => x⁻¹) (fun x => x) (fun x => rfl)]
  exact sum_univ_zmod_eq_zero hp2


/-! ## Dropping multiples of `p` -/

/-- `skip p m` is `1` when `p ∣ m` and `m` otherwise: the factor `m` with its
multiple-of-`p` case discarded. -/
def skip (p m : ℕ) : ℕ := if p ∣ m then 1 else m

example : skip 5 10 = 1 ∧ skip 5 7 = 7 := by decide

/-- Every `m` splits as its multiple-of-`p` part times `skip p m`. -/
theorem mul_skip (p m : ℕ) : (if p ∣ m then m else 1) * skip p m = m := by
  unfold skip; split_ifs <;> simp

/-- The image of `skip p m` in `ZMod (p ^ 2)`. -/
theorem cast_skip_sq (p m : ℕ) :
    ((skip p m : ℕ) : ZMod (p ^ 2)) = if p ∣ m then 1 else (m : ZMod (p ^ 2)) := by
  unfold skip; split_ifs <;> simp

/-- The image of `skip p m` in `ZMod p`. -/
theorem cast_skip (p m : ℕ) :
    ((skip p m : ℕ) : ZMod p) = if (m : ZMod p) = 0 then 1 else (m : ZMod p) := by
  unfold skip
  by_cases h : p ∣ m
  · simp [h, (ZMod.natCast_eq_zero_iff m p).2 h]
  · have h' : (m : ZMod p) ≠ 0 := fun h0 => h ((ZMod.natCast_eq_zero_iff m p).1 h0)
    simp [h, h']

/-- **Block shift.** For an odd prime `p` and `p ∤ d`, shifting the block
`d * j + g` (`j < p`) by `d * p * c` does not change the product of its
non-multiples of `p` modulo `p ^ 2`. -/
theorem block_shift {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (d g c : ℕ)
    (hd : (d : ZMod p) ≠ 0) :
    ((∏ j ∈ range p, skip p (d * (p * c + j) + g) : ℕ) : ZMod (p ^ 2)) =
      ((∏ j ∈ range p, skip p (d * j + g) : ℕ) : ZMod (p ^ 2)) := by
  have hrw : ∀ j, d * (p * c + j) + g = (d * j + g) + p * (d * c) := fun j => by ring
  have hdvd : ∀ j, (p ∣ (d * j + g) + p * (d * c)) ↔ p ∣ d * j + g :=
    fun j => (Nat.dvd_add_left (dvd_mul_right p _))
  simp only [Nat.cast_prod, cast_skip_sq, hrw, hdvd]
  have hsum := sum_range_affine_inv_eq_zero hp2 d g hd
  have key := prod_shift_eq (range p) (fun j => d * j + g)
    ((d : ZMod (p ^ 2)) * (c : ZMod (p ^ 2))) hsum
  refine Eq.trans (prod_congr rfl fun j _ => ?_) key
  split_ifs <;> push_cast <;> ring

/-- The `p`-block of the factorial shifts trivially modulo `p ^ 2`. -/
theorem block_shift_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) :
    ((∏ j ∈ range p, skip p (p * c + j + 1) : ℕ) : ZMod (p ^ 2)) =
      ((∏ j ∈ range p, skip p (j + 1) : ℕ) : ZMod (p ^ 2)) := by
  have h := block_shift hp2 1 1 c (by simp)
  simpa only [one_mul] using h

/-- `4` is nonzero modulo an odd prime. -/
theorem four_natCast_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ((4 : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h2 : p ∣ 2 ^ 2 := by simpa using h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
    ((Fact.out : p.Prime).dvd_of_dvd_pow h2))

/-- The `p`-block of `∏ (4k+3)` shifts trivially modulo `p ^ 2`. -/
theorem block_shift_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) :
    ((∏ j ∈ range p, skip p (4 * (p * c + j) + 3) : ℕ) : ZMod (p ^ 2)) =
      ((∏ j ∈ range p, skip p (4 * j + 3) : ℕ) : ZMod (p ^ 2)) :=
  block_shift hp2 4 3 c (four_natCast_ne_zero hp2)

/-- Modulo `p`, every affine block of non-multiples has the same product `W`. -/
theorem block_mod_p {p : ℕ} [Fact p.Prime] (d g : ℕ) (hd : (d : ZMod p) ≠ 0) :
    ((∏ j ∈ range p, skip p (d * j + g) : ℕ) : ZMod p) =
      ∏ x : ZMod p, (if x = 0 then 1 else x) := by
  simp only [Nat.cast_prod, cast_skip]
  exact prod_range_affine_eq d g hd (fun x => if x = 0 then 1 else x)

/-- The common block product modulo `p` is nonzero. -/
theorem prod_ite_ne_zero {p : ℕ} [Fact p.Prime] :
    ∏ x : ZMod p, (if x = 0 then (1 : ZMod p) else x) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro x _
  split_ifs with h
  · exact one_ne_zero
  · exact h


/-! ## The core congruence `2^(p-1) * ∏' (4j+3) ≡ ∏' (j+1) (mod p^2)` -/

/-- Splitting a product over `range (2n)` into even and odd indices. -/
theorem prod_range_two_mul {M : Type*} [CommMonoid M] (h : ℕ → M) (n : ℕ) :
    ∏ m ∈ range (2 * n), h m = ∏ m ∈ range n, (h (2 * m) * h (2 * m + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ, mul_assoc]

/-- Splitting a product over `range (k * p)` into `k` blocks of length `p`. -/
theorem prod_range_mul_blocks {M : Type*} [CommMonoid M] (h : ℕ → M) (p k : ℕ) :
    ∏ m ∈ range (k * p), h m = ∏ b ∈ range k, ∏ j ∈ range p, h (p * b + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, prod_range_add, ih, prod_range_succ, mul_comm p k]

/-- The `p`-free part of `(k p)!` is `X ^ k` modulo `p ^ 2`, `X = ∏' (j+1)`. -/
theorem prod_skip_succ_blocks {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    ((∏ m ∈ range (k * p), skip p (m + 1) : ℕ) : ZMod (p ^ 2)) =
      ((∏ j ∈ range p, skip p (j + 1) : ℕ) : ZMod (p ^ 2)) ^ k := by
  rw [prod_range_mul_blocks (fun m => skip p (m + 1)) p k, Nat.cast_prod]
  rw [prod_congr rfl fun b _ => block_shift_one hp2 b, prod_const, card_range]

/-- Counting the non-multiples of `p` in `[1, k p]`: each contributes a `2`. -/
theorem prod_two_blocks {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∏ m ∈ range (k * p), (if p ∣ m + 1 then 1 else 2) = 2 ^ (k * (p - 1)) := by
  rw [prod_range_mul_blocks (fun m => if p ∣ m + 1 then 1 else 2) p k]
  have hblock : ∀ b, ∏ j ∈ range p, (if p ∣ p * b + j + 1 then 1 else 2) = 2 ^ (p - 1) := by
    intro b
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
    rw [hq, prod_range_succ]
    have hlast : (q + 1) ∣ (q + 1) * b + q + 1 := ⟨b + 1, by ring⟩
    rw [if_pos hlast, mul_one, Nat.add_sub_cancel]
    rw [prod_congr rfl fun j hj => ?_, prod_const, card_range]
    rw [if_neg]
    intro hdvd
    have hj' : j < q := mem_range.1 hj
    rw [add_assoc, Nat.dvd_add_right (dvd_mul_right _ _)] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rw [prod_congr rfl fun b _ => hblock b, prod_const, card_range, ← pow_mul,
    mul_comm (p - 1) k]

/-- Doubling an index outside the multiples of the odd prime `p`. -/
theorem skip_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) :
    skip p (2 * (m + 1)) = (if p ∣ m + 1 then 1 else 2) * skip p (m + 1) := by
  have hcop : Nat.Coprime p 2 :=
    (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hiff : p ∣ 2 * (m + 1) ↔ p ∣ m + 1 := ⟨fun h => hcop.dvd_of_dvd_mul_left h,
    fun h => h.mul_left 2⟩
  unfold skip
  by_cases h : p ∣ m + 1 <;> simp [h, hiff]

/-- For `p ≡ 1 (mod 4)` the unique `j < p` with `p ∣ 4 j + 3` is `j = 3 (p / 4)`. -/
theorem dvd_four_mul_add_three_iff {p j : ℕ} (hp1 : p % 4 = 1) (hj : j < p) :
    p ∣ 4 * j + 3 ↔ j = 3 * (p / 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 4 * m + 1 := ⟨p / 4, by omega⟩
  have hm : (4 * m + 1) / 4 = m := by omega
  rw [hm]
  constructor
  · rintro ⟨q, hq⟩
    have hq4 : q < 4 := by nlinarith
    interval_cases q <;> omega
  · rintro rfl
    exact ⟨3, by ring⟩

/-- Exactly one `j < p` has `p ∣ 4 j + 3` when `p ≡ 1 (mod 4)`. -/
theorem filter_dvd_four_mul_add_three {p : ℕ} (hp1 : p % 4 = 1) :
    (range p).filter (fun j => p ∣ 4 * j + 3) = {3 * (p / 4)} := by
  ext j
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hj, hd⟩
    exact (dvd_four_mul_add_three_iff hp1 hj).1 hd
  · rintro rfl
    have hlt : 3 * (p / 4) < p := by omega
    exact ⟨hlt, (dvd_four_mul_add_three_iff hp1 hlt).2 rfl⟩

/-- **Reflection.** For `p ≡ 1 (mod 4)`, the `p`-free products over the residue
classes `1` and `3` modulo `4` below `4 p` agree modulo `p ^ 2`. -/
theorem prod_skip_one_eq_three {p : ℕ} [Fact p.Prime] (hp1 : p % 4 = 1) :
    ((∏ j ∈ range p, skip p (4 * j + 1) : ℕ) : ZMod (p ^ 2)) =
      ((∏ j ∈ range p, skip p (4 * j + 3) : ℕ) : ZMod (p ^ 2)) := by
  have hp2 : p ≠ 2 := by omega
  rw [← prod_range_reflect (fun j => skip p (4 * j + 1)) p, Nat.cast_prod]
  have hterm : ∀ j ∈ range p, ((skip p (4 * (p - 1 - j) + 1) : ℕ) : ZMod (p ^ 2)) =
      (if p ∣ 4 * j + 3 then (1 : ZMod (p ^ 2)) else -1) *
        (if p ∣ 4 * j + 3 then (1 : ZMod (p ^ 2)) else
          ((4 * j + 3 : ℕ) : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * (-4 : ZMod (p ^ 2))) := by
    intro j hj
    have hjp : j < p := mem_range.1 hj
    have hsum : 4 * (p - 1 - j) + 1 + (4 * j + 3) = 4 * p := by omega
    have hiff : p ∣ 4 * (p - 1 - j) + 1 ↔ p ∣ 4 * j + 3 := by
      rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff (4 * j + 3)]
      have h0 : ((4 * (p - 1 - j) + 1 : ℕ) : ZMod p) + ((4 * j + 3 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, hsum, Nat.cast_mul, ZMod.natCast_self, mul_zero]
      constructor
      · intro h; rw [h, zero_add] at h0; exact h0
      · intro h; rw [h, add_zero] at h0; exact h0
    rw [cast_skip_sq]
    by_cases h : p ∣ 4 * j + 3
    · rw [if_pos (hiff.2 h), if_pos h, if_pos h, one_mul]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, if_neg h]
      have hR : ((4 * (p - 1 - j) + 1 : ℕ) : ZMod (p ^ 2)) =
          4 * (p : ZMod (p ^ 2)) - ((4 * j + 3 : ℕ) : ZMod (p ^ 2)) := by
          rw [eq_sub_iff_add_eq, ← Nat.cast_add, hsum]; push_cast; ring
      rw [hR]; ring
  rw [prod_congr rfl hterm, prod_mul_distrib]
  have hsign : ∏ j ∈ range p, (if p ∣ 4 * j + 3 then (1 : ZMod (p ^ 2)) else -1) = 1 := by
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    have hcard := card_filter_add_card_filter_not
      (s := range p) (fun j => p ∣ 4 * j + 3)
    rw [filter_dvd_four_mul_add_three hp1, card_singleton, card_range] at hcard
    have heven : Even ((range p).filter (fun j => ¬ p ∣ 4 * j + 3)).card :=
      ⟨2 * (p / 4), by omega⟩
    exact heven.neg_one_pow
  rw [hsign, one_mul]
  have hshift := prod_shift_eq (range p) (fun j => 4 * j + 3) (-4 : ZMod (p ^ 2))
    (sum_range_affine_inv_eq_zero hp2 4 3 (four_natCast_ne_zero hp2))
  rw [hshift, Nat.cast_prod]
  exact prod_congr rfl fun j _ => (cast_skip_sq p _).symm


/-- In `ZMod (p ^ 2)`, a natural number not divisible by `p` is a unit. -/
theorem isUnit_cast_sq {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : ¬ p ∣ a) :
    IsUnit (a : ZMod (p ^ 2)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp two_pos).2 ha

/-- **Core congruence.** For a prime `p ≡ 1 (mod 4)`,
`2^(p-1) * ∏_{j<p, p ∤ 4j+3} (4j+3) ≡ ∏_{j<p, p ∤ j+1} (j+1) (mod p^2)`. -/
theorem core_congr {p : ℕ} [Fact p.Prime] (hp1 : p % 4 = 1) :
    ((2 ^ (p - 1) * ∏ j ∈ range p, skip p (4 * j + 3) : ℕ) : ZMod (p ^ 2)) =
      ((∏ j ∈ range p, skip p (j + 1) : ℕ) : ZMod (p ^ 2)) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set Q1 : ℕ := ∏ j ∈ range p, skip p (4 * j + 1) with hQ1
  set Q3 : ℕ := ∏ j ∈ range p, skip p (4 * j + 3) with hQ3
  set X : ℕ := ∏ j ∈ range p, skip p (j + 1) with hX
  set A : ℕ := 2 ^ (p - 1) * Q3 with hA
  -- the `p`-free part of `(4p)!`, split by parity of the factor
  have hsplit : ∏ m ∈ range (4 * p), skip p (m + 1) =
      2 ^ (2 * (p - 1)) * (∏ m ∈ range (2 * p), skip p (m + 1)) * (Q1 * Q3) := by
    rw [show 4 * p = 2 * (2 * p) by ring, prod_range_two_mul, prod_mul_distrib]
    have hodd : ∏ m ∈ range (2 * p), skip p (2 * m + 1) = Q1 * Q3 := by
      rw [prod_range_two_mul, prod_mul_distrib, hQ1, hQ3]
      congr 1
      · exact prod_congr rfl fun j _ => by ring_nf
      · exact prod_congr rfl fun j _ => by ring_nf
    have heven : ∏ m ∈ range (2 * p), skip p (2 * m + 1 + 1) =
        2 ^ (2 * (p - 1)) * ∏ m ∈ range (2 * p), skip p (m + 1) := by
      rw [← prod_two_blocks hp 2, ← prod_mul_distrib]
      exact prod_congr rfl fun m _ => by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, skip_two_mul hp hp2]
    rw [hodd, heven]
    ring
  have h4 := prod_skip_succ_blocks hp2 4
  have h2 := prod_skip_succ_blocks hp2 2
  rw [← hX] at h4 h2
  rw [hsplit, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, h2] at h4
  have hQ13 := prod_skip_one_eq_three hp1
  rw [← hQ1, ← hQ3] at hQ13
  rw [hQ13] at h4
  -- `X` is a unit modulo `p ^ 2`
  have hWne := prod_ite_ne_zero (p := p)
  have hXp : ((X : ℕ) : ZMod p) = ∏ x : ZMod p, (if x = 0 then 1 else x) := by
    have := block_mod_p (p := p) 1 1 (by simp)
    simpa only [one_mul] using this
  have hXndvd : ¬ p ∣ X := by
    intro hdvd
    rw [← ZMod.natCast_eq_zero_iff] at hdvd
    exact hWne (hXp ▸ hdvd)
  have hXu : IsUnit ((X : ℕ) : ZMod (p ^ 2)) := isUnit_cast_sq hp hXndvd
  -- hence `A ^ 2 = X ^ 2`
  have hsq : ((A : ℕ) : ZMod (p ^ 2)) ^ 2 = ((X : ℕ) : ZMod (p ^ 2)) ^ 2 := by
    have hXu2 : IsUnit (((X : ℕ) : ZMod (p ^ 2)) ^ 2) := hXu.pow 2
    apply hXu2.mul_left_cancel
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_mul'] at h4
    rw [hA]; push_cast
    linear_combination h4
  -- and `A ≡ X (mod p)`
  have hAp : ((A : ℕ) : ZMod p) = ((X : ℕ) : ZMod p) := by
    have hQ3p : ((Q3 : ℕ) : ZMod p) = ∏ x : ZMod p, (if x = 0 then 1 else x) :=
      block_mod_p 4 3 (four_natCast_ne_zero hp2)
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    rw [hA, Nat.cast_mul, Nat.cast_pow, hQ3p, hXp, Nat.cast_ofNat,
      ZMod.pow_card_sub_one_eq_one h2ne, one_mul]
  have hsumndvd : ¬ p ∣ A + X := by
    intro hdvd
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hAp, ← two_mul] at hdvd
    rcases mul_eq_zero.1 hdvd with h | h
    · have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · exact hXndvd ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hsu : IsUnit (((A + X : ℕ) : ZMod (p ^ 2))) := isUnit_cast_sq hp hsumndvd
  have hprod : (((A : ℕ) : ZMod (p ^ 2)) - X) * ((A + X : ℕ) : ZMod (p ^ 2)) = 0 := by
    push_cast
    linear_combination hsq
  have := (hsu.mul_left_eq_zero).1 hprod
  exact sub_eq_zero.1 this


/-! ## Block decompositions of `(p n)!` and `∏_{k < p n} (4k+3)` -/

/-- `(p n)! = p ^ n * n! * ∏_{b<n} ∏_{j<p} skip p (p b + j + 1)`. -/
theorem factorial_mul_eq_blocks {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (p * n).factorial =
      p ^ n * n.factorial * ∏ b ∈ range n, ∏ j ∈ range p, skip p (p * b + j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hblock : ∏ j ∈ range p, (p * n + j + 1) =
        p * (n + 1) * ∏ j ∈ range p, skip p (p * n + j + 1) := by
      rw [← prod_congr rfl fun j _ => mul_skip p (p * n + j + 1), prod_mul_distrib]
      congr 1
      rw [prod_eq_single (p - 1)]
      · have hv : p * n + (p - 1) + 1 = p * (n + 1) := by
          rw [add_assoc, Nat.sub_add_cancel hp]; ring
        rw [hv, if_pos (dvd_mul_right _ _)]
      · intro j hj hne
        rw [if_neg]
        intro hdvd
        rw [add_assoc, Nat.dvd_add_right (dvd_mul_right _ _)] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        have := mem_range.1 hj
        omega
      · intro h
        exact absurd (mem_range.2 (by omega)) h
    rw [mul_add, mul_one, ← prod_range_add_one_eq_factorial, prod_range_add,
      prod_range_add_one_eq_factorial, ih, prod_range_succ, Nat.factorial_succ, pow_succ]
    rw [show ∏ x ∈ range p, (p * n + x + 1) = ∏ j ∈ range p, (p * n + j + 1) from rfl, hblock]
    ring

/-- `∏_{k < p n} (4k+3) = p ^ n * ∏_{k<n} (4k+3) * ∏_{b<n} ∏_{j<p} skip p (4(p b + j)+3)`
for `p ≡ 1 (mod 4)`: the multiples of `p` among the factors are exactly
`p (4t+3)`, `t < n`. -/
theorem prod_four_mul_add_three_eq_blocks {p : ℕ} (hp1 : p % 4 = 1) (n : ℕ) :
    ∏ k ∈ range (p * n), (4 * k + 3) =
      p ^ n * (∏ k ∈ range n, (4 * k + 3)) *
        ∏ b ∈ range n, ∏ j ∈ range p, skip p (4 * (p * b + j) + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hblock : ∏ j ∈ range p, (4 * (p * n + j) + 3) =
        p * (4 * n + 3) * ∏ j ∈ range p, skip p (4 * (p * n + j) + 3) := by
      rw [← prod_congr rfl fun j _ => mul_skip p (4 * (p * n + j) + 3), prod_mul_distrib]
      congr 1
      have hval : 4 * (p * n + 3 * (p / 4)) + 3 = p * (4 * n + 3) := by
        have : p = 4 * (p / 4) + 1 := by omega
        nth_rewrite 3 [this]
        nth_rewrite 1 [this]
        ring
      rw [prod_eq_single (3 * (p / 4))]
      · rw [hval, if_pos (dvd_mul_right _ _)]
      · intro j hj hne
        rw [if_neg]
        intro hdvd
        have hdvd' : p ∣ 4 * j + 3 := by
          rw [show 4 * (p * n + j) + 3 = 4 * j + 3 + p * (4 * n) by ring,
            Nat.dvd_add_left (dvd_mul_right _ _)] at hdvd
          exact hdvd
        exact hne ((dvd_four_mul_add_three_iff hp1 (mem_range.1 hj)).1 hdvd')
      · intro h
        exact absurd (mem_range.2 (by omega)) h
    rw [mul_add, mul_one, prod_range_add, ih, prod_range_succ, prod_range_succ, hblock, pow_succ]
    ring

/-! ## Assembly -/

/-- The defining division is exact: `a n * n! = 2 ^ n * ∏_{k<n} (4k+3)`. -/
theorem a_mul_factorial (n : ℕ) :
    a n * n.factorial = 2 ^ n * ∏ k ∈ range n, (4 * k + 3) :=
  Nat.div_mul_cancel (factorial_dvd n)

/-- The exact integer identity behind the supercongruence:
`a (p n) * ∏_b X_b = a n * ∏_b (2^(p-1) Y_b)` with `X_b`, `Y_b` the `p`-free
block products of `(p n)!` and of `∏ (4k+3)`. -/
theorem a_mul_blocks {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (n : ℕ) :
    a (p * n) * ∏ b ∈ range n, ∏ j ∈ range p, skip p (p * b + j + 1) =
      a n * ∏ b ∈ range n, (2 ^ (p - 1) * ∏ j ∈ range p, skip p (4 * (p * b + j) + 3)) := by
  set X := ∏ b ∈ range n, ∏ j ∈ range p, skip p (p * b + j + 1) with hX
  set Y := ∏ b ∈ range n, ∏ j ∈ range p, skip p (4 * (p * b + j) + 3) with hY
  set P := ∏ k ∈ range n, (4 * k + 3) with hP
  have e1 := a_mul_factorial (p * n)
  rw [factorial_mul_eq_blocks hp.pos, prod_four_mul_add_three_eq_blocks hp1] at e1
  have e2 := a_mul_factorial n
  have h2p : 2 ^ (p * n) = 2 ^ n * (2 ^ (p - 1)) ^ n := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
    rw [Nat.add_sub_cancel, ← pow_mul, ← pow_add]
    ring_nf
  rw [prod_mul_distrib, prod_const, card_range]
  have hpos : 0 < p ^ n * n.factorial := Nat.mul_pos (pow_pos hp.pos n) (Nat.factorial_pos n)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc p ^ n * n.factorial * (a (p * n) * X)
      = a (p * n) * (p ^ n * n.factorial * X) := by ring
    _ = 2 ^ (p * n) * (p ^ n * P * Y) := e1
    _ = p ^ n * (2 ^ n * P) * ((2 ^ (p - 1)) ^ n * Y) := by rw [h2p]; ring
    _ = p ^ n * (a n * n.factorial) * ((2 ^ (p - 1)) ^ n * Y) := by rw [e2]
    _ = p ^ n * n.factorial * (a n * ((2 ^ (p - 1)) ^ n * Y)) := by ring

/-- **Peter Bala's supercongruence for A004982, all `n`.** For a prime
`p ≡ 1 (mod 4)` and every `n`, `a (p n) ≡ a n (mod p ^ 2)`. -/
theorem a_prime_mul_modEq {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (n : ℕ) :
    a (p * n) ≡ a n [MOD p ^ 2] := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  set X : ℕ := ∏ j ∈ range p, skip p (j + 1) with hXdef
  have key := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) (a_mul_blocks hp hp1 n)
  have hXb : ((∏ b ∈ range n, ∏ j ∈ range p, skip p (p * b + j + 1) : ℕ) : ZMod (p ^ 2)) =
      (X : ZMod (p ^ 2)) ^ n := by
    rw [Nat.cast_prod, prod_congr rfl fun b _ => block_shift_one hp2 b, prod_const, card_range]
  have hYb : ((∏ b ∈ range n, (2 ^ (p - 1) * ∏ j ∈ range p, skip p (4 * (p * b + j) + 3)) : ℕ) :
      ZMod (p ^ 2)) = (X : ZMod (p ^ 2)) ^ n := by
    have hb : ∀ b ∈ range n,
        ((2 ^ (p - 1) * ∏ j ∈ range p, skip p (4 * (p * b + j) + 3) : ℕ) : ZMod (p ^ 2)) =
          (X : ZMod (p ^ 2)) := by
      intro b _
      rw [Nat.cast_mul, block_shift_three hp2 b, ← Nat.cast_mul, core_congr hp1]
    rw [Nat.cast_prod, prod_congr rfl hb, prod_const, card_range]
  rw [Nat.cast_mul, Nat.cast_mul, hXb, hYb] at key
  have hXu : IsUnit ((X : ℕ) : ZMod (p ^ 2)) := by
    apply isUnit_cast_sq hp
    intro hdvd
    rw [← ZMod.natCast_eq_zero_iff] at hdvd
    have hXp : ((X : ℕ) : ZMod p) = ∏ x : ZMod p, (if x = 0 then 1 else x) := by
      have := block_mod_p (p := p) 1 1 (by simp)
      simpa only [one_mul] using this
    exact prod_ite_ne_zero (p := p) (hXp ▸ hdvd)
  rw [← ZMod.natCast_eq_natCast_iff]
  exact (hXu.pow n).mul_right_cancel key

/-! ## The conjecture -/

/-- **Peter Bala's conjecture for A004982 (Dec 22 2019), proved.**

Verbatim: "Conjecture: a(p*n) = a(n) (mod p^2) for prime p == 1 (mod 4) and all
positive integers n. Cf. A004981."

Here `a n = 2 ^ n * ∏_{k<n} (4k+3) / n!` is the OEIS definition; the division
is exact (`factorial_dvd`), so `a` is the integer sequence of the entry. The
statement keeps the entry's positivity guard `0 < n` (unused: the proof
(`a_prime_mul_modEq`) also covers `n = 0`). -/
theorem bala_conjecture (p n : ℕ) (hp : p.Prime) (hp1 : p % 4 = 1) (_hn : 0 < n) :
    a (p * n) ≡ a n [MOD p ^ 2] :=
  a_prime_mul_modEq hp hp1 n

/-! ## Sanity layer -/

-- Satisfiability: the hypotheses hold jointly at `p = 5`, `n = 1`, and the
-- conclusion is the concrete congruence `17556 ≡ 6 (mod 25)`.
example : Nat.Prime 5 ∧ 5 % 4 = 1 ∧ 0 < 1 ∧ a (5 * 1) ≡ a 1 [MOD 5 ^ 2] := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  decide

-- The hypothesis `p ≡ 1 (mod 4)` is load-bearing: at `p = 3` the congruence
-- fails already for `n = 1` (`308 - 6 = 302` is not divisible by `9`).
example : ¬ a (3 * 1) ≡ a 1 [MOD 3 ^ 2] := by decide

-- The modulus `p ^ 2` is sharp: at `p = 5`, `n = 1` the congruence fails
-- modulo `5 ^ 3` (`17556 - 6 = 17550 ≡ 50 (mod 125)`).
example : ¬ a (5 * 1) ≡ a 1 [MOD 5 ^ 3] := by decide

end Candidates.A004982ProdPrimePeter
