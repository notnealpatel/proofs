/-
# A089001 — Israel: `2k²+1` is prime iff `k` is not `d + t/d` with `t` triangular

## OEIS source (retrieved with `oeis show A089001`, 2026-10-21)

```
NAME:     Numbers k such that 2*k^2 + 1 is prime.
TERMS:    1,3,6,9,21,24,27,30,33,36,42,45,66,72,75,87,93,96,99,102,105,123,
          132,135,153,156,162,177,186,189,201,204,219,228,237,240,255,264,...
COMMENT (the conjecture):
  Conjecture: these are the positive numbers that cannot be represented as
  d + t/d where t is a triangular number (A000217) and d is a divisor of t.
  Note that if k = d + n*(n+1)/(2*d), then 2*k^2 + 1 =
  (2*d^2 + (n+1)^2)*(2*d^2 + n^2)/(2*d^2) cannot be prime.
  - _Robert Israel_, Mar 10 2026
```

## Status

Triage: open (no proof recorded in the entry or found in the literature).
The entry proves only the direction "representable ⇒ composite" (Israel's
factorization).  The converse is a reformulation of the classical fact
(Euler) that `2` is an idoneal number: a composite `N = x² + 2y²` has a second
representation.  This file proves **both** directions.

## Boundary conventions

* `t` must be **positive**: `t = 0` is triangular (A000217 starts at `0`) and
  every `d` divides `0`, so `k = k + 0/k` would make every `k` representable
  and the literal statement false at `k = 1`.  Divisors of a positive `t` are
  automatically positive in `ℕ`.
* `k` must be positive ("the positive numbers"): `k = 0` is neither in the
  sequence (`2·0+1 = 1` is not prime) nor representable.

## Computational evidence

`/tmp/claude/a089001/check.py`: the direct definition agrees with primality of
`2k²+1` for all `1 ≤ k ≤ 300`, and the reduction "`2k²+1 = x² + 2y²` with
`x ≥ 3`" agrees for all `1 ≤ k ≤ 8000`.

## Proof outline

* (⇒, Israel) With `e = t/d`, `2de = n(n+1)` and
  `2d²(2k²+1) = (2d² + (n+1)²)(2d² + n²)`; a prime `p = 2k²+1` divides one
  factor, so the other is at most `2d²`, impossible for `n ≥ 1`.
* (⇐) Write `2k²+1 = AB` with `A, B > 1`.  Thue's pigeonhole lemma shows every
  divisor of `2k²+1` has the form `u² + 2v²`; Brahmagupta's identity gives two
  representations `x² + 2y²` of `AB`, and they cannot both have `x² = 1`.  A
  representation with odd `x = 2n+1 ≥ 3` yields `k = d + e`, `de = n(n+1)/2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A089001PrimeNotExist

/-! ## Definition layer -/

/-- `t` is a triangular number (OEIS A000217): `t = n(n+1)/2` for some `n ≥ 0`.
The division is exact because `n(n+1)` is even. -/
def IsTriangular (t : ℕ) : Prop := ∃ n : ℕ, t = n * (n + 1) / 2

/-- Israel's representability: `k = d + t/d` for a **positive** triangular
number `t` and a divisor `d ∣ t` (the division `t / d` is exact). -/
def IsDivisorTriangularSum (k : ℕ) : Prop :=
  ∃ t d : ℕ, 0 < t ∧ IsTriangular t ∧ d ∣ t ∧ k = d + t / d

/-- Membership in OEIS A089001: `2k² + 1` is prime. -/
def InA089001 (k : ℕ) : Prop := (2 * k ^ 2 + 1).Prime

/-! ### Ground truth -/

example : IsTriangular 0 := ⟨0, rfl⟩
example : IsTriangular 1 := ⟨1, rfl⟩
example : IsTriangular 3 := ⟨2, rfl⟩
example : IsTriangular 6 := ⟨3, rfl⟩
example : IsTriangular 10 := ⟨4, rfl⟩

/-- First listed terms: `1, 3, 6, 9, 21` are in A089001. -/
example : InA089001 1 ∧ InA089001 3 ∧ InA089001 6 ∧ InA089001 9 ∧ InA089001 21 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [InA089001]

/-- Non-terms below `21`: `2, 4, 5, 7, 8, 10` are not in A089001. -/
example : ¬ InA089001 2 ∧ ¬ InA089001 4 ∧ ¬ InA089001 5 ∧ ¬ InA089001 7 ∧
    ¬ InA089001 8 ∧ ¬ InA089001 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [InA089001]

/-- `2 = 1 + 1/1` with `t = 1` triangular. -/
example : IsDivisorTriangularSum 2 := ⟨1, 1, by norm_num, ⟨1, rfl⟩, one_dvd 1, rfl⟩

/-- `4 = 1 + 3/1` with `t = 3` triangular. -/
example : IsDivisorTriangularSum 4 := ⟨3, 1, by norm_num, ⟨2, rfl⟩, one_dvd 3, rfl⟩

/-- `1` is not representable: `d ≥ 1` and `t / d ≥ 1` force `k ≥ 2`. -/
example : ¬ IsDivisorTriangularSum 1 := by
  rintro ⟨t, d, ht, -, hd, hk⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd ht
  have he0 : 0 < t / d := Nat.div_pos (Nat.le_of_dvd ht hd) hd0
  omega

/-! ## Israel's direction: representable ⇒ composite -/

/-- `2 · (n(n+1)/2) = n(n+1)`. -/
theorem two_mul_triangle (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)

/-- Israel's identity: if `2de = n(n+1)` then
`2d²(2(d+e)² + 1) = (2d² + (n+1)²)(2d² + n²)`. -/
theorem israel_identity (d e n : ℕ) (h : 2 * d * e = n * (n + 1)) :
    2 * d ^ 2 * (2 * (d + e) ^ 2 + 1) = (2 * d ^ 2 + (n + 1) ^ 2) * (2 * d ^ 2 + n ^ 2) := by
  have hz : (2 * d * e : ℤ) = n * (n + 1) := by exact_mod_cast h
  have key : (2 * d ^ 2 * (2 * (d + e) ^ 2 + 1) : ℤ) =
      (2 * d ^ 2 + (n + 1) ^ 2) * (2 * d ^ 2 + n ^ 2) := by
    linear_combination (4 * (d : ℤ) ^ 2 + n * (n + 1) + 2 * d * e) * hz
  exact_mod_cast key

/-- If `k` is representable as `d + t/d` with `t > 0` triangular and `d ∣ t`,
then `2k² + 1` is not prime (Israel, the direction recorded in the entry). -/
theorem not_prime_of_isDivisorTriangularSum (k : ℕ) (hk : IsDivisorTriangularSum k) :
    ¬ (2 * k ^ 2 + 1).Prime := by
  obtain ⟨t, d, ht, ⟨n, rfl⟩, hd, rfl⟩ := hk
  intro hp
  set e := n * (n + 1) / 2 / d with he
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd ht
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at ht
    · exact h0
  have hde : d * e = n * (n + 1) / 2 := Nat.mul_div_cancel' hd
  have h2de : 2 * d * e = n * (n + 1) := by
    rw [mul_assoc, hde, two_mul_triangle]
  have hid := israel_identity d e n h2de
  set p := 2 * (d + e) ^ 2 + 1 with hpdef
  have hdvd : p ∣ (2 * d ^ 2 + (n + 1) ^ 2) * (2 * d ^ 2 + n ^ 2) :=
    ⟨2 * d ^ 2, by rw [← hid]; ring⟩
  have hd2 : 0 < 2 * d ^ 2 := by positivity
  have hn2 : 0 < n ^ 2 := by positivity
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with ⟨q, hq⟩ | ⟨q, hq⟩
  · -- `p ∣ 2d² + (n+1)²`: then `q · (2d² + n²) = 2d²`, impossible.
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have hp0 : 0 < p := hp.pos
    rw [hq] at hid
    have hcancel : 2 * d ^ 2 = q * (2 * d ^ 2 + n ^ 2) := by
      apply Nat.eq_of_mul_eq_mul_left hp0
      rw [mul_comm p (2 * d ^ 2), hid]; ring
    nlinarith
  · have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have hp0 : 0 < p := hp.pos
    rw [hq] at hid
    have hcancel : 2 * d ^ 2 = q * (2 * d ^ 2 + (n + 1) ^ 2) := by
      apply Nat.eq_of_mul_eq_mul_left hp0
      rw [mul_comm p (2 * d ^ 2), hid]; ring
    nlinarith

/-! ## The converse: composite ⇒ representable -/

/-- **Thue's lemma for the form `u² + 2v²`.**  Every positive divisor `A` of
`2k² + 1` is of the form `a² + 2b²` with `a, b ∈ ℤ`. -/
theorem sq_add_two_sq_of_dvd (A k : ℕ) (hA : 0 < A) (hdvd : A ∣ 2 * k ^ 2 + 1) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = (A : ℤ) := by
  haveI : NeZero A := ⟨hA.ne'⟩
  set r := Nat.sqrt A with hr
  have hr2 : r ^ 2 ≤ A := by rw [hr, sq]; exact Nat.sqrt_le A
  have hr3 : A < (r + 1) ^ 2 := Nat.lt_succ_sqrt' A
  let f : Fin (r + 1) × Fin (r + 1) → ZMod A :=
    fun p => ((p.1 : ℕ) : ZMod A) - (k : ZMod A) * ((p.2 : ℕ) : ZMod A)
  have hcard : Fintype.card (ZMod A) < Fintype.card (Fin (r + 1) × Fin (r + 1)) := by
    simp only [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  set s : ℤ := (a₁ : ℕ) - (a₂ : ℕ) with hs
  set t : ℤ := (b₁ : ℕ) - (b₂ : ℕ) with ht
  have hst : ((s : ℤ) : ZMod A) = (k : ZMod A) * ((t : ℤ) : ZMod A) := by
    simp only [f] at heq
    simp only [hs, ht, Int.cast_sub, Int.cast_natCast]
    linear_combination heq
  have hk : ((2 * k ^ 2 + 1 : ℕ) : ZMod A) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  have hdiv : (A : ℤ) ∣ t ^ 2 + 2 * s ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk ⊢
    rw [hst]
    linear_combination (t : ZMod A) ^ 2 * hk
  have ha₁ : (a₁ : ℕ) ≤ r := Nat.lt_succ_iff.1 a₁.isLt
  have ha₂ : (a₂ : ℕ) ≤ r := Nat.lt_succ_iff.1 a₂.isLt
  have hb₁ : (b₁ : ℕ) ≤ r := Nat.lt_succ_iff.1 b₁.isLt
  have hb₂ : (b₂ : ℕ) ≤ r := Nat.lt_succ_iff.1 b₂.isLt
  have hrA : ((r : ℤ)) ^ 2 ≤ (A : ℤ) := by exact_mod_cast hr2
  have hs2 : s ^ 2 ≤ (A : ℤ) := by
    have h1 : -(r : ℤ) ≤ s := by rw [hs]; omega
    have h2 : s ≤ (r : ℤ) := by rw [hs]; omega
    nlinarith
  have ht2 : t ^ 2 ≤ (A : ℤ) := by
    have h1 : -(r : ℤ) ≤ t := by rw [ht]; omega
    have h2 : t ≤ (r : ℤ) := by rw [ht]; omega
    nlinarith
  have hpos : 0 < t ^ 2 + 2 * s ^ 2 := by
    by_contra hcon
    have hs0 : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    have ht0 : t = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    apply hne
    have e1 : a₁ = a₂ := Fin.ext (by omega)
    have e2 : b₁ = b₂ := Fin.ext (by omega)
    rw [e1, e2]
  obtain ⟨j, hj⟩ := hdiv
  have hApos : (0 : ℤ) < A := by exact_mod_cast hA
  have hj1 : 1 ≤ j := by
    by_contra hcon
    nlinarith
  have hj3 : j ≤ 3 := by
    by_contra hcon
    nlinarith
  interval_cases j
  · exact ⟨t, s, by linarith⟩
  · have hteven : Even t := by
      have h2t : Even (t ^ 2) := ⟨A - s ^ 2, by linarith⟩
      exact (Int.even_pow' two_ne_zero).1 h2t
    obtain ⟨u, hu⟩ := hteven
    exact ⟨s, u, by rw [hu] at hj; linarith⟩
  · have htA : t ^ 2 = A := by nlinarith
    exact ⟨t, 0, by rw [htA]; ring⟩

/-- From a representation `2k² + 1 = x² + 2y²` in `ℕ` with `x ≠ 1`, build the
representation `k = d + t/d` with `t = n(n+1)/2`, `x = 2n + 1`, `k = y + 2d`. -/
theorem isDivisorTriangularSum_of_sq_add_two_sq (k x y : ℕ)
    (h : x ^ 2 + 2 * y ^ 2 = 2 * k ^ 2 + 1) (hx : x ≠ 1) : IsDivisorTriangularSum k := by
  -- `x` is odd, `x = 2n + 1` with `n ≥ 1`.
  obtain ⟨n, hxn | hxn⟩ := Nat.even_or_odd' x
  · exfalso
    have h' : 2 * (2 * n ^ 2 + y ^ 2) = 2 * k ^ 2 + 1 := by rw [← h, hxn]; ring
    omega
  have hn : 1 ≤ n := by omega
  have hsq : 2 * (n * (n + 1)) + y ^ 2 = k ^ 2 := by
    have h' : 2 * (2 * (n * (n + 1)) + y ^ 2) + 1 = 2 * k ^ 2 + 1 := by rw [← h, hxn]; ring
    omega
  have hnn : 0 < n * (n + 1) := by positivity
  have hyk : y < k := by
    by_contra hcon
    have hky : k ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (not_lt.1 hcon) 2
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = y + j := ⟨k - y, by omega⟩
  have hj0 : 0 < j := by omega
  have hj : j * (2 * y + j) = 2 * (n * (n + 1)) := by
    have h' : (y + j) ^ 2 = y ^ 2 + j * (2 * y + j) := by ring
    omega
  obtain ⟨d, hjd | hjd⟩ := Nat.even_or_odd' j
  · subst hjd
    have hd0 : 0 < d := by omega
    have hT : n * (n + 1) = 2 * (d * (y + d)) := by
      have h' : 2 * d * (2 * y + 2 * d) = 2 * (2 * (d * (y + d))) := by ring
      omega
    have hTd : n * (n + 1) / 2 = d * (y + d) := by
      rw [hT, Nat.mul_div_cancel_left _ (by norm_num)]
    refine ⟨n * (n + 1) / 2, d, ?_, ⟨n, rfl⟩, ?_, ?_⟩
    · rw [hTd]; positivity
    · rw [hTd]; exact Dvd.intro _ rfl
    · rw [hTd, Nat.mul_div_cancel_left _ hd0]; ring
  · exfalso
    subst hjd
    have hodd : Odd ((2 * d + 1) * (2 * y + (2 * d + 1))) :=
      Nat.odd_mul.2 ⟨⟨d, rfl⟩, ⟨y + d, by ring⟩⟩
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) ⟨n * (n + 1), by ring⟩

/-- **Euler's idoneal property of `2`, specialized.**  If `k ≥ 1` and `2k² + 1`
is composite, then `2k² + 1 = x² + 2y²` with `x, y ∈ ℤ` and `x² ≠ 1`. -/
theorem exists_sq_add_two_sq_ne_one (k : ℕ) (hk : 0 < k) (hnp : ¬ (2 * k ^ 2 + 1).Prime) :
    ∃ x y : ℤ, x ^ 2 + 2 * y ^ 2 = 2 * (k : ℤ) ^ 2 + 1 ∧ x ^ 2 ≠ 1 := by
  set N := 2 * k ^ 2 + 1 with hN
  have hk2 : 0 < k ^ 2 := by positivity
  have hN1 : N ≠ 1 := by omega
  set A := N.minFac with hAdef
  have hAp : A.Prime := Nat.minFac_prime hN1
  have hA1 : 1 < A := hAp.one_lt
  have hAN : A ∣ N := Nat.minFac_dvd N
  obtain ⟨B, hB⟩ := hAN
  have hBN : B ∣ N := Dvd.intro_left A hB.symm
  have hB1 : 1 < B := by
    rcases Nat.lt_or_ge 1 B with h1 | h1
    · exact h1
    · interval_cases B
      · omega
      · rw [mul_one] at hB; rw [hB] at hnp; exact absurd hAp hnp
  obtain ⟨a, b, hab⟩ := sq_add_two_sq_of_dvd A k (by omega) ⟨B, hB⟩
  obtain ⟨c, e, hce⟩ := sq_add_two_sq_of_dvd B k (by omega) hBN
  have hNz : (2 * (k : ℤ) ^ 2 + 1) = (A : ℤ) * B := by exact_mod_cast hB
  have hA1z : (1 : ℤ) < A := by exact_mod_cast hA1
  have hB1z : (1 : ℤ) < B := by exact_mod_cast hB1
  by_contra hcon
  push Not at hcon
  have h1 : (a * c - 2 * b * e) ^ 2 = 1 := by
    apply hcon _ (a * e + b * c)
    rw [hNz, ← hab, ← hce]; ring
  have h2 : (a * c + 2 * b * e) ^ 2 = 1 := by
    apply hcon _ (a * e - b * c)
    rw [hNz, ← hab, ← hce]; ring
  have h1' : (a * c - 2 * (b * e) - 1) * (a * c - 2 * (b * e) + 1) = 0 := by
    linear_combination h1
  have h2' : (a * c + 2 * (b * e) - 1) * (a * c + 2 * (b * e) + 1) = 0 := by
    linear_combination h2
  have hbe : b * e = 0 := by
    rcases mul_eq_zero.1 h1' with h1'' | h1'' <;> rcases mul_eq_zero.1 h2' with h2'' | h2'' <;>
      omega
  have hac : a * c = 1 ∨ a * c = -1 := by
    rcases mul_eq_zero.1 h1' with h1'' | h1'' <;> omega
  have ha2 : a ^ 2 = 1 := by
    rcases hac with hac | hac
    · rcases Int.eq_one_or_neg_one_of_mul_eq_one hac with ha | ha <;> rw [ha] <;> norm_num
    · have hac' : a * (-c) = 1 := by linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hac' with ha | ha <;> rw [ha] <;> norm_num
  have hc2 : c ^ 2 = 1 := by
    rcases hac with hac | hac
    · have hca : c * a = 1 := by linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hca with hc | hc <;> rw [hc] <;> norm_num
    · have hca : c * (-a) = 1 := by linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hca with hc | hc <;> rw [hc] <;> norm_num
  rcases mul_eq_zero.1 hbe with hb | he
  · rw [hb, ha2] at hab; linarith
  · rw [he, hc2] at hce; linarith

/-- If `k ≥ 1` and `2k² + 1` is not prime, then `k` is representable as
`d + t/d` with `t > 0` triangular and `d ∣ t`. -/
theorem isDivisorTriangularSum_of_not_prime (k : ℕ) (hk : 0 < k)
    (hnp : ¬ (2 * k ^ 2 + 1).Prime) : IsDivisorTriangularSum k := by
  obtain ⟨x, y, hxy, hx1⟩ := exists_sq_add_two_sq_ne_one k hk hnp
  apply isDivisorTriangularSum_of_sq_add_two_sq k x.natAbs y.natAbs
  · have hz : ((x.natAbs : ℤ)) ^ 2 + 2 * ((y.natAbs : ℤ)) ^ 2 = 2 * (k : ℤ) ^ 2 + 1 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]; exact hxy
    exact_mod_cast hz
  · intro h
    apply hx1
    rw [← Int.natAbs_sq, h]; norm_num

/-! ## The conjecture -/

/-- **Israel's conjecture (A089001, Robert Israel, Mar 10 2026).**

Verbatim: "Conjecture: these are the positive numbers that cannot be
represented as d + t/d where t is a triangular number (A000217) and d is a
divisor of t."

Formal reading: for every `k ≥ 1`, `2k² + 1` is prime iff there are no `t > 0`
triangular and `d ∣ t` with `k = d + t/d`.  The positivity of `t` is required
(with `t = 0` every `k` is representable); `k ≥ 1` is the source's "positive
numbers". -/
theorem israel_conjecture (k : ℕ) (hk : 0 < k) :
    InA089001 k ↔ ¬ IsDivisorTriangularSum k := by
  constructor
  · intro hp hrep
    exact not_prime_of_isDivisorTriangularSum k hrep hp
  · intro hrep
    by_contra hnp
    exact hrep (isDivisorTriangularSum_of_not_prime k hk hnp)

end Candidates.A089001PrimeNotExist
