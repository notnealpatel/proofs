/-
# A277030 — Ordowski–Alkan: the least exponent `m` with `b ^ φ(n) ≡ b ^ m (mod n)`

## OEIS source (retrieved 2026-10-21 with `oeis show A277030`; author line
## from the live entry)

```
NAME:     Smallest m such that b^phi(n) == b^m (mod n) for every integer b,
          where phi(n) = A000010(n).
TERMS:    0,1,2,2,4,2,6,4,6,4,10,2,12,6,4,4,16,6,18,4,6,10,22,4,20,12,18,6,
          28,4,30,8,10,16,12,6,36,18,12,4,40,6,42,10,12,22,46,4,42,20,...
AUTHOR:   Thomas Ordowski and Altug Alkan, Sep 25 2016
KEYWORDS: nonn
COMMENT (the conjecture formalized here; no separate attribution, so it is
the authors', Sep 25 2016):
  Conjecture: a(n) > A002322(n) only for n = 8 and 24.
FORMULA (no separate attribution):
  Conjectured: a(n) = A002322(n), except for a(1) = 0 and a(8) = a(24) = 4.
```

`A002322` is the Carmichael function `λ`, Mathlib's
`ArithmeticFunction.carmichael`.

## Status

The triage recorded the conjecture as open: the entry gives no proof and no
later comment resolves it.  It follows from the folklore description of the
multiplicative semigroup of `ℤ/n` (index `max_p v_p(n)`, period `λ(n)`), so
it is a corollary of a known mechanism rather than a deep statement.  A
brute-force check (python, 2026-10-21, all bases `0 ≤ b < n`) for
`1 ≤ n ≤ 2600` finds `a(n) ≠ λ(n)` exactly at `n = 1, 8, 24`.

## Proof (formalized below, no `sorry`)

* Upper bound.  If every prime power `p ^ k ∣ n` has `k ≤ λ(n)`, then
  `b ^ φ(n) ≡ b ^ λ(n) (mod p ^ k)` for every `b`: if `p ∣ b` both sides are
  `0` mod `p ^ k`; otherwise `λ(p ^ k) ∣ λ(n) ∣ φ(n) - λ(n)` kills the
  difference.  Prime-power divisibility then gives the congruence mod `n`.
* `k ≤ λ(p ^ k)` for every prime power except `8`; and `8 ∣ n` with
  `λ(n) < 3` forces `λ(n) = 2`, hence `n ∣ 24`, hence `n ∈ {8, 24}`.
* Lower bound for `n ≥ 2`.  A unit of order `λ(n)` forces `λ(n) ∣ m`, and
  `b = 0` forces `m ≠ 0`.
* `n = 1, 8, 24` are decided directly in `ZMod n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A277030LeastPhiMod

open ArithmeticFunction

/-- The defining property of `A277030`: `b ^ φ(n) ≡ b ^ m (mod n)` for every integer `b`. -/
def PhiPowAgree (n m : ℕ) : Prop :=
  ∀ b : ℤ, b ^ n.totient ≡ b ^ m [ZMOD n]

/-- The exponent `m = φ(n)` always has the defining property, so the least one exists. -/
theorem phiPowAgree_totient (n : ℕ) : ∃ m, PhiPowAgree n m :=
  ⟨n.totient, fun _ => Int.ModEq.refl _⟩

open Classical in
/-- `A277030(n)`: the smallest `m ≥ 0` such that `b ^ φ(n) ≡ b ^ m (mod n)` for every
integer `b`. -/
noncomputable def a277030 (n : ℕ) : ℕ :=
  Nat.find (phiPowAgree_totient n)

/-- The defining congruence over all integers is equivalent to the identity
`b ^ φ(n) = b ^ m` in `ZMod n`. -/
theorem phiPowAgree_iff_zmod (n m : ℕ) :
    PhiPowAgree n m ↔ ∀ b : ZMod n, b ^ n.totient = b ^ m := by
  constructor
  · intro h b
    obtain ⟨c, rfl⟩ := ZMod.intCast_surjective b
    have hc := (ZMod.intCast_eq_intCast_iff _ _ n).mpr (h c)
    push_cast at hc
    exact hc
  · intro h b
    refine (ZMod.intCast_eq_intCast_iff _ _ n).mp ?_
    push_cast
    exact h _

/-- Characterisation of `a277030 n = k`: `k` has the property and no smaller exponent does. -/
theorem a277030_eq_iff (n k : ℕ) :
    a277030 n = k ↔ PhiPowAgree n k ∧ ∀ m < k, ¬ PhiPowAgree n m := by
  classical
  unfold a277030
  rw [Nat.find_eq_iff]

/-- Upper-bound engine: if every prime power `p ^ k ∣ n` has `k ≤ λ(n)`, then `λ(n)` has the
defining property. -/
theorem phiPowAgree_carmichael {n : ℕ} (hn : 0 < n)
    (hk : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → k ≤ carmichael n) :
    PhiPowAgree n (carmichael n) := by
  intro b
  have hlt : carmichael n ≤ n.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hn) (carmichael_dvd_totient n)
  obtain ⟨d, hd⟩ : ∃ d, n.totient = carmichael n + d := ⟨_, (Nat.add_sub_of_le hlt).symm⟩
  have hdvd_d : carmichael n ∣ d := by
    have h1 := carmichael_dvd_totient n
    rw [hd] at h1
    exact (Nat.dvd_add_right (dvd_refl _)).mp h1
  rw [hd, pow_add]
  refine (Int.ModEq.symm ?_)
  rw [Int.modEq_iff_dvd, Int.natCast_dvd]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ n).mpr fun p k hp hpk => ?_
  have hkle : k ≤ carmichael n := hk p k hp hpk
  rw [← Int.natCast_dvd, show b ^ carmichael n * b ^ d - b ^ carmichael n
      = b ^ carmichael n * (b ^ d - 1) by ring]
  by_cases hpb : (p : ℤ) ∣ b
  · refine Dvd.dvd.mul_right ?_ _
    push_cast
    exact (pow_dvd_pow_of_dvd hpb k).trans (pow_dvd_pow b hkle)
  · refine Dvd.dvd.mul_left ?_ _
    have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) b := by
      push_cast
      exact ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hpb).pow_left
    have hunit : IsUnit (b : ZMod (p ^ k)) := (ZMod.coe_int_isUnit_iff_isCoprime b _).mpr hcop
    have hdiv : carmichael (p ^ k) ∣ d := (carmichael_dvd hpk).trans hdvd_d
    obtain ⟨e, he⟩ := hdiv
    have hone : (b : ZMod (p ^ k)) ^ d = 1 := by
      have hu := pow_carmichael hunit.unit
      rw [he, pow_mul]
      rw [← IsUnit.unit_spec hunit, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hu,
        one_pow, Units.val_one]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hone, sub_self]

/-- Lower bound: for `n ≥ 2`, every exponent with the defining property is at least `λ(n)`.
A unit of order `λ(n)` forces `λ(n) ∣ m`, and `b = 0` rules out `m = 0`. -/
theorem carmichael_le_of_phiPowAgree {n m : ℕ} (hn : 2 ≤ n) (h : PhiPowAgree n m) :
    carmichael n ≤ m := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [phiPowAgree_iff_zmod] at h
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 := h 0
    rw [zero_pow (Nat.totient_pos.mpr (by omega)).ne', pow_zero] at h0
    exact zero_ne_one h0
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent
    (Monoid.ExponentExists.of_finite (G := (ZMod n)ˣ))
  have hgm : g ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← h, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one]
  have hdvd : carmichael n ∣ m := by
    rw [carmichael_eq_exponent', ← hg]
    exact orderOf_dvd_of_pow_eq_one hgm
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd

/-- `λ(n)` is positive for `n > 0`. -/
theorem carmichael_pos {n : ℕ} (hn : 0 < n) : 0 < carmichael n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [carmichael_eq_exponent']
  exact Monoid.exponent_pos.mpr (Monoid.ExponentExists.of_finite)

/-- For a prime power other than `8`, the exponent is at most the Carmichael function:
`k ≤ λ(p ^ k)` unless `p = 2` and `k = 3`. -/
theorem le_carmichael_prime_pow {p k : ℕ} (hp : p.Prime) (h : ¬ (p = 2 ∧ k = 3)) :
    k ≤ carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hk3 : k ≠ 3 := fun hk => h ⟨rfl, hk⟩
    by_cases hk2 : k = 2
    · subst hk2
      rw [carmichael_two_pow_of_le_two le_rfl]
      norm_num
    rw [carmichael_two_pow_of_ne_two hk2]
    by_cases hk : k ≤ 1
    · interval_cases k <;> simp
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    have hj : j < 2 ^ j := Nat.lt_two_pow_self
    rw [show j + 4 - 2 = j + 2 by omega, pow_add]
    omega
  · by_cases hk : k = 0
    · simp [hk]
    rw [carmichael_pow_of_prime_ne_two k hp hp2, Nat.totient_prime_pow hp (by omega)]
    have h1 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (k - 1) ≤ p ^ (k - 1) := Nat.pow_le_pow_left hp.two_le _
    have h3 : 1 ≤ p - 1 := by have := hp.two_le; omega
    calc k ≤ p ^ (k - 1) := by omega
      _ = p ^ (k - 1) * 1 := (mul_one _).symm
      _ ≤ p ^ (k - 1) * (p - 1) := Nat.mul_le_mul_left _ h3

/-- If `λ(n) = 2` then `n ∣ 24`. -/
theorem dvd_24_of_carmichael_eq_two {n : ℕ} (h : carmichael n = 2) : n ∣ 24 := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd 24 n).mpr fun q j hq hqj => ?_
  have hle : carmichael (q ^ j) ≤ 2 := h ▸ Nat.le_of_dvd (by omega) (carmichael_dvd hqj)
  by_cases hq2 : q = 2
  · subst hq2
    have hj : j ≤ 3 := by
      by_contra hj
      have := le_carmichael_prime_pow hq (k := j) (by omega)
      omega
    interval_cases j <;> norm_num
  · by_cases hj : j = 0
    · simp [hj]
    rw [carmichael_pow_of_prime_ne_two j hq hq2, Nat.totient_prime_pow hq (by omega)] at hle
    have hq3 : q = 3 := by
      have h1 : 1 ≤ q ^ (j - 1) := Nat.one_le_pow _ _ hq.pos
      have h2 := hq.two_le
      have h3 : q - 1 ≤ 2 := le_trans (Nat.le_mul_of_pos_left _ h1) hle
      omega
    subst hq3
    have hj1 : j = 1 := by
      by_contra hj1
      have h1 : 3 ≤ 3 ^ (j - 1) := by
        calc 3 = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 3 ^ (j - 1) * (3 - 1) ≤ 2 := hle
      omega
    subst hj1
    norm_num

/-- `λ(8) = 2`. -/
theorem carmichael_eight : carmichael 8 = 2 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, carmichael_two_pow_of_ne_two (by norm_num)]
  norm_num

/-- `λ(24) = 2`. -/
theorem carmichael_twentyFour : carmichael 24 = 2 := by
  have h3 : carmichael 3 = 2 := by
    rw [show (3 : ℕ) = 3 ^ 1 by norm_num, carmichael_pow_of_prime_ne_two 1 Nat.prime_three
      (by norm_num)]
    decide
  rw [show (24 : ℕ) = 8 * 3 by norm_num, carmichael_mul (by norm_num), carmichael_eight, h3]
  norm_num

/-- For `n > 0` other than `8` and `24`, every prime power `p ^ k ∣ n` has `k ≤ λ(n)`. -/
theorem le_carmichael_of_prime_pow_dvd {n : ℕ} (hn : 0 < n) (h8 : n ≠ 8) (h24 : n ≠ 24)
    {p k : ℕ} (hp : p.Prime) (hpk : p ^ k ∣ n) : k ≤ carmichael n := by
  by_cases hex : p = 2 ∧ k = 3
  · obtain ⟨rfl, rfl⟩ := hex
    have h8n : 8 ∣ n := by simpa using hpk
    have hdvd : 2 ∣ carmichael n := carmichael_eight ▸ carmichael_dvd h8n
    have hpos := carmichael_pos hn
    by_contra hlt
    have h2 : carmichael n = 2 := by
      obtain ⟨c, hc⟩ := hdvd
      omega
    have h24n := dvd_24_of_carmichael_eq_two h2
    have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) h24n
    interval_cases n <;> simp_all
  · exact (le_carmichael_prime_pow hp hex).trans
      (Nat.le_of_dvd (carmichael_pos hn) (carmichael_dvd hpk))

/-- **Formula (%F of A277030), main case.** For `n ≥ 2` with `n ≠ 8` and `n ≠ 24`,
`A277030(n) = λ(n)` (Carmichael function, `A002322`). -/
theorem a277030_eq_carmichael {n : ℕ} (hn : 2 ≤ n) (h8 : n ≠ 8) (h24 : n ≠ 24) :
    a277030 n = carmichael n := by
  rw [a277030_eq_iff]
  refine ⟨phiPowAgree_carmichael (by omega) fun p k hp hpk =>
    le_carmichael_of_prime_pow_dvd (by omega) h8 h24 hp hpk, fun m hm hm' => ?_⟩
  exact absurd (carmichael_le_of_phiPowAgree hn hm') (by omega)

/-- `A277030(1) = 0`. -/
theorem a277030_one : a277030 1 = 0 := by
  rw [a277030_eq_iff, phiPowAgree_iff_zmod]
  exact ⟨fun b => Subsingleton.elim _ _, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/-- `A277030(8) = 4`. -/
theorem a277030_eight : a277030 8 = 4 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

/-- `A277030(24) = 4`. -/
theorem a277030_twentyFour : a277030 24 = 4 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

/-- **Conjecture of A277030** ("a(n) > A002322(n) only for n = 8 and 24"), in the sharp
form: for `n ≥ 1`, `λ(n) < A277030(n)` holds exactly when `n = 8` or `n = 24`. -/
theorem carmichael_lt_a277030_iff {n : ℕ} (hn : 0 < n) :
    carmichael n < a277030 n ↔ n = 8 ∨ n = 24 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    by_cases h1 : n = 1
    · subst h1
      rw [a277030_one] at h
      exact Nat.not_lt_zero _ h
    rw [a277030_eq_carmichael (by omega) hne.1 hne.2] at h
    exact lt_irrefl _ h
  · rintro (rfl | rfl)
    · rw [a277030_eight, carmichael_eight]
      norm_num
    · rw [a277030_twentyFour, carmichael_twentyFour]
      norm_num

/-- **Formula of A277030 (%F)** in full: `a(n) = λ(n)` for every `n ≥ 1` except
`a(1) = 0` and `a(8) = a(24) = 4`. -/
theorem a277030_formula {n : ℕ} (hn : 0 < n) :
    a277030 n = if n = 1 then 0 else if n = 8 ∨ n = 24 then 4 else carmichael n := by
  by_cases h1 : n = 1
  · subst h1
    simp [a277030_one]
  by_cases h8 : n = 8
  · subst h8
    simp [a277030_eight]
  by_cases h24 : n = 24
  · subst h24
    simp [a277030_twentyFour]
  rw [if_neg h1, if_neg (by tauto), a277030_eq_carmichael (by omega) h8 h24]

/-! ## Ground truth: the first twelve listed terms `0,1,2,2,4,2,6,4,6,4,10,2` -/

example : a277030 1 = 0 := a277030_one

example : a277030 2 = 1 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m; decide⟩

example : a277030 3 = 2 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 4 = 2 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 5 = 4 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 6 = 2 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 7 = 6 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 8 = 4 := a277030_eight

example : a277030 9 = 6 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 10 = 4 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 11 = 10 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

example : a277030 12 = 2 := by
  rw [a277030_eq_iff]
  simp only [phiPowAgree_iff_zmod]
  exact ⟨by decide, fun m hm => by interval_cases m <;> decide⟩

/-! ## Sanity: the main statements are non-vacuous -/

-- The hypotheses of `a277030_eq_carmichael` are jointly satisfiable (`n = 12`),
-- and the conclusion there is the nontrivial value `λ(12) = 2`.
example : a277030 12 = carmichael 12 :=
  a277030_eq_carmichael (by norm_num) (by norm_num) (by norm_num)

-- Both directions of the conjecture are exercised: `8` is an exception, `16` is not.
example : carmichael 8 < a277030 8 := (carmichael_lt_a277030_iff (by norm_num)).mpr (Or.inl rfl)

example : ¬ carmichael 16 < a277030 16 := by
  rw [carmichael_lt_a277030_iff (by norm_num)]
  norm_num

end Candidates.A277030LeastPhiMod
