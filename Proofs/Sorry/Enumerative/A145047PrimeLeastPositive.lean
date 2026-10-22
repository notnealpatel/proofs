/-
# A145047 — Shevelev: the least admissible multiplier lies in A008784

## OEIS source (retrieved with `oeis show A145047` and the live entry,
## 2026-10-21)

```
NAME:     Primes p of the form 4k+1 for which s=10 is the least positive
          integer such that sp-(floor(sqrt(sp)))^2 is a square.
TERMS:    1237,1621,1721,1933,1949,1993,2221,2237,2309,2341,2473,2621,...
COMMENT (the conjecture):
  Conjecture: The least positive integer s can take values only from
  A008784 (see for s=1,2,5,10 sequences A145016, A145022, A145023 and this
  sequence).
AUTHOR:   Vladimir Shevelev, Sep 30 2008, Oct 05 2008
XREFS:    Cf. A145016, A145017, A145022, A145023, A008784.
```

A008784: "Numbers k such that sqrt(-1) mod k exists; or, numbers that are
primitively represented by x^2 + y^2."  Its first comment (Franklin T.
Adams-Watters, Sep 07 2008): "Numbers whose prime divisors are all
congruent to 1 mod 4, with the exception of at most a single factor of 2."
This file states membership in A008784 in that prime-divisor form:
`¬ 4 ∣ s` and no prime `q ≡ 3 (mod 4)` divides `s`.

## Status

Triage status: open.  The entry and the related entries A145016, A145022,
A145023, A245474 give no proof (A245474 has only an argument that the least
`s` is `< p`, a different statement).  Computation (python, 2026-10-21):
the claim holds for all 16900 primes `p ≡ 1 (mod 4)` below `400000`.

## Result

The conjecture is proved below (`leastS_mem_A008784`) by a descent: if
`s p = a² + b²` with `a = ⌊√(s p)⌋` and `d ∣ a`, `d ∣ b`, `d² ∣ s`, then
`s / d²` is again admissible, with `⌊√(s p / d²)⌋ = a / d`.  A prime
`q ≡ 3 (mod 4)` dividing `a² + b²` divides both `a` and `b`, and
`a² + b² ≡ 0 (mod 4)` forces `a`, `b` even.  The proof does not use that `p`
is prime beyond `q ≠ p`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A145047PrimeLeastPositive

/-! ## Definition layer -/

/-- `Admissible p s`: `s` is a positive integer such that
`s p - ⌊√(s p)⌋²` is a perfect square (OEIS A145047, NAME).

The natural-number subtraction is never truncated, since
`Nat.sqrt (s * p) ^ 2 ≤ s * p` (`Nat.sqrt_le'`). -/
def Admissible (p s : ℕ) : Prop :=
  0 < s ∧ IsSquare (s * p - Nat.sqrt (s * p) ^ 2)

instance (p : ℕ) : DecidablePred (Admissible p) := fun s => by
  unfold Admissible; infer_instance

/-- For `0 < p`, the multiplier `s = p` is admissible: `p·p - ⌊√(p²)⌋² = 0`. -/
theorem admissible_self {p : ℕ} (hp : 0 < p) : Admissible p p := by
  refine ⟨hp, ?_⟩
  rw [← sq, Nat.sqrt_eq', Nat.sub_self]
  exact ⟨0, rfl⟩

/-- `s(p)`: the least positive integer `s` such that `s p - ⌊√(s p)⌋²` is a
perfect square (OEIS A145047).  The defining set is nonempty for `0 < p`
(`admissible_self`), so the `sInf` is not the junk value `0`. -/
noncomputable def leastS (p : ℕ) : ℕ := sInf {s | Admissible p s}

/-- `leastS p` is admissible for `0 < p`. -/
theorem leastS_admissible {p : ℕ} (hp : 0 < p) : Admissible p (leastS p) :=
  Nat.sInf_mem (s := {s | Admissible p s}) ⟨p, admissible_self hp⟩

/-- No admissible multiplier is smaller than `leastS p`. -/
theorem leastS_le {p s : ℕ} (hs : Admissible p s) : leastS p ≤ s :=
  Nat.sInf_le hs

/-- Characterization of `leastS p` by an admissible `s` with no smaller
admissible multiplier. -/
theorem leastS_eq_of {p s : ℕ} (hs : Admissible p s)
    (hmin : ∀ t < s, ¬ Admissible p t) : leastS p = s := by
  refine le_antisymm (leastS_le hs) ?_
  by_contra hlt
  exact hmin _ (not_le.mp hlt) (Nat.sInf_mem (s := {s | Admissible p s}) ⟨s, hs⟩)

/-! ## Ground truth

`1237` and `1621` are the first two terms of A145047 (so `s(p) = 10`); `5`
is the first term of A145016 (`s = 1`), `13` of A145022 (`s = 2`). -/

example : leastS 1237 = 10 :=
  leastS_eq_of (by decide +kernel) (by decide +kernel)

example : leastS 1621 = 10 :=
  leastS_eq_of (by decide +kernel) (by decide +kernel)

example : leastS 5 = 1 :=
  leastS_eq_of (by decide +kernel) (by decide +kernel)

example : leastS 13 = 1 :=
  leastS_eq_of (by decide +kernel) (by decide +kernel)

/-- The hypotheses of `leastS_mem_A008784` are jointly satisfiable (`p = 5`). -/
example : Nat.Prime 5 ∧ 5 % 4 = 1 := ⟨by norm_num, rfl⟩

/-! ## Descent -/

/-- **Descent.**  If `0 < t`, `t d² p = a² + b²` with `a = ⌊√(t d² p)⌋`,
`d ∣ a`, `d ∣ b` and `0 < d`, then `t` is admissible. -/
theorem admissible_of_descent {p t d a b : ℕ} (ht : 0 < t) (hd : 0 < d)
    (hsum : t * d ^ 2 * p = a ^ 2 + b ^ 2)
    (ha : a = Nat.sqrt (t * d ^ 2 * p)) (hda : d ∣ a) (hdb : d ∣ b) :
    Admissible p t := by
  obtain ⟨a', rfl⟩ := hda
  obtain ⟨b', rfl⟩ := hdb
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hsum' : t * p = a' ^ 2 + b' ^ 2 := by
    have h1 : d ^ 2 * (t * p) = d ^ 2 * (a' ^ 2 + b' ^ 2) := by
      rw [← mul_assoc, mul_comm (d ^ 2) t, hsum]; ring
    exact Nat.eq_of_mul_eq_mul_left hd2 h1
  have hupper : t * d ^ 2 * p < (d * a' + 1) ^ 2 := by
    rw [ha]; exact Nat.lt_succ_sqrt' _
  have hsqrt : Nat.sqrt (t * p) = a' := by
    symm
    rw [Nat.eq_sqrt']
    refine ⟨by rw [hsum']; exact Nat.le_add_right _ _, ?_⟩
    have h2 : (d * a' + 1) ^ 2 ≤ (d * (a' + 1)) ^ 2 := by
      apply Nat.pow_le_pow_left; rw [mul_add, mul_one]; omega
    have h3 : d ^ 2 * (t * p) < d ^ 2 * (a' + 1) ^ 2 := by
      calc d ^ 2 * (t * p) = t * d ^ 2 * p := by ring
        _ < (d * a' + 1) ^ 2 := hupper
        _ ≤ (d * (a' + 1)) ^ 2 := h2
        _ = d ^ 2 * (a' + 1) ^ 2 := by ring
    exact Nat.lt_of_mul_lt_mul_left h3
  refine ⟨ht, b', ?_⟩
  rw [hsqrt, hsum', Nat.add_sub_cancel_left, sq]

/-- If `d² ∣ s` with `1 < d`, `s` admissible, and `d` divides both `⌊√(s p)⌋`
and the square root of the remainder, then `s` is not the least. -/
theorem not_least_of_descent {p s d a b : ℕ} (hs : 0 < s) (hd : 1 < d)
    (hsum : s * p = a ^ 2 + b ^ 2) (ha : a = Nat.sqrt (s * p))
    (hdvd : d ^ 2 ∣ s) (hda : d ∣ a) (hdb : d ∣ b) :
    ∃ t < s, Admissible p t := by
  obtain ⟨t, rfl⟩ := hdvd
  have ht : 0 < t := Nat.pos_of_mul_pos_left hs
  have hd1 : 1 < d ^ 2 := Nat.one_lt_pow two_ne_zero hd
  refine ⟨t, ?_, admissible_of_descent ht (by omega)
    (by rw [mul_comm t]; exact hsum) (by rw [mul_comm t]; exact ha) hda hdb⟩
  calc t = 1 * t := (one_mul t).symm
    _ < d ^ 2 * t := Nat.mul_lt_mul_of_pos_right hd1 ht

/-- From admissibility, extract `s p = a² + b²` with `a = ⌊√(s p)⌋`. -/
theorem exists_sq_add_sq_of_admissible {p s : ℕ} (hs : Admissible p s) :
    ∃ b, s * p = Nat.sqrt (s * p) ^ 2 + b ^ 2 := by
  obtain ⟨-, b, hb⟩ := hs
  refine ⟨b, ?_⟩
  have hle := Nat.sqrt_le' (s * p)
  rw [sq b, ← hb]
  omega

/-- A prime `q ≡ 3 (mod 4)` dividing `a² + b²` divides `b`. -/
theorem dvd_right_of_dvd_sq_add_sq {q a b : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3)
    (h : q ∣ a ^ 2 + b ^ 2) : q ∣ b := by
  haveI := Fact.mk hq
  by_contra hb
  have hy : (b : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hxy : (a : ZMod q) ^ 2 = -(b : ZMod q) ^ 2 := by
    have h0 : ((a ^ 2 + b ^ 2 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy hxy hq4

/-- `a² + b² ≡ 0 (mod 4)` forces `a` and `b` even. -/
theorem two_dvd_of_four_dvd_sq_add_sq {a b : ℕ} (h : 4 ∣ a ^ 2 + b ^ 2) :
    2 ∣ a ∧ 2 ∣ b := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Nat.pow_mod b] at h
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    ← Nat.mod_mod_of_dvd a (by norm_num : 2 ∣ 4), ← Nat.mod_mod_of_dvd b (by norm_num : 2 ∣ 4)]
  have ha : a % 4 < 4 := Nat.mod_lt a (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt b (by norm_num)
  generalize a % 4 = x at h ha ⊢
  generalize b % 4 = y at h hb ⊢
  interval_cases x <;> interval_cases y <;> simp_all

/-! ## The conjecture -/

/-- **Shevelev's conjecture (A145047, Vladimir Shevelev, Sep 30 2008).**

Verbatim: "Conjecture: The least positive integer s can take values only from
A008784."  For a prime `p ≡ 1 (mod 4)`, the least positive `s` with
`s p - ⌊√(s p)⌋²` a perfect square is in A008784: `4 ∤ s` and every prime
divisor `q` of `s` has `q % 4 ≠ 3`. -/
theorem leastS_mem_A008784 {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ¬ 4 ∣ leastS p ∧ ∀ q : ℕ, q.Prime → q ∣ leastS p → q % 4 ≠ 3 := by
  have hadm : Admissible p (leastS p) := leastS_admissible hp.pos
  have hmin : ∀ t < leastS p, ¬ Admissible p t := fun t ht h =>
    absurd (leastS_le h) (not_le.mpr ht)
  obtain ⟨b, hsum⟩ := exists_sq_add_sq_of_admissible hadm
  constructor
  · -- `4 ∣ s` forces `⌊√(s p)⌋` and `b` even; descend by `d = 2`.
    intro h4
    have h4sum : 4 ∣ Nat.sqrt (leastS p * p) ^ 2 + b ^ 2 :=
      hsum ▸ Dvd.dvd.mul_right h4 p
    obtain ⟨ha2, hb2⟩ := two_dvd_of_four_dvd_sq_add_sq h4sum
    obtain ⟨t, hlt, ht⟩ := not_least_of_descent hadm.1 one_lt_two hsum rfl
      (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4) ha2 hb2
    exact hmin t hlt ht
  · -- a prime `q ≡ 3 (mod 4)` dividing `s` divides `⌊√(s p)⌋` and `b`,
    -- hence `q² ∣ s` (as `q ≠ p`); descend by `d = q`.
    intro q hq hqs hq4
    have hqsum : q ∣ Nat.sqrt (leastS p * p) ^ 2 + b ^ 2 :=
      hsum ▸ Dvd.dvd.mul_right hqs p
    have hqb : q ∣ b := dvd_right_of_dvd_sq_add_sq hq hq4 hqsum
    have hqa : q ∣ Nat.sqrt (leastS p * p) :=
      hq.dvd_of_dvd_pow ((Nat.dvd_add_left (dvd_pow hqb two_ne_zero)).mp hqsum)
    have hq2sp : q ^ 2 ∣ leastS p * p := by
      rw [hsum]
      exact dvd_add (pow_dvd_pow_of_dvd hqa 2) (pow_dvd_pow_of_dvd hqb 2)
    have hcop : Nat.Coprime (q ^ 2) p :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_primes hq hp).mpr (by rintro rfl; omega))
    obtain ⟨t, hlt, ht⟩ := not_least_of_descent hadm.1 hq.one_lt hsum rfl
      (hcop.dvd_of_dvd_mul_right hq2sp) hqa hqb
    exact hmin t hlt ht

end Candidates.A145047PrimeLeastPositive
