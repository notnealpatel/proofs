/-
# A219930 — Perry: the odd members are exactly 1 and 3

## OEIS source (pulled with `oeis show A219930` and the live entry, 2026-10-21)

```
NAME:     n such that phi(n) represents a new lower bound for the phi function.
TERMS:    1,3,8,14,20,36,48,66,70,96,126,132,156,240,252,300,336,450,480,540,
          660,690,714,870,900,1080,1320,1470,1530,1710,1950,2340,2940,2970,...
KEYWORDS: nonn
AUTHOR:   Jon Perry, Dec 01 2012
COMMENT (the conjecture, comment 2; no separate attribution, so it is the
         author's, Jon Perry, Dec 01 2012):
  Conjecture: Except for 1 and 3, all members of the sequence are even. If n
  is odd, it cannot be squarefree.
PROGRAM (Mathematica, T. D. Noe, Dec 04 2012) — the operative definition:
  keep the n with phi(n) <= phi(m) for every m > n ("suffix minima"), then
  keep those whose phi value exceeds the phi value of every earlier kept n.
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  The second sentence "If n is odd, it cannot be squarefree" cannot
hold literally (3 is an odd squarefree member); it is read as a statement about
odd members other than 1 and 3, where it is vacuous once the first sentence is
proved.  Comments 1 and 3 of the entry are separate conjectures, not treated.

## Result in this file

The conjecture is proved, in the stronger form `odd_isSuffixMin`: an odd `n`
with `φ n ≤ φ m` for all `m > n` is `1` or `3`.  Witnesses: if `9 ∣ n`, write
`n = 9s` and use `m = 12s`; otherwise `n` has a prime factor `q ≥ 5`, write
`n = qr` and use `m = r(q+1)`.  Computation (Python sieve to `10^6`, retrieval
date above) reproduces the listed terms through 2940 and finds no odd suffix
minimum other than 1 and 3.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A219930PhiListsValue

open Nat

/-! ## Definition layer -/

/-- `n` is a *suffix minimum* of Euler's totient: `φ n ≤ φ m` for every
`m > n` (first filter in Noe's Mathematica program for A219930). -/
def IsSuffixMin (n : ℕ) : Prop := ∀ m, n < m → φ n ≤ φ m

/-- `n` is a term of A219930: `n ≥ 1` is a suffix minimum of `φ` and its `φ`
value is a new record over every smaller positive suffix minimum ("`φ n`
represents a new lower bound"; second filter in Noe's program). -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ IsSuffixMin n ∧ ∀ k, 0 < k → k < n → IsSuffixMin k → φ k < φ n

/-! ## Ground truth -/

/-- `1` is a term of A219930 (the first listed term). -/
theorem isTerm_one : IsTerm 1 := by
  refine ⟨Nat.one_pos, fun m hm => ?_, fun k hk hk1 _ => absurd hk1 (by omega)⟩
  rw [Nat.totient_one]
  exact Nat.totient_pos.mpr (by omega)

/-- `3` is a term of A219930 (the second listed term). -/
theorem isTerm_three : IsTerm 3 := by
  have h3 : φ 3 = 2 := Nat.totient_prime Nat.prime_three
  refine ⟨by norm_num, fun m hm => ?_, fun k hk hk3 _ => ?_⟩
  · rw [h3]
    have hm0 : φ m ≠ 0 := by rw [Ne, Nat.totient_eq_zero]; omega
    have hm1 : φ m ≠ 1 := by rw [Ne, Nat.totient_eq_one_iff]; omega
    omega
  · rw [h3]
    interval_cases k <;> decide

/-- `2` is a suffix minimum but not a term: its value `φ 2 = 1` repeats `φ 1`. -/
example : ¬ IsTerm 2 := fun h => absurd (h.2.2 1 Nat.one_pos (by norm_num) isTerm_one.2.1)
  (by decide)

/-- `4` is not a term: its value `φ 4 = 2` repeats `φ 3`. -/
example : ¬ IsTerm 4 := fun h => absurd (h.2.2 3 (by norm_num) (by norm_num) isTerm_three.2.1)
  (by decide)

/-- `5` is not a suffix minimum: `φ 5 = 4 > φ 6 = 2`. -/
example : ¬ IsSuffixMin 5 := fun h => absurd (h 6 (by norm_num)) (by decide)

/-- `6` is a suffix minimum but not a term: its value `φ 6 = 2` repeats `φ 3`. -/
example : ¬ IsTerm 6 := fun h => absurd (h.2.2 3 (by norm_num) (by norm_num) isTerm_three.2.1)
  (by decide)

/-- `7` is not a suffix minimum: `φ 7 = 6 > φ 8 = 4`. -/
example : ¬ IsSuffixMin 7 := fun h => absurd (h 8 (by norm_num)) (by decide)

/-! ## Helper lemmas -/

/-- Upper bound `φ (a * b) ≤ a * φ b`. -/
theorem totient_mul_le_mul_totient (a b : ℕ) : φ (a * b) ≤ a * φ b := by
  induction a using Nat.recOnMul generalizing b with
  | zero => simp
  | one => simp
  | prime p hp =>
    by_cases hpb : p ∣ b
    · rw [Nat.totient_mul_of_prime_of_dvd hp hpb]
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpb]
      exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
  | mul x y hx hy =>
    calc φ (x * y * b) = φ (x * (y * b)) := by rw [Nat.mul_assoc]
      _ ≤ x * φ (y * b) := hx (y * b)
      _ ≤ x * (y * φ b) := Nat.mul_le_mul_left x (hy b)
      _ = x * y * φ b := (Nat.mul_assoc x y (φ b)).symm

/-- Lower bound `(q - 1) * φ r ≤ φ (q * r)` for a prime `q`. -/
theorem pred_mul_totient_le (q r : ℕ) (hq : q.Prime) : (q - 1) * φ r ≤ φ (q * r) := by
  by_cases hqr : q ∣ r
  · rw [Nat.totient_mul_of_prime_of_dvd hq hqr]
    exact Nat.mul_le_mul_right _ (Nat.sub_le q 1)
  · rw [Nat.totient_mul_of_prime_of_not_dvd hq hqr]

/-- For odd `s`, `φ (12 s) < φ (9 s)`: the witness against `9 s` being a suffix
minimum. -/
theorem totient_twelve_mul_lt (s : ℕ) (hs : Odd s) : φ (12 * s) < φ (9 * s) := by
  have h3s : Odd (3 * s) := Nat.odd_mul.mpr ⟨by decide, hs⟩
  have hcop : Nat.Coprime 4 (3 * s) := by
    have h2 : Nat.Coprime 2 (3 * s) := Nat.coprime_two_left.mpr h3s
    simpa using Nat.Coprime.pow_left 2 h2
  have h12 : φ (12 * s) = 2 * φ (3 * s) := by
    rw [show 12 * s = 4 * (3 * s) by ring, Nat.totient_mul hcop]
    rfl
  have h9 : φ (9 * s) = 3 * φ (3 * s) := by
    rw [show 9 * s = 3 * (3 * s) by ring,
      Nat.totient_mul_of_prime_of_dvd Nat.prime_three (dvd_mul_right 3 s)]
  have hpos : 0 < φ (3 * s) := Nat.totient_pos.mpr (by have hs0 := hs.pos; omega)
  omega

/-- For a prime `q ≥ 5` and odd `r`, `m = r (q + 1)` exceeds `q r` and has
smaller totient: the witness against `q r` being a suffix minimum. -/
theorem totient_mul_succ_lt (q r : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) (hr : Odd r) :
    q * r < r * (q + 1) ∧ φ (r * (q + 1)) < φ (q * r) := by
  obtain ⟨k, hk⟩ : Even (q + 1) := (hq.eq_two_or_odd'.resolve_left (by omega)).add_one
  have hkq : k < q - 1 := by omega
  have hrpos : 0 < r := hr.pos
  have hm : r * (q + 1) = k * (2 * r) := by rw [hk]; ring
  have hphir : 0 < φ r := Nat.totient_pos.mpr hrpos
  refine ⟨by nlinarith, ?_⟩
  calc φ (r * (q + 1)) = φ (k * (2 * r)) := by rw [hm]
    _ ≤ k * φ (2 * r) := totient_mul_le_mul_totient k (2 * r)
    _ = k * φ r := by rw [Nat.totient_two_mul_of_odd hr]
    _ < (q - 1) * φ r := Nat.mul_lt_mul_of_pos_right hkq hphir
    _ ≤ φ (q * r) := pred_mul_totient_le q r hq

/-- An odd `n ∉ {1, 3}` not divisible by `9` has a prime factor `q ≥ 5`. -/
theorem exists_prime_five_le_dvd (n : ℕ) (hn : Odd n) (h9 : ¬ 9 ∣ n) (h1 : n ≠ 1)
    (h3 : n ≠ 3) : ∃ q, q.Prime ∧ 5 ≤ q ∧ q ∣ n := by
  have five_le : ∀ q, q.Prime → q ≠ 2 → q ≠ 3 → 5 ≤ q := by
    intro q hq hq2 hq3
    have hq4 : q ≠ 4 := by rintro rfl; exact absurd hq (by decide)
    have hq2' := hq.two_le
    omega
  have not_two : ∀ q, q ∣ n → q ≠ 2 := by
    rintro q hqn rfl
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hqn)
  by_cases h3n : 3 ∣ n
  · obtain ⟨t, rfl⟩ := h3n
    have ht1 : t ≠ 1 := by omega
    have ht3 : ¬ 3 ∣ t := by
      rintro ⟨u, rfl⟩
      exact h9 ⟨u, by ring⟩
    obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd ht1
    have hqn : q ∣ 3 * t := Dvd.dvd.mul_left hqt 3
    have hq3 : q ≠ 3 := by rintro rfl; exact ht3 hqt
    exact ⟨q, hq, five_le q hq (not_two q hqn) hq3, hqn⟩
  · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
    have hq3 : q ≠ 3 := by rintro rfl; exact h3n hqn
    exact ⟨q, hq, five_le q hq (not_two q hqn) hq3, hqn⟩

/-! ## Main results -/

/-- **Strong form.** An odd suffix minimum of Euler's totient (an odd `n` with
`φ n ≤ φ m` for every `m > n`) is `1` or `3`. -/
theorem odd_isSuffixMin (n : ℕ) (hn : Odd n) (h : IsSuffixMin n) : n = 1 ∨ n = 3 := by
  by_contra hne
  have h1 : n ≠ 1 := fun e => hne (Or.inl e)
  have h3 : n ≠ 3 := fun e => hne (Or.inr e)
  by_cases h9 : 9 ∣ n
  · obtain ⟨s, rfl⟩ := h9
    have hs : Odd s := (Nat.odd_mul.mp hn).2
    have hlt : 9 * s < 12 * s := by have hs0 := hs.pos; omega
    exact absurd (h (12 * s) hlt) (Nat.not_le.mpr (totient_twelve_mul_lt s hs))
  · obtain ⟨q, hq, hq5, r, rfl⟩ := exists_prime_five_le_dvd n hn h9 h1 h3
    have hr : Odd r := (Nat.odd_mul.mp hn).2
    obtain ⟨hlt, hphi⟩ := totient_mul_succ_lt q r hq hq5 hr
    exact absurd (h (r * (q + 1)) hlt) (Nat.not_le.mpr hphi)

/-- **Perry's conjecture (A219930, comment 2, Jon Perry, Dec 01 2012),
first sentence.** Verbatim: "Conjecture: Except for 1 and 3, all members of the
sequence are even." Every term of A219930 other than `1` and `3` is even. -/
theorem even_of_isTerm (n : ℕ) (h : IsTerm n) (h1 : n ≠ 1) (h3 : n ≠ 3) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact absurd (odd_isSuffixMin n ho h.2.1) (by omega)

/-- **Perry's conjecture (A219930, comment 2), second sentence, read as being
about odd terms other than `1` and `3`.** Verbatim: "If n is odd, it cannot be
squarefree." Literally false at `n = 3`; on the other odd terms it holds
vacuously, since by `even_of_isTerm` there are none. -/
theorem not_squarefree_of_isTerm_of_odd (n : ℕ) (h : IsTerm n) (hn : Odd n) (h1 : n ≠ 1)
    (h3 : n ≠ 3) : ¬ Squarefree n :=
  absurd (even_of_isTerm n h h1 h3) (Nat.not_even_iff_odd.mpr hn)

/-- The literal second sentence fails at `n = 3`: `3` is an odd, squarefree term. -/
example : IsTerm 3 ∧ Odd 3 ∧ Squarefree 3 :=
  ⟨isTerm_three, by decide, Nat.prime_three.squarefree⟩


end Candidates.A219930PhiListsValue
