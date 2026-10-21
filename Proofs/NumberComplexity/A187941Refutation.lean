/-
# A187941 — the `a(n) = 2^n` characterization fails at `n = 0`

## OEIS source (retrieved with `oeis show A187941` and the live entry, 2026-10-21)

```
NAME:     Least number with exactly n even divisors.
OFFSET:   0
AUTHOR:   Juri-Stepan Gerasimov, Mar 16 2011
TERMS:    1,2,4,8,12,32,24,128,48,72,96,2048,120,8192,384,288,240,131072,360,
          524288,480,1152,6144,8388608,720,2592,24576,1800,1920,536870912,...
COMMENT:  The only odd term in the sequence is 1, having zero even divisors.
          All larger odd numbers also have zero even divisors.
COMMENT (the conjecture; unsigned, hence the entry author's, Mar 16 2011):
  Conjecture: a(n) = 2^n only if n is prime or if n = 1.
COMMENT:  If the prime factorization of a number is 2^k p1^e1...pr^er, then the
          number of even divisors is k*(e1+1)...(er+1). [...] It is obvious that
          if n is prime, then a(n) = 2^n. [...] - _T. D. Noe_, Mar 16 2011
```

No later comment retracts or restricts the conjecture.

## Status

Refuted here, literally, at the offset `n = 0`: `a(0) = 1 = 2^0`, and `0` is
neither prime nor `1`.  The intended statement (for `n ≥ 1`) is true and is
proved below as `prime_or_eq_one_of_a_eq_two_pow`: if `n = p * q` with
`p, q ≥ 2`, then `2^p * 3^(q-1)` has exactly `n` even divisors and is smaller
than `2^n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A187941Refutation

open Finset

/-- The number of even divisors of `m` (zero for `m = 0`, whose `divisors` is
empty, and for odd `m`). -/
def evenDivisorCount (m : ℕ) : ℕ := #((Nat.divisors m).filter Even)

/-- Ground truth for `evenDivisorCount`: the even divisors of `12` are
`2, 4, 6, 12`, and odd numbers have none. -/
example : evenDivisorCount 12 = 4 ∧ evenDivisorCount 1 = 0 ∧ evenDivisorCount 9 = 0 ∧
    evenDivisorCount 24 = 6 := by
  decide

/-- The even divisors of `2 * m` are exactly the doubles of the divisors of
`m`, so `2 * m` has as many even divisors as `m` has divisors. -/
theorem evenDivisorCount_two_mul {m : ℕ} (hm : m ≠ 0) :
    evenDivisorCount (2 * m) = #(Nat.divisors m) := by
  have hset : (Nat.divisors (2 * m)).filter Even = (Nat.divisors m).image (2 * ·) := by
    ext x
    simp only [mem_filter, Nat.mem_divisors, mem_image]
    constructor
    · rintro ⟨⟨hdvd, -⟩, ⟨d, rfl⟩⟩
      refine ⟨d, ⟨?_, hm⟩, by ring⟩
      have h2 : 2 * d ∣ 2 * m := by rwa [two_mul]
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    · rintro ⟨d, ⟨hdvd, -⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left 2 hdvd, by positivity⟩, even_two_mul d⟩
  rw [evenDivisorCount, hset, card_image_of_injective _ (mul_right_injective₀ two_ne_zero)]

/-- A prime power `p ^ k` has `k + 1` divisors. -/
theorem card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    #(Nat.divisors (p ^ k)) = k + 1 := by
  rw [Nat.divisors_prime_pow hp, card_map, card_range]

/-- `2 ^ i * 3 ^ j` has `(i + 1) * (j + 1)` divisors. -/
theorem card_divisors_two_pow_mul_three_pow (i j : ℕ) :
    #(Nat.divisors (2 ^ i * 3 ^ j)) = (i + 1) * (j + 1) := by
  have hcop : Nat.Coprime (2 ^ i) (3 ^ j) := Nat.Coprime.pow i j (by norm_num)
  rw [Nat.Coprime.card_divisors_mul hcop, card_divisors_prime_pow Nat.prime_two,
    card_divisors_prime_pow Nat.prime_three]

/-- `2 ^ (k + 1)` has exactly `k + 1` even divisors. -/
theorem evenDivisorCount_two_pow_succ (k : ℕ) : evenDivisorCount (2 ^ (k + 1)) = k + 1 := by
  rw [pow_succ', evenDivisorCount_two_mul (by positivity),
    card_divisors_prime_pow Nat.prime_two]

/-- Every `n` is the even-divisor count of some positive integer: `1` for
`n = 0`, and `2 ^ n` for `n ≥ 1`. -/
theorem exists_evenDivisorCount_eq (n : ℕ) : ∃ m, 0 < m ∧ evenDivisorCount m = n := by
  rcases n with _ | k
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨2 ^ (k + 1), by positivity, evenDivisorCount_two_pow_succ k⟩

/-- **A187941.** `a n` is the least positive integer with exactly `n` even
divisors. -/
def a (n : ℕ) : ℕ := Nat.find (exists_evenDivisorCount_eq n)

/-- `a n = m` iff `m` is positive with `n` even divisors and no smaller
positive integer has `n` even divisors. -/
theorem a_eq_iff (n m : ℕ) :
    a n = m ↔ (0 < m ∧ evenDivisorCount m = n) ∧
      ∀ k < m, ¬ (0 < k ∧ evenDivisorCount k = n) :=
  Nat.find_eq_iff (exists_evenDivisorCount_eq n)

/-! ## Ground truth against the listed terms -/

example : a 0 = 1 := (a_eq_iff 0 1).2 (by decide)
example : a 1 = 2 := (a_eq_iff 1 2).2 (by decide)
example : a 2 = 4 := (a_eq_iff 2 4).2 (by decide)
example : a 3 = 8 := (a_eq_iff 3 8).2 (by decide)
example : a 4 = 12 := (a_eq_iff 4 12).2 (by decide)
example : a 5 = 32 := (a_eq_iff 5 32).2 (by decide)
example : a 6 = 24 := (a_eq_iff 6 24).2 (by decide)
example : a 8 = 48 := (a_eq_iff 8 48).2 (by decide)
example : a 9 = 72 := (a_eq_iff 9 72).2 (by decide)

/-! ## The conjecture -/

/-- **Conjecture in A187941 (Mar 16 2011).**
Verbatim: "Conjecture: a(n) = 2^n only if n is prime or if n = 1."
Stated over the entry's full domain `n ≥ 0` (offset `0`). -/
def Conjecture : Prop := ∀ n : ℕ, a n = 2 ^ n → n.Prime ∨ n = 1

/-- `a 0 = 1 = 2 ^ 0`: the number `1` has no even divisors. -/
theorem a_zero : a 0 = 2 ^ 0 := (a_eq_iff 0 1).2 (by decide)

/-- **Refutation of the A187941 conjecture.**
Counterexample `n = 0`: `a(0) = 1 = 2^0` (the entry's first term, with offset
`0`), yet `0` is neither prime nor `1`.  The author presumably intended
`n ≥ 1`; that corrected form is `prime_or_eq_one_of_a_eq_two_pow`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  rcases h 0 a_zero with h0 | h0
  · exact Nat.not_prime_zero h0
  · exact zero_ne_one h0

/-! ## The intended statement -/

/-- For `p, q ≥ 2`, the number `2 ^ p * 3 ^ (q - 1)` is smaller than `2 ^ (p * q)`. -/
theorem two_pow_mul_three_pow_lt {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    2 ^ p * 3 ^ (q - 1) < 2 ^ (p * q) := by
  obtain ⟨c, rfl⟩ : ∃ c, q = c + 1 := ⟨q - 1, by omega⟩
  have hc : c ≠ 0 := by omega
  have h34 : 3 ^ c < 4 ^ c := Nat.pow_lt_pow_left (by norm_num) hc
  have h4 : 4 ^ c ≤ (2 ^ p) ^ c := by
    apply Nat.pow_le_pow_left
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  calc 2 ^ p * 3 ^ (c + 1 - 1) = 2 ^ p * 3 ^ c := by rw [Nat.add_sub_cancel]
    _ < 2 ^ p * (2 ^ p) ^ c := Nat.mul_lt_mul_of_pos_left (h34.trans_le h4) (by positivity)
    _ = 2 ^ (p * (c + 1)) := by rw [← pow_mul, ← pow_add, mul_add, mul_one, add_comm]

/-- For `p, q ≥ 1`, the number `2 ^ p * 3 ^ (q - 1)` has exactly `p * q` even
divisors. -/
theorem evenDivisorCount_two_pow_mul_three_pow {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    evenDivisorCount (2 ^ p * 3 ^ (q - 1)) = p * q := by
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ', mul_assoc, evenDivisorCount_two_mul (by positivity),
    card_divisors_two_pow_mul_three_pow]

/-- **The intended A187941 statement (`n ≥ 1`).** If the least positive
integer with exactly `n` even divisors is `2 ^ n`, then `n` is prime or
`n = 1`.  For composite `n = p * q` the number `2 ^ p * 3 ^ (q - 1)` beats
`2 ^ n`. -/
theorem prime_or_eq_one_of_a_eq_two_pow {n : ℕ} (hn : 1 ≤ n) (ha : a n = 2 ^ n) :
    n.Prime ∨ n = 1 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnp, hn1⟩ := hcon
  have hn2 : 2 ≤ n := by omega
  obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
  have hpp : p.Prime := hpdef ▸ Nat.minFac_prime (by omega)
  have hp2 : 2 ≤ p := hpp.two_le
  have hplt : p < n := hpdef ▸ (Nat.not_prime_iff_minFac_lt hn2).1 hnp
  obtain ⟨q, hnpq⟩ : p ∣ n := hpdef ▸ Nat.minFac_dvd n
  have hq2 : 2 ≤ q := by
    rcases q with _ | _ | q
    · rw [Nat.mul_zero] at hnpq
      omega
    · rw [Nat.mul_one] at hnpq
      omega
    · omega
  have hwit : 0 < 2 ^ p * 3 ^ (q - 1) ∧ evenDivisorCount (2 ^ p * 3 ^ (q - 1)) = n := by
    refine ⟨by positivity, ?_⟩
    rw [hnpq]
    exact evenDivisorCount_two_pow_mul_three_pow (by omega) (by omega)
  have hle : a n ≤ 2 ^ p * 3 ^ (q - 1) := Nat.find_min' (exists_evenDivisorCount_eq n) hwit
  have hlt : 2 ^ p * 3 ^ (q - 1) < 2 ^ n := by
    rw [hnpq]
    exact two_pow_mul_three_pow_lt hp2 hq2
  omega

end Candidates.A187941Refutation
