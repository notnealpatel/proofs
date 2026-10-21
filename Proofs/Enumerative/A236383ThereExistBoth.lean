/-
# A236383 — Lagneau: the "x ‖ (x + n²)" square exists for every n ≥ 1

## OEIS source (retrieved with `oeis show A236383`, 2026-10-21)

```
NAME:     Smallest k such that k^2 is a concatenation of two numbers x and y
          where y = x + n^2 and x and y have the same number of digits.
TERMS:    428,453,465,381,369,358,917,421,394,452,704,716,442,833,323,380,347,
          697,8376,449,3994,407,439,431,4770,6961,391,336,3533,4277,7915,36332,
          7705,4487,3323,8869,8942,3250,4560,7632,90951,7988,4204,3606,8586,72774
COMMENT:  Conjecture: a(n) exists for all numbers n.
COMMENT:  a(1) = A030467(1).
COMMENT:  The corresponding sequence with x + n instead of x + n^2 starts with
          36363636364, 428, 8874, 5, 310, 7, 39 for n = 0,...,6, and
          a(7) > 10^70, if it exists. - _Giovanni Resta_, Jun 24 2019
```

The conjecture line is unsigned in the entry; per the triage it is due to the
entry author, Michel Lagneau (2014), and Giovanni Resta corrected the
definition in Jun 2019 (the local OEIS store carries no author field).  The Maple program splits
`k^2` (with an even number `2d` of digits) into its high half `x` and low half
`y` and tests `y - x = n^2`.

## Status

Triage: open — no proof or counterexample in the entry; the literature beyond
the entry was not searched, so novelty is not established.

This module proves the conjecture (theorem `exists_witness`), by an explicit
construction (no search, no CRT): with `u = 10^e ≡ 1 (mod 3)`,
`A = u + 1`, `B = u^2 - u + 1`, `10^(3e) + 1 = A * B`, and a residue split on
`n mod 3`, one writes down `K, α, β` with `K - n = α A`, `K + n = β B` (or the
signs swapped), so `K^2 = α β (10^(3e) + 1) + n^2`; for `u ≥ 3n + 4` the
product `x = α β` has exactly `3e` digits and so does `x + n^2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A236383ThereExistBoth

/-! ## Definition layer -/

/-- `IsWitness n k`: `k^2` is the decimal concatenation of two numbers `x` and
`y` with `y = x + n^2`, where `x` and `y` have the same number of decimal digits.
Concatenating `x` in front of `y` is `x * 10^(number of digits of y) + y`. -/
def IsWitness (n k : ℕ) : Prop :=
  ∃ x y : ℕ, (Nat.digits 10 x).length = (Nat.digits 10 y).length ∧ y = x + n ^ 2 ∧
    k ^ 2 = x * 10 ^ (Nat.digits 10 y).length + y

/-- Ground truth: `a(1) = 428`, `428^2 = 183184 = 183 ‖ 184`, `184 = 183 + 1^2`. -/
example : IsWitness 1 428 := ⟨183, 184, by norm_num, by norm_num, by norm_num⟩

/-- Ground truth: `a(2) = 453`, `453^2 = 205209 = 205 ‖ 209`, `209 = 205 + 2^2`. -/
example : IsWitness 2 453 := ⟨205, 209, by norm_num, by norm_num, by norm_num⟩

/-- Ground truth: `a(19) = 8376`, `8376^2 = 70157376 = 7015 ‖ 7376`,
`7376 = 7015 + 19^2`. -/
example : IsWitness 19 8376 := ⟨7015, 7376, by norm_num, by norm_num, by norm_num⟩

/-- Ground truth: `a(46) = 72774`, `72774^2 = 5296055076 = 52960 ‖ 55076`,
`55076 = 52960 + 46^2`. -/
example : IsWitness 46 72774 := ⟨52960, 55076, by norm_num, by norm_num, by norm_num⟩

/-! ## Digit-length bridge -/

/-- A number `x` with `10^(d-1) ≤ x < 10^d` and `0 < d` has exactly `d`
decimal digits. -/
theorem length_digits_eq_of_bounds {d x : ℕ} (hd : 0 < d) (hlo : 10 ^ (d - 1) ≤ x)
    (hhi : x < 10 ^ d) : (Nat.digits 10 x).length = d := by
  have hx : x ≠ 0 := by
    have hpos : 0 < 10 ^ (d - 1) := by positivity
    omega
  have hd' : d - 1 + 1 = d := by omega
  have hlog : Nat.log 10 x = d - 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow hlo (by rw [hd']; exact hhi)
  rw [Nat.length_digits 10 x (by norm_num) hx, hlog, hd']

/-! ## The explicit construction -/

/-- Residue `n = 3m + 1`.  With `u = 9m + 7 + 3w`, `β = 2m + 2(3m + 3 + w)`,
`α = β (u - 2) + 2`, `K = α (u + 1) + n`: then `K^2 = α β (u^3 + 1) + n^2`
and `u^3 ≤ 10 α β`, `α β + n^2 < u^3`. -/
theorem core_one (m w : ℕ) :
    ∃ K x : ℕ, K ^ 2 = x * ((9 * m + 7 + 3 * w) ^ 3 + 1) + (3 * m + 1) ^ 2 ∧
      (9 * m + 7 + 3 * w) ^ 3 ≤ 10 * x ∧ x + (3 * m + 1) ^ 2 < (9 * m + 7 + 3 * w) ^ 3 := by
  set β : ℕ := 2 * m + 2 * (3 * m + 3 + w) with hβ
  set α : ℕ := β * (9 * m + 5 + 3 * w) + 2 with hα
  refine ⟨α * (9 * m + 8 + 3 * w) + (3 * m + 1), α * β, ?_, ?_, ?_⟩
  · rw [hα, hβ]; ring
  · rw [hα, hβ]; ring_nf; nlinarith [Nat.zero_le (w * m), Nat.zero_le (w ^ 2 * m)]
  · rw [hα, hβ]; ring_nf; nlinarith [Nat.zero_le (w * m)]

/-- Residue `n = 3m + 2`.  With `u = 9m + 7 + 3w`, `β = 2m + 1 + (3m + 3 + w)`,
`α = β (u - 2) + 1`, `K = α (u + 1) + n`: then `K^2 = α β (u^3 + 1) + n^2`
and `u^3 ≤ 10 α β`, `α β + n^2 < u^3`. -/
theorem core_two (m w : ℕ) :
    ∃ K x : ℕ, K ^ 2 = x * ((9 * m + 7 + 3 * w) ^ 3 + 1) + (3 * m + 2) ^ 2 ∧
      (9 * m + 7 + 3 * w) ^ 3 ≤ 10 * x ∧ x + (3 * m + 2) ^ 2 < (9 * m + 7 + 3 * w) ^ 3 := by
  set β : ℕ := 2 * m + 1 + (3 * m + 3 + w) with hβ
  set α : ℕ := β * (9 * m + 5 + 3 * w) + 1 with hα
  refine ⟨α * (9 * m + 8 + 3 * w) + (3 * m + 2), α * β, ?_, ?_, ?_⟩
  · rw [hα, hβ]; ring
  · rw [hα, hβ]; ring_nf; nlinarith [Nat.zero_le (w * m), Nat.zero_le (w ^ 2 * m)]
  · rw [hα, hβ]; ring_nf; nlinarith [Nat.zero_le (w * m)]

/-- Residue `n = 3(m + 1)`.  With `u = 9m + 7 + 3w`, `β = u + 1 - 2(m + 1)`,
`α = β (u - 2) + 3`, `K = β (u^2 - u + 1) + n`: then `K^2 = α β (u^3 + 1) + n^2`
and `u^3 ≤ 10 α β`, `α β + n^2 < u^3`. -/
theorem core_zero (m w : ℕ) :
    ∃ K x : ℕ, K ^ 2 = x * ((9 * m + 7 + 3 * w) ^ 3 + 1) + (3 * (m + 1)) ^ 2 ∧
      (9 * m + 7 + 3 * w) ^ 3 ≤ 10 * x ∧
      x + (3 * (m + 1)) ^ 2 < (9 * m + 7 + 3 * w) ^ 3 := by
  set β : ℕ := 7 * m + 6 + 3 * w with hβ
  set α : ℕ := β * (9 * m + 5 + 3 * w) + 3 with hα
  refine ⟨β * ((9 * m + 7 + 3 * w) * (9 * m + 6 + 3 * w) + 1) + 3 * (m + 1), α * β, ?_, ?_, ?_⟩
  · rw [hα, hβ]; ring
  · rw [hα, hβ]; ring_nf; nlinarith [Nat.zero_le (w * m), Nat.zero_le (w ^ 2 * m)]
  · rw [hα, hβ]; ring_nf; nlinarith [Nat.zero_le (w * m)]

/-- Uniform core: if `u ≡ 1 (mod 3)`, `1 ≤ n` and `3n + 4 ≤ u`, then some `K`
satisfies `K^2 = x (u^3 + 1) + n^2` with `u^3 ≤ 10 x` and `x + n^2 < u^3`. -/
theorem core (n u : ℕ) (hn : 1 ≤ n) (hu : u % 3 = 1) (hbig : 3 * n + 4 ≤ u) :
    ∃ K x : ℕ, K ^ 2 = x * (u ^ 3 + 1) + n ^ 2 ∧ u ^ 3 ≤ 10 * x ∧ x + n ^ 2 < u ^ 3 := by
  obtain ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨m, hm⟩ :
      (∃ m, n = 3 * m + 1) ∨ (∃ m, n = 3 * m + 2) ∨ (∃ m, n = 3 * (m + 1)) := by
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · exact Or.inr (Or.inr ⟨n / 3 - 1, by omega⟩)
    · exact Or.inl ⟨n / 3, by omega⟩
    · exact Or.inr (Or.inl ⟨n / 3, by omega⟩)
  · obtain ⟨w, hw⟩ : ∃ w, u = 9 * m + 7 + 3 * w := ⟨(u - (9 * m + 7)) / 3, by omega⟩
    subst hm hw
    exact core_one m w
  · obtain ⟨w, hw⟩ : ∃ w, u = 9 * m + 7 + 3 * w := ⟨(u - (9 * m + 7)) / 3, by omega⟩
    subst hm hw
    exact core_two m w
  · obtain ⟨w, hw⟩ : ∃ w, u = 9 * m + 7 + 3 * w := ⟨(u - (9 * m + 7)) / 3, by omega⟩
    subst hm hw
    exact core_zero m w

/-- Numeric form (the triage's formal sketch): for `1 ≤ n` there are `k`, `d`,
`x` with `0 < d`, `k^2 = x * 10^d + (x + n^2)`, `10^(d-1) ≤ x` and
`x + n^2 < 10^d`. -/
theorem exists_bounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ k d x : ℕ, 0 < d ∧ k ^ 2 = x * 10 ^ d + (x + n ^ 2) ∧ 10 ^ (d - 1) ≤ x ∧
      x + n ^ 2 < 10 ^ d := by
  set u : ℕ := 10 ^ (n + 1) with hu_def
  have hu3 : u % 3 = 1 := by
    rw [hu_def, Nat.pow_mod]; norm_num
  have hbig : 3 * n + 4 ≤ u := by
    have hlt : n < 10 ^ n := Nat.lt_pow_self (by norm_num)
    have hpow : u = 10 * 10 ^ n := by rw [hu_def, pow_succ]; ring
    omega
  obtain ⟨K, x, hK, hlo, hhi⟩ := core n u hn hu3 hbig
  have hd : 10 ^ (3 * (n + 1)) = u ^ 3 := by rw [hu_def, ← pow_mul, mul_comm]
  have hd1 : 10 * 10 ^ (3 * (n + 1) - 1) = 10 ^ (3 * (n + 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  refine ⟨K, 3 * (n + 1), x, by omega, ?_, ?_, ?_⟩
  · rw [hd, hK]; ring
  · have h10 : 10 * 10 ^ (3 * (n + 1) - 1) ≤ 10 * x := by rw [hd1, hd]; exact hlo
    omega
  · rw [hd]; exact hhi

/-- **Lagneau's conjecture (A236383, Michel Lagneau, 2014), proved.**

Verbatim: "Conjecture: a(n) exists for all numbers n." — i.e. for every `n ≥ 1`
there is `k` such that `k^2` is the concatenation of two numbers `x` and `y`
with `y = x + n^2` and `x`, `y` having the same number of decimal digits. -/
theorem exists_witness (n : ℕ) (hn : 1 ≤ n) : ∃ k, IsWitness n k := by
  obtain ⟨k, d, x, hd, hk, hlo, hhi⟩ := exists_bounds n hn
  have hxd : (Nat.digits 10 x).length = d := length_digits_eq_of_bounds hd hlo (by omega)
  have hyd : (Nat.digits 10 (x + n ^ 2)).length = d :=
    length_digits_eq_of_bounds hd (by omega) hhi
  exact ⟨k, x, x + n ^ 2, by rw [hxd, hyd], rfl, by rw [hyd]; exact hk⟩

/-- Consequently `a(n)`, the least `k` with `IsWitness n k`, exists for every
`n ≥ 1`: there is a `k` that is a witness and no smaller `j` is. -/
theorem exists_least_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, IsWitness n k ∧ ∀ j < k, ¬ IsWitness n j := by
  classical
  have hex := exists_witness n hn
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

end Candidates.A236383ThereExistBoth
