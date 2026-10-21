/-
# A081725 — refutation of "a(n) = A065560(n) + n - prime(n) > 0"

## OEIS source (retrieved with `oeis show A081725` / `oeis show A065560`, 2026-10-21)

```
A081725
NAME:     a(n) = A065560(n) + n - prime(n).
TERMS:    1,2,4,3,5,5,7,7,6,8,15,7,10,10,9,8,11,10,11,14,13,14,13,11,12,15,16,
          20,21,13,14,14,17,13,16,16,16,17,17,17,20,16,20,22,26,19,13,15,19,21, ...
          (offset 2: a(2) = 1)
COMMENT (the conjecture; no author or date is attached to it in the entry):
  Conjecture: a(n) > 0.
COMMENT (later):
  The conjecture is false; a(709) = -14 is the first nonpositive term.
  - _Paolo Xausa_, Nov 11 2025

A065560
NAME:     a(n) is the smallest integer k such that
          floor((1+1/n)^(k+1))/floor((1+1/n)^k) = 1+1/n.
TERMS:    2,4,7,9,12,15,18,21,25,28,40,35,39,42,46,50,54,58,62,66, ...
          (offset 2: a(2) = 2)
COMMENT:  Conjecture: a(n)+n > prime(n).
COMMENT:  The above conjecture is false. The first counterexample occurs at
          n = 709: a(709) + 709 = 4658 + 709 = 5367 < prime(709) = 5381
          (see A081725). - _Paolo Xausa_, Nov 11 2025
```

## Status

The entry itself already records the refutation (Xausa, Nov 2025).  This module
kernel-checks it: `A065560(709) = 4658` and `prime(709) = 5381`, so
`A081725(709) = 4658 + 709 - 5381 = -14 < 0`.

Independent recomputation (Python, exact integer arithmetic, 2026-10-21)
reproduced the listed terms of both entries and found no nonpositive term of
A081725 for `2 ≤ n < 709`.

## Definition choices

* `k` ranges over `ℕ`: for negative `k` the floor `⌊(1+1/n)^k⌋` is `0` and the
  quotient is undefined, so the entry's "integer k" is a natural number.  For
  `n ≥ 2` the value `k = 0` never qualifies (the quotient is `⌊1+1/n⌋ / 1 = 1`).
* `A065560(n)` is not known to exist for every `n`, so it is expressed as the
  relation `IsA065560 n k` ("`k` is the least witness") rather than a total
  function; the conjecture quantifies over every such `k`.  This makes the
  conjecture *weaker* (it asserts nothing where no witness exists), hence the
  refutation stronger.
* `prime(n)` (1-indexed, `prime(1) = 2`) is `Nat.nth Nat.Prime (n - 1)`; the
  subtraction is guarded by `2 ≤ n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A081725Refutation

/-! ## Definitions mirroring the entries -/

/-- The base `1 + 1/n` of A065560, as a rational number. -/
def base (n : ℕ) : ℚ := 1 + 1 / n

/-- The defining property of A065560:
`floor((1+1/n)^(k+1)) / floor((1+1/n)^k) = 1 + 1/n` (in `ℚ`). -/
def RatioProperty (n k : ℕ) : Prop :=
  ((⌊base n ^ (k + 1)⌋ : ℤ) : ℚ) / ((⌊base n ^ k⌋ : ℤ) : ℚ) = base n

/-- `IsA065560 n k`: `k` is the smallest natural number with `RatioProperty n k`,
i.e. `A065560(n) = k`. -/
def IsA065560 (n k : ℕ) : Prop :=
  IsLeast {j : ℕ | RatioProperty n j} k

/-- **The conjecture of A081725** ("Conjecture: a(n) > 0", offset 2):
for every `n ≥ 2`, `A065560(n) + n - prime(n) > 0`, where `prime(n)` is the
`n`-th prime (`prime(1) = 2`). -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, IsA065560 n k →
    0 < (k : ℤ) + (n : ℤ) - (Nat.nth Nat.Prime (n - 1) : ℤ)

/-! ## Computable bridge for the floors -/

/-- The integer `⌊(n+1)^k / n^k⌋`, computed in `ℕ`. -/
def floorPow (n k : ℕ) : ℕ := (n + 1) ^ k / n ^ k

/-- For `n ≥ 1`, `⌊(1+1/n)^k⌋ = (n+1)^k / n^k` (natural-number division). -/
theorem floor_base_pow {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ⌊base n ^ k⌋ = (floorPow n k : ℤ) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb : base n ^ k = (((n + 1) ^ k : ℕ) : ℚ) / ((n ^ k : ℕ) : ℚ) := by
    rw [base, Nat.cast_pow, Nat.cast_pow, ← div_pow]
    congr 1
    field_simp
    push_cast
    ring
  rw [hb, Rat.floor_natCast_div_natCast, floorPow]
  push_cast
  rfl

/-- `floorPow n k ≥ 1`, since `(n+1)^k ≥ n^k > 0`. -/
theorem floorPow_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < floorPow n k := by
  unfold floorPow
  apply Nat.div_pos
  · exact Nat.pow_le_pow_left (Nat.le_succ n) k
  · positivity

/-- For `n ≥ 1`, the A065560 property is the integer identity
`floorPow n (k+1) * n = floorPow n k * (n+1)`. -/
theorem ratioProperty_iff {n : ℕ} (hn : 0 < n) (k : ℕ) :
    RatioProperty n k ↔ floorPow n (k + 1) * n = floorPow n k * (n + 1) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hF : ((floorPow n k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (floorPow_pos hn k).ne'
  have hbase : base n = ((n + 1 : ℕ) : ℚ) / (n : ℚ) := by
    rw [base]; field_simp; push_cast; ring
  rw [RatioProperty, floor_base_pow hn, floor_base_pow hn, hbase, Int.cast_natCast,
    Int.cast_natCast, div_eq_div_iff hF hn']
  norm_cast
  rw [Nat.mul_comm (n + 1)]

/-- Boolean checker: `noRatioBelow n m = true` iff the A065560 identity fails
for every `k < m`. -/
def noRatioBelow (n : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => (floorPow n (m + 1) * n != floorPow n m * (n + 1)) && noRatioBelow n m

/-- Soundness of `noRatioBelow`. -/
theorem not_ratioProperty_of_noRatioBelow {n m : ℕ} (hn : 0 < n)
    (h : noRatioBelow n m = true) : ∀ k < m, ¬ RatioProperty n k := by
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
    simp only [noRatioBelow, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro k hk
    rw [ratioProperty_iff hn]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · rw [← ratioProperty_iff hn]; exact ih h.2 k hlt
    · subst heq; exact h.1

/-- Decision procedure for `IsA065560 n k` (for `n ≥ 1`) by direct checking. -/
theorem isA065560_of_check {n k : ℕ} (hn : 0 < n)
    (hk : floorPow n (k + 1) * n = floorPow n k * (n + 1))
    (hbelow : noRatioBelow n k = true) : IsA065560 n k := by
  refine ⟨(ratioProperty_iff hn k).mpr hk, fun j hj => ?_⟩
  by_contra hlt
  exact not_ratioProperty_of_noRatioBelow hn hbelow j (by omega) hj

/-! ## Ground truth: the first terms -/

/-- `A065560(2) = 2`. -/
example : IsA065560 2 2 := isA065560_of_check (by norm_num) (by decide) (by decide)

/-- `A065560(3) = 4`. -/
example : IsA065560 3 4 := isA065560_of_check (by norm_num) (by decide) (by decide)

/-- `A065560(12) = 40` (the first descent of A065560). -/
example : IsA065560 12 40 := isA065560_of_check (by norm_num) (by decide) (by decide)

/-- `A081725(2) = A065560(2) + 2 - prime(2) = 2 + 2 - 3 = 1`. -/
example : (2 : ℤ) + 2 - (Nat.nth Nat.Prime (2 - 1) : ℤ) = 1 := by
  rw [show 2 - 1 = 1 from rfl, Nat.nth_prime_one_eq_three]; norm_num

/-! ## `prime(709) = 5381` -/

/-- Trial-division checker: `noSmallDivisor p D = true` iff no `m` with
`2 ≤ m ≤ D` and `m < p` divides `p`. -/
def noSmallDivisor (p : ℕ) : ℕ → Bool
  | 0 => true
  | d + 1 => (decide (d + 1 < 2) || decide (p ≤ d + 1) || p % (d + 1) != 0) &&
      noSmallDivisor p d

/-- Specification of `noSmallDivisor`. -/
theorem noSmallDivisor_iff (p D : ℕ) :
    noSmallDivisor p D = true ↔ ∀ m, 2 ≤ m → m ≤ D → m < p → ¬ m ∣ p := by
  induction D with
  | zero =>
    simp only [noSmallDivisor, true_iff]
    intro m hm hmD; omega
  | succ d ih =>
    simp only [noSmallDivisor, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      bne_iff_ne, ne_eq, ih, Nat.dvd_iff_mod_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩ m hm2 hmD hmp
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmD) with hlt | heq
      · exact h2 m hm2 (by omega) hmp
      · subst heq; omega
    · intro h
      refine ⟨?_, fun m hm2 hmD hmp => h m hm2 (by omega) hmp⟩
      by_cases hd : d + 1 < 2
      · exact Or.inl (Or.inl hd)
      by_cases hp : p ≤ d + 1
      · exact Or.inl (Or.inr hp)
      exact Or.inr (h (d + 1) (by omega) le_rfl (by omega))

/-- For `p ≤ 5475 < 74²`, primality is decided by trial division up to `73`. -/
theorem prime_iff_noSmallDivisor {p : ℕ} (hp : p < 5476) :
    Nat.Prime p ↔ (2 ≤ p ∧ noSmallDivisor p 73 = true) := by
  rw [noSmallDivisor_iff]
  constructor
  · intro hpr
    refine ⟨hpr.two_le, fun m hm2 _ hmp hdvd => ?_⟩
    rcases (Nat.dvd_prime hpr).mp hdvd with h | h <;> omega
  · rintro ⟨hp2, hnd⟩
    by_contra hnp
    have hmin_sq : Nat.minFac p ^ 2 ≤ p := Nat.minFac_sq_le_self (by omega) hnp
    have hmin_le : Nat.minFac p ≤ 73 := by
      by_contra hgt
      have : 74 ^ 2 ≤ Nat.minFac p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hmin_two : 2 ≤ Nat.minFac p := (Nat.minFac_prime (by omega)).two_le
    have hmin_lt : Nat.minFac p < p := by
      rcases (Nat.minFac_le (by omega : 0 < p)).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ Nat.minFac_prime (by omega)) hnp
    exact hnd _ hmin_two hmin_le hmin_lt (Nat.minFac_dvd p)

/-- `Nat.count` only depends on the predicate below the bound. -/
theorem count_congr_of_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (N : ℕ)
    (h : ∀ m < N, (p m ↔ q m)) : Nat.count p N = Nat.count q N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Nat.count_succ, Nat.count_succ, ih fun m hm => h m (by omega)]
    have hN := h N (Nat.lt_succ_self N)
    by_cases hp : p N
    · rw [if_pos hp, if_pos (hN.mp hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hN.mpr hq))]

/-- There are exactly `708` primes below `5381`. -/
theorem count_prime_5381 : Nat.count Nat.Prime 5381 = 708 := by
  have hcongr : Nat.count Nat.Prime 5381 =
      Nat.count (fun p => 2 ≤ p ∧ noSmallDivisor p 73 = true) 5381 :=
    count_congr_of_lt 5381 fun p hp => prime_iff_noSmallDivisor (by omega)
  rw [hcongr]
  decide +kernel

/-- `prime(709) = 5381`, i.e. `Nat.nth Nat.Prime 708 = 5381`. -/
theorem nth_prime_708 : Nat.nth Nat.Prime 708 = 5381 := by
  rw [← count_prime_5381]
  exact Nat.nth_count (p := Nat.Prime) (by norm_num)

/-! ## `A065560(709) = 4658` -/

/-- `A065560(709) = 4658`. -/
theorem isA065560_709 : IsA065560 709 4658 :=
  isA065560_of_check (by norm_num) (by decide +kernel) (by decide +kernel)

/-! ## The refutation -/

/-- **A081725's conjecture "a(n) > 0" is false.**  Counterexample `n = 709`
(found by Paolo Xausa, Nov 2025): `A065560(709) = 4658` and `prime(709) = 5381`,
so `a(709) = 4658 + 709 - 5381 = -14`.  The conjecture was presumably based on
the heuristic `A065560(n) ≈ n log n ≈ prime(n)` with the observed slack `+ n`;
the true inequality fails first at `n = 709`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hpos := h 709 (by norm_num) 4658 isA065560_709
  rw [show 709 - 1 = 708 from rfl, nth_prime_708] at hpos
  norm_num at hpos

/-- The concrete value `A081725(709) = -14`. -/
theorem a081725_709 :
    (4658 : ℤ) + (709 : ℕ) - (Nat.nth Nat.Prime (709 - 1) : ℤ) = -14 := by
  rw [show 709 - 1 = 708 from rfl, nth_prime_708]
  norm_num

end Candidates.A081725Refutation
