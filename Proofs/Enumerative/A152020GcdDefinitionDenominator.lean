/-
# A152020 — Cicuttin: `a(n) = denominator((n-2)^3/n^2)`

## OEIS source (pulled with `oeis show A152020`, retrieved 2026-10-21)

```
NAME:     Denominator of 8/(9*n^2) divided by 9.
TERMS:    1,1,9,2,25,9,49,8,81,25,121,18,169,49,225,32,289,81,361,50,441,121,
          529,72,625,169,729,98,841,225,961,128,1089,289,1225,162,1369,361,1521,
          200,1681,441,1849,242,2025,529,2209,288,2401,625
KEYWORDS: nonn,mult,easy
OFFSET:   terms are indexed from n = 1 (a(1) = 1, a(2) = 1, a(3) = 9, ...)
FORMULA (the conjecture):
  Conjecture: a(n) = denominator((n-2)^3/n^2). - _Andres Cicuttin_, Sep 19 2017
FORMULA (adjacent, unproved in the entry):
  a(n) = n^2/gcd(n^2, 8). - _Andrew Howroyd_, Jul 25 2018
PROGRAM:  (PARI) a(n) = denominator(8/(9*n^2))/9 \\ _Michel Marcus_, Jun 01 2013
```

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell); tractability "trivial".  The triage phrased the target as
"`n^2/gcd(n^2, 8)` (the definition) equals the denominator of `(n-2)^3/n^2`
for all `n ≥ 1`".  Since the entry's NAME is `denominator(8/(9 n^2))/9`, this
module states the conjecture against the NAME definition (`conjecture`), proves
Howroyd's closed form (`a_eq_sq_div_gcd`), and records the triage's phrasing
separately (`den_eq_sq_div_gcd`).

## Proof

`gcd(n^2, (n-2)^3) = gcd(n^2, 8)` for every `n`, by cases on `n mod 4`
(both sides are `8, 1, 4, 1` for `n ≡ 0, 1, 2, 3`), using explicit Bézout
certificates for the coprimality of the cofactors.  The denominator of
`p/q` is `|q| / gcd(q, p)` (`Rat.den_divInt`), and `gcd(9 n^2, 8) = gcd(n^2, 8)`
because `gcd(9, 8) = 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A152020GcdDefinitionDenominator

/-- **A152020** (NAME): `a(n)` is the denominator of `8/(9 n^2)` divided by `9`
(PARI: `denominator(8/(9*n^2))/9`).  Only meaningful for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := ((8 : ℚ) / (9 * (n : ℚ) ^ 2)).den / 9

/-- Cicuttin's expression: the denominator of `(n-2)^3/n^2`, computed in `ℚ`
(so `n - 2` is a rational, not truncated, difference). -/
def cicuttin (n : ℕ) : ℕ := ((((n : ℚ) - 2) ^ 3) / (n : ℚ) ^ 2).den

/-! ## Ground truth against the listed terms -/

example : a 1 = 1 := by decide +kernel
example : a 2 = 1 := by decide +kernel
example : a 3 = 9 := by decide +kernel
example : a 4 = 2 := by decide +kernel
example : a 8 = 8 := by decide +kernel
example : a 12 = 18 := by decide +kernel
example : cicuttin 1 = 1 := by decide +kernel
example : cicuttin 2 = 1 := by decide +kernel
example : cicuttin 3 = 9 := by decide +kernel
example : cicuttin 4 = 2 := by decide +kernel
example : cicuttin 8 = 8 := by decide +kernel
example : cicuttin 12 = 18 := by decide +kernel

/-- At the excluded index `n = 0` the two sides differ (junk values). -/
example : a 0 = 0 ∧ cicuttin 0 = 1 := by decide +kernel

/-! ## The gcd computation -/

/-- `gcd(n^2, (n-2)^3) = gcd(n^2, 8)` in `ℤ`, for every natural `n`
(both equal `8, 1, 4, 1` according as `n ≡ 0, 1, 2, 3 (mod 4)`). -/
theorem gcd_sq_sub_two_cube (n : ℕ) :
    Int.gcd ((n : ℤ) ^ 2) (((n : ℤ) - 2) ^ 3) = Int.gcd ((n : ℤ) ^ 2) 8 := by
  obtain ⟨k, hk | hk | hk | hk⟩ :
      ∃ k : ℕ, n = 4 * k ∨ n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 :=
    ⟨n / 4, by omega⟩
  all_goals subst hk; push_cast
  · -- n = 4k : both gcds are 8
    have h2 : IsCoprime (2 : ℤ) (2 * (k : ℤ) - 1) := ⟨k, -1, by ring⟩
    have hk' : IsCoprime (k : ℤ) (2 * (k : ℤ) - 1) := ⟨2, -1, by ring⟩
    have hA : IsCoprime (2 * (k : ℤ) ^ 2) ((2 * (k : ℤ) - 1) ^ 3) :=
      (h2.mul_left (hk'.pow_left)).pow_right
    have hL : ((4 * (k : ℤ)) ^ 2) = 8 * (2 * (k : ℤ) ^ 2) := by ring
    have hR : ((4 * (k : ℤ)) - 2) ^ 3 = 8 * ((2 * (k : ℤ) - 1) ^ 3) := by ring
    have hR8 : Int.gcd (8 * (2 * (k : ℤ) ^ 2)) 8 = 8 := by
      rw [Int.gcd_mul_right_left]; rfl
    rw [hL, hR, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hA, hR8]
    rfl
  · -- n = 4k+1 : both gcds are 1
    have hc : IsCoprime (4 * (k : ℤ) + 1) (4 * (k : ℤ) + 1 - 2) :=
      ⟨1 - 2 * k, 2 * k, by ring⟩
    have h2 : IsCoprime (4 * (k : ℤ) + 1) 2 := ⟨1, -2 * k, by ring⟩
    have h8 : (8 : ℤ) = 2 ^ 3 := by norm_num
    rw [Int.isCoprime_iff_gcd_eq_one.mp hc.pow, h8, Int.isCoprime_iff_gcd_eq_one.mp h2.pow]
  · -- n = 4k+2 : both gcds are 4
    have h2 : IsCoprime (2 * (k : ℤ) + 1) 2 := ⟨1, -k, by ring⟩
    have hk' : IsCoprime (2 * (k : ℤ) + 1) (k : ℤ) := ⟨1, -2, by ring⟩
    have hA : IsCoprime ((2 * (k : ℤ) + 1) ^ 2) (2 ^ 4 * (k : ℤ) ^ 3) :=
      IsCoprime.pow_left ((h2.pow_right (n := 4)).mul_right (hk'.pow_right (n := 3)))
    have hB : IsCoprime ((2 * (k : ℤ) + 1) ^ 2) 2 := h2.pow_left
    have hL : ((4 * (k : ℤ) + 2) ^ 2) = 4 * (2 * (k : ℤ) + 1) ^ 2 := by ring
    have hR : ((4 * (k : ℤ) + 2) - 2) ^ 3 = 4 * (2 ^ 4 * (k : ℤ) ^ 3) := by ring
    have h8 : (8 : ℤ) = 4 * 2 := by ring
    rw [hL, hR, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hA, h8, Int.gcd_mul_left,
      Int.isCoprime_iff_gcd_eq_one.mp hB]
  · -- n = 4k+3 : both gcds are 1
    have hc : IsCoprime (4 * (k : ℤ) + 3) (4 * (k : ℤ) + 3 - 2) :=
      ⟨-2 * k, 2 * k + 1, by ring⟩
    have h2 : IsCoprime (4 * (k : ℤ) + 3) 2 := ⟨1, -2 * k - 1, by ring⟩
    have h8 : (8 : ℤ) = 2 ^ 3 := by norm_num
    rw [Int.isCoprime_iff_gcd_eq_one.mp hc.pow, h8, Int.isCoprime_iff_gcd_eq_one.mp h2.pow]

/-- The denominator of `p / q` for integers `p`, `q` with `q ≠ 0` is
`|q| / gcd(q, p)`. -/
theorem den_intCast_div_intCast (p q : ℤ) (hq : q ≠ 0) :
    ((p : ℚ) / (q : ℚ)).den = q.natAbs / Int.gcd q p := by
  rw [← Rat.divInt_eq_div, Rat.den_divInt, if_neg hq]

/-- Cicuttin's denominator in closed form: for `n ≥ 1`,
`denominator((n-2)^3/n^2) = n^2 / gcd(n^2, 8)`.  This is the triage's phrasing of
the target. -/
theorem den_eq_sq_div_gcd (n : ℕ) (hn : 1 ≤ n) :
    cicuttin n = n ^ 2 / Nat.gcd (n ^ 2) 8 := by
  have hq : ((n : ℤ) ^ 2) ≠ 0 := by positivity
  have hcast : (((n : ℚ) - 2) ^ 3) / (n : ℚ) ^ 2
      = (((((n : ℤ) - 2) ^ 3 : ℤ)) : ℚ) / ((((n : ℤ) ^ 2 : ℤ)) : ℚ) := by
    push_cast; ring
  unfold cicuttin
  rw [hcast, den_intCast_div_intCast _ _ hq, gcd_sq_sub_two_cube]
  have h8 : ((8 : ℤ)) = ((8 : ℕ) : ℤ) := rfl
  rw [h8, ← Nat.cast_pow, Int.gcd_natCast_natCast, Int.natAbs_natCast]

/-- **Howroyd's formula (A152020, Andrew Howroyd, Jul 25 2018).**  For `n ≥ 1`,
`a(n) = n^2 / gcd(n^2, 8)`. -/
theorem a_eq_sq_div_gcd (n : ℕ) (hn : 1 ≤ n) :
    a n = n ^ 2 / Nat.gcd (n ^ 2) 8 := by
  have hq : (9 * (n : ℤ) ^ 2) ≠ 0 := by positivity
  have hcast : (8 : ℚ) / (9 * (n : ℚ) ^ 2)
      = (((8 : ℤ)) : ℚ) / (((9 * (n : ℤ) ^ 2 : ℤ)) : ℚ) := by
    push_cast; ring
  unfold a
  rw [hcast, den_intCast_div_intCast _ _ hq]
  have hnat : (9 * (n : ℤ) ^ 2) = ((9 * n ^ 2 : ℕ) : ℤ) := by push_cast; ring
  have h8 : ((8 : ℤ)) = ((8 : ℕ) : ℤ) := rfl
  have hcop : Nat.Coprime 9 8 := by norm_num
  rw [hnat, h8, Int.gcd_natCast_natCast, Int.natAbs_natCast,
    Nat.Coprime.gcd_mul_left_cancel _ hcop,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), Nat.mul_div_cancel_left _ (by norm_num)]

/-! ## The conjecture -/

/-- **Cicuttin's conjecture (A152020, Andres Cicuttin, Sep 19 2017).**

Verbatim: "Conjecture: a(n) = denominator((n-2)^3/n^2)."

Here `a(n)` is the entry's NAME, `denominator(8/(9 n^2))/9`, and the right side
is the denominator of the rational number `(n-2)^3/n^2`.  The guard `1 ≤ n` is
the entry's offset; at `n = 0` both sides are junk (`a 0 = 0`, `cicuttin 0 = 1`). -/
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : a n = cicuttin n := by
  rw [a_eq_sq_div_gcd n hn, den_eq_sq_div_gcd n hn]

end Candidates.A152020GcdDefinitionDenominator
