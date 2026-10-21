/-
# A363411 — Bala: the 5-adic valuation of `Re ∏ (1 + k√-3)`

## OEIS source (retrieved 2026-10-21 with `oeis show A363411`; author line
from the live entry `https://oeis.org/A363411/internal`)

```
NAME:     a(n) = the real part of Product_{k = 0..n} 1 + k*sqrt(-3).
TERMS:    1,1,-5,-32,112,2212,-5348,-292880,276976,64180144,60400144,
          -21123205376,-68151050240,9766562233792,57568265355328,...
KEYWORDS: sign,easy
AUTHOR:   _Peter Bala_, Jun 01 2023
FORMULA (the conjecture, verbatim; no separate attribution, so it is the
         entry author's, Peter Bala, Jun 01 2023):
  Conjecture: the 5-adic valuation v_5(a(n+2)) = A079998(n) (checked up to
  n = 5000).
```

`A079998(n)` is the characteristic function of the multiples of `5`
(`1` if `5 ∣ n`, else `0`).  The entry's other conjectures (type 1/2/3
primes, `v_p(a(n)) ~ n/(p-1)`) are not covered here.

## Status

Triage: open (no proof in the entry or found in the literature).  This file
gives a complete kernel-checked proof of the stated 5-adic conjecture, with
the side fact `a(n+2) ≠ 0`.

## Proof outline

Write `z n = ∏_{k ≤ n} (1 + k w)` in `ℤ√(-3)`, so `z (n+1) = z n · (1 + (n+1) w)`.
Since `1 + (n+25) w ≡ 1 + n w (mod 25)`, induction gives
`z (n+25) ≡ 7 · z n (mod 25)` componentwise, from the base value
`z 25 ≡ 7 (mod 25)`.  Hence `a (n + 25 q) ≡ 7^q a n (mod 25)`, and `7^q` is a
unit mod `25`, so `5`- and `25`-divisibility of `a (n+2)` depend only on
`n mod 25`; the 25 residues are checked by `decide`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A363411ProdSqrtOtherwise

/-! ## Definitions -/

/-- `z n = ∏_{k=0}^{n} (1 + k·√-3)` as an element of `ℤ[√-3]`. -/
def z (n : ℕ) : ℤ√(-3) := ∏ k ∈ Finset.range (n + 1), (⟨1, k⟩ : ℤ√(-3))

/-- OEIS A363411: `a n` is the real part of `∏_{k=0}^{n} (1 + k·√-3)`. -/
def a (n : ℕ) : ℤ := (z n).re

/-! ## Ground truth against the listed terms -/

example : a 0 = 1 := by decide
example : a 1 = 1 := by decide
example : a 2 = -5 := by decide
example : a 3 = -32 := by decide
example : a 4 = 112 := by decide
example : a 5 = 2212 := by decide
example : a 6 = -5348 := by decide
example : a 7 = -292880 := by decide
example : a 8 = 276976 := by decide
example : a 9 = 64180144 := by decide
example : a 10 = 60400144 := by decide
example : a 11 = -21123205376 := by decide
example : a 14 = 57568265355328 := by decide
example : a 20 = -77896195282519949963264 := by decide

/-! ## Recurrence -/

/-- One step of the product: `z (n+1) = z n · (1 + (n+1)√-3)`. -/
theorem z_succ (n : ℕ) : z (n + 1) = z n * ⟨1, ((n + 1 : ℕ) : ℤ)⟩ := by
  rw [z, Finset.prod_range_succ]
  rfl

/-- Real part of one step: `re z (n+1) = re z n - 3 (n+1) im z n`. -/
theorem re_z_succ (n : ℕ) :
    (z (n + 1)).re = (z n).re - 3 * ((n : ℤ) + 1) * (z n).im := by
  rw [z_succ, Zsqrtd.re_mul]
  push_cast
  ring

/-- Imaginary part of one step: `im z (n+1) = im z n + (n+1) re z n`. -/
theorem im_z_succ (n : ℕ) :
    (z (n + 1)).im = (z n).im + ((n : ℤ) + 1) * (z n).re := by
  rw [z_succ, Zsqrtd.im_mul]
  push_cast
  ring

/-! ## Periodicity modulo 25 -/

/-- Base case: `z 25 ≡ 7 (mod 25)` componentwise (finite computation). -/
theorem z_twentyfive_modEq :
    (25 : ℤ) ∣ (z 25).re - 7 ∧ (25 : ℤ) ∣ (z 25).im := by
  decide

/-- Block periodicity: `z (n+25) ≡ 7 · z n (mod 25)` componentwise. -/
theorem z_add_twentyfive (n : ℕ) :
    (25 : ℤ) ∣ (z (n + 25)).re - 7 * (z n).re ∧
      (25 : ℤ) ∣ (z (n + 25)).im - 7 * (z n).im := by
  induction n with
  | zero =>
    have hz0re : (z 0).re = 1 := by decide
    have hz0im : (z 0).im = 0 := by decide
    rw [hz0re, hz0im]
    simpa using z_twentyfive_modEq
  | succ n ih =>
    obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := ih
    have hre := re_z_succ (n + 25)
    have him := im_z_succ (n + 25)
    have hre' := re_z_succ n
    have him' := im_z_succ n
    rw [show n + 1 + 25 = n + 25 + 1 by omega]
    push_cast at hre him
    constructor
    · refine ⟨A - 3 * ((n : ℤ) + 1) * B - 3 * (z (n + 25)).im, ?_⟩
      rw [hre, hre']
      linear_combination hA - 3 * ((n : ℤ) + 1) * hB
    · refine ⟨B + ((n : ℤ) + 1) * A + (z (n + 25)).re, ?_⟩
      rw [him, him']
      linear_combination hB + ((n : ℤ) + 1) * hA

/-- Iterated periodicity: `a (n + 25 q) ≡ 7^q · a n (mod 25)`. -/
theorem a_add_mul_twentyfive (n q : ℕ) :
    (25 : ℤ) ∣ a (n + 25 * q) - 7 ^ q * a n := by
  suffices h : (25 : ℤ) ∣ (z (n + 25 * q)).re - 7 ^ q * (z n).re ∧
      (25 : ℤ) ∣ (z (n + 25 * q)).im - 7 ^ q * (z n).im from h.1
  induction q with
  | zero => simp
  | succ q ih =>
    obtain ⟨hre, him⟩ := ih
    obtain ⟨hre1, him1⟩ := z_add_twentyfive (n + 25 * q)
    rw [show n + 25 * (q + 1) = n + 25 * q + 25 by ring]
    constructor
    · have h7 : (25 : ℤ) ∣ 7 * ((z (n + 25 * q)).re - 7 ^ q * (z n).re) :=
        dvd_mul_of_dvd_right hre 7
      have hsum := dvd_add hre1 h7
      rw [show (z (n + 25 * q + 25)).re - 7 ^ (q + 1) * (z n).re =
          (z (n + 25 * q + 25)).re - 7 * (z (n + 25 * q)).re +
            7 * ((z (n + 25 * q)).re - 7 ^ q * (z n).re) by ring]
      exact hsum
    · have h7 : (25 : ℤ) ∣ 7 * ((z (n + 25 * q)).im - 7 ^ q * (z n).im) :=
        dvd_mul_of_dvd_right him 7
      have hsum := dvd_add him1 h7
      rw [show (z (n + 25 * q + 25)).im - 7 ^ (q + 1) * (z n).im =
          (z (n + 25 * q + 25)).im - 7 * (z (n + 25 * q)).im +
            7 * ((z (n + 25 * q)).im - 7 ^ q * (z n).im) by ring]
      exact hsum

/-! ## Residue transfer -/

/-- `7^q` is coprime to `25`. -/
theorem isCoprime_twentyfive_seven_pow (q : ℕ) : IsCoprime (25 : ℤ) (7 ^ q) := by
  have h : IsCoprime (25 : ℤ) 7 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  exact h.pow_right

/-- If `25 ∣ x - u·y` with `u` coprime to `25`, then `d ∣ x ↔ d ∣ y` for
`d ∣ 25`. -/
theorem dvd_iff_of_modEq_unit {x y u d : ℤ} (hd : d ∣ 25) (hu : IsCoprime (25 : ℤ) u)
    (h : (25 : ℤ) ∣ x - u * y) : d ∣ x ↔ d ∣ y := by
  have hdu : IsCoprime d u := hu.of_isCoprime_of_dvd_left hd
  have hxy : d ∣ x - u * y := hd.trans h
  constructor
  · intro hx
    have huy : d ∣ u * y := by
      have h2 := dvd_sub hx hxy
      rwa [sub_sub_cancel] at h2
    exact hdu.dvd_of_dvd_mul_left huy
  · intro hy
    have huy : d ∣ u * y := dvd_mul_of_dvd_right hy u
    have h2 := dvd_add hxy huy
    rwa [sub_add_cancel] at h2

/-- The 25 base residues: for `r < 25`, if `5 ∣ r` then `5 ∣ a (r+2)` and
`25 ∤ a (r+2)`; otherwise `5 ∤ a (r+2)` (finite computation). -/
theorem base_residues :
    ∀ r < 25, (5 ∣ r → (5 : ℤ) ∣ a (r + 2) ∧ ¬ (25 : ℤ) ∣ a (r + 2)) ∧
      (¬ 5 ∣ r → ¬ (5 : ℤ) ∣ a (r + 2)) := by
  decide

/-- Divisibility pattern of `a (n+2)` by `5` and `25`, for every `n`. -/
theorem dvd_pattern (n : ℕ) :
    (5 ∣ n → (5 : ℤ) ∣ a (n + 2) ∧ ¬ (25 : ℤ) ∣ a (n + 2)) ∧
      (¬ 5 ∣ n → ¬ (5 : ℤ) ∣ a (n + 2)) := by
  set r := n % 25 with hr
  set q := n / 25 with hq
  have hn : n + 2 = (r + 2) + 25 * q := by omega
  have hr25 : r < 25 := Nat.mod_lt n (by norm_num)
  have h5 : 5 ∣ n ↔ 5 ∣ r := by omega
  have hmod := a_add_mul_twentyfive (r + 2) q
  rw [← hn] at hmod
  have hcop := isCoprime_twentyfive_seven_pow q
  have e5 : (5 : ℤ) ∣ a (n + 2) ↔ (5 : ℤ) ∣ a (r + 2) :=
    dvd_iff_of_modEq_unit (by norm_num) hcop hmod
  have e25 : (25 : ℤ) ∣ a (n + 2) ↔ (25 : ℤ) ∣ a (r + 2) :=
    dvd_iff_of_modEq_unit (dvd_refl _) hcop hmod
  obtain ⟨hb1, hb2⟩ := base_residues r hr25
  rw [h5, e5, e25]
  exact ⟨hb1, hb2⟩

/-! ## The conjecture -/

/-- **Bala's conjecture (A363411, Peter Bala, Jun 01 2023), proved.**

Verbatim: "Conjecture: the 5-adic valuation v_5(a(n+2)) = A079998(n)
(checked up to n = 5000)."  Here `A079998(n) = 1` if `5 ∣ n` and `0`
otherwise.  The statement also records `a (n+2) ≠ 0`, so the valuation is
not the junk value `padicValInt 5 0 = 0`. -/
theorem a_add_two_ne_zero_and_padicValInt_five (n : ℕ) :
    a (n + 2) ≠ 0 ∧ padicValInt 5 (a (n + 2)) = if 5 ∣ n then 1 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h1, h2⟩ := dvd_pattern n
  by_cases h5 : 5 ∣ n
  · obtain ⟨hd5, hnd25⟩ := h1 h5
    have hne : a (n + 2) ≠ 0 := by
      rintro h0
      exact hnd25 (h0 ▸ dvd_zero _)
    refine ⟨hne, ?_⟩
    rw [if_pos h5]
    have hge : 1 ≤ padicValInt 5 (a (n + 2)) := by
      have hor := (padicValInt_dvd_iff (p := 5) 1 (a (n + 2))).1 (by simpa using hd5)
      exact hor.resolve_left hne
    have hlt : ¬ 2 ≤ padicValInt 5 (a (n + 2)) := by
      intro h2le
      have hpow := (padicValInt_dvd_iff (p := 5) 2 (a (n + 2))).2 (Or.inr h2le)
      norm_num at hpow
      exact hnd25 hpow
    omega
  · have hnd := h2 h5
    have hne : a (n + 2) ≠ 0 := by
      rintro h0
      exact hnd (h0 ▸ dvd_zero _)
    refine ⟨hne, ?_⟩
    rw [if_neg h5]
    exact padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hnd)

end Candidates.A363411ProdSqrtOtherwise
