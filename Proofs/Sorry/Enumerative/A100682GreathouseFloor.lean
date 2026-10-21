/-
# A100682 — Greathouse: floor identity with finite exceptions (refuted)

## OEIS source (pulled with `oeis show A100682`, retrieved 2026-10-21)

```
NAME:     Floor of 4th root of pentatope numbers.
TERMS:    0,1,1,1,2,2,3,3,4,4,5,5,6,6,6,7,7,8,8,9,9,10,10,11,11,11,12,12,13,
          13,14,14,15,15,16,16,16,17,17,18,18,19,19,20,20,21,21,21,22,22,23,
          23,24,24,25,25,25,26,26,27,27,28,28,29,29,30,30,30,31,31
FORMULA:  a(n) = floor((A000332(n+3))^(1/4)) = floor(Ptop(n)^(1/4))
          = floor(C(n+3, 4)^1/4) = floor((n * (n+1) * (n+2) * (n+3)/4!)^(1/4)).
PROGRAM:  (PARI) a(n)=sqrtnint(binomial(n+3,4),4)
COMMENT (the conjecture):
  Conjecture: a(n) = floor((n - 3/2)/24^(1/4)) for n not in
  {0, 1, 6, 17, 2403, 5318}. - _Charles R Greathouse IV_, May 01 2012
```

## Offset

The entry now has offset 0 with `a(n) = floor(C(n+3,4)^(1/4))`.  The comment
was written for the older indexing `a(m) = floor(C(m,4)^(1/4))`, `m = n + 3`
(read literally at the current offset it fails for every large `n`, since
`a(n) ≈ (n + 3/2)/24^(1/4)`).  In the current offset the conjecture reads

  `a(n) = floor((n + 3/2)/24^(1/4))` for `n ∉ {3, 14, 2400, 5315}`.

Both readings are stated and refuted below.

## Status

Triage (2026-10-21): false.  An exact search over `n ≤ 3·10^9` found the
exceptions `3, 14, 2400, 5315, 634027528, 1705327315` (current offset).  The
last two are not in Greathouse's list.  Re-verified here with exact Python
integer arithmetic (`isqrt(isqrt(C(n+3,4)))` against the largest `k` with
`384 k^4 ≤ (2n+3)^4`), and an exhaustive exact check of `n < 3·10^5` found only
`3, 14, 2400, 5315`.  No literature proof or refutation of the comment was
found; the counterexamples are not recorded in the entry.

At `n = 634027528`: `a(n) = 286454272` but `floor((n + 3/2)/24^(1/4)) = 286454273`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A100682GreathouseFloor

/-! ## Definition layer -/

/-- OEIS A100682 (offset 0): `a(n) = floor(C(n+3,4)^(1/4))`, the floor of the
real fourth root of the pentatope number `C(n+3,4)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ⌊((Nat.choose (n + 3) 4 : ℕ) : ℝ) ^ (1 / 4 : ℝ)⌋₊

/-- Greathouse's right-hand side, in the current offset:
`floor((n + 3/2)/24^(1/4))`, as an integer floor. -/
noncomputable def greathouseRHS (n : ℕ) : ℤ :=
  ⌊((n : ℝ) + 3 / 2) / (24 : ℝ) ^ (1 / 4 : ℝ)⌋

/-! ## Fourth-root bridges -/

/-- For `0 ≤ x` and `0 ≤ c`: `c ≤ x^(1/4) ↔ c^4 ≤ x`. -/
theorem le_rpow_quarter_iff {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    c ≤ x ^ (1 / 4 : ℝ) ↔ c ^ 4 ≤ x := by
  have hy : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx _
  have hpow : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    rw [one_div]
    exact_mod_cast Real.rpow_inv_natCast_pow (n := 4) hx (by norm_num)
  rw [← pow_le_pow_iff_left₀ hc hy (by norm_num : (4 : ℕ) ≠ 0), hpow]

/-- For `0 ≤ x` and `0 ≤ c`: `x^(1/4) < c ↔ x < c^4`. -/
theorem rpow_quarter_lt_iff {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    x ^ (1 / 4 : ℝ) < c ↔ x < c ^ 4 := by
  rw [← not_le, le_rpow_quarter_iff hx hc, not_le]

/-- Integer fourth-root characterization of `a`: if `k^4 ≤ C(n+3,4) < (k+1)^4`
then `a n = k`. -/
theorem a_eq_of_bounds (n k : ℕ) (hlo : k ^ 4 ≤ Nat.choose (n + 3) 4)
    (hhi : Nat.choose (n + 3) 4 < (k + 1) ^ 4) : a n = k := by
  have hx : (0 : ℝ) ≤ ((Nat.choose (n + 3) 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold a
  rw [Nat.floor_eq_iff (Real.rpow_nonneg hx _)]
  constructor
  · rw [le_rpow_quarter_iff hx (Nat.cast_nonneg k)]
    exact_mod_cast hlo
  · rw [rpow_quarter_lt_iff hx (by positivity)]
    exact_mod_cast hhi

/-- Closed form of the pentatope number used for evaluation:
`24 · C(n+3,4) = n(n+1)(n+2)(n+3)`. -/
theorem choose_add_three_four (n : ℕ) :
    Nat.choose (n + 3) 4 = (n + 3) * (n + 2) * (n + 1) * n / 24 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial]
  rw [show n + 3 - 3 = n by omega, show n + 3 - 2 = n + 1 by omega,
    show n + 3 - 1 = n + 2 by omega, Nat.sub_zero]
  congr 1
  ring

/-- For `0 ≤ x` and `0 ≤ c`: `x^(1/4) ≤ c ↔ x ≤ c^4`. -/
theorem rpow_quarter_le_iff {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    x ^ (1 / 4 : ℝ) ≤ c ↔ x ≤ c ^ 4 := by
  have hy : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx _
  have hpow : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    rw [one_div]
    exact_mod_cast Real.rpow_inv_natCast_pow (n := 4) hx (by norm_num)
  rw [← pow_le_pow_iff_left₀ hy hc (by norm_num : (4 : ℕ) ≠ 0), hpow]

/-- Computable form of `a`, matching the PARI program `sqrtnint(binomial(n+3,4),4)`:
`a n = ⌊√⌊√(n(n+1)(n+2)(n+3)/24)⌋⌋`. -/
theorem a_eq_sqrt_sqrt (n : ℕ) :
    a n = Nat.sqrt (Nat.sqrt ((n + 3) * (n + 2) * (n + 1) * n / 24)) := by
  rw [← choose_add_three_four]
  set x := Nat.choose (n + 3) 4 with hx
  set k := Nat.sqrt (Nat.sqrt x) with hk
  apply a_eq_of_bounds
  · have h1 : k ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : Nat.sqrt x ^ 2 ≤ x := Nat.sqrt_le' _
    calc k ^ 4 = (k ^ 2) ^ 2 := by ring
      _ ≤ Nat.sqrt x ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ x := h2
  · have h1 : Nat.sqrt x < (k + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h2 : x < (Nat.sqrt x + 1) ^ 2 := Nat.lt_succ_sqrt' _
    calc x < (Nat.sqrt x + 1) ^ 2 := h2
      _ ≤ ((k + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (k + 1) ^ 4 := by ring

/-- Ground truth: the first 70 listed terms of A100682 (offset 0). -/
example : (List.range 70).map a =
    [0, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11,
      11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20,
      21, 21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29,
      30, 30, 30, 31, 31] := by
  rw [show a = fun n => Nat.sqrt (Nat.sqrt ((n + 3) * (n + 2) * (n + 1) * n / 24)) from
    funext a_eq_sqrt_sqrt]
  decide +kernel

/-- Real form of Greathouse's comparison: for `0 ≤ y` and `0 < c`,
`c ≤ y / 24^(1/4) ↔ 24 c^4 ≤ y^4`. -/
theorem le_div_rpow_quarter_iff {y c : ℝ} (hy : 0 ≤ y) (hc : 0 < c) :
    c ≤ y / (24 : ℝ) ^ (1 / 4 : ℝ) ↔ 24 * c ^ 4 ≤ y ^ 4 := by
  have h24 : (0 : ℝ) < (24 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [le_div_iff₀ h24, ← le_div_iff₀' hc,
    rpow_quarter_le_iff (by norm_num) (div_nonneg hy hc.le), div_pow,
    le_div_iff₀ (pow_pos hc 4)]

/-- Greathouse's right-hand side is nonnegative in the current offset. -/
theorem greathouseRHS_nonneg (n : ℕ) : 0 ≤ greathouseRHS n := by
  unfold greathouseRHS
  apply Int.floor_nonneg.mpr
  apply div_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)

/-- Integer form of the comparison: for `0 < k`,
`k ≤ floor((n + 3/2)/24^(1/4)) ↔ 384 k^4 ≤ (2n+3)^4`. -/
theorem le_greathouseRHS_iff (n k : ℕ) (hk : 0 < k) :
    (k : ℤ) ≤ greathouseRHS n ↔ 384 * k ^ 4 ≤ (2 * n + 3) ^ 4 := by
  unfold greathouseRHS
  rw [Int.le_floor, Int.cast_natCast,
    le_div_rpow_quarter_iff (by positivity) (by exact_mod_cast hk)]
  have hid : ((2 * (n : ℝ) + 3)) ^ 4 = 16 * ((n : ℝ) + 3 / 2) ^ 4 := by ring
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  constructor <;> intro h <;> linarith

/-- Integer fourth-root characterization of Greathouse's right-hand side:
if `384 k^4 ≤ (2n+3)^4 < 384 (k+1)^4` then `floor((n + 3/2)/24^(1/4)) = k`. -/
theorem greathouseRHS_eq_of_bounds (n k : ℕ) (hlo : 384 * k ^ 4 ≤ (2 * n + 3) ^ 4)
    (hhi : (2 * n + 3) ^ 4 < 384 * (k + 1) ^ 4) : greathouseRHS n = k := by
  apply le_antisymm
  · have hnot : ¬ ((k + 1 : ℕ) : ℤ) ≤ greathouseRHS n := by
      rw [le_greathouseRHS_iff n (k + 1) (Nat.succ_pos k)]
      omega
    push_cast at hnot
    omega
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, Nat.cast_zero]
      exact greathouseRHS_nonneg n
    · exact (le_greathouseRHS_iff n k hk).mpr hlo

/-- Ground truth for `greathouseRHS` at a listed exception: `n = 3` gives
`floor(4.5/24^(1/4)) = 2` while `a 3 = floor(15^(1/4)) = 1`. -/
example : greathouseRHS 3 = 2 ∧ a 3 = 1 :=
  ⟨greathouseRHS_eq_of_bounds 3 2 (by norm_num) (by norm_num),
    a_eq_of_bounds 3 1 (by decide) (by decide)⟩

/-- Ground truth for `greathouseRHS` at a non-exception: `n = 4` gives
`floor(5.5/24^(1/4)) = 2 = a 4`. -/
example : greathouseRHS 4 = 2 ∧ a 4 = 2 :=
  ⟨greathouseRHS_eq_of_bounds 4 2 (by norm_num) (by norm_num),
    a_eq_of_bounds 4 2 (by decide) (by decide)⟩

/-! ## Counterexamples -/

/-- New exception at `n = 634027528` (current offset): `a n = 286454272` while
`floor((n + 3/2)/24^(1/4)) = 286454273`. -/
theorem exception_634027528 :
    a 634027528 = 286454272 ∧ greathouseRHS 634027528 = 286454273 := by
  constructor
  · apply a_eq_of_bounds <;> rw [choose_add_three_four] <;> norm_num
  · exact greathouseRHS_eq_of_bounds _ _ (by norm_num) (by norm_num)

/-- New exception at `n = 1705327315` (current offset): `a n = 770468589` while
`floor((n + 3/2)/24^(1/4)) = 770468590`. -/
theorem exception_1705327315 :
    a 1705327315 = 770468589 ∧ greathouseRHS 1705327315 = 770468590 := by
  constructor
  · apply a_eq_of_bounds <;> rw [choose_add_three_four] <;> norm_num
  · exact greathouseRHS_eq_of_bounds _ _ (by norm_num) (by norm_num)

/-! ## The conjecture, refuted -/

/-- **Greathouse's conjecture (A100682, Charles R Greathouse IV, May 01 2012)
is false**, in the current offset.

Verbatim comment: "Conjecture: a(n) = floor((n - 3/2)/24^(1/4)) for n not in
{0, 1, 6, 17, 2403, 5318}."  Shifted to the entry's current offset 0
(`a(n) = floor(C(n+3,4)^(1/4))`), the claim is
`a(n) = floor((n + 3/2)/24^(1/4))` for all `n ∉ {3, 14, 2400, 5315}`.
The value `n = 634027528` is a further exception. -/
theorem greathouse_conjecture_false :
    ¬ ∀ n : ℕ, n ∉ ({3, 14, 2400, 5315} : Finset ℕ) →
      (a n : ℤ) = ⌊((n : ℝ) + 3 / 2) / (24 : ℝ) ^ (1 / 4 : ℝ)⌋ := by
  intro H
  have hN : (634027528 : ℕ) ∉ ({3, 14, 2400, 5315} : Finset ℕ) := by decide
  have h := H 634027528 hN
  change (a 634027528 : ℤ) = greathouseRHS 634027528 at h
  rw [exception_634027528.1, exception_634027528.2] at h
  norm_num at h

/-- **Greathouse's conjecture in its original indexing is false.**

With `b(m) = floor(C(m,4)^(1/4))` (the entry's former indexing, `m = n + 3`,
so `m ≥ 3`), the verbatim claim `b(m) = floor((m - 3/2)/24^(1/4))` for
`m ∉ {0, 1, 6, 17, 2403, 5318}` fails at `m = 634027531`. -/
theorem greathouse_conjecture_false_original_offset :
    ¬ ∀ m : ℕ, 3 ≤ m → m ∉ ({0, 1, 6, 17, 2403, 5318} : Finset ℕ) →
      ((⌊((Nat.choose m 4 : ℕ) : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℕ) : ℤ) =
        ⌊((m : ℝ) - 3 / 2) / (24 : ℝ) ^ (1 / 4 : ℝ)⌋ := by
  intro H
  have hM : (634027528 + 3 : ℕ) ∉ ({0, 1, 6, 17, 2403, 5318} : Finset ℕ) := by decide
  have h := H (634027528 + 3) (by norm_num) hM
  have hshift : (((634027528 + 3 : ℕ) : ℝ) - 3 / 2) = ((634027528 : ℕ) : ℝ) + 3 / 2 := by
    push_cast
    ring
  rw [hshift] at h
  change (a 634027528 : ℤ) = greathouseRHS 634027528 at h
  rw [exception_634027528.1, exception_634027528.2] at h
  norm_num at h

end Candidates.A100682GreathouseFloor
