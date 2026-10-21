/-
# A144637 — Bala: the rescaled e.g.f. `A(6x)/18` has odd coefficients exactly at `x^(2^k)`

## OEIS source (re-pulled with `oeis show A144637`, 2026-10-21)

```
NAME:     Column 2 of triangle in A144633.
TERMS:    0,0,1,-3,11,-45,175,-315,-6265,139755,-2127125,28153125,-327452125,
          2921393475,-2998820825,-788463550875,28464750689375,-739460838241125,
          16173782241491875,-294957734383186875,3672958879661946875,
          19544468129733421875,-3601613031568517590625
KEYWORDS: sign,easy
FORMULA:  E.g.f.: B(x)^2/2 where B(x) is e.g.f. for A144636. [_Vladeta Jovovic_, Jan 24 2009]
FORMULA (From _Peter Bala_, Feb 19 2026):
  E.g.f. A(x) satisfies the algebraic equation
    2*A(x)^3 + 3*A(x)^2 + 18*(1 + x)*A(x) = 9*x^2.
  (1/18)*A(6*x) = x^2 - 6*x^3 + 33*x^4 - 162*x^5 + 630*x^6 - 972*x^7 - 14499*x^8 + ...
    appears to be an integral series and satisfies the algebraic equation
    36*y(x)^3 + 3*y(x)^2 + (1 + 6*x)*y(x) = x^2.
  Conjecture: (1/18)*6^(n)*a(n)/n! is odd iff n = 2^k for k >= 1. (End)
```

## Status

Triage: open (no proof in the entry or the literature found by the triage;
not mentioned in Fried arXiv:2607.24832).  Checked numerically for
`n ≤ 600` (2026-10-21) via the integer recurrence below; the recurrence
reproduces all 23 listed terms through `c(n) = 6^n a(n) / (18 n!)`.

## What this file proves (no `sorry`)

* `c` is the coefficient sequence of the unique power series `z` with
  `z(0) = 0` and `36 z^3 + 3 z^2 + (1 + 6x) z = x^2` (Bala's equation for
  `A(6x)/18`; substituting `A(6x) = 18 z` into
  `2A^3 + 3A^2 + 18(1+x)A = 9x^2` at `x ↦ 6x` and dividing by `324` gives it).
  Over every commutative ring, in particular `ℚ`, the unique solution with zero
  constant term has coefficients `(c n : R)` (`coeff_eq_of_equation`), so the
  series is integral, and `c` solves the equation (`map_z_equation`).
* `odd_iff`: `c n` is odd iff `n = 2^k` with `1 ≤ k` — Bala's conjecture.

Proof idea: modulo `2` the equation reads `z = x^2 + z^2`, and squaring in
characteristic `2` sends `∑ c_i x^i` to `∑ c_i x^(2i)`, so the reduction is
`∑_{k ≥ 1} x^(2^k)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A144637SumCoefficientsOdd

open Finset PowerSeries

/-! ## Definition layer -/

/-- The coefficients `c n = [x^n] z` of the unique power series `z` with `z(0) = 0`
and `36 z^3 + 3 z^2 + (1 + 6x) z = x^2`, i.e. `z = A(6x)/18` with `A` the e.g.f. of
A144637, so that `c n = 6^n a(n) / (18 n!)`.

The recursion is the coefficient form of `z = x^2 - 3 z^2 - 6 x z - 36 z^3`:
for `n + 1`, the convolution sums range over indices `< n + 1` whose sum is
`n + 1` (the omitted terms carry a factor `c 0 = 0`). -/
def c : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      (if n + 1 = 2 then 1 else 0)
        - 3 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            (if i.1 + j.1 = n + 1 then c i.1 * c j.1 else 0)
        - 6 * c n
        - 36 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            (if i.1 + j.1 + k.1 = n + 1 then c i.1 * c j.1 * c k.1 else 0)

/-- The power series `z = ∑ c n x^n ∈ ℤ⟦X⟧`, i.e. `A(6x)/18`. -/
noncomputable def z : ℤ⟦X⟧ := PowerSeries.mk c

/-- `c 0 = 0`. -/
theorem c_zero : c 0 = 0 := by rw [c]

/-- The defining recursion of `c` at `n + 1`, valued in any commutative ring. -/
theorem c_succ_cast {R : Type*} [CommRing R] (n : ℕ) :
    ((c (n + 1) : ℤ) : R) =
      (if n + 1 = 2 then 1 else 0)
        - 3 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            (if i.1 + j.1 = n + 1 then (c i.1 : R) * c j.1 else 0)
        - 6 * (c n : R)
        - 36 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            (if i.1 + j.1 + k.1 = n + 1 then (c i.1 : R) * c j.1 * c k.1 else 0) := by
  rw [c]
  push_cast
  rfl

/-! ### Ground truth against the listed terms -/

/-- `c 1 = 0`. -/
theorem c_one : c 1 = 0 := by rw [c]; simp [c_zero]
/-- `c 2 = 1`. -/
theorem c_two : c 2 = 1 := by rw [c]; simp [Fin.sum_univ_succ, c_zero, c_one]
/-- `c 3 = -6`. -/
theorem c_three : c 3 = -6 := by rw [c]; simp [Fin.sum_univ_succ, c_zero, c_one, c_two]
/-- `c 4 = 33`. -/
theorem c_four : c 4 = 33 := by
  rw [c]; simp [Fin.sum_univ_succ, c_zero, c_one, c_two, c_three]
/-- `c 5 = -162`. -/
theorem c_five : c 5 = -162 := by
  rw [c]; simp [Fin.sum_univ_succ, c_zero, c_one, c_two, c_three, c_four]
/-- `c 6 = 630`. -/
theorem c_six : c 6 = 630 := by
  rw [c]; simp [Fin.sum_univ_succ, c_zero, c_one, c_two, c_three, c_four, c_five]
/-- `c 7 = -972`. -/
theorem c_seven : c 7 = -972 := by
  rw [c]; simp [Fin.sum_univ_succ, c_zero, c_one, c_two, c_three, c_four, c_five, c_six]
/-- `c 8 = -14499`. -/
theorem c_eight : c 8 = -14499 := by
  rw [c]
  simp [Fin.sum_univ_succ, c_zero, c_one, c_two, c_three, c_four, c_five, c_six, c_seven]

/- Bala's printed expansion: `x^2 - 6x^3 + 33x^4 - 162x^5 + 630x^6 - 972x^7 - 14499x^8`. -/
example : c 2 = 1 ∧ c 3 = -6 ∧ c 4 = 33 ∧ c 5 = -162 ∧ c 6 = 630 ∧ c 7 = -972 ∧
    c 8 = -14499 :=
  ⟨c_two, c_three, c_four, c_five, c_six, c_seven, c_eight⟩

/- Against the listed terms `a(n)` of A144637: `c n = 6^n a(n) / (18 n!)`. -/
example : (c 2 : ℚ) = 6 ^ 2 * 1 / (18 * Nat.factorial 2) := by
  rw [c_two]; norm_num [Nat.factorial]
example : (c 3 : ℚ) = 6 ^ 3 * (-3) / (18 * Nat.factorial 3) := by
  rw [c_three]; norm_num [Nat.factorial]
example : (c 4 : ℚ) = 6 ^ 4 * 11 / (18 * Nat.factorial 4) := by
  rw [c_four]; norm_num [Nat.factorial]
example : (c 5 : ℚ) = 6 ^ 5 * (-45) / (18 * Nat.factorial 5) := by
  rw [c_five]; norm_num [Nat.factorial]
example : (c 6 : ℚ) = 6 ^ 6 * 175 / (18 * Nat.factorial 6) := by
  rw [c_six]; norm_num [Nat.factorial]
example : (c 7 : ℚ) = 6 ^ 7 * (-315) / (18 * Nat.factorial 7) := by
  rw [c_seven]; norm_num [Nat.factorial]
example : (c 8 : ℚ) = 6 ^ 8 * (-6265) / (18 * Nat.factorial 8) := by
  rw [c_eight]; norm_num [Nat.factorial]

/-! ## Convolution bridges -/

/-- A double sum over `Fin (m + 1)` restricted to `j + k = N` is the antidiagonal
convolution at `N`, provided `N ≤ m + 1` and `f 0 = 0`. -/
theorem fin_sum_sq_eq_antidiagonal {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0)
    (m N : ℕ) (hN : N ≤ m + 1) :
    ∑ j : Fin (m + 1), ∑ k : Fin (m + 1), (if j.1 + k.1 = N then f j.1 * f k.1 else 0)
      = ∑ p ∈ antidiagonal N, f p.1 * f p.2 := by
  let h : ℕ → R := fun j => if j ≤ N then f j * f (N - j) else 0
  have hinner : ∀ j : Fin (m + 1),
      ∑ k : Fin (m + 1), (if j.1 + k.1 = N then f j.1 * f k.1 else 0) = h j.1 := by
    intro j
    obtain ⟨j, hj⟩ := j
    dsimp only [h]
    rw [Fin.sum_univ_eq_sum_range (fun k => if j + k = N then f j * f k else 0)]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [hf, if_pos (Nat.zero_le N)]
      simp only [zero_mul, ite_self, Finset.sum_const_zero]
    · by_cases hjN : j ≤ N
      · rw [if_pos hjN, Finset.sum_eq_single_of_mem (N - j) (by rw [mem_range]; omega)]
        · rw [if_pos (by omega)]
        · intro k _ hne
          rw [if_neg (by omega)]
      · rw [if_neg hjN]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg (by omega)]
  have hlast : h (m + 1) = 0 := by
    dsimp only [h]
    split_ifs with hle
    · rw [show N - (m + 1) = 0 by omega, hf, mul_zero]
    · rfl
  rw [Finset.sum_congr rfl fun j _ => hinner j, Fin.sum_univ_eq_sum_range h,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hrange : ∑ j ∈ range (m + 1), h j = ∑ j ∈ range (m + 2), h j := by
    rw [Finset.sum_range_succ _ (m + 1), hlast, add_zero]
  rw [hrange]
  have hsub : ∑ j ∈ range (N + 1), h j = ∑ j ∈ range (m + 2), h j := by
    refine Finset.sum_subset (range_subset_range.2 (show N + 1 ≤ m + 2 by omega)) ?_
    intro j hj hjN
    rw [mem_range] at hj hjN
    dsimp only [h]
    rw [if_neg (by omega)]
  rw [← hsub]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  dsimp only [h]
  rw [if_pos (by omega)]

/-- The triple sum in the definition of `c` is the coefficient of the cube. -/
theorem fin_sum_cube_eq_antidiagonal {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0)
    (m : ℕ) :
    ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), ∑ k : Fin (m + 1),
        (if i.1 + j.1 + k.1 = m + 1 then f i.1 * f j.1 * f k.1 else 0)
      = ∑ p ∈ antidiagonal (m + 1), f p.1 * ∑ q ∈ antidiagonal p.2, f q.1 * f q.2 := by
  let T : ℕ → R := fun N => ∑ q ∈ antidiagonal N, f q.1 * f q.2
  have hpt : ∀ i : Fin (m + 1),
      ∑ j : Fin (m + 1), ∑ k : Fin (m + 1),
        (if i.1 + j.1 + k.1 = m + 1 then f i.1 * f j.1 * f k.1 else 0)
      = f i.1 * T (m + 1 - i.1) := by
    intro i
    obtain ⟨i, hi⟩ := i
    dsimp only [T]
    rw [← fin_sum_sq_eq_antidiagonal f hf m (m + 1 - i) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [hf, zero_mul, ite_self]
    · by_cases hjk : j.1 + k.1 = m + 1 - i
      · rw [if_pos (by omega), if_pos hjk, mul_assoc]
      · rw [if_neg (by omega), if_neg hjk, mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hpt i, Fin.sum_univ_eq_sum_range
    (fun i => f i * T (m + 1 - i)), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ _ (m + 1)]
  have hlast : f (m + 1, m + 1 - (m + 1)).1
      * ∑ q ∈ antidiagonal (m + 1, m + 1 - (m + 1)).2, f q.1 * f q.2 = 0 := by
    rw [Nat.sub_self, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hf, mul_zero,
      mul_zero]
  rw [hlast, add_zero]

/-! ## Fidelity: `c` is the coefficient sequence of the unique solution of Bala's equation -/

/-- The `(n + 1)`-st coefficient of `36 F^3 + 3 F^2 + (1 + 6x) F` for `F = ∑ f n x^n`. -/
theorem coeff_succ_lhs {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    coeff (n + 1) (36 * (PowerSeries.mk f) ^ 3 + 3 * (PowerSeries.mk f) ^ 2
        + (1 + 6 * X) * PowerSeries.mk f)
      = 36 * ∑ p ∈ antidiagonal (n + 1), f p.1 * ∑ q ∈ antidiagonal p.2, f q.1 * f q.2
        + 3 * ∑ p ∈ antidiagonal (n + 1), f p.1 * f p.2 + f (n + 1) + 6 * f n := by
  have e : 36 * (PowerSeries.mk f) ^ 3 + 3 * (PowerSeries.mk f) ^ 2
        + (1 + 6 * X) * PowerSeries.mk f
      = C (36 : R) * (PowerSeries.mk f * (PowerSeries.mk f * PowerSeries.mk f))
        + C (3 : R) * (PowerSeries.mk f * PowerSeries.mk f) + PowerSeries.mk f
        + C (6 : R) * (X * PowerSeries.mk f) := by
    rw [map_ofNat, map_ofNat, map_ofNat]
    ring
  rw [e, map_add, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul,
    coeff_mk, coeff_mk]
  simp only [coeff_mul, coeff_mk]

/-- The constant coefficient of `36 F^3 + 3 F^2 + (1 + 6x) F` vanishes when `F(0) = 0`. -/
theorem coeff_zero_lhs {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0) :
    coeff 0 (36 * (PowerSeries.mk f) ^ 3 + 3 * (PowerSeries.mk f) ^ 2
      + (1 + 6 * X) * PowerSeries.mk f) = 0 := by
  have h0 : constantCoeff (PowerSeries.mk f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, hf]
  rw [coeff_zero_eq_constantCoeff_apply]
  simp [h0]

/-- A series `F = ∑ f n x^n` with `F(0) = 0` solves `36 F^3 + 3 F^2 + (1 + 6x) F = x^2`
iff its coefficients satisfy the recursion defining `c`. -/
theorem equation_iff_recursion {R : Type*} [CommRing R] (f : ℕ → R) (hf : f 0 = 0) :
    36 * (PowerSeries.mk f) ^ 3 + 3 * (PowerSeries.mk f) ^ 2
        + (1 + 6 * X) * PowerSeries.mk f = X ^ 2 ↔
      ∀ n : ℕ, f (n + 1) =
        (if n + 1 = 2 then 1 else 0)
          - 3 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              (if i.1 + j.1 = n + 1 then f i.1 * f j.1 else 0)
          - 6 * f n
          - 36 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
              (if i.1 + j.1 + k.1 = n + 1 then f i.1 * f j.1 * f k.1 else 0) := by
  constructor
  · intro h n
    have hn := congrArg (coeff (n + 1)) h
    rw [coeff_succ_lhs, coeff_X_pow, ← fin_sum_sq_eq_antidiagonal f hf n (n + 1) le_rfl,
      ← fin_sum_cube_eq_antidiagonal f hf n] at hn
    linear_combination hn
  · intro hrec
    ext n
    rcases n with _ | n
    · rw [coeff_zero_lhs f hf, coeff_X_pow, if_neg (by norm_num)]
    · rw [coeff_succ_lhs, coeff_X_pow, ← fin_sum_sq_eq_antidiagonal f hf n (n + 1) le_rfl,
        ← fin_sum_cube_eq_antidiagonal f hf n, hrec n]
      ring

/-- Two sequences vanishing at `0` and satisfying the recursion of `c` coincide. -/
theorem eq_of_recursion {R : Type*} [CommRing R] (f g : ℕ → R) (hf0 : f 0 = 0)
    (hg0 : g 0 = 0)
    (hf : ∀ n : ℕ, f (n + 1) =
        (if n + 1 = 2 then 1 else 0)
          - 3 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              (if i.1 + j.1 = n + 1 then f i.1 * f j.1 else 0)
          - 6 * f n
          - 36 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
              (if i.1 + j.1 + k.1 = n + 1 then f i.1 * f j.1 * f k.1 else 0))
    (hg : ∀ n : ℕ, g (n + 1) =
        (if n + 1 = 2 then 1 else 0)
          - 3 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              (if i.1 + j.1 = n + 1 then g i.1 * g j.1 else 0)
          - 6 * g n
          - 36 * ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
              (if i.1 + j.1 + k.1 = n + 1 then g i.1 * g j.1 * g k.1 else 0))
    (n : ℕ) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · rw [hf0, hg0]
  · have hfin : ∀ i : Fin (n + 1), f i.1 = g i.1 := fun i => ih i.1 (by omega)
    rw [hf n, hg n, ih n (by omega)]
    simp only [hfin]

/-- **Fidelity.** `z = ∑ c n x^n` solves Bala's equation
`36 z^3 + 3 z^2 + (1 + 6x) z = x^2` in `ℤ⟦X⟧`. -/
theorem z_equation : 36 * z ^ 3 + 3 * z ^ 2 + (1 + 6 * X) * z = X ^ 2 :=
  (equation_iff_recursion c c_zero).2 fun n => by rw [c]

/-- **Fidelity.** Over any commutative ring `R`, the image of `z` solves Bala's
equation. -/
theorem map_z_equation {R : Type*} [CommRing R] :
    36 * (PowerSeries.map (Int.castRingHom R) z) ^ 3
        + 3 * (PowerSeries.map (Int.castRingHom R) z) ^ 2
        + (1 + 6 * X) * PowerSeries.map (Int.castRingHom R) z = X ^ 2 := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom R)) z_equation
  simpa only [map_add, map_mul, map_pow, map_one, map_ofNat, PowerSeries.map_X] using hmap

/-- **Fidelity and integrality.** Over any commutative ring `R` (in particular `ℚ`), every
power series `W` with `W(0) = 0` and `36 W^3 + 3 W^2 + (1 + 6x) W = x^2` has
coefficients `coeff n W = c n`.  Hence `A(6x)/18`, the unique such series over `ℚ`,
has the integer coefficients `c n`. -/
theorem coeff_eq_of_equation {R : Type*} [CommRing R] (W : R⟦X⟧)
    (h0 : constantCoeff W = 0)
    (hW : 36 * W ^ 3 + 3 * W ^ 2 + (1 + 6 * X) * W = X ^ 2) (n : ℕ) :
    coeff n W = ((c n : ℤ) : R) := by
  let f : ℕ → R := fun m => coeff m W
  have hWf : W = PowerSeries.mk f := by
    ext m
    rw [coeff_mk]
  have hf0 : f 0 = 0 := by
    change coeff 0 W = 0
    rw [coeff_zero_eq_constantCoeff_apply, h0]
  rw [hWf] at hW
  have hfrec := (equation_iff_recursion f hf0).1 hW
  exact eq_of_recursion f (fun m => ((c m : ℤ) : R)) hf0 (by rw [c_zero, Int.cast_zero])
    hfrec (fun m => c_succ_cast m) n

/- Non-vacuity of `coeff_eq_of_equation` over `ℚ`: the image of `z` satisfies both
hypotheses. -/
example : constantCoeff (PowerSeries.map (Int.castRingHom ℚ) z) = 0 ∧
    36 * (PowerSeries.map (Int.castRingHom ℚ) z) ^ 3
        + 3 * (PowerSeries.map (Int.castRingHom ℚ) z) ^ 2
        + (1 + 6 * X) * PowerSeries.map (Int.castRingHom ℚ) z = X ^ 2 := by
  refine ⟨?_, map_z_equation⟩
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, z, coeff_mk, c_zero, eq_intCast,
    Int.cast_zero]

/-! ## Characteristic two -/

/-- In `ZMod 2`, the self-convolution at `N` is `f (N / 2)` for even `N` and `0` for
odd `N` (Frobenius: `(∑ f_i x^i)^2 = ∑ f_i x^(2i)`). -/
theorem sum_antidiagonal_mul_zmod_two (f : ℕ → ZMod 2) (N : ℕ) :
    ∑ p ∈ antidiagonal N, f p.1 * f p.2 = if Even N then f (N / 2) else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ × ℕ => p.1 = p.2)]
  have hoff : ∑ p ∈ (antidiagonal N).filter (fun p : ℕ × ℕ => ¬ p.1 = p.2), f p.1 * f p.2
      = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm (f p.2)]
      generalize f p.1 * f p.2 = x
      revert x
      decide
    · intro p hp _ hswap
      rw [mem_filter] at hp
      have h12 := congrArg Prod.snd hswap
      rw [Prod.snd_swap] at h12
      exact hp.2 h12
    · intro p hp
      rw [mem_filter, HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨by omega, fun h => hp.2 h.symm⟩
    · intro p _
      exact Prod.swap_swap p
  rw [hoff, add_zero]
  split_ifs with hN
  · obtain ⟨h, rfl⟩ := hN
    have hhalf : (h + h) / 2 = h := by omega
    rw [hhalf, Finset.sum_eq_single_of_mem (h, h)]
    · rw [← sq, ZMod.pow_card]
    · rw [mem_filter, HasAntidiagonal.mem_antidiagonal]
      exact ⟨rfl, rfl⟩
    · intro p hp hne
      rw [mem_filter, HasAntidiagonal.mem_antidiagonal] at hp
      exact absurd (Prod.ext (by omega) (by omega)) hne
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [mem_filter, HasAntidiagonal.mem_antidiagonal] at hp
    exact absurd ⟨p.1, by omega⟩ hN

/-- Modulo `2`: `c (n + 1) ≡ [n + 1 = 2] + ∑_{i + j = n + 1} c i c j`. -/
theorem c_succ_zmod_two (n : ℕ) :
    ((c (n + 1) : ℤ) : ZMod 2) =
      (if n + 1 = 2 then 1 else 0)
        + ∑ p ∈ antidiagonal (n + 1), ((c p.1 : ℤ) : ZMod 2) * ((c p.2 : ℤ) : ZMod 2) := by
  rw [c_succ_cast, fin_sum_sq_eq_antidiagonal (fun k => ((c k : ℤ) : ZMod 2))
    (by rw [c_zero, Int.cast_zero]) n (n + 1) le_rfl]
  have h3 : (3 : ZMod 2) = -1 := by decide
  have h6 : (6 : ZMod 2) = 0 := by decide
  have h36 : (36 : ZMod 2) = 0 := by decide
  rw [h3, h6, h36]
  ring

/-- `2 ^ k`-structure of the doubling step: `h + h = 2 ^ k` for some `1 ≤ k` iff `h = 1`
or `h = 2 ^ k` for some `1 ≤ k`. -/
theorem exists_pow_double_iff (h : ℕ) :
    (∃ k : ℕ, 1 ≤ k ∧ h + h = 2 ^ k) ↔ h = 1 ∨ ∃ k : ℕ, 1 ≤ k ∧ h = 2 ^ k := by
  constructor
  · rintro ⟨k, hk, hkeq⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ] at hkeq
    have hh : h = 2 ^ k' := by omega
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · left
      rw [hh, pow_zero]
    · exact Or.inr ⟨k', hk', hh⟩
  · rintro (rfl | ⟨k, _, rfl⟩)
    · exact ⟨1, le_rfl, rfl⟩
    · exact ⟨k + 1, by omega, by rw [pow_succ]; ring⟩

open Classical in
/-- The reduction of `c n` modulo `2` is the indicator of `n ∈ {2, 4, 8, 16, …}`. -/
theorem c_cast_zmod_two (n : ℕ) :
    ((c n : ℤ) : ZMod 2) = if ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · rw [c_zero, Int.cast_zero, if_neg]
    rintro ⟨k, _, hk⟩
    exact (pow_pos two_pos k).ne' hk.symm
  · have hsq := sum_antidiagonal_mul_zmod_two (fun k => ((c k : ℤ) : ZMod 2)) (n + 1)
    beta_reduce at hsq
    rw [c_succ_zmod_two, hsq]
    by_cases hev : Even (n + 1)
    · obtain ⟨h, hh⟩ := hev
      rw [if_pos (show Even (n + 1) from ⟨h, hh⟩), show (n + 1) / 2 = h by omega, ih h (by omega), hh,
        exists_pow_double_iff]
      by_cases h1 : h = 1
      · have hnot : ¬ ∃ k : ℕ, 1 ≤ k ∧ h = 2 ^ k := by
          rintro ⟨k, hk, hkeq⟩
          rw [h1] at hkeq
          have h2le : 2 ≤ 2 ^ k := by
            calc 2 = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ k := Nat.pow_le_pow_right two_pos hk
          omega
        rw [if_pos (show h + h = 2 by omega), if_neg hnot, if_pos (Or.inl h1), add_zero]
      · rw [if_neg (show ¬ h + h = 2 by omega), zero_add]
        by_cases hP : ∃ k : ℕ, 1 ≤ k ∧ h = 2 ^ k
        · rw [if_pos hP, if_pos (Or.inr hP)]
        · rw [if_neg hP, if_neg (show ¬ (h = 1 ∨ ∃ k : ℕ, 1 ≤ k ∧ h = 2 ^ k) from fun hor => hor.elim h1 hP)]
    · rw [if_neg hev, add_zero, if_neg (show ¬ n + 1 = 2 from fun h2 => hev (h2 ▸ even_two)), if_neg]
      rintro ⟨k, hk, hkeq⟩
      apply hev
      rw [hkeq]
      exact (Nat.even_pow' (by omega)).mpr even_two

/-! ## The conjecture -/

/-- **Bala's conjecture (A144637, Peter Bala, Feb 19 2026).**

Verbatim: "Conjecture: (1/18)*6^(n)*a(n)/n! is odd iff n = 2^k for k >= 1."

Here `c n = 6^n a(n) / (18 n!)` is the `n`-th coefficient of `A(6x)/18`, the unique
power series `z` with `z(0) = 0` and `36 z^3 + 3 z^2 + (1 + 6x) z = x^2`
(see `coeff_eq_of_equation`).  The conclusion is the parity statement for every
`n : ℕ`, including `n = 0` and `n = 1` (`c 0 = c 1 = 0` are even and neither index
is `2^k` with `1 ≤ k`). -/
theorem odd_iff (n : ℕ) : Odd (c n) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k := by
  classical
  rw [← ZMod.intCast_eq_one_iff_odd, c_cast_zmod_two]
  split_ifs with hP
  · exact iff_of_true rfl hP
  · exact iff_of_false (by decide) hP

end Candidates.A144637SumCoefficientsOdd
