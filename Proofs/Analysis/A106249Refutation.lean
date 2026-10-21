/-
# A106249 — Lagneau: roots of `x^n + 1` in the left half-plane (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A106249` and the live
## entry https://oeis.org/A106249)

```
NAME:     Expansion of (1-x+x^2+x^3)/((1+x)*(1+x^2)*(1-x)^2).
OFFSET:   0
TERMS:    1,0,1,2,3,2,3,4,5,4,5,6,7,6,7,8,9,8,9,10,11,10,11,12,13,12,13,14,
          15,14,15,16,17,16,17,18,19,18,19,20,21,20,21,22,23,22,23,24,...
COMMENT:  Conjecture: number of roots of x^n + 1 in the left half-plane for
          n > 0. - _Michel Lagneau_, Oct 31 2012
FORMULA:  G.f.: (1-x+x^2+x^3)/(1-x-x^4+x^5)
          = (1+x^2+2*x^3+x^4+2*x^5+x^6)/(1-x^4)^2.
MATH:     LinearRecurrence[{1,0,0,1,-1},{1,0,1,2,3},80]
AUTHOR:   _Paul Barry_, Apr 27 2005
```

No later comment retracts or corrects the conjecture.  (Lagneau's companion
formula "a(n) = numbers of times cos(-Pi/n+2k*Pi/n) < 0 for k = 0..n-1",
Nov 02 2012, counts the same roots and is off by one in the same way; it is
not formalized here.)

## Status

This module **refutes** the conjecture.  For `n = 1`, `x + 1` has the single
root `-1`, which lies in the left half-plane, while `a(1) = 0`
(`conjecture_false`).  The conjecture is in fact false for every `n > 0`:
the root counts for `n = 1, 2, 3, ...` are `1, 0, 1, 2, 3, 2, ...`, the
sequence itself without its offset shift.  The corrected statement, that the
number of roots of `x^(n+1) + 1` with negative real part is `a(n)`, is proved
below as `ncard_leftRoots_succ`.  (Since `-1` has real part `< 0`, `n = 1`
also refutes the reading with the closed half-plane.)
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A106249Refutation

open Complex

/-! ## Definition layer -/

/-- A106249: the coefficients of `(1-x+x^2+x^3)/((1+x)*(1+x^2)*(1-x)^2)`.
The denominator expands to `1 - x - x^4 + x^5`, so the coefficients obey
`a(n) = a(n-1) + a(n-4) - a(n-5)` from the initial terms `1, 0, 1, 2, 3`
(the entry's program `LinearRecurrence[{1,0,0,1,-1},{1,0,1,2,3},80]`).
The bridge to the generating function is `a_genFun`. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | n + 5 => a (n + 4) + a (n + 1) - a n

/-- The set of roots of `x^n + 1` in the open left half-plane `Re z < 0`. -/
def leftRoots (n : ℕ) : Set ℂ := {z : ℂ | z ^ n + 1 = 0 ∧ z.re < 0}

/-! ## Ground truth -/

-- The recurrence reproduces the DATA line.
example : (List.range 24).map a =
    [1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 7, 6, 7, 8, 9, 8, 9, 10, 11, 10, 11, 12] := by
  decide +kernel

/-- **Generating-function bridge.** The power series with coefficients `a n`,
times `(1+x)(1+x^2)(1-x)^2`, is `1 - x + x^2 + x^3`; that is, `a` is the
expansion named by A106249. -/
theorem a_genFun :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 + PowerSeries.X) * (1 + PowerSeries.X ^ 2) * (1 - PowerSeries.X) ^ 2) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
  have hden : ((1 + PowerSeries.X) * (1 + PowerSeries.X ^ 2) * (1 - PowerSeries.X) ^ 2 :
      PowerSeries ℚ) = 1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by
    ring
  have hnum : (1 - PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℚ) =
      1 - PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
    ring
  rw [hden, hnum]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  match n with
  | 0 => norm_num [a]
  | 1 => norm_num [a]
  | 2 => norm_num [a]
  | 3 => norm_num [a]
  | 4 => norm_num [a]
  | n + 5 =>
    simp only [show 1 ≤ n + 5 by omega, show 4 ≤ n + 5 by omega, show 5 ≤ n + 5 by omega,
      if_true, show n + 5 - 1 = n + 4 by omega, show n + 5 - 4 = n + 1 by omega,
      show n + 5 - 5 = n by omega, a]
    push_cast
    ring

/-- `x + 1` has exactly one root, `-1`, and it lies in the left half-plane. -/
theorem leftRoots_one : leftRoots 1 = {-1} := by
  ext z
  simp only [leftRoots, pow_one, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, -⟩
    exact eq_neg_of_add_eq_zero_left hz
  · rintro rfl
    norm_num

/-! ## The conjecture and its refutation -/

/-- **Lagneau's conjecture (A106249, Oct 31 2012).** Verbatim: "Conjecture:
number of roots of x^n + 1 in the left half-plane for n > 0."  The roots are
counted as a set (they are simple), the half-plane is `Re z < 0`, and the
count is cast to `ℤ`, where `a` takes its values. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → ((leftRoots n).ncard : ℤ) = a n

/-- **The conjecture is false**, with counterexample `n = 1`: `x + 1` has one
root (`-1`) in the left half-plane, but `a(1) = 0`.  The author evidently
intended the offset-shifted count `a(n-1)`; see `ncard_leftRoots_succ`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h1 := h 1 Nat.one_pos
  rw [leftRoots_one, Set.ncard_singleton] at h1
  have ha : a 1 = 0 := rfl
  rw [ha] at h1
  norm_num at h1

/-! ## The corrected statement

The roots of `x^n + 1` are `exp(iπ(2k+1)/n)` for `k < n`; such a root has
negative real part exactly when `n < 2(2k+1) < 3n`. -/

/-- The `k`-th root `exp(iπ(2k+1)/n)` of `x^n + 1`. -/
noncomputable def root (n k : ℕ) : ℂ := exp (((Real.pi * (2 * k + 1) / n : ℝ) : ℂ) * I)

/-- Each `root n k` is a root of `x^n + 1`. -/
theorem root_pow_add_one (n k : ℕ) (hn : 0 < n) : root n k ^ n + 1 = 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [root, ← exp_nat_mul]
  have harg : (n : ℂ) * (((Real.pi * (2 * k + 1) / n : ℝ) : ℂ) * I) =
      (k : ℂ) * (2 * Real.pi * I) + Real.pi * I := by
    push_cast
    field_simp
  rw [harg, exp_add, exp_nat_mul, exp_two_pi_mul_I, exp_pi_mul_I]
  simp

/-- Every root of `x^n + 1` is `root n k` for some `k < n`. -/
theorem exists_root_eq (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : z ^ n + 1 = 0) :
    ∃ k < n, root n k = z := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set w : ℂ := exp (Real.pi * I / n) with hw
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hwn : w ^ n = -1 := by
    rw [hw, ← exp_nat_mul, mul_div_cancel₀ _ hn', exp_pi_mul_I]
  have hpow : (z / w) ^ n = 1 := by
    rw [div_pow, hwn, eq_neg_of_add_eq_zero_left hz]
    norm_num
  obtain ⟨i, hi, hzi⟩ := (isPrimitiveRoot_exp n hn.ne').eq_pow_of_pow_eq_one hpow
  refine ⟨i, hi, ?_⟩
  have hz' : z = exp (2 * Real.pi * I / n) ^ i * w := by
    rw [hzi, div_mul_cancel₀ _ hw0]
  rw [hz', hw, ← exp_nat_mul, ← exp_add, root]
  congr 1
  push_cast
  field_simp

/-- The real part of `root n k` is `cos(π(2k+1)/n)`. -/
theorem root_re (n k : ℕ) : (root n k).re = Real.cos (Real.pi * (2 * k + 1) / n) :=
  exp_ofReal_mul_I_re _

/-- The roots `root n k`, `k < n`, are pairwise distinct. -/
theorem root_injOn (n : ℕ) (hn : 0 < n) : Set.InjOn (root n) (Finset.range n) := by
  intro j hj k hk hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨m, hm⟩ := exp_eq_exp_iff_exists_int.mp hjk
  have hm' : ((j : ℤ) : ℂ) = (k : ℤ) + m * n := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast at hm ⊢
    field_simp at hm
    linear_combination hm / 2
  have hm'' : (j : ℤ) = k + m * n := by exact_mod_cast hm'
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hm0
  omega

/-- For `k < n`, `cos(π(2k+1)/n) < 0` iff `n < 4k+2 < 3n`. -/
theorem cos_neg_iff (n k : ℕ) (hk : k < n) :
    Real.cos (Real.pi * (2 * k + 1) / n) < 0 ↔ n < 4 * k + 2 ∧ 4 * k + 2 < 3 * n := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  set θ := Real.pi * (2 * k + 1) / n with hθ
  have hθn : θ * n = Real.pi * (2 * k + 1) := by
    rw [hθ]; field_simp
  constructor
  · intro hcos
    by_contra hbad
    rcases not_and_or.mp hbad with h1 | h1
    · have h1R : (4 * k + 2 : ℝ) ≤ n := by exact_mod_cast not_lt.mp h1
      have hle : θ ≤ Real.pi / 2 := by
        by_contra hc
        simp only [not_le] at hc
        nlinarith
      have hge : 0 ≤ θ := by positivity
      have hcos' := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hle
      linarith
    · have h1R : (3 * n : ℝ) ≤ 4 * k + 2 := by exact_mod_cast not_lt.mp h1
      have hge : Real.pi + Real.pi / 2 ≤ θ := by
        by_contra hc
        simp only [not_le] at hc
        nlinarith
      have hlt : θ < 2 * Real.pi := by
        by_contra hc
        simp only [not_lt] at hc
        nlinarith
      have hcos' := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := 2 * Real.pi - θ)
        (by linarith) (by linarith)
      rw [Real.cos_two_pi_sub] at hcos'
      linarith
  · rintro ⟨h1, h2⟩
    have h1R : (n : ℝ) < 4 * k + 2 := by exact_mod_cast h1
    have h2R : (4 * k + 2 : ℝ) < 3 * n := by exact_mod_cast h2
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · by_contra hc
      simp only [not_lt] at hc
      nlinarith
    · by_contra hc
      simp only [not_lt] at hc
      nlinarith

/-- `a` has period-4 increments: `a(n+4) = a(n) + 2`. -/
theorem a_add_four (n : ℕ) : a (n + 4) = a n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 + 4 = n + 5 by omega, a, ih]
    ring

/-- Closed form: `a(m) = ⌊(3m+4)/4⌋ - ⌊(m+3)/4⌋`. -/
theorem a_eq (m : ℕ) : a m = (((3 * m + 4) / 4 : ℕ) : ℤ) - (((m + 3) / 4 : ℕ) : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | m + 4 =>
      have h1 : (3 * (m + 4) + 4) / 4 = (3 * m + 4) / 4 + 3 := by omega
      have h2 : (m + 4 + 3) / 4 = (m + 3) / 4 + 1 := by omega
      rw [a_add_four, ih m (by omega), h1, h2]
      push_cast
      ring

/-- The left-half-plane roots of `x^n + 1` are the `root n k` with
`k < n` and `n < 4k+2 < 3n`. -/
theorem leftRoots_eq (n : ℕ) (hn : 0 < n) :
    leftRoots n = ↑(((Finset.range n).filter
      (fun k => n < 4 * k + 2 ∧ 4 * k + 2 < 3 * n)).image (root n)) := by
  ext z
  simp only [leftRoots, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter,
    Finset.mem_range, Set.mem_image]
  constructor
  · rintro ⟨hz, hre⟩
    obtain ⟨k, hk, rfl⟩ := exists_root_eq n hn z hz
    refine ⟨k, ⟨hk, (cos_neg_iff n k hk).mp ?_⟩, rfl⟩
    rwa [root_re] at hre
  · rintro ⟨k, ⟨hk, hcond⟩, rfl⟩
    refine ⟨root_pow_add_one n k hn, ?_⟩
    rw [root_re]
    exact (cos_neg_iff n k hk).mpr hcond

/-- **Corrected form (proved).** For every `n`, the number of roots of
`x^(n+1) + 1` in the open left half-plane is `a(n)`; that is, Lagneau's count
holds with the index shifted by one. -/
theorem ncard_leftRoots_succ (n : ℕ) : ((leftRoots (n + 1)).ncard : ℤ) = a n := by
  rw [leftRoots_eq (n + 1) n.succ_pos, Set.ncard_coe_finset,
    Finset.card_image_of_injOn ((root_injOn (n + 1) n.succ_pos).mono
      (Finset.coe_subset.mpr (Finset.filter_subset _ _))), a_eq]
  have hfilter : (Finset.range (n + 1)).filter
      (fun k => n + 1 < 4 * k + 2 ∧ 4 * k + 2 < 3 * (n + 1)) =
      Finset.Ico ((n + 3) / 4) ((3 * n + 4) / 4) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter, Nat.card_Ico]
  omega

-- Non-vacuity of the corrected form at the refuting index: one root for `n = 1`.
example : (leftRoots 1).ncard = 1 := by
  rw [leftRoots_one, Set.ncard_singleton]

end Candidates.A106249Refutation
