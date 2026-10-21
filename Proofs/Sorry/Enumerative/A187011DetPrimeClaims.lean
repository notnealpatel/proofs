/-
# A187011 — Zhi-Wei Sun: sign and growth of det(|p_i - p_j|)

## OEIS source (pulled with `oeis show A187011` and the live `%`-format entry, 2026-10-21)

```
NAME:     Determinant of the n X n matrix with (i,j)-entry equal to |p_i-p_j|,
          where p_k denotes the k-th prime.
OFFSET:   0,4
TERMS:    1,0,-1,12,-80,1152,-5632,61440,-278528,2752512,-42467328,182452224,
          -2642411520,23555211264,-99052683264,869730877440,-11828339933184,...
COMMENT:  Conjecture: (-1)^(n-1)*a(n) > 0 for all n > 1, and |a(n)|^{1/n} tends
          to the infinity.
AUTHOR:   Zhi-Wei Sun, Aug 30 2013   (the %C line itself carries no separate
          signature; the entry author is Sun)
```

## Status

Triage (2026-10-21): proved elsewhere.  The sign part is classical; the growth part is
known only via sieve methods and is not formalized here.

The sign claim follows from the classical determinant of a distance matrix of points
on a line: for `x_1 < ⋯ < x_n`,
`det (|x_i - x_j|) = (-1)^(n-1) 2^(n-2) (x_n - x_1) ∏ (x_{i+1} - x_i)`
(path case of Graham–Pollak 1971 / Bapat–Kirkland–Neumann 2005).  The growth claim
reduces, by the same formula, to the geometric mean of the first `n` prime gaps tending
to infinity, which follows from Brun/Selberg sieve upper bounds for prime pairs
`(p, p + h)`; this sieve input is not available in Mathlib.

## Computational re-validation (2026-10-21)

Exact rational Gaussian elimination for `n ≤ 39` (python, `Fraction`): the closed form
above matches the determinant for every `2 ≤ n ≤ 39`, the sign claim holds there, and
the values agree with the 23 listed terms `a(0..22)`.  `|a(n)|^{1/n}` is about
`4.1, 5.8, 6.3, 7.0, 7.5, 7.3, 7.8` at `n = 5, 10, …, 35` (slow, log-like growth).

## What is proved here

* `det_distMat`: the closed form for strictly increasing points in any linearly ordered
  field, with an extra additive shift `t` (kernel-checked).
* `a_add_two`: `a (m+2) = (-1)^(m+1) 2^m (p_{m+2} - 2) ∏_{i ≤ m} (p_{i+2} - p_{i+1})`.
* `sign_pos`: the first claim of the conjecture, `0 < (-1)^(n-1) a(n)` for `1 < n`.
* `growth_of_tendsto_mean_log_gap`: the second claim follows from "the mean of `log` of
  the first `n` prime gaps tends to infinity" (kernel-checked reduction).
* `tendsto_mean_log_prime_gap`: that prime-gap statement, the single `sorry` (needs a
  Brun/Selberg twin-type upper bound not in Mathlib).  `growth` and `sun_conjecture`
  depend on it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A187011DetPrimeClaims

open Matrix Filter

section DistMat

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The distance matrix `(|x i - x j|)` of points `x` on a line, shifted by the constant
`t` in every entry. -/
def distMat {k : ℕ} (x : Fin k → 𝕜) (t : 𝕜) : Matrix (Fin k) (Fin k) 𝕜 :=
  Matrix.of fun i j => |x i - x j| + t

/-- **Determinant of a shifted distance matrix on a line.**  For strictly increasing
points `x 0 < x 1 < ⋯ < x (m+1)` in a linearly ordered field and any shift `t`,
`det (|x i - x j| + t) = (-1)^(m+1) · 2^m · (x_last - x_0 + 2t) · ∏ (x_{i+1} - x_i)`.
At `t = 0` this is the classical path case of the Graham–Pollak / Bapat–Kirkland–Neumann
distance-matrix determinant.  The shift `t` makes the induction (Schur complement on the
last point) go through. -/
theorem det_distMat (m : ℕ) (x : Fin (m + 2) → 𝕜) (hx : StrictMono x) (t : 𝕜) :
    (distMat x t).det = (-1) ^ (m + 1) * 2 ^ m * (x (Fin.last _) - x 0 + 2 * t) *
      ∏ i : Fin (m + 1), (x i.succ - x i.castSucc) := by
  induction m generalizing t with
  | zero =>
    have h01 : x 0 < x 1 := hx (by decide)
    rw [Matrix.det_fin_two]
    simp only [distMat, Matrix.of_apply, sub_self, abs_zero, abs_of_neg (sub_neg.mpr h01),
      abs_of_pos (sub_pos.mpr h01)]
    simp [Fin.last]
    ring
  | succ m ih =>
    set l : Fin (m + 3) := Fin.last (m + 2) with hl
    set p : Fin (m + 3) := (Fin.last (m + 1)).castSucc with hp
    have hpl : p ≠ l := Fin.castSucc_ne_last _
    have hlp : l ≠ p := hpl.symm
    set g : 𝕜 := x l - x p with hg
    have hle : ∀ i : Fin (m + 2), x i.castSucc ≤ x p :=
      fun i => hx.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))
    have hxpl : x p < x l := hx (Fin.castSucc_lt_last _)
    set N := distMat x t with hN
    set N1 := N.updateCol l (fun k => N k l + (-1 : 𝕜) • N k p) with hN1
    set N2 := N1.updateRow l (N1 l + (-1 : 𝕜) • N1 p) with hN2
    set w : Fin (m + 3) → 𝕜 := fun j => if j = l then 0 else 1 / 2 with hw
    set E : Matrix (Fin (m + 3)) (Fin (m + 3)) 𝕜 :=
      1 + replicateCol Unit (Pi.single l (1 : 𝕜)) * replicateRow Unit w with hE
    have hdetE : E.det = 1 := by
      rw [hE, det_one_add_replicateCol_mul_replicateRow]
      simp [hw]
    have hdet : N.det = (N2 * E).det := by
      rw [det_mul, hdetE, mul_one, hN2, det_updateRow_add_smul_self _ hlp, hN1,
        det_updateCol_add_smul_self _ hlp]
    have hN3 : ∀ i j, (N2 * E) i j = N2 i j + N2 i l * w j := by
      intro i j
      simp [hE, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, mul_add,
        Finset.sum_add_distrib, Pi.single_apply]
    have hcl : ∀ i : Fin (m + 2), i.castSucc ≠ l := fun i => Fin.castSucc_ne_last i
    have hdl : ∀ i : Fin (m + 2), |x i.castSucc - x l| = g + (x p - x i.castSucc) := by
      intro i
      rw [abs_of_neg (by linarith [hle i]), hg]
      ring
    have hdp : ∀ i : Fin (m + 2), |x i.castSucc - x p| = x p - x i.castSucc := by
      intro i
      rw [abs_of_nonpos (by linarith [hle i])]
      ring
    have hN2ij : ∀ i j : Fin (m + 2), N2 i.castSucc j.castSucc = |x i.castSucc - x j.castSucc| + t := by
      intro i j
      simp [hN2, hN1, hN, distMat, Matrix.updateRow_apply, hcl]
    have hN2il : ∀ i : Fin (m + 2), N2 i.castSucc l = g := by
      intro i
      simp only [hN2, hN1, hN, distMat, Matrix.updateRow_apply, Matrix.updateCol_apply, hcl,
        if_false, if_true, Matrix.of_apply, smul_eq_mul]
      rw [hdl, hdp]
      ring
    have hN2lj : ∀ j : Fin (m + 2), N2 l j.castSucc = g := by
      intro j
      simp only [hN2, hN1, hN, distMat, Matrix.updateRow_apply, Matrix.updateCol_apply, hcl,
        if_false, if_true, Matrix.of_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
      rw [abs_sub_comm, hdl, abs_sub_comm, hdp]
      ring
    have hN2ll : N2 l l = -2 * g := by
      simp only [hN2, hN1, hN, distMat, Matrix.updateRow_apply, Matrix.updateCol_apply,
        if_true, Matrix.of_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
      rw [abs_sub_comm (x p) (x l), abs_of_pos (sub_pos.mpr hxpl), sub_self, sub_self, abs_zero,
        hg]
      ring
    have hw_cs : ∀ j : Fin (m + 2), w j.castSucc = 1 / 2 := fun j => by simp [hw, hcl]
    have hw_l : w l = 0 := by simp [hw]
    have hrow : ∀ j : Fin (m + 2), (N2 * E) l j.castSucc = 0 := by
      intro j
      rw [hN3, hN2lj, hN2ll, hw_cs]
      ring
    have hcorner : (N2 * E) l l = -2 * g := by
      rw [hN3, hN2ll, hw_l]
      ring
    have hminor : (N2 * E).submatrix Fin.castSucc Fin.castSucc =
        distMat (x ∘ Fin.castSucc) (t + g / 2) := by
      ext i j
      rw [Matrix.submatrix_apply, hN3, hN2ij, hN2il, hw_cs]
      simp only [distMat, Matrix.of_apply, Function.comp_apply]
      ring
    have hxc : StrictMono (x ∘ Fin.castSucc) := hx.comp Fin.strictMono_castSucc
    have hsa : l.succAbove = Fin.castSucc := by rw [hl]; exact Fin.succAbove_last
    have hsign : ((-1 : 𝕜) ^ ((l : ℕ) + (l : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    have hlast : (Fin.last (m + 1)).succ = l := by rw [hl, Fin.succ_last]
    rw [hdet, Matrix.det_succ_row _ l, Fin.sum_univ_castSucc]
    simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hcorner, hsign, hsa, hminor, ih _ hxc, Fin.prod_univ_castSucc (n := m + 1)]
    simp only [Function.comp_apply, Fin.succ_castSucc, Fin.castSucc_zero, hlast, ← hp]
    rw [hg]
    ring

end DistMat

/-! ## The sequence -/

/-- **A187011.** `a n = det (|p_i - p_j|)_{1 ≤ i, j ≤ n}` with `p_k` the `k`-th prime.
Lean indexes from `0`, so OEIS `p_{k+1}` is `Nat.nth Nat.Prime k` (`= 2` at `k = 0`).
The empty determinant gives `a 0 = 1`, matching the OEIS offset `0`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin n => |(Nat.nth Nat.Prime i : ℤ) - Nat.nth Nat.Prime j|).det

/-- Ground truth `a(0) = 1` (empty determinant). -/
example : a 0 = 1 := by
  simp [a]

/-- Ground truth `a(1) = 0`. -/
example : a 1 = 0 := by
  simp [a, Matrix.det_unique]

/-- Ground truth `a(2) = -1`. -/
example : a 2 = -1 := by
  simp [a, Matrix.det_fin_two, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- Ground truth `a(3) = 12`, computed directly from the 3 × 3 determinant. -/
example : a 3 = 12 := by
  simp [a, Matrix.det_fin_three, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five]

/-- The `ℚ`-cast of `a (m+2)` is the unshifted distance-matrix determinant of the first
`m + 2` primes. -/
theorem cast_a_eq_det_distMat (n : ℕ) :
    (a n : ℚ) = (distMat (fun i : Fin n => (Nat.nth Nat.Prime i : ℚ)) 0).det := by
  rw [a, Int.cast_det]
  congr 1
  ext i j
  simp [distMat]

/-- **Closed form for A187011.** For `n = m + 2 ≥ 2`,
`a n = (-1)^(n-1) · 2^(n-2) · (p_n - p_1) · ∏_{i < n-1} (p_{i+2} - p_{i+1})`
(OEIS indexing), here with `p_1 = 2`. -/
theorem a_add_two (m : ℕ) :
    a (m + 2) = (-1) ^ (m + 1) * 2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℤ) - 2) *
      ∏ i : Fin (m + 1), ((Nat.nth Nat.Prime (i + 1) : ℤ) - Nat.nth Nat.Prime i) := by
  have hmono : StrictMono (fun i : Fin (m + 2) => (Nat.nth Nat.Prime i : ℚ)) := by
    intro i j hij
    have h : Nat.nth Nat.Prime i < Nat.nth Nat.Prime j :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Fin.lt_def.mp hij)
    show (Nat.nth Nat.Prime i : ℚ) < Nat.nth Nat.Prime j
    exact_mod_cast h
  apply Int.cast_injective (α := ℚ)
  rw [cast_a_eq_det_distMat, det_distMat m _ hmono 0]
  push_cast
  simp [Nat.nth_prime_zero_eq_two]

/-- Ground truth `a(4) = -80` via the closed form (`p = 2, 3, 5, 7`). -/
example : a 4 = -80 := by
  rw [a_add_two]
  simp [Fin.prod_univ_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-- **Sun's conjecture, sign part (A187011).**  Verbatim: "(-1)^(n-1)*a(n) > 0 for all
n > 1".  The guard `1 < n` is from the source and keeps the truncated exponent `n - 1`
honest; it is load-bearing, since `a 1 = 0`. -/
theorem sign_pos (n : ℕ) (hn : 1 < n) : 0 < (-1) ^ (n - 1) * a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hlast : (2 : ℤ) < Nat.nth Nat.Prime (m + 1) := by
    have h := hsm (Nat.succ_pos m)
    rw [Nat.nth_prime_zero_eq_two] at h
    exact_mod_cast h
  have hgaps : 0 < ∏ i : Fin (m + 1),
      ((Nat.nth Nat.Prime (i + 1) : ℤ) - Nat.nth Nat.Prime i) := by
    apply Finset.prod_pos
    intro i _
    have h := hsm (Nat.lt_succ_self (i : ℕ))
    have h' : (Nat.nth Nat.Prime i : ℤ) < Nat.nth Nat.Prime (i + 1) := by exact_mod_cast h
    linarith
  have hexp : m + 2 - 1 = m + 1 := by omega
  rw [a_add_two, hexp]
  have hsq : ((-1 : ℤ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc (0 : ℤ) < 2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℤ) - 2) *
        ∏ i : Fin (m + 1), ((Nat.nth Nat.Prime (i + 1) : ℤ) - Nat.nth Nat.Prime i) := by
        have h2 : (0 : ℤ) < 2 ^ m := by positivity
        have hp2 : (0 : ℤ) < (Nat.nth Nat.Prime (m + 1) : ℤ) - 2 := by linarith
        positivity
    _ = _ := by linear_combination (-(2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℤ) - 2) *
        ∏ i : Fin (m + 1), ((Nat.nth Nat.Prime (i + 1) : ℤ) - Nat.nth Nat.Prime i))) * hsq

/-- Every prime gap is at least `1`: `1 ≤ p_{i+2} - p_{i+1}` (OEIS indexing), over `ℝ`. -/
theorem one_le_gap (i : ℕ) :
    (1 : ℝ) ≤ (Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i := by
  have h : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self i)
  have h' : (Nat.nth Nat.Prime i : ℝ) + 1 ≤ Nat.nth Nat.Prime (i + 1) := by exact_mod_cast h
  linarith

/-- The product of the first `m + 1` prime gaps is positive. -/
theorem prod_gap_pos (m : ℕ) :
    0 < ∏ i ∈ Finset.range (m + 1), ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i) :=
  Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (one_le_gap i)

/-- The product of the first `m + 1` prime gaps is at most `|a (m+2)|`, by the closed form
`a_add_two` (the dropped factors `2^m` and `p_{m+2} - 2` are both `≥ 1`). -/
theorem prod_gap_le_abs_a (m : ℕ) :
    ∏ i ∈ Finset.range (m + 1), ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i) ≤
      |(a (m + 2) : ℝ)| := by
  set P : ℝ := ∏ i ∈ Finset.range (m + 1),
    ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i) with hP
  have hPpos : 0 < P := prod_gap_pos m
  have hlast : (3 : ℝ) ≤ Nat.nth Nat.Prime (m + 1) := by
    have h := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.succ_pos m)
    rw [Nat.nth_prime_zero_eq_two] at h
    have h' : 3 ≤ Nat.nth Nat.Prime (m + 1) := h
    exact_mod_cast h'
  have hcast : (a (m + 2) : ℝ) = (-1) ^ (m + 1) * (2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℝ) - 2) * P) := by
    rw [a_add_two, hP, ← Fin.prod_univ_eq_prod_range
      (fun i => ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i))]
    push_cast
    ring
  have hrest : 0 < 2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℝ) - 2) * P := by
    have h3 : (0 : ℝ) < (Nat.nth Nat.Prime (m + 1) : ℝ) - 2 := by linarith
    positivity
  have habs : |(a (m + 2) : ℝ)| = 2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℝ) - 2) * P := by
    rw [hcast, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hrest]
  rw [habs]
  have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ (Nat.nth Nat.Prime (m + 1) : ℝ) - 2 := by linarith
  have h23 : (1 : ℝ) ≤ 2 ^ m * ((Nat.nth Nat.Prime (m + 1) : ℝ) - 2) :=
    one_le_mul_of_one_le_of_one_le h2 h3
  nlinarith

/-- **Conditional growth (reduction of the second claim to prime gaps).**  If the mean
of `log` over the first `n` prime gaps tends to infinity, then `|a n|^{1/n} → ∞`.
This isolates the only missing input of Sun's growth claim: a statement about prime gaps
(which follows informally from Brun's sieve) with no determinant content left. -/
theorem growth_of_tendsto_mean_log_gap
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
      Real.log ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i)) / n) atTop atTop) :
    Tendsto (fun n : ℕ => |(a n : ℝ)| ^ ((1 : ℝ) / n)) atTop atTop := by
  rw [← Filter.tendsto_add_atTop_iff_nat 2]
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n,
    Real.log ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i) with hS
  have h1 : Tendsto (fun m : ℕ => S (m + 1) / ((m + 1 : ℕ) : ℝ) / 2) atTop atTop :=
    ((Filter.tendsto_add_atTop_iff_nat 1).mpr h).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono (fun m => ?_) (Real.tendsto_exp_atTop.comp h1)
  have hgpos : ∀ i ∈ Finset.range (m + 1),
      (0 : ℝ) < (Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i :=
    fun i _ => lt_of_lt_of_le one_pos (one_le_gap i)
  have hS0 : 0 ≤ S (m + 1) :=
    Finset.sum_nonneg fun i _ => Real.log_nonneg (one_le_gap i)
  have hSlog : S (m + 1) = Real.log (∏ i ∈ Finset.range (m + 1),
      ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i)) :=
    (Real.log_prod fun i hi => (hgpos i hi).ne').symm
  have hpos : 0 < |(a (m + 2) : ℝ)| := lt_of_lt_of_le (prod_gap_pos m) (prod_gap_le_abs_a m)
  have hlog : S (m + 1) ≤ Real.log |(a (m + 2) : ℝ)| := by
    rw [hSlog]
    exact Real.log_le_log (prod_gap_pos m) (prod_gap_le_abs_a m)
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hstep : S (m + 1) / ((m + 1 : ℕ) : ℝ) / 2 ≤ Real.log |(a (m + 2) : ℝ)| * (1 / ((m + 2 : ℕ) : ℝ)) := by
    rw [div_div, mul_one_div]
    have hden : ((m + 2 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * 2 := by push_cast; linarith
    calc S (m + 1) / (((m + 1 : ℕ) : ℝ) * 2) ≤ S (m + 1) / ((m + 2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hS0 hm2 hden
      _ ≤ Real.log |(a (m + 2) : ℝ)| / ((m + 2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hlog hm2.le
  rw [Function.comp_apply, Real.rpow_def_of_pos hpos]
  exact Real.exp_le_exp.mpr hstep

/-- **Prime-gap input (the single open obligation of this module).**  The mean of
`log g_i` over the first `n` prime gaps `g_i = p_{i+2} - p_{i+1}` (OEIS indexing) tends to
infinity.

Remaining goal (exact):
`Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
  Real.log ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i)) / n) atTop atTop`.

Informal proof (known, not in Mathlib): by the Brun (or Selberg) upper-bound sieve, for each
fixed even `h` the number of primes `p ≤ x` with `p + h` prime is `O_h(x / log² x)`, which is
`o(π(x))`.  Summing over `h ≤ H`, the proportion of the first `n` gaps that are `≤ H` tends
to `0`, so the mean of `log g_i` is eventually `≥ (1 - ε) log H` for every `H`.  Mathlib's
`SelbergSieve` file only sets up the `Λ²` sieve; the twin-type upper bound is not available.
An elementary (Legendre/Eratosthenes) sieve is too weak: it only gives `O(x / (log log x)²)`. -/
theorem tendsto_mean_log_prime_gap :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
      Real.log ((Nat.nth Nat.Prime (i + 1) : ℝ) - Nat.nth Nat.Prime i)) / n) atTop atTop := by
  sorry

/-- **Sun's conjecture, growth part (A187011).**  Verbatim: "|a(n)|^{1/n} tends to the
infinity".  Stated over `ℝ` with `rpow`; the base `|a n|` is nonnegative, and the junk
exponent `1/0 = 0` at `n = 0` does not affect a limit along `atTop`.  Proved here from the
prime-gap input `tendsto_mean_log_prime_gap` (which carries the module's only `sorry`) via
the kernel-checked reduction `growth_of_tendsto_mean_log_gap`. -/
theorem growth :
    Tendsto (fun n : ℕ => |(a n : ℝ)| ^ ((1 : ℝ) / n)) atTop atTop :=
  growth_of_tendsto_mean_log_gap tendsto_mean_log_prime_gap

/-- **Sun's conjecture (A187011, Zhi-Wei Sun, Aug 30 2013), both parts.**
"(-1)^(n-1)*a(n) > 0 for all n > 1, and |a(n)|^{1/n} tends to the infinity."
The sign part is proved (`sign_pos`); the growth part `growth` depends on the
unproved prime-gap input `tendsto_mean_log_prime_gap`. -/
theorem sun_conjecture :
    (∀ n : ℕ, 1 < n → 0 < (-1) ^ (n - 1) * a n) ∧
      Tendsto (fun n : ℕ => |(a n : ℝ)| ^ ((1 : ℝ) / n)) atTop atTop :=
  ⟨sign_pos, growth⟩

end Candidates.A187011DetPrimeClaims
