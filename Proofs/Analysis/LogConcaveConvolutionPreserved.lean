/-
# Log-concavity under convolution and products of geometric polynomials

Source: Fabrizio Zanello, *Log-concavity of level Hilbert functions and
pure O-sequences*, arXiv:2210.09447, Section 3, Proposition `type1`.
Its generating-function proof identifies a type-1 pure O-sequence with
the coefficients of `∏ᵢ (1+q+⋯+q^{aᵢ})` and invokes the classical
log-concave product lemma (Stanley's 1989 survey, Proposition 2; Brenti).

This file proves the coefficient/product theorem, not a theorem
quantifying over pure O-sequences or Hilbert functions. Their identification
with these coefficients is not formalized here.

Convolution preserves nonnegative log-concavity and no internal zeros.
No finite-support hypothesis is needed: every convolution coefficient is
a finite sum. The no-internal-zeros assumption is essential; the example
`(1,0,0,1) * (1,1) = (1,1,0,1,1)` records failure without it.

The proof derives PF₂ from these hypotheses and uses a finite 2×2
Cauchy–Binet identity. Polynomial multiplication and induction then give
log-concavity of the geometric-polynomial product.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.LogConcaveConvolutionPreserved

open Finset

/-- A real sequence `a` is log-concave: `a i * a (i + 2) ≤ a (i + 1) ^ 2` for every `i`.
This is Zanello's `a_{i-1} a_{i+1} ≤ a_i²` for all indices `i ≥ 1`, reindexed so
that no natural-number subtraction occurs. -/
def LogConcave (a : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, a i * a (i + 2) ≤ a (i + 1) ^ 2

/-- A real sequence `a` has no internal zeros: if `i ≤ j ≤ k` and `a i ≠ 0`,
`a k ≠ 0`, then `a j ≠ 0`.  Equivalently, the support of `a` is an interval. -/
def NoInternalZeros (a : ℕ → ℝ) : Prop :=
  ∀ i j k : ℕ, i ≤ j → j ≤ k → a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- Cauchy product of two sequences: `conv a b n = ∑_{i + j = n} a i * b j`.
For polynomials, `(p * q).coeff = conv p.coeff q.coeff` (`coeff_mul_eq_conv`). -/
def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal n, a p.1 * b p.2

/-- Ratio monotonicity: for a nonnegative log-concave sequence without internal
zeros, `a i * a (m + 1) ≤ a (i + 1) * a m` whenever `i ≤ m`. -/
theorem step_ineq {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hlc : LogConcave a)
    (hz : NoInternalZeros a) (i m : ℕ) (him : i ≤ m) :
    a i * a (m + 1) ≤ a (i + 1) * a m := by
  by_cases hzero : a i = 0 ∨ a (m + 1) = 0
  · rcases hzero with h | h
    · rw [h, zero_mul]; exact mul_nonneg (ha0 _) (ha0 _)
    · rw [h, mul_zero]; exact mul_nonneg (ha0 _) (ha0 _)
  simp only [not_or] at hzero
  obtain ⟨hai, ham⟩ := hzero
  have hpos : ∀ t, i ≤ t → t ≤ m + 1 → 0 < a t := fun t h1 h2 =>
    lt_of_le_of_ne (ha0 t) (Ne.symm (hz i t (m + 1) h1 h2 hai ham))
  clear hai ham
  induction m, him using Nat.le_induction with
  | base => rw [mul_comm]
  | succ m him ih =>
    have ih' := ih (fun t h1 h2 => hpos t h1 (by omega))
    have hm : 0 < a m := hpos m him (by omega)
    have hlcm := hlc m
    have key : a m * (a i * a (m + 1 + 1)) ≤ a m * (a (i + 1) * a (m + 1)) := by
      calc a m * (a i * a (m + 1 + 1)) = a i * (a m * a (m + 2)) := by ring
        _ ≤ a i * a (m + 1) ^ 2 := mul_le_mul_of_nonneg_left hlcm (ha0 i)
        _ = a (m + 1) * (a i * a (m + 1)) := by ring
        _ ≤ a (m + 1) * (a (i + 1) * a m) := mul_le_mul_of_nonneg_left ih' (ha0 _)
        _ = a m * (a (i + 1) * a (m + 1)) := by ring
    exact le_of_mul_le_mul_left key hm

/-- PF₂ property: for a nonnegative log-concave sequence without internal zeros,
an outer pair `i, j` and an inner pair `k, l` with `i ≤ k, l ≤ j` and
`i + j = k + l` satisfy `a i * a j ≤ a k * a l`. -/
theorem pf2 {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hlc : LogConcave a)
    (hz : NoInternalZeros a) (i k l j : ℕ) (hik : i ≤ k) (hil : i ≤ l) (hkj : k ≤ j)
    (hlj : l ≤ j) (hsum : i + j = k + l) :
    a i * a j ≤ a k * a l := by
  wlog hkl : k ≤ l generalizing k l
  · rw [mul_comm (a k)]; exact this l k hil hik hlj hkj (by omega) (by omega)
  induction hd : k - i generalizing i j with
  | zero =>
    obtain rfl : k = i := by omega
    obtain rfl : l = j := by omega
    exact le_refl _
  | succ d ih =>
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    calc a i * a (m + 1) ≤ a (i + 1) * a m := step_ineq ha0 hlc hz i m (by omega)
      _ ≤ a k * a l := ih (i + 1) m (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


/-- Antisymmetrization (2×2 Cauchy–Binet in sign form): if `D` is antisymmetric
and, for `k < l`, both `X l k ≤ X k l` and `0 ≤ D k l`, then the double sum
`∑_{k,l ∈ S} X k l * D k l` is nonnegative. -/
theorem sum_sum_mul_antisymm_nonneg (S : Finset ℕ) (X D : ℕ → ℕ → ℝ)
    (hD : ∀ k l, D l k = -D k l) (hX : ∀ k l, k < l → X l k ≤ X k l)
    (hD0 : ∀ k l, k < l → 0 ≤ D k l) :
    0 ≤ ∑ k ∈ S, ∑ l ∈ S, X k l * D k l := by
  have hswap : ∑ k ∈ S, ∑ l ∈ S, X k l * D k l = ∑ k ∈ S, ∑ l ∈ S, -(X l k * D k l) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hD]; ring
  have htwo : 2 * ∑ k ∈ S, ∑ l ∈ S, X k l * D k l =
      ∑ k ∈ S, ∑ l ∈ S, (X k l - X l k) * D k l := by
    calc 2 * ∑ k ∈ S, ∑ l ∈ S, X k l * D k l
        = ∑ k ∈ S, ∑ l ∈ S, X k l * D k l + ∑ k ∈ S, ∑ l ∈ S, -(X l k * D k l) := by
          rw [← hswap]; ring
      _ = ∑ k ∈ S, ∑ l ∈ S, (X k l - X l k) * D k l := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  have hterm : ∀ k l, 0 ≤ (X k l - X l k) * D k l := by
    intro k l
    rcases lt_trichotomy k l with hkl | rfl | hkl
    · exact mul_nonneg (sub_nonneg.mpr (hX k l hkl)) (hD0 k l hkl)
    · have : D k k = 0 := by linarith [hD k k]
      rw [this, mul_zero]
    · have h1 : X k l - X l k ≤ 0 := sub_nonpos.mpr (hX l k hkl)
      have h2 : D k l ≤ 0 := by rw [hD l k] at *; linarith [hD0 l k hkl, hD k l]
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hsum : 0 ≤ ∑ k ∈ S, ∑ l ∈ S, (X k l - X l k) * D k l :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hterm k l
  linarith

/-- `revCol b m k = b (m - k)` if `k ≤ m` and `0` otherwise: the column `b (m - ·)`
extended by zero past `m`, avoiding truncated subtraction. -/
def revCol (b : ℕ → ℝ) (m k : ℕ) : ℝ := if k ≤ m then b (m - k) else 0

/-- The shifted sequence `0, a 0, a 1, …` (coefficients of `X * p`). -/
def shift (a : ℕ → ℝ) (l : ℕ) : ℝ := if l = 0 then 0 else a (l - 1)

/-- The convolution as a sum over `range N` for any `N > m`, using `revCol`. -/
theorem conv_eq_sum_range (a b : ℕ → ℝ) (m N : ℕ) (hN : m < N) :
    conv a b m = ∑ k ∈ range N, a k * revCol b m k := by
  rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j)]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show m + 1 ≤ N by omega))]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [revCol, if_pos (by omega)]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [revCol, if_neg (by omega), mul_zero]

/-- Convolving the shifted sequence raises the index by one. -/
theorem conv_shift_succ (a b : ℕ → ℝ) (m : ℕ) : conv (shift a) b (m + 1) = conv a b m := by
  rw [conv, Finset.Nat.sum_antidiagonal_succ]
  simp [shift, conv]


/-- **Product lemma (Stanley 1989, Prop. 2; used in Zanello, arXiv:2210.09447,
Prop. `type1`).** If `a` and `b` are nonnegative, log-concave and have no internal
zeros, then their convolution is log-concave. -/
theorem logConcave_conv {a b : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : LogConcave a) (hb : LogConcave b) (haz : NoInternalZeros a)
    (hbz : NoInternalZeros b) : LogConcave (conv a b) := by
  intro n
  set S := range (n + 3) with hS
  let X : ℕ → ℕ → ℝ := fun k l => a k * shift a l
  let D : ℕ → ℕ → ℝ := fun k l =>
    revCol b (n + 1) k * revCol b (n + 2) l - revCol b (n + 2) k * revCol b (n + 1) l
  have hexpand : ∑ k ∈ S, ∑ l ∈ S, X k l * D k l =
      conv a b (n + 1) ^ 2 - conv a b n * conv a b (n + 2) := by
    have e1 := conv_eq_sum_range a b (n + 1) (n + 3) (by omega)
    have e2 := conv_eq_sum_range a b (n + 2) (n + 3) (by omega)
    have e3 := conv_eq_sum_range (shift a) b (n + 2) (n + 3) (by omega)
    have e4 := conv_eq_sum_range (shift a) b (n + 1) (n + 3) (by omega)
    rw [conv_shift_succ] at e3 e4
    rw [show conv a b (n + 1) ^ 2 - conv a b n * conv a b (n + 2) =
        conv a b (n + 1) * conv a b (n + 1) - conv a b (n + 2) * conv a b n by ring]
    nth_rewrite 1 [e1]
    rw [e3, e2, e4, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [X, D]
    ring
  have hD : ∀ k l, D l k = -D k l := fun k l => by simp only [D]; ring
  have hX : ∀ k l, k < l → X l k ≤ X k l := by
    intro k l hkl
    simp only [X, shift]
    split_ifs with hk hl hl
    · omega
    · rw [mul_zero]; exact mul_nonneg (ha0 _) (ha0 _)
    · omega
    · have := pf2 ha0 ha haz (k - 1) k (l - 1) l (by omega) (by omega) (by omega) (by omega)
        (by omega)
      linarith [mul_comm (a l) (a (k - 1))]
  have hD0 : ∀ k l, k < l → 0 ≤ D k l := by
    intro k l hkl
    simp only [D, revCol]
    by_cases hl : l ≤ n + 1
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos hl, sub_nonneg]
      have := pf2 hb0 hb hbz (n + 1 - l) (n + 1 - k) (n + 2 - l) (n + 2 - k) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      linarith [mul_comm (b (n + 2 - k)) (b (n + 1 - l))]
    · rw [if_neg hl, mul_zero, sub_zero]
      split_ifs <;> first
        | exact mul_nonneg (hb0 _) (hb0 _)
        | simp
  have hmain := sum_sum_mul_antisymm_nonneg S X D hD hX hD0
  rw [hexpand] at hmain
  linarith


/-- The convolution of nonnegative sequences is nonnegative. -/
theorem conv_nonneg {a b : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (n : ℕ) :
    0 ≤ conv a b n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (ha0 _) (hb0 _)

/-- For nonnegative sequences, `conv a b n ≠ 0` iff `n = i + j` with `a i ≠ 0`
and `b j ≠ 0`. -/
theorem conv_ne_zero_iff {a b : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (n : ℕ) :
    conv a b n ≠ 0 ↔ ∃ i j, i + j = n ∧ a i ≠ 0 ∧ b j ≠ 0 := by
  rw [conv, Ne, Finset.sum_eq_zero_iff_of_nonneg fun p _ => mul_nonneg (ha0 _) (hb0 _)]
  constructor
  · intro h
    push Not at h
    obtain ⟨p, hp, hne⟩ := h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact ⟨p.1, p.2, hp, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  · rintro ⟨i, j, hij, hi, hj⟩ hall
    exact mul_ne_zero hi hj (hall (i, j) (Finset.HasAntidiagonal.mem_antidiagonal.mpr hij))

/-- The convolution of nonnegative sequences without internal zeros has no
internal zeros (the sum of two intervals is an interval). -/
theorem noInternalZeros_conv {a b : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (haz : NoInternalZeros a) (hbz : NoInternalZeros b) : NoInternalZeros (conv a b) := by
  intro i j k hij hjk hi hk
  rw [conv_ne_zero_iff ha0 hb0] at hi hk ⊢
  obtain ⟨i1, i2, hi12, hai, hbi⟩ := hi
  obtain ⟨k1, k2, hk12, hak, hbk⟩ := hk
  refine ⟨min (max i1 k1) (j - min i2 k2), j - min (max i1 k1) (j - min i2 k2), by omega, ?_, ?_⟩
  · rcases le_total i1 k1 with h | h
    · exact haz i1 _ k1 (by omega) (by omega) hai hak
    · exact haz k1 _ i1 (by omega) (by omega) hak hai
  · rcases le_total i2 k2 with h | h
    · exact hbz i2 _ k2 (by omega) (by omega) hbi hbk
    · exact hbz k2 _ i2 (by omega) (by omega) hbk hbi


open Polynomial

/-- Polynomial multiplication is convolution of coefficient sequences. -/
theorem coeff_mul_eq_conv (p q : ℝ[X]) : (p * q).coeff = conv p.coeff q.coeff := by
  funext n
  rw [Polynomial.coeff_mul, conv]

/-- **Product lemma, polynomial form.** If `p, q : ℝ[X]` have nonnegative,
log-concave coefficient sequences without internal zeros, then so does `p * q`. -/
theorem logConcave_mul {p q : ℝ[X]} (hp0 : ∀ n, 0 ≤ p.coeff n) (hq0 : ∀ n, 0 ≤ q.coeff n)
    (hp : LogConcave p.coeff) (hq : LogConcave q.coeff) (hpz : NoInternalZeros p.coeff)
    (hqz : NoInternalZeros q.coeff) :
    LogConcave (p * q).coeff ∧ NoInternalZeros (p * q).coeff := by
  rw [coeff_mul_eq_conv]
  exact ⟨logConcave_conv hp0 hq0 hp hq hpz hqz, noInternalZeros_conv hp0 hq0 hpz hqz⟩

/-- The polynomial `1 + X + ⋯ + X ^ m`. -/
noncomputable def geomPoly (m : ℕ) : ℝ[X] := ∑ i ∈ range (m + 1), (X : ℝ[X]) ^ i

/-- The coefficients of `1 + X + ⋯ + X ^ m`: `1` up to degree `m`, `0` after. -/
theorem coeff_geomPoly (m n : ℕ) : (geomPoly m).coeff n = if n ≤ m then 1 else 0 := by
  rw [geomPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- `1 + X + ⋯ + X ^ m` has nonnegative coefficients. -/
theorem geomPoly_coeff_nonneg (m n : ℕ) : 0 ≤ (geomPoly m).coeff n := by
  rw [coeff_geomPoly]; split_ifs <;> norm_num

/-- `1 + X + ⋯ + X ^ m` has log-concave coefficients. -/
theorem logConcave_geomPoly (m : ℕ) : LogConcave (geomPoly m).coeff := fun i => by
  simp only [coeff_geomPoly]
  split_ifs <;> first | omega | norm_num

/-- `1 + X + ⋯ + X ^ m` has no internal zeros. -/
theorem noInternalZeros_geomPoly (m : ℕ) : NoInternalZeros (geomPoly m).coeff :=
  fun i j k hij hjk hi hk => by
    rw [coeff_geomPoly] at hi hk ⊢
    split_ifs at hi hk ⊢ <;> omega

/-- `geomPoly 0 = 1`. -/
theorem geomPoly_zero : geomPoly 0 = 1 := by simp [geomPoly]

/-- The product `∏ᵢ (1 + X + ⋯ + X ^ {aᵢ})` has nonnegative, log-concave
coefficients without internal zeros (induction on the list of exponents). -/
theorem prod_geomPoly_props (l : List ℕ) :
    (∀ n, 0 ≤ (l.map geomPoly).prod.coeff n) ∧ LogConcave (l.map geomPoly).prod.coeff ∧
      NoInternalZeros (l.map geomPoly).prod.coeff := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, ← geomPoly_zero]
    exact ⟨geomPoly_coeff_nonneg 0, logConcave_geomPoly 0, noInternalZeros_geomPoly 0⟩
  | cons m t ih =>
    obtain ⟨h0, hlc, hz⟩ := ih
    rw [List.map_cons, List.prod_cons, coeff_mul_eq_conv]
    exact ⟨conv_nonneg (geomPoly_coeff_nonneg m) h0,
      logConcave_conv (geomPoly_coeff_nonneg m) h0 (logConcave_geomPoly m) hlc
        (noInternalZeros_geomPoly m) hz,
      noInternalZeros_conv (geomPoly_coeff_nonneg m) h0 (noInternalZeros_geomPoly m) hz⟩

/-- The coefficient sequence of `∏ᵢ (1 + q + ⋯ + q^{aᵢ})` is log-concave.
This is the generating-function result used in Zanello, arXiv:2210.09447,
Proposition `type1`; the identification with pure O-sequences is not formalized. -/
theorem pureO_type1_logConcave (a : List ℕ) :
    LogConcave (a.map (fun m => ∑ i ∈ range (m + 1), (X : ℝ[X]) ^ i)).prod.coeff :=
  (prod_geomPoly_props a).2.1

/-! ## Examples -/

/-- `(1, 2, 1)` is log-concave. -/
example : LogConcave (fun n => if n = 1 then 2 else if n ≤ 2 then 1 else 0) := by
  intro i
  rcases i with _ | _ | i <;> simp

/-- `(1, 1, 2)` is not log-concave: `1 * 2 > 1 ^ 2`. -/
example : ¬ LogConcave (fun n => if n = 2 then 2 else if n ≤ 2 then 1 else 0) := by
  intro h
  have h0 := h 0
  norm_num at h0

/-- `(1, 0, 0, 1)` has an internal zero. -/
example : ¬ NoInternalZeros (fun n => if n = 0 ∨ n = 3 then 1 else 0) := by
  intro h
  exact h 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `conv` at a small instance: `(1, 1) * (1, 1, 1)` has coefficient `2` at `1`. -/
example : conv (fun n => if n ≤ 1 then 1 else 0) (fun n => if n ≤ 2 then 1 else 0) 1 = 2 := by
  norm_num [conv, Finset.Nat.antidiagonal_succ]

/-- `(1 + q)(1 + q + q²) = 1 + 2q + 2q² + q³`: the type-1 pure O-sequence `(1, 2, 2, 1)`
generated by `x y²`; checked at degree `2`. -/
example : (geomPoly 1 * geomPoly 2).coeff 2 = 2 := by
  rw [coeff_mul_eq_conv]
  norm_num [conv, Finset.Nat.antidiagonal_succ, coeff_geomPoly]

/-- Joint satisfiability of the hypotheses of `logConcave_mul`: `1 + X` and
`1 + X + X²` satisfy all six hypotheses. -/
example : LogConcave (geomPoly 1 * geomPoly 2).coeff ∧
    NoInternalZeros (geomPoly 1 * geomPoly 2).coeff :=
  logConcave_mul (geomPoly_coeff_nonneg 1) (geomPoly_coeff_nonneg 2) (logConcave_geomPoly 1)
    (logConcave_geomPoly 2) (noInternalZeros_geomPoly 1) (noInternalZeros_geomPoly 2)

/-- The no-internal-zeros hypothesis is necessary: `(1, 0, 0, 1)` and `(1, 1)` are
nonnegative and log-concave, but their convolution `(1, 1, 0, 1, 1)` is not
log-concave (`1 * 1 > 0 ^ 2` at the middle). -/
theorem not_logConcave_conv_of_internal_zeros :
    LogConcave (fun n => if n = 0 ∨ n = 3 then (1 : ℝ) else 0) ∧
      LogConcave (fun n => if n ≤ 1 then (1 : ℝ) else 0) ∧
      ¬ LogConcave (conv (fun n => if n = 0 ∨ n = 3 then 1 else 0)
        (fun n => if n ≤ 1 then 1 else 0)) := by
  refine ⟨fun i => ?_, fun i => ?_, fun h => ?_⟩
  · rcases i with _ | _ | _ | _ | i <;> simp
  · rcases i with _ | i <;> simp
  · have h1 := h 1
    norm_num [conv, Finset.Nat.antidiagonal_succ] at h1

end Candidates.LogConcaveConvolutionPreserved
