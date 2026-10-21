/-
# A002114 — Bala: Glaisher's H' numbers are eventually periodic mod k with period φ(k)

## OEIS source (retrieved with `oeis show A002114`, 2026-10-21)

```
NAME:     Glaisher's H' numbers.
OFFSET:   1 (programs list `seq(a(n), n = 1..14)`)
TERMS:    1,11,301,15371,1261501,151846331,25201039501,5515342166891,...
KEYWORDS: nice,easy,nonn,changed
FORMULA:  E.g.f. 1/2*1/(2*cos(x)-1).  [the definition used here]
FORMULA:  a(n) = 2 * Sum_{k = 1..n} (-1)^(k+1) * binomial(2*n, 2*k) * a(n-k)
          with a(0) := 1/2.  - _Peter Bala_, Oct 03 2026
COMMENT (the conjecture, From _Peter Bala_, Oct 03 2026):
  Conjecture: more generally, reducing the sequence modulo a positive integer
  k produces an eventually periodic sequence with period dividing phi(k).
  For example, modulo 13 the sequence becomes [1, 11, 2, 5, 7, 0,  1, 11, 2,
  5, 7, 0, ...], with an apparent period of 6 = phi(13)/2. Cf. A000364 and
  A000436. [The conjecture is true when k = p is a prime since the congruence
  a(n+p-1) == a(n) (mod p) holds for all n >= 1. Cf. A215066. - _Peter Bala_,
  Oct 13 2026]
```

## Status

Triage: open (the entry proves only the prime case `k = p`; no proof of the
general case was found in the entry or the literature).  Computation
(`timeout 300 python3`): the period `φ(k)` holds for every `k ≤ 300` and
`n ≤ 420`, with eventual period starting by `n = 4`; the bridge identity
`b(n) = (-1)^n d(2n)` below was checked numerically for `n ≤ 40`.

This module proves the conjecture for every `k ≥ 1`
(`a002114_eventuallyPeriodic`), in the form "eventual period `φ(k)`"
(period dividing `φ(k)` is the same statement: some eventual period divides
`φ(k)` iff `φ(k)` is an eventual period).

## Proof

Write `Y = e^x - 1`.  Then `e^{-x} = 1/(1+Y)` and
`1/(2 cosh x - 1) = H(Y)` with `H(Y) = (1+Y)/(1+Y+Y^2) = ∑ χ(m) Y^m`, where
`χ = 1, 0, -1` repeats mod 3.  So `d(m) := m! [x^m] 1/(2 cosh x - 1)` is the
weighted Stirling transform `∑_j χ(j) j! S(m,j)`, which the repository
already proves eventually periodic with period `φ(K)` modulo every `K ≥ 1`
(`OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic`).
Replacing `cosh` by `cos` twists the `x^(2n)` coefficient by `(-1)^n`, so
`2 a(n) = b(n) = (-1)^n d(2n)`; this is checked through the shared
recurrence.  Apply periodicity modulo `2k` (`φ(2k) ∣ 2 φ(k)`), divide by `2`,
and absorb the sign `(-1)^{φ(k)}`, which is `1` for `k ≥ 3` and harmless
modulo `k ≤ 2`.

## Definition layer

`glaisherB n = (2n)! [x^(2n)] 1/(2 cos x - 1)` is defined by Bala's
recurrence and `a002114 n = glaisherB n / 2` (exact division for `n ≥ 1`,
`two_mul_a002114`).  The theorem `a002114_eq_egf_coeff` proves that for
`n ≥ 1` this equals `(2n)! [x^(2n)] (2 (2 cos x - 1))⁻¹` in `ℚ⟦X⟧` with
Mathlib's `PowerSeries.cos`, i.e. the entry's e.g.f. definition.  The value
`a002114 0 = 0` lies outside the entry's offset and does not affect any
eventual statement.
-/
import Enumerative.OrdinaryIntegralEGFComposition

set_option autoImplicit false

open Finset PowerSeries

namespace Candidates.A002114GlaisherCosPeter

/-- `χ m = 1, 0, -1` according as `m ≡ 0, 1, 2 (mod 3)`. -/
def chi (m : ℕ) : ℤ := if m % 3 = 0 then 1 else if m % 3 = 1 then 0 else -1

/-- The ordinary series `∑ χ(m) X^m = (1 + X) / (1 + X + X^2)`. -/
noncomputable def chiSeries : PowerSeries ℤ := PowerSeries.mk chi

/-- `H(X) (1 + X + X^2) = 1 + X` for `H = ∑ χ(m) X^m`. -/
theorem chiSeries_mul : chiSeries * (1 + X + X ^ 2) = 1 + X := by
  ext n
  rw [mul_add, mul_add, mul_one, pow_two, ← mul_assoc]
  rcases n with _ | _ | n
  · simp [chiSeries, chi]
  · simp [chiSeries, chi, coeff_succ_mul_X]
  · simp only [map_add, coeff_succ_mul_X, chiSeries, coeff_mk, coeff_one, coeff_X]
    simp only [chi]
    omega

/-- The exponential series `D(x) = H(e^x - 1)` with `H = ∑ χ(m) X^m`. -/
noncomputable def chiEGF : PowerSeries ℚ :=
  PowerSeries.subst (exp ℚ - 1) (PowerSeries.map (Int.castRingHom ℚ) chiSeries)

/-- `D(x) (e^x - 1 + e^{-x}) = 1`, i.e. `D = 1 / (2 cosh x - 1)`. -/
theorem chiEGF_mul : chiEGF * (exp ℚ - 1 + evalNegHom (exp ℚ)) = 1 := by
  have hc : constantCoeff (exp ℚ - 1) = 0 := by simp
  have ha : HasSubst (exp ℚ - 1) := HasSubst.of_constantCoeff_zero' hc
  have h0 := congrArg (PowerSeries.map (Int.castRingHom ℚ)) chiSeries_mul
  simp only [map_mul, map_add, map_one, map_pow, map_X] at h0
  have h1 := congrArg (PowerSeries.subst (exp ℚ - 1)) h0
  rw [subst_mul ha, subst_add ha, subst_add ha, subst_pow ha, subst_X ha] at h1
  have hone : PowerSeries.subst (exp ℚ - 1) (1 : PowerSeries ℚ) = 1 := by
    rw [← map_one (PowerSeries.C (R := ℚ)), subst_C]
    rfl
  rw [hone] at h1
  change chiEGF * _ = _ at h1
  have h2 := exp_mul_exp_neg_eq_one (A := ℚ)
  linear_combination (evalNegHom (exp ℚ)) * h1 + (1 + chiEGF - chiEGF * exp ℚ) * h2

/-- `d(m) = ∑_j χ(j) j! S(m,j)`: the factorial-scaled coefficients of `chiEGF`. -/
def chiTransform (m : ℕ) : ℤ := OrdinaryIntegralEGF.weightedStirlingTransform chi m

/-- Coefficient weights of `e^x - 1 + e^{-x}`, scaled by `i!`. -/
def cWeight (i : ℕ) : ℤ := 1 + (-1) ^ i - if i = 0 then 1 else 0

/-- `[x^m] D(x) = d(m) / m!`. -/
theorem coeff_chiEGF (m : ℕ) :
    coeff m chiEGF = (chiTransform m : ℚ) / (m.factorial : ℚ) := by
  have h := OrdinaryIntegralEGF.factorial_mul_coeff_subst_exp_sub_one chiSeries m
  have hfun : (fun j => coeff j chiSeries) = chi := by
    funext j
    simp [chiSeries]
  rw [hfun] at h
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  rw [chiTransform, ← h]
  field_simp
  rfl

/-- `[x^i] (e^x - 1 + e^{-x}) = cWeight i / i!`. -/
theorem coeff_cosh_like (i : ℕ) :
    coeff i (exp ℚ - 1 + evalNegHom (exp ℚ)) = (cWeight i : ℚ) / (i.factorial : ℚ) := by
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  change coeff i (exp ℚ - 1 + rescale (-1 : ℚ) (exp ℚ)) = _
  rw [map_add, map_sub, coeff_rescale, coeff_exp, coeff_one]
  rcases i with _ | i
  · simp [cWeight]
  · simp only [cWeight, Nat.add_one_ne_zero, if_false, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    field_simp
    ring

/-- The recurrence encoded by `D(x) (e^x - 1 + e^{-x}) = 1`. -/
theorem chiTransform_rec (m : ℕ) :
    ∑ i ∈ range (m + 1), (m.choose i : ℤ) * cWeight i * chiTransform (m - i) =
      if m = 0 then 1 else 0 := by
  have h := congrArg (coeff m) chiEGF_mul
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (exp ℚ - 1 + evalNegHom (exp ℚ)) * coeff j chiEGF)] at h
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 := congrArg (fun q : ℚ => (m.factorial : ℚ) * q) h
  simp only [Finset.mul_sum, coeff_one] at h2
  have hcast : ((∑ i ∈ range (m + 1), (m.choose i : ℤ) * cWeight i *
      chiTransform (m - i) : ℤ) : ℚ) = ((if m = 0 then 1 else 0 : ℤ) : ℚ) := by
    rw [show ((if m = 0 then 1 else 0 : ℤ) : ℚ) = (m.factorial : ℚ) * (if m = 0 then 1 else 0)
      by split_ifs with h0 <;> simp [h0], ← h2]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_cosh_like, coeff_chiEGF]
    have hfac := Nat.choose_mul_factorial_mul_factorial hle
    have hfacq : (m.choose i : ℚ) * (i.factorial : ℚ) * ((m - i).factorial : ℚ) =
        (m.factorial : ℚ) := by exact_mod_cast hfac
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hmi : ((m - i).factorial : ℚ) ≠ 0 := by exact_mod_cast (m - i).factorial_ne_zero
    rw [← hfacq]
    field_simp
  exact_mod_cast hcast

/-- `b(n) = (2n)! [x^(2n)] 1/(2 cos x - 1)`, via Bala's recurrence
`b(0) = 1`, `b(n) = 2 ∑_{k=1}^{n} (-1)^(k+1) C(2n,2k) b(n-k)`. -/
def glaisherB : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2 * ∑ k ∈ range (n + 1),
      (-1) ^ k * ((2 * (n + 1)).choose (2 * (k + 1)) : ℤ) * glaisherB (n - k)
decreasing_by omega

-- Ground truth: `b = 1, 2, 22, ...` is twice A002114 (`1, 11, ...`) after `b(0) = 1`.
example : glaisherB 0 = 1 := by simp [glaisherB]
example : glaisherB 1 = 2 := by simp [glaisherB]
example : glaisherB 2 = 22 := by
  simp [glaisherB, Finset.sum_range_succ, Nat.choose]

/-- Split a sum over `range (2N+1)` into even and odd indices. -/
theorem sum_range_two_mul_add_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ i ∈ range (2 * N + 1), f i =
      ∑ j ∈ range (N + 1), f (2 * j) + ∑ j ∈ range N, f (2 * j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j => f (2 * j)) (N + 1),
      Finset.sum_range_succ (fun j => f (2 * j + 1)) N,
      show 2 * N + 1 + 1 = 2 * (N + 1) by ring]
    abel

/-- `d(0) = χ(0) = 1`. -/
theorem chiTransform_zero : chiTransform 0 = 1 := by
  simp [chiTransform, OrdinaryIntegralEGF.weightedStirlingTransform, chi]

/-- Even-index recurrence: `d(2n+2) = -2 ∑_{j=0}^{n} C(2n+2, 2j+2) d(2(n-j))`. -/
theorem chiTransform_even_rec (n : ℕ) :
    chiTransform (2 * (n + 1)) = -2 * ∑ j ∈ range (n + 1),
      ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * chiTransform (2 * (n - j)) := by
  have h := chiTransform_rec (2 * (n + 1))
  rw [if_neg (by omega), show 2 * (n + 1) + 1 = 2 * (n + 1) + 1 from rfl,
    sum_range_two_mul_add_one] at h
  have hodd : ∑ j ∈ range (n + 1), ((2 * (n + 1)).choose (2 * j + 1) : ℤ) *
      cWeight (2 * j + 1) * chiTransform (2 * (n + 1) - (2 * j + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [cWeight, pow_succ, pow_mul]
  rw [hodd, add_zero, Finset.sum_range_succ'] at h
  have hc0 : cWeight (2 * 0) = 1 := by simp [cWeight]
  have heven : ∀ j ∈ range (n + 1), ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
      cWeight (2 * (j + 1)) * chiTransform (2 * (n + 1) - 2 * (j + 1)) =
      2 * (((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * chiTransform (2 * (n - j))) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hc : cWeight (2 * (j + 1)) = 2 := by
      simp [cWeight, pow_mul]
    rw [hc, show 2 * (n + 1) - 2 * (j + 1) = 2 * (n - j) by omega]
    ring
  rw [Finset.sum_congr rfl heven, ← Finset.mul_sum, hc0] at h
  simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul] at h
  linarith

/-- **Bridge.** `b(n) = (-1)^n d(2n)`: the cosine e.g.f. coefficients are the
sign-twisted even coefficients of `H(e^x - 1)`. -/
theorem glaisherB_eq (n : ℕ) : glaisherB n = (-1) ^ n * chiTransform (2 * n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [glaisherB, chiTransform_zero]
    · rw [glaisherB, chiTransform_even_rec, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [ih (n - k) (by omega)]
      have hpow : ((-1 : ℤ) ^ (n + 1)) = -((-1) ^ k * (-1) ^ (n - k)) := by
        rw [← pow_add, Nat.add_sub_cancel' hkn, pow_succ]
        ring
      rw [hpow]
      ring

/-- Glaisher's `H'` numbers (A002114, offset 1): `a(n) = b(n) / 2`. -/
def a002114 (n : ℕ) : ℤ := glaisherB n / 2

/-- The division defining `a002114` is exact on the entry's range `n ≥ 1`. -/
theorem two_mul_a002114 {n : ℕ} (hn : 1 ≤ n) : 2 * a002114 n = glaisherB n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a002114, glaisherB, Int.mul_ediv_cancel_left _ (by norm_num)]

-- Ground truth against the DATA line `1, 11, 301, 15371`.
example : a002114 1 = 1 := by simp [a002114, glaisherB]
example : a002114 2 = 11 := by
  simp [a002114, glaisherB, Finset.sum_range_succ, Nat.choose]
example : a002114 3 = 301 := by
  simp [a002114, glaisherB, Finset.sum_range_succ, Nat.choose]
example : a002114 4 = 15371 := by
  simp [a002114, glaisherB, Finset.sum_range_succ, Nat.choose]

/-- `φ(2k) ∣ 2 φ(k)`. -/
theorem totient_two_mul_dvd (k : ℕ) : Nat.totient (2 * k) ∣ 2 * Nat.totient k := by
  have h := Nat.totient_gcd_mul_totient_mul 2 k
  have hg : Nat.gcd 2 k ∣ 2 := Nat.gcd_dvd_left 2 k
  calc Nat.totient (2 * k) ∣ Nat.totient (Nat.gcd 2 k) * Nat.totient (2 * k) :=
        Dvd.intro_left _ rfl
    _ = Nat.totient k * Nat.gcd 2 k := by rw [h, Nat.totient_two, one_mul]
    _ ∣ Nat.totient k * 2 := Nat.mul_dvd_mul_left _ hg
    _ = 2 * Nat.totient k := mul_comm _ _

/-- An eventual period `Q` modulo `k` yields every multiple `t Q` as one. -/
theorem chiTransform_period_mul (k N Q : ℕ)
    (hN : ∀ m : ℕ, N ≤ m → (chiTransform (m + Q) : ZMod k) = (chiTransform m : ZMod k)) :
    ∀ t m : ℕ, N ≤ m → (chiTransform (m + t * Q) : ZMod k) = (chiTransform m : ZMod k) := by
  intro t
  induction t with
  | zero => intro m _; simp
  | succ t ih =>
    intro m hm
    rw [show m + (t + 1) * Q = m + t * Q + Q by ring, hN _ (by omega), ih m hm]

/-- `d(2j) = (-1)^j b(j)`. -/
theorem chiTransform_two_mul (j : ℕ) : chiTransform (2 * j) = (-1) ^ j * glaisherB j := by
  rw [glaisherB_eq, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- **Bala's conjecture (A002114, Peter Bala, Oct 03 2026), proved.**

Verbatim: "Conjecture: more generally, reducing the sequence modulo a positive
integer k produces an eventually periodic sequence with period dividing
phi(k)."

Formal reading: for every `k ≥ 1` there is `N` such that
`a(n + φ(k)) ≡ a(n) (mod k)` for all `n ≥ N`.  The entry records only the
prime case `k = p`; this theorem covers every positive modulus. -/
theorem a002114_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (a002114 (n + Nat.totient k) : ZMod k) = (a002114 n : ZMod k) := by
  obtain ⟨N, hN⟩ := OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic chi
    (2 * k) (by omega)
  obtain ⟨t, ht⟩ := totient_two_mul_dvd k
  refine ⟨N + 1, fun n hn => ?_⟩
  set P := Nat.totient k with hP
  have hper := chiTransform_period_mul (2 * k) N (Nat.totient (2 * k)) hN t (2 * n) (by omega)
  rw [show 2 * n + t * Nat.totient (2 * k) = 2 * (n + P) by rw [mul_comm t, ← ht]; ring,
    chiTransform_two_mul, chiTransform_two_mul,
    ← two_mul_a002114 (by omega : 1 ≤ n + P), ← two_mul_a002114 (by omega : 1 ≤ n),
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hper
  have h2k : (2 : ℤ) * k ∣ 2 * ((-1) ^ n * a002114 n - (-1) ^ (n + P) * a002114 (n + P)) := by
    push_cast at hper
    convert hper using 1
    ring
  have hk1 : (k : ℤ) ∣ (-1) ^ n * a002114 n - (-1) ^ (n + P) * a002114 (n + P) :=
    Int.dvd_of_mul_dvd_mul_left (by norm_num) h2k
  have hk2 : (k : ℤ) ∣ a002114 n - (-1) ^ P * a002114 (n + P) := by
    have hmul := Dvd.dvd.mul_left hk1 ((-1) ^ n)
    have hsq : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    have heq : (-1) ^ n * ((-1) ^ n * a002114 n - (-1) ^ (n + P) * a002114 (n + P)) =
        a002114 n - (-1) ^ P * a002114 (n + P) := by
      rw [pow_add]
      linear_combination (a002114 n - (-1) ^ P * a002114 (n + P)) * hsq
    rwa [heq] at hmul
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases Nat.even_or_odd P with hev | hodd
  · rwa [hev.neg_one_pow, one_mul] at hk2
  · have hle : k ≤ 2 := by
      by_contra hlt
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.totient_even (by omega))
    have hk2' : (k : ℤ) ∣ 2 := by interval_cases k <;> norm_num
    rw [hodd.neg_one_pow] at hk2
    have h2a : (k : ℤ) ∣ 2 * a002114 n := Dvd.dvd.mul_right hk2' _
    have heq2 : a002114 n - a002114 (n + P) =
        2 * a002114 n - (a002114 n - (-1) * a002114 (n + P)) := by ring
    rw [heq2]
    exact dvd_sub h2a hk2

/-- Integer form of `(2 cos x - 1) B(x) = 1` at `x^(2N)`. -/
theorem glaisherB_cos_rec (N : ℕ) :
    ∑ j ∈ range (N + 1), ((2 * N).choose (2 * j) : ℤ) *
      (2 * (-1) ^ j - if j = 0 then 1 else 0) * glaisherB (N - j) =
      if N = 0 then 1 else 0 := by
  rcases N with _ | n
  · simp [glaisherB]
  · rw [Finset.sum_range_succ', if_neg (Nat.succ_ne_zero n)]
    have hterm : ∀ j ∈ range (n + 1),
        ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
          (2 * (-1) ^ (j + 1) - if j + 1 = 0 then 1 else 0) * glaisherB (n + 1 - (j + 1)) =
        -2 * ((-1) ^ j * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * glaisherB (n - j)) := by
      intro j _
      rw [if_neg (Nat.succ_ne_zero j), show n + 1 - (j + 1) = n - j by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Nat.sub_zero, glaisherB]
    simp

/-- The even exponential generating function `B(x) = ∑ b(n) x^(2n) / (2n)!`. -/
noncomputable def glaisherBEGF : PowerSeries ℚ :=
  PowerSeries.mk fun m => if Even m then (glaisherB (m / 2) : ℚ) / (m.factorial : ℚ) else 0

/-- Integer weight of `x^i / i!` in `2 cos x - 1` for even `i`. -/
def cosWeight (j : ℕ) : ℤ := 2 * (-1) ^ j - if j = 0 then 1 else 0

/-- `[x^i] (2 cos x - 1) = cosWeight (i/2) / i!` for even `i`, and `0` for odd `i`. -/
theorem coeff_two_cos_sub_one (i : ℕ) :
    coeff i (2 * cos ℚ - 1) =
      if Even i then (cosWeight (i / 2) : ℚ) / (i.factorial : ℚ) else 0 := by
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  rw [two_mul, map_sub, map_add, coeff_one]
  simp only [cos, coeff_mk, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases he : Even i
  · rw [if_pos he, if_pos he]
    rcases i with _ | i
    · simp [cosWeight]
    · rw [if_neg (Nat.succ_ne_zero i), cosWeight, if_neg (by
        obtain ⟨r, hr⟩ := he
        omega)]
      push_cast
      ring
  · rw [if_neg he, if_neg he, if_neg (by rintro rfl; exact he Even.zero)]
    simp

/-- `(2 cos x - 1) B(x) = 1`: the recurrence-defined `b` has the entry's e.g.f. -/
theorem cos_mul_glaisherBEGF : (2 * cos ℚ - 1) * glaisherBEGF = 1 := by
  ext m
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (2 * cos ℚ - 1) * coeff j glaisherBEGF), coeff_one]
  simp only [coeff_two_cos_sub_one, glaisherBEGF, coeff_mk]
  rcases Nat.even_or_odd m with ⟨N, hN⟩ | hodd
  · rw [show m = 2 * N by omega] at *
    rw [sum_range_two_mul_add_one]
    have hoddz : ∑ j ∈ range N, ((if Even (2 * j + 1) then
        (cosWeight ((2 * j + 1) / 2) : ℚ) / ((2 * j + 1).factorial : ℚ) else 0) *
        (if Even (2 * N - (2 * j + 1)) then (glaisherB ((2 * N - (2 * j + 1)) / 2) : ℚ) /
          ((2 * N - (2 * j + 1)).factorial : ℚ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (by simp), zero_mul]
    rw [hoddz, add_zero]
    have hfac : ((2 * N).factorial : ℚ) ≠ 0 := by exact_mod_cast (2 * N).factorial_ne_zero
    have hterm : ∀ j ∈ range (N + 1),
        (if Even (2 * j) then (cosWeight (2 * j / 2) : ℚ) / ((2 * j).factorial : ℚ) else 0) *
        (if Even (2 * N - 2 * j) then (glaisherB ((2 * N - 2 * j) / 2) : ℚ) /
          ((2 * N - 2 * j).factorial : ℚ) else 0) =
        (((2 * N).choose (2 * j) : ℤ) * cosWeight j * glaisherB (N - j) : ℚ) /
          ((2 * N).factorial : ℚ) := by
      intro j hj
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : 2 * N - 2 * j = 2 * (N - j) := by omega
      rw [if_pos (even_two_mul j), hsub, if_pos (even_two_mul _),
        Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos]
      have hfacq : ((2 * N).choose (2 * j) : ℚ) * ((2 * j).factorial : ℚ) *
          ((2 * (N - j)).factorial : ℚ) = ((2 * N).factorial : ℚ) := by
        rw [← hsub]
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
      have h1 : ((2 * j).factorial : ℚ) ≠ 0 := by exact_mod_cast (2 * j).factorial_ne_zero
      have h2 : ((2 * (N - j)).factorial : ℚ) ≠ 0 := by
        exact_mod_cast (2 * (N - j)).factorial_ne_zero
      have h3 : ((2 * N).choose (2 * j) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      rw [← hfacq]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    have hrec := congrArg (fun z : ℤ => (z : ℚ)) (glaisherB_cos_rec N)
    push_cast at hrec
    rw [div_eq_iff hfac]
    simp only [cosWeight]
    push_cast
    rw [hrec]
    rcases N with _ | N <;> simp
  · rw [if_neg (by rintro rfl; exact (Nat.not_odd_iff_even.mpr Even.zero) hodd)]
    apply Finset.sum_eq_zero
    intro i hi
    have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases he : Even i
    · have hno : ¬ Even (m - i) := by
        rw [Nat.not_even_iff_odd]
        exact Nat.Odd.sub_even hle hodd he
      rw [if_neg hno, mul_zero]
    · rw [if_neg he, zero_mul]

/-- The literal e.g.f. `1 / (2 (2 cos x - 1))` is `B(x) / 2`. -/
theorem inv_two_mul_two_cos_sub_one :
    (2 * (2 * cos ℚ - 1))⁻¹ = PowerSeries.C (1 / 2 : ℚ) * glaisherBEGF := by
  have hconst : constantCoeff (2 * (2 * cos ℚ - 1)) ≠ 0 := by
    have hcos : constantCoeff (cos ℚ) = 1 := by simp [cos]
    rw [map_mul, map_sub, map_mul, map_one, map_ofNat constantCoeff 2, hcos]
    norm_num
  rw [PowerSeries.inv_eq_iff_mul_eq_one hconst]
  have h2 : PowerSeries.C (1 / 2 : ℚ) * 2 = 1 := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from
      (map_ofNat PowerSeries.C 2).symm, ← map_mul]
    norm_num
  calc PowerSeries.C (1 / 2 : ℚ) * glaisherBEGF * (2 * (2 * cos ℚ - 1)) =
      (PowerSeries.C (1 / 2 : ℚ) * 2) * ((2 * cos ℚ - 1) * glaisherBEGF) := by ring
    _ = 1 := by rw [h2, cos_mul_glaisherBEGF, one_mul]

/-- **Definition check.** For `n ≥ 1`, `a(n) = (2n)! [x^(2n)] 1/(2(2 cos x - 1))`,
the defining e.g.f. of A002114. -/
theorem a002114_eq_egf_coeff {n : ℕ} (hn : 1 ≤ n) :
    (a002114 n : ℚ) = ((2 * n).factorial : ℚ) * coeff (2 * n) ((2 * (2 * cos ℚ - 1))⁻¹) := by
  rw [inv_two_mul_two_cos_sub_one, coeff_C_mul, glaisherBEGF, coeff_mk,
    if_pos (even_two_mul n), Nat.mul_div_cancel_left _ two_pos, ← two_mul_a002114 hn]
  have hf : ((2 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast (2 * n).factorial_ne_zero
  push_cast
  field_simp

/-- Satisfiability of the hypothesis at the entry's worked modulus `k = 13`. -/
example : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (a002114 (n + Nat.totient 13) : ZMod 13) = (a002114 n : ZMod 13) :=
  a002114_eventuallyPeriodic 13 (by norm_num)

end Candidates.A002114GlaisherCosPeter
