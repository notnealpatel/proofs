/-
# A276371 — Bala: `a(n) mod k` is eventually periodic with period dividing `φ(k)`

## OEIS source (retrieved with `oeis show A276371`, 2026-10-21)

```
NAME:     Expansion of e.g.f. exp(x/2)/(2 - exp(2*x))^(1/4).
TERMS:    1,1,3,19,177,2161,32643,587539,12273537,291853441,7782998883,
          230028553459,7462717994097,263654454838321,...
COMMENT (the conjecture):
  Conjecture: the sequence a(n) taken modulo a positive integer k is eventually
  periodic with the period dividing phi(k). For example, the sequence taken
  modulo 21 begins [1, 1, 3, 19, 9, 19, 9, 1, 3, 19, 9, 19, 9, 1, 3, 19, 9, 19,
  9, ...] with an apparent period of 6 (= phi(21)/2) starting at n = 1.
  - _Peter Bala_, Oct 23 2025
FORMULA (used as the definition below):
  a(0) = 1; a(n) = a(n-1) + Sum_{k=1..n-1} 2^k * binomial(n-1,k) * a(n-k).
  - _Seiichi Manyama_, Nov 16 2023
```

No later comment in the entry retracts or corrects the conjecture.

## Status

This module **refutes** the conjecture.  Modulo `k = 4` the sequence is
`1, 1, 3, 3, 1, 1, 3, 3, ...` from `n = 0`: its exact period is `4`, which does
not divide `φ(4) = 2`.  The mechanism: modulo `4` every term of the recurrence
with `2^k`, `k ≥ 2`, vanishes, so `a(n+1) ≡ (2n+1) a(n) (mod 4)`.

## Definition fidelity

`a` is defined by Manyama's recurrence (shifted to `n + 1`).  The e.g.f.
definition of the entry is connected by `egf_pow_four_mul` and `egf_unique`:
the e.g.f. `A(x) = Σ a(n) xⁿ / n!` is the unique power series over `ℚ` with
constant term `1` such that `A⁴ · (2 - e^{2x}) = e^{2x}`, which is the
fractional-power-free form of `A = exp(x/2) / (2 - exp(2x))^(1/4)` (note
`exp(x/2)⁴ = e^{2x}`; constant term `1` selects the principal fourth root).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A276371Refutation

open PowerSeries

/-! ## Definition layer -/

/-- OEIS A276371, via Manyama's recurrence:
`a(0) = 1`, `a(n+1) = a(n) + Σ_{k=1}^{n} 2^k · C(n,k) · a(n+1-k)`.
The summation index is shifted (`k ↦ k + 1`, `k < n`), so `a (n - k)` is
`a(n + 1 - (k + 1))` with `k < n`; the natural subtraction never truncates. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => a n + ∑ k ∈ Finset.range n, 2 ^ (k + 1) * (n.choose (k + 1) : ℤ) * a (n - k)
decreasing_by all_goals omega

/-- The defining recurrence of `a` as an equation. -/
theorem a_succ (n : ℕ) : a (n + 1) =
    a n + ∑ k ∈ Finset.range n, 2 ^ (k + 1) * (n.choose (k + 1) : ℤ) * a (n - k) := by
  rw [a]

-- Ground truth: the first twelve listed terms of A276371.
example : (List.range 12).map a = [1, 1, 3, 19, 177, 2161, 32643, 587539, 12273537,
    291853441, 7782998883, 230028553459] := by
  decide +kernel

/-! ## Fidelity bridge to the e.g.f. -/

/-- The exponential generating function `Σ a(n) xⁿ / n!` of A276371 over `ℚ`. -/
noncomputable def egf : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- The power series `e^{2x} = Σ 2ⁿ xⁿ / n!`. -/
noncomputable def expTwo : ℚ⟦X⟧ := rescale (2 : ℚ) (exp ℚ)

/-- Coefficients of `e^{2x}`. -/
theorem coeff_expTwo (n : ℕ) : coeff n expTwo = 2 ^ n / n.factorial := by
  simp [expTwo, coeff_rescale, coeff_exp, div_eq_mul_inv]

/-- `d/dx e^{2x} = 2 e^{2x}`. -/
theorem derivative_expTwo : d⁄dX ℚ expTwo = 2 * expTwo := by
  ext n
  rw [coeff_derivative, coeff_expTwo, show (2 : ℚ⟦X⟧) = C (2 : ℚ) from rfl, coeff_C_mul,
    coeff_expTwo, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The derivative of the e.g.f. is the e.g.f. of the shifted sequence. -/
theorem derivative_egf :
    d⁄dX ℚ egf = PowerSeries.mk fun n => (a (n + 1) : ℚ) / n.factorial := by
  ext n
  rw [coeff_derivative, egf, coeff_mk, coeff_mk, Nat.factorial_succ]
  push_cast
  field_simp

/-- The recurrence summed over the full binomial range:
`Σ_{k=0}^{n} 2^k C(n,k) a(n-k+1) = 2 a(n+1) - a(n)`. -/
theorem sum_choose_mul_a (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 2 ^ k * (n.choose k : ℤ) * a (n - k + 1)
      = 2 * a (n + 1) - a n := by
  rw [Finset.sum_range_succ', a_succ]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  have hterm : ∀ k ∈ Finset.range n,
      2 ^ (k + 1) * (n.choose (k + 1) : ℤ) * a (n - (k + 1) + 1)
        = 2 ^ (k + 1) * (n.choose (k + 1) : ℤ) * a (n - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n - (k + 1) + 1 = n - k by omega]
  rw [Finset.sum_congr rfl hterm, a_succ]
  ring

/-- The e.g.f. satisfies the linear ODE `(2 - e^{2x}) A' = A`. -/
theorem egf_ode : (2 - expTwo) * d⁄dX ℚ egf = egf := by
  ext n
  have hsum := sum_choose_mul_a n
  rw [sub_mul, map_sub, derivative_egf, show (2 : ℚ⟦X⟧) = C (2 : ℚ) from rfl, coeff_C_mul,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk, coeff_expTwo, egf]
  have hterm : ∀ k ∈ Finset.range (n + 1), (2 : ℚ) ^ k / k.factorial *
      ((a (n - k + 1) : ℚ) / (n - k).factorial)
        = (2 ^ k * (n.choose k : ℤ) * a (n - k + 1) : ℤ) / n.factorial := by
    intro k hk
    rw [Finset.mem_range] at hk
    push_cast
    rw [Nat.cast_choose ℚ (by omega : k ≤ n)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Int.cast_sum, hsum]
  push_cast
  field_simp
  ring

/-- The e.g.f. has constant term `a(0) = 1`. -/
theorem constantCoeff_egf : constantCoeff egf = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, egf, coeff_mk]
  simp [a]

/-- `e^{2x}` has constant term `1`. -/
theorem constantCoeff_expTwo : constantCoeff expTwo = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expTwo]
  simp

/-- **E.g.f. identity.** `A(x)⁴ · (2 - e^{2x}) = e^{2x}`, i.e. the e.g.f. of
`a` is `exp(x/2) / (2 - exp(2x))^(1/4)` in fractional-power-free form. -/
theorem egf_pow_four_mul : egf ^ 4 * (2 - expTwo) = expTwo := by
  set F : ℚ⟦X⟧ := egf ^ 4 * (2 - expTwo) - expTwo with hF
  have hdF : d⁄dX ℚ F = 2 * F := by
    have h2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := Derivation.map_natCast _ 2
    rw [hF, map_sub, Derivation.leibniz, map_sub, derivative_pow, h2, derivative_expTwo]
    simp only [smul_eq_mul]
    have hode := egf_ode
    push_cast
    linear_combination (4 * egf ^ 3) * hode
  have hF0 : F = 0 := by
    ext n
    induction n with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, hF, map_sub, map_mul, map_pow, map_sub,
        constantCoeff_egf, constantCoeff_expTwo, map_ofNat]
      norm_num
    | succ n ih =>
      have hn := congrArg (coeff n) hdF
      rw [coeff_derivative, show (2 : ℚ⟦X⟧) = C (2 : ℚ) from rfl, coeff_C_mul, ih] at hn
      rw [map_zero]
      have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
      simpa [hne] using hn
  exact sub_eq_zero.mp hF0

/-- **Uniqueness.** Any power series `B` over `ℚ` with constant term `1` and
`B⁴ · (2 - e^{2x}) = e^{2x}` is the e.g.f. of `a`.  Hence `a` is exactly the
sequence `n! [xⁿ] exp(x/2) / (2 - exp(2x))^(1/4)` of the entry. -/
theorem egf_unique (B : ℚ⟦X⟧) (hB0 : constantCoeff B = 1)
    (hB : B ^ 4 * (2 - expTwo) = expTwo) : B = egf := by
  have hne : (2 - expTwo : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    rw [map_sub, constantCoeff_expTwo, map_zero, map_ofNat] at hc
    norm_num at hc
  have h4 : B ^ 4 = egf ^ 4 :=
    mul_right_cancel₀ hne (hB.trans egf_pow_four_mul.symm)
  have hfac : (B - egf) * ((B + egf) * (B ^ 2 + egf ^ 2)) = 0 := by
    linear_combination h4
  have hs : B + egf ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    rw [map_add, hB0, constantCoeff_egf, map_zero] at hc
    norm_num at hc
  have hq : B ^ 2 + egf ^ 2 ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    rw [map_add, map_pow, map_pow, hB0, constantCoeff_egf, map_zero] at hc
    norm_num at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (mul_ne_zero hs hq))

/-! ## The conjecture -/

/-- **Bala's conjecture (A276371, Peter Bala, Oct 23 2025).**

Verbatim: "Conjecture: the sequence a(n) taken modulo a positive integer k is
eventually periodic with the period dividing phi(k)."

Formalized in its weakest reading: for every `k ≥ 1` there are a threshold `N`
and a positive period `P ∣ φ(k)` with `a(n + P) ≡ a(n) (mod k)` for all
`n ≥ N`.  (Any stronger reading, e.g. that the *minimal* eventual period divides
`φ(k)`, implies this one, so its refutation refutes them all.) -/
def BalaConjecture : Prop :=
  ∀ k : ℕ, 0 < k → ∃ N P : ℕ, 0 < P ∧ P ∣ Nat.totient k ∧
    ∀ n : ℕ, N ≤ n → a (n + P) ≡ a n [ZMOD k]

-- Satisfiability of the conjecture's body at `k = 3` (`φ(3) = 2`): the witness
-- `N = 1`, `P = 2` meets the side conditions and the first congruence
-- `a(3) ≡ a(1) (mod 3)`, so the claim is not vacuous.
example : ∃ N P : ℕ, 0 < P ∧ P ∣ Nat.totient 3 ∧ a (N + P) ≡ a N [ZMOD 3] :=
  ⟨1, 2, by norm_num, by decide, by decide +kernel⟩

/-! ## The refutation -/

/-- Modulo `4`, `a(n+1) ≡ (2n+1) a(n)`: every recurrence term with `2^k`,
`k ≥ 2`, vanishes. -/
theorem a_succ_modEq_four (n : ℕ) : a (n + 1) ≡ (2 * n + 1) * a n [ZMOD 4] := by
  rw [a_succ]
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    have h4 : (4 : ℤ) ∣ ∑ k ∈ Finset.range m,
        2 ^ (k + 1 + 1) * ((m + 1).choose (k + 1 + 1) : ℤ) * a (m + 1 - (k + 1)) := by
      apply Finset.dvd_sum
      intro k _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ⟨2 ^ k, by ring⟩ _) _
    obtain ⟨c, hc⟩ := h4
    rw [hc]
    simp only [zero_add, pow_one, Nat.choose_one_right, Nat.sub_zero, Nat.cast_add,
      Nat.cast_one]
    exact Int.modEq_iff_dvd.mpr ⟨-c, by ring⟩

/-- `a(n) mod 4` is `1` when `n ≡ 0, 1 (mod 4)` and `3` when `n ≡ 2, 3 (mod 4)`. -/
theorem a_emod_four (n : ℕ) : a n % 4 = if n % 4 < 2 then 1 else 3 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have h := a_succ_modEq_four n
    unfold Int.ModEq at h
    rw [h, Int.mul_emod, ih]
    have hn : ((2 * (n : ℤ) + 1) % 4) = if n % 2 = 0 then 1 else 3 := by
      split_ifs with h2 <;> omega
    rw [hn]
    split_ifs <;> omega

/-- Modulo `4`, the sequence has period `4` from `n = 0`. -/
theorem a_add_four_modEq (n : ℕ) : a (n + 4) ≡ a n [ZMOD 4] := by
  unfold Int.ModEq
  rw [a_emod_four, a_emod_four, Nat.add_mod_right]

/-- Modulo `4`, two steps never return: `a(n + 2) ≢ a(n) (mod 4)` for every `n`,
so no eventual period of `a mod 4` divides `2`. -/
theorem a_add_two_not_modEq (n : ℕ) : ¬ a (n + 2) ≡ a n [ZMOD 4] := by
  unfold Int.ModEq
  rw [a_emod_four, a_emod_four]
  split_ifs <;> omega

/-- **Bala's conjecture for A276371 is false.**

Counterexample: `k = 4`.  Here `φ(4) = 2`, but `a(n) mod 4` runs
`1, 1, 3, 3, 1, 1, 3, 3, ...` (`a_emod_four`), with exact period `4`
(`a_add_four_modEq`, `a_add_two_not_modEq`).  A period `P ∣ 2` would make
`a(N + 2) ≡ a(N) (mod 4)`, which never holds.

In a sample of moduli (all `k ≤ 1000` with a period found within the search
window, per the triage computation, and a spot check of `k ∈ {2,3,5,7,8,9,12,
16,20,21,24,25,27,32,64}`) the claim held for every `k ≠ 4`; the author
probably intended the statement for `k ≠ 4` (this restricted form is neither
claimed nor proved here). -/
theorem balaConjecture_false : ¬ BalaConjecture := by
  intro hconj
  obtain ⟨N, P, hP, hPdvd, hper⟩ := hconj 4 (by norm_num)
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hPdvd
  have hP12 : P = 1 ∨ P = 2 := by
    have hle : P ≤ 2 := Nat.le_of_dvd (by norm_num) hPdvd
    omega
  have hstep : a (N + 2) ≡ a N [ZMOD 4] := by
    rcases hP12 with h1 | h2
    · subst h1
      exact (hper (N + 1) (by omega)).trans (hper N le_rfl)
    · subst h2
      exact hper N le_rfl
  exact a_add_two_not_modEq N hstep

end Candidates.A276371Refutation
