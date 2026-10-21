/-
# A002050 — Bala: simplices of the barycentric subdivision are eventually periodic mod k

## OEIS source (retrieved with `oeis show A002050`, 2026-10-21)

```
NAME:     Number of simplices in barycentric subdivision of n-simplex.
TERMS:    0,1,5,25,149,1081,9365,94585,1091669,14174521,204495125,3245265145,...
KEYWORDS: nonn,easy,nice
FORMULA:  E.g.f.: (exp(2x)-exp(x))/(2-exp(x)).
FORMULA:  a(n) = 1 + 2*Sum_{k=2..n} k!*Stirling2(n,k), n > 0, a(0)=1.
          - _Vladimir Kruchinin_, Sep 27 2013
          (the DATA line has a(0) = 0, which the e.g.f. confirms; the
          `a(0)=1` in this formula is an entry typo, irrelevant here.)
COMMENT (the conjecture):
  Conjecture: Let k be a positive integer. The sequence obtained by reducing
  a(n) modulo k is eventually periodic with the period dividing
  phi(k) = A000010(k). For example, modulo 9 we obtain the sequence
  [0, 1, 5, 7, 5, 1, 5, 4, 5, 7, 5, 1, 5, 4, 5, 7, 5, 1, 5, 4, 5, 7, 5, ...],
  with an apparent period of 6 = phi(9) beginning at a(5).
  - _Peter Bala_, Aug 03 2023
```

## Status

Triage: proved-elsewhere. The e.g.f. is `G(e^x - 1)` with the ordinary
integral series `G(Y) = Y(1+Y)/(1-Y) = Y + 2Y^2 + 2Y^3 + ...`, so the claim
is the instance `G = mk g` (`g 0 = 0`, `g 1 = 1`, `g m = 2` for `m ≥ 2`) of
the repository theorem
`OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic` (Bala's
A000670 family comment of 2022-07-08, which itself points to A002050). It is
equivalently `a(n) = 2*A000670(n) - 1` for `n ≥ 1`, and eventual periodicity
of the Fubini numbers mod `k` with period dividing `φ(k)` is Poonen (1988).
Nothing here is a novelty claim.

Computation (2026-10-21, Python, `a(n) = 2*fubini(n) - 1`): for every
`1 ≤ k ≤ 300` and `n ≤ 400`, `a(n + φ(k)) ≡ a(n) (mod k)` from `n = 6` on.

## Definitional fidelity

`a` is Kruchinin's Stirling-sum formula (with the DATA-line value
`a 0 = 0`), and `a_eq_factorial_mul_coeff_egf` proves it equals
`n! * [x^n]` of the entry's e.g.f. `(exp(2x) - exp x) * (2 - exp x)⁻¹`
in `ℚ⟦X⟧`, so the conjecture is stated about the entry's own sequence.
The combinatorial NAME (simplex counting) is not formalized; the e.g.f.
FORMULA is the definition used.
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Enumerative.OrdinaryIntegralEGFComposition

set_option autoImplicit false

namespace Candidates.A002050SimplicesBarycentricSubdivision

open PowerSeries Finset

/-! ## Definition layer -/

/-- Ordinary coefficients of `G(Y) = Y(1+Y)/(1-Y) = Y + 2Y^2 + 2Y^3 + ⋯`,
the outer series with `e.g.f. = G(e^x - 1)`. -/
def g : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | _ + 2 => 2

/-- A002050: `a(n) = Σ_{m=0}^{n} g(m) m! S₂(n,m)`, i.e. Kruchinin's
`a(n) = 1 + 2 Σ_{k=2}^{n} k! S₂(n,k)` for `n > 0`, with `a(0) = 0`. -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ range (n + 1), g m * (m.factorial : ℤ) * (n.stirlingSecond m : ℤ)

/-- The entry's e.g.f. `(exp(2x) - exp(x)) / (2 - exp(x))` in `ℚ⟦X⟧`. -/
noncomputable def egf : PowerSeries ℚ :=
  (exp ℚ ^ 2 - exp ℚ) * (2 - exp ℚ)⁻¹

-- Ground truth: the first nine DATA terms.
example : (List.range 9).map a = [0, 1, 5, 25, 149, 1081, 9365, 94585, 1091669] := by
  decide

/-! ## Bridge to the e.g.f. -/

/-- `G(Y) (1 - Y) = Y + Y^2` over `ℤ`, i.e. `G = Y(1+Y)/(1-Y)`. -/
theorem mk_g_mul_one_sub_X : PowerSeries.mk g * (1 - X) = X + X ^ 2 := by
  ext n
  rcases n with _ | _ | _ | n
  · simp [g]
  · simp [mul_sub, g]
  · simp [mul_sub, g, coeff_X_pow, coeff_X]
  · simp [mul_sub, g, coeff_X_pow, coeff_X]

/-- The same identity after casting the coefficients to `ℚ`. -/
theorem map_mk_g_mul_one_sub_X :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk g) * (1 - X) = X + X ^ 2 := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) mk_g_mul_one_sub_X
  simpa only [map_mul, map_sub, map_one, map_X, map_add, map_pow] using h

/-- The entry's e.g.f. is the formal composition `G(exp x - 1)`. -/
theorem egf_eq_subst : egf = PowerSeries.subst (exp ℚ - 1)
    (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk g)) := by
  have hc : constantCoeff (exp ℚ - 1) = 0 := by simp
  have ha : HasSubst (exp ℚ - 1) := HasSubst.of_constantCoeff_zero' hc
  set S : PowerSeries ℚ := PowerSeries.subst (exp ℚ - 1)
    (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk g)) with hS
  have h1 : S * (2 - exp ℚ) = exp ℚ ^ 2 - exp ℚ := by
    have h := congrArg (substAlgHom ha) map_mk_g_mul_one_sub_X
    rw [map_mul, map_sub, map_one, map_add, map_pow, substAlgHom_X,
      coe_substAlgHom] at h
    calc S * (2 - exp ℚ) = S * (1 - (exp ℚ - 1)) := by ring
      _ = (exp ℚ - 1) + (exp ℚ - 1) ^ 2 := h
      _ = exp ℚ ^ 2 - exp ℚ := by ring
  have h2 : constantCoeff (2 - exp ℚ) ≠ 0 := by
    rw [map_sub, map_ofNat, constantCoeff_exp]
    norm_num
  unfold egf
  rw [← h1, mul_assoc, PowerSeries.mul_inv_cancel _ h2, mul_one]

/-- `a n = n! · [xⁿ] (exp(2x) - exp x)/(2 - exp x)`: `a` is the entry's sequence. -/
theorem a_eq_factorial_mul_coeff_egf (n : ℕ) :
    (a n : ℚ) = (n.factorial : ℚ) * coeff n egf := by
  rw [egf_eq_subst, OrdinaryIntegralEGF.factorial_mul_coeff_subst_exp_sub_one]
  simp only [a, OrdinaryIntegralEGF.weightedStirlingTransform, coeff_mk]

-- Ground truth through the e.g.f.: `2! · [x²] egf = 5`.
example : ((Nat.factorial 2 : ℕ) : ℚ) * coeff 2 egf = 5 := by
  rw [← a_eq_factorial_mul_coeff_egf]
  have h : a 2 = 5 := by decide
  rw [h]
  norm_num

/-! ## The conjecture -/

/-- **Bala's conjecture (A002050, Peter Bala, Aug 03 2023), proved.**

Verbatim: "Let k be a positive integer. The sequence obtained by reducing
a(n) modulo k is eventually periodic with the period dividing phi(k)."

Formal reading: for every `k ≥ 1` there is a threshold `N` from which
`φ(k)` is a period of `a mod k`; hence the least eventual period divides
`φ(k)`. Instance of `OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic`
with outer coefficients `g`. -/
theorem a_mod_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (a (n + Nat.totient k) : ZMod k) = (a n : ZMod k) :=
  OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic g k hk

/-- The conjecture in "period dividing `φ(k)`" form, phrased directly on
the integers `n! · [xⁿ] egf`: some positive `P ∣ φ(k)` is an eventual
period modulo `k`. -/
theorem egf_coeff_mod_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = (n.factorial : ℚ) * coeff n egf) ∧
      ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧ ∀ n : ℕ, N ≤ n →
        (b (n + P) : ZMod k) = (b n : ZMod k) := by
  obtain ⟨N, hN⟩ := a_mod_eventuallyPeriodic k hk
  exact ⟨a, a_eq_factorial_mul_coeff_egf, N, Nat.totient k, dvd_rfl,
    Nat.totient_pos.mpr hk, hN⟩

/-! ## Sanity layer -/

-- Bala's example modulo 9 (`φ 9 = 6`): `a 11 ≡ a 5 ≡ 1`.
example : (a (5 + Nat.totient 9) : ZMod 9) = (a 5 : ZMod 9) := by
  have h9 : Nat.totient 9 = 6 := by decide
  rw [h9]
  decide

-- "Eventually" is load-bearing: `a 6 = 9365 ≡ 5 (mod 9)` but `a 0 = 0`.
example : (a (0 + Nat.totient 9) : ZMod 9) ≠ (a 0 : ZMod 9) := by
  have h9 : Nat.totient 9 = 6 := by decide
  rw [h9]
  decide

end Candidates.A002050SimplicesBarycentricSubdivision
