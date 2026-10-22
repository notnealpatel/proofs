/-
# A145656: Bala's logarithmic-integral formula

OEIS A145656 defines `a(n)` as the numerator of
`A(n) = ∑_{d=1}^{n-1} 2^(n-d)/d` (the entry's genus-1 polynomial at `m = 2`).
Peter Bala's conjecture (2024-06-10) identifies it with the numerator of
`2^n log 2 - 2^(n+1) ∫₀¹ x^(2n-1)/(1+x²)^n dx`.

The real expression equals the rational `A(n)`. The final statement
exhibits a rational representative and proves that every rational
representative has numerator `a(n)`; no numerator operation on arbitrary
reals is assumed. The source offset requires `1 ≤ n`, excluding truncation
of the integrand exponent at `n = 0`. In the finite sum, `d < n` likewise
keeps the natural exponent `n-d` untruncated.

For `J m = ∫₀¹ x^(2m+1)/(1+x²)^(m+1) dx`, an explicit antiderivative gives
`J (m+1) = J m - (1/2)^(m+1)/(2(m+1))`, with `J 0 = log 2 / 2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A145656NumeratorLogSum

open intervalIntegral

/-! ## Definition layer -/

/-- The entry's polynomial `A[1,n](m) = Sum_{d = 1..n-1} m^(n-d)/d` at
`m = 2`, as an exact rational. -/
def A (n : ℕ) : ℚ := ∑ d ∈ Finset.Ico 1 n, (2 : ℚ) ^ (n - d) / d

/-- A145656: `a(n)` is the numerator of `Sum_{d = 1..n-1} 2^(n-d)/d`. -/
def a (n : ℕ) : ℤ := (A n).num

/-- Bala's real expression
`2^n log 2 - 2^(n+1) ∫₀¹ x^(2n-1)/(1+x²)^n dx`. -/
noncomputable def logIntegralExpr (n : ℕ) : ℝ :=
  2 ^ n * Real.log 2 - 2 ^ (n + 1) * ∫ x in (0 : ℝ)..1, x ^ (2 * n - 1) / (1 + x ^ 2) ^ n

-- Examples: the first twelve terms of the DATA line.
example : (List.range 12).map (fun i => a (i + 1)) =
    [0, 2, 5, 32, 131, 661, 1327, 18608, 148969, 447047, 89422, 1967410] := by
  decide +kernel

-- Examples: the entry's displayed polynomials at `m = 2`.
example : A 1 = 0 ∧ A 2 = 2 ∧ A 3 = 2 / 2 + 2 ^ 2 ∧ A 4 = 2 / 3 + 2 ^ 2 / 2 + 2 ^ 3 := by
  decide +kernel

/-! ## Integral lemmas -/

/-- `1 + x²` is positive. -/
lemma one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

/-- The integrand `x^(2m+1)/(1+x²)^(m+1)` is continuous. -/
lemma continuous_integrand (m : ℕ) :
    Continuous fun x : ℝ => x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 1) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (pow_pos (one_add_sq_pos x) _).ne'

/-- The correction term `x^(2m+1)/(1+x²)^(m+2)` is continuous. -/
lemma continuous_correction (m : ℕ) :
    Continuous fun x : ℝ => x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 2) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (pow_pos (one_add_sq_pos x) _).ne'

/-- Base case: `∫₀¹ x/(1+x²) dx = log 2 / 2`. -/
lemma integral_base :
    ∫ x in (0 : ℝ)..1, x ^ (2 * 0 + 1) / (1 + x ^ 2) ^ (0 + 1) = Real.log 2 / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2) / 2)
        (x ^ (2 * 0 + 1) / (1 + x ^ 2) ^ (0 + 1)) x := by
    intro x _
    have hx : (1 + x ^ 2) ≠ 0 := (one_add_sq_pos x).ne'
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2) / 2)
        (2 * x / (1 + x ^ 2) / 2) x :=
      (h1.log hx).div_const 2
    refine h2.congr_deriv ?_
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv ((continuous_integrand 0).intervalIntegrable _ _)]
  norm_num

/-- The correction integral:
`∫₀¹ x^(2m+1)/(1+x²)^(m+2) dx = (1/2)^(m+1) / (2(m+1))`, via the
antiderivative `(x²/(1+x²))^(m+1) / (2(m+1))`. -/
lemma integral_correction (m : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 2)
      = (1 / 2 : ℝ) ^ (m + 1) / (2 * (m + 1)) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => (y ^ 2 / (1 + y ^ 2)) ^ (m + 1) / (2 * (m + 1)))
        (x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 2)) x := by
    intro x _
    have hx : (1 + x ^ 2) ≠ 0 := (one_add_sq_pos x).ne'
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have h0 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have hq : HasDerivAt (fun y : ℝ => y ^ 2 / (1 + y ^ 2))
        ((2 * x * (1 + x ^ 2) - x ^ 2 * (2 * x)) / (1 + x ^ 2) ^ 2) x := h0.div h1 hx
    have h2 : HasDerivAt (fun y : ℝ => (y ^ 2 / (1 + y ^ 2)) ^ (m + 1) / (2 * (m + 1)))
        ((m + 1 : ℕ) * (x ^ 2 / (1 + x ^ 2)) ^ m *
          ((2 * x * (1 + x ^ 2) - x ^ 2 * (2 * x)) / (1 + x ^ 2) ^ 2) / (2 * (m + 1))) x := by
      simpa using (hq.pow (m + 1)).div_const (2 * ((m : ℝ) + 1))
    refine h2.congr_deriv ?_
    push_cast
    rw [div_pow]
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv ((continuous_correction m).intervalIntegrable _ _)]
  norm_num

/-- Pointwise recurrence of the integrands:
`x^(2m+3)/(1+x²)^(m+2) = x^(2m+1)/(1+x²)^(m+1) - x^(2m+1)/(1+x²)^(m+2)`. -/
lemma integrand_succ (m : ℕ) (x : ℝ) :
    x ^ (2 * (m + 1) + 1) / (1 + x ^ 2) ^ (m + 1 + 1)
      = x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 1) - x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 2) := by
  have hx : (1 + x ^ 2) ≠ 0 := (one_add_sq_pos x).ne'
  field_simp
  ring

/-- Closed form: `∫₀¹ x^(2m+1)/(1+x²)^(m+1) dx = log 2 / 2 - Σ_{d<m} (1/2)^(d+1)/(2(d+1))`. -/
lemma integral_closed_form (m : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 1)
      = Real.log 2 / 2 - ∑ d ∈ Finset.range m, (1 / 2 : ℝ) ^ (d + 1) / (2 * (d + 1)) := by
  induction m with
  | zero => simpa using integral_base
  | succ m ih =>
    have hsplit : ∫ x in (0 : ℝ)..1, x ^ (2 * (m + 1) + 1) / (1 + x ^ 2) ^ (m + 1 + 1)
        = (∫ x in (0 : ℝ)..1, x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 1))
          - ∫ x in (0 : ℝ)..1, x ^ (2 * m + 1) / (1 + x ^ 2) ^ (m + 2) := by
      simp_rw [integrand_succ m]
      exact integral_sub ((continuous_integrand m).intervalIntegrable _ _)
        ((continuous_correction m).intervalIntegrable _ _)
    rw [hsplit, ih, integral_correction, Finset.sum_range_succ]
    ring

/-! ## The identity and the conjecture -/

/-- **The identity behind Bala's conjecture.** For `1 ≤ n`,
`2^n log 2 - 2^(n+1) ∫₀¹ x^(2n-1)/(1+x²)^n dx = Sum_{d=1}^{n-1} 2^(n-d)/d`. -/
theorem logIntegralExpr_eq (n : ℕ) (hn : 1 ≤ n) : logIntegralExpr n = (A n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hexp : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [logIntegralExpr, hexp, integral_closed_form, A]
  push_cast
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sub, Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.range m, (2 : ℝ) ^ (m + 1 + 1) * ((1 / 2) ^ (i + 1) / (2 * ((i : ℝ) + 1)))
      = ∑ k ∈ Finset.range m, (2 : ℝ) ^ (m + 1 - (1 + k)) / ((1 + k : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < m := Finset.mem_range.mp hk
    have hpow : (2 : ℝ) ^ (m + 1 + 1) = 2 ^ (m + 1 - (1 + k)) * 2 ^ (k + 1) * 2 := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [hpow, one_div_pow]
    push_cast
    field_simp
    ring
  rw [← hsum]
  ring

/-- Bala's conjecture (OEIS A145656, 2024-06-10): for `n ≥ 1`,
`2^n log 2 - 2^(n+1) ∫₀¹ x^(2n-1)/(1+x²)^n dx` has a rational
representative, and every such representative has numerator `a n`. -/
theorem a_eq_num_logIntegralExpr (n : ℕ) (hn : 1 ≤ n) :
    (∃ q : ℚ, (q : ℝ) = logIntegralExpr n) ∧
      ∀ q : ℚ, (q : ℝ) = logIntegralExpr n → q.num = a n := by
  have hA : logIntegralExpr n = (A n : ℝ) := logIntegralExpr_eq n hn
  refine ⟨⟨A n, hA.symm⟩, fun q hq => ?_⟩
  have hqA : q = A n := by exact_mod_cast hq.trans hA
  rw [hqA, a]

-- Non-vacuity: the hypothesis `1 ≤ n` is satisfiable, and at `n = 2` the
-- conjecture pins the numerator `2`.
example : (∃ q : ℚ, (q : ℝ) = logIntegralExpr 2) ∧
    ∀ q : ℚ, (q : ℝ) = logIntegralExpr 2 → q.num = 2 := by
  refine ⟨(a_eq_num_logIntegralExpr 2 (by norm_num)).1, fun q hq => ?_⟩
  rw [(a_eq_num_logIntegralExpr 2 (by norm_num)).2 q hq]
  decide +kernel

end Candidates.A145656NumeratorLogSum
