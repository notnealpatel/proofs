/-
# Small counterexamples to the Gaussian Moments Conjecture: `¬ GMC(n)` for `n ≥ 4`

## Source

arXiv 2607.18186, Christopher D. Long, "Small Counterexamples to the Gaussian
Moments Conjecture" (dated July 20, 2026). Retrieved 2026-10-21
(`fetch 2607.18186`, LaTeX source).

Where: Section 1 (statement of `GMC(n)`); Section 3, eqs. `contraction` and
`coefficient-contraction`; Section 4, Proposition 4.1 (the four-variable cubic
`P_4`). The three-variable quartic of Section 5 (Theorem 5.1, Corollary 5.2) is
**not** formalized here.

Verbatim (Section 1):

> Let `X=(X_1,…,X_n)` be a vector of independent standard real Gaussian random
> variables. Derksen, van den Essen, and Zhao formulated the Gaussian Moments
> Conjecture `GMC(n)` as follows: if `P ∈ ℂ[x_1,…,x_n]` satisfies
> `E(P(X)^m)=0 (m ≥ 1)`, then, for every `Q ∈ ℂ[x_1,…,x_n]`, `E(Q(X)P(X)^m)=0`
> for all sufficiently large `m` [DVEZ, Conjecture 1.1].

Verbatim (Section 3):

> Let `X,Y` be independent standard real Gaussians and put `Z=(X+iY)/√2`,
> `W=(X-iY)/√2`. [...] Rotational invariance gives `E(W^a Z^b)=δ_{ab} a!`
> `(a,b ≥ 0)`. Equivalently, for every polynomial `R ∈ ℂ[z]`,
> `E(W^a R(Z)) = a! [z^a] R(z)`.

Verbatim (Section 4):

> Set `P_4=(1+Z_2)(W_1(1-Z_1)+W_2)`, `Q_4=Z_2`. [...]
> **Proposition 4.1.** For every `A ∈ ℂ[z]` and `m ≥ 1`,
> `E(A(Z_2)P_4^m) = m! [z^m] A(z)(1+z)^{m-1}`. In particular,
> `E(P_4^m)=0`, `E(Q_4P_4^m)=m!` `(m ≥ 1)`.

Verbatim (abstract): "We also give a six-term cubic example in four variables,
which was found first and already proves failure for every `n ≥ 4`."

## Status

Proved in the paper (known result). This file is a kernel-checked
formalization of the four-variable refutation; it contains no `sorry`.

## What is formalized

* `integral_Wc_pow_mul_Zc_pow`: the contraction rule `E(W^a Z^b) = δ_{ab} a!`
  for the Gaussian law on `ℝ²` (off-diagonal by Mathlib's rotation invariance
  `IsGaussian.map_rotation_eq_self`; diagonal from `E(X^{2k}) = (2k-1)!!`).
* `integral_Wc_pow_mul_eval_Zc`: the coefficient form `E(W^k R(Z)) = k! [z^k] R`.
* `integral_eval_mul_P4_pow` (Proposition 4.1, master formula), with
  `integral_P4_pow` and `integral_Q4_mul_P4_pow`.
* `GMC n`, stated with `MvPolynomial (Fin n) ℂ` evaluated at a vector of `n`
  independent standard real Gaussians (`Measure.pi` of `gaussianReal 0 1`).
* `not_GMC_four : ¬ GMC 4` and `not_GMC_of_four_le : 4 ≤ n → ¬ GMC n`.

Indices: the paper's `(X_1, Y_1, X_2, Y_2)` are the coordinates `0, 1, 2, 3`.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Complex
open scoped Nat

namespace Candidates.SmallCounterexamplesGaussianMoments


/-- The complex Gaussian coordinate `Z = (X + iY)/√2` of a point `p = (X, Y)` of `ℝ²`. -/
noncomputable def Zc (p : ℝ × ℝ) : ℂ := ((p.1 : ℂ) + p.2 * I) / ((Real.sqrt 2 : ℝ) : ℂ)
/-- The conjugate complex Gaussian coordinate `W = (X - iY)/√2` of a point `p = (X, Y)`
of `ℝ²` (a complex *linear* polynomial in `X, Y`, equal to `conj Z` pointwise). -/
noncomputable def Wc (p : ℝ × ℝ) : ℂ := ((p.1 : ℂ) - p.2 * I) / ((Real.sqrt 2 : ℝ) : ℂ)

/-- The law of a pair `(X, Y)` of independent standard real Gaussians. -/
noncomputable abbrev γ2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- `Z` is continuous. -/
lemma continuous_Zc : Continuous Zc := by unfold Zc; fun_prop
/-- `W` is continuous. -/
lemma continuous_Wc : Continuous Wc := by unfold Wc; fun_prop

/-- Crude growth bound `‖Z(p)‖ ≤ 2‖p‖` (sup norm on `ℝ × ℝ`). -/
lemma norm_Zc_le (p : ℝ × ℝ) : ‖Zc p‖ ≤ 2 * ‖p‖ := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]; norm_num
  have hs : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold Zc
  rw [norm_div, hs, div_le_iff₀ (by linarith)]
  have h1 : ‖(p.1 : ℂ) + p.2 * I‖ ≤ |p.1| + |p.2| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hp1 : |p.1| ≤ ‖p‖ := by simpa using norm_fst_le p
  have hp2 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
  nlinarith [norm_nonneg p]

/-- Crude growth bound `‖W(p)‖ ≤ 2‖p‖` (sup norm on `ℝ × ℝ`). -/
lemma norm_Wc_le (p : ℝ × ℝ) : ‖Wc p‖ ≤ 2 * ‖p‖ := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]; norm_num
  have hs : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold Wc
  rw [norm_div, hs, div_le_iff₀ (by linarith)]
  have h1 : ‖(p.1 : ℂ) - p.2 * I‖ ≤ |p.1| + |p.2| := by
    refine (norm_sub_le _ _).trans ?_
    simp
  have hp1 : |p.1| ≤ ‖p‖ := by simpa using norm_fst_le p
  have hp2 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
  nlinarith [norm_nonneg p]

/-- Every monomial `W^a Z^b` is integrable for the standard Gaussian law on `ℝ²`
(all moments of a Gaussian measure are finite, `IsGaussian.memLp_id`). -/
lemma integrable_Wc_pow_mul_Zc_pow (a b : ℕ) :
    Integrable (fun p => Wc p ^ a * Zc p ^ b) γ2 := by
  have hm : Integrable (fun p : ℝ × ℝ => ‖p‖ ^ (a + b)) γ2 := by
    rcases Nat.eq_zero_or_pos (a + b) with h | h
    · simp [h]
    · exact (IsGaussian.memLp_id γ2 (a + b : ℕ) (by simp)).integrable_norm_pow (by omega)
  refine (hm.const_mul (2 ^ (a + b))).mono' ?_ ?_
  · exact ((continuous_Wc.pow a).mul (continuous_Zc.pow b)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, norm_pow, norm_pow, pow_add, pow_add]
    calc ‖Wc p‖ ^ a * ‖Zc p‖ ^ b ≤ (2 * ‖p‖) ^ a * (2 * ‖p‖) ^ b := by
          gcongr
          · exact norm_Wc_le p
          · exact norm_Zc_le p
      _ = 2 ^ a * 2 ^ b * (‖p‖ ^ a * ‖p‖ ^ b) := by ring

/-- Rotating the plane by `θ` multiplies `W` by `e^{iθ}`. -/
lemma Wc_rotation (θ : ℝ) (p : ℝ × ℝ) :
    Wc (ContinuousLinearMap.rotation θ p) = cexp (θ * I) * Wc p := by
  have he : cexp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [ContinuousLinearMap.rotation_apply, he]
  unfold Wc
  simp only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Rotating the plane by `θ` multiplies `Z` by `e^{-iθ}`. -/
lemma Zc_rotation (θ : ℝ) (p : ℝ × ℝ) :
    Zc (ContinuousLinearMap.rotation θ p) = cexp (-(θ * I)) * Zc p := by
  have he : cexp (-(θ * I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_sin]
    ring
  rw [ContinuousLinearMap.rotation_apply, he]
  unfold Zc
  simp only [smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Off-diagonal case of the contraction rule: `E(W^a Z^b) = 0` for `a ≠ b`, by rotation
invariance of the standard Gaussian law on `ℝ²` (`IsGaussian.map_rotation_eq_self`) applied
at the angle `π/(a-b)`, which multiplies the integrand by `-1`. -/
lemma integral_Wc_pow_mul_Zc_pow_of_ne {a b : ℕ} (hab : a ≠ b) :
    ∫ p, Wc p ^ a * Zc p ^ b ∂γ2 = 0 := by
  set θ : ℝ := Real.pi / ((a : ℝ) - b) with hθ
  have hne : ((a : ℝ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  have hrot : γ2.map (ContinuousLinearMap.rotation θ) = γ2 :=
    IsGaussian.map_rotation_eq_self (μ := gaussianReal 0 1)
      (by simp [integral_id_gaussianReal]) θ
  have key : ∫ p, Wc p ^ a * Zc p ^ b ∂γ2
      = -∫ p, Wc p ^ a * Zc p ^ b ∂γ2 := by
    conv_lhs => rw [← hrot]
    rw [integral_map (f := fun p => Wc p ^ a * Zc p ^ b)
      (ContinuousLinearMap.rotation θ).continuous.measurable.aemeasurable
      ((continuous_Wc.pow a).mul (continuous_Zc.pow b)).aestronglyMeasurable]
    simp_rw [Wc_rotation, Zc_rotation, mul_pow, ← Complex.exp_nat_mul]
    have hc : cexp (↑a * (↑θ * I)) * cexp (↑b * -(↑θ * I)) = -1 := by
      rw [← Complex.exp_add]
      have hexp : (↑a * (↑θ * I) + ↑b * -(↑θ * I) : ℂ) = (Real.pi : ℂ) * I := by
        have hθ' : (θ : ℂ) * ((a : ℂ) - b) = Real.pi := by
          rw [hθ]; push_cast
          have hne' : ((a : ℂ) - b) ≠ 0 := by exact_mod_cast hne
          field_simp
        linear_combination I * hθ'
      rw [hexp, Complex.exp_pi_mul_I]
    calc ∫ p, cexp (↑a * (↑θ * I)) * Wc p ^ a * (cexp (↑b * -(↑θ * I)) * Zc p ^ b) ∂γ2
        = ∫ p, (cexp (↑a * (↑θ * I)) * cexp (↑b * -(↑θ * I))) * (Wc p ^ a * Zc p ^ b) ∂γ2 := by
          congr 1; ext p; ring
      _ = _ := by rw [hc, integral_const_mul]; ring
  linear_combination key / 2

open Real in
/-- Even moments of the standard real Gaussian: `E(T^{2k}) = (2k-1)!!` (paper eq.
`real-gaussian`), via `∫_0^∞ x^{2k} e^{-x²/2} dx` and `Γ(k + 1/2) = (2k-1)!! √π / 2^k`. -/
lemma integral_even_pow_gaussianReal (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) = ((2 * k - 1)‼ : ℝ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul, sub_zero, NNReal.coe_one, mul_one]
  have hfun : (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * x ^ (2 * k))
      = fun x => (√(2 * π))⁻¹ * (fun y : ℝ => y ^ (2 * k) * rexp (-(1 / 2) * y ^ 2)) |x| := by
    ext x
    beta_reduce
    rw [(even_two_mul k).pow_abs, sq_abs]
    ring_nf
  rw [hfun, integral_const_mul,
    integral_comp_abs (f := fun y : ℝ => y ^ (2 * k) * rexp (-(1 / 2) * y ^ 2))]
  have hIoi : ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k) * rexp (-(1 / 2) * x ^ 2)
      = ∫ x in Set.Ioi (0 : ℝ), x ^ ((2 * k : ℕ) : ℝ) * rexp (-(1 / 2) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [Real.rpow_natCast]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hIoi, _root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
    (by have := (Nat.cast_nonneg (2 * k) : (0 : ℝ) ≤ _); linarith) (by norm_num)]
  have hq : (((2 * k : ℕ) : ℝ) + 1) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  rw [hq, Real.Gamma_nat_add_half]
  have hpow : (1 / 2 : ℝ) ^ (-((k : ℝ) + 1 / 2)) = 2 ^ k * √2 := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg,
      Real.rpow_add (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow, one_div]
  have hneg : -(((2 * k : ℕ) : ℝ) + 1) / 2 = -((k : ℝ) + 1 / 2) := by push_cast; ring
  rw [hneg, hpow]
  have h2pi : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
  rw [h2pi]
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hspi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp


/-- `W + Z = √2 · X`. -/
lemma Wc_add_Zc (p : ℝ × ℝ) : Wc p + Zc p = ((Real.sqrt 2 : ℝ) : ℂ) * (p.1 : ℂ) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hsq' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq, hsq]
  unfold Wc Zc
  field_simp
  linear_combination (-(p.1 : ℂ)) * hsq'

/-- `C(2a, a) · a! = 2^a · (2a-1)!!`. -/
lemma choose_mul_factorial_two_mul (a : ℕ) :
    (2 * a).choose a * a ! = 2 ^ a * (2 * a - 1)‼ := by
  have h1 : (2 * a).choose a * a ! * a ! = (2 * a)! := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 2 * a) (k := a) (by omega)
    rwa [show 2 * a - a = a by omega] at this
  have h2 : (2 * a)! = 2 ^ a * a ! * (2 * a - 1)‼ := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rfl
    · have := Nat.factorial_eq_mul_doubleFactorial (2 * a - 1)
      rw [show 2 * a - 1 + 1 = 2 * a by omega, Nat.doubleFactorial_two_mul] at this
      exact this
  have hpos : 0 < a ! := Nat.factorial_pos a
  have h3 : (2 * a).choose a * a ! * a ! = 2 ^ a * (2 * a - 1)‼ * a ! := by
    rw [h1, h2]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

/-- Diagonal case of the contraction rule: `E(W^a Z^a) = a!`. Expanding
`E((W+Z)^{2a}) = 2^a E(X^{2a}) = 2^a (2a-1)!!` binomially, only the term `C(2a,a) E(W^a Z^a)`
survives by the off-diagonal case. -/
lemma integral_Wc_pow_mul_Zc_pow_self (a : ℕ) :
    ∫ p, Wc p ^ a * Zc p ^ a ∂γ2 = (a ! : ℂ) := by
  -- expand `(W + Z)^(2a)` and use off-diagonal vanishing
  have hexp : ∫ p, (Wc p + Zc p) ^ (2 * a) ∂γ2
      = ((2 * a).choose a : ℂ) * ∫ p, Wc p ^ a * Zc p ^ a ∂γ2 := by
    simp_rw [add_pow]
    rw [integral_finsetSum _ (fun m _ =>
      (integrable_Wc_pow_mul_Zc_pow m (2 * a - m)).mul_const _)]
    rw [Finset.sum_eq_single a]
    · rw [integral_mul_const, show 2 * a - a = a by omega, mul_comm]
    · intro m _ hma
      rw [integral_mul_const, integral_Wc_pow_mul_Zc_pow_of_ne (by omega), zero_mul]
    · intro ha
      exact absurd (Finset.mem_range.mpr (by omega)) ha
  have hlhs : ∫ p, (Wc p + Zc p) ^ (2 * a) ∂γ2 = (2 : ℂ) ^ a * ((2 * a - 1)‼ : ℂ) := by
    simp_rw [Wc_add_Zc, mul_pow]
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ (2 * a) = 2 ^ a := by
      rw [pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [hsq, integral_const_mul]
    congr 1
    have hfst := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (fun x : ℝ => ((x ^ (2 * a) : ℝ) : ℂ)) (fun _ : ℝ => (1 : ℂ))
    simp only [mul_one, integral_const, probReal_univ, one_smul] at hfst
    push_cast at hfst
    rw [hfst]
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, integral_even_pow_gaussianReal]
    norm_cast
  have hchoose := choose_mul_factorial_two_mul a
  have hne : ((2 * a).choose a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  apply mul_left_cancel₀ hne
  rw [← hexp, hlhs]
  exact_mod_cast hchoose.symm


/-- **Gaussian contraction rule** (paper, Section 3, eq. `contraction`): for independent
standard real Gaussians `X, Y`, with `Z = (X+iY)/√2`, `W = (X-iY)/√2`,
`E(W^a Z^b) = δ_{ab} a!`. -/
lemma integral_Wc_pow_mul_Zc_pow (a b : ℕ) :
    ∫ p, Wc p ^ a * Zc p ^ b ∂γ2 = if a = b then (a ! : ℂ) else 0 := by
  split_ifs with h
  · subst h; exact integral_Wc_pow_mul_Zc_pow_self a
  · exact integral_Wc_pow_mul_Zc_pow_of_ne h

/-- `W^k R(Z)` is integrable for every polynomial `R ∈ ℂ[z]`. -/
lemma integrable_Wc_pow_mul_eval_Zc (k : ℕ) (R : Polynomial ℂ) :
    Integrable (fun p => Wc p ^ k * R.eval (Zc p)) γ2 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  refine integrable_finsetSum _ fun i _ => ?_
  have := (integrable_Wc_pow_mul_Zc_pow k i).const_mul (R.coeff i)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

/-- **Coefficient form of the contraction rule** (paper, Section 3, eq.
`coefficient-contraction`): `E(W^k R(Z)) = k! [z^k] R(z)` for every `R ∈ ℂ[z]`. -/
lemma integral_Wc_pow_mul_eval_Zc (k : ℕ) (R : Polynomial ℂ) :
    ∫ p, Wc p ^ k * R.eval (Zc p) ∂γ2 = (k ! : ℂ) * R.coeff k := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ =>
    ((integrable_Wc_pow_mul_Zc_pow k i).const_mul (R.coeff i)).congr
      (Filter.Eventually.of_forall fun p => by simp only; ring)]
  have hterm : ∀ i, ∫ p, Wc p ^ k * (R.coeff i * Zc p ^ i) ∂γ2
      = R.coeff i * (if k = i then (k ! : ℂ) else 0) := by
    intro i
    rw [← integral_Wc_pow_mul_Zc_pow, ← integral_const_mul]
    congr 1; ext p; ring
  simp_rw [hterm]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl, mul_comm]
  · intro i _ hik
    simp [Ne.symm hik]
  · intro hk
    have hlt : R.natDegree < k := by simpa using hk
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

/-- Alternating telescoping of coefficients: for `G ∈ ℂ[z]`,
`∑_{a=0}^{n} (-1)^a [z^{n-a}] (G·(z+1)) = [z^n] G` (the paper's
`[z^n] F·∑_a (-z)^a = [z^n] F/(1+z)` step). -/
lemma sum_neg_one_pow_coeff_mul_X_add_one (G : Polynomial ℂ) (n : ℕ) :
    ∑ a ∈ Finset.range (n + 1), (-1 : ℂ) ^ a * (G * (Polynomial.X + 1)).coeff (n - a)
      = G.coeff n := by
  induction n with
  | zero => simp [mul_add]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hshift : ∀ a ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ (a + 1) * (G * (Polynomial.X + 1)).coeff (n + 1 - (a + 1))
          = -((-1 : ℂ) ^ a * (G * (Polynomial.X + 1)).coeff (n - a)) := by
      intro a _
      rw [show n + 1 - (a + 1) = n - a by omega, pow_succ]; ring
    rw [Finset.sum_congr rfl hshift, Finset.sum_neg_distrib, ih]
    simp only [pow_zero, one_mul, Nat.sub_zero, mul_add, mul_one, Polynomial.coeff_add,
      Polynomial.coeff_mul_X]
    ring


/-- The law of four independent standard real Gaussians `X₁, Y₁, X₂, Y₂`
(coordinates `0, 1, 2, 3`). -/
noncomputable abbrev μ4 : Measure (Fin 4 → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- Reassemble two points of `ℝ²` into a point of `ℝ⁴`. -/
def pack (q : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 4 → ℝ := ![q.1.1, q.1.2, q.2.1, q.2.2]

/-- `pack` is continuous. -/
lemma continuous_pack : Continuous pack := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [pack] <;> fun_prop

/-- Preimage of a box under `pack`. -/
lemma pack_preimage_pi (s : Fin 4 → Set ℝ) :
    pack ⁻¹' (Set.univ.pi s) = (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
  ext q
  simp only [Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_succ, Set.mem_prod, pack]
  simp [and_assoc]

/-- The law of `(X₁, Y₁, X₂, Y₂)` is the product of the laws of `(X₁, Y₁)` and `(X₂, Y₂)`. -/
lemma map_pack : (γ2.prod γ2).map pack = μ4 := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply continuous_pack.measurable (MeasurableSet.univ_pi hs),
    pack_preimage_pi, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    Fin.prod_univ_four]
  ring

/-- Change of variables `ℝ⁴ ≅ ℝ² × ℝ²` for a continuous integrand. -/
lemma integral_μ4 (F : (Fin 4 → ℝ) → ℂ) (hF : Continuous F) :
    ∫ v, F v ∂μ4 = ∫ q, F (pack q) ∂(γ2.prod γ2) := by
  rw [← map_pack, integral_map continuous_pack.measurable.aemeasurable
    hF.aestronglyMeasurable]


/-- The paper's four-variable cubic (eq. `P4`):
`P₄ = (1 + Z₂)(W₁(1 - Z₁) + W₂)` with `Z_j, W_j` built from coordinates
`(X₁, Y₁) = (v 0, v 1)` and `(X₂, Y₂) = (v 2, v 3)`. -/
noncomputable def P4 (v : Fin 4 → ℝ) : ℂ :=
  (1 + Zc (v 2, v 3)) * (Wc (v 0, v 1) * (1 - Zc (v 0, v 1)) + Wc (v 2, v 3))

/-- `P₄` is continuous. -/
lemma continuous_P4 : Continuous P4 := by
  unfold P4
  have h01 : Continuous fun v : Fin 4 → ℝ => (v 0, v 1) := by fun_prop
  have h23 : Continuous fun v : Fin 4 → ℝ => (v 2, v 3) := by fun_prop
  have hZ01 := continuous_Zc.comp h01
  have hW01 := continuous_Wc.comp h01
  have hZ23 := continuous_Zc.comp h23
  have hW23 := continuous_Wc.comp h23
  exact (continuous_const.add hZ23).mul ((hW01.mul (continuous_const.sub hZ01)).add hW23)

/-- `P₄` in split coordinates. -/
lemma P4_pack (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    P4 (pack q) = (1 + Zc q.2) * (Wc q.1 * (1 - Zc q.1) + Wc q.2) := rfl

/-- `[z^a] (1 - z)^a = (-1)^a`. -/
lemma coeff_one_sub_X_pow_self (a : ℕ) :
    ((1 - Polynomial.X : Polynomial ℂ) ^ a).coeff a = (-1) ^ a := by
  have h : (1 - Polynomial.X : Polynomial ℂ)
      = Polynomial.C (-1) * (Polynomial.X + Polynomial.C (-1)) := by
    simp only [map_neg, map_one]; ring
  rw [h, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  simp

/-- Binomial expansion of `A(Z₂) P₄^m` by the number `a` of factors taken from
`W₁(1 - Z₁)`, as a sum of products of a function of `(X₁, Y₁)` and a function of
`(X₂, Y₂)`. -/
lemma P4_expand (A : Polynomial ℂ) (m : ℕ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    A.eval (Zc q.2) * P4 (pack q) ^ m
      = ∑ a ∈ Finset.range (m + 1), (m.choose a : ℂ) *
          ((Wc q.1 ^ a * ((1 - Polynomial.X : Polynomial ℂ) ^ a).eval (Zc q.1)) *
            (Wc q.2 ^ (m - a) * (A * (Polynomial.X + 1) ^ m).eval (Zc q.2))) := by
  rw [P4_pack, mul_pow, add_pow (Wc q.1 * (1 - Zc q.1)) (Wc q.2) m, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_add, mul_pow]
  ring

/-- Independence: the expectation of a product of contraction terms in the two pairs
factors into a product of coefficient contractions. -/
lemma integral_prod_term (a b : ℕ) (R S : Polynomial ℂ) :
    ∫ q, (Wc q.1 ^ a * R.eval (Zc q.1)) * (Wc q.2 ^ b * S.eval (Zc q.2)) ∂(γ2.prod γ2)
      = ((a ! : ℂ) * R.coeff a) * ((b ! : ℂ) * S.coeff b) := by
  rw [integral_prod_mul (f := fun p => Wc p ^ a * R.eval (Zc p))
    (g := fun p => Wc p ^ b * S.eval (Zc p)), integral_Wc_pow_mul_eval_Zc,
    integral_Wc_pow_mul_eval_Zc]

/-- **Proposition 4.1 (master formula)** of arXiv 2607.18186: for every `A ∈ ℂ[z]` and
`m ≥ 1`, `E(A(Z₂) P₄^m) = m! [z^m] A(z)(1+z)^{m-1}`. -/
theorem integral_eval_mul_P4_pow (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    ∫ v, A.eval (Zc (v 2, v 3)) * P4 v ^ m ∂μ4
      = (m ! : ℂ) * (A * (Polynomial.X + 1) ^ (m - 1)).coeff m := by
  have hcont : Continuous fun v : Fin 4 → ℝ => A.eval (Zc (v 2, v 3)) * P4 v ^ m := by
    have h23 : Continuous fun v : Fin 4 → ℝ => (v 2, v 3) := by fun_prop
    exact (A.continuous.comp (continuous_Zc.comp h23)).mul (continuous_P4.pow m)
  rw [integral_μ4 _ hcont]
  have hpack : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), Zc (pack q 2, pack q 3) = Zc q.2 := fun q => rfl
  simp_rw [hpack, P4_expand]
  rw [integral_finsetSum _ fun a _ =>
    ((integrable_Wc_pow_mul_eval_Zc a _).mul_prod
      (integrable_Wc_pow_mul_eval_Zc (m - a) _)).const_mul _]
  simp_rw [integral_const_mul]
  simp_rw [integral_prod_term, coeff_one_sub_X_pow_self]
  have hfac : ∀ a ∈ Finset.range (m + 1),
      (m.choose a : ℂ) * ((a ! : ℂ) * (-1) ^ a *
        (((m - a)! : ℂ) * (A * (Polynomial.X + 1) ^ m).coeff (m - a)))
        = (m ! : ℂ) * ((-1) ^ a * (A * (Polynomial.X + 1) ^ m).coeff (m - a)) := by
    intro a ha
    have hfa : (m.choose a * a ! * (m - a)! : ℂ) = (m ! : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    rw [← hfa]; ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  congr 1
  have hsplit : A * (Polynomial.X + 1) ^ m = (A * (Polynomial.X + 1) ^ (m - 1)) * (Polynomial.X + 1) := by
    conv_lhs => rw [show m = m - 1 + 1 by omega, pow_succ]
    ring
  rw [hsplit, sum_neg_one_pow_coeff_mul_X_add_one]


/-- `[z^k] (z+1)^n = C(n, k)`. -/
lemma coeff_X_add_one_pow (n k : ℕ) :
    ((Polynomial.X + 1 : Polynomial ℂ) ^ n).coeff k = (n.choose k : ℂ) := by
  rw [← Polynomial.C_1, Polynomial.coeff_X_add_C_pow, one_pow, one_mul]

/-- **Proposition 4.1, first moment family**: `E(P₄^m) = 0` for every `m ≥ 1`. -/
theorem integral_P4_pow (m : ℕ) (hm : 1 ≤ m) : ∫ v, P4 v ^ m ∂μ4 = 0 := by
  have h := integral_eval_mul_P4_pow 1 m hm
  simp only [Polynomial.eval_one, one_mul] at h
  rw [h, coeff_X_add_one_pow, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- **Proposition 4.1, mixed moments**: `E(Q₄ P₄^m) = m!` for every `m ≥ 1`, where
`Q₄ = Z₂`. -/
theorem integral_Q4_mul_P4_pow (m : ℕ) (hm : 1 ≤ m) :
    ∫ v, Zc (v 2, v 3) * P4 v ^ m ∂μ4 = (m ! : ℂ) := by
  have h := integral_eval_mul_P4_pow Polynomial.X m hm
  simp only [Polynomial.eval_X] at h
  rw [h]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, Polynomial.coeff_X_mul, coeff_X_add_one_pow, Nat.choose_self]
  simp

/-- The standard Gaussian measure on `ℝⁿ`: the law of `n` independent standard real
Gaussians. -/
noncomputable abbrev gaussVec (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The **Gaussian Moments Conjecture** `GMC(n)` (Derksen–van den Essen–Zhao, Israel J.
Math. 219 (2017), Conj. 1.1), as stated in arXiv 2607.18186, Section 1: if
`P ∈ ℂ[x_1, …, x_n]` satisfies `E(P(X)^m) = 0` for all `m ≥ 1`, then for every
`Q ∈ ℂ[x_1, …, x_n]`, `E(Q(X) P(X)^m) = 0` for all sufficiently large `m`; here `X` is a
vector of `n` independent standard real Gaussians. (Polynomials in Gaussians are integrable,
so these Bochner integrals are genuine expectations; the integrals used in the refutation
below are evaluated from explicitly integrable expansions.) -/
def GMC (n : ℕ) : Prop :=
  ∀ P : MvPolynomial (Fin n) ℂ,
    (∀ m : ℕ, 1 ≤ m →
      ∫ x, (MvPolynomial.eval (fun i => (x i : ℂ)) P) ^ m ∂gaussVec n = 0) →
    ∀ Q : MvPolynomial (Fin n) ℂ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∫ x, MvPolynomial.eval (fun i => (x i : ℂ)) Q *
        (MvPolynomial.eval (fun i => (x i : ℂ)) P) ^ m ∂gaussVec n = 0

/-- The complex linear polynomial `(x_i + i x_j)/√2` (a `Z` coordinate). -/
noncomputable def zPoly (i j : Fin 4) : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.C ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) *
    (MvPolynomial.X i + MvPolynomial.C I * MvPolynomial.X j)

/-- The complex linear polynomial `(x_i - i x_j)/√2` (a `W` coordinate). -/
noncomputable def wPoly (i j : Fin 4) : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.C ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) *
    (MvPolynomial.X i - MvPolynomial.C I * MvPolynomial.X j)

/-- `P₄ = (1 + Z₂)(W₁(1 - Z₁) + W₂)` as an element of `ℂ[x_0, x_1, x_2, x_3]`. -/
noncomputable def P4poly : MvPolynomial (Fin 4) ℂ :=
  (1 + zPoly 2 3) * (wPoly 0 1 * (1 - zPoly 0 1) + wPoly 2 3)

/-- `Q₄ = Z₂` as an element of `ℂ[x_0, x_1, x_2, x_3]`. -/
noncomputable def Q4poly : MvPolynomial (Fin 4) ℂ := zPoly 2 3

/-- Evaluating `zPoly i j` at a real point gives `Z`. -/
lemma eval_zPoly (i j : Fin 4) (v : Fin 4 → ℝ) :
    MvPolynomial.eval (fun k => (v k : ℂ)) (zPoly i j) = Zc (v i, v j) := by
  simp [zPoly, Zc, div_eq_inv_mul, mul_comm I]

/-- Evaluating `wPoly i j` at a real point gives `W`. -/
lemma eval_wPoly (i j : Fin 4) (v : Fin 4 → ℝ) :
    MvPolynomial.eval (fun k => (v k : ℂ)) (wPoly i j) = Wc (v i, v j) := by
  simp [wPoly, Wc, div_eq_inv_mul, mul_comm I]

/-- Evaluating `P4poly` at a real point gives the function `P4`. -/
lemma eval_P4poly (v : Fin 4 → ℝ) :
    MvPolynomial.eval (fun k => (v k : ℂ)) P4poly = P4 v := by
  simp only [P4poly, map_mul, map_add, map_sub, map_one, eval_zPoly, eval_wPoly, P4]

/-- Evaluating `Q4poly` at a real point gives `Z₂`. -/
lemma eval_Q4poly (v : Fin 4 → ℝ) :
    MvPolynomial.eval (fun k => (v k : ℂ)) Q4poly = Zc (v 2, v 3) := eval_zPoly 2 3 v

/-- **`GMC(4)` is false** (arXiv 2607.18186, Proposition 4.1): `P₄` has all moments
`E(P₄^m) = 0` (`m ≥ 1`), yet `E(Q₄ P₄^m) = m! ≠ 0` for every `m ≥ 1`. -/
theorem not_GMC_four : ¬ GMC 4 := by
  intro h
  obtain ⟨N, hN⟩ := h P4poly (fun m hm => by simpa only [eval_P4poly] using integral_P4_pow m hm)
    Q4poly
  have hval := hN (N + 1) (by omega)
  simp only [eval_P4poly, eval_Q4poly] at hval
  rw [integral_Q4_mul_P4_pow (N + 1) (by omega)] at hval
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (N + 1))) hval


/-- Restriction `ℝⁿ → ℝ⁴` to the first four coordinates is measurable. -/
lemma measurable_restrictFour {n : ℕ} (hn : 4 ≤ n) :
    Measurable (fun (x : Fin n → ℝ) (j : Fin 4) => x (Fin.castLE hn j)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The first four coordinates of a standard Gaussian vector in `ℝⁿ` (`4 ≤ n`) form a
standard Gaussian vector in `ℝ⁴`. -/
lemma map_restrictFour_gaussVec {n : ℕ} (hn : 4 ≤ n) :
    (gaussVec n).map (fun (x : Fin n → ℝ) (j : Fin 4) => x (Fin.castLE hn j)) = gaussVec 4 := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  let s' : Fin n → Set ℝ := fun i => if h : (i : ℕ) < 4 then s ⟨i, h⟩ else Set.univ
  have hs' : ∀ i, MeasurableSet (s' i) := by
    intro i
    simp only [s']
    split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  have hpre : (fun (x : Fin n → ℝ) (j : Fin 4) => x (Fin.castLE hn j)) ⁻¹' Set.univ.pi s
      = Set.univ.pi s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, s']
    constructor
    · intro hx i
      split_ifs with h
      · exact hx ⟨i, h⟩
      · trivial
    · intro hx j
      have hj := hx (Fin.castLE hn j)
      simpa [j.isLt] using hj
  rw [Measure.map_apply (measurable_restrictFour hn) (MeasurableSet.univ_pi hs), hpre,
    Measure.pi_pi]
  let g : ℕ → ENNReal := fun i => if h : i < 4 then gaussianReal 0 1 (s ⟨i, h⟩) else 1
  have hL : ∀ i : Fin n, gaussianReal 0 1 (s' i) = g i := by
    intro i
    simp only [s', g]
    split_ifs <;> simp
  have hR : ∀ j : Fin 4, gaussianReal 0 1 (s j) = g j := by
    intro j
    simp [g, j.isLt]
  simp_rw [hL, hR]
  rw [Fin.prod_univ_eq_prod_range g n, Fin.prod_univ_eq_prod_range g 4,
    ← Finset.prod_range_mul_prod_Ico g hn]
  have hone : ∏ i ∈ Finset.Ico 4 n, g i = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hi4 : ¬ i < 4 := by
      rw [Finset.mem_Ico] at hi
      omega
    simp [g, hi4]
  rw [hone, mul_one]

/-- Padding by independent Gaussian variables does not change the expectation of a
(continuous) function of the first four coordinates. -/
lemma integral_restrictFour {n : ℕ} (hn : 4 ≤ n) (F : (Fin 4 → ℝ) → ℂ) (hF : Continuous F) :
    ∫ x, F (fun j => x (Fin.castLE hn j)) ∂gaussVec n = ∫ y, F y ∂gaussVec 4 := by
  rw [← map_restrictFour_gaussVec hn, integral_map (measurable_restrictFour hn).aemeasurable
    hF.aestronglyMeasurable]

/-- Evaluating a renamed polynomial evaluates the original at the first four
coordinates. -/
lemma eval_rename_castLE {n : ℕ} (hn : 4 ≤ n) (P : MvPolynomial (Fin 4) ℂ) (x : Fin n → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.rename (Fin.castLE hn) P)
      = MvPolynomial.eval (fun k => ((fun j => x (Fin.castLE hn j)) k : ℂ)) P := by
  rw [MvPolynomial.eval_rename]; rfl

/-- Polynomial functions `ℝ⁴ → ℂ` are continuous. -/
lemma continuous_eval_ofReal (P : MvPolynomial (Fin 4) ℂ) :
    Continuous fun y : Fin 4 → ℝ => MvPolynomial.eval (fun k => (y k : ℂ)) P :=
  (MvPolynomial.continuous_eval P).comp (by fun_prop)

/-- **`GMC(n)` is false for every `n ≥ 4`** (arXiv 2607.18186, abstract and Section 4:
"already proves failure for every `n ≥ 4`"): use `P₄, Q₄` in the first four variables and
ignore the remaining independent Gaussian variables. -/
theorem not_GMC_of_four_le {n : ℕ} (hn : 4 ≤ n) : ¬ GMC n := by
  intro h
  have hP : ∀ m : ℕ, 1 ≤ m → ∫ x, (MvPolynomial.eval (fun i => (x i : ℂ))
      (MvPolynomial.rename (Fin.castLE hn) P4poly)) ^ m ∂gaussVec n = 0 := by
    intro m hm
    simp_rw [eval_rename_castLE hn]
    rw [integral_restrictFour hn (fun y => (MvPolynomial.eval (fun k => (y k : ℂ)) P4poly) ^ m)
      ((continuous_eval_ofReal P4poly).pow m)]
    simpa only [eval_P4poly] using integral_P4_pow m hm
  obtain ⟨N, hN⟩ := h _ hP (MvPolynomial.rename (Fin.castLE hn) Q4poly)
  have hval := hN (N + 1) (by omega)
  simp_rw [eval_rename_castLE hn] at hval
  rw [integral_restrictFour hn (fun y => MvPolynomial.eval (fun k => (y k : ℂ)) Q4poly *
      (MvPolynomial.eval (fun k => (y k : ℂ)) P4poly) ^ (N + 1))
      ((continuous_eval_ofReal Q4poly).mul ((continuous_eval_ofReal P4poly).pow (N + 1)))] at hval
  simp only [eval_P4poly, eval_Q4poly] at hval
  rw [integral_Q4_mul_P4_pow (N + 1) (by omega)] at hval
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (N + 1))) hval

/-! ## Ground-truth checks -/

/-- `W` is the complex conjugate of `Z` pointwise (paper: "`W = conj Z` as random
variables"). -/
lemma Wc_eq_conj_Zc (p : ℝ × ℝ) : Wc p = (starRingEnd ℂ) (Zc p) := by
  simp only [Wc, Zc, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

example : Zc (1, 0) = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by simp [Zc]

example : Wc (0, 1) = -I / ((Real.sqrt 2 : ℝ) : ℂ) := by simp [Wc]

example : P4 0 = 0 := by simp [P4, Wc, Zc]

/-- Smallest instances of Proposition 4.1: `E(P₄) = 0` and `E(Q₄ P₄) = 1! = 1`. -/
example : ∫ v, P4 v ∂μ4 = 0 := by simpa using integral_P4_pow 1 le_rfl

example : ∫ v, Zc (v 2, v 3) * P4 v ∂μ4 = 1 := by
  simpa using integral_Q4_mul_P4_pow 1 le_rfl

/-- Contraction-rule sanity check: `E(W Z) = E(|Z|²) = 1`. -/
example : ∫ p, Wc p * Zc p ∂γ2 = 1 := by
  simpa using integral_Wc_pow_mul_Zc_pow 1 1

/-- Non-vacuity of the `GMC` hypothesis at `n = 4`: `P4poly` satisfies it. -/
example : ∀ m : ℕ, 1 ≤ m →
    ∫ x, (MvPolynomial.eval (fun i => (x i : ℂ)) P4poly) ^ m ∂gaussVec 4 = 0 := fun m hm => by
  simpa only [eval_P4poly] using integral_P4_pow m hm

end Candidates.SmallCounterexamplesGaussianMoments
