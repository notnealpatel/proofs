/-
# Stanley's 1985 dimer-denominator conjecture fails at `k = 13`

Xuejun Guo and Zhengyu Tao, *Counterexamples to Stanley's conjecture on
dimer coverings*, arXiv:2605.28195, Section 2, Lemma 2.1 (`lem:criterion`),
Theorem 2.2 (`thm:mainresult`), and identity `eq:keyeq1`, disprove
Stanley's 1985 distinct-roots conjecture for the explicit denominator `Q_k`.

This file proves that `Q_k` is not squarefree for `k+1 = 14h` with `1 ≤ h`;
at `k = 13` it also states nonseparability. The `30h-1` family and
the dimer-counting interpretation of `Q_k` are not formalized.
The definitions below follow `eq:cjej`, `eq:aS`, and `eq:defofQk`.

## Proof route

With `a = cos(π/7)`: `cos(2π/7) = 2a² − 1`, `cos(3π/7) = 4a³ − 3a`, and
`cos(3π/7) = −cos(4π/7)` forces `8a³ − 4a² − 4a + 1 = 0` (after removing the
factor `a + 1`).  In `ℚ(a)` all three numbers `1 + cos²(jπ/7)` are squares:
`sqrt(1 + a²) = 4a² − a − 1`, `sqrt(1 + cos²(2π/7)) = −2a² + 2a + 1`,
`sqrt(1 + cos²(3π/7)) = 2a² + a − 3/2` (found with Sage; each right side is
nonnegative because `√3/2 < a ≤ 1`).  The key identity is then a polynomial
identity modulo the cubic.
-/
import Mathlib

set_option autoImplicit false

namespace Combinatorics.StanleyDimerDenominatorThirteen

open Polynomial Real

/-! ## Definitions mirroring the source -/

/-- The trigonometric unit `cos θ + sqrt(1 + cos² θ)`. -/
noncomputable def cst (θ : ℝ) : ℝ := Real.cos θ + √(1 + Real.cos θ ^ 2)

/-- Stanley's `c_j = cos(jπ/(k+1)) + sqrt(1 + cos²(jπ/(k+1)))` (paper, (eq:cjej)). -/
noncomputable def stanleyC (k j : ℕ) : ℝ :=
  Real.cos (j * π / (k + 1)) + √(1 + Real.cos (j * π / (k + 1)) ^ 2)

/-- Stanley's `c̄_j = cos(jπ/(k+1)) − sqrt(1 + cos²(jπ/(k+1)))` (paper, (eq:cjej)). -/
noncomputable def stanleyCbar (k j : ℕ) : ℝ :=
  Real.cos (j * π / (k + 1)) - √(1 + Real.cos (j * π / (k + 1)) ^ 2)

/-- Stanley's `a_S = (∏_{j∈S} c_j)(∏_{j∈{1,…,ℓ}∖S} c̄_j)` with `ℓ = ⌊k/2⌋`
(paper, (eq:aS)); intended for `S ⊆ {1,…,ℓ}`. -/
noncomputable def stanleyA (k : ℕ) (S : Finset ℕ) : ℝ :=
  (∏ j ∈ S, stanleyC k j) * ∏ j ∈ Finset.Icc 1 (k / 2) \ S, stanleyCbar k j

/-- Stanley's explicit denominator `Q_k` (paper, (eq:defofQk)):
`∏_{S⊆{1,…,ℓ}} (1 − a_S x)` for even `k` and `∏_{S⊆{1,…,ℓ}} (1 − a_S² x²)` for
odd `k`, where `ℓ = ⌊k/2⌋`. -/
noncomputable def stanleyQ (k : ℕ) : ℝ[X] :=
  if Even k then ∏ S ∈ (Finset.Icc 1 (k / 2)).powerset, (1 - C (stanleyA k S) * X)
  else ∏ S ∈ (Finset.Icc 1 (k / 2)).powerset, (1 - C (stanleyA k S ^ 2) * X ^ 2)

/-! ## Basic facts -/

/-- `c_j` is the trigonometric unit `cst` at the angle `jπ/(k+1)`. -/
theorem stanleyC_eq_cst (k j : ℕ) : stanleyC k j = cst (j * π / (k + 1)) := rfl

/-- `cos θ + sqrt(1 + cos² θ)` is positive. -/
theorem cst_pos (θ : ℝ) : 0 < cst θ := by
  unfold cst
  have hs : 0 ≤ √(1 + Real.cos θ ^ 2) := Real.sqrt_nonneg _
  have hsq : (√(1 + Real.cos θ ^ 2)) ^ 2 = 1 + Real.cos θ ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (Real.cos θ + √(1 + Real.cos θ ^ 2))]

/-- `c_j` is positive. -/
theorem stanleyC_pos (k j : ℕ) : 0 < stanleyC k j := cst_pos _

/-- `c_j c̄_j = −1` (paper, Section 1). -/
theorem stanleyC_mul_stanleyCbar (k j : ℕ) : stanleyC k j * stanleyCbar k j = -1 := by
  unfold stanleyC stanleyCbar
  have hsq : (√(1 + Real.cos (j * π / (k + 1)) ^ 2)) ^ 2 = 1 + Real.cos (j * π / (k + 1)) ^ 2 :=
    Real.sq_sqrt (by positivity)
  linear_combination -hsq

/-- `c̄_j ≠ 0`. -/
theorem stanleyCbar_ne_zero (k j : ℕ) : stanleyCbar k j ≠ 0 := by
  intro h
  have h1 := stanleyC_mul_stanleyCbar k j
  rw [h, mul_zero] at h1
  norm_num at h1

/-- `a_S ≠ 0`. -/
theorem stanleyA_ne_zero (k : ℕ) (S : Finset ℕ) : stanleyA k S ≠ 0 := by
  unfold stanleyA
  refine mul_ne_zero ?_ ?_
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => (stanleyC_pos k j).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => stanleyCbar_ne_zero k j

/-- For `S ⊆ {1,…,ℓ}`: `a_S · b_{{1,…,ℓ}} = (−1)^{ℓ−|S|} b_S²`, where
`b_S = ∏_{j∈S} c_j` (paper, Section 2, before Lemma 2.1). -/
theorem stanleyA_mul_prod_full (k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (k / 2)) :
    stanleyA k S * ∏ j ∈ Finset.Icc 1 (k / 2), stanleyC k j =
      (-1) ^ (Finset.Icc 1 (k / 2) \ S).card * (∏ j ∈ S, stanleyC k j) ^ 2 := by
  have hpair : (∏ j ∈ Finset.Icc 1 (k / 2) \ S, stanleyCbar k j) *
      ∏ j ∈ Finset.Icc 1 (k / 2) \ S, stanleyC k j = (-1) ^ (Finset.Icc 1 (k / 2) \ S).card := by
    rw [← Finset.prod_mul_distrib]
    have hfun : ∀ j, stanleyCbar k j * stanleyC k j = -1 := fun j => by
      rw [mul_comm]; exact stanleyC_mul_stanleyCbar k j
    simp only [hfun, Finset.prod_const]
  rw [stanleyA, ← Finset.prod_sdiff hS]
  linear_combination (∏ j ∈ S, stanleyC k j) ^ 2 * hpair

/-- Lemma 2.1 (the direction used): if `S, T ⊆ {1,…,ℓ}` and `b_S = b_T`, then
`a_S² = a_T²`. -/
theorem stanleyA_sq_eq_of_prod_eq (k : ℕ) (S T : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (k / 2))
    (hT : T ⊆ Finset.Icc 1 (k / 2)) (h : ∏ j ∈ S, stanleyC k j = ∏ j ∈ T, stanleyC k j) :
    stanleyA k S ^ 2 = stanleyA k T ^ 2 := by
  set P := ∏ j ∈ Finset.Icc 1 (k / 2), stanleyC k j with hPdef
  have hP : P ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun j _ => (stanleyC_pos k j).ne')
  have hSP := stanleyA_mul_prod_full k S hS
  have hTP := stanleyA_mul_prod_full k T hT
  have hsign : ∀ n : ℕ, ((-1 : ℝ) ^ n) ^ 2 = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hS2 : stanleyA k S ^ 2 * P ^ 2 = (∏ j ∈ S, stanleyC k j) ^ 4 := by
    rw [← mul_pow, hSP, mul_pow, hsign]; ring
  have hT2 : stanleyA k T ^ 2 * P ^ 2 = (∏ j ∈ T, stanleyC k j) ^ 4 := by
    rw [← mul_pow, hTP, mul_pow, hsign]; ring
  exact mul_right_cancel₀ hP (by rw [hS2, hT2, h])

/-! ## The key identity (eq:keyeq1) -/

/-- Identity (eq:keyeq1) of arXiv:2605.28195:
`cos(π/7) + sqrt(1+cos²(π/7)) = (cos(2π/7) + sqrt(1+cos²(2π/7)))
(cos(3π/7) + sqrt(1+cos²(3π/7)))`, i.e. `c_7(1) = c_7(2) c_7(3)`. -/
theorem key_identity : cst (π / 7) = cst (2 * π / 7) * cst (3 * π / 7) := by
  unfold cst
  set a := Real.cos (π / 7) with ha
  have h2 : Real.cos (2 * π / 7) = 2 * a ^ 2 - 1 := by
    rw [show 2 * π / 7 = 2 * (π / 7) by ring, Real.cos_two_mul]
  have h3 : Real.cos (3 * π / 7) = 4 * a ^ 3 - 3 * a := by
    rw [show 3 * π / 7 = 3 * (π / 7) by ring, Real.cos_three_mul]
  have h4 : Real.cos (4 * π / 7) = 2 * (2 * a ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * π / 7 = 2 * (2 * π / 7) by ring, Real.cos_two_mul, h2]
  have h34 : Real.cos (3 * π / 7) = -Real.cos (4 * π / 7) := by
    rw [show 3 * π / 7 = π - 4 * π / 7 by ring, Real.cos_pi_sub]
  have hlow : √3 / 2 < a := by
    rw [← Real.cos_pi_div_six]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have hle : a ≤ 1 := Real.cos_le_one _
  have hsq3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < a := lt_trans (by positivity) hlow
  have ha2 : 3 / 4 < a ^ 2 := by nlinarith [Real.sqrt_nonneg 3]
  -- `a = cos(π/7)` is a root of the minimal cubic `8a³ − 4a² − 4a + 1`.
  have hcubic : 8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 = 0 := by
    have hquartic : (a + 1) * (8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1) = 0 := by
      rw [h3, h4] at h34
      linear_combination h34
    exact (mul_eq_zero.mp hquartic).resolve_left (by linarith)
  -- The three square roots lie in `ℚ(a)`.
  have hA : √(1 + a ^ 2) = 4 * a ^ 2 - a - 1 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by nlinarith)]
    linear_combination (-2 * a) * hcubic
  have hB : √(1 + (2 * a ^ 2 - 1) ^ 2) = -2 * a ^ 2 + 2 * a + 1 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by nlinarith)]
    linear_combination hcubic
  have hC : √(1 + (4 * a ^ 3 - 3 * a) ^ 2) = 2 * a ^ 2 + a - 3 / 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by nlinarith)]
    linear_combination (2 * a ^ 3 + a ^ 2 - 2 * a - 5 / 4) * hcubic
  rw [h2, h3, hA, hB, hC]
  linear_combination (-a - 1) * hcubic

/-! ## Examples on small cases -/

/-- `Q_1 = 1 − x²` (`ℓ = 0`, a single empty subset with `a_∅ = 1`). -/
example : stanleyQ 1 = 1 - X ^ 2 := by
  simp [stanleyQ, stanleyA]

/-- `Q_2 = 1 − x − x²` (the Fibonacci denominator of `2 × n` domino tilings):
here `ℓ = 1`, `c_1 + c̄_1 = 2 cos(π/3) = 1` and `c_1 c̄_1 = −1`. -/
example : stanleyQ 2 = 1 - X - X ^ 2 := by
  have hsum : stanleyC 2 1 + stanleyCbar 2 1 = 1 := by
    unfold stanleyC stanleyCbar
    have hcos : Real.cos (((1 : ℕ) : ℝ) * π / (((2 : ℕ) : ℝ) + 1)) = 1 / 2 := by
      rw [show ((1 : ℕ) : ℝ) * π / (((2 : ℕ) : ℝ) + 1) = π / 3 by push_cast; ring]
      exact Real.cos_pi_div_three
    rw [hcos]
    ring
  have hprod := stanleyC_mul_stanleyCbar 2 1
  have hU : Finset.Icc 1 (2 / 2) = {1} := by decide
  have hne : (∅ : Finset ℕ) ≠ {1} := by decide
  have hP : ({1} : Finset ℕ).powerset = {∅, {1}} := by decide
  rw [stanleyQ, if_pos (by decide), hU, hP, Finset.prod_pair hne]
  have hA0 : stanleyA 2 ∅ = stanleyCbar 2 1 := by simp [stanleyA]
  have hA1 : stanleyA 2 {1} = stanleyC 2 1 := by simp [stanleyA]
  rw [hA0, hA1]
  calc (1 - C (stanleyCbar 2 1) * X) * (1 - C (stanleyC 2 1) * X)
      = 1 - C (stanleyC 2 1 + stanleyCbar 2 1) * X
          + C (stanleyC 2 1 * stanleyCbar 2 1) * X ^ 2 := by
        simp only [map_add, map_mul]; ring
    _ = 1 - X - X ^ 2 := by
        rw [hsum, hprod]; simp only [map_one, map_neg]; ring

/-! ## The counterexamples -/

/-- Theorem 2.2 of arXiv:2605.28195 (first family): for every `h ≥ 1` and
`k = 14h − 1` (stated as `k + 1 = 14h`), Stanley's explicit `Q_k ∈ ℝ[X]` has a
repeated factor, namely `1 − a_S² x²` for `S = {2h}` and `T = {4h, 6h}`;
hence `Q_k` is not squarefree. -/
theorem stanleyQ_not_squarefree_of_add_one_eq (k h : ℕ) (hh : 0 < h) (hk : k + 1 = 14 * h) :
    ¬ Squarefree (stanleyQ k) := by
  have hodd : ¬ Even k := by
    rintro ⟨r, hr⟩
    omega
  have hkR : (k : ℝ) + 1 = 14 * h := by exact_mod_cast hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hangle : ∀ m : ℕ, ((m * h : ℕ) : ℝ) * π / ((k : ℝ) + 1) = m * π / 14 := fun m => by
    rw [hkR]; push_cast; field_simp
  have hc2 : stanleyC k (2 * h) = cst (π / 7) := by
    rw [stanleyC_eq_cst, hangle 2]; congr 1; ring
  have hc4 : stanleyC k (4 * h) = cst (2 * π / 7) := by
    rw [stanleyC_eq_cst, hangle 4]; congr 1; ring
  have hc6 : stanleyC k (6 * h) = cst (3 * π / 7) := by
    rw [stanleyC_eq_cst, hangle 6]; congr 1; ring
  set U := Finset.Icc 1 (k / 2) with hU
  set S₀ : Finset ℕ := {2 * h} with hS₀
  set T₀ : Finset ℕ := {4 * h, 6 * h} with hT₀
  have hS₀U : S₀ ⊆ U := by
    intro x hx
    simp only [hS₀, Finset.mem_singleton] at hx
    simp only [hU, Finset.mem_Icc]
    omega
  have hT₀U : T₀ ⊆ U := by
    intro x hx
    simp only [hT₀, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hU, Finset.mem_Icc]
    omega
  have h46 : 4 * h ≠ 6 * h := by omega
  have hne : S₀ ≠ T₀ := by
    intro heq
    have hmem : 4 * h ∈ S₀ := by rw [heq]; simp [hT₀]
    simp only [hS₀, Finset.mem_singleton] at hmem
    omega
  have hb : ∏ j ∈ S₀, stanleyC k j = ∏ j ∈ T₀, stanleyC k j := by
    rw [hS₀, hT₀, Finset.prod_singleton, Finset.prod_pair h46, hc2, hc4, hc6, key_identity]
  have hsq : stanleyA k S₀ ^ 2 = stanleyA k T₀ ^ 2 :=
    stanleyA_sq_eq_of_prod_eq k S₀ T₀ hS₀U hT₀U hb
  set f : Finset ℕ → ℝ[X] := fun S => 1 - C (stanleyA k S ^ 2) * X ^ 2 with hf
  have hQ : stanleyQ k = ∏ S ∈ U.powerset, f S := by
    rw [stanleyQ, if_neg hodd]
  have hdvd : f S₀ * f S₀ ∣ stanleyQ k := by
    have hpair : f S₀ * f S₀ = ∏ S ∈ ({S₀, T₀} : Finset (Finset ℕ)), f S := by
      rw [Finset.prod_pair hne, hf]
      simp only [hsq]
    rw [hpair, hQ]
    refine Finset.prod_dvd_prod_of_subset _ _ f ?_
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rw [Finset.mem_powerset]
    rcases hS with rfl | rfl
    · exact hS₀U
    · exact hT₀U
  intro hsf
  have hunit : IsUnit (f S₀) := hsf _ hdvd
  have hdeg : (f S₀).natDegree = 2 := by
    rw [hf]
    simp only
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;>
      rw [Polynomial.natDegree_C_mul_X_pow 2 _ (pow_ne_zero 2 (stanleyA_ne_zero k S₀))]
    simp
  have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  omega

/-- The smallest counterexample: Stanley's explicit `Q_13 ∈ ℝ[X]` is not
squarefree (arXiv:2605.28195, Theorem 2.2 with `h = 1`), so Stanley's 1985
conjecture that `Q_k` has distinct roots fails at `k = 13`. -/
theorem stanleyQ_thirteen_not_squarefree : ¬ Squarefree (stanleyQ 13) :=
  stanleyQ_not_squarefree_of_add_one_eq 13 1 (by norm_num) (by norm_num)

/-- Stanley's explicit `Q_13 ∈ ℝ[X]` does not have distinct roots: it is not
separable (arXiv:2605.28195, Theorem 2.2 with `h = 1`). -/
theorem stanleyQ_thirteen_not_separable : ¬ (stanleyQ 13).Separable :=
  fun hsep => stanleyQ_thirteen_not_squarefree hsep.squarefree

end Combinatorics.StanleyDimerDenominatorThirteen
