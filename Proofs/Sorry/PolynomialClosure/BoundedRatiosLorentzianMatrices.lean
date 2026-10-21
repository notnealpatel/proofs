/-
# Bounded ratios for Lorentzian matrices: hypermetric ratios on rank ≤ 2

## Source

arXiv:2510.25030, Daoji Huang, June Huh, Daniel Soskin and Botong Wang,
"Bounded ratios for Lorentzian matrices".

* Section 1, Conjecture `conj:intro-at-most-2` (stated after Theorem C):
  "The optimal bounding constant for any normalized reduced bounded ratio on
  L_n^+ is at most 2."  The paper proves it for `n ≤ 5` only.
* Section 1, hypermetric ratios: "If ∑ h_i = 1, the vector (h_i h_j)_{i<j} is a
  reduced bounded ratio on L_n^+."  Its coordinate sum is `(1 - ∑ h_i²)/2`, so
  the normalized ratio is `(h_i h_j)/((∑ h_i² - 1)/2)`.
* Section 5 "Rank 2 Lorentzian matrices": the Lorentzian matrices of rank at
  most 2 are the Hessians `p_ij = a_i b_j + a_j b_i` of `(∑ a_i x_i)(∑ b_i x_i)`
  with `a, b ≥ 0` (Proposition before `thm:BR_rk2`); Conjecture `conj:sub-free`
  strengthens Conjecture `conj:intro-at-most-2` on this locus and is verified by
  computer for `n ≤ 6`.

## Target (special case, open in the literature as of 2026-10-21)

Conjecture `conj:intro-at-most-2` for every hypermetric ratio and every `n`,
restricted to rank ≤ 2 Lorentzian matrices with `a, b > 0`.  With the full
(torus-invariant) exponents `α_ij = h_i h_j` (`i < j`) and
`α_ii = h_i (h_i - 1)/2`, it reads
`∏_{i ≤ j} p_ij ^ α_ij ≤ 2 ^ ((∑ h_i² - 1)/2)`.
Putting `t_i = a_i / b_i`, the scaling factors cancel and the claim becomes
`∑_{i<j} h_i h_j log (t_i + t_j) + ∑_i C(h_i, 2) log t_i ≤ 0`.

## Proof (formalized below)

1. Cube lemma: `H(x) = ∑_{i<j} h_i h_j x_i x_j + ∑_i C(h_i,2) x_i ≥ 0` on
   `[0,1]^n`, because `2 H(x) = S² - S + ∑ h_i² x_i (1 - x_i)` with
   `S = ∑ h_i x_i`, which is affine in each coordinate and equals
   `m² - m ≥ 0` (`m ∈ ℤ`) at the vertices.
2. Mellin transform: for `s > 0`,
   `Γ(s) ψ(s) = ∫_0^∞ u^(s-1) H(e^(-u t)) du ≥ 0`, where
   `ψ(s) = ∑_{i<j} h_i h_j (t_i + t_j)^(-s) + ∑_i C(h_i,2) t_i^(-s)`.
3. `ψ(0) = C(∑ h_i, 2) = 0` and `ψ'(0) = -(log form)`, so the log form is `≤ 0`.

Date: 2026-10-21.  Status in the paper: open (conjecture); this special case
(all `n`, all hypermetric ratios, rank ≤ 2 with positive `a, b`) is not
claimed in the paper.
-/
import Mathlib

set_option autoImplicit false

open Finset Real MeasureTheory Filter Topology

namespace BoundedRatiosLorentzianMatrices

/-! ## Off-diagonal sums -/

/-- The strictly-upper-triangular part of a product of sums:
`∑_{i<j} (x_i y_j + x_j y_i) = (∑ x)(∑ y) - ∑ x_i y_i`. -/
theorem sum_Ioi_bilinear {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Ioi i, (x i * y j + x j * y i) =
      (∑ i, x i) * (∑ i, y i) - ∑ i, x i * y i := by
  have hsplit : ∀ i : Fin n, ∑ j, x i * y j =
      ∑ j ∈ Iio i, x i * y j + x i * y i + ∑ j ∈ Ioi i, x i * y j := by
    intro i
    have e1 : univ.filter (· < i) = Iio i := by ext; simp
    have e2 : univ.filter (fun j => ¬ j < i) = Ici i := by ext; simp
    rw [← sum_filter_add_sum_filter_not univ (· < i), e1, e2, ← Ioi_insert,
      sum_insert (by simp)]
    ring
  have hcomm : ∑ i, ∑ j ∈ Iio i, x i * y j = ∑ i, ∑ j ∈ Ioi i, x j * y i := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun j => Ioi j)]
    intro a b; simp
  rw [Finset.sum_mul_sum]
  simp_rw [hsplit, Finset.sum_add_distrib, hcomm]
  ring

/-- `2 ∑_{i<j} x_i x_j = (∑ x)² - ∑ x_i²`. -/
theorem two_mul_sum_Ioi {n : ℕ} (x : Fin n → ℝ) :
    2 * ∑ i, ∑ j ∈ Ioi i, x i * x j = (∑ i, x i) ^ 2 - ∑ i, x i ^ 2 := by
  have hb := sum_Ioi_bilinear x x
  have h2 : ∀ i j, x i * x j + x j * x i = 2 * (x i * x j) := fun i j => by ring
  have hsym : ∑ i, ∑ j ∈ Ioi i, (x i * x j + x j * x i) =
      2 * ∑ i, ∑ j ∈ Ioi i, x i * x j := by
    simp_rw [h2, Finset.mul_sum]
  rw [hsym] at hb
  rw [hb, sq]
  simp_rw [sq]

/-! ## Definitions -/

/-- The hypermetric log form of the source, specialized to rank ≤ 2 Lorentzian
matrices after the substitution `t_i = a_i / b_i`:
`∑_{i<j} h_i h_j log (t_i + t_j) + ∑_i C(h_i, 2) log t_i`. -/
noncomputable def hypermetricLogForm {n : ℕ} (h : Fin n → ℤ) (t : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, (h i : ℝ) * h j * Real.log (t i + t j) +
    ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 * Real.log (t i)

/-- The multilinear "cube" form `∑_{i<j} h_i h_j x_i x_j + ∑_i C(h_i, 2) x_i`. -/
noncomputable def cubeForm {n : ℕ} (h : Fin n → ℤ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, (h i : ℝ) * h j * (x i * x j) +
    ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 * x i

/-- The Mellin transform of `u ↦ H(e^{-u t})` divided by `Γ(s)`:
`∑_{i<j} h_i h_j (t_i + t_j)^{-s} + ∑_i C(h_i, 2) t_i^{-s}`. -/
noncomputable def mellinForm {n : ℕ} (h : Fin n → ℤ) (t : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, (h i : ℝ) * h j * (t i + t j) ^ (-s) +
    ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 * t i ^ (-s)

/-- The rank ≤ 2 Lorentzian matrix: the Hessian `p_ij = a_i b_j + a_j b_i` of
the quadratic form `(∑ a_i x_i)(∑ b_i x_i)`. -/
def rankTwoMatrix {n : ℕ} (a b : Fin n → ℝ) (i j : Fin n) : ℝ :=
  a i * b j + a j * b i

/-- The full hypermetric ratio `∏_{i<j} p_ij^{h_i h_j} ∏_i p_ii^{h_i(h_i-1)/2}`
attached to an integer vector `h` (torus invariant when `∑ h_i = 1`). -/
noncomputable def hypermetricRatio {n : ℕ} (h : Fin n → ℤ) (p : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i, ∏ j ∈ Ioi i, p i j ^ ((h i : ℝ) * h j)) *
    ∏ i, p i i ^ ((h i : ℝ) * ((h i : ℝ) - 1) / 2)

/-! ## Ground truth -/

/-- `Ioi 1 = {2}` in `Fin 3` (used to evaluate the ground-truth examples). -/
private theorem Ioi_one_fin_three : Finset.Ioi (1 : Fin 3) = {2} := by decide

/-- `Ioi 2 = ∅` in `Fin 3` (used to evaluate the ground-truth examples). -/
private theorem Ioi_two_fin_three : Finset.Ioi (2 : Fin 3) = ∅ := by decide

/-- The diagonal of the rank ≤ 2 matrix is `p_ii = 2 a_i b_i`. -/
example (a b : Fin 3 → ℝ) : rankTwoMatrix a b 0 0 = 2 * a 0 * b 0 := by
  simp only [rankTwoMatrix]; ring

/-- Cube form at the vertex `1_{0,1}` for `h = (1, 1, -1)`: `C(h_0 + h_1, 2) = C(2, 2) = 1`. -/
example : cubeForm ![1, 1, -1] ![1, 1, 0] = 1 := by
  simp [cubeForm, Fin.sum_univ_three, Ioi_one_fin_three, Ioi_two_fin_three]

/-- The log form for `h = (-1, 1, 1)`. -/
example (t : Fin 3 → ℝ) : hypermetricLogForm ![-1, 1, 1] t =
    Real.log (t 1 + t 2) - Real.log (t 0 + t 1) - Real.log (t 0 + t 2) + Real.log (t 0) := by
  simp [hypermetricLogForm, Fin.sum_univ_three, Ioi_one_fin_three, Ioi_two_fin_three]
  ring

/-- The paper's Section 5 example: for `h = (-1, 1, 1)` the hypermetric ratio is the
triangular ratio `p_11 p_23 / (p_12 p_13)` (bounded there by `2 = 2^{(3-1)/2}`). -/
example (p : Fin 3 → Fin 3 → ℝ) : hypermetricRatio ![-1, 1, 1] p =
    p 0 0 * p 1 2 / (p 0 1 * p 0 2) := by
  simp [hypermetricRatio, Fin.prod_univ_three, Ioi_one_fin_three, Ioi_two_fin_three,
    Real.rpow_neg_one]
  ring

/-! ## Step 1: the cube lemma -/

/-- Generalized cube inequality: for any integer `c` and `x ∈ [0,1]^s`,
`(c + S)² - (c + S) + ∑ h_i² x_i (1 - x_i) ≥ 0` with `S = ∑ h_i x_i`. -/
theorem cube_aux {ι : Type*} [DecidableEq ι] (h : ι → ℤ) (x : ι → ℝ) (s : Finset ι)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) (c : ℤ) :
    0 ≤ ((c : ℝ) + ∑ i ∈ s, (h i : ℝ) * x i) ^ 2 - ((c : ℝ) + ∑ i ∈ s, (h i : ℝ) * x i)
      + ∑ i ∈ s, (h i : ℝ) ^ 2 * (x i * (1 - x i)) := by
  induction s using Finset.induction_on generalizing c with
  | empty =>
    simp only [Finset.sum_empty, add_zero]
    have hc : (0 : ℤ) ≤ c ^ 2 - c := by nlinarith [sq_nonneg (2 * c - 1)]
    exact_mod_cast hc
  | insert k s hk ih =>
    have hx' : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    obtain ⟨hk0, hk1⟩ := hx k (Finset.mem_insert_self k s)
    have ih0 := ih hx' c
    have ih1 := ih hx' (c + h k)
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    push_cast at ih1
    set T := (c : ℝ) + ∑ i ∈ s, (h i : ℝ) * x i
    set R := ∑ i ∈ s, (h i : ℝ) ^ 2 * (x i * (1 - x i))
    have hT : (c : ℝ) + (h k : ℝ) + ∑ i ∈ s, (h i : ℝ) * x i = T + h k := by ring
    rw [hT] at ih1
    have key : ((c : ℝ) + ((h k : ℝ) * x k + ∑ i ∈ s, (h i : ℝ) * x i)) ^ 2
        - ((c : ℝ) + ((h k : ℝ) * x k + ∑ i ∈ s, (h i : ℝ) * x i))
        + ((h k : ℝ) ^ 2 * (x k * (1 - x k)) + R)
        = (1 - x k) * (T ^ 2 - T + R) + x k * ((T + h k) ^ 2 - (T + h k) + R) := by
      simp only [T]; ring
    rw [key]
    exact add_nonneg (mul_nonneg (by linarith) ih0) (mul_nonneg hk0 ih1)

/-- Cube lemma: `∑_{i<j} h_i h_j x_i x_j + ∑_i C(h_i, 2) x_i ≥ 0` on `[0,1]^n`,
for every integer vector `h`. -/
theorem cubeForm_nonneg {n : ℕ} (h : Fin n → ℤ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : 0 ≤ cubeForm h x := by
  have haux := cube_aux h x univ (fun i _ => hx i) 0
  have h2 := two_mul_sum_Ioi (fun i => (h i : ℝ) * x i)
  have hform : 2 * cubeForm h x = (0 + ∑ i, (h i : ℝ) * x i) ^ 2 -
      (0 + ∑ i, (h i : ℝ) * x i) + ∑ i, (h i : ℝ) ^ 2 * (x i * (1 - x i)) := by
    have hre : ∀ i j, (h i : ℝ) * h j * (x i * x j) = (h i * x i) * (h j * x j) :=
      fun i j => by ring
    simp only [cubeForm, hre, mul_add, h2, zero_add, Finset.mul_sum]
    have key : ∑ i, 2 * ((h i : ℝ) * ((h i : ℝ) - 1) / 2 * x i) - ∑ i, ((h i : ℝ) * x i) ^ 2
        = ∑ i, (h i : ℝ) ^ 2 * (x i * (1 - x i)) - ∑ i, (h i : ℝ) * x i := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith [key]
  push_cast at haux
  linarith

/-! ## Step 2: the Mellin transform -/

/-- One Gamma integral: `∫_0^∞ u^(σ-1) (c e^{-λ u}) du = c Γ(σ) λ^{-σ}`. -/
theorem integral_term {σ l : ℝ} (c : ℝ) (hσ : 0 < σ) (hl : 0 < l) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ (σ - 1) * (c * Real.exp (-(l * u))) =
      c * (Real.Gamma σ * l ^ (-σ)) := by
  have hcomm : ∀ u : ℝ, u ^ (σ - 1) * (c * Real.exp (-(l * u))) =
      c * (u ^ (σ - 1) * Real.exp (-(l * u))) := fun u => by ring
  simp_rw [hcomm]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hl, one_div,
    Real.inv_rpow hl.le, ← Real.rpow_neg hl.le]
  ring

/-- Each Gamma integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_term {σ l : ℝ} (c : ℝ) (hσ : 0 < σ) (hl : 0 < l) :
    IntegrableOn (fun u : ℝ => u ^ (σ - 1) * (c * Real.exp (-(l * u)))) (Set.Ioi 0) := by
  have hne : ∫ u in Set.Ioi (0 : ℝ), u ^ (σ - 1) * Real.exp (-(l * u)) ≠ 0 := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hl]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) σ) (Real.Gamma_pos_of_pos hσ)).ne'
  have hint : IntegrableOn (fun u : ℝ => u ^ (σ - 1) * Real.exp (-(l * u))) (Set.Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  have hcomm : (fun u : ℝ => u ^ (σ - 1) * (c * Real.exp (-(l * u)))) =
      fun u => c * (u ^ (σ - 1) * Real.exp (-(l * u))) := funext fun u => by ring
  rw [hcomm]
  exact hint.const_mul c

/-- Pointwise expansion of `u^(σ-1) H(e^{-u t})` into Gamma integrands. -/
theorem rpow_mul_cubeForm_exp {n : ℕ} (h : Fin n → ℤ) (t : Fin n → ℝ) (σ u : ℝ) :
    u ^ (σ - 1) * cubeForm h (fun i => Real.exp (-(t i * u))) =
      ∑ i, ∑ j ∈ Ioi i, u ^ (σ - 1) * ((h i : ℝ) * h j * Real.exp (-((t i + t j) * u))) +
        ∑ i, u ^ (σ - 1) * ((h i : ℝ) * ((h i : ℝ) - 1) / 2 * Real.exp (-(t i * u))) := by
  have hexp : ∀ i j, Real.exp (-(t i * u)) * Real.exp (-(t j * u)) =
      Real.exp (-((t i + t j) * u)) := fun i j => by
    rw [← Real.exp_add]; ring_nf
  simp only [cubeForm, mul_add, Finset.mul_sum, hexp]

/-- Mellin identity: for `σ > 0` and `t > 0`,
`∫_0^∞ u^(σ-1) H(e^{-u t}) du = Γ(σ) ψ(σ)`. -/
theorem integral_cubeForm {n : ℕ} (h : Fin n → ℤ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Set.Ioi (0 : ℝ), u ^ (σ - 1) * cubeForm h (fun i => Real.exp (-(t i * u))) =
      Real.Gamma σ * mellinForm h t σ := by
  have htt : ∀ i j, 0 < t i + t j := fun i j => add_pos (ht i) (ht j)
  simp_rw [rpow_mul_cubeForm_exp]
  rw [integral_add, integral_finsetSum, integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j _ => integrableOn_term _ hσ (htt _ j))]
    simp_rw [integral_term _ hσ (htt _ _), integral_term _ hσ (ht _)]
    simp only [mellinForm, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · exact fun i _ => integrableOn_term _ hσ (ht i)
  · exact fun i _ => integrable_finsetSum _ fun j _ => integrableOn_term _ hσ (htt i j)
  · exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => integrableOn_term _ hσ (htt i j)
  · exact integrable_finsetSum _ fun i _ => integrableOn_term _ hσ (ht i)

/-- `ψ(σ) ≥ 0` for every `σ > 0` (Mellin transform of a nonnegative function). -/
theorem mellinForm_nonneg {n : ℕ} (h : Fin n → ℤ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    {σ : ℝ} (hσ : 0 < σ) : 0 ≤ mellinForm h t σ := by
  have hint : 0 ≤ ∫ u in Set.Ioi (0 : ℝ),
      u ^ (σ - 1) * cubeForm h (fun i => Real.exp (-(t i * u))) := by
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    refine mul_nonneg (Real.rpow_nonneg hu0.le _) (cubeForm_nonneg h _ fun i => ?_)
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have := mul_pos (ht i) hu0
    linarith
  rw [integral_cubeForm h t ht hσ] at hint
  exact nonneg_of_mul_nonneg_right (by linarith) (Real.Gamma_pos_of_pos hσ)

/-! ## Step 3: differentiate at `σ = 0` -/

/-- `d/ds λ^{-s} = -log λ` at `s = 0`. -/
theorem hasDerivAt_rpow_neg_zero {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun s : ℝ => l ^ (-s)) (-Real.log l) 0 := by
  have hd := (Real.hasStrictDerivAt_const_rpow hl (-0)).hasDerivAt.comp 0 (hasDerivAt_neg 0)
  simpa [Function.comp_def] using hd

/-- `ψ'(0) = -(hypermetric log form)`. -/
theorem hasDerivAt_mellinForm {n : ℕ} (h : Fin n → ℤ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    HasDerivAt (mellinForm h t) (-hypermetricLogForm h t) 0 := by
  have hd := HasDerivAt.add
    (HasDerivAt.fun_sum (u := univ) fun i _ => HasDerivAt.fun_sum (u := Ioi i) fun j _ =>
      (hasDerivAt_rpow_neg_zero (add_pos (ht i) (ht j))).const_mul ((h i : ℝ) * h j))
    (HasDerivAt.fun_sum (u := univ) fun i _ =>
      (hasDerivAt_rpow_neg_zero (ht i)).const_mul ((h i : ℝ) * ((h i : ℝ) - 1) / 2))
  refine hd.congr_deriv ?_
  simp only [hypermetricLogForm, mul_neg, Finset.sum_neg_distrib, neg_add]

/-- `ψ(0) = C(∑ h_i, 2) = 0` when `∑ h_i = 1`. -/
theorem mellinForm_zero {n : ℕ} (h : Fin n → ℤ) (hsum : ∑ i, h i = 1) (t : Fin n → ℝ) :
    mellinForm h t 0 = 0 := by
  have hs : ∑ i, (h i : ℝ) = 1 := by exact_mod_cast hsum
  have h2 := two_mul_sum_Ioi (fun i => (h i : ℝ))
  have hdiag : ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 =
      (∑ i, (h i : ℝ) ^ 2 - ∑ i, (h i : ℝ)) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [mellinForm, neg_zero, Real.rpow_zero, mul_one]
  rw [hdiag, hs]
  rw [hs] at h2
  linarith

/-- **Hypermetric ratios on rank ≤ 2 Lorentzian matrices (log form).**
For every `n`, every integer vector `h` with `∑ h_i = 1` and every `t ∈ ℝ_{>0}^n`,
`∑_{i<j} h_i h_j log (t_i + t_j) + ∑_i C(h_i, 2) log t_i ≤ 0`.
This is Conjecture `conj:intro-at-most-2` of arXiv:2510.25030 for hypermetric
ratios, restricted to rank ≤ 2 Lorentzian matrices, after `t_i = a_i / b_i`. -/
theorem hypermetricLogForm_nonpos {n : ℕ} (h : Fin n → ℤ) (hsum : ∑ i, h i = 1)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) : hypermetricLogForm h t ≤ 0 := by
  have hslope := (hasDerivAt_mellinForm h t ht).tendsto_slope_zero_right
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ s⁻¹ • (mellinForm h t (0 + s) - mellinForm h t 0) := by
    refine eventually_nhdsWithin_of_forall fun s hs => ?_
    have hs0 : 0 < s := hs
    rw [mellinForm_zero h hsum, zero_add, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hs0.le) (mellinForm_nonneg h t ht hs0)
  have hge := ge_of_tendsto hslope hev
  linarith

/-! ## Step 4: the matrix form on rank ≤ 2 Lorentzian matrices -/

/-- The logarithm of a hypermetric ratio of a positive symmetric array. -/
theorem log_hypermetricRatio {n : ℕ} (h : Fin n → ℤ) (p : Fin n → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) :
    Real.log (hypermetricRatio h p) =
      ∑ i, ∑ j ∈ Ioi i, (h i : ℝ) * h j * Real.log (p i j) +
        ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 * Real.log (p i i) := by
  have hpos1 : ∀ i j, 0 < p i j ^ ((h i : ℝ) * h j) := fun i j =>
    Real.rpow_pos_of_pos (hp i j) _
  have hpos2 : ∀ i, 0 < p i i ^ ((h i : ℝ) * ((h i : ℝ) - 1) / 2) := fun i =>
    Real.rpow_pos_of_pos (hp i i) _
  have hprod1 : ∀ i, 0 < ∏ j ∈ Ioi i, p i j ^ ((h i : ℝ) * h j) := fun i =>
    Finset.prod_pos fun j _ => hpos1 i j
  rw [hypermetricRatio, Real.log_mul (Finset.prod_pos fun i _ => hprod1 i).ne'
      (Finset.prod_pos fun i _ => hpos2 i).ne',
    Real.log_prod fun i _ => (hprod1 i).ne', Real.log_prod fun i _ => (hpos2 i).ne']
  simp_rw [Real.log_prod fun j _ => (hpos1 _ j).ne']
  simp_rw [Real.log_rpow (hp _ _)]

/-- `log p_ij = log b_i + log b_j + log (a_i/b_i + a_j/b_j)` for `p = a bᵀ + b aᵀ`. -/
theorem log_rankTwoMatrix {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i j : Fin n) :
    Real.log (rankTwoMatrix a b i j) =
      Real.log (b i) + Real.log (b j) + Real.log (a i / b i + a j / b j) := by
  have hbi := (hb i).ne'
  have hbj := (hb j).ne'
  have ht : 0 < a i / b i + a j / b j := add_pos (div_pos (ha i) (hb i)) (div_pos (ha j) (hb j))
  have heq : rankTwoMatrix a b i j = b i * b j * (a i / b i + a j / b j) := by
    simp only [rankTwoMatrix]; field_simp
  rw [heq, Real.log_mul (mul_pos (hb i) (hb j)).ne' ht.ne', Real.log_mul hbi hbj]

/-- Positivity of the rank ≤ 2 Lorentzian matrix for `a, b > 0`. -/
theorem rankTwoMatrix_pos {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i j : Fin n) : 0 < rankTwoMatrix a b i j :=
  add_pos (mul_pos (ha i) (hb j)) (mul_pos (ha j) (hb i))

/-- **Hypermetric ratios on rank ≤ 2 Lorentzian matrices (matrix form).**
For `a, b ∈ ℝ_{>0}^n`, `p_ij = a_i b_j + a_j b_i` and `h ∈ ℤ^n` with `∑ h_i = 1`,
`∏_{i<j} p_ij^{h_i h_j} ∏_i p_ii^{h_i(h_i-1)/2} ≤ 2^{(∑ h_i² - 1)/2}`;
i.e. the normalized hypermetric ratio is bounded by `2` on rank ≤ 2 Lorentzian
matrices with positive factors.  This is Conjecture `conj:intro-at-most-2` of
arXiv:2510.25030 for hypermetric ratios on this locus. -/
theorem hypermetricRatio_rankTwoMatrix_le {n : ℕ} (h : Fin n → ℤ) (hsum : ∑ i, h i = 1)
    (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    hypermetricRatio h (rankTwoMatrix a b) ≤ 2 ^ ((∑ i, (h i : ℝ) ^ 2 - 1) / 2) := by
  set t : Fin n → ℝ := fun i => a i / b i
  have ht : ∀ i, 0 < t i := fun i => div_pos (ha i) (hb i)
  have hp := rankTwoMatrix_pos a b ha hb
  have hs : ∑ i, (h i : ℝ) = 1 := by exact_mod_cast hsum
  have hRpos : 0 < hypermetricRatio h (rankTwoMatrix a b) := by
    unfold hypermetricRatio
    exact mul_pos (Finset.prod_pos fun i _ => Finset.prod_pos fun j _ =>
      Real.rpow_pos_of_pos (hp i j) _) (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hp i i) _)
  have hdiag : ∀ i, Real.log (rankTwoMatrix a b i i) =
      Real.log 2 + 2 * Real.log (b i) + Real.log (t i) := by
    intro i
    have htwo : a i / b i + a i / b i = 2 * t i := by simp only [t]; ring
    rw [log_rankTwoMatrix a b ha hb i i, htwo, Real.log_mul two_ne_zero (ht i).ne']
    ring
  -- off-diagonal part
  have E2 : ∑ i, ∑ j ∈ Ioi i, (h i : ℝ) * h j * Real.log (rankTwoMatrix a b i j) =
      ∑ i, ∑ j ∈ Ioi i, ((h i : ℝ) * ((h j : ℝ) * Real.log (b j)) +
          (h j : ℝ) * ((h i : ℝ) * Real.log (b i))) +
        ∑ i, ∑ j ∈ Ioi i, (h i : ℝ) * h j * Real.log (t i + t j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [log_rankTwoMatrix a b ha hb i j]
    ring
  -- diagonal part
  have E3 : ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 * Real.log (rankTwoMatrix a b i i) =
      ∑ i, (h i : ℝ) * ((h i : ℝ) * Real.log (b i)) - ∑ i, (h i : ℝ) * Real.log (b i) +
        (∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2) * Real.log 2 +
        ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 * Real.log (t i) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdiag i]
    ring
  have E4 := sum_Ioi_bilinear (fun i => (h i : ℝ)) (fun i => (h i : ℝ) * Real.log (b i))
  have E5 : ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 = (∑ i, (h i : ℝ) ^ 2 - 1) / 2 := by
    have hsplit : ∑ i, (h i : ℝ) * ((h i : ℝ) - 1) / 2 =
        (∑ i, (h i : ℝ) ^ 2 - ∑ i, (h i : ℝ)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hs]
  have hF := hypermetricLogForm_nonpos h hsum t ht
  have hlogR : Real.log (hypermetricRatio h (rankTwoMatrix a b)) =
      hypermetricLogForm h t + (∑ i, (h i : ℝ) ^ 2 - 1) / 2 * Real.log 2 := by
    rw [log_hypermetricRatio h _ hp, E2, E3, E4, E5, hs, hypermetricLogForm]
    ring
  rw [← Real.log_le_log_iff hRpos (Real.rpow_pos_of_pos two_pos _), hlogR,
    Real.log_rpow two_pos]
  linarith

/-- Non-vacuity: the hypotheses of `hypermetricRatio_rankTwoMatrix_le` hold jointly
for the triangular vector `h = (1, 1, -1)` and `a = b = 1`. -/
example : hypermetricRatio ![1, 1, -1] (rankTwoMatrix (fun _ : Fin 3 => 1) (fun _ => 1)) ≤
    2 ^ ((∑ i, ((![1, 1, -1] : Fin 3 → ℤ) i : ℝ) ^ 2 - 1) / 2) :=
  hypermetricRatio_rankTwoMatrix_le ![1, 1, -1] (by decide) _ _ (fun _ => one_pos)
    (fun _ => one_pos)

end BoundedRatiosLorentzianMatrices
