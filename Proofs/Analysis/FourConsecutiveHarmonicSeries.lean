/-
# Euler's harmonic sum and the consecutive-pair identity

Source: Wilson J. Chen and Vincent Nguyen, *A Series Involving a Product
of Four Consecutive Harmonic Numbers*, arXiv:2507.19502, Section 1.
The introductory equations (EulerGoldbach), (OriginalEulerSum) at `n = 2`,
and (Consecutive2) give
`∑_{k≥1} H_k/k² = 2ζ(3)` and
`∑_{k≥1} H_k H_{k+1}/(k(k+1)) = ζ(2)+2ζ(3)`.
These are known inputs to that paper: Euler's identity and the
Furdui–Sîntămărian identity (cited there to *Sharp Mathematical Analysis*,
pp. 238–240 and p. 119, respectively).

Only these one-harmonic and consecutive-pair (`q = 1`) identities are
formalized here, not the paper's four-consecutive (`q = 3`) result.
Mathlib's rational `harmonic k` is cast to `ℝ` or `ℂ`, and `ζ` is
`riemannZeta`. The paper-indexed series have a zero totalized `k = 0` term.

A nonnegative double series `∑_{n,k≥1} 1/(nk(n+k))`, summed by rows and
antidiagonals, gives Euler's identity. An exact partial-sum identity,
`H_N²/N → 0`, Euler's sum, and the Basel sum give the consecutive-pair
identity. Each is supplied in real `HasSum` and complex zeta forms.
-/
import Mathlib

set_option autoImplicit false

namespace FourConsecutiveHarmonicSeries

open Filter Topology

/-! ## Examples for the objects involved -/

/-- `H_1 = 1`, `H_2 = 3/2`, `H_3 = 11/6`. -/
example : harmonic 1 = 1 ∧ harmonic 2 = 3 / 2 ∧ harmonic 3 = 11 / 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [harmonic, Finset.sum_range_succ]

/-- First summand of the `q = 1` series: `H_1 H_2/(1·2) = 3/4`. -/
example : harmonic 1 * harmonic 2 / (1 * 2) = 3 / 4 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- First summand of Euler's series after `H_1/1^2 = 1`: `H_2/2^2 = 3/8`. -/
example : harmonic 2 / 2 ^ 2 = 3 / 8 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- Telescoping: if `f` is antitone and tends to `0`, then
`∑_{k ≥ 0} (f k - f (k + m)) = ∑_{k < m} f k`. -/
theorem hasSum_sub_shift_of_antitone {f : ℕ → ℝ} (hf : Antitone f)
    (hlim : Tendsto f atTop (𝓝 0)) (m : ℕ) :
    HasSum (fun k => f k - f (k + m)) (∑ k ∈ Finset.range m, f k) := by
  have hnonneg : ∀ k, 0 ≤ f k - f (k + m) := fun k =>
    sub_nonneg.mpr (hf (Nat.le_add_right k m))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpartial : ∀ N, ∑ k ∈ Finset.range N, (f k - f (k + m)) =
      ∑ k ∈ Finset.range m, f k - ∑ i ∈ Finset.range m, f (N + i) := by
    intro N
    have h1 := Finset.sum_range_add f N m
    have h2 := Finset.sum_range_add f m N
    rw [Finset.sum_sub_distrib, add_comm N m] at *
    simp only [add_comm _ m] at h1 h2 ⊢
    linarith
  simp_rw [hpartial]
  have htail : Tendsto (fun N => ∑ i ∈ Finset.range m, f (N + i)) atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.range m) fun i _ =>
      hlim.comp (tendsto_add_atTop_nat i)
    simpa using hsum
  simpa using tendsto_const_nhds.sub htail


/-- The harmonic number as a finite real sum: `H_n = ∑_{i<n} 1/(i+1)`. -/
theorem harmonic_real_eq (n : ℕ) :
    (harmonic n : ℝ) = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) := by
  simp [harmonic]

/-- Real harmonic numbers are nonnegative. -/
theorem harmonic_real_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  rw [harmonic_real_eq]
  exact Finset.sum_nonneg fun i _ => by positivity

/-- `∑_{k ≥ 0} (1/(k+1) - 1/(k+n+2)) = H_{n+1}`. -/
theorem hasSum_inv_sub_inv_shift (n : ℕ) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + n + 2))
      (harmonic (n + 1) : ℝ) := by
  have hanti : Antitone fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    intro a b hab
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := hasSum_sub_shift_of_antitone hanti hlim (n + 1)
  rw [harmonic_real_eq]
  convert h using 2 with k
  push_cast
  ring_nf

/-- The inner sum of the Euler double series:
`∑_{k ≥ 0} 1/((n+1)(k+1)(n+k+2)) = H_{n+1}/(n+1)^2`. -/
theorem hasSum_euler_inner (n : ℕ) :
    HasSum (fun k : ℕ => 1 / (((n : ℝ) + 1) * ((k : ℝ) + 1) * ((n : ℝ) + k + 2)))
      ((harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have h := (hasSum_inv_sub_inv_shift n).mul_left (1 / ((n : ℝ) + 1) ^ 2)
  have hf : (fun k : ℕ => 1 / (((n : ℝ) + 1) * ((k : ℝ) + 1) * ((n : ℝ) + k + 2))) =
      fun k : ℕ => 1 / ((n : ℝ) + 1) ^ 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + n + 2)) := by
    funext k
    field_simp
    ring
  have hv : (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2 =
      1 / ((n : ℝ) + 1) ^ 2 * (harmonic (n + 1) : ℝ) := by ring
  rw [hf, hv]
  exact h

/-- `H_{n} ≤ 1 + 2 √n`, in rpow form. -/
theorem harmonic_le_one_add_two_rpow (n : ℕ) :
    (harmonic n : ℝ) ≤ 1 + 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have h1 := harmonic_le_one_add_log n
  have h2 := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 2)
  have h3 : (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
  linarith

/-- The Euler series `∑ H_{n+1}/(n+1)^2` is summable. -/
theorem summable_harmonic_div_sq :
    Summable fun n : ℕ => (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have hs := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using hs
  have hp32 : Summable fun n : ℕ => (((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
    have hs := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))
    simpa using hs
  refine (hp2.add (hp32.mul_left 2)).of_nonneg_of_le
    (fun n => div_nonneg (harmonic_real_nonneg (n + 1)) (by positivity)) fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hH := harmonic_le_one_add_two_rpow (n + 1)
  push_cast at hH
  have hsplit : ((n : ℝ) + 1) ^ 2 =
      ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hr : 0 < ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hr' : 0 < ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  calc (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2
      ≤ (1 + 2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) / ((n : ℝ) + 1) ^ 2 := by
        gcongr
    _ = 1 / ((n : ℝ) + 1) ^ 2 + 2 * (((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [add_div, hsplit]
        field_simp


/-- The Euler double series term `1/(n k (n+k))`, shifted to `n, k ≥ 0`. -/
noncomputable def eulerDoubleTerm (p : ℕ × ℕ) : ℝ :=
  1 / (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * ((p.1 : ℝ) + p.2 + 2))

/-- `eulerDoubleTerm (0, 0) = 1/(1·1·2)` and `eulerDoubleTerm (1, 0) = 1/(2·1·3)`. -/
example : eulerDoubleTerm (0, 0) = 1 / 2 ∧ eulerDoubleTerm (1, 0) = 1 / 6 := by
  refine ⟨?_, ?_⟩ <;> norm_num [eulerDoubleTerm]

/-- Fiber sum over the antidiagonal `i + j = m`:
`∑_{i+j=m} 1/((i+1)(j+1)(m+2)) = 2 H_{m+1}/(m+2)^2`. -/
theorem sum_antidiagonal_eulerDoubleTerm (m : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, eulerDoubleTerm p =
      2 * (harmonic (m + 1) : ℝ) / ((m : ℝ) + 2) ^ 2 := by
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal m, eulerDoubleTerm p =
      (1 / ((p.1 : ℝ) + 1) + 1 / ((p.2 : ℝ) + 1)) / ((m : ℝ) + 2) ^ 2 := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hp' : (p.1 : ℝ) + p.2 = m := by exact_mod_cast hp
    unfold eulerDoubleTerm
    rw [← hp']
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_add_distrib]
  have hswap : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, 1 / ((p.2 : ℝ) + 1) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, 1 / ((p.1 : ℝ) + 1) :=
    (Finset.Nat.sum_antidiagonal_swap (f := fun p : ℕ × ℕ => 1 / ((p.1 : ℝ) + 1)))
  have hH : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, 1 / ((p.1 : ℝ) + 1) = (harmonic (m + 1) : ℝ) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, harmonic_real_eq]
  rw [hswap, hH]
  ring

/-- The Euler double series `∑_{n,k ≥ 1} 1/(n k (n+k))` is summable. -/
theorem summable_eulerDoubleTerm : Summable eulerDoubleTerm := by
  have hnonneg : 0 ≤ eulerDoubleTerm := fun p => by unfold eulerDoubleTerm; positivity
  refine (summable_prod_of_nonneg hnonneg).mpr ⟨fun n => (hasSum_euler_inner n).summable, ?_⟩
  refine summable_harmonic_div_sq.congr fun n => ?_
  exact ((hasSum_euler_inner n).tsum_eq).symm

/-- Summing the Euler double series row by row gives `∑ H_{n+1}/(n+1)^2`. -/
theorem hasSum_harmonic_div_sq_double :
    HasSum (fun n : ℕ => (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2)
      (∑' p, eulerDoubleTerm p) :=
  summable_eulerDoubleTerm.hasSum.prod_fiberwise fun n => hasSum_euler_inner n

/-- Summing the Euler double series along antidiagonals gives
`∑_{m ≥ 0} 2 H_{m+1}/(m+2)^2`. -/
theorem hasSum_antidiagonal_double :
    HasSum (fun m : ℕ => 2 * (harmonic (m + 1) : ℝ) / ((m : ℝ) + 2) ^ 2)
      (∑' p, eulerDoubleTerm p) := by
  have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr
    summable_eulerDoubleTerm.hasSum
  refine h.sigma fun m => ?_
  rw [← sum_antidiagonal_eulerDoubleTerm m, ← Finset.sum_coe_sort]
  exact hasSum_fintype _


/-- Dropping the first term of the Euler series: if `∑_{n ≥ 0} H_{n+1}/(n+1)^2 = A`
then `∑_{m ≥ 0} H_{m+2}/(m+2)^2 = A - 1`. -/
theorem hasSum_harmonic_div_sq_shift {A : ℝ}
    (hAs : HasSum (fun n : ℕ => (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2) A) :
    HasSum (fun m : ℕ => (harmonic (m + 2) : ℝ) / ((m : ℝ) + 2) ^ 2) (A - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr hAs
  simp only [Finset.range_one, Finset.sum_singleton] at h
  have hf : (fun n : ℕ => (harmonic (n + 1 + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2) =
      fun m : ℕ => (harmonic (m + 2) : ℝ) / ((m : ℝ) + 2) ^ 2 := by
    funext m
    rw [Nat.cast_add, Nat.cast_one, add_assoc (m : ℝ), one_add_one_eq_two]
  have hv : A - (harmonic (0 + 1) : ℝ) / (((0 : ℕ) : ℝ) + 1) ^ 2 = A - 1 := by
    norm_num [harmonic]
  rw [hf, hv] at h
  exact h

/-- `∑_{n ≥ 0} 1/(n+1)^3` converges to its sum `ζ(3)` (real form). -/
theorem hasSum_inv_cube :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  push_cast at h ⊢
  exact h.hasSum

/-- **Euler's sum** (real form): `∑_{k ≥ 1} H_k / k^2 = 2 ∑_{k ≥ 1} 1/k^3`. -/
theorem hasSum_harmonic_div_sq :
    HasSum (fun n : ℕ => (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2)
      (2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) := by
  set A := ∑' n : ℕ, (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2 with hA
  set Z := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 with hZ
  have hAs : HasSum (fun n : ℕ => (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) ^ 2) A :=
    summable_harmonic_div_sq.hasSum
  have hS : ∑' p, eulerDoubleTerm p = A := hasSum_harmonic_div_sq_double.unique hAs
  have hA1 := hasSum_harmonic_div_sq_shift hAs
  -- shifted zeta series: `∑_{m ≥ 0} 1/(m+2)^3 = Z - 1`
  have hZ1 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 3) (Z - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_inv_cube
    simp only [Finset.range_one, Finset.sum_singleton] at h
    have hf : (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 3) =
        fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 3 := by
      funext m
      rw [Nat.cast_add, Nat.cast_one, add_assoc (m : ℝ), one_add_one_eq_two]
    have hv : Z - 1 / (((0 : ℕ) : ℝ) + 1) ^ 3 = Z - 1 := by norm_num
    rw [hf, hv] at h
    exact h
  have hcomb := (hA1.mul_left 2).sub (hZ1.mul_left 2)
  have hpt : (fun m : ℕ => 2 * (harmonic (m + 2) : ℝ) / ((m : ℝ) + 2) ^ 2 * 0 +
      (2 * ((harmonic (m + 2) : ℝ) / ((m : ℝ) + 2) ^ 2) - 2 * (1 / ((m : ℝ) + 2) ^ 3))) =
      fun m : ℕ => 2 * (harmonic (m + 1) : ℝ) / ((m : ℝ) + 2) ^ 2 := by
    funext m
    rw [harmonic_succ (m + 1)]
    push_cast
    field_simp
    ring
  have hcomb' : HasSum (fun m : ℕ => 2 * (harmonic (m + 1) : ℝ) / ((m : ℝ) + 2) ^ 2)
      (2 * (A - 1) - 2 * (Z - 1)) := by
    rw [← hpt]
    simpa using hcomb
  have hEq := hasSum_antidiagonal_double.unique hcomb'
  have hAZ : A = 2 * Z := by linarith
  rw [← hAZ]
  exact hAs


/-- Recurrence `H_{n+1} = H_n + 1/(n+1)` in `ℝ`. -/
theorem harmonic_real_succ (n : ℕ) :
    (harmonic (n + 1) : ℝ) = harmonic n + 1 / ((n : ℝ) + 1) := by
  rw [harmonic_succ]
  push_cast
  ring

/-- Partial-sum identity for the `q = 1` series: for every `N`,
`∑_{n<N} H_{n+1}H_{n+2}/((n+1)(n+2))
  = 1 - H_{N+1}^2/(N+1) + ∑_{n<N} H_{n+2}/(n+2)^2 + ∑_{n<N} 1/(n+1)^2 - H_N/(N+1)`. -/
theorem sum_range_consecutive_pair (N : ℕ) :
    ∑ n ∈ Finset.range N, (harmonic (n + 1) : ℝ) * harmonic (n + 2) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      1 - (harmonic (N + 1) : ℝ) ^ 2 / ((N : ℝ) + 1) +
        ∑ n ∈ Finset.range N, (harmonic (n + 2) : ℝ) / ((n : ℝ) + 2) ^ 2 +
        ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2 -
        (harmonic N : ℝ) / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num [harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := harmonic_real_succ N
    have h2 := harmonic_real_succ (N + 1)
    rw [show N + 1 + 1 = N + 2 from rfl] at h2
    rw [h2, h1]
    push_cast
    field_simp
    ring


/-- `∑_{n ≥ 0} 1/(n+1)^2 = π^2/6` (Euler's Basel sum, from Mathlib). -/
theorem hasSum_inv_sq_succ :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hv : Real.pi ^ 2 / 6 - ∑ i ∈ Finset.range 1, 1 / ((i : ℕ) : ℝ) ^ 2 =
      Real.pi ^ 2 / 6 := by
    simp
  have hf : (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    funext n
    rw [Nat.cast_add, Nat.cast_one]
  rw [hv, hf] at h
  exact h

/-- `(1 + log x)^2 / x → 0` as `x → ∞`. -/
theorem tendsto_one_add_log_sq_div :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ 2 / x) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hsum := (h0.add (h1.const_mul 2)).add h2
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp
  ring

/-- `(1 + log x) / x → 0` as `x → ∞`. -/
theorem tendsto_one_add_log_div :
    Tendsto (fun x : ℝ => (1 + Real.log x) / x) atTop (𝓝 0) := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsum := h0.add h1
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp

/-- `N + 1 → ∞` in `ℝ` along `ℕ`. -/
theorem tendsto_natCast_add_one_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- `H_{N+1}^2/(N+1) → 0`. -/
theorem tendsto_harmonic_sq_div :
    Tendsto (fun N : ℕ => (harmonic (N + 1) : ℝ) ^ 2 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => by positivity) (fun N => ?_)
    (tendsto_one_add_log_sq_div.comp tendsto_natCast_add_one_atTop)
  have hH := harmonic_le_one_add_log (N + 1)
  push_cast at hH
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp only [Function.comp_apply]
  gcongr
  exact harmonic_real_nonneg (N + 1)

/-- `H_N/(N+1) → 0`. -/
theorem tendsto_harmonic_div :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => div_nonneg (harmonic_real_nonneg N) (by positivity))
    (fun N => ?_) (tendsto_one_add_log_div.comp tendsto_natCast_add_one_atTop)
  have hH := harmonic_le_one_add_log (N + 1)
  push_cast at hH
  have hmono : (harmonic N : ℝ) ≤ harmonic (N + 1) := by
    rw [harmonic_real_succ N]
    have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
    linarith
  simp only [Function.comp_apply]
  gcongr
  linarith

/-- **Furdui–Sîntămărian identity, `q = 1`** (real form, shifted index `k = n + 1`):
`∑_{k ≥ 1} H_k H_{k+1}/(k(k+1)) = π^2/6 + 2 ∑_{k ≥ 1} 1/k^3`. -/
theorem hasSum_consecutive_pair :
    HasSum (fun n : ℕ => (harmonic (n + 1) : ℝ) * harmonic (n + 2) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (Real.pi ^ 2 / 6 + 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ (harmonic (n + 1) : ℝ) * harmonic (n + 2) /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := fun n =>
    div_nonneg (mul_nonneg (harmonic_real_nonneg _) (harmonic_real_nonneg _)) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hE := (hasSum_harmonic_div_sq_shift hasSum_harmonic_div_sq).tendsto_sum_nat
  have hZ2 := hasSum_inv_sq_succ.tendsto_sum_nat
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_harmonic_sq_div).add
    hE).add hZ2 |>.sub tendsto_harmonic_div
  have hval : 1 - 0 + (2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 - 1) + Real.pi ^ 2 / 6 - 0 =
      Real.pi ^ 2 / 6 + 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 := by ring
  rw [hval] at hlim
  refine hlim.congr fun N => ?_
  rw [sum_range_consecutive_pair N]


/-- `ζ(3) = ∑_{n ≥ 0} 1/(n+1)^3`, the real series viewed in `ℂ`. -/
theorem riemannZeta_three_eq_tsum :
    riemannZeta 3 = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := 3) (by norm_num), Complex.ofReal_tsum]
  congr 1
  funext n
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  rfl

/-- **Euler's sum** `∑_{k ≥ 1} H_k/k^2 = 2 ζ(3)` (shifted index `k = n + 1`). -/
theorem hasSum_harmonic_div_sq_zeta :
    HasSum (fun n : ℕ => (harmonic (n + 1) : ℂ) / ((n : ℂ) + 1) ^ 2) (2 * riemannZeta 3) := by
  have h := Complex.hasSum_ofReal.mpr hasSum_harmonic_div_sq
  rw [riemannZeta_three_eq_tsum]
  push_cast at h ⊢
  exact h

/-- **Furdui–Sîntămărian `q = 1`**:
`∑_{k ≥ 1} H_k H_{k+1}/(k(k+1)) = ζ(2) + 2 ζ(3)` (shifted index `k = n + 1`). -/
theorem hasSum_consecutive_pair_zeta :
    HasSum (fun n : ℕ => (harmonic (n + 1) : ℂ) * harmonic (n + 2) /
        (((n : ℂ) + 1) * ((n : ℂ) + 2)))
      (riemannZeta 2 + 2 * riemannZeta 3) := by
  have h := Complex.hasSum_ofReal.mpr hasSum_consecutive_pair
  rw [riemannZeta_three_eq_tsum, riemannZeta_two]
  push_cast at h ⊢
  exact h


/-- **Euler's sum, paper indexing** (eq. (EulerGoldbach) / (OriginalEulerSum) at `n = 2`
of arXiv:2507.19502): `∑_{k ≥ 1} H_k/k^2 = 2 ζ(3)`. The `k = 0` summand is
`H_0/0^2 = 0` since `H_0 = 0`. -/
theorem euler_sum_eq_two_zeta_three :
    HasSum (fun k : ℕ => (harmonic k : ℂ) / (k : ℂ) ^ 2) (2 * riemannZeta 3) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa using hasSum_harmonic_div_sq_zeta

/-- **Furdui–Sîntămărian `q = 1`, paper indexing** (eq. (Consecutive2) of
arXiv:2507.19502): `∑_{k ≥ 1} H_k H_{k+1}/(k(k+1)) = ζ(2) + 2 ζ(3)`. The `k = 0`
summand is `0` since `H_0 = 0`. -/
theorem consecutive_pair_eq_zeta_two_add_two_zeta_three :
    HasSum (fun k : ℕ => (harmonic k : ℂ) * harmonic (k + 1) / ((k : ℂ) * ((k : ℂ) + 1)))
      (riemannZeta 2 + 2 * riemannZeta 3) := by
  rw [← hasSum_nat_add_iff' 1]
  have hf : (fun n : ℕ => (harmonic (n + 1) : ℂ) * harmonic (n + 1 + 1) /
      (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) + 1))) =
      fun n : ℕ => (harmonic (n + 1) : ℂ) * harmonic (n + 2) /
        (((n : ℂ) + 1) * ((n : ℂ) + 2)) := by
    funext n
    rw [Nat.cast_add, Nat.cast_one, add_assoc (n : ℂ) 1 1, one_add_one_eq_two]
  have hv : riemannZeta 2 + 2 * riemannZeta 3 -
      ∑ k ∈ Finset.range 1, (harmonic k : ℂ) * harmonic (k + 1) / ((k : ℂ) * ((k : ℂ) + 1)) =
      riemannZeta 2 + 2 * riemannZeta 3 := by
    simp
  rw [hf, hv]
  exact hasSum_consecutive_pair_zeta

end FourConsecutiveHarmonicSeries
