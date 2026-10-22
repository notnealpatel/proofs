/-
# A108211: Kimberling's harmonic-floor identity

Clark Kimberling's conjecture (OEIS A108211, 2014-09-09) states, for `n ≥ 1`,
`⌊1/(1/(4n) - log 2 + H_{2n} - H_n)⌋ = 16n² + 1`.

Writing the denominator as `x n`, its telescoping difference is
`1/(4n(n+1)(2n+1))`, and `x n → 0` by the Euler–Mascheroni limit.
Comparing differences with `1/(16n²+c)`, for `c = 1, 2`, gives
`1/(16n²+2) < x n < 1/(16n²+1)` and hence the floor identity.

The guard `1 ≤ n` matches the source offset and is essential: at `n = 0`
the empty sum and totalized division give a floor of `-2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A108211HarmonicFloor

open Filter Topology Finset

/-- The OEIS sequence A108211: `a n = 16 n^2 + 1` (offset 1). -/
def a (n : ℕ) : ℕ := 16 * n ^ 2 + 1

example : (List.range 10).map (fun i => a (i + 1)) =
    [17, 65, 145, 257, 401, 577, 785, 1025, 1297, 1601] := by decide

/-- The tail sum `1/(n+1) + 1/(n+2) + ⋯ + 1/(2n)` of the conjecture. -/
noncomputable def tailSum (n : ℕ) : ℝ := ∑ k ∈ Icc (n + 1) (2 * n), (1 : ℝ) / k

example : tailSum 0 = 0 := by simp [tailSum]

example : tailSum 2 = 7 / 12 := by
  rw [tailSum, show Icc (2 + 1) (2 * 2) = {3, 4} by decide]
  norm_num

/-- The denominator of the conjecture:
`x n = 1/(4n) - log 2 + (1/(n+1) + ⋯ + 1/(2n))`. -/
noncomputable def x (n : ℕ) : ℝ := 1 / (4 * (n : ℝ)) - Real.log 2 + tailSum n

example : x 1 = 1 / 4 - Real.log 2 + 1 / 2 := by
  rw [x, tailSum, show Icc (1 + 1) (2 * 1) = {2} by decide]
  norm_num

/-- The tail sum is a difference of harmonic numbers: `tailSum n = H_{2n} - H_n`. -/
lemma tailSum_eq_harmonic (n : ℕ) :
    tailSum n = (harmonic (2 * n) : ℝ) - harmonic n := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  push_cast
  have h := Finset.sum_Ioc_consecutive (fun i : ℕ => ((i : ℝ))⁻¹) (Nat.zero_le n)
    (by omega : n ≤ 2 * n)
  have e : ∀ a b : ℕ, Icc (a + 1) b = Ioc a b := fun a b => by
    ext i
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [tailSum, e, e 0, e 0]
  simp only [one_div]
  linarith

/-- Telescoping step: for `n ≥ 1`, `x n - x (n+1) = 1/(4n(n+1)(2n+1))`. -/
lemma x_sub_x_succ (n : ℕ) (hn : 1 ≤ n) :
    x n - x (n + 1) = 1 / (4 * n * (n + 1) * (2 * n + 1)) := by
  have h1 : (n : ℝ) ≠ 0 := by positivity
  simp only [x, tailSum_eq_harmonic, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, harmonic_succ]
  push_cast
  field_simp
  ring

/-- `x n → 0`, from `H_m - log m → γ` applied at `m = n` and `m = 2n`. -/
lemma tendsto_x : Tendsto x atTop (𝓝 0) := by
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id]; omega) tendsto_id
  have h1 := Real.tendsto_harmonic_sub_log.comp h2n
  have h2 := Real.tendsto_harmonic_sub_log
  have h4 : Tendsto (fun n : ℕ => (1 / 4 : ℝ) * (1 / (n : ℝ))) atTop (𝓝 ((1 / 4) * 0)) :=
    tendsto_one_div_atTop_nhds_zero_nat.const_mul _
  have hsum := h4.add (h1.sub h2)
  rw [mul_zero, sub_self, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, x, tailSum_eq_harmonic]
  push_cast
  rw [Real.log_mul two_ne_zero hn0]
  field_simp
  ring

/-- For `m ≥ 1`, the step `1/(4m(m+1)(2m+1))` is smaller than the step of
`1/(16m^2+1)` (the difference of cross-products is `32m^2 + 32m - 17`). -/
lemma step_lt_upper (m : ℝ) (hm : 1 ≤ m) :
    1 / (4 * m * (m + 1) * (2 * m + 1)) < 1 / (16 * m ^ 2 + 1) - 1 / (16 * (m + 1) ^ 2 + 1) := by
  rw [div_sub_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hm]

/-- For `m ≥ 1`, the step `1/(4m(m+1)(2m+1))` is larger than the step of
`1/(16m^2+2)` (the difference of cross-products is `36`). -/
lemma lower_lt_step (m : ℝ) (hm : 1 ≤ m) :
    1 / (16 * m ^ 2 + 2) - 1 / (16 * (m + 1) ^ 2 + 2) < 1 / (4 * m * (m + 1) * (2 * m + 1)) := by
  rw [div_sub_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hm]

/-- For `0 ≤ c`, `1/(16(k+1)^2 + c) → 0`. -/
lemma tendsto_g (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun k : ℕ => 1 / (16 * ((k : ℝ) + 1) ^ 2 + c)) atTop (𝓝 0) := by
  have hat : Tendsto (fun k : ℕ => 16 * ((k : ℝ) + 1) ^ 2 + c) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hat

/-- Upper bound: for `n ≥ 1`, `x n < 1/(16n^2+1)`. -/
lemma x_lt_upper (n : ℕ) (hn : 1 ≤ n) : x n < 1 / (16 * (n : ℝ) ^ 2 + 1) := by
  let y : ℕ → ℝ := fun k => x (k + 1) - 1 / (16 * ((k : ℝ) + 1) ^ 2 + 1)
  have hy : StrictMono y := by
    refine strictMono_nat_of_lt_succ (fun k => ?_)
    have hstep := x_sub_x_succ (k + 1) (by omega)
    have hineq := step_lt_upper ((k : ℝ) + 1) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
    simp only [y]
    push_cast at hstep ⊢
    linarith
  have hlim : Tendsto y atTop (𝓝 0) := by
    have := (tendsto_x.comp (tendsto_add_atTop_nat 1)).sub (tendsto_g 1 zero_le_one)
    rw [sub_zero] at this
    exact this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := hy (Nat.lt_succ_self k)
  have h2 := hy.monotone.ge_of_tendsto hlim (k + 1)
  simp only [y] at h1 h2
  push_cast at h1 h2 ⊢
  linarith

/-- Lower bound: for `n ≥ 1`, `1/(16n^2+2) < x n`. -/
lemma lower_lt_x (n : ℕ) (hn : 1 ≤ n) : 1 / (16 * (n : ℝ) ^ 2 + 2) < x n := by
  let z : ℕ → ℝ := fun k => x (k + 1) - 1 / (16 * ((k : ℝ) + 1) ^ 2 + 2)
  have hz : StrictAnti z := by
    refine strictAnti_nat_of_succ_lt (fun k => ?_)
    have hstep := x_sub_x_succ (k + 1) (by omega)
    have hineq := lower_lt_step ((k : ℝ) + 1) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
    simp only [z]
    push_cast at hstep ⊢
    linarith
  have hlim : Tendsto z atTop (𝓝 0) := by
    have := (tendsto_x.comp (tendsto_add_atTop_nat 1)).sub (tendsto_g 2 zero_le_two)
    rw [sub_zero] at this
    exact this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := hz (Nat.lt_succ_self k)
  have h2 := hz.antitone.le_of_tendsto hlim (k + 1)
  simp only [z] at h1 h2
  push_cast at h1 h2 ⊢
  linarith

/-- Kimberling's conjecture (OEIS A108211, 2014-09-09): for `n ≥ 1`,
`⌊1/(1/(4n) - log 2 + ∑_{k=n+1}^{2n} 1/k)⌋ = a n = 16n²+1`.
The guard matches the entry's offset. -/
theorem kimberling_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ⌊(1 : ℝ) / (1 / (4 * (n : ℝ)) - Real.log 2 + ∑ k ∈ Icc (n + 1) (2 * n), (1 : ℝ) / k)⌋
      = (a n : ℤ) := by
  change ⌊1 / x n⌋ = _
  rw [a]
  have hlo := lower_lt_x n hn
  have hup := x_lt_upper n hn
  have hpos : 0 < x n := lt_trans (by positivity) hlo
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_div_iff₀ hpos]
    rw [lt_div_iff₀ (by positivity)] at hup
    linarith
  · rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ (by positivity)] at hlo
    linarith

example : ⌊(1 : ℝ) / (1 / (4 * ((1 : ℕ) : ℝ)) - Real.log 2 +
    ∑ k ∈ Icc ((1 : ℕ) + 1) (2 * 1), (1 : ℝ) / k)⌋ = 17 :=
  kimberling_conjecture 1 le_rfl

end Candidates.A108211HarmonicFloor
