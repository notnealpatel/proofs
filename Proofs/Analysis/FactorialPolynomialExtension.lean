import Analysis.ComplexPolynomialGrowth
import Analysis.ComplexNormalSeries
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

open scoped BigOperators Topology
open Filter Polynomial

namespace FactorialPolynomialExtension

private theorem summable_growth (a c : ℕ) (R C : ℝ) :
    Summable (fun n : ℕ => (2 * C / (n.factorial : ℝ)) *
      (2 * (R + 1)) ^ (2 * (a * (n + 1) + c)) *
        Real.exp (2 * (((a * (n + 1) + c : ℕ) : ℝ) + 1))) := by
  let t : ℝ := 2 * (R + 1)
  let K : ℝ := 2 * C * t ^ (2 * (a + c)) * Real.exp (2 * ((a + c : ℕ) + 1))
  let A : ℝ := t ^ (2 * a) * Real.exp (2 * (a : ℝ))
  have heq : ∀ n : ℕ, (2 * C / (n.factorial : ℝ)) *
      t ^ (2 * (a * (n + 1) + c)) *
        Real.exp (2 * (((a * (n + 1) + c : ℕ) : ℝ) + 1)) =
      K * (A ^ n / (n.factorial : ℝ)) := by
    intro n
    have hdeg : 2 * (a * (n + 1) + c) = 2 * (a + c) + (2 * a) * n := by ring
    have hexp : 2 * (((a * (n + 1) + c : ℕ) : ℝ) + 1) =
        2 * ((a + c : ℕ) + 1 : ℝ) + (n : ℝ) * (2 * (a : ℝ)) := by
      push_cast
      ring
    dsimp [K, A]
    rw [hdeg, hexp, pow_add, pow_mul, Real.exp_add, Real.exp_nat_mul, mul_pow]
    ring
  simpa only [← heq] using (Real.summable_pow_div_factorial A).mul_left K

/-- Factorially accurate, separately polynomial complex approximants with linear degree
 growth give an entire extension of a real profile on the closed unit square, together
 with convergence of the approximants at every complex pair. This is
 conditional on the stated global polynomial representations, not an assertion that a
 particular endpoint profile or Bernstein construction satisfies them. -/
theorem exists_differentiable_extension_with_tendsto
    (a c : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (b : ℕ → ℂ × ℂ → ℂ) (P : ℝ × ℝ → ℝ)
    (hb : ∀ n, Differentiable ℂ (b n))
    (hx : ∀ n w, ∃ p : ℂ[X], p.natDegree ≤ a * n + c ∧
      ∀ z, p.eval z = b n (z, w))
    (hy : ∀ n z, ∃ p : ℂ[X], p.natDegree ≤ a * n + c ∧
      ∀ w, p.eval w = b n (z, w))
    (herr : ∀ n (x y : ℝ), x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      ‖b n ((x : ℂ), (y : ℂ)) - (P (x, y) : ℂ)‖ ≤ C / (n.factorial : ℝ)) :
    ∃ E : ℂ × ℂ → ℂ, Differentiable ℂ E ∧
      (∀ z, Tendsto (fun n => b n z) atTop (𝓝 (E z))) ∧
      ∀ (x y : ℝ), x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        E ((x : ℂ), (y : ℂ)) = (P (x, y) : ℂ) := by
  let f : ℕ → ℂ × ℂ → ℂ := fun n z => b (n + 1) z - b n z
  have hf : ∀ n, Differentiable ℂ (f n) := fun n => (hb (n + 1)).sub (hb n)
  have hpoly (h : ∀ n w, ∃ p : ℂ[X], p.natDegree ≤ a * n + c ∧
      ∀ z, p.eval z = b n (z, w)) (n : ℕ) (w : ℂ) :
      ∃ p : ℂ[X], p.natDegree ≤ a * (n + 1) + c ∧
        ∀ z, p.eval z = f n (z, w) := by
    obtain ⟨p, hp, hep⟩ := h (n + 1) w
    obtain ⟨q, hq, heq⟩ := h n w
    refine ⟨p - q, (natDegree_sub_le p q).trans (max_le hp ?_), ?_⟩
    · exact hq.trans (by gcongr; omega)
    · intro z
      simp only [eval_sub, hep, heq, f]
  have hpolyY (n : ℕ) (z : ℂ) :
      ∃ p : ℂ[X], p.natDegree ≤ a * (n + 1) + c ∧
        ∀ w, p.eval w = f n (z, w) := by
    obtain ⟨p, hp, hep⟩ := hy (n + 1) z
    obtain ⟨q, hq, heq⟩ := hy n z
    refine ⟨p - q, (natDegree_sub_le p q).trans (max_le hp ?_), ?_⟩
    · exact hq.trans (by gcongr; omega)
    · intro w
      simp only [eval_sub, hep, heq, f]
  have hsquare (n : ℕ) (x y : ℝ) (hx0 : x ∈ Set.Icc 0 1)
      (hy0 : y ∈ Set.Icc 0 1) :
      ‖f n ((x : ℂ), (y : ℂ))‖ ≤ 2 * C / (n.factorial : ℝ) := by
    have hfac : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    have he : C / ((n + 1).factorial : ℝ) ≤ C / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left hC (by positivity) hfac
    calc
      _ = ‖(b (n + 1) ((x : ℂ), (y : ℂ)) - (P (x, y) : ℂ)) -
          (b n ((x : ℂ), (y : ℂ)) - (P (x, y) : ℂ))‖ := by congr 1; dsimp [f]; ring
      _ ≤ _ := norm_sub_le _ _
      _ ≤ C / (n.factorial : ℝ) + C / (n.factorial : ℝ) :=
        add_le_add ((herr (n + 1) x y hx0 hy0).trans he) (herr n x y hx0 hy0)
      _ = _ := by ring
  have hnormal : ∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n z, z ∈ Metric.closedBall (0 : ℂ × ℂ) R → ‖f n z‖ ≤ u n := by
    intro R hR
    refine ⟨_, summable_growth a c R C, ?_⟩
    intro n z hz
    have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact ComplexPolynomialGrowth.norm_le_of_separately_polynomial
      (a * (n + 1) + c) R (2 * C / (n.factorial : ℝ)) hR.le (by positivity)
      (fun v w => f n (v, w)) (hpoly hx n) (hpolyY n) (hsquare n)
      z.1 z.2 ((norm_fst_le z).trans hzR) ((norm_snd_le z).trans hzR)
  let E : ℂ × ℂ → ℂ := fun z => b 0 z + ∑' n, f n z
  have hlim (z : ℂ × ℂ) : Tendsto (fun n => b n z) atTop (𝓝 (E z)) := by
    have hsum := ComplexNormalSeries.summable_of_normal f hnormal z
    have htel (n : ℕ) : ∑ k ∈ Finset.range n, f k z = b n z - b 0 z := by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; dsimp [f]; ring
    have ht := hsum.hasSum.tendsto_sum_nat.const_add (b 0 z)
    simpa only [htel, add_sub_cancel] using ht
  refine ⟨E, (hb 0).add
    (ComplexNormalSeries.differentiable_tsum_of_normal f hf hnormal), hlim, ?_⟩
  intro x y hx0 hy0
  let z : ℂ × ℂ := ((x : ℂ), (y : ℂ))
  have herrlim : Tendsto (fun n : ℕ => C / (n.factorial : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((Real.summable_pow_div_factorial 1).mul_left C).tendsto_atTop_zero
  have hlimP : Tendsto (fun n => b n z) atTop (𝓝 (P (x, y) : ℂ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => herr n x y hx0 hy0) herrlim
  exact tendsto_nhds_unique (hlim z) hlimP


/-- Factorially accurate, separately polynomial complex approximants with linear degree
 growth give an entire extension of a real profile on the closed unit square. This is
 conditional on the stated global polynomial representations, not an assertion that a
 particular endpoint profile or Bernstein construction satisfies them. -/
theorem exists_differentiable_extension
    (a c : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (b : ℕ → ℂ × ℂ → ℂ) (P : ℝ × ℝ → ℝ)
    (hb : ∀ n, Differentiable ℂ (b n))
    (hx : ∀ n w, ∃ p : ℂ[X], p.natDegree ≤ a * n + c ∧
      ∀ z, p.eval z = b n (z, w))
    (hy : ∀ n z, ∃ p : ℂ[X], p.natDegree ≤ a * n + c ∧
      ∀ w, p.eval w = b n (z, w))
    (herr : ∀ n (x y : ℝ), x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      ‖b n ((x : ℂ), (y : ℂ)) - (P (x, y) : ℂ)‖ ≤ C / (n.factorial : ℝ)) :
    ∃ E : ℂ × ℂ → ℂ, Differentiable ℂ E ∧
      ∀ (x y : ℝ), x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        E ((x : ℂ), (y : ℂ)) = (P (x, y) : ℂ) := by
  obtain ⟨E, hE, _, hEP⟩ :=
    exists_differentiable_extension_with_tendsto a c C hC b P hb hx hy herr
  exact ⟨E, hE, hEP⟩

example :
    ∃ E : ℂ × ℂ → ℂ, Differentiable ℂ E ∧
      (∀ z, Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (E z))) ∧
      ∀ (x y : ℝ), x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        E ((x : ℂ), (y : ℂ)) = (1 : ℂ) := by
  let b : ℕ → ℂ × ℂ → ℂ := fun _ _ => 1
  let P : ℝ × ℝ → ℝ := fun _ => 1
  have hC : (0 : ℝ) ≤ 1 := by norm_num
  have hb : ∀ n, Differentiable ℂ (b n) := fun _ => differentiable_const 1
  have hx : ∀ n w, ∃ p : ℂ[X], p.natDegree ≤ 0 * n + 0 ∧
      ∀ z, p.eval z = b n (z, w) := by
    intro n w
    exact ⟨C 1, by simp, by simp [b]⟩
  have hy : ∀ n z, ∃ p : ℂ[X], p.natDegree ≤ 0 * n + 0 ∧
      ∀ w, p.eval w = b n (z, w) := by
    intro n z
    exact ⟨C 1, by simp, by simp [b]⟩
  have herr : ∀ n (x y : ℝ), x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      ‖b n ((x : ℂ), (y : ℂ)) - (P (x, y) : ℂ)‖ ≤ 1 / (n.factorial : ℝ) := by
    intro n x y hx0 hy0
    simp only [b, P, Complex.ofReal_one, sub_self, norm_zero]
    positivity
  exact exists_differentiable_extension_with_tendsto 0 0 1 hC b P hb hx hy herr

example : (0 : ℝ) ∈ Set.Icc 0 1 ∧ (1 : ℝ) ∈ Set.Icc 0 1 := by
  norm_num

end FactorialPolynomialExtension
