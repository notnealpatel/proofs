import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false

namespace ComplexNormalSeries

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- A series normally bounded on every centered closed ball is summable at every point. -/
theorem summable_of_normal (f : ℕ → E → F)
    (hnormal : ∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n x, x ∈ Metric.closedBall (0 : E) R → ‖f n x‖ ≤ u n)
    (x : E) : Summable (fun n => f n x) := by
  obtain ⟨u, hu, hbound⟩ := hnormal (‖x‖ + 1) (by positivity)
  apply hu.of_norm_bounded
  intro n
  apply hbound n x
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (show ‖x‖ ≤ ‖x‖ + 1 by linarith)

/-- Normal convergence on centered closed balls preserves complex differentiability,
for an arbitrary complex normed domain and complete complex normed codomain. -/
theorem differentiable_tsum_of_normal (f : ℕ → E → F)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hnormal : ∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n x, x ∈ Metric.closedBall (0 : E) R → ‖f n x‖ ≤ u n) :
    Differentiable ℂ (fun x => ∑' n, f n x) := by
  intro x
  let R : ℝ := ‖x‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨u, hu, hbound⟩ := hnormal (R + 1) (by linarith)
  have hderiv : ∀ n y, y ∈ Metric.ball (0 : E) R →
      ‖fderiv ℂ (f n) y‖ ≤ 2 * u n := by
    intro n y hy
    have hyR : ‖y‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    have hylarge : y ∈ Metric.closedBall (0 : E) (R + 1) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hmaps : Set.MapsTo (f n) (Metric.ball y 1)
        (Metric.closedBall (f n y) (2 * u n)) := by
      intro z hz
      have hzR : ‖z‖ ≤ R + 1 := by
        have hdist : ‖z - y‖ < 1 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hz
        calc
          ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith
      have hzlarge : z ∈ Metric.closedBall (0 : E) (R + 1) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hzR
      simp only [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖f n z - f n y‖ ≤ ‖f n z‖ + ‖f n y‖ := norm_sub_le _ _
        _ ≤ u n + u n := add_le_add (hbound n z hzlarge) (hbound n y hylarge)
        _ = 2 * u n := by ring
    have hschwarz := Complex.norm_fderiv_le_div_of_mapsTo_ball
      (hf n).differentiableOn hmaps (by norm_num : (0 : ℝ) < 1)
    simpa only [div_one] using hschwarz
  have hx : x ∈ Metric.ball (0 : E) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  have hzero : (0 : E) ∈ Metric.ball (0 : E) R := by
    simpa only [Metric.mem_ball, dist_self] using hR
  exact (hasFDerivAt_tsum_of_isPreconnected (hu.mul_left 2) Metric.isOpen_ball
    (convex_ball (0 : E) R).isPreconnected
    (fun n y _ => (hf n y).hasFDerivAt) hderiv hzero
    (summable_of_normal f hnormal 0) hx).differentiableAt

example :
    (∀ _n : ℕ, Differentiable ℂ (fun _ : ℂ × ℂ => (0 : ℂ × ℂ))) ∧
    (∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n (x : ℂ × ℂ), x ∈ Metric.closedBall (0 : ℂ × ℂ) R →
        ‖(fun (_ : ℕ) (_ : ℂ × ℂ) => (0 : ℂ × ℂ)) n x‖ ≤ u n) := by
  constructor
  · intro n
    exact differentiable_const _
  · intro R hR
    exact ⟨fun _ => 0, summable_zero, by intros; simp⟩

end ComplexNormalSeries
