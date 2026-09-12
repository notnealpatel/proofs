/-
  Erdős Problem #142 — bounded Fourier-to-affine density increment.

  Dirichlet approximation selects a bounded positive step on which the
  exponential character is nearly constant. The accepted affine increment
  theorem then supplies an explicit progression and its affine pullback.

  This is conditional on the stated large balanced Fourier correlation; it
  does not derive that correlation from three-AP-freeness or an AP count.
-/

import Erdos.Erdos142.SmallPhase
import Erdos.Erdos142.AffineIncrement

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- A large balanced correlation with the Fourier character
`n ↦ exp (2 * π * I * θ * n)` yields a density increment on an explicit
finite affine progression. Its positive common difference is at most `Q`, its
length lies in `[K, 2 * K)`, and the affine pullback inherits three-AP-freeness. -/
theorem exists_affine_density_increment_of_fourier_correlation
    (A : Finset ℕ) (N Q K : ℕ) (θ η : ℝ)
    (hAU : A ⊆ Finset.range N) (hQ : 0 < Q) (hK : 0 < K)
    (hQK : Q * K ≤ N) (hη : 0 < η)
    (hscale : 8 * Real.pi * (K : ℝ) ≤ η * (Q : ℝ))
    (hcorr : η * (N : ℝ) ≤
      ‖∑ x ∈ Finset.range N,
        (balancedIndicator (Finset.range N) A x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * θ * x)‖) :
    ∃ d a m : ℕ, ∃ P B : Finset ℕ,
      0 < d ∧ d ≤ Q ∧ d * K ≤ N ∧
      P = (Finset.range m).image (fun i => a + d * i) ∧
      B = (Finset.range m).filter (fun i => a + d * i ∈ A) ∧
      P ⊆ Finset.range N ∧ B ⊆ Finset.range m ∧
      K ≤ m ∧ m < 2 * K ∧ P.card = m ∧
      (A.card : ℝ) / N + η / 4 ≤ ((A ∩ P).card : ℝ) / P.card ∧
      B.card = (A ∩ P).card ∧
      (ThreeAPFree (A : Set ℕ) → ThreeAPFree (B : Set ℕ)) := by
  let χ : ℕ → ℂ := fun n => Complex.exp (2 * Real.pi * Complex.I * θ * n)
  let δ : ℝ := 2 * Real.pi / (Q : ℝ)
  obtain ⟨d, hd, hdQ, hdK, hphase⟩ := exists_small_phase_step θ hQ hQK
  have hadd : ∀ m n, χ (m + n) = χ m * χ n := by
    intro m n
    rw [show χ (m + n) = Complex.exp
      ((2 * Real.pi * Complex.I * θ * m) +
       (2 * Real.pi * Complex.I * θ * n)) by
      dsimp only [χ]
      congr 1
      push_cast
      ring]
    exact Complex.exp_add _ _
  have hnorm : ∀ n, ‖χ n‖ = 1 := by
    intro n
    rw [Complex.norm_exp]
    simp
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hhalf : ((2 * K : ℕ) : ℝ) * δ ≤ η / 2 := by
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    calc
      ((2 * K : ℕ) : ℝ) * δ = 4 * Real.pi * (K : ℝ) / (Q : ℝ) := by
        dsimp only [δ]
        push_cast
        ring
      _ ≤ η / 2 := by
        rw [div_le_iff₀ hQr]
        nlinarith [hscale]
  obtain ⟨a, m, P, B, hPform, hBform, hPsub, hBsub, hmK, hm2K,
      hPcard, hinc, hBcard, hfree⟩ :=
    exists_affine_density_increment_of_correlation A N d K χ δ η hAU hd hK hdK
      hadd hnorm hδ (by simpa only [χ, δ] using hphase) hη hhalf
      (by simpa only [χ] using hcorr)
  exact ⟨d, a, m, P, B, hd, hdQ, hdK, hPform, hBform, hPsub, hBsub,
    hmK, hm2K, hPcard, hinc, hBcard, hfree⟩

/-- The hypotheses are jointly satisfiable at a nontrivial scale: for
`N = 256`, `Q = 128`, `K = 2`, `θ = 1 / 2`, and `η = 1 / 2`, the 128 even
points have balanced Fourier correlation exactly 128. -/
example :
    let A := (Finset.range 128).image (fun i => 2 * i)
    A ⊆ Finset.range 256 ∧ 1 < A.card ∧
      0 < (128 : ℕ) ∧ 0 < (2 : ℕ) ∧ 128 * 2 ≤ 256 ∧
      0 < (1 / 2 : ℝ) ∧
      8 * Real.pi * (2 : ℝ) ≤ (1 / 2 : ℝ) * (128 : ℝ) ∧
      (1 / 2 : ℝ) * (256 : ℝ) ≤
        ‖∑ x ∈ Finset.range 256,
          (balancedIndicator (Finset.range 256) A x : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ) * x)‖ := by
  dsimp only
  have hsub : (Finset.range 128).image (fun i => 2 * i) ⊆
      Finset.range 256 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hi ⊢
    omega
  have hcardA : ((Finset.range 128).image (fun i => 2 * i)).card = 128 := by
    rw [Finset.card_image_of_injective]
    · rfl
    · intro x y hxy
      exact Nat.mul_left_cancel (by norm_num) hxy
  refine ⟨hsub, by omega, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · nlinarith [Real.pi_le_four]
  · have hmem (x : ℕ) (hx : x < 256) :
        x ∈ (Finset.range 128).image (fun i => 2 * i) ↔ Even x := by
      constructor
      · intro hxin
        obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp hxin
        rw [← hxi]
        exact even_two_mul i
      · rintro ⟨i, hxi⟩
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_range.mpr ?_, ?_⟩
        · omega
        · omega
    have hexp (x : ℕ) :
        Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ) * x) =
          (-1 : ℂ) ^ x := by
      rw [show 2 * Real.pi * Complex.I * (1 / 2 : ℝ) * x =
          (x : ℂ) * (Real.pi * Complex.I) by
        push_cast
        ring]
      rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    have hsummand (x : ℕ) (hx : x < 256) :
        (balancedIndicator (Finset.range 256)
              ((Finset.range 128).image (fun i => 2 * i)) x : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ) * x) =
          (1 / 2 : ℂ) := by
      rw [hexp]
      simp only [balancedIndicator, hcardA, Finset.card_range]
      rw [neg_one_pow_eq_ite]
      by_cases heven : Even x
      · rw [if_pos heven, if_pos ((hmem x hx).2 heven)]
        norm_num
      · have hnotmem : x ∉ (Finset.range 128).image (fun i => 2 * i) :=
          fun hxin => heven ((hmem x hx).1 hxin)
        rw [if_neg heven, if_neg hnotmem]
        norm_num
    have hsum :
        ∑ x ∈ Finset.range 256,
          (balancedIndicator (Finset.range 256)
              ((Finset.range 128).image (fun i => 2 * i)) x : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ) * x) =
          (128 : ℂ) := by
      calc
        _ = ∑ x ∈ Finset.range 256, (1 / 2 : ℂ) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hsummand x (Finset.mem_range.mp hx)
        _ = (128 : ℂ) := by norm_num
    rw [hsum]
    norm_num

#check @exists_affine_density_increment_of_fourier_correlation
#print axioms exists_affine_density_increment_of_fourier_correlation

end Erdos142
