/-
  Erdős Problem #142 — an explicit optimized finite density step.

  The scale parameters are selected by rounding
  `2 * α * sqrt (N / (768 * π))` down.  The resulting specialization of the
  interval spectral density increment records both the density gain and the
  square-root loss in interval length.  This module performs no iteration.
-/

import Erdos.Erdos142.IntervalSpectralDeficit
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace Erdos142

set_option maxHeartbeats 800000 in
/-- The floor and quotient parameters used in the optimized density step obey
all hypotheses of the bounded affine density-increment theorem. -/
theorem optimizedDensityStep_parameters
    (N : ℕ) (α : ℝ) (hN : 0 < N) (hα : 0 < α) (hαone : α ≤ 1)
    (hthreshold : 768 * Real.pi ≤ α ^ 2 * (N : ℝ)) :
    let x : ℝ := α * Real.sqrt ((N : ℝ) / (768 * Real.pi))
    let K : ℕ := Nat.floor (2 * x)
    let Q : ℕ := N / K
    0 < K ∧ 0 < Q ∧ Q * K ≤ N ∧
      8 * Real.pi * (K : ℝ) ≤ (α ^ 2 / 12) * (Q : ℝ) ∧
      x ≤ (K : ℝ) ∧ (K : ℝ) ≤ 2 * x ∧ K ≤ N / 2 := by
  let C : ℝ := 768 * Real.pi
  let x : ℝ := α * Real.sqrt ((N : ℝ) / C)
  let K : ℕ := Nat.floor (2 * x)
  let Q : ℕ := N / K
  have hpi : 0 < Real.pi := Real.pi_pos
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hCfour : 4 < C := by
    dsimp only [C]
    nlinarith [Real.pi_gt_three]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hαsq : 0 ≤ α ^ 2 := sq_nonneg α
  have hαsqone : α ^ 2 ≤ 1 := by nlinarith
  have hthresholdC : C ≤ α ^ 2 * (N : ℝ) := by
    simpa only [C] using hthreshold
  have hCN : C ≤ (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hαsqone hNr.le
    nlinarith
  have hratioNonneg : 0 ≤ (N : ℝ) / C := by positivity
  have hratioOne : 1 ≤ (N : ℝ) / C := by
    apply (le_div_iff₀ hC).2
    simpa only [one_mul] using hCN
  have hsqrtNonneg : 0 ≤ Real.sqrt ((N : ℝ) / C) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt ((N : ℝ) / C)) ^ 2 = (N : ℝ) / C := by
    exact Real.sq_sqrt hratioNonneg
  have hxNonneg : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hscaledRatio : 1 ≤ α ^ 2 * ((N : ℝ) / C) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hC).2
    simpa only [one_mul] using hthresholdC
  have hxOne : 1 ≤ x := by
    dsimp only [x]
    nlinarith [hsqrtSq]
  have hsqrtRatioLe : Real.sqrt ((N : ℝ) / C) ≤ (N : ℝ) / C := by
    nlinarith [hsqrtSq]
  have hxRatio : x ≤ (N : ℝ) / C := by
    dsimp only [x]
    have hmul : α * Real.sqrt ((N : ℝ) / C) ≤
        1 * Real.sqrt ((N : ℝ) / C) :=
      mul_le_mul_of_nonneg_right hαone hsqrtNonneg
    nlinarith
  have hKupper : (K : ℝ) ≤ 2 * x := by
    dsimp only [K]
    exact Nat.floor_le (by positivity)
  have hKlowerStrict : 2 * x - 1 < (K : ℝ) := by
    dsimp only [K]
    have hfloor := Nat.lt_floor_add_one (2 * x)
    linarith
  have hxK : x ≤ (K : ℝ) := by
    linarith
  have hKrPos : 0 < (K : ℝ) := lt_of_lt_of_le (by positivity : 0 < x) hxK
  have hK : 0 < K := by exact_mod_cast hKrPos
  have hKhalfR : (K : ℝ) ≤ (N : ℝ) / 2 := by
    have hCfour' : 4 ≤ C := hCfour.le
    have hfourx : 4 * x ≤ (N : ℝ) := by
      calc
        4 * x ≤ 4 * ((N : ℝ) / C) := by nlinarith [hxRatio]
        _ ≤ (N : ℝ) := by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hC).2
          have hmul := mul_le_mul_of_nonneg_right hCfour' hNr.le
          nlinarith
    nlinarith [hKupper]
  have htwoKN : 2 * K ≤ N := by
    exact_mod_cast (show (2 : ℝ) * (K : ℝ) ≤ (N : ℝ) by nlinarith [hKhalfR])
  have hKhalf : K ≤ N / 2 := by omega
  have hKN : K ≤ N := by omega
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact Nat.div_pos hKN hK
  have hQK : Q * K ≤ N := by
    dsimp only [Q]
    exact Nat.div_mul_le_self N K
  have hdivision : N < K * (Q + 1) := by
    dsimp only [Q]
    exact Nat.lt_mul_div_succ N hK
  have hdivisionR : (N : ℝ) < (K : ℝ) * ((Q : ℝ) + 1) := by
    exact_mod_cast hdivision
  have hNKQ : (N : ℝ) - (K : ℝ) < (K : ℝ) * (Q : ℝ) := by
    nlinarith [hdivisionR]
  have hxSq : x ^ 2 = α ^ 2 * ((N : ℝ) / C) := by
    dsimp only [x]
    rw [mul_pow, hsqrtSq]
  have hKsq : (K : ℝ) ^ 2 ≤ 4 * α ^ 2 * ((N : ℝ) / C) := by
    nlinarith [sq_nonneg (2 * x - (K : ℝ)), hxSq, hKupper]
  have h96 : 96 * Real.pi * (K : ℝ) ^ 2 ≤
      α ^ 2 * (N : ℝ) / 2 := by
    have hCeq : C = 768 * Real.pi := rfl
    rw [hCeq] at hKsq
    have hpiNe : Real.pi ≠ 0 := hpi.ne'
    field_simp [hpiNe] at hKsq ⊢
    nlinarith [hKsq, hpi]
  have hαK : α ^ 2 * (K : ℝ) ≤ α ^ 2 * (N : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hKhalfR hαsq]
  have h96sub : 96 * Real.pi * (K : ℝ) ^ 2 ≤
      α ^ 2 * ((N : ℝ) - (K : ℝ)) := by
    nlinarith [h96, hαK]
  have hαNKQ : α ^ 2 * ((N : ℝ) - (K : ℝ)) <
      α ^ 2 * ((K : ℝ) * (Q : ℝ)) := by
    exact mul_lt_mul_of_pos_left hNKQ (sq_pos_of_pos hα)
  have h96strict : 96 * Real.pi * (K : ℝ) ^ 2 <
      α ^ 2 * ((K : ℝ) * (Q : ℝ)) := h96sub.trans_lt hαNKQ
  have hscaleCore : 96 * Real.pi * (K : ℝ) < α ^ 2 * (Q : ℝ) := by
    have hfactored : (K : ℝ) * (96 * Real.pi * (K : ℝ)) <
        (K : ℝ) * (α ^ 2 * (Q : ℝ)) := by
      convert h96strict using 1 <;> ring
    exact lt_of_mul_lt_mul_left hfactored hKrPos.le
  have hscale : 8 * Real.pi * (K : ℝ) ≤
      (α ^ 2 / 12) * (Q : ℝ) := by
    nlinarith [hscaleCore]
  simpa only [C, x, K, Q] using
    And.intro hK (And.intro hQ (And.intro hQK
      (And.intro hscale (And.intro hxK (And.intro hKupper hKhalf)))))

/-- An AP-free set of density `α` above the explicit threshold has an AP-free
pullback of density at least `α + α²/48` and length between the stated
square-root scales. -/
theorem exists_optimized_density_step_of_threeAPFree
    (N : ℕ) (A : Finset ℕ) (hN : 0 < N)
    (hA : A ⊆ Finset.range N) (hAnonempty : A.Nonempty)
    (hfree : ThreeAPFree (A : Set ℕ))
    (hthreshold : 768 * Real.pi ≤
      ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ)) :
    let α : ℝ := (A.card : ℝ) / (N : ℝ)
    ∃ m : ℕ, ∃ B : Finset ℕ,
      B ⊆ Finset.range m ∧ B.Nonempty ∧ ThreeAPFree (B : Set ℕ) ∧
      α + α ^ 2 / 48 ≤ (B.card : ℝ) / (m : ℝ) ∧ m ≤ N ∧
      α * Real.sqrt ((N : ℝ) / (768 * Real.pi)) ≤ (m : ℝ) ∧
      (m : ℝ) < 4 * α * Real.sqrt ((N : ℝ) / (768 * Real.pi)) := by
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  let x : ℝ := α * Real.sqrt ((N : ℝ) / (768 * Real.pi))
  let K : ℕ := Nat.floor (2 * x)
  let Q : ℕ := N / K
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hAr : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAnonempty
  have hα : 0 < α := by
    dsimp only [α]
    positivity
  have hcard : A.card ≤ N := by
    simpa only [Finset.card_range] using Finset.card_le_card hA
  have hαone : α ≤ 1 := by
    dsimp only [α]
    exact (div_le_one hNr).2 (by exact_mod_cast hcard)
  obtain ⟨hK, hQ, hQK, hscale, hxK, hKupper, hKhalf⟩ :=
    optimizedDensityStep_parameters N α hN hα hαone (by
      simpa only [α] using hthreshold)
  have hdense : 4 ≤ α ^ 2 * (N : ℝ) := by
    have hpi := Real.pi_gt_three
    nlinarith [hthreshold]
  obtain ⟨d, a, m, P, B, hd, hdQ, hdK, hPform, hBform, hPsub, hBsub,
      hmK, hm2K, hPcard, hinc, hBcard, hfreeB⟩ :=
    exists_affine_density_increment_of_threeAPFree A N Q K hN hA
      hAnonempty hfree (by simpa only [α] using hdense) hQ hK hQK
      (by simpa only [α] using hscale)
  have hdensity : α + α ^ 2 / 48 ≤ (B.card : ℝ) / (m : ℝ) := by
    simpa only [α, hBcard, hPcard] using hinc
  have hBcardPosR : 0 < (B.card : ℝ) := by
    have hgainPos : α < α + α ^ 2 / 48 := by
      nlinarith [sq_pos_of_pos hα]
    have hdensityPos : 0 < (B.card : ℝ) / (m : ℝ) :=
      hα.trans (hgainPos.trans_le hdensity)
    rcases (div_pos_iff.mp hdensityPos) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (by positivity : 0 ≤ (B.card : ℝ))) hneg.1)
  have hBnonempty : B.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hBcardPosR
  have hKhalf' : K ≤ N / 2 := by
    simpa only [K, x] using hKhalf
  have hmN : m ≤ N := by omega
  have hxm : x ≤ (m : ℝ) := by
    exact hxK.trans (by exact_mod_cast hmK)
  have hm4x : (m : ℝ) < 4 * x := by
    have hm2Kr : (m : ℝ) < 2 * (K : ℝ) := by exact_mod_cast hm2K
    nlinarith [hKupper]
  refine ⟨m, B, hBsub, hBnonempty, hfreeB, hdensity, hmN, ?_, ?_⟩
  · simpa only [x, α] using hxm
  · simpa only [x, α, mul_assoc] using hm4x

/-- If a density floor `δ` is already fixed, the optimized AP-free transition
has new interval length at least `sqrt (N / ((768π) / δ²))`.  This is the
natural-state interface used by the separate abstract iteration. -/
theorem exists_optimized_density_step_of_density_floor
    (N : ℕ) (A : Finset ℕ) (δ : ℝ) (hN : 0 < N)
    (hA : A ⊆ Finset.range N) (hAnonempty : A.Nonempty)
    (hfree : ThreeAPFree (A : Set ℕ)) (hδ : 0 < δ)
    (hδdensity : δ ≤ (A.card : ℝ) / (N : ℝ))
    (hsize : 768 * Real.pi / δ ^ 2 ≤ (N : ℝ)) :
    let α : ℝ := (A.card : ℝ) / (N : ℝ)
    ∃ m : ℕ, ∃ B : Finset ℕ,
      B ⊆ Finset.range m ∧ B.Nonempty ∧ ThreeAPFree (B : Set ℕ) ∧
      α + α ^ 2 / 48 ≤ (B.card : ℝ) / (m : ℝ) ∧ m ≤ N ∧
      Real.sqrt ((N : ℝ) / ((768 * Real.pi) / δ ^ 2)) ≤ (m : ℝ) := by
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hthresholdδ : 768 * Real.pi ≤ δ ^ 2 * (N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hδsq).1 hsize
  have hthreshold : 768 * Real.pi ≤ α ^ 2 * (N : ℝ) := by
    have hα : 0 < α := lt_of_lt_of_le hδ hδdensity
    have hsquares : δ ^ 2 ≤ α ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsquares (by positivity : 0 ≤ (N : ℝ))]
  obtain ⟨m, B, hBsub, hBnonempty, hfreeB, hdensity, hmN, hmLower, hmUpper⟩ :=
    exists_optimized_density_step_of_threeAPFree N A hN hA hAnonempty hfree
      (by simpa only [α] using hthreshold)
  have hradicand :
      (N : ℝ) / ((768 * Real.pi) / δ ^ 2) =
        δ ^ 2 * ((N : ℝ) / (768 * Real.pi)) := by
    field_simp [hδ.ne', Real.pi_ne_zero]
  have hsqrtIdentity :
      Real.sqrt ((N : ℝ) / ((768 * Real.pi) / δ ^ 2)) =
        δ * Real.sqrt ((N : ℝ) / (768 * Real.pi)) := by
    rw [hradicand]
    rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have hδLower :
      δ * Real.sqrt ((N : ℝ) / (768 * Real.pi)) ≤ (m : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hδdensity (Real.sqrt_nonneg _)).trans hmLower
  refine ⟨m, B, hBsub, hBnonempty, hfreeB, hdensity, hmN, ?_⟩
  rw [hsqrtIdentity]
  exact hδLower

/-- The parameter assumptions are jointly satisfiable at density `1/2`. -/
example :
    let α : ℝ := 1 / 2
    0 < α ∧ α ≤ 1 ∧
      768 * Real.pi ≤ α ^ 2 * (16384 : ℝ) := by
  dsimp only
  constructor
  · norm_num
  constructor
  · norm_num
  · nlinarith [Real.pi_lt_four]

#check @optimizedDensityStep_parameters
#check @exists_optimized_density_step_of_threeAPFree
#check @exists_optimized_density_step_of_density_floor

#print axioms optimizedDensityStep_parameters
#print axioms exists_optimized_density_step_of_threeAPFree
#print axioms exists_optimized_density_step_of_density_floor

end Erdos142
