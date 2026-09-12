/-
  Erdős Problem #142 — a bounded spectral consequence of a cyclic
  three-term-progression deficit.

  This file packages the standard balanced-indicator telescoping argument.
  It does not perform a density increment or an iteration.
-/

import Erdos.Erdos142.FourierAP
import Erdos.Erdos142.CyclicAPCount
import Mathlib.Tactic

set_option autoImplicit false

open Finset
open scoped BigOperators ComplexConjugate ZMod

namespace Erdos142

/-- The complex-valued `0/1` indicator of a finite subset of `ZMod p`. -/
def cyclicIndicator (p : ℕ) (A : Finset (ZMod p)) : ZMod p → ℂ :=
  fun x => if x ∈ A then 1 else 0

/-- The indicator of `A` balanced at its density inside `I`. -/
noncomputable def cyclicBalancedIndicator (p : ℕ) (I A : Finset (ZMod p)) :
    ZMod p → ℂ :=
  cyclicIndicator p A -
    (((A.card : ℝ) / (I.card : ℝ) : ℝ) : ℂ) • cyclicIndicator p I

/-- Ground truth: the cyclic indicator is one on its set. -/
example : cyclicIndicator 5 ({2} : Finset (ZMod 5)) 2 = 1 := by
  simp [cyclicIndicator]

/-- Ground truth: balancing a singleton inside a two-point set gives `1/2`
on that singleton. -/
example : cyclicBalancedIndicator 5 ({1, 2} : Finset (ZMod 5)) {2} 2 = 1 / 2 := by
  have hcard : ({1, 2} : Finset (ZMod 5)).card = 2 := by decide
  norm_num [cyclicBalancedIndicator, cyclicIndicator, hcard]

/-- Summing a cyclic indicator gives the cardinality of its support. -/
theorem sum_cyclicIndicator (p : ℕ) [NeZero p] (A : Finset (ZMod p)) :
    ∑ x : ZMod p, cyclicIndicator p A x = (A.card : ℂ) := by
  classical
  simp only [cyclicIndicator, Finset.sum_boole, filter_mem_eq_inter]
  rw [inter_eq_right.mpr (subset_univ A)]

/-- The spatial squared `L²` mass of an indicator is its cardinality. -/
theorem sum_sq_norm_cyclicIndicator (p : ℕ) [NeZero p]
    (A : Finset (ZMod p)) :
    ∑ x : ZMod p, ‖cyclicIndicator p A x‖ ^ 2 = (A.card : ℝ) := by
  classical
  calc
    (∑ x : ZMod p, ‖cyclicIndicator p A x‖ ^ 2) =
        ∑ x : ZMod p, if x ∈ A then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [cyclicIndicator, hx]
    _ = (A.card : ℝ) := by
      simp only [Finset.sum_boole, filter_mem_eq_inter]
      rw [inter_eq_right.mpr (subset_univ A)]

/-- Scaling an indicator by a nonnegative real scalar scales its squared
`L²` mass by the square of that scalar. -/
theorem sum_sq_norm_real_mul_cyclicIndicator (p : ℕ) [NeZero p]
    (a : ℝ) (ha : 0 ≤ a) (A : Finset (ZMod p)) :
    ∑ x : ZMod p, ‖(a : ℂ) * cyclicIndicator p A x‖ ^ 2 =
      a ^ 2 * (A.card : ℝ) := by
  have hnorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    (∑ x : ZMod p, ‖(a : ℂ) * cyclicIndicator p A x‖ ^ 2) =
        ∑ x : ZMod p, a ^ 2 * ‖cyclicIndicator p A x‖ ^ 2 := by
      apply sum_congr rfl
      intro x _
      rw [norm_mul, hnorm, mul_pow]
    _ = a ^ 2 * ∑ x : ZMod p, ‖cyclicIndicator p A x‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = a ^ 2 * (A.card : ℝ) := by
      rw [sum_sq_norm_cyclicIndicator]

/-- The trilinear AP sum of an indicator is the cyclic oriented progression
count, cast to `ℂ`. -/
theorem threeAPSum_cyclicIndicator (p : ℕ) [NeZero p]
    (A : Finset (ZMod p)) :
    threeAPSum p (cyclicIndicator p A) (cyclicIndicator p A)
      (cyclicIndicator p A) = (cyclicThreeAPCount p A : ℂ) := by
  classical
  rw [threeAPSum, cyclicThreeAPCount]
  rw [show (((((Finset.univ : Finset (ZMod p)).product Finset.univ).filter
      (fun xd => xd.1 ∈ A ∧ xd.1 + xd.2 ∈ A ∧
        xd.1 + 2 * xd.2 ∈ A)).card : ℕ) : ℂ) =
      (∑ xd ∈ (Finset.univ : Finset (ZMod p)).product Finset.univ,
        if xd.1 ∈ A ∧ xd.1 + xd.2 ∈ A ∧ xd.1 + 2 * xd.2 ∈ A
        then 1 else 0) by
    simp only [Finset.sum_boole]]
  simp only [cyclicIndicator]
  calc
    (∑ x : ZMod p, ∑ d : ZMod p,
        ((if x ∈ A then (1 : ℂ) else 0) *
          if x + d ∈ A then 1 else 0) *
          if x + 2 * d ∈ A then 1 else 0) =
        ∑ x : ZMod p, ∑ d : ZMod p,
          if x ∈ A ∧ x + d ∈ A ∧ x + 2 * d ∈ A then (1 : ℂ) else 0 := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro d _
      by_cases hx : x ∈ A <;>
        by_cases hy : x + d ∈ A <;>
          by_cases hz : x + 2 * d ∈ A <;> simp [hx, hy, hz]
    _ = ∑ xd ∈ (Finset.univ : Finset (ZMod p)).product
          (Finset.univ : Finset (ZMod p)),
          if xd.1 ∈ A ∧ xd.1 + xd.2 ∈ A ∧ xd.1 + 2 * xd.2 ∈ A
          then (1 : ℂ) else 0 := by
      exact (Finset.sum_product (Finset.univ : Finset (ZMod p))
        (Finset.univ : Finset (ZMod p))
        (fun xd => if xd.1 ∈ A ∧ xd.1 + xd.2 ∈ A ∧
          xd.1 + 2 * xd.2 ∈ A then (1 : ℂ) else 0)).symm

/-- Scaling all three entries of the AP form scales it cubically. -/
theorem threeAPSum_const_mul (p : ℕ) [NeZero p] (c : ℂ)
    (u v w : ZMod p → ℂ) :
    threeAPSum p (fun x => c * u x) (fun x => c * v x)
      (fun x => c * w x) = c ^ 3 * threeAPSum p u v w := by
  simp only [threeAPSum]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro d _
  ring

/-- A function on a nonempty finite type attains its largest norm. -/
theorem exists_max_norm {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℂ) :
    ∃ r M, 0 ≤ M ∧ (∀ x, ‖f x‖ ≤ M) ∧ ‖f r‖ = M := by
  classical
  let values : Finset ℝ := Finset.univ.image fun x => ‖f x‖
  have hvalues : values.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty ι›
    exact ⟨‖f x‖, by simp [values]⟩
  let M : ℝ := values.max' hvalues
  have hMmem : M ∈ values := Finset.max'_mem values hvalues
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hMmem
  refine ⟨r, M, ?_, ?_, ?_⟩
  · rw [← hr]
    exact norm_nonneg _
  · intro x
    exact Finset.le_max' values ‖f x‖ (by simp [values])
  · exact hr

/-- A positive deficit between the random-density baseline for `I` and the
cyclic three-term-progression count of `A` forces a large nonzero Fourier
coefficient of the balanced indicator. -/
theorem exists_nonzero_fourier_of_cyclic_deficit
    (p : ℕ) [NeZero p] (hp : Odd p) (I A : Finset (ZMod p))
    (hI : I.Nonempty) (hA : A.Nonempty) (hAI : A ⊆ I)
    (hdeficit :
      0 < ((A.card : ℝ) / (I.card : ℝ)) ^ 3 *
          (cyclicThreeAPCount p I : ℝ) - (cyclicThreeAPCount p A : ℝ)) :
    ∃ r : ZMod p, r ≠ 0 ∧
      (((A.card : ℝ) / (I.card : ℝ)) ^ 3 *
          (cyclicThreeAPCount p I : ℝ) - (cyclicThreeAPCount p A : ℝ)) /
          (3 * ((A.card : ℝ) / (I.card : ℝ)) * (I.card : ℝ)) ≤
        ‖unnormalizedDFT p (cyclicBalancedIndicator p I A) r‖ := by
  classical
  let α : ℝ := (A.card : ℝ) / (I.card : ℝ)
  let D : ℝ := α ^ 3 * (cyclicThreeAPCount p I : ℝ) -
    (cyclicThreeAPCount p A : ℝ)
  let uA : ZMod p → ℂ := cyclicIndicator p A
  let uI : ZMod p → ℂ := fun x => (α : ℂ) * cyclicIndicator p I x
  let F : ZMod p → ℂ := uA - uI
  change 0 < D at hdeficit
  change ∃ r : ZMod p, r ≠ 0 ∧
    D / (3 * α * (I.card : ℝ)) ≤
      ‖unnormalizedDFT p (cyclicBalancedIndicator p I A) r‖
  have hIcard : 0 < (I.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hI
  have hAcard : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hcard : (A.card : ℝ) ≤ (I.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hAI
  have hαpos : 0 < α := by
    exact div_pos hAcard hIcard
  have hα0 : 0 ≤ α := hαpos.le
  have hα1 : α ≤ 1 := by
    exact (div_le_one hIcard).2 hcard
  have hαI : α * (I.card : ℝ) = (A.card : ℝ) := by
    exact div_mul_cancel₀ (A.card : ℝ) hIcard.ne'
  have hαIComplex : (α : ℂ) * (I.card : ℂ) = (A.card : ℂ) := by
    exact_mod_cast hαI
  have hαsq : α ^ 2 ≤ α := by
    nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hα1)]
  have hscaled : α ^ 2 * (I.card : ℝ) ≤ (A.card : ℝ) := by
    calc
      α ^ 2 * (I.card : ℝ) ≤ α * (I.card : ℝ) :=
        mul_le_mul_of_nonneg_right hαsq hIcard.le
      _ = (A.card : ℝ) := hαI
  have hL2A : ∑ x : ZMod p, ‖uA x‖ ^ 2 = (A.card : ℝ) := by
    exact sum_sq_norm_cyclicIndicator p A
  have hL2I : ∑ x : ZMod p, ‖uI x‖ ^ 2 =
      α ^ 2 * (I.card : ℝ) := by
    exact sum_sq_norm_real_mul_cyclicIndicator p α hα0 I
  have hsqrt : Real.sqrt (α ^ 2 * (I.card : ℝ)) ≤
      Real.sqrt (A.card : ℝ) := Real.sqrt_le_sqrt hscaled
  obtain ⟨r, M, hM, hFourier, hr⟩ :=
    exists_max_norm (fun s => unnormalizedDFT p F s)
  have hfirst : ‖threeAPSum p F uA uA‖ ≤ M * (A.card : ℝ) := by
    calc
      ‖threeAPSum p F uA uA‖ ≤
          M * Real.sqrt (∑ x : ZMod p, ‖uA x‖ ^ 2) *
            Real.sqrt (∑ x : ZMod p, ‖uA x‖ ^ 2) :=
        norm_threeAPSum_le_spatial_of_first_fourier_bound p hp F uA uA M hM hFourier
      _ = M * (A.card : ℝ) := by
        rw [hL2A]
        calc
          M * Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ) =
              M * (Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ)) := by ring
          _ = M * (A.card : ℝ) := by rw [Real.mul_self_sqrt hAcard.le]
  have hmiddle : ‖threeAPSum p uI F uA‖ ≤ M * (A.card : ℝ) := by
    calc
      ‖threeAPSum p uI F uA‖ ≤
          M * Real.sqrt (∑ x : ZMod p, ‖uI x‖ ^ 2) *
            Real.sqrt (∑ x : ZMod p, ‖uA x‖ ^ 2) :=
        norm_threeAPSum_le_spatial_of_middle_fourier_bound p uI F uA M hM hFourier
      _ = M * Real.sqrt (α ^ 2 * (I.card : ℝ)) *
            Real.sqrt (A.card : ℝ) := by rw [hL2I, hL2A]
      _ ≤ M * Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hM) (Real.sqrt_nonneg _)
      _ = M * (A.card : ℝ) := by
        calc
          M * Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ) =
              M * (Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ)) := by ring
          _ = M * (A.card : ℝ) := by rw [Real.mul_self_sqrt hAcard.le]
  have hlast : ‖threeAPSum p uI uI F‖ ≤ M * (A.card : ℝ) := by
    calc
      ‖threeAPSum p uI uI F‖ ≤
          M * Real.sqrt (∑ x : ZMod p, ‖uI x‖ ^ 2) *
            Real.sqrt (∑ x : ZMod p, ‖uI x‖ ^ 2) :=
        norm_threeAPSum_le_spatial_of_last_fourier_bound p hp uI uI F M hM hFourier
      _ = M * Real.sqrt (α ^ 2 * (I.card : ℝ)) *
            Real.sqrt (α ^ 2 * (I.card : ℝ)) := by rw [hL2I]
      _ ≤ M * Real.sqrt (A.card : ℝ) *
            Real.sqrt (α ^ 2 * (I.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hM) (Real.sqrt_nonneg _)
      _ ≤ M * Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg hM (Real.sqrt_nonneg _))
      _ = M * (A.card : ℝ) := by
        calc
          M * Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ) =
              M * (Real.sqrt (A.card : ℝ) * Real.sqrt (A.card : ℝ)) := by ring
          _ = M * (A.card : ℝ) := by rw [Real.mul_self_sqrt hAcard.le]
  have hAPA : threeAPSum p uA uA uA = (cyclicThreeAPCount p A : ℂ) := by
    exact threeAPSum_cyclicIndicator p A
  have hAPI : threeAPSum p uI uI uI =
      (α : ℂ) ^ 3 * (cyclicThreeAPCount p I : ℂ) := by
    calc
      threeAPSum p uI uI uI =
          (α : ℂ) ^ 3 * threeAPSum p (cyclicIndicator p I)
            (cyclicIndicator p I) (cyclicIndicator p I) :=
        threeAPSum_const_mul p (α : ℂ) (cyclicIndicator p I)
          (cyclicIndicator p I) (cyclicIndicator p I)
      _ = (α : ℂ) ^ 3 * (cyclicThreeAPCount p I : ℂ) := by
        rw [threeAPSum_cyclicIndicator]
  have hFsub : uA - uI = F := rfl
  have htel : threeAPSum p uA uA uA - threeAPSum p uI uI uI =
      threeAPSum p F uA uA + threeAPSum p uI F uA +
        threeAPSum p uI uI F := by
    simpa only [hFsub] using threeAPSum_sub_threeAPSum p uA uA uA uI uI uI
  have hdiff : threeAPSum p uA uA uA - threeAPSum p uI uI uI =
      -(D : ℂ) := by
    rw [hAPA, hAPI]
    dsimp only [D]
    push_cast
    ring
  have hsum : threeAPSum p F uA uA + threeAPSum p uI F uA +
      threeAPSum p uI uI F = -(D : ℂ) := htel.symm.trans hdiff
  have hnorm : ‖threeAPSum p F uA uA + threeAPSum p uI F uA +
      threeAPSum p uI uI F‖ = D := by
    rw [hsum, norm_neg, Complex.norm_real, Real.norm_of_nonneg hdeficit.le]
  have hDle : D ≤ 3 * M * (A.card : ℝ) := by
    calc
      D = ‖threeAPSum p F uA uA + threeAPSum p uI F uA +
          threeAPSum p uI uI F‖ := hnorm.symm
      _ ≤ ‖threeAPSum p F uA uA + threeAPSum p uI F uA‖ +
          ‖threeAPSum p uI uI F‖ := norm_add_le _ _
      _ ≤ (‖threeAPSum p F uA uA‖ + ‖threeAPSum p uI F uA‖) +
          ‖threeAPSum p uI uI F‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ (M * (A.card : ℝ) + M * (A.card : ℝ)) +
          M * (A.card : ℝ) := add_le_add (add_le_add hfirst hmiddle) hlast
      _ = 3 * M * (A.card : ℝ) := by ring
  have hMpos : 0 < M := by
    by_contra hnot
    have hMzero : M = 0 := le_antisymm (le_of_not_gt hnot) hM
    rw [hMzero] at hDle
    norm_num at hDle
    exact (not_lt_of_ge hDle) hdeficit
  have hsumF : ∑ x : ZMod p, F x = 0 := by
    change (∑ x : ZMod p, (cyclicIndicator p A x -
      (α : ℂ) * cyclicIndicator p I x)) = 0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cyclicIndicator,
      sum_cyclicIndicator, hαIComplex, sub_self]
  have hDFTzero : unnormalizedDFT p F 0 = 0 := by
    rw [unnormalizedDFT_zero, hsumF]
  have hrne : r ≠ 0 := by
    intro hre
    subst r
    rw [hDFTzero, norm_zero] at hr
    linarith
  have hden : 0 < 3 * α * (I.card : ℝ) := by positivity
  have hquot : D / (3 * α * (I.card : ℝ)) ≤ M := by
    apply (div_le_iff₀ hden).2
    calc
      D ≤ 3 * M * (A.card : ℝ) := hDle
      _ = M * (3 * α * (I.card : ℝ)) := by rw [← hαI]; ring
  refine ⟨r, hrne, ?_⟩
  change D / (3 * α * (I.card : ℝ)) ≤
    ‖unnormalizedDFT p F r‖
  rw [hr]
  exact hquot

set_option maxRecDepth 100000 in
/-- Joint ground truth for the generic theorem: the eight-point set
`{0,1,3,4,9,10,12,13}` inside the first nineteen residues modulo `41`
has a strictly positive cyclic deficit. -/
example :
    let I := natCyclicImage 41 (Finset.range 19)
    let A := natCyclicImage 41 ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ)
    ∃ r : ZMod 41, r ≠ 0 ∧
      (((A.card : ℝ) / (I.card : ℝ)) ^ 3 *
          (cyclicThreeAPCount 41 I : ℝ) - (cyclicThreeAPCount 41 A : ℝ)) /
          (3 * ((A.card : ℝ) / (I.card : ℝ)) * (I.card : ℝ)) ≤
        ‖unnormalizedDFT 41 (cyclicBalancedIndicator 41 I A) r‖ := by
  dsimp only
  apply exists_nonzero_fourier_of_cyclic_deficit 41 (by norm_num)
  · decide
  · decide
  · decide
  · have hIcard : (natCyclicImage 41 (Finset.range 19)).card = 19 := by decide
    have hAcard :
        (natCyclicImage 41
          ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ)).card = 8 := by decide
    have hIcount :
        cyclicThreeAPCount 41 (natCyclicImage 41 (Finset.range 19)) = 181 := by decide
    have hAcount :
        cyclicThreeAPCount 41
          (natCyclicImage 41
            ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ)) = 8 := by decide
    norm_num [hIcard, hAcard, hIcount, hAcount]

/-- Boundary ground truth: for `{0,1,3,4}` inside the first eight residues
modulo `19`, the cyclic deficit is exactly zero rather than positive. -/
example :
    let I := natCyclicImage 19 (Finset.range 8)
    let A := natCyclicImage 19 ({0, 1, 3, 4} : Finset ℕ)
    ((A.card : ℝ) / (I.card : ℝ)) ^ 3 *
        (cyclicThreeAPCount 19 I : ℝ) - (cyclicThreeAPCount 19 A : ℝ) = 0 := by
  dsimp only
  have hIcard : (natCyclicImage 19 (Finset.range 8)).card = 8 := by decide
  have hAcard :
      (natCyclicImage 19 ({0, 1, 3, 4} : Finset ℕ)).card = 4 := by decide
  have hIcount :
      cyclicThreeAPCount 19 (natCyclicImage 19 (Finset.range 8)) = 32 := by decide
  have hAcount :
      cyclicThreeAPCount 19
        (natCyclicImage 19 ({0, 1, 3, 4} : Finset ℕ)) = 4 := by decide
  norm_num [hIcard, hAcard, hIcount, hAcount]

#check @cyclicIndicator
#check @cyclicBalancedIndicator
#check @threeAPSum_cyclicIndicator
#check @exists_nonzero_fourier_of_cyclic_deficit

#print axioms sum_cyclicIndicator
#print axioms sum_sq_norm_cyclicIndicator
#print axioms threeAPSum_cyclicIndicator
#print axioms exists_nonzero_fourier_of_cyclic_deficit

end Erdos142
