/-
  Erdős Problem #142 — the bounded finite interval spectral bridge.

  A deficit in the natural ordered three-term-progression count is transported
  to an odd cyclic group of size `2N+1`.  The cyclic spectral estimate then
  supplies one large balanced exponential correlation.  The final theorem
  composes this bridge once with the accepted affine density-increment lemma;
  it performs no Roth iteration.
-/

import Erdos.Erdos142.SpectralDeficit
import Erdos.Erdos142.FourierIntervalTransport
import Erdos.Erdos142.CyclicAPCount
import Erdos.Erdos142.FourierIncrement

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos142

/-- The natural interval three-AP deficit: the random-density baseline formed
with the exact ordered-pair count of `range N`, minus the ordered-pair count
`A.card + 2 * threeAPCount A` of `A`. -/
noncomputable def intervalAPDeficit (N : ℕ) (A : Finset ℕ) : ℝ :=
  ((A.card : ℝ) / (N : ℝ)) ^ 3 *
      (naturalThreeAPPairs (Finset.range N)).card -
    (A.card : ℝ) - 2 * (threeAPCount A : ℝ)

/-- Ground truth: the eight ternary-digit points below `14` have deficit
`72/7`. -/
example :
    intervalAPDeficit 14 ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ) = 72 / 7 := by
  have hcard : ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ).card = 8 := by decide
  have hcount : threeAPCount ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ) = 0 := by decide
  have hpairs : (naturalThreeAPPairs (Finset.range 14)).card = 98 := by decide
  norm_num [intervalAPDeficit, hcard, hcount, hpairs]

/-- A positive natural interval AP deficit forces a large balanced
exponential correlation.  The witnessing phase is obtained explicitly from
a nonzero frequency modulo `2N+1`. -/
theorem exists_large_balanced_correlation_of_intervalAPDeficit_pos
    (N : ℕ) (A : Finset ℕ) (hN : 0 < N)
    (hA : A ⊆ Finset.range N) (hAnonempty : A.Nonempty)
    (hdeficit : 0 < intervalAPDeficit N A) :
    ∃ θ : ℝ,
      intervalAPDeficit N A /
          (3 * ((A.card : ℝ) / (N : ℝ)) * (N : ℝ)) ≤
        ‖∑ n ∈ Finset.range N,
          (balancedIndicator (Finset.range N) A n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * θ * (n : ℝ))‖ := by
  let p : ℕ := 2 * N + 1
  have hpne : NeZero p := ⟨by dsimp only [p]; omega⟩
  letI : NeZero p := hpne
  have hpOdd : Odd p := by
    dsimp only [p]
    exact ⟨N, by omega⟩
  have hnoWrap : 2 * N < p := by
    dsimp only [p]
    omega
  have hNp : N < p := by omega
  let I : Finset (ZMod p) := natCyclicImage p (Finset.range N)
  let B : Finset (ZMod p) := natCyclicImage p A
  have hIcard : I.card = N := by
    dsimp only [I]
    simpa only [Finset.card_range] using
      card_natCyclicImage_eq_card p N (Finset.range N) (fun _ h => h) hNp.le
  have hBcard : B.card = A.card := by
    dsimp only [B]
    exact card_natCyclicImage_eq_card p N A hA hNp.le
  have hInonempty : I.Nonempty := by
    apply Finset.card_pos.mp
    rw [hIcard]
    exact hN
  have hBnonempty : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    exact Finset.card_pos.mpr hAnonempty
  have hBI : B ⊆ I := by
    dsimp only [B, I, natCyclicImage]
    exact Finset.image_mono (fun a : ℕ => (a : ZMod p)) hA
  have hIcount : cyclicThreeAPCount p I =
      (naturalThreeAPPairs (Finset.range N)).card := by
    dsimp only [I]
    exact cyclicThreeAPCount_eq_card_naturalThreeAPPairs p N
      (Finset.range N) (fun _ h => h) hnoWrap hpOdd
  have hBcount : cyclicThreeAPCount p B =
      A.card + 2 * threeAPCount A := by
    dsimp only [B]
    exact cyclicThreeAPCount_natCyclicImage p N A hA hnoWrap hpOdd
  have hcyclicDeficit :
      0 < ((B.card : ℝ) / (I.card : ℝ)) ^ 3 *
          (cyclicThreeAPCount p I : ℝ) - (cyclicThreeAPCount p B : ℝ) := by
    rw [hIcard, hBcard, hIcount, hBcount]
    push_cast
    simpa only [intervalAPDeficit, sub_sub] using hdeficit
  obtain ⟨r, hr, hlarge⟩ :=
    exists_nonzero_fourier_of_cyclic_deficit p hpOdd I B hInonempty
      hBnonempty hBI hcyclicDeficit
  let θ : ℝ := -((r.val : ℝ) / (p : ℝ))
  refine ⟨θ, ?_⟩
  have htransport := unnormalizedDFT_balanced_natCyclicImage_eq_interval_sum
    p N A hA hN hNp r
  have hbalanced : cyclicBalancedIndicator p I B = fun x =>
      (if x ∈ B then (1 : ℂ) else 0) -
        (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ) *
          (if x ∈ I then (1 : ℂ) else 0) := by
    funext x
    simp only [cyclicBalancedIndicator, cyclicIndicator, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hBcard, hIcard]
  rw [hbalanced, htransport] at hlarge
  rw [hIcard, hBcard, hIcount, hBcount] at hlarge
  push_cast at hlarge
  push_cast
  simpa only [intervalAPDeficit, sub_sub, θ, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_natCast] using hlarge

/-- An AP-free subset of `range N` with `α²N ≥ 4` has a balanced
Fourier correlation of size at least `α²N/12`, where
`α = A.card / N`. -/
theorem exists_large_balanced_correlation_of_threeAPFree
    (N : ℕ) (A : Finset ℕ) (hN : 0 < N)
    (hA : A ⊆ Finset.range N) (hAnonempty : A.Nonempty)
    (hfree : ThreeAPFree (A : Set ℕ))
    (hdense : 4 ≤ ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ)) :
    ∃ θ : ℝ,
      ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ) / 12 ≤
        ‖∑ n ∈ Finset.range N,
          (balancedIndicator (Finset.range N) A n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * θ * (n : ℝ))‖ := by
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  let S : ℝ := (naturalThreeAPPairs (Finset.range N)).card
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hAr : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAnonempty
  have hα : 0 < α := div_pos hAr hNr
  have hcount : threeAPCount A = 0 := (threeAPCount_eq_zero_iff A).2 hfree
  have hbaseline : (N : ℝ) ^ 2 ≤ 2 * S := by
    dsimp only [S]
    exact_mod_cast sq_le_two_mul_card_naturalThreeAPPairs_range N
  have hscaledBaseline : α ^ 3 * (N : ℝ) ^ 2 ≤ 2 * (α ^ 3 * S) := by
    nlinarith [mul_le_mul_of_nonneg_left hbaseline (by positivity : 0 ≤ α ^ 3)]
  have hαN : α * (N : ℝ) = (A.card : ℝ) := by
    dsimp only [α]
    exact div_mul_cancel₀ (A.card : ℝ) hNr.ne'
  have hdense' : 4 ≤ α ^ 2 * (N : ℝ) := by
    simpa only [α] using hdense
  have hcardBound : 4 * (A.card : ℝ) ≤ α ^ 3 * (N : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hdense' (mul_nonneg hα.le hNr.le)
    rw [hαN] at hmul
    nlinarith
  have hdeficitForm : intervalAPDeficit N A =
      α ^ 3 * S - (A.card : ℝ) := by
    simp only [intervalAPDeficit, hcount, Nat.cast_zero, mul_zero, sub_zero,
      α, S]
  have hdeficitLower : α ^ 3 * (N : ℝ) ^ 2 / 4 ≤
      intervalAPDeficit N A := by
    rw [hdeficitForm]
    nlinarith
  have hdeficitPos : 0 < intervalAPDeficit N A := by
    have hlowerPos : 0 < α ^ 3 * (N : ℝ) ^ 2 / 4 := by positivity
    exact hlowerPos.trans_le hdeficitLower
  obtain ⟨θ, hθ⟩ :=
    exists_large_balanced_correlation_of_intervalAPDeficit_pos N A hN hA
      hAnonempty hdeficitPos
  refine ⟨θ, ?_⟩
  apply le_trans ?_ hθ
  have hden : 0 < 3 * α * (N : ℝ) := by positivity
  apply (le_div_iff₀ hden).2
  rw [show ((A.card : ℝ) / (N : ℝ)) = α by rfl]
  nlinarith [hdeficitLower]

/-- One bounded density-increment step for an AP-free interval set.
Under the explicit scale conditions, the resulting affine progression has
length in `[K, 2K)`, density at least `α + α²/48`, and an AP-free pullback.
No iteration is asserted. -/
theorem exists_affine_density_increment_of_threeAPFree
    (A : Finset ℕ) (N Q K : ℕ)
    (hN : 0 < N) (hA : A ⊆ Finset.range N) (hAnonempty : A.Nonempty)
    (hfree : ThreeAPFree (A : Set ℕ))
    (hdense : 4 ≤ ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ))
    (hQ : 0 < Q) (hK : 0 < K) (hQK : Q * K ≤ N)
    (hscale : 8 * Real.pi * (K : ℝ) ≤
      (((A.card : ℝ) / (N : ℝ)) ^ 2 / 12) * (Q : ℝ)) :
    ∃ d a m : ℕ, ∃ P B : Finset ℕ,
      0 < d ∧ d ≤ Q ∧ d * K ≤ N ∧
      P = (Finset.range m).image (fun i => a + d * i) ∧
      B = (Finset.range m).filter (fun i => a + d * i ∈ A) ∧
      P ⊆ Finset.range N ∧ B ⊆ Finset.range m ∧
      K ≤ m ∧ m < 2 * K ∧ P.card = m ∧
      (A.card : ℝ) / N + ((A.card : ℝ) / N) ^ 2 / 48 ≤
        ((A ∩ P).card : ℝ) / P.card ∧
      B.card = (A ∩ P).card ∧ ThreeAPFree (B : Set ℕ) := by
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  let η : ℝ := α ^ 2 / 12
  have hAr : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAnonempty
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hα : 0 < α := div_pos hAr hNr
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨θ, hcorr⟩ :=
    exists_large_balanced_correlation_of_threeAPFree N A hN hA hAnonempty
      hfree hdense
  have hcorr' : η * (N : ℝ) ≤
      ‖∑ n ∈ Finset.range N,
        (balancedIndicator (Finset.range N) A n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * θ * (n : ℝ))‖ := by
    dsimp only [η, α]
    nlinarith
  have hscale' : 8 * Real.pi * (K : ℝ) ≤ η * (Q : ℝ) := by
    simpa only [η, α] using hscale
  obtain ⟨d, a, m, P, B, hd, hdQ, hdK, hPform, hBform, hPsub,
      hBsub, hmK, hm2K, hPcard, hinc, hBcard, hfreePullback⟩ :=
    exists_affine_density_increment_of_fourier_correlation A N Q K θ η hA
      hQ hK hQK hη hscale' hcorr'
  have hdensity : (A.card : ℝ) / N + ((A.card : ℝ) / N) ^ 2 / 48 ≤
      ((A ∩ P).card : ℝ) / P.card := by
    calc
      (A.card : ℝ) / N + ((A.card : ℝ) / N) ^ 2 / 48 =
          (A.card : ℝ) / N + η / 4 := by
        dsimp only [η, α]
        ring
      _ ≤ ((A ∩ P).card : ℝ) / P.card := hinc
  exact ⟨d, a, m, P, B, hd, hdQ, hdK, hPform, hBform, hPsub, hBsub,
    hmK, hm2K, hPcard, hdensity, hBcard, hfreePullback hfree⟩

/-- Joint satisfiability for the AP-free spectral corollary: the eight
numbers with ternary digits in `{0,1}` below `14` are AP-free and satisfy
`α²N ≥ 4`. -/
example :
    let A : Finset ℕ := {0, 1, 3, 4, 9, 10, 12, 13}
    A ⊆ Finset.range 14 ∧ A.Nonempty ∧ ThreeAPFree (A : Set ℕ) ∧
      4 ≤ ((A.card : ℝ) / (14 : ℝ)) ^ 2 * (14 : ℝ) := by
  dsimp only
  refine ⟨by decide, by decide, (threeAPCount_eq_zero_iff _).mp (by decide), ?_⟩
  norm_num

#check @intervalAPDeficit
#check @exists_large_balanced_correlation_of_intervalAPDeficit_pos
#check @exists_large_balanced_correlation_of_threeAPFree
#check @exists_affine_density_increment_of_threeAPFree

#print axioms exists_large_balanced_correlation_of_intervalAPDeficit_pos
#print axioms exists_large_balanced_correlation_of_threeAPFree
#print axioms exists_affine_density_increment_of_threeAPFree

end Erdos142
