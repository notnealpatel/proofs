/-
  Erdős Problem #142 — a classical Roth-scale explicit finite threshold.

  This combines the optimized one-step density increment with the abstract
  density iteration.  It is an explicit double-exponential bound, not the
  asymptotic statement of Erdős Problem #142 and not the strongest known
  quantitative form of Roth's theorem.
-/

import Erdos.Erdos142.DensityIteration
import Erdos.Erdos142.OptimizedDensityStep

set_option autoImplicit false

namespace Erdos142

/-- The explicit finite threshold produced by the optimized density iteration. -/
noncomputable def explicitRothThreshold (δ : ℝ) : ℝ :=
  ((768 * Real.pi) / δ ^ 2) ^ (2 ^ (Nat.ceil (49 / δ) + 1))

example : explicitRothThreshold 1 =
    (768 * Real.pi) ^ (2 ^ 50) := by
  norm_num [explicitRothThreshold]

private theorem explicitRothThreshold_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < explicitRothThreshold δ := by
  unfold explicitRothThreshold
  positivity

/-- A positive-density three-term-progression-free subset of `range N` forces
`N` below the classical explicit double-exponential Roth threshold. -/
theorem size_lt_explicitRothThreshold_of_threeAPFree
    (δ : ℝ) (N : ℕ) (A : Finset ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hN : 0 < N)
    (hA : A ⊆ Finset.range N) (hfree : ThreeAPFree (A : Set ℕ))
    (hdensity : δ ≤ (A.card : ℝ) / (N : ℝ)) :
    (N : ℝ) < explicitRothThreshold δ := by
  have hAnonempty : A.Nonempty := by
    apply Finset.card_pos.mp
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hcardr : 0 < (A.card : ℝ) := by
      have hdensityPos : 0 < (A.card : ℝ) / (N : ℝ) := hδ.trans_le hdensity
      rcases div_pos_iff.mp hdensityPos with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge (by positivity : 0 ≤ (A.card : ℝ))) hneg.1)
    exact_mod_cast hcardr
  let State := {p : ℕ × Finset ℕ //
    0 < p.1 ∧ p.2.Nonempty ∧ p.2 ⊆ Finset.range p.1 ∧
      ThreeAPFree (p.2 : Set ℕ)}
  let size : State → ℝ := fun s => (s.1.1 : ℝ)
  let density : State → ℝ := fun s => (s.1.2.card : ℝ) / (s.1.1 : ℝ)
  let B : ℝ := (768 * Real.pi) / δ ^ 2
  have hB : 1 < B := by
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hδsqone : δ ^ 2 ≤ 1 := by nlinarith [sq_nonneg δ]
    have hnum : 1 < 768 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hnum_nonneg : 0 ≤ 768 * Real.pi := by positivity
    have hnum_le : 768 * Real.pi ≤ (768 * Real.pi) / δ ^ 2 := by
      apply (le_div_iff₀ hδsq).2
      nlinarith [mul_le_mul_of_nonneg_left hδsqone hnum_nonneg]
    exact hnum.trans_le hnum_le
  have hdensityState : ∀ s : State, 0 < density s ∧ density s ≤ 1 := by
    intro s
    have hsN : 0 < s.1.1 := s.2.1
    have hsNr : 0 < (s.1.1 : ℝ) := by exact_mod_cast hsN
    have hsCard : 0 < s.1.2.card := Finset.card_pos.mpr s.2.2.1
    have hsCardr : 0 < (s.1.2.card : ℝ) := by exact_mod_cast hsCard
    have hcard_le : s.1.2.card ≤ s.1.1 := by
      simpa only [Finset.card_range] using Finset.card_le_card s.2.2.2.1
    dsimp only [density]
    constructor
    · positivity
    · exact (div_le_one hsNr).2 (by exact_mod_cast hcard_le)
  have hsizeState : ∀ s : State, 0 ≤ size s := by
    intro s
    dsimp only [size]
    positivity
  have hstep : ∀ s : State, δ ≤ density s → B ≤ size s →
      ∃ s', density s + density s ^ 2 / 48 ≤ density s' ∧
        Real.sqrt (size s / B) ≤ size s' := by
    intro s hsδ hslarge
    obtain ⟨m, C, hCsub, hCnonempty, hCfree, hCinc, hmN, hmLower⟩ :=
      exists_optimized_density_step_of_density_floor s.1.1 s.1.2 δ s.2.1
        s.2.2.2.1 s.2.2.1 s.2.2.2.2 hδ (by simpa only [density] using hsδ)
        (by simpa only [B, size] using hslarge)
    have hm : 0 < m := by
      have hcardPos : 0 < C.card := Finset.card_pos.mpr hCnonempty
      have hcardLe : C.card ≤ m := by
        simpa only [Finset.card_range] using Finset.card_le_card hCsub
      omega
    let s' : State := ⟨(m, C), hm, hCnonempty, hCsub, hCfree⟩
    refine ⟨s', ?_, ?_⟩
    · simpa only [density, s'] using hCinc
    · simpa only [size, B, s'] using hmLower
  let s₀ : State := ⟨(N, A), hN, hAnonempty, hA, hfree⟩
  have hresult := size_lt_explicit_threshold size density hδ hδone hB
    hdensityState hsizeState hstep s₀ (by simpa only [density, s₀] using hdensity)
  simpa only [size, B, s₀, explicitRothThreshold] using hresult

/-- Product-form variant of the explicit finite Roth threshold.  The assumption
`0 < N` prevents the density hypothesis from being an empty-interval artifact. -/
theorem size_lt_explicitRothThreshold_of_mul_le_card
    (δ : ℝ) (N : ℕ) (A : Finset ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hN : 0 < N)
    (hA : A ⊆ Finset.range N) (hfree : ThreeAPFree (A : Set ℕ))
    (hdensity : δ * (N : ℝ) ≤ (A.card : ℝ)) :
    (N : ℝ) < explicitRothThreshold δ := by
  apply size_lt_explicitRothThreshold_of_threeAPFree δ N A hδ hδone hN hA hfree
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  exact (le_div_iff₀ hNr).2 hdensity

/-- Above the explicit threshold, the Roth number has density strictly less
than `δ`. -/
theorem rothNumberNat_lt_mul_of_explicitRothThreshold_le
    (δ : ℝ) (N : ℕ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hthreshold : explicitRothThreshold δ ≤ (N : ℝ)) :
    (rothNumberNat N : ℝ) < δ * (N : ℝ) := by
  have hNr : 0 < (N : ℝ) :=
    (explicitRothThreshold_pos hδ).trans_le hthreshold
  have hN : 0 < N := by exact_mod_cast hNr
  obtain ⟨A, hA, hcard, hfree⟩ := rothNumberNat_spec N
  by_contra hnot
  have hdensity : δ * (N : ℝ) ≤ (A.card : ℝ) := by
    rw [hcard]
    exact le_of_not_gt hnot
  have hlt := size_lt_explicitRothThreshold_of_mul_le_card δ N A hδ hδone hN
    hA hfree hdensity
  exact (not_lt_of_ge hthreshold) hlt

/-- The hypotheses of the finite theorem are jointly satisfiable at density
`1/2`, witnessed by the AP-free set `{0, 2}` in `range 4`. -/
example :
    let δ : ℝ := 1 / 2
    let N : ℕ := 4
    let A : Finset ℕ := {0, 2}
    0 < δ ∧ δ ≤ 1 ∧ 0 < N ∧ A ⊆ Finset.range N ∧
      ThreeAPFree (A : Set ℕ) ∧ δ ≤ (A.card : ℝ) / (N : ℝ) ∧
      (N : ℝ) < explicitRothThreshold δ := by
  dsimp only
  have hA : ({0, 2} : Finset ℕ) ⊆ Finset.range 4 := by decide
  have hfree : ThreeAPFree (({0, 2} : Finset ℕ) : Set ℕ) :=
    (threeAPCount_eq_zero_iff _).mp (by decide)
  have hbound := size_lt_explicitRothThreshold_of_threeAPFree
    (1 / 2) 4 {0, 2} (by norm_num) (by norm_num) (by norm_num) hA hfree (by norm_num)
  exact ⟨by norm_num, by norm_num, by norm_num, hA, hfree, by norm_num, hbound⟩

#check @explicitRothThreshold
#check @size_lt_explicitRothThreshold_of_threeAPFree
#check @size_lt_explicitRothThreshold_of_mul_le_card
#check @rothNumberNat_lt_mul_of_explicitRothThreshold_le

#print axioms size_lt_explicitRothThreshold_of_threeAPFree
#print axioms size_lt_explicitRothThreshold_of_mul_le_card
#print axioms rothNumberNat_lt_mul_of_explicitRothThreshold_le

end Erdos142
