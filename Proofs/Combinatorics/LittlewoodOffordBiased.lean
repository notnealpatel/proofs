import Combinatorics.LittlewoodOfford

set_option autoImplicit false

open scoped BigOperators Classical

namespace LittlewoodOfford

noncomputable section

/-- The probability of the cardinality layer `k` for `n` iid Bernoulli trials. -/
def bernoulliLayer (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- The largest binomial layer probability, including both endpoint layers. -/
def bernoulliPeak (n : ℕ) (p : ℝ) : ℝ :=
  ((Finset.range (n + 1)).image (bernoulliLayer n p)).max'
    (by exact ⟨bernoulliLayer n p 0, Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), rfl⟩⟩)

/-- The explicit iid Bernoulli mass of a half-open subset-sum interval. -/
def bernoulliIntervalMass {α : Type*} [Fintype α]
    (a : α → ℝ) (d t p : ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset α)).filter
    (fun S => t ≤ ∑ i ∈ S, a i ∧ (∑ i ∈ S, a i) < t + d),
      p ^ S.card * (1 - p) ^ (Fintype.card α - S.card)

example (p : ℝ) : bernoulliLayer 0 p 0 = 1 := by simp [bernoulliLayer]
example (p : ℝ) : bernoulliPeak 0 p = 1 := by simp [bernoulliPeak, bernoulliLayer]

/-- Every binomial layer is bounded by the finite peak. -/
theorem bernoulliLayer_le_peak (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    bernoulliLayer n p k ≤ bernoulliPeak n p := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩

/-- The finite peak is attained at a cardinality between zero and `n`. -/
theorem bernoulliPeak_attained (n : ℕ) (p : ℝ) :
    ∃ k, k ≤ n ∧ bernoulliLayer n p k = bernoulliPeak n p := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
    (Finset.max'_mem ((Finset.range (n + 1)).image (bernoulliLayer n p)) _)
  exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), heq⟩

/-- The binomial peak is nonnegative for a Bernoulli parameter. -/
theorem bernoulliPeak_nonneg (n : ℕ) (p : ℝ) (_hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliPeak n p := by
  have hzero : 0 ≤ bernoulliLayer n p 0 := by
    unfold bernoulliLayer
    positivity
  exact hzero.trans (bernoulliLayer_le_peak n 0 p (Nat.zero_le n))

private theorem positive_interval_antichain {α : Type*} [Fintype α]
    (a : α → ℝ) (d t : ℝ) (hd : 0 < d) (ha : ∀ i, d ≤ a i) :
    IsAntichain (· ⊆ ·)
      (((Finset.univ : Finset (Finset α)).filter
        (fun S => t ≤ ∑ i ∈ S, a i ∧ (∑ i ∈ S, a i) < t + d)) : Set (Finset α)) := by
  intro S hS T hT hne hST
  have hTS : ¬ T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
  have hi : i ∈ T \ S := Finset.mem_sdiff.mpr ⟨hiT, hiS⟩
  have hsingle : ({i} : Finset α) ⊆ T \ S := Finset.singleton_subset_iff.mpr hi
  have hsum : a i ≤ ∑ j ∈ T \ S, a j := by
    simpa using Finset.sum_le_sum_of_subset_of_nonneg hsingle
      (fun j _ _ => le_trans (le_of_lt hd) (ha j))
  have hsplit := Finset.sum_sdiff (f := a) hST
  have hgap : d + (∑ j ∈ S, a j) ≤ ∑ j ∈ T, a j := by
    linarith [ha i]
  have hSmem := (Finset.mem_filter.mp hS).2
  have hTmem := (Finset.mem_filter.mp hT).2
  linarith [hSmem.1, hTmem.2]

/-- Sharp Littlewood–Offord concentration for positive coefficients and iid
Bernoulli selectors. The empty index type and parameters zero and one are allowed.
This is the weighted LYM bound, not an assertion for arbitrary signed coefficients. -/
theorem bernoulliIntervalMass_le_peak {α : Type*} [Fintype α]
    (a : α → ℝ) (d t p : ℝ) (hd : 0 < d) (ha : ∀ i, d ≤ a i)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliIntervalMass a d t p ≤ bernoulliPeak (Fintype.card α) p := by
  let A := (Finset.univ : Finset (Finset α)).filter
    (fun S => t ≤ ∑ i ∈ S, a i ∧ (∑ i ∈ S, a i) < t + d)
  let M := bernoulliPeak (Fintype.card α) p
  have hM : 0 ≤ M := bernoulliPeak_nonneg _ p hp hp1
  have hLYM : (∑ S ∈ A, ((Fintype.card α).choose S.card : ℝ)⁻¹) ≤ 1 :=
    Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
      (positive_interval_antichain a d t hd ha)
  have hweight (S : Finset α) :
      p ^ S.card * (1 - p) ^ (Fintype.card α - S.card) ≤
        M * ((Fintype.card α).choose S.card : ℝ)⁻¹ := by
    have hc : (0 : ℝ) < ((Fintype.card α).choose S.card : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos S.card_le_univ)
    have hl := bernoulliLayer_le_peak (Fintype.card α) S.card p S.card_le_univ
    apply (le_div_iff₀ hc).mpr
    simpa only [bernoulliLayer, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hl
  calc
    bernoulliIntervalMass a d t p ≤
        ∑ S ∈ A, M * ((Fintype.card α).choose S.card : ℝ)⁻¹ :=
      Finset.sum_le_sum (fun S _ => hweight S)
    _ = M * ∑ S ∈ A, ((Fintype.card α).choose S.card : ℝ)⁻¹ :=
      (Finset.mul_sum A _ M).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hLYM hM
    _ = bernoulliPeak (Fintype.card α) p := mul_one M

/-- With unit coefficients the interval at the integer `k` is exactly layer `k`. -/
theorem bernoulliIntervalMass_unit {α : Type*} [Fintype α]
    (p : ℝ) (k : ℕ) (_hk : k ≤ Fintype.card α) :
    bernoulliIntervalMass (fun _ : α => (1 : ℝ)) 1 (k : ℝ) p =
      bernoulliLayer (Fintype.card α) p k := by
  have hfilter : ((Finset.univ : Finset (Finset α)).filter
      (fun S => (k : ℝ) ≤ ∑ _i ∈ S, (1 : ℝ) ∧
        (∑ _i ∈ S, (1 : ℝ)) < (k : ℝ) + 1)) =
        (Finset.univ : Finset α).powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro h
      have hlo : k ≤ S.card := by exact_mod_cast h.1
      have hhi : S.card < k + 1 := by exact_mod_cast h.2
      exact Nat.le_antisymm (Nat.le_of_lt_succ hhi) hlo
    · intro h
      rw [h]
      constructor
      · exact le_rfl
      · linarith
  unfold bernoulliIntervalMass
  rw [hfilter]
  have heq : (∑ S ∈ (Finset.univ : Finset α).powersetCard k,
      p ^ S.card * (1 - p) ^ (Fintype.card α - S.card)) =
      ∑ _S ∈ (Finset.univ : Finset α).powersetCard k,
        p ^ k * (1 - p) ^ (Fintype.card α - k) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [heq]
  simp [bernoulliLayer, Finset.card_powersetCard, mul_assoc]

/-- Some unit-coefficient interval attains the peak, so the universal bound is sharp. -/
theorem exists_bernoulliIntervalMass_eq_peak {α : Type*} [Fintype α] (p : ℝ) :
    ∃ k : ℕ, k ≤ Fintype.card α ∧
      bernoulliIntervalMass (fun _ : α => (1 : ℝ)) 1 (k : ℝ) p =
        bernoulliPeak (Fintype.card α) p := by
  obtain ⟨k, hk, heq⟩ := bernoulliPeak_attained (Fintype.card α) p
  exact ⟨k, hk, (bernoulliIntervalMass_unit p k hk).trans heq⟩

example : (0 : ℝ) < 1 ∧ (∀ _i : Fin 2, (1 : ℝ) ≤ 1) ∧
    (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 := by
  norm_num

example (p : ℝ) : bernoulliIntervalMass (fun _ : Fin 0 => (1 : ℝ)) 1 0 p = 1 := by
  simpa [bernoulliLayer] using
    (bernoulliIntervalMass_unit (α := Fin 0) p 0 (by simp))

example : bernoulliIntervalMass (fun _ : Fin 2 => (1 : ℝ)) 1 0 0 = 1 := by
  simpa [bernoulliLayer] using
    (bernoulliIntervalMass_unit (α := Fin 2) 0 0 (by norm_num))

example : bernoulliIntervalMass (fun _ : Fin 2 => (1 : ℝ)) 1 2 1 = 1 := by
  simpa [bernoulliLayer] using
    (bernoulliIntervalMass_unit (α := Fin 2) 1 2 (by norm_num))

end

end LittlewoodOfford
