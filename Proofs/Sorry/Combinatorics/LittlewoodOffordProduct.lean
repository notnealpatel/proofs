import Combinatorics.LittlewoodOffordBiased

/-!
Recovery of the sorry-free partial product argument only. The full-target row identity,
odds/product bridge, normalized shadow, compression LYM, interval upper bound, and
endpoints remain unproved here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace LittlewoodOfford.Product

noncomputable section

/-- The actual independent Bernoulli mass of a subset, including endpoint biases. -/
def mass {α : Type*} [Fintype α] (p : α → ℝ) (S : Finset α) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ (Finset.univ \ S), (1 - p i)

/-- The actual mass of cardinality rank `k`. -/
def rankMass {α : Type*} [Fintype α] (p : α → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset α).powersetCard k, mass p S

/-- The explicit maximum of all ranks from zero through the ambient dimension. -/
def peak {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ((Finset.range (Fintype.card α + 1)).image (rankMass p)).max'
    (by exact ⟨rankMass p 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩)

/-- The actual mass of a half-open subset-sum interval. -/
def intervalMass {α : Type*} [Fintype α]
    (p a : α → ℝ) (d t : ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset α)).filter
    (fun S => t ≤ ∑ i ∈ S, a i ∧ (∑ i ∈ S, a i) < t + d), mass p S

example (p : Fin 0 → ℝ) : mass p ∅ = 1 := by simp [mass]
example : mass (fun _ : Fin 1 => (1 / 3 : ℝ)) ∅ = 2 / 3 := by
  norm_num [mass]
example (p : Fin 0 → ℝ) : rankMass p 0 = 1 := by simp [rankMass, mass]
example (p : Fin 0 → ℝ) : peak p = 1 := by simp [peak, rankMass, mass]

/-- Every actual rank is bounded by the explicit finite peak. -/
theorem rankMass_le_peak {α : Type*} [Fintype α] (p : α → ℝ)
    (k : ℕ) (hk : k ≤ Fintype.card α) : rankMass p k ≤ peak p := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩

/-- A maximizing rank always exists, including dimension zero. -/
theorem peak_attained {α : Type*} [Fintype α] (p : α → ℝ) :
    ∃ k, k ≤ Fintype.card α ∧ rankMass p k = peak p := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
    (Finset.max'_mem ((Finset.range (Fintype.card α + 1)).image (rankMass p)) _)
  exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), heq⟩

/-- Unit coefficients identify the half-open integer interval with exactly one rank. -/
theorem intervalMass_unit {α : Type*} [Fintype α] (p : α → ℝ) (k : ℕ) :
    intervalMass p (fun _ => 1) 1 (k : ℝ) = rankMass p k := by
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
  exact congrArg (fun F : Finset (Finset α) => ∑ S ∈ F, mass p S) hfilter

/-- Some unit-coefficient interval attains the finite peak for every bias vector. -/
theorem exists_intervalMass_eq_peak {α : Type*} [Fintype α] (p : α → ℝ) :
    ∃ k, k ≤ Fintype.card α ∧ intervalMass p (fun _ => 1) 1 (k : ℝ) = peak p := by
  obtain ⟨k, hk, heq⟩ := peak_attained p
  exact ⟨k, hk, (intervalMass_unit p k).trans heq⟩

example (p : Fin 0 → ℝ) : intervalMass p (fun _ => 1) 1 0 = 1 := by
  simpa [rankMass, mass] using intervalMass_unit p 0

/-- The multiplicative weight corresponding to positive odds. -/
def weight {α : Type*} (w : α → ℝ) (S : Finset α) : ℝ := ∏ i ∈ S, w i

/-- The elementary symmetric sum of multiplicative weights at rank `k`. -/
def elementary {α : Type*} [Fintype α] (w : α → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset α).powersetCard k, weight w S

/-- The kernel numerator indexed by the target set `u` and its deleted element `j`.
On adjacent ranks its denominator is positive; the column identity below supplies
that guard explicitly. -/
def columnKernel {α : Type*} [Fintype α] (w : α → ℝ)
    (k : ℕ) (u : Finset α) (j : α) : ℝ :=
  ∑ t ∈ (Finset.univ : Finset α).powersetCard k,
    if j ∈ t then 0 else weight w t / ((u \ t).card : ℝ)

example : weight (fun _ : Fin 1 => (2 : ℝ)) Finset.univ = 2 := by
  simp [weight]
example (w : Fin 0 → ℝ) : elementary w 0 = 1 := by simp [elementary, weight]
example : columnKernel (fun _ : Fin 1 => (2 : ℝ)) 0 Finset.univ 0 = 1 := by
  simp [columnKernel, weight]

/-- A set of size `k+1` has a nonempty difference from every rank-`k` set. -/
theorem sdiff_card_pos {α : Type*} [DecidableEq α] (u t : Finset α) (k : ℕ)
    (hu : u.card = k + 1) (ht : t.card = k) : 0 < (u \ t).card := by
  apply Finset.card_pos.mpr
  by_contra hn
  have hsub : u ⊆ t := by
    intro i hi
    by_contra hit
    exact hn ⟨i, Finset.mem_sdiff.mpr ⟨hi, hit⟩⟩
  have hc := Finset.card_le_card hsub
  omega

/-- The actual finite column identity: summing over deleted elements gives the
rank-`k` elementary symmetric sum, with no normalized-matching assumption. -/
theorem columnKernel_sum {α : Type*} [Fintype α] (w : α → ℝ)
    (k : ℕ) (u : Finset α) (hu : u.card = k + 1) :
    (∑ j ∈ u, columnKernel w k u j) = elementary w k := by
  unfold columnKernel elementary
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have htcard := (Finset.mem_powersetCard.mp ht).2
  have hpos : (0 : ℝ) < ((u \ t).card : ℝ) :=
    Nat.cast_pos.mpr (sdiff_card_pos u t k hu htcard)
  have hsum : (∑ j ∈ u, if j ∈ t then (0 : ℝ)
      else weight w t / ((u \ t).card : ℝ)) =
      ∑ _j ∈ u \ t, weight w t / ((u \ t).card : ℝ) := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp_all
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ (weight w t) (ne_of_gt hpos)

end
end LittlewoodOfford.Product
