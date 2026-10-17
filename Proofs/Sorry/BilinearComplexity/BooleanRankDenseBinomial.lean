import Sorry.BilinearComplexity.BooleanRankDenseZero
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
open scoped BigOperators Classical

namespace BilinearComplexity
open BooleanRankProbability

/-- The exact mass of any prescribed set of singleton-zero rows. -/
theorem oneZeroRows_mass (n : ℕ) (p : ℝ) (S : Finset (Fin n)) :
    (∑ A : BoolMatrix n n, if oneZeroRows A = S then matrixWeight p A else 0) =
      ((n : ℝ)*(1-p)*p^(n-1))^S.card *
        (1-(n : ℝ)*(1-p)*p^(n-1))^(n-S.card) := by
  classical
  have he (A : BoolMatrix n n) : oneZeroRows A = S ↔
      ∀ i, if i ∈ S then (∃ a, ∀ c, A i c = if c = a then 0 else 1)
        else ¬ (∃ a, ∀ c, A i c = if c = a then 0 else 1) := by
    rw [Finset.ext_iff]
    apply forall_congr'
    intro i
    rw [mem_oneZeroRows_iff_singletonZero]
    change ((∃ a, ∀ c, A i c = if c = a then 0 else 1) ↔ i ∈ S) ↔ _
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [he]
  change (∑ A : BoolMatrix n n, if ∀ i, _ then ∏ i, ∏ c, entryWeight p (A i c)
    else 0) = _
  have hf := cylinder_factor
    (fun (_ : Fin n) (x : Fin n → BoolSemiring) => ∏ c, entryWeight p (x c))
    (fun i (x : Fin n → BoolSemiring) => if i ∈ S then
      (∃ a, ∀ c, x c = if c = a then 0 else 1) else
      ¬ (∃ a, ∀ c, x c = if c = a then 0 else 1))
  calc
    _ = ∏ i : Fin n, ∑ x : Fin n → BoolSemiring,
        if (if i ∈ S then (∃ a, ∀ c, x c = if c = a then 0 else 1)
          else ¬ (∃ a, ∀ c, x c = if c = a then 0 else 1))
        then ∏ c, entryWeight p (x c) else 0 := by
      convert hf using 1
      apply Finset.sum_congr rfl
      intro A hA
      split_ifs <;> rfl
    _ = ∏ i : Fin n, if i ∈ S then (n : ℝ)*(1-p)*p^(n-1)
        else 1-(n : ℝ)*(1-p)*p^(n-1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hs : i ∈ S
      · simpa [hs] using (row_oneZero_mass (n := n) p)
      · simpa [hs] using (row_not_oneZero_mass (n := n) p)
    _ = _ := by
      rw [Finset.prod_ite]
      have hS : Finset.univ.filter (fun i : Fin n => i ∈ S) = S := by ext; simp
      have hC : Finset.univ.filter (fun i : Fin n => i ∉ S) = Sᶜ := by ext; simp
      simp [hS, hC, Finset.card_compl]

/-- The actual singleton-zero row count has the binomial atom mass, including endpoints. -/
theorem oneZeroCount_mass (n : ℕ) (p : ℝ) (k : ℕ) (_hk : k ≤ n) :
    (∑ A : BoolMatrix n n, if oneZeroCount A = k then matrixWeight p A else 0) =
      (Nat.choose n k : ℝ) * ((n : ℝ)*(1-p)*p^(n-1))^k *
        (1-(n : ℝ)*(1-p)*p^(n-1))^(n-k) := by
  classical
  have he (A : BoolMatrix n n) :
      (if oneZeroCount A = k then matrixWeight p A else 0) =
      ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
        if oneZeroRows A = S then matrixWeight p A else 0 := by
    by_cases h : oneZeroCount A = k
    · rw [Finset.sum_eq_single (oneZeroRows A)]
      · simp [h]
      · intro S hS hne
        simp [Ne.symm hne]
      · intro hn
        exact (hn (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩)).elim
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro S hS
      have hc := (Finset.mem_powersetCard.mp hS).2
      have hn : oneZeroRows A ≠ S := by
        intro hs
        apply h
        exact (congrArg Finset.card hs).trans hc
      simp [hn]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [oneZeroRows_mass]
  calc
    _ = ∑ _S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
        ((n : ℝ)*(1-p)*p^(n-1))^k * (1-(n : ℝ)*(1-p)*p^(n-1))^(n-k) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = _ := by simp [mul_assoc]

/-- Singleton-zero counts cannot exceed the number of rows. -/
theorem oneZeroCount_mass_eq_zero (n : ℕ) (p : ℝ) (k : ℕ) (hk : n < k) :
    (∑ A : BoolMatrix n n, if oneZeroCount A = k then matrixWeight p A else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro A hA
  have hc : oneZeroCount A ≤ n := by
    simpa [oneZeroCount] using (Finset.card_le_univ (oneZeroRows A))
  have hn : oneZeroCount A ≠ k := by omega
  simp [hn]

/-- Every event of the actual singleton-zero count has its exact finite binomial mass. -/
theorem oneZeroCount_event_mass (n : ℕ) (p : ℝ) (E : ℕ → Prop) :
    (∑ A : BoolMatrix n n, if E (oneZeroCount A) then matrixWeight p A else 0) =
      ∑ k ∈ Finset.range (n+1), if E k then
        (Nat.choose n k : ℝ) * ((n : ℝ)*(1-p)*p^(n-1))^k *
          (1-(n : ℝ)*(1-p)*p^(n-1))^(n-k) else 0 := by
  classical
  have he (A : BoolMatrix n n) :
      (if E (oneZeroCount A) then matrixWeight p A else 0) =
      ∑ k ∈ Finset.range (n+1), if E k then
        (if oneZeroCount A = k then matrixWeight p A else 0) else 0 := by
    rw [Finset.sum_eq_single (oneZeroCount A)]
    · simp
    · intro k hk hne
      simp [Ne.symm hne]
    · intro hn
      have hc : oneZeroCount A ≤ n := by
        simpa [oneZeroCount] using (Finset.card_le_univ (oneZeroRows A))
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hE : E k
  · simp only [if_pos hE]
    exact oneZeroCount_mass n p k (by have := Finset.mem_range.mp hk; omega)
  · simp [hE]

/-- On every event, the actual displayed-row OR-generation defect is within the
full four-term dense error of the binomial law. -/
theorem denseDefect_event_mass_abs_le (n : ℕ) (p : ℝ)
    (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1) (E : ℕ → Prop) :
    |(∑ A : BoolMatrix n n, if E (denseDefect A) then matrixWeight p A else 0) -
      (∑ k ∈ Finset.range (n+1), if E k then
        (Nat.choose n k : ℝ) * ((n : ℝ)*(1-p)*p^(n-1))^k *
          (1-(n : ℝ)*(1-p)*p^(n-1))^(n-k) else 0)| ≤
      (n : ℝ)*(p^n+(1-p)^n) +
      (n : ℝ)*((n : ℝ)-1)*((p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1)) +
      (n : ℝ)^2*((n : ℝ)-1)*(1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) +
      (Nat.choose n 2 : ℝ)*(n : ℝ)*((1-p)*p^(n-1))^2 := by
  classical
  rw [← oneZeroCount_event_mass n p E, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun A _ => ?_)).trans
    (denseGoodEvent_complement_mass_le n p hn hp hp1)
  have hw := matrixWeight_nonneg p hp hp1 A
  by_cases hg : denseGoodEvent A
  · rw [denseDefect_eq_oneZeroCount A hg]
    simp [hg]
  · by_cases hd : E (denseDefect A) <;> by_cases ho : E (oneZeroCount A) <;>
      simp [hg, hd, ho, abs_of_nonneg hw, hw]

example : (2 ≤ 4) ∧ 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 ∧
    Nonempty (Fin 4) ∧ Nonempty (BoolMatrix 4 4) := by
  exact ⟨by decide, by norm_num, by norm_num, ⟨0⟩, ⟨boolId 4⟩⟩

example :
    let A : BoolMatrix 4 4 := fun i c =>
      if i = 3 then (if c = 3 then 0 else 1) else (if i = c then 1 else 0)
    denseGoodEvent A ∧ oneZeroCount A = 1 ∧ denseDefect A = 1 ∧
      0 < matrixWeight (1/2) A := by
  intro A
  have hg : denseGoodEvent A := by unfold A denseGoodEvent; decide
  have hx : oneZeroCount A = 1 := by unfold A; decide
  refine ⟨hg, hx, (denseDefect_eq_oneZeroCount A hg).trans hx, ?_⟩
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro c hc
  unfold entryWeight
  split_ifs <;> norm_num

example :
    (∑ A : BoolMatrix 4 4, if oneZeroCount A = 1 then matrixWeight (1/2) A else 0) =
      (27/64 : ℝ) := by
  rw [oneZeroCount_mass 4 (1/2) 1 (by decide)]
  norm_num

end BilinearComplexity
