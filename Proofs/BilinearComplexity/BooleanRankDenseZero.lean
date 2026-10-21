import BilinearComplexity.BooleanRankDenseProbability

set_option autoImplicit false
open scoped BigOperators Classical

namespace BilinearComplexity
open BooleanRankProbability

private theorem row_singleton_mass {n : ℕ} (p : ℝ) (a : Fin n) :
    (∑ x : Fin n → BoolSemiring,
      if ∀ c, x c = if c = a then 0 else 1 then ∏ c, entryWeight p (x c) else 0) =
      (1-p) * p^(n-1) := by
  classical
  trans ∏ c : Fin n, ∑ v : BoolSemiring,
    if v = (if c = a then 0 else 1) then entryWeight p v else 0
  · convert cylinder_factor (fun (_ : Fin n) v => entryWeight p v)
      (fun c v => v = if c = a then 0 else 1) using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    simp only [ite_true, entryWeight, show (0 : BoolSemiring) ≠ 1 by decide, if_false]
    have he : (∏ c ∈ Finset.univ.erase a,
        entryWeight p (if c = a then 0 else 1)) = p^(n-1) := by
      calc
        _ = ∏ _c ∈ (Finset.univ.erase a : Finset (Fin n)), p := by
          apply Finset.prod_congr rfl
          intro c hc
          simp [Finset.ne_of_mem_erase hc, entryWeight]
        _ = _ := by simp
    exact congrArg (fun t : ℝ => (1-p) * t) he

/-- The mass of a single row with exactly one zero is the sum of its disjoint
singleton-coordinate patterns. -/
theorem row_oneZero_mass {n : ℕ} (p : ℝ) :
    (∑ x : Fin n → BoolSemiring,
      if ∃ a, ∀ c, x c = if c = a then 0 else 1
      then ∏ c, entryWeight p (x c) else 0) = (n : ℝ)*(1-p)*p^(n-1) := by
  classical
  have he (x : Fin n → BoolSemiring) :
      (if ∃ a, ∀ c, x c = if c = a then 0 else 1
        then ∏ c, entryWeight p (x c) else 0) =
      ∑ a : Fin n, if ∀ c, x c = if c = a then 0 else 1
        then ∏ c, entryWeight p (x c) else 0 := by
    by_cases h : ∃ a, ∀ c, x c = if c = a then 0 else 1
    · obtain ⟨a, ha⟩ := h
      have hu : ∀ b, (∀ c, x c = if c = b then 0 else 1) → b = a := by
        intro b hb
        by_contra hba
        have h0 := hb b
        have h1 := ha b
        simp only [ite_true, if_neg hba] at h0 h1
        exact (by decide : (0 : BoolSemiring) ≠ 1) (h0.symm.trans h1)
      rw [Finset.sum_eq_single a]
      · rw [if_pos (show ∃ b, ∀ c, x c = if c = b then 0 else 1 from ⟨a, ha⟩), if_pos ha]
      · intro b _ hba
        have hb : ¬ (∀ c, x c = if c = b then 0 else 1) := fun hb => hba (hu b hb)
        simp [hb]
      · simp
    · have hn : ∀ a, ¬ (∀ c, x c = if c = a then 0 else 1) :=
        fun a ha => h ⟨a, ha⟩
      simp [hn]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [row_singleton_mass]
  simp [mul_assoc]

/-- The complementary single-row mass excludes exactly the singleton-zero patterns. -/
theorem row_not_oneZero_mass {n : ℕ} (p : ℝ) :
    (∑ x : Fin n → BoolSemiring,
      if ¬ (∃ a, ∀ c, x c = if c = a then 0 else 1)
      then ∏ c, entryWeight p (x c) else 0) = 1-(n : ℝ)*(1-p)*p^(n-1) := by
  classical
  have he (x : Fin n → BoolSemiring) :
      (if ¬ (∃ a, ∀ c, x c = if c = a then 0 else 1)
        then ∏ c, entryWeight p (x c) else 0) =
      (∏ c, entryWeight p (x c)) -
        (if ∃ a, ∀ c, x c = if c = a then 0 else 1
          then ∏ c, entryWeight p (x c) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.sum_sub_distrib, row_oneZero_mass, ← Fintype.prod_sum]
  simp [sum_entryWeight]

/-- Absence of one-zero rows has the exact iid row-product mass. This identity
needs no probabilistic independence premise and even holds at empty size. -/
theorem oneZeroCount_zero_mass (n : ℕ) (p : ℝ) :
    (∑ A : BoolMatrix n n, if oneZeroCount A = 0 then matrixWeight p A else 0) =
      (1-(n : ℝ)*(1-p)*p^(n-1))^n := by
  classical
  have he (A : BoolMatrix n n) : oneZeroCount A = 0 ↔
      ∀ i, ¬ (∃ a, ∀ c, A i c = if c = a then 0 else 1) := by
    rw [oneZeroCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact forall_congr' (fun i => not_congr (mem_oneZeroRows_iff_singletonZero A i))
  simp_rw [he]
  change (∑ A : BoolMatrix n n, if ∀ i, ¬ (∃ a, ∀ c, A i c = if c = a then 0 else 1)
    then ∏ i, ∏ c, entryWeight p (A i c) else 0) = _
  have hf := cylinder_factor
    (fun (_ : Fin n) (x : Fin n → BoolSemiring) => ∏ c, entryWeight p (x c))
    (fun (_ : Fin n) (x : Fin n → BoolSemiring) =>
      ¬ (∃ a, ∀ c, x c = if c = a then 0 else 1))
  calc
    _ = ∏ _i : Fin n, ∑ x : Fin n → BoolSemiring,
        if ¬ (∃ a, ∀ c, x c = if c = a then 0 else 1)
        then ∏ c, entryWeight p (x c) else 0 := by
      convert hf using 1
      apply Finset.sum_congr rfl
      intro A hA
      split_ifs <;> rfl
    _ = _ := by simp_rw [row_not_oneZero_mass]; simp

/-- The pointwise mismatch of the two zero events is supported off the dense
 good event; summing gives the actual finite symmetric-difference bound. -/
theorem denseDefect_zero_mass_sub_oneZeroCount_abs_le (n : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    |(∑ A : BoolMatrix n n, if denseDefect A = 0 then matrixWeight p A else 0) -
      (∑ A : BoolMatrix n n, if oneZeroCount A = 0 then matrixWeight p A else 0)| ≤
      ∑ A : BoolMatrix n n, if ¬ denseGoodEvent A then matrixWeight p A else 0 := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro A hA
  have hw := matrixWeight_nonneg p hp hp1 A
  by_cases hg : denseGoodEvent A
  · rw [denseDefect_eq_oneZeroCount A hg]
    simp [hg]
  · by_cases hd : denseDefect A = 0 <;> by_cases ho : oneZeroCount A = 0 <;>
      simp [hg, hd, ho, abs_of_nonneg hw, hw]

/-- The actual zero-defect probability differs from the exact no-singleton
row-product probability by at most the full four-term finite dense bound. -/
theorem denseDefect_zero_mass_abs_le (n : ℕ) (p : ℝ)
    (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1) :
    |(∑ A : BoolMatrix n n, if denseDefect A = 0 then matrixWeight p A else 0) -
      (1-(n : ℝ)*(1-p)*p^(n-1))^n| ≤
      (n : ℝ)*(p^n+(1-p)^n) +
      (n : ℝ)*((n : ℝ)-1)*((p+(1-p)^2)^n-p^n-(n : ℝ)*(1-p)^2*p^(n-1)) +
      (n : ℝ)^2*((n : ℝ)-1)*(1-p)*p^(n-1)*(1-(1-p)*p)^(n-1) +
      (Nat.choose n 2 : ℝ)*(n : ℝ)*((1-p)*p^(n-1))^2 := by
  rw [← oneZeroCount_zero_mass n p]
  exact (denseDefect_zero_mass_sub_oneZeroCount_abs_le n p hp hp1).trans
    (denseGoodEvent_complement_mass_le n p hn hp hp1)

example : (2 ≤ 3) ∧ 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 ∧
    Nonempty (Fin 3) ∧ Nonempty (BoolMatrix 3 3) ∧ denseGoodEvent (boolId 3) ∧
    oneZeroCount (boolId 3) = 0 := by
  refine ⟨by decide, by norm_num, by norm_num, ⟨0⟩, ⟨boolId 3⟩, ?_, by decide⟩
  unfold denseGoodEvent
  decide

end BilinearComplexity
