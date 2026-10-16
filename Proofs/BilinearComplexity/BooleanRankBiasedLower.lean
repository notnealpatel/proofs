import BilinearComplexity.BooleanRankProbability
import BilinearComplexity.BooleanRankCounting

set_option autoImplicit false

open scoped BigOperators

namespace BilinearComplexity.BooleanRankProbability

/-- A zero displayed row gives the lower bound `(1-p)^n` on the actual
Bernoulli-weighted mass of matrices with deficient displayed-row OR rank. -/
theorem zero_row_pow_le_deficit_sum (n : ℕ) (hn : 1 ≤ n)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (1 - p) ^ n ≤ ∑ A : BoolMatrix n n,
      if boolRowRank A < n then matrixWeight p A else 0 := by
  classical
  let r : Fin n := ⟨0, hn⟩
  have hmass : (∑ A : BoolMatrix n n,
      if ∀ j, A r j = 0 then matrixWeight p A else 0) = (1 - p) ^ n := by
    rw [matrix_column_cylinder p (fun _ x => x r = 0)]
    have hcol : (∑ x : Fin n → BoolSemiring,
        if x r = 0 then ∏ i, entryWeight p (x i) else 0) = 1 - p := by
      simpa [entryWeight] using fixed_entries_mass p {r} 0
    simp only [hcol, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hmass]
  apply Finset.sum_le_sum
  intro A hA
  by_cases hz : ∀ j, A r j = 0
  · have hrank : boolRowRank A < n := by
      apply (boolRowRank_lt_iff_redundant A).mpr
      refine ⟨r, ∅, by simp, ?_⟩
      funext j
      simp [rowsSum, hz j]
    simp [hz, hrank]
  · simp only [hz, if_false]
    split_ifs
    · exact matrixWeight_nonneg p hp hp1 A
    · exact le_rfl

/-- In a single column the pivot is one and some other entry is one with
weight `p*(1-(1-p)^(n-1))`, including the empty-other-rows case. -/
theorem full_row_or_column_mass {n : ℕ} (p : ℝ) (r : Fin n) :
    (∑ x : Fin n → BoolSemiring,
      if x r = 1 ∧ ∃ i, i ≠ r ∧ x i = 1
      then ∏ i, entryWeight p (x i) else 0) =
      p * (1 - (1 - p) ^ (n - 1)) := by
  classical
  have hpivot : (∑ x : Fin n → BoolSemiring,
      if x r = 1 then ∏ i, entryWeight p (x i) else 0) = p := by
    simpa [entryWeight] using fixed_entries_mass p {r} 1
  have hsingle : (∑ x : Fin n → BoolSemiring,
      if ∀ i, x i = (if i = r then 1 else 0)
      then ∏ i, entryWeight p (x i) else 0) = p * (1 - p) ^ (n - 1) := by
    trans ∏ i : Fin n, ∑ b : BoolSemiring,
      if b = (if i = r then 1 else 0) then entryWeight p b else 0
    · convert cylinder_factor (fun (_ : Fin n) b => entryWeight p b)
        (fun i b => b = (if i = r then 1 else 0)) using 1
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> rfl
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    simp only [ite_true, entryWeight]
    congr 1
    calc
      (∏ i ∈ Finset.univ.erase r, if (if i = r then 1 else 0) = (1 : BoolSemiring)
        then p else 1 - p) = ∏ _i ∈ Finset.univ.erase r, (1 - p) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [(Finset.mem_erase.mp hi).1]
      _ = (1 - p) ^ (n - 1) := by simp
  have hsplit (x : Fin n → BoolSemiring) :
      (if x r = 1 then ∏ i, entryWeight p (x i) else 0) =
        (if x r = 1 ∧ ∃ i, i ≠ r ∧ x i = 1
          then ∏ i, entryWeight p (x i) else 0) +
        (if ∀ i, x i = (if i = r then 1 else 0)
          then ∏ i, entryWeight p (x i) else 0) := by
    by_cases hr : x r = 1
    · by_cases ho : ∃ i, i ≠ r ∧ x i = 1
      · have hnot : ¬ ∀ i, x i = (if i = r then 1 else 0) := by
          intro h
          obtain ⟨i, hir, hi⟩ := ho
          have hi0 : x i = 0 := by simpa [hir] using h i
          rw [hi] at hi0
          exact (by decide : (1 : BoolSemiring) ≠ 0) hi0
        simp [hr, ho, hnot]
      · have hall : ∀ i, x i = (if i = r then 1 else 0) := by
          intro i
          by_cases hir : i = r
          · simpa [hir] using hr
          · have hi0 : x i = 0 := (BoolSemiring.eq_zero_or_eq_one (x i)).resolve_right
              (fun hi => ho ⟨i, hir, hi⟩)
            simp [hir, hi0]
        simp [hr, hall]
    · have hnot : ¬ ∀ i, x i = (if i = r then 1 else 0) := by
        intro h
        exact hr (by simpa using h r)
      simp [hr, hnot]
  have hsum := congrArg (fun f : (Fin n → BoolSemiring) → ℝ => ∑ x, f x)
    (funext hsplit)
  rw [Finset.sum_add_distrib, hpivot, hsingle] at hsum
  calc
    _ = p - p * (1 - p) ^ (n - 1) := (eq_sub_iff_add_eq).mpr hsum.symm
    _ = _ := by rw [mul_sub, mul_one]

/-- A full pivot row that is the OR of all the other rows gives the lower
bound `(p*(1-(1-p)^(n-1)))^n` on the actual weighted rank-deficit sum. -/
theorem full_row_or_pow_le_deficit_sum (n : ℕ) (hn : 1 ≤ n)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (p * (1 - (1 - p) ^ (n - 1))) ^ n ≤ ∑ A : BoolMatrix n n,
      if boolRowRank A < n then matrixWeight p A else 0 := by
  classical
  let r : Fin n := ⟨0, hn⟩
  have hmass : (∑ A : BoolMatrix n n,
      if ∀ j, A r j = 1 ∧ ∃ i, i ≠ r ∧ A i j = 1
      then matrixWeight p A else 0) = (p * (1 - (1 - p) ^ (n - 1))) ^ n := by
    rw [matrix_column_cylinder p
      (fun _ x => x r = 1 ∧ ∃ i, i ≠ r ∧ x i = 1)]
    simp only [full_row_or_column_mass, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [← hmass]
  apply Finset.sum_le_sum
  intro A hA
  by_cases hfull : ∀ j, A r j = 1 ∧ ∃ i, i ≠ r ∧ A i j = 1
  · have hrank : boolRowRank A < n := by
      apply (boolRowRank_lt_iff_redundant A).mpr
      refine ⟨r, Finset.univ.erase r, by simp, ?_⟩
      funext j
      rw [(hfull j).1]
      symm
      apply (BoolSemiring.sum_eq_one_iff _ _).mpr
      obtain ⟨i, hir, hij⟩ := (hfull j).2
      exact ⟨i, Finset.mem_erase.mpr ⟨hir, Finset.mem_univ i⟩, hij⟩
    simp [hfull, hrank]
  · simp only [hfull, if_false]
    split_ifs
    · exact matrixWeight_nonneg p hp hp1 A
    · exact le_rfl

example : 1 ≤ (1 : ℕ) ∧ 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    Nonempty (Fin 1) ∧ Nonempty (BoolMatrix 1 1) := by
  exact ⟨by decide, by norm_num, by norm_num, ⟨0⟩, ⟨0⟩⟩

example : ∀ j : Fin 2,
    (fun _ _ => (1 : BoolSemiring)) (0 : Fin 2) j = 1 ∧
      ∃ i : Fin 2, i ≠ 0 ∧ (fun _ _ => (1 : BoolSemiring)) i j = 1 := by
  intro j
  exact ⟨rfl, 1, by decide, rfl⟩

end BilinearComplexity.BooleanRankProbability
