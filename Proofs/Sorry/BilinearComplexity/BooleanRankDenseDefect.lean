import BilinearComplexity.BooleanRankCounting

set_option autoImplicit false

namespace BilinearComplexity

/-- Coordinates at which a displayed row is zero. -/
def zeroCoordinates {n : ℕ} (A : BoolMatrix n n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun c => A i c = 0)

/-- Displayed rows with exactly one zero coordinate. -/
def oneZeroRows {n : ℕ} (A : BoolMatrix n n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (zeroCoordinates A i).card = 1)

/-- Displayed rows with at least two zero coordinates. -/
def multiZeroRows {n : ℕ} (A : BoolMatrix n n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 2 ≤ (zeroCoordinates A i).card)

example : zeroCoordinates (boolId 3) 0 = {1, 2} := by decide
example : oneZeroRows (boolId 3) = ∅ := by decide
example : multiZeroRows (boolId 3) = Finset.univ := by decide

/-- Each row in an OR witness is dominated by its target row. -/
theorem rowLE_of_rowsSum_eq {n : ℕ} {A : BoolMatrix n n}
    {W : Finset (Fin n)} {i j : Fin n} (hj : j ∈ W)
    (heq : rowsSum A W = A i) : RowLE (A j) (A i) := by
  rw [← heq]
  exact rowLE_rowsSum hj

private theorem zeroCoordinates_subset_of_rowLE {n : ℕ} {A : BoolMatrix n n}
    {i j : Fin n} (h : RowLE (A j) (A i)) :
    zeroCoordinates A i ⊆ zeroCoordinates A j := by
  intro c hc
  have hi : A i c = 0 := (Finset.mem_filter.mp hc).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ c, ?_⟩
  rcases BoolSemiring.eq_zero_or_eq_one (A j c) with hz | ho
  · exact hz
  · have hone := h c ho
    rw [hi] at hone
    simp at hone

private theorem row_partition {n : ℕ} (A : BoolMatrix n n)
    (hz : ∀ i, ∃ c, A i c = 0) (i : Fin n) :
    i ∈ oneZeroRows A ∨ i ∈ multiZeroRows A := by
  obtain ⟨c, hc⟩ := hz i
  have hp : 0 < (zeroCoordinates A i).card :=
    Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
  simp only [oneZeroRows, multiZeroRows, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- If every displayed row is spanned by a fixed set, that set spans the entire
set of subset ORs, not just the total OR. -/
theorem rowSpan_eq_univ_of_rows_mem {n : ℕ} (A : BoolMatrix n n)
    (T : Finset (Fin n)) (h : ∀ i, A i ∈ rowSpan A T) :
    rowSpan A T = rowSpan A Finset.univ := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr (Finset.subset_univ S), rfl⟩
  · intro v hv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    have hw : ∀ i, ∃ W, W ⊆ T ∧ rowsSum A W = A i := by
      intro i
      obtain ⟨W, hW, heq⟩ := Finset.mem_image.mp (h i)
      exact ⟨W, Finset.mem_powerset.mp hW, heq⟩
    choose W hWT hWeq using hw
    refine Finset.mem_image.mpr ⟨S.biUnion W, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro j hj
      obtain ⟨i, hi, hjW⟩ := Finset.mem_biUnion.mp hj
      exact hWT i hjW
    · funext c
      have hone : rowsSum A (S.biUnion W) c = 1 ↔ rowsSum A S c = 1 := by
        simp only [rowsSum, BoolSemiring.sum_eq_one_iff]
        constructor
        · rintro ⟨j, hj, hjc⟩
          obtain ⟨i, hi, hjW⟩ := Finset.mem_biUnion.mp hj
          refine ⟨i, hi, ?_⟩
          rw [← hWeq i]
          exact (BoolSemiring.sum_eq_one_iff _ _).mpr ⟨j, hjW, hjc⟩
        · rintro ⟨i, hi, hic⟩
          rw [← hWeq i] at hic
          obtain ⟨j, hjW, hjc⟩ := (BoolSemiring.sum_eq_one_iff _ _).mp hic
          exact ⟨j, Finset.mem_biUnion.mpr ⟨i, hi, hjW⟩, hjc⟩
      rcases BoolSemiring.eq_zero_or_eq_one (rowsSum A (S.biUnion W) c) with hz | ho <;>
        rcases BoolSemiring.eq_zero_or_eq_one (rowsSum A S c) with hz' | ho' <;>
        simp_all

/-- On the deterministic dense good event, the multi-zero rows form a spanning
set and the actual displayed-row OR rank is their cardinality. -/
theorem boolRowRank_eq_multiZeroRows_card {n : ℕ} (A : BoolMatrix n n)
    (_hn : 2 ≤ n)
    (hone : ∀ i, ∃ c, A i c = 1)
    (hzero : ∀ i, ∃ c, A i c = 0)
    (hanti : ∀ i ∈ multiZeroRows A, ∀ j, j ≠ i → ¬ RowLE (A j) (A i))
    (hgen : ∀ u ∈ oneZeroRows A, ∃ W : Finset (Fin n),
      u ∉ W ∧ rowsSum A W = A u)
    (hinj : Set.InjOn (zeroCoordinates A) ↑(oneZeroRows A)) :
    rowSpan A (multiZeroRows A) = rowSpan A Finset.univ ∧
      boolRowRank A = (multiZeroRows A).card := by
  classical
  have hspan : rowSpan A (multiZeroRows A) = rowSpan A Finset.univ := by
    apply rowSpan_eq_univ_of_rows_mem
    intro i
    rcases row_partition A hzero i with hi | hi
    · obtain ⟨W, hiW, hW⟩ := hgen i hi
      refine Finset.mem_image.mpr ⟨W, Finset.mem_powerset.mpr ?_, hW⟩
      intro j hj
      rcases row_partition A hzero j with hjU | hjT
      · have hdom := rowLE_of_rowsSum_eq hj hW
        have heq : zeroCoordinates A i = zeroCoordinates A j := by
          apply Finset.eq_of_subset_of_card_le (zeroCoordinates_subset_of_rowLE hdom)
          have hci := (Finset.mem_filter.mp hi).2
          have hcj := (Finset.mem_filter.mp hjU).2
          omega
        have hji : i = j := hinj hi hjU heq
        exact False.elim (hiW (hji.symm ▸ hj))
      · exact hjT
    · exact mem_rowSpan_self A hi
  refine ⟨hspan, le_antisymm ?_ ?_⟩
  · exact boolRowRank_le_of_boolRowRankLE ⟨multiZeroRows A, le_rfl, hspan⟩
  · obtain ⟨S, hcard, hS⟩ := boolRowRankLE_boolRowRank A
    suffices hsub : multiZeroRows A ⊆ S from (Finset.card_le_card hsub).trans hcard
    intro i hi
    have hmem : A i ∈ rowSpan A S := by
      rw [hS]
      exact mem_rowSpan_self A (Finset.mem_univ i)
    obtain ⟨W, hW, heq⟩ := Finset.mem_image.mp hmem
    obtain ⟨c, hc⟩ := hone i
    have hsum : rowsSum A W c = 1 := by rw [heq]; exact hc
    obtain ⟨j, hj, hjc⟩ := (BoolSemiring.sum_eq_one_iff _ _).mp hsum
    have hji : j = i := by
      by_contra hne
      exact hanti i hi j hne (rowLE_of_rowsSum_eq hj heq)
    exact hji ▸ (Finset.mem_powerset.mp hW hj)

example : (2 ≤ 3) ∧
    (∀ i : Fin 3, ∃ c, boolId 3 i c = 1) ∧
    (∀ i : Fin 3, ∃ c, boolId 3 i c = 0) ∧
    (∀ i ∈ multiZeroRows (boolId 3), ∀ j, j ≠ i →
      ¬ RowLE (boolId 3 j) (boolId 3 i)) ∧
    (∀ u ∈ oneZeroRows (boolId 3), ∃ W : Finset (Fin 3),
      u ∉ W ∧ rowsSum (boolId 3) W = boolId 3 u) ∧
    Set.InjOn (zeroCoordinates (boolId 3)) ↑(oneZeroRows (boolId 3)) := by
  decide

end BilinearComplexity
