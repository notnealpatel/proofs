import BilinearComplexity.BooleanRankGeneric

set_option autoImplicit false

namespace BilinearComplexity

/-- Full displayed-row-rank matrices are a subset of all Boolean matrices. -/
theorem fullRowRankCount_le_total (n : ℕ) : fullRowRankCount n ≤ 2 ^ (n * n) := by
  unfold fullRowRankCount
  exact (Finset.card_filter_le _ _).trans_eq (by
    rw [Finset.card_univ, card_boolMatrix])

private theorem bool_eq_of_one_iff (a b : BoolSemiring) (h : a = 1 ↔ b = 1) : a = b := by
  rcases BoolSemiring.eq_zero_or_eq_one a with ha | ha <;>
    rcases BoolSemiring.eq_zero_or_eq_one b with hb | hb <;> simp_all

/-- Substituting an omitted row's OR expression preserves every row sum. -/
theorem rowsSum_substitute {m n : ℕ} (A : BoolMatrix m n) (i : Fin m)
    (T S : Finset (Fin m)) (_hi : i ∉ T) (hrow : A i = rowsSum A T) :
    rowsSum A S = rowsSum A (if i ∈ S then S.erase i ∪ T else S) := by
  classical
  by_cases his : i ∈ S
  · simp only [his, if_true]
    funext c
    apply bool_eq_of_one_iff
    simp only [rowsSum, BoolSemiring.sum_eq_one_iff]
    constructor
    · rintro ⟨j, hj, hjc⟩
      by_cases hji : j = i
      · subst j
        have ht : rowsSum A T c = 1 := by rw [← hrow]; exact hjc
        obtain ⟨k, hk, hkc⟩ := (BoolSemiring.sum_eq_one_iff T _).mp ht
        exact ⟨k, Finset.mem_union_right _ hk, hkc⟩
      · exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hji, hj⟩), hjc⟩
    · rintro ⟨j, hj, hjc⟩
      rcases Finset.mem_union.mp hj with hjs | hjt
      · exact ⟨j, (Finset.mem_erase.mp hjs).2, hjc⟩
      · have hc : A i c = 1 := by
          rw [hrow]
          exact (BoolSemiring.sum_eq_one_iff T _).mpr ⟨j, hjt, hjc⟩
        exact ⟨i, his, hc⟩
  · simp [his]

/-- A redundant displayed row may be deleted without changing the OR span. -/
theorem rowSpan_erase_eq_of_rowsSum {m n : ℕ} (A : BoolMatrix m n) (i : Fin m)
    (T : Finset (Fin m)) (hi : i ∉ T) (hrow : A i = rowsSum A T) :
    rowSpan A (Finset.univ.erase i) = rowSpan A Finset.univ := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr (Finset.subset_univ S), rfl⟩
  · intro v hv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    let U := if i ∈ S then S.erase i ∪ T else S
    refine Finset.mem_image.mpr ⟨U, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro j hj
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ j⟩
      intro hji
      subst j
      by_cases his : i ∈ S
      · simp [U, his, hi] at hj
      · simp [U, his] at hj
    · exact (rowsSum_substitute A i T S hi hrow).symm

/-- Rank drops exactly when a displayed row is the OR of other displayed rows;
the witness may be empty, accounting for zero rows. -/
theorem boolRowRank_lt_iff_redundant {m n : ℕ} (A : BoolMatrix m n) :
    boolRowRank A < m ↔ ∃ i : Fin m, ∃ T : Finset (Fin m), i ∉ T ∧ A i = rowsSum A T := by
  classical
  constructor
  · intro hr
    obtain ⟨S, hcard, hspan⟩ := boolRowRankLE_boolRowRank A
    have hmissing : ∃ i : Fin m, i ∉ S := by
      by_contra h
      push Not at h
      have hS : S = Finset.univ := Finset.eq_univ_of_forall h
      rw [hS, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    obtain ⟨i, hi⟩ := hmissing
    have hmem : A i ∈ rowSpan A S := by
      rw [hspan]
      exact mem_rowSpan_self A (Finset.mem_univ i)
    obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp hmem
    exact ⟨i, T, fun hit => hi ((Finset.mem_powerset.mp hT) hit), heq.symm⟩
  · rintro ⟨i, T, hi, hrow⟩
    have hle : boolRowRank A ≤ (Finset.univ.erase i).card :=
      boolRowRank_le_of_boolRowRankLE
        ⟨Finset.univ.erase i, le_rfl, rowSpan_erase_eq_of_rowsSum A i T hi hrow⟩
    have hcard : (Finset.univ.erase i).card = m - 1 := by simp
    have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
    omega

example : ∃ i : Fin 2, ∃ T : Finset (Fin 2),
    i ∉ T ∧ (0 : BoolMatrix 2 2) i = rowsSum 0 T := by
  exact ⟨0, ∅, by simp, by funext c; simp [rowsSum]⟩

example : 1 ≤ (1 : ℕ) ∧ 1 ≤ 2 - 1 := by decide

/-- A fixed omitted-row equality event has at most one matrix per choice
of all remaining rows, including when the OR witness is empty. -/
theorem card_filter_row_eq_rowsSum_le {m n : ℕ} (i : Fin m)
    (T : Finset (Fin m)) (hi : i ∉ T) :
    (Finset.univ.filter fun A : BoolMatrix m n => A i = rowsSum A T).card
      ≤ 2 ^ (n * (m - 1)) := by
  classical
  have hinj : (Finset.univ.filter fun A : BoolMatrix m n => A i = rowsSum A T).card
      ≤ (Finset.univ : Finset ({j : Fin m // j ≠ i} → Fin n → BoolSemiring)).card := by
    apply Finset.card_le_card_of_injOn (fun A (j : {j : Fin m // j ≠ i}) => A j.1)
    · intro A hA
      exact Finset.mem_univ _
    · intro A hA B hB hAB
      have ha := (Finset.mem_filter.mp hA).2
      have hb := (Finset.mem_filter.mp hB).2
      have hother : ∀ j : Fin m, j ≠ i → A j = B j := by
        intro j hj
        exact congrFun hAB ⟨j, hj⟩
      funext j c
      by_cases hji : j = i
      · subst j
        rw [ha, hb]
        apply Finset.sum_congr rfl
        intro k hk
        exact congrFun (hother k (fun hki => hi (hki ▸ hk))) c
      · exact congrFun (hother j hji) c
  have hsub : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter fun j : Fin m => j ≠ i) = Finset.univ.erase i := by
      ext j
      simp [ne_comm]
    rw [hset]
    simp
  have hBS : Fintype.card BoolSemiring = 2 := rfl
  refine hinj.trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
    hBS, Fintype.card_fin, hsub, ← pow_mul]

/-- For a fixed target and set of dominated rows, each column has at most
`2 ^ U.card + 1` patterns; rows outside the constraint are free. -/
theorem card_filter_rowsLE_le {m n : ℕ} (i : Fin m)
    (U : Finset (Fin m)) (hi : i ∉ U) :
    (Finset.univ.filter fun A : BoolMatrix m n =>
      ∀ j ∈ U, RowLE (A j) (A i)).card ≤
      (2 ^ U.card + 1) ^ n * 2 ^ (n * (m - U.card - 1)) := by
  classical
  let encode := fun (A : BoolMatrix m n) =>
    ((fun c => if A i c = 1 then some (fun j : {j // j ∈ U} => A j.1 c) else none),
      fun j : {j : Fin m // j ≠ i ∧ j ∉ U} => A j.1)
  have hinj : (Finset.univ.filter fun A : BoolMatrix m n =>
      ∀ j ∈ U, RowLE (A j) (A i)).card ≤
      (Finset.univ : Finset ((Fin n → Option ({j : Fin m // j ∈ U} → BoolSemiring)) ×
        ({j : Fin m // j ≠ i ∧ j ∉ U} → Fin n → BoolSemiring))).card := by
    apply Finset.card_le_card_of_injOn encode
    · intro A hA
      exact Finset.mem_univ _
    · intro A hA B hB hAB
      have ha := (Finset.mem_filter.mp hA).2
      have hb := (Finset.mem_filter.mp hB).2
      have hc := congrArg Prod.fst hAB
      have hf := congrArg Prod.snd hAB
      have htarget : ∀ c, A i c = 1 ↔ B i c = 1 := by
        intro c
        have hcol := congrFun hc c
        dsimp [encode] at hcol
        by_cases h1 : A i c = 1 <;> by_cases h2 : B i c = 1 <;> simp_all
      funext j c
      by_cases hji : j = i
      · subst j
        exact bool_eq_of_one_iff _ _ (htarget c)
      · by_cases hju : j ∈ U
        · apply bool_eq_of_one_iff
          constructor
          · intro h1
            have hai := ha j hju c h1
            have hbi := (htarget c).mp hai
            have hcol := congrFun hc c
            dsimp [encode] at hcol
            simp only [hai, hbi, if_true, Option.some.injEq] at hcol
            exact (congrFun hcol ⟨j, hju⟩).symm.trans h1
          · intro h1
            have hbi := hb j hju c h1
            have hai := (htarget c).mpr hbi
            have hcol := congrFun hc c
            dsimp [encode] at hcol
            simp only [hai, hbi, if_true, Option.some.injEq] at hcol
            exact (congrFun hcol ⟨j, hju⟩).trans h1
        · exact congrFun (congrFun hf ⟨j, hji, hju⟩) c
  have hU : Fintype.card {j : Fin m // j ∈ U} = U.card := by simp
  have hfree : Fintype.card {j : Fin m // j ≠ i ∧ j ∉ U} = m - U.card - 1 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter fun j : Fin m => j ≠ i ∧ j ∉ U) =
        (insert i U)ᶜ := by
      ext j
      simp
    rw [heq, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem hi]
    omega
  have hBS : Fintype.card BoolSemiring = 2 := rfl
  refine hinj.trans_eq ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fun, hBS, hU, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fun, hBS, Fintype.card_fin, hfree, ← pow_mul]

/-- A deficient matrix has either a small exact OR witness or a prescribed
number of other displayed rows dominated by a target row. -/
theorem boolRowRank_lt_witness_dichotomy {m n : ℕ} (A : BoolMatrix m n)
    (K : ℕ) (hr : boolRowRank A < m) :
    ∃ i : Fin m,
      (∃ T : Finset (Fin m), i ∉ T ∧ T.card < K ∧ A i = rowsSum A T) ∨
      (∃ U : Finset (Fin m), i ∉ U ∧ U.card = K ∧ ∀ j ∈ U, RowLE (A j) (A i)) := by
  obtain ⟨i, T, hi, heq⟩ := (boolRowRank_lt_iff_redundant A).mp hr
  refine ⟨i, ?_⟩
  by_cases hsmall : T.card < K
  · exact Or.inl ⟨T, hi, hsmall, heq⟩
  · obtain ⟨U, hUT, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hsmall)
    refine Or.inr ⟨U, fun hiU => hi (hUT hiU), hcard, ?_⟩
    intro j hj
    rw [heq]
    exact rowLE_rowsSum (hUT hj)

example : ∀ j ∈ (∅ : Finset (Fin 2)),
    RowLE ((0 : BoolMatrix 2 2) j) ((0 : BoolMatrix 2 2) 0) := by simp

/-- The deficit in full-rank matrices counts exactly the rank-deficient ones. -/
theorem total_sub_fullRowRankCount_eq (n : ℕ) :
    2 ^ (n * n) - fullRowRankCount n =
      (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A < n).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BoolMatrix n n))) (fun A => boolRowRank A = n)
  have heq : (Finset.univ.filter fun A : BoolMatrix n n => ¬ boolRowRank A = n) =
      (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A < n) := by
    apply Finset.filter_congr
    intro A hA
    have hle := boolRowRank_le_rows A
    omega
  rw [heq, Finset.card_univ, card_boolMatrix] at h
  unfold fullRowRankCount
  omega

/-- The two-scale finite union bound for the actual displayed-row OR rank. -/
theorem total_sub_fullRowRankCount_le (n K : ℕ) (_hK : 1 ≤ K) (_hKn : K ≤ n - 1) :
    2 ^ (n * n) - fullRowRankCount n ≤
      n * 2 ^ (n * (n - 1)) * (∑ k ∈ Finset.range K, Nat.choose (n - 1) k) +
      n * Nat.choose (n - 1) K * (2 ^ K + 1) ^ n * 2 ^ (n * (n - K - 1)) := by
  classical
  let E := fun (i : Fin n) (T : Finset (Fin n)) =>
    Finset.univ.filter fun A : BoolMatrix n n => A i = rowsSum A T
  let D := fun (i : Fin n) (U : Finset (Fin n)) =>
    Finset.univ.filter fun A : BoolMatrix n n => ∀ j ∈ U, RowLE (A j) (A i)
  let small := fun i : Fin n => (Finset.range K).biUnion fun k =>
    ((Finset.univ.erase i).powersetCard k).biUnion (E i)
  let large := fun i : Fin n =>
    ((Finset.univ.erase i).powersetCard K).biUnion (D i)
  have hsmall : ∀ i : Fin n, (small i).card ≤
      2 ^ (n * (n - 1)) * (∑ k ∈ Finset.range K, Nat.choose (n - 1) k) := by
    intro i
    refine Finset.card_biUnion_le.trans ?_
    calc
      ∑ k ∈ Finset.range K, (((Finset.univ.erase i).powersetCard k).biUnion (E i)).card
          ≤ ∑ k ∈ Finset.range K, Nat.choose (n - 1) k * 2 ^ (n * (n - 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hbound := Finset.card_biUnion_le_card_mul
          ((Finset.univ.erase i).powersetCard k) (E i) (2 ^ (n * (n - 1))) (by
            intro T hT
            have hsub := (Finset.mem_powersetCard.mp hT).1
            exact card_filter_row_eq_rowsSum_le i T (fun hi =>
              (Finset.mem_erase.mp (hsub hi)).1 rfl))
        simpa using hbound
      _ = _ := by rw [← Finset.sum_mul, Nat.mul_comm]
  have hlarge : ∀ i : Fin n, (large i).card ≤
      Nat.choose (n - 1) K * ((2 ^ K + 1) ^ n * 2 ^ (n * (n - K - 1))) := by
    intro i
    have hbound := Finset.card_biUnion_le_card_mul
      ((Finset.univ.erase i).powersetCard K) (D i)
      ((2 ^ K + 1) ^ n * 2 ^ (n * (n - K - 1))) (by
        intro U hU
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
        have hi : i ∉ U := fun hi => (Finset.mem_erase.mp (hsub hi)).1 rfl
        simpa [hcard] using card_filter_rowsLE_le (n := n) i U hi)
    simpa using hbound
  have hcover : (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A < n) ⊆
      Finset.univ.biUnion (fun i : Fin n => small i ∪ large i) := by
    intro A hA
    obtain ⟨i, hcase⟩ := boolRowRank_lt_witness_dichotomy A K (Finset.mem_filter.mp hA).2
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rcases hcase with ⟨T, hi, hcard, heq⟩ | ⟨U, hi, hcard, hdom⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨T.card, Finset.mem_range.mpr hcard, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨T, Finset.mem_powersetCard.mpr ⟨?_, rfl⟩, ?_⟩
      · intro j hj
        exact Finset.mem_erase.mpr ⟨fun hji => hi (hji ▸ hj), Finset.mem_univ j⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ A, heq⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨U, Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩
      · intro j hj
        exact Finset.mem_erase.mpr ⟨fun hji => hi (hji ▸ hj), Finset.mem_univ j⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ A, hdom⟩
  rw [total_sub_fullRowRankCount_eq]
  refine (Finset.card_le_card hcover).trans ?_
  have hbound := Finset.card_biUnion_le_card_mul Finset.univ
    (fun i : Fin n => small i ∪ large i)
    (2 ^ (n * (n - 1)) * (∑ k ∈ Finset.range K, Nat.choose (n - 1) k) +
      Nat.choose (n - 1) K * ((2 ^ K + 1) ^ n * 2 ^ (n * (n - K - 1)))) (by
        intro i hi
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hsmall i) (hlarge i)))
  simpa [Nat.mul_add, Nat.mul_assoc] using hbound

example : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) ∧
    ({1, 2} : Finset (Fin 3)).card = 2 ∧
    (∀ j ∈ ({1, 2} : Finset (Fin 3)),
      RowLE ((0 : BoolMatrix 3 3) j) ((0 : BoolMatrix 3 3) 0)) ∧
    1 ≤ (2 : ℕ) ∧ 2 ≤ 3 - 1 := by decide

end BilinearComplexity
