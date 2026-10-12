import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos132.KnownSixPointCombinatorics

private theorem cycle_bits (c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 : Bool)
    (h : ¬ (c01 = c02 ∧ c02 = c12) ∧
    ¬ (c01 = c03 ∧ c03 = c13) ∧
    ¬ (c01 = c04 ∧ c04 = c14) ∧
    ¬ (c02 = c03 ∧ c03 = c23) ∧
    ¬ (c02 = c04 ∧ c04 = c24) ∧
    ¬ (c03 = c04 ∧ c04 = c34) ∧
    ¬ (c12 = c13 ∧ c13 = c23) ∧
    ¬ (c12 = c14 ∧ c14 = c24) ∧
    ¬ (c13 = c14 ∧ c14 = c34) ∧
    ¬ (c23 = c24 ∧ c24 = c34)) :
    (c01 = true ∧ c02 = false ∧ c03 = false ∧ c04 = true ∧ c12 = true ∧ c13 = false ∧ c14 = false ∧ c23 = true ∧ c24 = false ∧ c34 = true) ∨
    (c01 = true ∧ c02 = false ∧ c03 = true ∧ c04 = false ∧ c12 = true ∧ c13 = false ∧ c14 = false ∧ c23 = false ∧ c24 = true ∧ c34 = true) ∨
    (c01 = true ∧ c02 = false ∧ c03 = false ∧ c04 = true ∧ c12 = false ∧ c13 = true ∧ c14 = false ∧ c23 = true ∧ c24 = true ∧ c34 = false) ∨
    (c01 = true ∧ c02 = true ∧ c03 = false ∧ c04 = false ∧ c12 = false ∧ c13 = true ∧ c14 = false ∧ c23 = false ∧ c24 = true ∧ c34 = true) ∨
    (c01 = true ∧ c02 = false ∧ c03 = true ∧ c04 = false ∧ c12 = false ∧ c13 = false ∧ c14 = true ∧ c23 = true ∧ c24 = true ∧ c34 = false) ∨
    (c01 = true ∧ c02 = true ∧ c03 = false ∧ c04 = false ∧ c12 = false ∧ c13 = false ∧ c14 = true ∧ c23 = true ∧ c24 = false ∧ c34 = true) ∨
    (c01 = false ∧ c02 = true ∧ c03 = false ∧ c04 = true ∧ c12 = true ∧ c13 = true ∧ c14 = false ∧ c23 = false ∧ c24 = false ∧ c34 = true) ∨
    (c01 = false ∧ c02 = true ∧ c03 = true ∧ c04 = false ∧ c12 = true ∧ c13 = false ∧ c14 = true ∧ c23 = false ∧ c24 = false ∧ c34 = true) ∨
    (c01 = false ∧ c02 = true ∧ c03 = false ∧ c04 = true ∧ c12 = false ∧ c13 = true ∧ c14 = true ∧ c23 = true ∧ c24 = false ∧ c34 = false) ∨
    (c01 = false ∧ c02 = true ∧ c03 = true ∧ c04 = false ∧ c12 = false ∧ c13 = true ∧ c14 = true ∧ c23 = false ∧ c24 = true ∧ c34 = false) ∨
    (c01 = false ∧ c02 = false ∧ c03 = true ∧ c04 = true ∧ c12 = true ∧ c13 = true ∧ c14 = false ∧ c23 = false ∧ c24 = true ∧ c34 = false) ∨
    (c01 = false ∧ c02 = false ∧ c03 = true ∧ c04 = true ∧ c12 = true ∧ c13 = false ∧ c14 = true ∧ c23 = true ∧ c24 = false ∧ c34 = false) := by
  all_goals try (cases c01 <;> simp_all)
  all_goals try (cases c02 <;> simp_all)
  all_goals try (cases c03 <;> simp_all)
  all_goals try (cases c04 <;> simp_all)
  all_goals try (cases c12 <;> simp_all)
  all_goals try (cases c13 <;> simp_all)
  all_goals try (cases c14 <;> simp_all)
  all_goals try (cases c23 <;> simp_all)
  all_goals try (cases c24 <;> simp_all)

private theorem ramsey_bits (c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : Bool)
    (h : ¬ (c01 = c02 ∧ c02 = c12) ∧
    ¬ (c01 = c03 ∧ c03 = c13) ∧
    ¬ (c01 = c04 ∧ c04 = c14) ∧
    ¬ (c01 = c05 ∧ c05 = c15) ∧
    ¬ (c02 = c03 ∧ c03 = c23) ∧
    ¬ (c02 = c04 ∧ c04 = c24) ∧
    ¬ (c02 = c05 ∧ c05 = c25) ∧
    ¬ (c03 = c04 ∧ c04 = c34) ∧
    ¬ (c03 = c05 ∧ c05 = c35) ∧
    ¬ (c04 = c05 ∧ c05 = c45) ∧
    ¬ (c12 = c13 ∧ c13 = c23) ∧
    ¬ (c12 = c14 ∧ c14 = c24) ∧
    ¬ (c12 = c15 ∧ c15 = c25) ∧
    ¬ (c13 = c14 ∧ c14 = c34) ∧
    ¬ (c13 = c15 ∧ c15 = c35) ∧
    ¬ (c14 = c15 ∧ c15 = c45) ∧
    ¬ (c23 = c24 ∧ c24 = c34) ∧
    ¬ (c23 = c25 ∧ c25 = c35) ∧
    ¬ (c24 = c25 ∧ c25 = c45) ∧
    ¬ (c34 = c35 ∧ c35 = c45)) : False := by
  rcases h with ⟨h012,h013,h014,h015,h023,h024,h025,h034,h035,h045,h123,h124,h125,h134,h135,h145,h234,h235,h245,h345⟩
  all_goals cases c01 <;> simp_all
  all_goals cases c02 <;> simp_all
  all_goals cases c03 <;> simp_all

/-- A symmetric two-coloring of five vertices without monochromatic triangles has a
cyclic labeling with one color on consecutive vertices and the other on the star. -/
theorem cycle_of_triangle_free (c : Fin 5 → Fin 5 → Bool)
    (hs : ∀ i j, c i j = c j i)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ (c i j = c i k ∧ c i k = c j k)) :
    ∃ p : Fin 5 → Fin 5, Function.Injective p ∧
      (∀ i, c (p i) (p (i + 1)) = true) ∧
      (∀ i, c (p i) (p (i + 2)) = false) := by
  have hbits := cycle_bits (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 1 2) (c 1 3) (c 1 4) (c 2 3) (c 2 4) (c 3 4) (by
    refine ⟨ht 0 1 2 (by decide) (by decide) (by decide), ht 0 1 3 (by decide) (by decide) (by decide), ht 0 1 4 (by decide) (by decide) (by decide), ht 0 2 3 (by decide) (by decide) (by decide), ht 0 2 4 (by decide) (by decide) (by decide), ht 0 3 4 (by decide) (by decide) (by decide), ht 1 2 3 (by decide) (by decide) (by decide), ht 1 2 4 (by decide) (by decide) (by decide), ht 1 3 4 (by decide) (by decide) (by decide), ht 2 3 4 (by decide) (by decide) (by decide)⟩)
  rcases hbits with h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 1, 2, 3, 4], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 1 = true
        exact h01
      · change c 1 2 = true
        exact h12
      · change c 2 3 = true
        exact h23
      · change c 3 4 = true
        exact h34
      · change c 4 0 = true
        exact (hs 4 0).trans h04
    · intro i
      fin_cases i
      · change c 0 2 = false
        exact h02
      · change c 1 3 = false
        exact h13
      · change c 2 4 = false
        exact h24
      · change c 3 0 = false
        exact (hs 3 0).trans h03
      · change c 4 1 = false
        exact (hs 4 1).trans h14
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 1, 2, 4, 3], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 1 = true
        exact h01
      · change c 1 2 = true
        exact h12
      · change c 2 4 = true
        exact h24
      · change c 4 3 = true
        exact (hs 4 3).trans h34
      · change c 3 0 = true
        exact (hs 3 0).trans h03
    · intro i
      fin_cases i
      · change c 0 2 = false
        exact h02
      · change c 1 4 = false
        exact h14
      · change c 2 3 = false
        exact h23
      · change c 4 0 = false
        exact (hs 4 0).trans h04
      · change c 3 1 = false
        exact (hs 3 1).trans h13
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 1, 3, 2, 4], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 1 = true
        exact h01
      · change c 1 3 = true
        exact h13
      · change c 3 2 = true
        exact (hs 3 2).trans h23
      · change c 2 4 = true
        exact h24
      · change c 4 0 = true
        exact (hs 4 0).trans h04
    · intro i
      fin_cases i
      · change c 0 3 = false
        exact h03
      · change c 1 2 = false
        exact h12
      · change c 3 4 = false
        exact h34
      · change c 2 0 = false
        exact (hs 2 0).trans h02
      · change c 4 1 = false
        exact (hs 4 1).trans h14
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 1, 3, 4, 2], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 1 = true
        exact h01
      · change c 1 3 = true
        exact h13
      · change c 3 4 = true
        exact h34
      · change c 4 2 = true
        exact (hs 4 2).trans h24
      · change c 2 0 = true
        exact (hs 2 0).trans h02
    · intro i
      fin_cases i
      · change c 0 3 = false
        exact h03
      · change c 1 4 = false
        exact h14
      · change c 3 2 = false
        exact (hs 3 2).trans h23
      · change c 4 0 = false
        exact (hs 4 0).trans h04
      · change c 2 1 = false
        exact (hs 2 1).trans h12
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 1, 4, 2, 3], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 1 = true
        exact h01
      · change c 1 4 = true
        exact h14
      · change c 4 2 = true
        exact (hs 4 2).trans h24
      · change c 2 3 = true
        exact h23
      · change c 3 0 = true
        exact (hs 3 0).trans h03
    · intro i
      fin_cases i
      · change c 0 4 = false
        exact h04
      · change c 1 2 = false
        exact h12
      · change c 4 3 = false
        exact (hs 4 3).trans h34
      · change c 2 0 = false
        exact (hs 2 0).trans h02
      · change c 3 1 = false
        exact (hs 3 1).trans h13
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 1, 4, 3, 2], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 1 = true
        exact h01
      · change c 1 4 = true
        exact h14
      · change c 4 3 = true
        exact (hs 4 3).trans h34
      · change c 3 2 = true
        exact (hs 3 2).trans h23
      · change c 2 0 = true
        exact (hs 2 0).trans h02
    · intro i
      fin_cases i
      · change c 0 4 = false
        exact h04
      · change c 1 3 = false
        exact h13
      · change c 4 2 = false
        exact (hs 4 2).trans h24
      · change c 3 0 = false
        exact (hs 3 0).trans h03
      · change c 2 1 = false
        exact (hs 2 1).trans h12
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 2, 1, 3, 4], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 2 = true
        exact h02
      · change c 2 1 = true
        exact (hs 2 1).trans h12
      · change c 1 3 = true
        exact h13
      · change c 3 4 = true
        exact h34
      · change c 4 0 = true
        exact (hs 4 0).trans h04
    · intro i
      fin_cases i
      · change c 0 1 = false
        exact h01
      · change c 2 3 = false
        exact h23
      · change c 1 4 = false
        exact h14
      · change c 3 0 = false
        exact (hs 3 0).trans h03
      · change c 4 2 = false
        exact (hs 4 2).trans h24
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 2, 1, 4, 3], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 2 = true
        exact h02
      · change c 2 1 = true
        exact (hs 2 1).trans h12
      · change c 1 4 = true
        exact h14
      · change c 4 3 = true
        exact (hs 4 3).trans h34
      · change c 3 0 = true
        exact (hs 3 0).trans h03
    · intro i
      fin_cases i
      · change c 0 1 = false
        exact h01
      · change c 2 4 = false
        exact h24
      · change c 1 3 = false
        exact h13
      · change c 4 0 = false
        exact (hs 4 0).trans h04
      · change c 3 2 = false
        exact (hs 3 2).trans h23
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 2, 3, 1, 4], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 2 = true
        exact h02
      · change c 2 3 = true
        exact h23
      · change c 3 1 = true
        exact (hs 3 1).trans h13
      · change c 1 4 = true
        exact h14
      · change c 4 0 = true
        exact (hs 4 0).trans h04
    · intro i
      fin_cases i
      · change c 0 3 = false
        exact h03
      · change c 2 1 = false
        exact (hs 2 1).trans h12
      · change c 3 4 = false
        exact h34
      · change c 1 0 = false
        exact (hs 1 0).trans h01
      · change c 4 2 = false
        exact (hs 4 2).trans h24
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 2, 4, 1, 3], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 2 = true
        exact h02
      · change c 2 4 = true
        exact h24
      · change c 4 1 = true
        exact (hs 4 1).trans h14
      · change c 1 3 = true
        exact h13
      · change c 3 0 = true
        exact (hs 3 0).trans h03
    · intro i
      fin_cases i
      · change c 0 4 = false
        exact h04
      · change c 2 1 = false
        exact (hs 2 1).trans h12
      · change c 4 3 = false
        exact (hs 4 3).trans h34
      · change c 1 0 = false
        exact (hs 1 0).trans h01
      · change c 3 2 = false
        exact (hs 3 2).trans h23
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 3, 1, 2, 4], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 3 = true
        exact h03
      · change c 3 1 = true
        exact (hs 3 1).trans h13
      · change c 1 2 = true
        exact h12
      · change c 2 4 = true
        exact h24
      · change c 4 0 = true
        exact (hs 4 0).trans h04
    · intro i
      fin_cases i
      · change c 0 1 = false
        exact h01
      · change c 3 2 = false
        exact (hs 3 2).trans h23
      · change c 1 4 = false
        exact h14
      · change c 2 0 = false
        exact (hs 2 0).trans h02
      · change c 4 3 = false
        exact (hs 4 3).trans h34
  · rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
    refine ⟨![0, 3, 2, 1, 4], by decide, ?_, ?_⟩
    · intro i
      fin_cases i
      · change c 0 3 = true
        exact h03
      · change c 3 2 = true
        exact (hs 3 2).trans h23
      · change c 2 1 = true
        exact (hs 2 1).trans h12
      · change c 1 4 = true
        exact h14
      · change c 4 0 = true
        exact (hs 4 0).trans h04
    · intro i
      fin_cases i
      · change c 0 2 = false
        exact h02
      · change c 3 1 = false
        exact (hs 3 1).trans h13
      · change c 2 4 = false
        exact h24
      · change c 1 0 = false
        exact (hs 1 0).trans h01
      · change c 4 3 = false
        exact (hs 4 3).trans h34

/-- Every symmetric two-coloring of six vertices has a monochromatic triangle. -/
theorem exists_monochromatic_triangle_six (c : Fin 6 → Fin 6 → Bool)
    (hs : ∀ i j, c i j = c j i) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      c i j = c i k ∧ c i k = c j k := by
  by_contra h
  have ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ (c i j = c i k ∧ c i k = c j k) := by
    intro i j k hij hik hjk hc
    exact h ⟨i,j,k,hij,hik,hjk,hc⟩
  exact ramsey_bits (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 0 5) (c 1 2) (c 1 3) (c 1 4) (c 1 5) (c 2 3) (c 2 4) (c 2 5) (c 3 4) (c 3 5) (c 4 5) (by
    refine ⟨ht 0 1 2 (by decide) (by decide) (by decide), ht 0 1 3 (by decide) (by decide) (by decide), ht 0 1 4 (by decide) (by decide) (by decide), ht 0 1 5 (by decide) (by decide) (by decide), ht 0 2 3 (by decide) (by decide) (by decide), ht 0 2 4 (by decide) (by decide) (by decide), ht 0 2 5 (by decide) (by decide) (by decide), ht 0 3 4 (by decide) (by decide) (by decide), ht 0 3 5 (by decide) (by decide) (by decide), ht 0 4 5 (by decide) (by decide) (by decide), ht 1 2 3 (by decide) (by decide) (by decide), ht 1 2 4 (by decide) (by decide) (by decide), ht 1 2 5 (by decide) (by decide) (by decide), ht 1 3 4 (by decide) (by decide) (by decide), ht 1 3 5 (by decide) (by decide) (by decide), ht 1 4 5 (by decide) (by decide) (by decide), ht 2 3 4 (by decide) (by decide) (by decide), ht 2 3 5 (by decide) (by decide) (by decide), ht 2 4 5 (by decide) (by decide) (by decide), ht 3 4 5 (by decide) (by decide) (by decide)⟩)

example : ∃ c : Fin 6 → Fin 6 → Bool, ∀ i j, c i j = c j i :=
  ⟨fun _ _ => true, fun _ _ => rfl⟩

example : ∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ (c i j = c i k ∧ c i k = c j k)) := by
  refine ⟨fun i j => decide (j = i + 1 ∨ i = j + 1), ?_, ?_⟩
  · decide
  · decide

end Erdos132.KnownSixPointCombinatorics
