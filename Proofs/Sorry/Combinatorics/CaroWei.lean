import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ErdosCandidates.CaroWei

universe u

private theorem degree_induce_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Set V)
    [DecidablePred (· ∈ R)] (x : R) : (G.induce R).degree x ≤ G.degree x := by
  classical
  have h := Finset.card_le_card
    (Finset.inter_subset_left (s₁ := G.neighborFinset x) (s₂ := R.toFinset))
  rw [← G.map_neighborFinset_induce x, Finset.card_map] at h
  exact h

private theorem exists_of_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
        (∑ v : V, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (S.card : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G _ hcard
    classical
    by_cases hV : IsEmpty V
    · letI := hV
      exact ⟨∅, by simp [SimpleGraph.IsIndepSet], by simp⟩
    · haveI : Nonempty V := not_isEmpty_iff.mp hV
      obtain ⟨v, _, hv⟩ := Finset.exists_min_image Finset.univ (fun x => G.degree x) Finset.univ_nonempty
      have hmin (x : V) : G.degree v ≤ G.degree x := hv x (Finset.mem_univ x)
      let C : Finset V := insert v (G.neighborFinset v)
      let R := {x : V // x ∉ C}
      let H : SimpleGraph R := G.induce {x | x ∉ C}
      have hvC : v ∈ C := Finset.mem_insert_self _ _
      have hsmall : Fintype.card R < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (by simpa using hvC)
      have hCcard : C.card = G.degree v + 1 := by
        simp [C, G.card_neighborFinset_eq_degree]
      have hCweight : (∑ x ∈ C, (1 : ℝ) / ((G.degree x : ℝ) + 1)) ≤ 1 := by
        calc
          _ ≤ ∑ _x ∈ C, (1 : ℝ) / ((G.degree v : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro x _
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right (hmin x) 1
          _ = 1 := by
            rw [Finset.sum_const, hCcard, nsmul_eq_mul]
            push_cast
            field_simp
      have hRweight : (∑ x : R, (1 : ℝ) / ((G.degree x : ℝ) + 1)) ≤
          ∑ x : R, (1 : ℝ) / ((H.degree x : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro x _
        apply one_div_le_one_div_of_le (by positivity)
        have hd : H.degree x ≤ G.degree x := degree_induce_le G {x | x ∉ C} x
        exact_mod_cast Nat.add_le_add_right hd 1
      obtain ⟨T, hTind, hTweight⟩ := ih (Fintype.card R) hsmall R H rfl
      let e : R ↪ V := Function.Embedding.subtype (fun x => x ∉ C)
      let U : Finset V := T.map e
      have hU (x : V) (hx : x ∈ U) : x ∉ C := by
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.property
      have hvU : v ∉ U := fun hvU => hU v hvU hvC
      have hUind : G.IsIndepSet (U : Set V) := by
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
        have hab : a ≠ b := fun hab => hxy (congrArg e hab)
        exact hTind ha hb hab
      have hvnotadj (x : V) (hx : x ∈ U) : ¬ G.Adj v x := by
        intro hadj
        exact hU x hx (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x).mpr hadj))
      have hSind : G.IsIndepSet ((insert v U : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · exact hvnotadj y hy
        · rcases hy with rfl | hy
          · exact fun hadj => hvnotadj x hx hadj.symm
          · exact hUind hx hy hxy
      have hScard : (insert v U).card = T.card + 1 := by
        rw [Finset.card_insert_of_notMem hvU, Finset.card_map]
      have hpart : (∑ x ∈ C, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
          (∑ x : R, (1 : ℝ) / ((G.degree x : ℝ) + 1)) =
          ∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1) := by
        rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
        exact Fintype.sum_subtype_add_sum_subtype (fun x => x ∈ C)
          (fun x => (1 : ℝ) / ((G.degree x : ℝ) + 1))
      refine ⟨insert v U, hSind, ?_⟩
      rw [← hpart, hScard, Nat.cast_add, Nat.cast_one]
      linarith

/-- The Caro–Wei bound: a finite simple graph has an independent vertex set whose
cardinality is at least the sum of the reciprocals of degree plus one. -/
theorem exists_independent_set {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      (∑ v : V, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (S.card : ℝ) :=
  exists_of_card (Fintype.card V) V G rfl

example : ∃ S : Finset (Fin 0), (⊥ : SimpleGraph (Fin 0)).IsIndepSet (S : Set (Fin 0)) ∧
    (∑ v : Fin 0, (1 : ℝ) / (((⊥ : SimpleGraph (Fin 0)).degree v : ℝ) + 1)) ≤
      (S.card : ℝ) := exists_independent_set ⊥

example : ∃ S : Finset (Fin 3), (⊤ : SimpleGraph (Fin 3)).IsIndepSet (S : Set (Fin 3)) ∧
    (∑ v : Fin 3, (1 : ℝ) / (((⊤ : SimpleGraph (Fin 3)).degree v : ℝ) + 1)) ≤
      (S.card : ℝ) := exists_independent_set ⊤

end ErdosCandidates.CaroWei
