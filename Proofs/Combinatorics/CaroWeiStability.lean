import Combinatorics.CaroWeiEquality

set_option autoImplicit false

namespace ErdosCandidates.CaroWei

/-- A bounded-degree graph has an independent set whose Caro–Wei excess pays
for deleting vertices until every two-edge path has adjacent distinct endpoints. -/
theorem exists_independent_set_stability {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ v : V, G.degree v ≤ D) :
    ∃ S X : Finset V, G.IsIndepSet (S : Set V) ∧
      (∀ a b c : V, a ∉ X → b ∉ X → c ∉ X →
        G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) ∧
      (X.card : ℝ) ≤ ((D : ℝ) * ((D : ℝ) + 1)^2) *
        ((S.card : ℝ) - ∑ v : V, 1 / ((G.degree v : ℝ) + 1)) := by
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hlocal : ∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c
    · obtain ⟨S, hS, heq⟩ := exists_independent_set_equality G hlocal
      refine ⟨S, ∅, hS, ?_, ?_⟩
      · intro a b c _ _ _ hab hbc hac
        exact hlocal a b c hab hbc hac
      · simp [heq]
    · push Not at hlocal
      obtain ⟨a, b, c, hab, hbc, hac, hnac⟩ := hlocal
      obtain ⟨v, hstep⟩ := exists_residual_step G D hD hdegree a b c hab hbc hac hnac
      let C := insert v (G.neighborFinset v)
      let R := {x : V // x ∉ C}
      let H : SimpleGraph R := G.induce {x | x ∉ C}
      have hvC : v ∈ C := Finset.mem_insert_self _ _
      have hsmall : Fintype.card R < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (not_not.mpr hvC)
      have hdeg (x : R) : H.degree x ≤ D := by
        have hm := Finset.card_le_card
          (Finset.inter_subset_left (s₁ := G.neighborFinset x)
            (s₂ := ({x | x ∉ C} : Set V).toFinset))
        rw [← G.map_neighborFinset_induce (s := {x | x ∉ C}) x,
          Finset.card_map] at hm
        exact hm.trans (hdegree x)
      obtain ⟨T, Y, hT, hY, hbound⟩ :=
        ih (Fintype.card R) hsmall H hdeg rfl
      let e : R ↪ V := Function.Embedding.subtype (fun x => x ∉ C)
      let U := T.map e
      let X := C ∪ Y.map e
      have hU (x : V) (hx : x ∈ U) : x ∉ C := by
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.property
      have hvU : v ∉ U := fun hv => hU v hv hvC
      have hUind : G.IsIndepSet (U : Set V) := by
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
        exact hT ha hb (fun he => hxy (congrArg e he))
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
      have hclosed : ∀ a b c : V, a ∉ X → b ∉ X → c ∉ X →
          G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c := by
        intro a b c ha hb hc hab hbc hac
        have hout (x : V) (hx : x ∉ X) : x ∉ C :=
          fun hm => hx (Finset.mem_union_left _ hm)
        let a' : R := ⟨a, hout a ha⟩
        let b' : R := ⟨b, hout b hb⟩
        let c' : R := ⟨c, hout c hc⟩
        have hnot (x : R) (hx : (x : V) ∉ X) : x ∉ Y := by
          intro hm
          exact hx (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨x, hm, rfl⟩))
        exact hY a' b' c' (hnot a' ha) (hnot b' hb) (hnot c' hc)
          hab hbc (fun he => hac (congrArg Subtype.val he))
      have hCcard : C.card ≤ D + 1 := by
        have he : C.card = G.degree v + 1 := by
          simp [C, G.card_neighborFinset_eq_degree]
        rw [he]
        exact Nat.add_le_add_right (hdegree v) 1
      have hXcard : (X.card : ℝ) ≤ (D : ℝ) + 1 + (Y.card : ℝ) := by
        have hc := (Finset.card_union_le C (Y.map e)).trans
          (Nat.add_le_add_right hCcard (Y.map e).card)
        rw [Finset.card_map] at hc
        exact_mod_cast hc
      refine ⟨insert v U, X, hSind, hclosed, ?_⟩
      rw [hScard, Nat.cast_add, Nat.cast_one]
      change (∑ x : V, (1 : ℝ) / ((G.degree x : ℝ) + 1)) +
        1 / ((D : ℝ) * ((D : ℝ) + 1)) ≤
        1 + ∑ x : R, (1 : ℝ) / ((H.degree x : ℝ) + 1) at hstep
      have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
      have hKpos : 0 ≤ (D : ℝ) * ((D : ℝ) + 1)^2 := by positivity
      have hpay : ((D : ℝ) * ((D : ℝ) + 1)^2) *
          (1 / ((D : ℝ) * ((D : ℝ) + 1))) = (D : ℝ) + 1 := by
        field_simp
      have hscaled := mul_le_mul_of_nonneg_left hstep hKpos
      nlinarith

example : (2 ≤ (2 : ℕ)) ∧
    (∀ v : Fin 3, (⊤ : SimpleGraph (Fin 3)).degree v ≤ 2) := by decide

example : ∃ S X : Finset (Fin 3),
    (⊤ : SimpleGraph (Fin 3)).IsIndepSet (S : Set (Fin 3)) ∧
    (∀ a b c : Fin 3, a ∉ X → b ∉ X → c ∉ X →
      (⊤ : SimpleGraph (Fin 3)).Adj a b → (⊤ : SimpleGraph (Fin 3)).Adj b c →
      a ≠ c → (⊤ : SimpleGraph (Fin 3)).Adj a c) ∧
    (X.card : ℝ) ≤ ((2 : ℝ) * ((2 : ℝ) + 1)^2) *
      ((S.card : ℝ) - ∑ v : Fin 3, 1 / (((⊤ : SimpleGraph (Fin 3)).degree v : ℝ) + 1)) :=
  exists_independent_set_stability ⊤ 2 (by decide) (by decide)

example : let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
    (2 ≤ (2 : ℕ)) ∧ (∀ v, G.degree v ≤ 2) ∧
      ¬ (∀ a b c, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) := by
  decide

example : let G : SimpleGraph (Fin 3) :=
    SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
    ∃ S X : Finset (Fin 3), G.IsIndepSet (S : Set (Fin 3)) ∧
      (∀ a b c : Fin 3, a ∉ X → b ∉ X → c ∉ X →
        G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) ∧
      (X.card : ℝ) ≤ ((2 : ℝ) * ((2 : ℝ) + 1)^2) *
        ((S.card : ℝ) - ∑ v : Fin 3, 1 / ((G.degree v : ℝ) + 1)) := by
  let G : SimpleGraph (Fin 3) := SimpleGraph.fromRel (fun x y => x.val + 1 = y.val)
  exact exists_independent_set_stability G 2 (by decide) (by decide)

end ErdosCandidates.CaroWei
