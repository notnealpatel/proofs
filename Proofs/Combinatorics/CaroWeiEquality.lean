import Combinatorics.CaroWeiDefect

set_option autoImplicit false

namespace ErdosCandidates.CaroWei

private theorem closed_eq_of_mem {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (hlocal : ∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c)
    (x y : V) (hy : y ∈ insert x (G.neighborFinset x)) :
    insert y (G.neighborFinset y) = insert x (G.neighborFinset x) := by
  have hsubset (a b : V) (hab : b ∈ insert a (G.neighborFinset a)) :
      insert b (G.neighborFinset b) ⊆ insert a (G.neighborFinset a) := by
    intro z hz
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hab hz ⊢
    rcases hab with rfl | hab
    · exact hz
    rcases hz with rfl | hbz
    · exact Or.inr hab
    by_cases haz : z = a
    · exact Or.inl haz
    · exact Or.inr (hlocal a b z hab hbz (Ne.symm haz))
  apply Finset.Subset.antisymm (hsubset x y hy)
  apply hsubset y x
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hy ⊢
  exact hy.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

/-- If every two-edge path with distinct endpoints has adjacent endpoints,
all independent sets have cardinality at most the Caro–Wei weight. -/
theorem independent_bound_of_local {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlocal : ∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    (S.card : ℝ) ≤ ∑ v : V, 1 / ((G.degree v : ℝ) + 1) := by
  classical
  let C : V → Finset V := fun x => insert x (G.neighborFinset x)
  let w : V → ℝ := fun x => 1 / ((G.degree x : ℝ) + 1)
  have hcard (x : V) : (C x).card = G.degree x + 1 := by
    simp [C, G.card_neighborFinset_eq_degree]
  have hweight (x : V) : ∑ y ∈ C x, w y = 1 := by
    have hdeg (y : V) (hy : y ∈ C x) : G.degree y = G.degree x := by
      have heq := congrArg Finset.card (closed_eq_of_mem G hlocal x y hy)
      rw [hcard y, hcard x] at heq
      omega
    calc
      _ = ∑ _y ∈ C x, 1 / ((G.degree x : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [w]
        rw [hdeg y hy]
      _ = 1 := by
        rw [Finset.sum_const, hcard x, nsmul_eq_mul]
        push_cast
        field_simp
  have hdisjoint : (S : Set V).PairwiseDisjoint C := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hzx hzy
    have heq : C y = C x :=
      (closed_eq_of_mem G hlocal y z hzy).symm.trans
        (closed_eq_of_mem G hlocal x z hzx)
    have hyx : y ∈ C x := heq ▸ Finset.mem_insert_self y (G.neighborFinset y)
    have hadj : G.Adj x y := by
      rcases Finset.mem_insert.mp hyx with he | he
      · exact (hxy he.symm).elim
      · exact (G.mem_neighborFinset x y).mp he
    exact hS hx hy hxy hadj
  calc
    (S.card : ℝ) = ∑ x ∈ S, ∑ y ∈ C x, w y := by simp [hweight]
    _ = ∑ y ∈ S.biUnion C, w y := (Finset.sum_biUnion hdisjoint).symm
    _ ≤ ∑ y : V, w y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro y _ _
      dsimp [w]
      positivity

/-- The universal reverse Caro–Wei inequality holds exactly for graphs in which
all two-edge paths with distinct endpoints have adjacent endpoints (unions of cliques). -/
theorem universal_independent_bound_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ S : Finset V, G.IsIndepSet (S : Set V) →
      (S.card : ℝ) ≤ ∑ v : V, 1 / ((G.degree v : ℝ) + 1)) ↔
    (∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) := by
  classical
  constructor
  · intro hbound a b c hab hbc hac
    by_contra hnac
    let D := max 2 (Finset.univ.sup (fun x => G.degree x))
    have hD : 2 ≤ D := le_max_left _ _
    have hdegree (x : V) : G.degree x ≤ D :=
      (Finset.le_sup (f := fun y => G.degree y) (Finset.mem_univ x)).trans
        (le_max_right _ _)
    obtain ⟨S, hS, hgain⟩ :=
      exists_independent_set_defect G D hD hdegree a b c hab hbc hac hnac
    have hpos : (0 : ℝ) < 1 / ((D : ℝ) * ((D : ℝ) + 1)) := by
      have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
      positivity
    have hupper := hbound S hS
    linarith
  · exact fun hlocal S hS => independent_bound_of_local G hlocal S hS

/-- On a union of cliques the Caro–Wei weight is attained by an independent set. -/
theorem exists_independent_set_equality {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlocal : ∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c) :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      (S.card : ℝ) = ∑ v : V, 1 / ((G.degree v : ℝ) + 1) := by
  obtain ⟨S, hS, hlower⟩ := exists_independent_set G
  exact ⟨S, hS, le_antisymm (independent_bound_of_local G hlocal S hS) hlower⟩

example : ∀ a b c : Fin 3, (⊤ : SimpleGraph (Fin 3)).Adj a b →
    (⊤ : SimpleGraph (Fin 3)).Adj b c → a ≠ c →
    (⊤ : SimpleGraph (Fin 3)).Adj a c := by
  decide

example : ∃ S : Finset (Fin 3), (⊤ : SimpleGraph (Fin 3)).IsIndepSet (S : Set (Fin 3)) ∧
    (S.card : ℝ) = ∑ v : Fin 3, 1 / (((⊤ : SimpleGraph (Fin 3)).degree v : ℝ) + 1) :=
  exists_independent_set_equality ⊤ (by decide)

example : ∃ S : Finset (Fin 0), (⊥ : SimpleGraph (Fin 0)).IsIndepSet (S : Set (Fin 0)) ∧
    (S.card : ℝ) = ∑ v : Fin 0, 1 / (((⊥ : SimpleGraph (Fin 0)).degree v : ℝ) + 1) :=
  exists_independent_set_equality ⊥ (by decide)

end ErdosCandidates.CaroWei
