import Mathlib

set_option autoImplicit false

namespace HypercubeGraph
open SimpleGraph

/-- The hypercube on Boolean vectors, adjacent at exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := (Finset.univ.filter (fun i => x i ≠ y i)).card = 1
  symm := ⟨by
    intro x y h
    simpa [ne_comm] using h⟩
  loopless := ⟨by
    intro x h
    simp at h⟩

instance (n : ℕ) : DecidableRel (hypercube n).Adj := fun _ _ => inferInstanceAs (Decidable (_ = 1))

example : (hypercube 1).Adj (fun _ => false) (fun _ => true) := by decide
example : ¬ (hypercube 0).Adj (fun _ => false) (fun _ => true) := by decide

/-- A graph is C4-free if there is no injective copy of the four-cycle. -/
def C4Free {V : Type*} (H : SimpleGraph V) : Prop :=
  (cycleGraph 4).Free H

example {V : Type*} (H : SimpleGraph V) :
    C4Free H ↔ (cycleGraph 4).Free H := Iff.rfl

open scoped Classical in
/-- The original finite supremum over all C4-free subgraphs of the hypercube. -/
noncomputable def maxC4FreeEdges (n : ℕ) : ℕ :=
  Finset.sup
    (Finset.univ.filter
      (fun H : SimpleGraph (Fin n → Bool) => H ≤ hypercube n ∧ C4Free H))
    (fun H => H.edgeFinset.card)

/-- There are two choices independently at each coordinate. -/
theorem hypercube_card_verts (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by simp

private def flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !(x j) else x j

example : flip (fun _ : Fin 1 => false) 0 = (fun _ => true) := by decide

private theorem flip_adj {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (hypercube n).Adj x (flip x i) := by
  change (Finset.univ.filter (fun j => x j ≠ flip x i j)).card = 1
  have h : Finset.univ.filter (fun j => x j ≠ flip x i j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j; simp [flip]
    · simp [flip, hj]
  rw [h]
  simp

private theorem flip_injective {n : ℕ} (x : Fin n → Bool) :
    Function.Injective (flip x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [flip, hij] at hi

private theorem eq_flip_of_adj {n : ℕ} (x y : Fin n → Bool)
    (h : (hypercube n).Adj x y) : ∃ i, flip x i = y := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hdiff : ∀ j, x j ≠ y j ↔ j = i := by
    intro j
    have hm := congrArg (fun s : Finset (Fin n) => j ∈ s) hi
    simpa using hm
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j = i
  · subst j
    have hn : x i ≠ y i := (hdiff i).mpr rfl
    simp only [flip]
    cases hx : x i <;> cases hy : y i <;> simp_all
  · have he : x j = y j := not_ne_iff.mp (fun hn => hj ((hdiff j).mp hn))
    simp [flip, hj, he]

/-- Each vertex has exactly one neighbor for each coordinate. -/
theorem hypercube_degree (n : ℕ) [DecidableRel (hypercube n).Adj] (x : Fin n → Bool) :
    (hypercube n).degree x = n := by
  classical
  let e : Fin n ≃ {y // (hypercube n).Adj x y} :=
    Equiv.ofBijective (fun i => ⟨flip x i, flip_adj x i⟩) (by
      constructor
      · intro i j h
        exact flip_injective x (congrArg Subtype.val h)
      · intro y
        obtain ⟨i, hi⟩ := eq_flip_of_adj x y.val y.property
        exact ⟨i, Subtype.ext hi⟩)
  rw [SimpleGraph.degree, ← Fintype.card_coe]
  simpa using (Fintype.card_congr e).symm

/-- Handshaking gives the exact number of hypercube edges, including dimension zero. -/
theorem hypercube_card_edges (n : ℕ) [DecidableRel (hypercube n).Adj] :
    (hypercube n).edgeFinset.card = n * 2 ^ (n - 1) := by
  classical
  have hs := (hypercube n).sum_degrees_eq_twice_card_edges
  simp only [hypercube_degree, Finset.sum_const, Finset.card_univ,
    hypercube_card_verts, smul_eq_mul] at hs
  cases n with
  | zero => simp_all
  | succ k =>
    simp only [Nat.add_sub_cancel, pow_succ] at *
    nlinarith

private theorem cycle_four_edges : (cycleGraph 4).edgeFinset.card = 4 := by decide

/-- An injective four-cycle copy requires at least four distinct edges. -/
theorem c4Free_of_card_edges_lt_four {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.edgeFinset.card < 4) :
    C4Free H := by
  classical
  intro hc
  obtain ⟨f⟩ := hc
  have hcard := Fintype.card_le_of_embedding f.mapEdgeSet
  rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet, cycle_four_edges] at hcard
  omega

example : C4Free (⊥ : SimpleGraph (Fin 1)) :=
  c4Free_of_card_edges_lt_four _ (by decide)

/-- Bottom is always a feasible subgraph in the extremal supremum. -/
theorem c4Free_bot {V : Type*} : C4Free (⊥ : SimpleGraph V) := by
  intro hc
  obtain ⟨f⟩ := hc
  exact f.toHom.map_rel (by decide : (cycleGraph 4).Adj 0 1)

private def squareVertex (i : Fin 4) : Fin 2 → Bool :=
  ![![false, false], ![false, true], ![true, true], ![true, false]] i

example : squareVertex 0 = ![false, false] := rfl
example : squareVertex 3 = ![true, false] := rfl

private def squareCopy : (cycleGraph 4).Copy (hypercube 2) where
  toHom := {
    toFun := squareVertex
    map_rel' := by decide }
  injective' := by decide

example : squareCopy 0 = ![false, false] := rfl

/-- The two-dimensional cube contains the four-cycle in cyclic Gray-code order. -/
theorem not_c4Free_hypercube_two : ¬ C4Free (hypercube 2) := by
  intro h
  exact h ⟨squareCopy⟩

/-- Every admissible subgraph is bounded by the finite supremum. -/
theorem card_edges_le_maxC4FreeEdges (n : ℕ) (H : SimpleGraph (Fin n → Bool))
    [DecidableRel H.Adj] (hsub : H ≤ hypercube n) (hfree : C4Free H) :
    H.edgeFinset.card ≤ maxC4FreeEdges n := by
  classical
  unfold maxC4FreeEdges
  letI : DecidableRel H.Adj := fun x y => Classical.propDecidable (H.Adj x y)
  apply le_trans (b := H.edgeFinset.card)
  · exact le_of_eq (by
      apply congrArg Finset.card
      ext e
      simp only [SimpleGraph.mem_edgeFinset])
  · exact Finset.le_sup
      (s := Finset.univ.filter
        (fun G : SimpleGraph (Fin n → Bool) => G ≤ hypercube n ∧ C4Free G))
      (f := fun G : SimpleGraph (Fin n → Bool) => G.edgeFinset.card)
      (b := H) (by simp [hsub, hfree])

open scoped Classical in
/-- The finite supremum is attained by an admissible subgraph. -/
theorem maxC4FreeEdges_attained (n : ℕ) :
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ C4Free H ∧
      H.edgeFinset.card = maxC4FreeEdges n := by
  classical
  let s := Finset.univ.filter
    (fun H : SimpleGraph (Fin n → Bool) => H ≤ hypercube n ∧ C4Free H)
  have hne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [s, c4Free_bot]
  obtain ⟨H, hH, he⟩ := Finset.exists_mem_eq_sup s hne (fun H => H.edgeFinset.card)
  have hm : H ≤ hypercube n ∧ C4Free H := (Finset.mem_filter.mp hH).2
  exact ⟨H, hm.1, hm.2, he.symm⟩

/-- The extremal count cannot exceed all the edges of the cube. -/
theorem maxC4FreeEdges_le (n : ℕ) : maxC4FreeEdges n ≤ n * 2 ^ (n - 1) := by
  classical
  obtain ⟨H, hsub, hfree, he⟩ := maxC4FreeEdges_attained n
  rw [← he, ← hypercube_card_edges n]
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)

/-- In dimension zero there are no edges to retain. -/
theorem maxC4FreeEdges_zero : maxC4FreeEdges 0 = 0 := by
  have h := maxC4FreeEdges_le 0
  simpa using h

/-- The one-dimensional cube is a single C4-free edge. -/
theorem maxC4FreeEdges_one : maxC4FreeEdges 1 = 1 := by
  have hu := maxC4FreeEdges_le 1
  have hf : C4Free (hypercube 1) :=
    c4Free_of_card_edges_lt_four _ (by rw [hypercube_card_edges]; decide)
  have hl := card_edges_le_maxC4FreeEdges 1 (hypercube 1) le_rfl hf
  rw [hypercube_card_edges] at hl
  norm_num at hu hl ⊢
  omega

private def brokenSquare : SimpleGraph (Fin 2 → Bool) :=
  (hypercube 2).deleteEdges {s(squareVertex 0, squareVertex 1)}

private instance : DecidableRel brokenSquare.Adj := by
  unfold brokenSquare
  infer_instance

private theorem brokenSquare_card : brokenSquare.edgeFinset.card = 3 := by decide

example : ¬ brokenSquare.Adj (squareVertex 0) (squareVertex 1) := by decide

example : brokenSquare ≤ hypercube 2 := SimpleGraph.deleteEdges_le _

/-- Removing one edge of the square realizes the maximum of three edges. -/
theorem maxC4FreeEdges_two : maxC4FreeEdges 2 = 3 := by
  classical
  obtain ⟨H, hsub, hf, he⟩ := maxC4FreeEdges_attained 2
  have hc : (hypercube 2).edgeFinset.card = 4 := by rw [hypercube_card_edges]; decide
  have hle : H.edgeFinset.card ≤ 4 := by
    rw [← hc]
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
  have hne : H.edgeFinset.card ≠ 4 := by
    intro h4
    have heq : H.edgeFinset = (hypercube 2).edgeFinset :=
      Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hsub) (by omega)
    have hg : H = hypercube 2 := SimpleGraph.edgeFinset_inj.mp heq
    exact not_c4Free_hypercube_two (hg ▸ hf)
  have hbfree : C4Free brokenSquare :=
    c4Free_of_card_edges_lt_four _ (by rw [brokenSquare_card]; decide)
  have hlo := card_edges_le_maxC4FreeEdges 2 brokenSquare
    (SimpleGraph.deleteEdges_le _) hbfree
  rw [brokenSquare_card] at hlo
  omega

example (n : ℕ) : Nonempty (Fin n → Bool) := ⟨fun _ => false⟩

example : hypercube 1 ≤ hypercube 1 ∧ C4Free (hypercube 1) ∧
    (hypercube 1).edgeFinset.card = 1 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · exact c4Free_of_card_edges_lt_four _ (by decide)
  · decide

example : maxC4FreeEdges 0 = 0 := maxC4FreeEdges_zero
example : maxC4FreeEdges 1 = 1 := maxC4FreeEdges_one
example : maxC4FreeEdges 2 = 3 := maxC4FreeEdges_two

end HypercubeGraph
