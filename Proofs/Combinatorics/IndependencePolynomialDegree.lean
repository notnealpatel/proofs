import Combinatorics.IndependencePolynomial

set_option autoImplicit false

namespace ErdosCandidates.E993

open SimpleGraph

private theorem extension_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (s : Finset V) (hs : Gᶜ.IsClique s) :
    Fintype.card V ≤
      (Finset.univ.filter (fun v => v ∉ s ∧ Gᶜ.IsClique (↑(insert v s) : Set V))).card +
        (Δ + 1) * s.card := by
  classical
  let e := Finset.univ.filter (fun v => v ∉ s ∧ Gᶜ.IsClique (↑(insert v s) : Set V))
  let b := s ∪ s.biUnion (fun u => G.neighborFinset u)
  have hcover : (Finset.univ : Finset V) ⊆ e ∪ b := by
    intro v hv
    by_cases hb : v ∈ b
    · exact Finset.mem_union_right e hb
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hv, ?_, ?_⟩
      · intro hvs
        exact hb (Finset.mem_union_left _ hvs)
      · rw [Finset.coe_insert]
        apply hs.insert
        intro u hu hne
        have hnot : ¬ G.Adj u v := by
          intro huv
          exact hb (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨u, hu, (G.mem_neighborFinset u v).mpr huv⟩))
        exact ⟨hne, fun hvu => hnot hvu.symm⟩
  have hb : b.card ≤ (Δ + 1) * s.card := by
    calc
      b.card ≤ s.card + (s.biUnion (fun u => G.neighborFinset u)).card := Finset.card_union_le _ _
      _ ≤ s.card + ∑ u ∈ s, (G.neighborFinset u).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ s.card + ∑ u ∈ s, Δ := by
        apply Nat.add_le_add_left
        exact Finset.sum_le_sum (fun u _ => hdeg u)
      _ = (Δ + 1) * s.card := by simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]
  calc
    Fintype.card V = (Finset.univ : Finset V).card := Finset.card_univ.symm
    _ ≤ (e ∪ b).card := Finset.card_le_card hcover
    _ ≤ e.card + b.card := Finset.card_union_le _ _
    _ ≤ e.card + (Δ + 1) * s.card := Nat.add_le_add_left hb _

private theorem extension_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (∑ s ∈ Gᶜ.cliqueFinset k,
      (Finset.univ.filter (fun v => v ∉ s ∧
        Gᶜ.IsClique (↑(insert v s) : Set V))).card) =
      (k + 1) * indepCount G (k + 1) := by
  classical
  let e := fun s : Finset V => Finset.univ.filter
    (fun v => v ∉ s ∧ Gᶜ.IsClique (↑(insert v s) : Set V))
  have hcard : ((Gᶜ.cliqueFinset k).sigma e).card =
      ((Gᶜ.cliqueFinset (k + 1)).sigma (fun s => s)).card := by
    apply Finset.card_bij (fun a _ => (⟨insert a.2 a.1, a.2⟩ : Sigma (fun _ : Finset V => V)))
    · intro a ha
      obtain ⟨hs, hv⟩ := Finset.mem_sigma.mp ha
      have hs' := SimpleGraph.mem_cliqueFinset_iff.mp hs
      have hv' : a.2 ∉ a.1 ∧ Gᶜ.IsClique (↑(insert a.2 a.1) : Set V) := by
        simpa [e] using hv
      apply Finset.mem_sigma.mpr
      refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ⟨hv'.2, ?_⟩, Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hv'.1, hs'.2]
    · intro a ha b hb hab
      obtain ⟨hs, hv⟩ := Finset.mem_sigma.mp ha
      obtain ⟨ht, hw⟩ := Finset.mem_sigma.mp hb
      have hv' : a.2 ∉ a.1 := (Finset.mem_filter.mp hv).2.1
      have hw' : b.2 ∉ b.1 := (Finset.mem_filter.mp hw).2.1
      have hfirst : insert a.2 a.1 = insert b.2 b.1 := congrArg Sigma.fst hab
      have hsecond : a.2 = b.2 := eq_of_heq (Sigma.mk.inj_iff.mp hab).2
      have hsets : a.1 = b.1 := by
        have he := congrArg (fun s => s.erase a.2) hfirst
        rw [Finset.erase_insert hv', hsecond, Finset.erase_insert hw'] at he
        exact he
      exact Sigma.ext hsets (by simpa using hsecond)
    · intro b hb
      obtain ⟨ht, hv⟩ := Finset.mem_sigma.mp hb
      have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
      have herase : Gᶜ.IsClique (↑(b.1.erase b.2) : Set V) := by
        intro x hx y hy hxy
        exact ht'.1 (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
      refine ⟨⟨b.1.erase b.2, b.2⟩, ?_, ?_⟩
      · apply Finset.mem_sigma.mpr
        refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ⟨herase, ?_⟩, ?_⟩
        · change (b.1.erase b.2).card = k
          have hc := Finset.card_erase_add_one hv
          rw [ht'.2] at hc
          omega
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, Finset.notMem_erase _ _, ?_⟩
          rw [Finset.insert_erase hv]
          exact ht'.1
      · simp [Finset.insert_erase hv]
  rw [Finset.card_sigma, Finset.card_sigma] at hcard
  calc
    _ = ∑ s ∈ Gᶜ.cliqueFinset (k + 1), s.card := hcard
    _ = ∑ _s ∈ Gᶜ.cliqueFinset (k + 1), (k + 1) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact (SimpleGraph.mem_cliqueFinset_iff.mp hs).2
    _ = (k + 1) * indepCount G (k + 1) := by simp [indepCount, Nat.mul_comm]

/-- If every vertex has degree at most `Δ`, the independent-set counts satisfy
this subtraction-free extension-incidence inequality, including all boundary sizes. -/
theorem indepCount_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ k : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) :
    Fintype.card V * indepCount G k ≤
      (k + 1) * indepCount G (k + 1) + ((Δ + 1) * k) * indepCount G k := by
  classical
  have hsum := Finset.sum_le_sum (s := Gᶜ.cliqueFinset k)
    (fun s hs => extension_bound G Δ hdeg s
      (SimpleGraph.mem_cliqueFinset_iff.mp hs).1)
  have hsize : (∑ s ∈ Gᶜ.cliqueFinset k, (Δ + 1) * s.card) =
      ((Δ + 1) * k) * indepCount G k := by
    calc
      _ = ∑ _s ∈ Gᶜ.cliqueFinset k, (Δ + 1) * k := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [(SimpleGraph.mem_cliqueFinset_iff.mp hs).2]
      _ = _ := by simp [indepCount, Nat.mul_comm]
  rw [Finset.sum_add_distrib, hsize, extension_sum G k] at hsum
  simpa [indepCount, Nat.mul_comm] using hsum

/-- The independent-set sequence is nondecreasing at each size for which
`(Δ + 2) * k + 1` does not exceed the number of vertices. -/
theorem indepCount_le_succ_of_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ k : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hk : (Δ + 2) * k + 1 ≤ Fintype.card V) :
    indepCount G k ≤ indepCount G (k + 1) := by
  have hmain := indepCount_degree_bound G Δ k hdeg
  have hmul := Nat.mul_le_mul_right (indepCount G k) hk
  have hcancel : (k + 1) * indepCount G k + ((Δ + 1) * k) * indepCount G k ≤
      (k + 1) * indepCount G (k + 1) + ((Δ + 1) * k) * indepCount G k := by
    calc
      _ = ((Δ + 2) * k + 1) * indepCount G k := by ring
      _ ≤ Fintype.card V * indepCount G k := hmul
      _ ≤ _ := hmain
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hcancel) (by omega)

/-- Below `card V / (Δ + 2)`, each next independent-set count is at least
the preceding one. The denominator is positive for every natural `Δ`. -/
theorem indepCount_le_succ_of_lt_card_div {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ k : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hk : k < Fintype.card V / (Δ + 2)) :
    indepCount G k ≤ indepCount G (k + 1) := by
  apply indepCount_le_succ_of_degree_bound G Δ k hdeg
  have hmul : (Δ + 2) * (k + 1) ≤ Fintype.card V :=
    (Nat.mul_le_mul_left (Δ + 2) (Nat.succ_le_of_lt hk)).trans
      (Nat.mul_div_le _ _)
  calc
    (Δ + 2) * k + 1 ≤ (Δ + 2) * k + (Δ + 2) := by omega
    _ = (Δ + 2) * (k + 1) := by ring
    _ ≤ Fintype.card V := hmul

/-- The independent-set counts are nondecreasing on the initial segment ending
at `card V / (Δ + 2)`, under a uniform upper bound `Δ` on degrees. -/
theorem indepCount_mono_initial_of_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ Fintype.card V / (Δ + 2)) :
    indepCount G i ≤ indepCount G j := by
  have hmono : ∀ t, i ≤ t → t ≤ Fintype.card V / (Δ + 2) →
      indepCount G i ≤ indepCount G t := by
    intro t hit
    induction t, hit using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ t hit iht =>
      intro ht
      exact (iht (by omega)).trans
        (indepCount_le_succ_of_lt_card_div G Δ t hdeg (by omega))
  exact hmono j hij hj

example : (∀ v : Fin 4, (⊥ : SimpleGraph (Fin 4)).degree v ≤ 0) ∧
    (0 + 2) * 1 + 1 ≤ Fintype.card (Fin 4) := by
  constructor
  · intro v
    simp
  · decide

example : indepCount (⊥ : SimpleGraph (Fin 4)) 1 ≤
    indepCount (⊥ : SimpleGraph (Fin 4)) 2 :=
  indepCount_le_succ_of_degree_bound _ 0 1 (by intro v; simp) (by decide)

example : indepCount (⊥ : SimpleGraph (Fin 0)) 0 = 1 ∧
    indepCount (⊥ : SimpleGraph (Fin 0)) 1 = 0 := by decide

example : indepCount (⊥ : SimpleGraph (Fin 3)) 4 = 0 ∧
    indepCount (⊥ : SimpleGraph (Fin 3)) 5 = 0 := by decide

end ErdosCandidates.E993
