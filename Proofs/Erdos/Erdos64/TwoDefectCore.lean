/-
Finite low-degree pruning for the reviewed bipartite two-defect repair.
This core theorem itself assumes neither bipartiteness nor connectedness.
Minimal surviving order replaces the forest/leaf-count argument: the low-count
invariant forbids order three, so deleting one leaf cannot exhaust the graph.
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace Erdos64.TwoDefectCore
open SimpleGraph
open scoped Classical

/-- The number of neighbors retained in a vertex finset, including for ambient vertices. -/
noncomputable def retainedDegree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (v : V) : ℕ := by
  classical
  exact (G.neighborFinset v ∩ s).card

/-- Retained degree is exactly the usual degree in the induced graph at surviving vertices. -/
theorem retainedDegree_eq_induce {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) [DecidableRel G.Adj] (v : (s : Set V)) :
    retainedDegree G s v = (G.induce (s : Set V)).degree v := by
  classical
  have h := map_neighborFinset_induce (G := G) (s := (s : Set V)) v
  convert (congrArg Finset.card h).symm using 1
  · simp only [retainedDegree]
    congr 1
    ext x
    simp
  · simp only [Finset.card_map, card_neighborFinset_eq_degree]
    congr 1
    exact Subsingleton.elim _ _

/-- The surviving vertices with at most two retained neighbors. -/
noncomputable def lowVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) : Finset V := by
  classical
  exact s.filter (fun v => retainedDegree G s v ≤ 2)

/-- Membership in the low-degree finset agrees with the standard induced degree condition. -/
theorem mem_lowVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) [DecidableRel G.Adj] (v : V) :
    v ∈ lowVertices G s ↔ ∃ h : v ∈ s,
      (G.induce (s : Set V)).degree ⟨v, h⟩ ≤ 2 := by
  classical
  simp only [lowVertices, Finset.mem_filter]
  constructor
  · rintro ⟨h, hd⟩
    exact ⟨h, (retainedDegree_eq_induce G s ⟨v,h⟩) ▸ hd⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, (retainedDegree_eq_induce G s ⟨v,h⟩).symm ▸ hd⟩

private theorem retainedDegree_erase {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (z v : V) :
    retainedDegree G (s.erase z) v = retainedDegree G s v -
      (if G.Adj v z ∧ z ∈ s then 1 else 0) := by
  classical
  have hs : G.neighborFinset v ∩ s.erase z = (G.neighborFinset v ∩ s).erase z := by
    ext x
    simp [and_comm, and_assoc]
  simp only [retainedDegree, hs, Finset.card_erase_eq_ite, Finset.mem_inter,
    mem_neighborFinset]
  split_ifs <;> simp_all

/-- Deleting an isolated vertex or a leaf cannot increase the number of low-degree vertices. -/
theorem lowVertices_card_erase_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (z : V) (hz : z ∈ s) (hd : retainedDegree G s z ≤ 1) :
    (lowVertices G (s.erase z)).card ≤ (lowVertices G s).card := by
  classical
  let old := (lowVertices G s).erase z
  let fresh := lowVertices G (s.erase z) \ old
  have hzlow : z ∈ lowVertices G s := by
    simp only [lowVertices, Finset.mem_filter]
    exact ⟨hz, by omega⟩
  have hfresh : fresh ⊆ G.neighborFinset z ∩ s := by
    intro v hv
    obtain ⟨hvnew, hvold⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvs, hvdeg⟩ := Finset.mem_filter.mp hvnew
    obtain ⟨hvz, hvs⟩ := Finset.mem_erase.mp hvs
    have hnot : ¬ retainedDegree G s v ≤ 2 := by
      intro h
      exact hvold (Finset.mem_erase.mpr ⟨hvz, Finset.mem_filter.mpr ⟨hvs,h⟩⟩)
    have hformula := retainedDegree_erase G s z v
    have hadj : G.Adj v z := by
      by_contra hn
      simp only [hn, false_and, ↓reduceIte, Nat.sub_zero] at hformula
      exact hnot (hformula ▸ hvdeg)
    exact Finset.mem_inter.mpr ⟨by simpa using hadj.symm, hvs⟩
  have hfcard : fresh.card ≤ 1 :=
    (Finset.card_le_card hfresh).trans hd
  have hsub : lowVertices G (s.erase z) ⊆ old ∪ fresh := by
    intro v hv
    by_cases ho : v ∈ old
    · exact Finset.mem_union_left _ ho
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,ho⟩)
  have hbound := (Finset.card_le_card hsub).trans (Finset.card_union_le old fresh)
  have hocard : old.card = (lowVertices G s).card - 1 :=
    Finset.card_erase_of_mem hzlow
  have hpos := Finset.card_pos.mpr ⟨z,hzlow⟩
  omega

private theorem retainedDegree_lt_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (v : V) (hv : v ∈ s) : retainedDegree G s v < s.card := by
  classical
  have hsub : G.neighborFinset v ∩ s ⊆ s.erase v := by
    intro x hx
    obtain ⟨hn, hs⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_erase.mpr ⟨(G.mem_neighborFinset v x |>.mp hn).ne.symm, hs⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at hc
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  unfold retainedDegree
  omega

/-- A finite simple graph with at most two low-degree vertices and a vertex of degree
at least three has a surviving induced core of order at least four, minimum degree two,
and at most two low-degree vertices. No connectivity or bipartiteness is assumed. -/
theorem exists_induced_core {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hlow : (lowVertices G Finset.univ).card ≤ 2)
    (hhigh : ∃ v, 3 ≤ G.degree v) :
    ∃ s : Finset V, 4 ≤ s.card ∧ s.card ≤ Fintype.card V ∧
      (∀ v : (s : Set V), 2 ≤ (G.induce (s : Set V)).degree v) ∧
      (lowVertices G s).card ≤ 2 := by
  classical
  let candidates := Finset.univ.powerset.filter (fun s : Finset V =>
    3 ≤ s.card ∧ (lowVertices G s).card ≤ 2)
  have huniv : Finset.univ ∈ candidates := by
    obtain ⟨v, hv⟩ := hhigh
    have hcard := G.degree_lt_card_verts v
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset, Finset.card_univ]
    exact ⟨Finset.subset_univ _, by omega, hlow⟩
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨_, huniv⟩
  obtain ⟨hs3, hslow⟩ := (Finset.mem_filter.mp hs).2
  have hs4 : 4 ≤ s.card := by
    by_contra hn
    have hsEq : s.card = 3 := by omega
    have hall : lowVertices G s = s := by
      ext v
      simp only [lowVertices, Finset.mem_filter, and_iff_left_iff_imp]
      intro hv
      have hd := retainedDegree_lt_card G s v hv
      omega
    rw [hall, hsEq] at hslow
    omega
  have hdeg : ∀ v ∈ s, 2 ≤ retainedDegree G s v := by
    intro z hz
    by_contra hn
    have hz1 : retainedDegree G s z ≤ 1 := by omega
    have hlow' := (lowVertices_card_erase_le G s z hz hz1).trans hslow
    have hcard' : (s.erase z).card = s.card - 1 := Finset.card_erase_of_mem hz
    have hmem : s.erase z ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, by omega, hlow'⟩
    have hminimal := hmin (s.erase z) hmem
    omega
  refine ⟨s, hs4, Finset.card_le_univ s, ?_, hslow⟩
  intro v
  rw [← retainedDegree_eq_induce G s v]
  exact hdeg v v.property

/-- With every vertex retained, retained degree is the usual ambient degree. -/
theorem retainedDegree_univ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : retainedDegree G Finset.univ v = G.degree v := by
  classical
  unfold retainedDegree
  simp only [Finset.inter_univ, degree]
  congr 1
  ext x
  simp

/-- The ambient low-degree finset uses the ordinary graph degree. -/
theorem lowVertices_univ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    lowVertices G Finset.univ = Finset.univ.filter (fun v => G.degree v ≤ 2) := by
  classical
  ext v
  simp only [lowVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    retainedDegree_univ]

/-- The low-degree count in an induced graph equals the ambient surviving low-degree count. -/
theorem lowVertices_card_eq_induce {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (s : Finset V) :
    (lowVertices G s).card =
      (Finset.univ.filter (fun v : (s : Set V) =>
        (G.induce (s : Set V)).degree v ≤ 2)).card := by
  classical
  let f : (s : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (Finset.univ.filter (fun v : (s : Set V) =>
        (G.induce (s : Set V)).degree v ≤ 2)).map f = lowVertices G s := by
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_lowVertices]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
    · rintro ⟨h, hd⟩
      exact ⟨⟨v,h⟩, hd, rfl⟩
  simpa only [Finset.card_map] using (congrArg Finset.card hmap).symm

/-- Standard-degree interface to the core theorem: the surviving subtype is explicitly
nonempty, has order at most the original, minimum degree two, and at most two low vertices. -/
theorem exists_induced_core_of_low_degree_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlow : (Finset.univ.filter (fun v => G.degree v ≤ 2)).card ≤ 2)
    (hhigh : ∃ v, 3 ≤ G.degree v) :
    ∃ s : Finset V, Nonempty (s : Set V) ∧
      Fintype.card (s : Set V) ≤ Fintype.card V ∧
      (∀ v : (s : Set V), 2 ≤ (G.induce (s : Set V)).degree v) ∧
      (Finset.univ.filter (fun v : (s : Set V) =>
        (G.induce (s : Set V)).degree v ≤ 2)).card ≤ 2 := by
  classical
  have hl : (lowVertices G Finset.univ).card ≤ 2 := by
    rwa [lowVertices_univ]
  obtain ⟨s, hs4, hscard, hd, hl⟩ := exists_induced_core G hl hhigh
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hsne
  refine ⟨s, ⟨⟨v,hv⟩⟩, ?_, hd, ?_⟩
  · simpa using hscard
  · rwa [← lowVertices_card_eq_induce]

/-- Every genuine cycle of an induced core lifts to a genuine ambient cycle of the same
exact length. This applies to all lengths, not merely even or dyadic lengths. -/
theorem cycle_induce_transport {V : Type*} (G : SimpleGraph V) (s : Set V) {n : ℕ}
    (h : ∃ x, ∃ p : (G.induce s).Walk x x, p.IsCycle ∧ p.length = n) :
    ∃ x, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = n := by
  obtain ⟨x, p, hp, hlen⟩ := h
  let f : G.induce s →g G := ⟨Subtype.val, fun {_ _} hab => induce_adj.mp hab⟩
  exact ⟨x.val, p.map f, hp.map Subtype.val_injective, by
    rw [Walk.length_map, hlen]⟩

/-- A six-vertex test graph: a complete four-vertex graph, an isolated vertex,
and a leaf attached to vertex zero. -/
private def fixture : SimpleGraph (Fin 6) where
  Adj x y := x ≠ y ∧ (x.val < 4 ∧ y.val < 4 ∨ x = 0 ∧ y = 5 ∨ x = 5 ∧ y = 0)
  symm := ⟨by
    intro x y h
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2,h.1⟩)⟩
  loopless := ⟨by intro x; simp⟩

private theorem fixture_degree (v : Fin 6) : fixture.degree v =
    if v = 4 then 0 else if v = 5 then 1 else if v = 0 then 4 else 3 := by
  classical
  have hn : fixture.neighborFinset v = Finset.univ.filter (fun w => fixture.Adj v w) := by
    ext w
    simp
  have hu : (Finset.univ : Finset (Fin 6)) = {0,1,2,3,4,5} := by decide
  rw [degree, hn, hu]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  fin_cases v <;>
    simp [fixture, Fin.ext_iff, -Fin.val_eq_zero_iff]

example : (lowVertices fixture Finset.univ).card = 2 ∧
    fixture.degree 4 = 0 ∧ fixture.degree 5 = 1 ∧ 3 ≤ fixture.degree 0 := by
  classical
  have hset : lowVertices fixture Finset.univ = {4,5} := by
    ext v
    simp only [lowVertices_univ, Finset.mem_filter, Finset.mem_univ, true_and,
      fixture_degree, Finset.mem_insert, Finset.mem_singleton]
    fin_cases v <;> simp [Fin.ext_iff, -Fin.val_eq_zero_iff]
  rw [hset]
  simp [fixture_degree, Fin.ext_iff, -Fin.val_eq_zero_iff]

end Erdos64.TwoDefectCore
