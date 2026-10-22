/-
Erdős–Gyárfás problem 64 — the minimal-counterexample reductions.

PROVENANCE. The reduction layer of arXiv:2609.28594, Lemma 3.2, the minimal
counterexample analysis used in the proof of Theorem 3.7. Graphs are finite,
undirected and simple. `Erdos64.IsMinimalCounterexample` (see `Basic.lean`) is
lexicographic minimality of `(number of vertices, number of edges)` among
`Erdos64.IsCounterexample`s, over all finite vertex types in the same universe;
nothing else is assumed, in particular no connectedness and no conclusion
below is folded into the definition.

WHAT IS PROVED HERE (all consequences of minimality, with hypotheses explicit).

1. Cycle transport.  A power-of-two cycle survives passing to a supergraph, so
   deleting vertices/edges cannot create one:
   `hasPowerOfTwoCycle_of_le`, `not_hasPowerOfTwoCycle_of_le`,
   `hasPowerOfTwoCycle_induce`/`not_hasPowerOfTwoCycle_induce`,
   `hasPowerOfTwoCycle_deleteEdges`/`not_hasPowerOfTwoCycle_deleteEdges`.
   The transport is proved by mapping the walk along the inclusion homomorphism
   (`SimpleGraph.Walk.map` along `SimpleGraph.Hom`, using
   `SimpleGraph.Walk.IsCycle.map` with injectivity of the inclusion), never
   assumed.

2. `false_of_adjacent_degreeGeFour`: two adjacent high-degree vertices (degree
   at least 4) are impossible.  Deleting the edge between them keeps the minimum
   degree at least 3 and keeps the graph a counterexample with strictly fewer
   edges, contradicting minimality.

3. `false_of_forall_neighbor_degreeGeFour` and `exists_adjacent_degreeThree`:
   every vertex has a neighbour of degree exactly three.  Deleting a vertex all
   of whose neighbours are high-degree leaves a smaller counterexample on the
   induced vertex type `↥({v}ᶜ : Set V)`, contradicting minimality.

4. `degreeThree_of_adj_degreeGeFour`: every neighbour of a high-degree vertex
   has degree exactly three (immediate from 2 and the minimum degree bound).

5. `card_highDegreeNeighbors_le_two`: a vertex of degree three has at most two
   high-degree neighbours.

6. `eq_of_le_of_minDegree_three` (same vertex type) and
   `not_card_lt_of_minDegree_three_induce` / `eq_univ_of_minDegree_three_induce`
   (induced subgraphs): there is no strictly smaller subgraph or induced
   subgraph with minimum degree at least three.

Degree bookkeeping is proved from `Finset` computations on `G.neighborFinset`
(`neighborFinset_deleteEdges_singleton`, `degree_deleteEdges_singleton`,
`degree_induce_compl_singleton`), so the numerical hypotheses of the
lexicographic arguments are exact.
-/

import Erdos.Erdos64.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### 1. Transport of power-of-two cycles -/

/-- A power-of-two cycle of a subgraph is a power-of-two cycle of the ambient graph: the walk is
mapped along the inclusion homomorphism, which is injective. -/
theorem hasPowerOfTwoCycle_of_le {H G : SimpleGraph V} (hle : H ≤ G)
    (hcyc : HasPowerOfTwoCycle H) : HasPowerOfTwoCycle G := by
  obtain ⟨k, hk, v, c, hc, hlen⟩ := hcyc
  refine ⟨k, hk, (SimpleGraph.Hom.ofLE hle) v, c.map (SimpleGraph.Hom.ofLE hle), hc.map ?_, ?_⟩
  · intro a b hab
    simpa [SimpleGraph.Hom.ofLE_apply] using hab
  · rw [SimpleGraph.Walk.length_map, hlen]

/-- Contrapositive of `hasPowerOfTwoCycle_of_le`: a supergraph of a graph without a power-of-two
cycle has none either. In particular deleting edges cannot create a forbidden cycle. -/
theorem not_hasPowerOfTwoCycle_of_le {H G : SimpleGraph V} (hle : H ≤ G)
    (hG : ¬ HasPowerOfTwoCycle G) : ¬ HasPowerOfTwoCycle H :=
  fun hcyc => hG (hasPowerOfTwoCycle_of_le hle hcyc)

/-- A power-of-two cycle of an induced subgraph is a power-of-two cycle of the ambient graph. -/
theorem hasPowerOfTwoCycle_induce (G : SimpleGraph V) (s : Set V)
    (hcyc : HasPowerOfTwoCycle (G.induce s)) : HasPowerOfTwoCycle G := by
  obtain ⟨k, hk, v, c, hc, hlen⟩ := hcyc
  let f : G.induce s →g G := ⟨Subtype.val, fun {_ _} hab => SimpleGraph.induce_adj.mp hab⟩
  exact ⟨k, hk, (v : V), c.map f, hc.map Subtype.val_injective, by
    rw [SimpleGraph.Walk.length_map, hlen]⟩

/-- Deleting vertices cannot create a forbidden cycle. -/
theorem not_hasPowerOfTwoCycle_induce (G : SimpleGraph V) (s : Set V)
    (hG : ¬ HasPowerOfTwoCycle G) : ¬ HasPowerOfTwoCycle (G.induce s) :=
  fun hcyc => hG (hasPowerOfTwoCycle_induce G s hcyc)

/-- A power-of-two cycle of an edge-deleted graph is a power-of-two cycle of the original graph. -/
theorem hasPowerOfTwoCycle_deleteEdges (G : SimpleGraph V) (s : Set (Sym2 V))
    (hcyc : HasPowerOfTwoCycle (G.deleteEdges s)) : HasPowerOfTwoCycle G :=
  hasPowerOfTwoCycle_of_le (deleteEdges_le s) hcyc

/-- Deleting edges cannot create a forbidden cycle. -/
theorem not_hasPowerOfTwoCycle_deleteEdges (G : SimpleGraph V) (s : Set (Sym2 V))
    (hG : ¬ HasPowerOfTwoCycle G) : ¬ HasPowerOfTwoCycle (G.deleteEdges s) :=
  fun hcyc => hG (hasPowerOfTwoCycle_deleteEdges G s hcyc)

/-! ### 2. Degree bookkeeping -/

/-- The complement of a singleton has one vertex fewer. -/
theorem card_compl_singleton [Fintype V] [DecidableEq V] (v : V) :
    Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := by
  rw [← Set.toFinset_card, Set.toFinset_compl, Set.toFinset_singleton, Finset.compl_singleton,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

/-- The degree of a vertex in the induced subgraph on the complement of a singleton: only the
edge to the deleted vertex is lost. -/
theorem degree_induce_compl_singleton (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) (x : ↥({v}ᶜ : Set V)) :
    (G.induce {v}ᶜ).degree x = G.degree (x : V) - (if G.Adj (x : V) v then 1 else 0) := by
  have hmap := map_neighborFinset_induce (G := G) (s := {v}ᶜ) x
  have hset : G.neighborFinset (x : V) ∩ ({v}ᶜ : Set V).toFinset
      = (G.neighborFinset (x : V)).erase v := by
    ext y
    simp [Finset.mem_erase, and_comm]
  rw [← card_neighborFinset_eq_degree, ← Finset.card_map, hmap, hset, Finset.card_erase_eq_ite]
  by_cases h : G.Adj (x : V) v <;> simp [h]

/-- The neighbours of `w` in the graph obtained by deleting the single edge `{u, v}` are the
neighbours of `w` in `G`, minus the other endpoint of the deleted edge when `w` is an endpoint. -/
theorem neighborFinset_deleteEdges_singleton (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (u v w : V) :
    (G.deleteEdges {s(u, v)}).neighborFinset w
      = (G.neighborFinset w).filter (fun x => ¬(w = u ∧ x = v ∨ w = v ∧ x = u)) := by
  rw [neighborFinset_eq_filter, neighborFinset_eq_filter]
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [deleteEdges_adj]
  constructor
  · rintro ⟨h, hmem⟩
    exact ⟨h, fun hc => hmem (by rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)⟩
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hmem => hne (by simpa using hmem)⟩

/-- Deleting a single edge lowers the degree of one endpoint by exactly one. -/
theorem degree_deleteEdges_adj_left (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).degree u = G.degree u - 1 := by
  have huv_ne : u ≠ v := huv.ne
  have hset : (G.neighborFinset u).filter (fun x => ¬(u = u ∧ x = v ∨ u = v ∧ x = u))
      = (G.neighborFinset u).erase v := by
    ext x
    simp [Finset.mem_erase, huv_ne, and_comm]
  rw [SimpleGraph.degree, neighborFinset_deleteEdges_singleton, hset,
    Finset.card_erase_of_mem (by simpa using huv), card_neighborFinset_eq_degree]

/-- Deleting a single edge lowers the degree of the other endpoint by exactly one. -/
theorem degree_deleteEdges_adj_right (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).degree v = G.degree v - 1 := by
  have huv_ne : u ≠ v := huv.ne
  have hset : (G.neighborFinset v).filter (fun x => ¬(v = u ∧ x = v ∨ v = v ∧ x = u))
      = (G.neighborFinset v).erase u := by
    ext x
    simp [Finset.mem_erase, huv_ne.symm, and_comm]
  rw [SimpleGraph.degree, neighborFinset_deleteEdges_singleton, hset,
    Finset.card_erase_of_mem (by simpa using huv.symm), card_neighborFinset_eq_degree]

/-- Deleting a single edge does not change the degree of a non-endpoint. -/
theorem degree_deleteEdges_of_ne (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    (G.deleteEdges {s(u, v)}).degree w = G.degree w := by
  have hset : (G.neighborFinset w).filter (fun x => ¬(w = u ∧ x = v ∨ w = v ∧ x = u))
      = G.neighborFinset w := by
    ext x
    simp [hwu, hwv]
  rw [SimpleGraph.degree, neighborFinset_deleteEdges_singleton, hset,
    card_neighborFinset_eq_degree]

/-- The degree in the graph obtained by deleting a single edge. -/
theorem degree_deleteEdges_singleton (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) (w : V) :
    (G.deleteEdges {s(u, v)}).degree w
      = G.degree w - (if w = u ∨ w = v then 1 else 0) := by
  by_cases hwu : w = u
  · rw [hwu, if_pos (Or.inl rfl)]
    exact degree_deleteEdges_adj_left G huv
  · by_cases hwv : w = v
    · rw [hwv, if_pos (Or.inr rfl)]
      exact degree_deleteEdges_adj_right G huv
    · rw [if_neg (fun hc => hc.elim hwu hwv)]
      exact degree_deleteEdges_of_ne G hwu hwv

/-- Deleting an edge strictly decreases the number of edges. -/
theorem card_edgeFinset_deleteEdges_singleton_lt (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).edgeFinset.card < G.edgeFinset.card := by
  have hne : G.deleteEdges {s(u, v)} ≠ G := by
    intro hEq
    have hmem : s(u, v) ∈ (G.deleteEdges {s(u, v)}).edgeSet := by
      rw [hEq]
      exact (mem_edgeSet G).mpr huv
    rw [edgeSet_deleteEdges] at hmem
    exact hmem.2 (Set.mem_singleton _)
  have hlt : G.deleteEdges {s(u, v)} < G := lt_of_le_of_ne (deleteEdges_le _) hne
  exact Finset.card_lt_card (edgeFinset_ssubset_edgeFinset.mpr hlt)

/-! ### 3. Lexicographic size comparisons -/

/-- On a fixed vertex type, strictly fewer edges means a strictly smaller lexicographic size. -/
theorem lexLt_size_of_card_edgeFinset_lt {H G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel H.Adj] [DecidableRel G.Adj] (h : H.edgeFinset.card < G.edgeFinset.card) :
    LexLt (size H) (size G) := by
  refine Or.inr ⟨by simp [size], ?_⟩
  simpa [size] using h

/-- Strictly fewer vertices means a strictly smaller lexicographic size, on any vertex type. -/
theorem lexLt_size_of_card_verts_lt {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : Fintype.card W < Fintype.card V) : LexLt (size H) (size G) :=
  Or.inl (by simpa [size] using h)

/-! ### 4. Transport of the counterexample property -/

/-- A subgraph with minimum degree at least three, inside a counterexample, is again a
counterexample: it inherits the vertex type, its minimum degree is assumed, and deleting edges
cannot create a forbidden cycle. -/
theorem IsCounterexample.of_le_of_degree {H G : SimpleGraph V} [Fintype V] [DecidableRel H.Adj]
    [DecidableRel G.Adj] (hle : H ≤ G) (hG : IsCounterexample G)
    (hdeg : ∀ v : V, 3 ≤ H.degree v) : IsCounterexample H :=
  ⟨hG.1, hdeg, not_hasPowerOfTwoCycle_of_le hle hG.2.2⟩

/-- An induced subgraph with minimum degree at least three, inside a counterexample, is again a
counterexample. Nonemptiness is required explicitly: the vertex-wise degree condition is vacuous
on an empty vertex set. -/
theorem IsCounterexample.of_induce {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hG : IsCounterexample G) (s : Set V) [Fintype s] [DecidablePred (· ∈ s)]
    (hdeg : ∀ v : s, 3 ≤ (G.induce s).degree v) (hne : Nonempty s) :
    IsCounterexample (G.induce s) :=
  ⟨hne, hdeg, not_hasPowerOfTwoCycle_induce G s hG.2.2⟩

/-- An edge-deleted graph with minimum degree at least three, inside a counterexample, is again a
counterexample. -/
theorem IsCounterexample.of_deleteEdges {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : IsCounterexample G) (s : Set (Sym2 V)) [DecidablePred (· ∈ s)]
    (hdeg : ∀ w : V, 3 ≤ (G.deleteEdges s).degree w) : IsCounterexample (G.deleteEdges s) :=
  ⟨hG.1, hdeg, not_hasPowerOfTwoCycle_deleteEdges G s hG.2.2⟩

/-! ### 5. The reductions -/

/-- **Reduction (2).** No two high-degree vertices are adjacent in a minimal counterexample.

If `u ~ v` and both have degree at least `4`, deleting the edge `uv` leaves every degree at least
`3` (`degree_deleteEdges_singleton`), keeps the graph free of power-of-two cycles
(`not_hasPowerOfTwoCycle_deleteEdges`), and strictly decreases the number of edges while keeping
the vertex type, contradicting lexicographic minimality. -/
theorem false_of_adjacent_degreeGeFour {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) {u v : V} (huv : G.Adj u v)
    (hu : degreeGeFour G u) (hv : degreeGeFour G v) : False := by
  have hdeg : ∀ w : V, 3 ≤ (G.deleteEdges {s(u, v)}).degree w := by
    intro w
    rw [degree_deleteEdges_singleton G huv w]
    by_cases hw : w = u ∨ w = v
    · rw [if_pos hw]
      have h4 : 4 ≤ G.degree w := by
        rcases hw with hwu | hwv
        · rw [hwu]
          exact hu
        · rw [hwv]
          exact hv
      omega
    · rw [if_neg hw]
      exact hmin.degree_ge_three w
  exact hmin.false_of_size_lexLt (G.deleteEdges {s(u, v)})
    (IsCounterexample.of_deleteEdges hmin.1 {s(u, v)} hdeg)
    (lexLt_size_of_card_edgeFinset_lt (card_edgeFinset_deleteEdges_singleton_lt G huv))

/-- **Reduction (3), key step.** A vertex all of whose neighbours are high-degree is impossible in
a minimal counterexample.

Deleting such a vertex leaves a graph on the induced vertex type `↥({v}ᶜ : Set V)` in which every
remaining degree is at least `3` (each neighbour loses at most the edge to `v`, and it had degree
at least `4`; non-neighbours lose nothing), still free of power-of-two cycles
(`not_hasPowerOfTwoCycle_induce`), with strictly fewer vertices. This contradicts minimality. -/
theorem false_of_forall_neighbor_degreeGeFour {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) {v : V}
    (hv : ∀ w : V, G.Adj v w → degreeGeFour G w) : False := by
  have hne : Nonempty ↥({v}ᶜ : Set V) := by
    have hcard : 1 < Fintype.card V := by
      have := hmin.card_verts_ge_four
      omega
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hcard v
    exact ⟨⟨w, by simpa using hw⟩⟩
  have hdeg : ∀ x : ↥({v}ᶜ : Set V), 3 ≤ (G.induce {v}ᶜ).degree x := by
    intro x
    rw [degree_induce_compl_singleton G v x]
    by_cases hx : G.Adj (x : V) v
    · rw [if_pos hx]
      have h4 : 4 ≤ G.degree (x : V) := hv (x : V) hx.symm
      omega
    · rw [if_neg hx]
      exact hmin.degree_ge_three (x : V)
  refine hmin.false_of_size_lexLt (G.induce {v}ᶜ)
    (IsCounterexample.of_induce hmin.1 {v}ᶜ hdeg hne) ?_
  refine lexLt_size_of_card_verts_lt (G.induce {v}ᶜ) ?_
  rw [card_compl_singleton v]
  have := hmin.card_verts_ge_four
  omega

/-- **Reduction (3).** Every vertex of a minimal counterexample has a neighbour of degree exactly
three. If no neighbour had degree three, every neighbour would be high-degree (degrees are at
least three), contradicting `false_of_forall_neighbor_degreeGeFour`. -/
theorem exists_adjacent_degreeThree {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) (v : V) :
    ∃ w : V, G.Adj v w ∧ degreeThree G w := by
  by_contra h
  refine false_of_forall_neighbor_degreeGeFour (v := v) hmin fun w hw => ?_
  by_contra h4
  exact h ⟨w, hw, degreeThree_of_three_le_of_not_degreeGeFour G (hmin.degree_ge_three w) h4⟩

/-- **Reduction (4).** Every neighbour of a high-degree vertex has degree exactly three. -/
theorem degreeThree_of_adj_degreeGeFour {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) {v w : V} (hvw : G.Adj v w)
    (hv : degreeGeFour G v) : degreeThree G w := by
  by_contra h3
  exact false_of_adjacent_degreeGeFour hmin hvw hv
    (degreeGeFour_of_three_le_of_not_degreeThree G (hmin.degree_ge_three w) h3)

/-- **Reduction (5).** A vertex of degree three has at most two high-degree neighbours.

If it had three, then since it has exactly three neighbours in total, every neighbour would be
high-degree, contradicting `false_of_forall_neighbor_degreeGeFour`. -/
theorem card_highDegreeNeighbors_le_two {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) {v : V} (hv : degreeThree G v) :
    (highDegreeNeighbors G v).card ≤ 2 := by
  have hdeg : G.degree v = 3 := hv
  have hsub := highDegreeNeighbors_subset_neighborFinset G v
  have hcard_neighbor : (G.neighborFinset v).card = 3 := by
    rw [card_neighborFinset_eq_degree]
    exact hdeg
  by_contra h
  rw [not_le] at h
  have hcard : (highDegreeNeighbors G v).card = (G.neighborFinset v).card := by
    refine le_antisymm (Finset.card_le_card hsub) ?_
    omega
  have heq : highDegreeNeighbors G v = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  refine false_of_forall_neighbor_degreeGeFour (v := v) hmin fun w hw => ?_
  have hw' : w ∈ highDegreeNeighbors G v := by
    rw [heq]
    simpa using hw
  exact (mem_highDegreeNeighbors.mp hw').1

/-- **Reduction (6), subgraph form.** No proper subgraph on the same vertex type has minimum
degree at least three: such a subgraph would be a counterexample with strictly fewer edges. -/
theorem eq_of_le_of_minDegree_three {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) {H : SimpleGraph V}
    [DecidableRel H.Adj] (hle : H ≤ G) (hdeg : ∀ v : V, 3 ≤ H.degree v) : H = G := by
  by_contra hne
  have hH : IsCounterexample H := IsCounterexample.of_le_of_degree hle hmin.1 hdeg
  have hlt : H.edgeFinset.card < G.edgeFinset.card :=
    Finset.card_lt_card (edgeFinset_ssubset_edgeFinset.mpr (lt_of_le_of_ne hle hne))
  exact hmin.false_of_size_lexLt H hH (lexLt_size_of_card_edgeFinset_lt hlt)

/-- **Reduction (6), induced form.** No induced subgraph on strictly fewer vertices has minimum
degree at least three. The hypothesis is the `minDegree` formulation, which is not vacuous on an
empty vertex set (unlike the vertex-wise degree condition). -/
theorem not_card_lt_of_minDegree_three_induce {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) (s : Set V) [Fintype s]
    [DecidablePred (· ∈ s)] (hdeg : 3 ≤ (G.induce s).minDegree) :
    ¬ Fintype.card s < Fintype.card V := by
  intro hlt
  have hne : Nonempty s := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    haveI : Subsingleton s := ⟨fun a _ => isEmptyElim a⟩
    rw [minDegree_of_subsingleton] at hdeg
    omega
  have hdeg' : ∀ v : s, 3 ≤ (G.induce s).degree v := fun v =>
    hdeg.trans (minDegree_le_degree (G.induce s) v)
  exact hmin.false_of_size_lexLt (G.induce s)
    (IsCounterexample.of_induce hmin.1 s hdeg' hne) (lexLt_size_of_card_verts_lt (G.induce s) hlt)

/-- **Reduction (6), induced form, vertex-set version.** If the induced subgraph on a vertex set
has minimum degree at least three, the vertex set is everything. -/
theorem eq_univ_of_minDegree_three_induce {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) (s : Set V) [Fintype s]
    [DecidablePred (· ∈ s)] (hdeg : 3 ≤ (G.induce s).minDegree) : s = Set.univ := by
  have hcard : Fintype.card s = Fintype.card V := by
    have h := not_card_lt_of_minDegree_three_induce hmin s hdeg
    have hle : Fintype.card s ≤ Fintype.card V := Fintype.card_subtype_le _
    omega
  have hfinset : s.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Set.toFinset_card]
    exact hcard
  have hcoe : ((s.toFinset : Finset V) : Set V) = s := Set.coe_toFinset s
  rw [← hcoe, hfinset]
  simp

end Erdos64
