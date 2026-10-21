/-
  Erdős Problem #916 — a cycle plus a vertex with three neighbours on it.
  Status: proved (Thomassen 1974).  Tier A proof target.

  Verbatim statement (`goof erdos fetch 916`, pulled 2026-08-05):

    "Does every graph with $n$ vertices and $2n-2$ edges contain a cycle
    and another vertex adjacent to three vertices on the cycle?"

  DB remarks: a stronger form of Dirac's theorem [Di60] that every such
  graph contains a subdivision of K₄.  Answer YES, proved by Thomassen
  [Th74] (~5-page direct argument, "A minimal condition implying a
  special K₄-subdivision in a graph").

  Mathlib inventory (leandoc 2026-08-05):
  * `SimpleGraph.Walk.IsCycle` (structure, Paths.lean) — cycles as
    closed walks with distinct internal vertices;
  * `SimpleGraph.edgeFinset` with `card` for the edge count;
  * `Walk.support` (List V) for "vertices on the cycle";
  * neighbourhood filtering via `G.Adj`.
  No off-the-shelf lemma; all primitives exist.  Medium risk of
  Walk-API friction (flagged by the candidates audit).
  Repo adjacency: `Proofs/Erdos/Erdos715/RegularSubgraph.lean` (graph
  edge-counting experience).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E916

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `HasCycleWithTripleAttachment G`: `G` contains a cycle `c` and a
    vertex `v` not on `c` adjacent to at least three vertices of `c`.
    "Vertices on the cycle" = `c.support`; adjacency counted over the
    de-duplicated support. -/
def HasCycleWithTripleAttachment (G : SimpleGraph V) [DecidableRel G.Adj] :
    Prop :=
  ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧
    ∃ v : V, v ∉ c.support ∧
      3 ≤ (c.support.toFinset.filter (fun u => G.Adj v u)).card

/-- Satisfiability at a concrete model: `K₄` (complete graph on 4
    vertices, 6 = 2·4 − 2 edges) has a triangle and the fourth vertex is
    adjacent to all three of its vertices.
    -- PROVABLE (explicit walk + decide). -/
example : HasCycleWithTripleAttachment (⊤ : SimpleGraph (Fin 4)) := by
  let c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0 :=
    .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 0 1)
      (.cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 1 2)
        (.cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 2 0) .nil))
  refine ⟨0, c, ?_, 3, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff, Walk.isPath_def]
    decide
  · decide
  · decide

/-- **Erdős #916, Thomassen's theorem** (Th74): every graph on `n`
    vertices with at least `2n − 2` edges contains a cycle together with
    a vertex off the cycle adjacent to three of its vertices.

    Source text: "Does every graph with $n$ vertices and $2n-2$ edges
    contain a cycle and another vertex adjacent to three vertices on the
    cycle?"  Answer yes (Thomassen 1974).

    Formalization notes:
    * Edge hypothesis stated as `2 * n ≤ G.edgeFinset.card + 2` to avoid
      ℕ-subtraction junk at small `n` (per STYLE.md); for `n ≥ 2` this is
      exactly `#edges ≥ 2n − 2`.
    * `n = Fintype.card V`; single cardinality API (`Finset.card`) used
      throughout.
    * Sanity floor: a graph needs ≥ 4 vertices for the conclusion to be
      satisfiable (cycle ≥ 3 vertices + 1 external vertex); for n ≤ 3
      the hypothesis `#edges ≥ 2n−2` already exceeds `C(n,2)` (n=3:
      4 > 3 ✓, n=2: 2 > 1 ✓, n=1: 0 = 0 — n=1 has 0 ≥ 0 edges and the
      claim would be FALSE, hence the guard `2 ≤ n`... n=1: 2·1 ≤ e+2
      means e ≥ 0, vacuous hypothesis satisfied by the empty graph which
      has no cycle.  The guard `4 ≤ n` below keeps the statement honest;
      the DB statement implicitly assumes n large enough.

    Proof sketch (attack plan): Thomassen's proof takes a minimal
    counterexample and analyses a longest path/cycle: pick a shortest
    cycle `C` in a graph of min degree ≥ 3 (after deleting low-degree
    vertices, preserving the edge bound: deleting a vertex of degree ≤ 2
    keeps `e ≥ 2n − 2`), then a vertex off `C` with three neighbours on
    `C` exists by counting.  The reduction "min degree ≥ 3 or delete"
    is the mechanizable core; the case analysis on chords is the 5-page
    part.  Mathlib tools: `SimpleGraph.deleteVerts`,
    `SimpleGraph.minDegree`, `Walk.IsCycle`, strong induction on
    `Fintype.card V`.  Effort M per candidates audit. -/
theorem thomassen_cycle_triple_attachment (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 4 ≤ Fintype.card V)
    (he : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    HasCycleWithTripleAttachment G := by
  sorry

/-- A graph all of whose edges pass through one vertex is acyclic. -/
private lemma isAcyclic_of_forall_adj {W : Type*} (H : SimpleGraph W) (z : W)
    (h : ∀ a b, H.Adj a b → a = z ∨ b = z) : H.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rw [isBridge_iff]
  rintro ⟨p⟩
  have hne : a ≠ b := hab.ne
  -- the endpoint of the deleted edge that is not `z` has no remaining edge
  have key : ∀ x : W, s(x, z) = s(a, b) → x ≠ z →
      (H.deleteEdges {s(a, b)}).Walk x z → False := by
    intro x hxz hx q
    cases q with
    | nil => exact hx rfl
    | @cons _ t _ hq _ =>
      rw [deleteEdges_adj, Set.mem_singleton_iff] at hq
      rcases h x t hq.1 with hx' | ht
      · exact hx hx'
      · exact hq.2 (ht ▸ hxz)
  rcases h a b hab with rfl | rfl
  · exact key b Sym2.eq_swap hne.symm p.reverse
  · exact key a rfl hne p

/-- The book graph `K₂ + 3K₁` on `Fin 5`: an edge is present exactly when
    its endpoints are distinct and at least one of them lies in `{0, 1}`. -/
private def book : SimpleGraph (Fin 5) where
  Adj a b := a ≠ b ∧ (a.val < 2 ∨ b.val < 2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in `book` is decidable. -/
private instance book.decAdj : DecidableRel book.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (a.val < 2 ∨ b.val < 2)))

/-- Sharpness sanity: `2n − 3` edges do not suffice.  Witness family:
    a theta-graph-free construction — e.g. the "book" `K_{2,n-2}` plus
    an edge... The DB records the bound as tight; the standard witness is
    a maximal series-parallel graph (`2n − 3` edges, no K₄-subdivision,
    hence no cycle-with-triple-attachment).  Concrete small case: some
    graph on 5 vertices with 7 edges and no cycle+triple-attachment.
    -- PROVABLE (native_decide over graphs on 5 vertices, or an explicit
    witness + decide).  Needs a probe to pick the witness. -/
theorem sharpness_five_vertices :
    ∃ G : SimpleGraph (Fin 5), ∃ _ : DecidableRel G.Adj,
      G.edgeFinset.card = 7 ∧ ¬ HasCycleWithTripleAttachment G := by
  refine ⟨book, book.decAdj, by decide, ?_⟩
  rintro ⟨w, c, hc, v, hv, hcard⟩
  by_cases hv2 : 2 ≤ v.val
  · have hsub : (c.support.toFinset.filter (fun u => book.Adj v u)).card ≤
        (univ.filter (fun u => book.Adj v u)).card :=
      card_le_card (filter_subset_filter _ (subset_univ _))
    have hdeg : ∀ x : Fin 5, 2 ≤ x.val →
        (univ.filter (fun u => book.Adj x u)).card ≤ 2 := by decide
    have hv_deg := hdeg v hv2
    omega
  · let z : Fin 5 := if v = 0 then 1 else 0
    let H : SimpleGraph (Fin 5) :=
      { Adj := fun a b => book.Adj a b ∧ a ≠ v ∧ b ≠ v
        symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
        loopless := ⟨fun _ h => h.1.1 rfl⟩ }
    have hz : ∀ a b, H.Adj a b → a = z ∨ b = z := by
      have hall : ∀ x : Fin 5, ¬ 2 ≤ x.val → ∀ a b : Fin 5, book.Adj a b → a ≠ x → b ≠ x →
          a = (if x = 0 then 1 else 0) ∨ b = (if x = 0 then 1 else 0) := by decide
      intro a b hab
      exact hall v hv2 a b hab.1 hab.2.1 hab.2.2
    have hq : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        have hab : book.Adj a b := c.edges_subset_edgeSet he
        have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges he
        have hb : b ∈ c.support := c.snd_mem_support_of_mem_edges he
        exact ⟨hab, ne_of_mem_of_not_mem ha hv, ne_of_mem_of_not_mem hb hv⟩
    exact isAcyclic_of_forall_adj H z hz (c.transfer H hq) (hc.transfer hq)

end ErdosCandidates.E916

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - DB statement matches file header verbatim.
   - Solver attribution Thomassen [Th74] matches DB.
   - Edge hypothesis `2 * n ≤ G.edgeFinset.card + 2` is the correct ℕ-subtraction-free rearrangement of `#edges ≥ 2n - 2`.
   - K₄ satisfiability: 6 = 2*4-2 edges, triangle + vertex adjacent to all 3. Correct.
   - Guard `4 ≤ Fintype.card V` is necessary: n=1 with 0 edges satisfies 2 ≤ 0+2 but has no cycle. The guard is conservative (2 ≤ n would suffice since n=2,3 are vacuous), but not a fidelity error.
   - FLAG (minor): `HasCycleWithTripleAttachment` uses `c.support.toFinset.filter (fun u => G.Adj v u)` which counts adjacencies over `support.toFinset`. `Walk.support` for a cycle `w → ... → w` includes `w` twice (head and last); `toFinset` deduplicates, so the count is correct for vertex-set membership. No fidelity issue, but worth confirming `Walk.support` head/tail overlap behavior during proof.
   - FLAG (minor): `sharpness_five_vertices` claims a graph on 5 vertices with 7 = 2*5-3 edges and no cycle+triple attachment. The reasoning via series-parallel graphs (no K₄-subdivision, hence no cycle+triple) is sound, but the concrete witness is not provided — the `sorry` must construct one.
-/
