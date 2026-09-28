/-
Erdős–Gyárfás problem 64 — the doubling reduction.

PROVENANCE. arXiv:2609.28594, Lemma 3.5 (`lem:D`) and Corollary 3.6
(`cor:notall`), the "doubling reduction" of Sec. 3.2.  Graphs are finite,
undirected and simple throughout; `G` is an arbitrary finite simple graph and
`hmin : Erdos64.IsMinimalCounterexample G` (see `Basic.lean`) is lexicographic
minimality of `(number of vertices, number of edges)` among the
`Erdos64.IsCounterexample`s.

SOURCE CLAIM BOUNDARY.  The source defines, for a minimal counterexample `G`,

* `L = {v : d(v) = 3}`, `H = {v : d(v) ≥ 4}`, and
* `L₂ = {v ∈ L : v has exactly two neighbours in H}`,

and a multigraph `M` on vertex set `H` whose edges `xy` are in bijection with
the vertices `v ∈ L₂` with `N_G(v) ∩ H = {x, y}`.  Lemma 3.5 then proves

  (1) `M` is simple,
  (2) `M` contains no cycle of length `2 ^ k`, `k ≥ 1`,
  (3) `M` is `2`-degenerate,

and deduces `|L₂| = |E(M)| ≤ 2h - 3` for `h ≥ 2`, `L₂ = ∅` for `h ≤ 1`.
Corollary 3.6 records that `L = L₂` is impossible.

WHAT IS FORMALIZED HERE.  Because `SimpleGraph` adjacency is a proposition,
the source's "multigraph, then prove simple" is replaced by the honest
`SimpleGraph` relation `doublingGraph G` on the subtype `↥(degreeGeFourFinset G)`
whose edges are witnessed by a vertex of `L₂`.  Simplicity is *not* an
assumption: `doublingGraph` is loopless by construction (`card = 2` rules out a
degenerate pair), and the source's uniqueness argument — distinct `L₂` vertices
cannot determine the same unordered high pair, since `x u y v x` would be a
genuine `4`-cycle of `G` — is proved as
`eq_of_mem_degreeThreeTwoHigh_of_highDegreeNeighbors_eq`.  That uniqueness is
what makes the edge count `|L₂| = |E(M)|` faithful; it is proved, not assumed:
`card_degreeThreeTwoHigh_eq_card_edgeFinset`.

Cycle lifting (item (2) above) is *proved*, not assumed: a cycle in
`doublingGraph G` of length `t` is lifted, by inserting the (unique) `L₂`
witness of every edge, to a cycle of `G` of length `2 * t`
(`exists_lift_isCycle`).  The exponent shift is the reason the source states
`k ≥ 1` where the ambient conjecture uses `k ≥ 2`: a `2 ^ k`-cycle of `M`
becomes a `2 ^ (k + 1)`-cycle of `G`, and `2 ^ 1 = 2` is already impossible in
the simple graph `M`, so `not_hasPowerOfTwoCycle_doublingGraph` needs no case
analysis on `k`.

Item (3) above is formalized in the "no subgraph has minimum degree at least
three" form, which is exactly the hypothesis consumed by the `2`-degeneracy
edge bound of Lemma 3.4: `false_of_minDegree_three_of_le_doublingGraph` and
`exists_degree_le_two_of_le_doublingGraph`.  The numerical bound
`|E(M)| ≤ 2h - 3` itself is *not* proved here; only the degeneracy property it
consumes.

Nothing in this file assumes witness uniqueness, cycle lifting, or minimality
as a hypothesis: minimality appears only where the source uses it, and the
corresponding conclusions are `False`, not axioms.
-/

import Erdos.Erdos64.Reductions
import Mathlib.Combinatorics.SimpleGraph.Dart

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### 1. `L₂` and the doubled graph -/

/-- `L₂`, the set of degree-three vertices with exactly two neighbours in `H`
(notation of arXiv:2609.28594, Sec. 3.2). -/
def degreeThreeTwoHigh (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finset V :=
  (degreeThreeFinset G).filter fun v => (highDegreeNeighbors G v).card = 2

/-- Membership in `L₂`: `v` has degree three and exactly two high-degree
neighbours. -/
@[simp] theorem mem_degreeThreeTwoHigh {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v : V} : v ∈ degreeThreeTwoHigh G ↔ degreeThree G v ∧ (highDegreeNeighbors G v).card = 2 := by
  simp [degreeThreeTwoHigh]

/-- `L₂` consists of degree-three vertices. -/
theorem degreeThreeTwoHigh_subset_degreeThreeFinset (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : degreeThreeTwoHigh G ⊆ degreeThreeFinset G :=
  Finset.filter_subset _ _

/-- A vertex of `L₂` has degree exactly three. -/
theorem degreeThree_of_mem_degreeThreeTwoHigh {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {v : V} (hv : v ∈ degreeThreeTwoHigh G) : degreeThree G v :=
  (mem_degreeThreeTwoHigh.mp hv).1

/-- A vertex of `L₂` has exactly two high-degree neighbours. -/
theorem card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {v : V} (hv : v ∈ degreeThreeTwoHigh G) :
    (highDegreeNeighbors G v).card = 2 :=
  (mem_degreeThreeTwoHigh.mp hv).2

/-- A vertex of `L₂` has a high-degree neighbour. -/
theorem exists_mem_highDegreeNeighbors_of_mem_degreeThreeTwoHigh {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {v : V} (hv : v ∈ degreeThreeTwoHigh G) :
    ∃ x : V, x ∈ highDegreeNeighbors G v := by
  have := card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh hv
  exact Finset.card_pos.mp (by omega)

/-- The high-degree vertex set `H` is never all of `V` in a minimal
counterexample: a degree-three vertex exists. -/
theorem exists_notMem_degreeGeFourFinset {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    ∃ v : V, v ∉ degreeGeFourFinset G := by
  obtain ⟨v⟩ := hmin.isCounterexample.nonempty
  obtain ⟨w, _, hw⟩ := exists_adjacent_degreeThree hmin v
  refine ⟨w, fun hmem => ?_⟩
  have h4 : 4 ≤ G.degree w := mem_degreeGeFourFinset.mp hmem
  have h3 : G.degree w = 3 := hw
  omega

/-- The doubled graph `M` of arXiv:2609.28594, Lemma 3.5: a simple graph on the
high-degree vertices, where distinct `x, y` are adjacent iff some `v ∈ L₂` has
high-degree neighbour set exactly `{x, y}`.  Simplicity is proved (the relation
is loopless because a `L₂` vertex has exactly two high-degree neighbours), not
assumed. -/
def doublingGraph (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    SimpleGraph ↥(degreeGeFourFinset G) where
  Adj x y := ∃ v ∈ degreeThreeTwoHigh G, highDegreeNeighbors G v = {(x : V), (y : V)}
  symm := ⟨by
    rintro x y ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [h, Finset.pair_comm]⟩⟩
  loopless := ⟨by
    rintro x ⟨v, hv, h⟩
    have hcard := card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh hv
    rw [h, Finset.pair_eq_singleton, Finset.card_singleton] at hcard
    omega⟩

/-- Adjacency in the doubled graph, unfolded. -/
theorem doublingGraph_adj_iff {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)} :
    (doublingGraph G).Adj x y ↔
      ∃ v ∈ degreeThreeTwoHigh G, highDegreeNeighbors G v = {(x : V), (y : V)} :=
  Iff.rfl

/-- A vertex of `L₂` realises an edge of the doubled graph. -/
theorem doublingGraph_adj_of_mem {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {v : V} (hv : v ∈ degreeThreeTwoHigh G) {x y : ↥(degreeGeFourFinset G)}
    (h : highDegreeNeighbors G v = {(x : V), (y : V)}) : (doublingGraph G).Adj x y :=
  ⟨v, hv, h⟩

/-- A high-degree vertex is not a vertex of `L₂`. -/
theorem ne_of_mem_degreeGeFour_of_mem_degreeThreeTwoHigh {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] {w : ↥(degreeGeFourFinset G)} {u : V}
    (hu : u ∈ degreeThreeTwoHigh G) : (w : V) ≠ u := by
  intro h
  have h4 : 4 ≤ G.degree (w : V) := mem_degreeGeFourFinset.mp w.2
  have h3 : G.degree u = 3 := degreeThree_of_mem_degreeThreeTwoHigh hu
  rw [h] at h4
  omega

/-- Classical decidability of adjacency in the doubled graph. -/
noncomputable instance instDecidableAdjDoublingGraph (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] : DecidableRel (doublingGraph G).Adj :=
  Classical.decRel _

/-! ### 2. Uniqueness of the `L₂` witness

The source's proof that the auxiliary multigraph is simple: two distinct
vertices of `L₂` determining the same unordered high pair would produce the
`4`-cycle `x u y v x` in `G`, a forbidden power-of-two cycle. -/

/-- Two `Finset`s of the shape `{a, b}` and `{c, d}` with `a ≠ b` determine the
same unordered pair in `Sym2`. -/
theorem sym2_eq_of_pair_finset_eq {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (h : ({a, b} : Finset α) = {c, d}) : s(a, b) = s(c, d) := by
  have ha : a = c ∨ a = d := by
    have hmem : a ∈ ({c, d} : Finset α) := h ▸ (by simp : a ∈ ({a, b} : Finset α))
    simpa using hmem
  have hb : b = c ∨ b = d := by
    have hmem : b ∈ ({c, d} : Finset α) := h ▸ (by simp : b ∈ ({a, b} : Finset α))
    simpa using hmem
  rcases ha with hac | had
  · subst hac
    rcases hb with hbc | hbd
    · exact absurd hbc.symm hab
    · rw [hbd]
  · subst had
    rcases hb with hbc | hbd
    · rw [hbc, Sym2.eq_swap]
    · exact absurd hbd hab.symm

/-- **Simplicity of the doubling multigraph.**  Two vertices of `L₂` with the
same set of high-degree neighbours are equal, in a graph without a power-of-two
cycle: otherwise `x u y v x` is a `4`-cycle. -/
theorem eq_of_mem_degreeThreeTwoHigh_of_highDegreeNeighbors_eq {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G) {u v : V}
    (hu : u ∈ degreeThreeTwoHigh G) (hv : v ∈ degreeThreeTwoHigh G)
    (h : highDegreeNeighbors G u = highDegreeNeighbors G v) : u = v := by
  by_contra huv
  obtain ⟨x, y, hxy, huxy⟩ := Finset.card_eq_two.mp
    (card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh hu)
  have hvxy : highDegreeNeighbors G v = {x, y} := by rw [← h, huxy]
  have hxmem : x ∈ highDegreeNeighbors G u := by rw [huxy]; simp
  have hymem : y ∈ highDegreeNeighbors G u := by rw [huxy]; simp
  have hxmemv : x ∈ highDegreeNeighbors G v := by rw [hvxy]; simp
  have hymemv : y ∈ highDegreeNeighbors G v := by rw [hvxy]; simp
  have hx4 : degreeGeFour G x := (mem_highDegreeNeighbors.mp hxmem).1
  have hy4 : degreeGeFour G y := (mem_highDegreeNeighbors.mp hymem).1
  have hux : G.Adj u x := (mem_highDegreeNeighbors.mp hxmem).2
  have huy : G.Adj u y := (mem_highDegreeNeighbors.mp hymem).2
  have hvx : G.Adj v x := (mem_highDegreeNeighbors.mp hxmemv).2
  have hvy : G.Adj v y := (mem_highDegreeNeighbors.mp hymemv).2
  have hu3 : degreeThree G u := degreeThree_of_mem_degreeThreeTwoHigh hu
  have hv3 : degreeThree G v := degreeThree_of_mem_degreeThreeTwoHigh hv
  simp only [degreeThree] at hu3 hv3
  simp only [degreeGeFour] at hx4 hy4
  have hux_ne : u ≠ x := by intro h'; rw [h'] at hu3; omega
  have huy_ne : u ≠ y := by intro h'; rw [h'] at hu3; omega
  have hvx_ne : v ≠ x := by intro h'; rw [h'] at hv3; omega
  have hvy_ne : v ≠ y := by intro h'; rw [h'] at hv3; omega
  refine hG ⟨2, by omega, x,
    Walk.cons (hux.symm) (Walk.cons huy (Walk.cons (hvy.symm) (Walk.cons hvx Walk.nil))), ?_,
    by simp [Walk.length_cons]⟩
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by simp [Walk.length_cons]⟩
  rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ Walk.not_nil_cons]
  simp only [Walk.support_cons, Walk.support_nil]
  have hyv_ne : y ≠ v := hvy_ne.symm
  have hyx_ne : y ≠ x := hxy.symm
  simp [huy_ne, huv, hux_ne, hyv_ne, hyx_ne, hvx_ne]

/-- **Uniqueness of the `L₂` witness of an edge of the doubled graph.**  For an
edge of `doublingGraph G` the witnessing vertex of `L₂` is unique.  This is the
form in which simplicity is used to keep the edge count faithful. -/
theorem existsUnique_witness_doublingGraph {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G) {x y : ↥(degreeGeFourFinset G)}
    (h : (doublingGraph G).Adj x y) :
    ∃! v : V, v ∈ degreeThreeTwoHigh G ∧ highDegreeNeighbors G v = {(x : V), (y : V)} := by
  obtain ⟨v, hv, hspec⟩ := h
  refine ⟨v, ⟨hv, hspec⟩, ?_⟩
  rintro w ⟨hw, hwspec⟩
  refine eq_of_mem_degreeThreeTwoHigh_of_highDegreeNeighbors_eq hG hw hv ?_
  rw [hwspec, hspec]

/-! ### 3. The exact edge correspondence -/

/-- The vertices of `L₂` are in exact bijective cardinality correspondence with
edges of the doubled graph.  The bijection sends a vertex to its unordered pair
of high-degree neighbours; injectivity is the four-cycle argument above. -/
theorem card_degreeThreeTwoHigh_eq_card_edgeFinset {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G) :
    (degreeThreeTwoHigh G).card = (doublingGraph G).edgeFinset.card := by
  classical
  let x (v : V) (hv : v ∈ degreeThreeTwoHigh G) : V := Classical.choose
    (Finset.card_eq_two.mp (card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh hv))
  let y (v : V) (hv : v ∈ degreeThreeTwoHigh G) : V := Classical.choose
    (Classical.choose_spec
      (Finset.card_eq_two.mp (card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh hv)))
  have hdata (v : V) (hv : v ∈ degreeThreeTwoHigh G) :
      x v hv ≠ y v hv ∧ highDegreeNeighbors G v = {x v hv, y v hv} :=
    Classical.choose_spec (Classical.choose_spec
      (Finset.card_eq_two.mp (card_highDegreeNeighbors_of_mem_degreeThreeTwoHigh hv)))
  have hpair (v : V) (hv : v ∈ degreeThreeTwoHigh G) :
      highDegreeNeighbors G v = {x v hv, y v hv} := (hdata v hv).2
  have hxy (v : V) (hv : v ∈ degreeThreeTwoHigh G) : x v hv ≠ y v hv := (hdata v hv).1
  have hx (v : V) (hv : v ∈ degreeThreeTwoHigh G) :
      x v hv ∈ degreeGeFourFinset G := by
    rw [mem_degreeGeFourFinset]
    have hxmem : x v hv ∈ highDegreeNeighbors G v :=
      (hpair v hv).symm ▸ Finset.mem_insert_self _ _
    exact (mem_highDegreeNeighbors.mp hxmem).1
  have hy (v : V) (hv : v ∈ degreeThreeTwoHigh G) :
      y v hv ∈ degreeGeFourFinset G := by
    rw [mem_degreeGeFourFinset]
    have hymem : y v hv ∈ highDegreeNeighbors G v :=
      (hpair v hv).symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (mem_highDegreeNeighbors.mp hymem).1
  let i (v : V) (hv : v ∈ degreeThreeTwoHigh G) :
      Sym2 ↥(degreeGeFourFinset G) := s(⟨x v hv, hx v hv⟩, ⟨y v hv, hy v hv⟩)
  apply Finset.card_bij i
  · intro v hv
    rw [mem_edgeFinset, mem_edgeSet]
    exact doublingGraph_adj_of_mem hv (hpair v hv)
  · intro u hu v hv huv
    apply eq_of_mem_degreeThreeTwoHigh_of_highDegreeNeighbors_eq hG hu hv
    have hpairs :
        ({x u hu, y u hu} : Finset V) = {x v hv, y v hv} := by
      have hs := congrArg Sym2.toFinset huv
      simpa [i, Sym2.toFinset_mk_eq] using congrArg
        (Finset.map ⟨Subtype.val, Subtype.val_injective⟩) hs
    rw [hpair u hu, hpair v hv, hpairs]
  · intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : (doublingGraph G).Adj a b := (mem_edgeSet _).mp ((mem_edgeFinset).mp he)
      obtain ⟨v, hv, hvpair⟩ := hab
      refine ⟨v, hv, ?_⟩
      change s(⟨x v hv, hx v hv⟩, ⟨y v hv, hy v hv⟩) = s(a, b)
      have hchosen : ({x v hv, y v hv} : Finset V) = {(a : V), (b : V)} := by
        rw [← hpair v hv, hvpair]
      have hval := sym2_eq_of_pair_finset_eq (hxy v hv) hchosen
      rw [Sym2.eq_iff] at hval ⊢
      rcases hval with hval | hval
      · exact Or.inl ⟨Subtype.ext hval.1, Subtype.ext hval.2⟩
      · exact Or.inr ⟨Subtype.ext hval.1, Subtype.ext hval.2⟩

/-! ### 4. Lifting walks and cycles -/

/-- The canonical `L₂` vertex inserted in an edge of the doubled graph. -/
noncomputable def doublingWitness {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) : V :=
  Classical.choose hxy

/-- The chosen doubling witness belongs to `L₂` and has the prescribed high neighbours. -/
theorem doublingWitness_spec {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) :
    doublingWitness hxy ∈ degreeThreeTwoHigh G ∧
      highDegreeNeighbors G (doublingWitness hxy) = {(x : V), (y : V)} :=
  Classical.choose_spec hxy

/-- The chosen witness is adjacent in `G` to the left endpoint. -/
theorem adj_doublingWitness_left {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) : G.Adj (x : V) (doublingWitness hxy) := by
  have hx : (x : V) ∈ highDegreeNeighbors G (doublingWitness hxy) := by
    rw [(doublingWitness_spec hxy).2]
    exact Finset.mem_insert_self _ _
  exact (mem_highDegreeNeighbors.mp hx).2.symm

/-- The chosen witness is adjacent in `G` to the right endpoint. -/
theorem adj_doublingWitness_right {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) : G.Adj (doublingWitness hxy) (y : V) := by
  have hy : (y : V) ∈ highDegreeNeighbors G (doublingWitness hxy) := by
    rw [(doublingWitness_spec hxy).2]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact (mem_highDegreeNeighbors.mp hy).2

/-- A chosen doubling witness is not high-degree. -/
theorem doublingWitness_not_mem_degreeGeFourFinset {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) : doublingWitness hxy ∉ degreeGeFourFinset G := by
  intro hw
  exact ne_of_mem_degreeGeFour_of_mem_degreeThreeTwoHigh (w := ⟨doublingWitness hxy, hw⟩)
    (doublingWitness_spec hxy).1 rfl

/-- Equal chosen witnesses determine equal unordered doubled edges. -/
theorem edge_eq_of_doublingWitness_eq {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y a b : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) (hab : (doublingGraph G).Adj a b)
    (h : doublingWitness hxy = doublingWitness hab) : s(x, y) = s(a, b) := by
  have hpairs : ({(x : V), (y : V)} : Finset V) = {(a : V), (b : V)} := by
    rw [← (doublingWitness_spec hxy).2, ← (doublingWitness_spec hab).2, h]
  have hxyval : (x : V) ≠ (y : V) := fun hval => hxy.ne (Subtype.ext hval)
  have hval : s((x : V), (y : V)) = s((a : V), (b : V)) :=
    sym2_eq_of_pair_finset_eq hxyval hpairs
  rw [Sym2.eq_iff] at hval ⊢
  rcases hval with hval | hval
  · exact Or.inl ⟨Subtype.ext hval.1, Subtype.ext hval.2⟩
  · exact Or.inr ⟨Subtype.ext hval.1, Subtype.ext hval.2⟩

/-- Chosen witnesses agree when their unordered doubled edges agree. -/
theorem doublingWitness_eq_of_edge_eq {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G)
    {x y a b : ↥(degreeGeFourFinset G)}
    (hxy : (doublingGraph G).Adj x y) (hab : (doublingGraph G).Adj a b)
    (hedge : s(x, y) = s(a, b)) : doublingWitness hxy = doublingWitness hab := by
  apply eq_of_mem_degreeThreeTwoHigh_of_highDegreeNeighbors_eq hG
    (doublingWitness_spec hxy).1 (doublingWitness_spec hab).1
  rw [(doublingWitness_spec hxy).2, (doublingWitness_spec hab).2]
  have hs := congrArg Sym2.toFinset hedge
  simpa [Sym2.toFinset_mk_eq] using congrArg
    (Finset.map ⟨Subtype.val, Subtype.val_injective⟩) hs

/-- Replace every doubled edge of a walk by its two-edge path through the chosen `L₂` witness. -/
noncomputable def liftDoublingWalk {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : {x y : ↥(degreeGeFourFinset G)} →
      (doublingGraph G).Walk x y → G.Walk (x : V) (y : V)
  | _, _, .nil => .nil
  | _, _, .cons h p =>
      .cons (adj_doublingWitness_left h)
        (.cons (adj_doublingWitness_right h) (liftDoublingWalk p))

/-- Lifting doubles the length of a walk. -/
@[simp] theorem length_liftDoublingWalk {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {x y : ↥(degreeGeFourFinset G)}
    (p : (doublingGraph G).Walk x y) : (liftDoublingWalk p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftDoublingWalk, ih, Nat.mul_succ]

/-- Membership in a lifted support is either an original high vertex or the
chosen witness of an edge of the original walk. -/
theorem mem_support_liftDoublingWalk_iff {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G)
    {x y : ↥(degreeGeFourFinset G)}
    (p : (doublingGraph G).Walk x y) (v : V) :
    v ∈ (liftDoublingWalk p).support ↔
      (∃ z ∈ p.support, (z : V) = v) ∨
      ∃ (a b : ↥(degreeGeFourFinset G)) (h : (doublingGraph G).Adj a b),
        s(a, b) ∈ p.edges ∧ doublingWitness h = v := by
  induction p with
  | nil => simp [liftDoublingWalk, eq_comm]
  | @cons x y z h p ih =>
      simp only [liftDoublingWalk, Walk.support_cons, Walk.edges_cons, List.mem_cons,
        ih]
      constructor
      · rintro (rfl | rfl | hp)
        · exact Or.inl ⟨x, Or.inl rfl, rfl⟩
        · exact Or.inr ⟨x, y, h, Or.inl rfl, rfl⟩
        · rcases hp with ⟨a, ha, rfl⟩ | ⟨a, b, hab, he, hw⟩
          · exact Or.inl ⟨a, Or.inr ha, rfl⟩
          · exact Or.inr ⟨a, b, hab, Or.inr he, hw⟩
      · rintro (⟨a, rfl | ha, hav⟩ | ⟨a, b, hab, hedge | he, hw⟩)
        · exact Or.inl hav.symm
        · exact Or.inr (Or.inr (Or.inl ⟨a, ha, hav⟩))
        · have hwit : doublingWitness hab = doublingWitness h :=
            doublingWitness_eq_of_edge_eq hG hab h hedge
          exact Or.inr (Or.inl (hw.symm.trans hwit))
        · exact Or.inr (Or.inr (Or.inr ⟨a, b, hab, he, hw⟩))

/-- Lifting preserves simple paths. -/
theorem isPath_liftDoublingWalk {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G)
    {x y : ↥(degreeGeFourFinset G)} (p : (doublingGraph G).Walk x y)
    (hp : p.IsPath) : (liftDoublingWalk p).IsPath := by
  induction p with
  | nil => simp [liftDoublingWalk]
  | @cons x y z h p ih =>
      have hp' : p.IsPath ∧ x ∉ p.support := (Walk.cons_isPath_iff h p).mp hp
      have hlift : (liftDoublingWalk p).IsPath := ih hp'.1
      have hw_not : doublingWitness h ∉ (liftDoublingWalk p).support := by
        intro hw
        rw [mem_support_liftDoublingWalk_iff hG] at hw
        rcases hw with ⟨a, ha, hav⟩ | ⟨a, b, hab, he, heq⟩
        · have hhigh : doublingWitness h ∈ degreeGeFourFinset G := by
            rw [← hav]
            exact a.2
          exact doublingWitness_not_mem_degreeGeFourFinset h hhigh
        · have hedge : s(x, y) = s(a, b) := edge_eq_of_doublingWitness_eq h hab heq.symm
          have hfirst : s(x, y) ∈ p.edges := hedge ▸ he
          exact hp'.2 (p.fst_mem_support_of_mem_edges hfirst)
      have htail :
          (Walk.cons (adj_doublingWitness_right h) (liftDoublingWalk p)).IsPath :=
        (Walk.cons_isPath_iff _ _).mpr ⟨hlift, hw_not⟩
      apply (Walk.cons_isPath_iff _ _).mpr
      refine ⟨htail, ?_⟩
      simp only [Walk.support_cons, List.mem_cons, not_or]
      constructor
      · intro hxw
        have hhigh : doublingWitness h ∈ degreeGeFourFinset G := hxw ▸ x.2
        exact doublingWitness_not_mem_degreeGeFourFinset h hhigh
      · intro hx
        rw [mem_support_liftDoublingWalk_iff hG] at hx
        rcases hx with ⟨a, ha, hav⟩ | ⟨a, b, hab, he, heq⟩
        · have hax : a = x := Subtype.ext hav
          rw [hax] at ha
          exact hp'.2 ha
        · have hhigh : doublingWitness hab ∈ degreeGeFourFinset G := by
            rw [heq]
            exact x.2
          exact doublingWitness_not_mem_degreeGeFourFinset hab hhigh

/-- Every simple cycle in the doubled graph lifts to a simple cycle in `G` of
exactly twice the length.  No lifting principle is assumed: the walk is the
explicit edge-by-edge insertion `liftDoublingWalk`. -/
theorem exists_lift_isCycle {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G)
    {x : ↥(degreeGeFourFinset G)} (c : (doublingGraph G).Walk x x)
    (hc : c.IsCycle) :
    ∃ q : G.Walk (x : V) (x : V), q.IsCycle ∧ q.length = 2 * c.length := by
  refine ⟨liftDoublingWalk c, ?_, length_liftDoublingWalk c⟩
  cases c with
  | nil => exact (Walk.not_isCycle_nil hc).elim
  | @cons _ y _ h p =>
      have hc' : p.IsPath ∧ s(x, y) ∉ p.edges := (Walk.cons_isCycle_iff p h).mp hc
      have hlift : (liftDoublingWalk p).IsPath := isPath_liftDoublingWalk hG p hc'.1
      have hw_not : doublingWitness h ∉ (liftDoublingWalk p).support := by
        intro hw
        rw [mem_support_liftDoublingWalk_iff hG] at hw
        rcases hw with ⟨a, ha, hav⟩ | ⟨a, b, hab, he, heq⟩
        · have hhigh : doublingWitness h ∈ degreeGeFourFinset G := by
            rw [← hav]
            exact a.2
          exact doublingWitness_not_mem_degreeGeFourFinset h hhigh
        · have hedge : s(x, y) = s(a, b) :=
            edge_eq_of_doublingWitness_eq h hab heq.symm
          exact hc'.2 (hedge ▸ he)
      rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · change (Walk.cons (adj_doublingWitness_right h) (liftDoublingWalk p)).IsPath
        exact (Walk.cons_isPath_iff _ _).mpr ⟨hlift, hw_not⟩
      · rw [length_liftDoublingWalk]
        have hthree : 3 ≤ (Walk.cons h p).length := hc.three_le_length
        omega

/-- The doubled graph of a graph without power-of-two cycles also has no
power-of-two cycle.  A cycle of exponent `k` lifts to exponent `k + 1`. -/
theorem not_hasPowerOfTwoCycle_doublingGraph {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hG : ¬ HasPowerOfTwoCycle G) :
    ¬ HasPowerOfTwoCycle (doublingGraph G) := by
  rintro ⟨k, hk, x, c, hc, hlen⟩
  obtain ⟨q, hq, hqLen⟩ := exists_lift_isCycle hG c hc
  apply hG
  refine ⟨k + 1, by omega, (x : V), q, hq, ?_⟩
  rw [hqLen, hlen, pow_succ, Nat.mul_comm]

/-! ### 5. Minimality and two-degeneracy -/

/-- No subgraph of the doubled graph can have minimum degree at least three.
Otherwise it is itself a smaller counterexample: cycle-freeness is inherited
from the doubled graph, while its vertex type is the proper high-degree subset
of the vertices of `G`. -/
theorem false_of_minDegree_three_of_le_doublingGraph {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    {K : SimpleGraph ↥(degreeGeFourFinset G)} [DecidableRel K.Adj]
    (hle : K ≤ doublingGraph G) (hdeg : 3 ≤ K.minDegree) : False := by
  have hne : Nonempty ↥(degreeGeFourFinset G) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    haveI : Subsingleton ↥(degreeGeFourFinset G) := ⟨fun a _ => isEmptyElim a⟩
    rw [minDegree_of_subsingleton] at hdeg
    omega
  haveI : Nonempty ↥(degreeGeFourFinset G) := hne
  have hKdeg : ∀ v : ↥(degreeGeFourFinset G), 3 ≤ K.degree v := fun v =>
    hdeg.trans (minDegree_le_degree K v)
  have hK : IsCounterexample K := ⟨hne, hKdeg,
    not_hasPowerOfTwoCycle_of_le hle
      (not_hasPowerOfTwoCycle_doublingGraph hmin.not_hasPowerOfTwoCycle)⟩
  have hcard : Fintype.card ↥(degreeGeFourFinset G) < Fintype.card V := by
    rw [Fintype.card_coe, ← Finset.card_univ]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    obtain ⟨v, hv⟩ := exists_notMem_degreeGeFourFinset hmin
    intro heq
    apply hv
    rw [heq]
    exact Finset.mem_univ v
  exact hmin.false_of_size_lexLt K hK (lexLt_size_of_card_verts_lt K hcard)

/-- Every nonempty subgraph of the doubled graph has a vertex of degree at most
two.  This is the hereditary low-degree formulation of `2`-degeneracy used by
the later density argument. -/
theorem exists_degree_le_two_of_le_doublingGraph {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    {K : SimpleGraph ↥(degreeGeFourFinset G)} [DecidableRel K.Adj]
    (hle : K ≤ doublingGraph G) (hne : Nonempty ↥(degreeGeFourFinset G)) :
    ∃ v : ↥(degreeGeFourFinset G), K.degree v ≤ 2 := by
  letI : Nonempty ↥(degreeGeFourFinset G) := hne
  obtain ⟨v, hv⟩ := K.exists_minimal_degree_vertex
  refine ⟨v, ?_⟩
  by_contra hnot
  have hdeg : 3 ≤ K.minDegree := by omega
  exact false_of_minDegree_three_of_le_doublingGraph hmin hle hdeg

/-- Every nonempty induced subgraph of the doubled graph has a vertex of degree
at most two.  Unlike the fixed-vertex-set formulation, this hereditary form
allows vertices to be peeled one at a time and is therefore directly sufficient
for the standard induction proving `|E(M)| ≤ 2 * |H| - 3` when `2 ≤ |H|`. -/
theorem exists_degree_le_two_induce_doublingGraph {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (s : Set ↥(degreeGeFourFinset G)) [Fintype s] [DecidablePred (· ∈ s)]
    (hne : Nonempty s) :
    ∃ v : s, ((doublingGraph G).induce s).degree v ≤ 2 := by
  by_contra hex
  have hdeg : ∀ v : s, 3 ≤ ((doublingGraph G).induce s).degree v := by
    intro v
    have hv : ¬((doublingGraph G).induce s).degree v ≤ 2 := fun hv => hex ⟨v, hv⟩
    omega
  have hcounter : IsCounterexample ((doublingGraph G).induce s) :=
    ⟨hne, hdeg, not_hasPowerOfTwoCycle_induce (doublingGraph G) s
      (not_hasPowerOfTwoCycle_doublingGraph hmin.not_hasPowerOfTwoCycle)⟩
  have hhighcard : Fintype.card ↥(degreeGeFourFinset G) < Fintype.card V := by
    rw [Fintype.card_coe, ← Finset.card_univ]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    obtain ⟨v, hv⟩ := exists_notMem_degreeGeFourFinset hmin
    intro heq
    apply hv
    rw [heq]
    exact Finset.mem_univ v
  have hcard : Fintype.card s < Fintype.card V :=
    (Fintype.card_le_of_injective (fun x : s => (x : ↥(degreeGeFourFinset G)))
      Subtype.val_injective).trans_lt hhighcard
  exact hmin.false_of_size_lexLt ((doublingGraph G).induce s) hcounter
    (lexLt_size_of_card_verts_lt ((doublingGraph G).induce s) hcard)

end Erdos64
