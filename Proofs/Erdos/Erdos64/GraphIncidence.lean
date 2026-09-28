/-
Erdős–Gyárfás problem 64 — the explicit partition graph → incidence-configuration bridge.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic
Bipartite Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Section 2
("Incidence configurations and cycle translations"), Proposition `prop:incidence`.  Graphs here
are finite, undirected and simple.

SOURCE CLAIM BOUNDARY.  Section 2 records that a simple cubic bipartite graph together with a
specified bipartition `(X, Y)` determines an incidence structure on the point set `X` indexed by
the block indices `Y`, whose block at `y` is `N_G(y)`; the Levi graph of that structure is
isomorphic to `G` through the vertex bijection induced by the partition; and the local cycle
translations (`C₄`, `C₆`) of that section are statements about that structure.  This module
formalizes exactly that bridge.

WHAT IS FORMALIZED HERE.  Given a finite simple graph `G` on `V`, explicit finite sides
`X Y : Finset V` with `hXY : G.IsBipartiteWith X Y` and `hcover : X ∪ Y = univ`, it

* defines the point type `Point X = {v // v ∈ X}` and the block-index type `Block Y = {v // v ∈ Y}`
  and extracts the incidence configuration `graphIncidenceConfig G X Y`, whose block at `b` is
  precisely the point-side neighbour set of the original vertex `b.1`, with membership
  `p ∈ config.blocks b ↔ G.Adj p.1 b.1`;
* defines the explicit vertex equivalence `V ≃ Sum (Point X) (Block Y)` determined by the
  partition (a hand-written `if`/`else` on `v ∈ X`, with disjointness from `hXY` and coverage from
  `hcover` supplying the inverse laws) and the induced `SimpleGraph.Iso G config.leviGraph`;
* transports simple cycles of every length across that isomorphism, so that
  `HasSimpleCycleOfLength G n ↔ HasSimpleCycleOfLength config.leviGraph n`;
* derives, from `G.IsRegularOfDegree 3`, `3`-uniformity and `3`-regularity of the extracted
  configuration and `3`-regularity of its Levi graph, counting the original neighbour vertices
  through `SimpleGraph.neighborFinset` and `SimpleGraph.degree` and assuming nothing about
  injectivity of neighbourhoods (block indices with equal neighbourhoods remain distinct);
* derives, from the absence of a simple `4`-cycle in `G`, linearity of the extracted
  configuration, and from a simple `6`-cycle in `G` a `BergeTriangle` of the extracted
  configuration;
* proves the two sides have equal cardinality under `G.IsRegularOfDegree 3` and hence, from
  `Fintype.card V ≤ 58`, that each side has at most `29` vertices.

No connectedness assumption is made, and the empty graph on the empty vertex type remains a
valid instance.

NOT FORMALIZED HERE.  This is the explicit *partition* graph→configuration bridge only.  It does
**not** extract a partition from a bare `G.IsBipartite` (the sides `X`, `Y` are inputs, not
produced), it does not formalize the source's exhaustive restricted-growth search or its static
witness certificates, and it does not prove the `60`-vertex theorem (`thm:main`, `cor:bound`) or
any lower bound on `Fintype.card V`.  The `≤ 29` bounds below are upper bounds on the side sizes
under the stated hypotheses, not a `60`-vertex statement.
-/

import Erdos.Erdos64.IncidenceCycles

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

/-! ### The two sides of an explicit finite bipartition -/

/-- The **point side** of an explicit finite bipartition: the vertices lying in the side `X`,
as a subtype of the ambient vertex type.  Distinct vertices are distinct points. -/
abbrev Point {V : Type u} (X : Finset V) : Type u := {v : V // v ∈ X}

/-- The **block-index side** of an explicit finite bipartition: the vertices lying in the side
`Y`, as a subtype of the ambient vertex type.  Two block indices whose blocks coincide remain
distinct elements of this type; nothing below quotients them. -/
abbrev Block {V : Type u} (Y : Finset V) : Type u := {v : V // v ∈ Y}

section Helpers

variable {V : Type u}

/-- Every vertex outside `X` lies in `Y`, because the two sides cover the vertex set.  This is
the coverage half of the partition, used to build the `Sum`-valued vertex map. -/
theorem mem_of_notMem_of_union_eq_univ [Fintype V] [DecidableEq V] {X Y : Finset V}
    (hcover : X ∪ Y = Finset.univ) {v : V}
    (hv : v ∉ X) : v ∈ Y := by
  have huv : v ∈ X ∪ Y := by rw [hcover]; exact Finset.mem_univ v
  exact (Finset.mem_union.mp huv).resolve_left hv

/-- No vertex of `X` lies in `Y`: the disjointness half of the partition. -/
theorem notMem_Y_of_mem_X_of_isBipartiteWith {G : SimpleGraph V} {X Y : Finset V}
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) {v : V} (hv : v ∈ X) : v ∉ Y :=
  fun hw => Set.disjoint_left.mp hXY.disjoint (by simpa using hv) hw

/-- No vertex of `Y` lies in `X`: the disjointness half of the partition. -/
theorem notMem_X_of_mem_Y_of_isBipartiteWith {G : SimpleGraph V} {X Y : Finset V}
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) {v : V} (hv : v ∈ Y) : v ∉ X :=
  fun hw => Set.disjoint_left.mp hXY.disjoint hw hv

/-- The point type has the same cardinality as its defining side. -/
theorem card_point_eq_card (X : Finset V) : Fintype.card (Point X) = X.card :=
  Fintype.card_coe X

/-- The block-index type has the same cardinality as its defining side. -/
theorem card_block_eq_card (Y : Finset V) : Fintype.card (Block Y) = Y.card :=
  Fintype.card_coe Y

end Helpers

section Extracted

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (X Y : Finset V)

/-- The incidence configuration **extracted from the explicit partition** `(X, Y)` of `G`: the
points are the vertices in `X` and the block indexed by `b : Block Y` is the set of point-side
neighbours of the original vertex `b.1`.  Block indices are the vertices of `Y` themselves, so
two block indices with the same neighbourhood stay distinct. -/
def graphIncidenceConfig : IncidenceConfig (Point X) (Block Y) where
  blocks b := (G.neighborFinset b.1).subtype (fun v => v ∈ X)

end Extracted

section Bridge

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

/-- **Membership iff.**  A point `p` lies in the block indexed by `b` exactly when the original
vertices are adjacent in `G`.  The orientation is `G.Adj p.1 b.1`; the symmetrically equivalent
statement with `G.Adj b.1 p.1` follows by `SimpleGraph.adj_comm`. -/
theorem mem_graphIncidenceConfig_blocks (p : Point X) (b : Block Y) :
    p ∈ (graphIncidenceConfig G X Y).blocks b ↔ G.Adj p.1 b.1 := by
  simp only [graphIncidenceConfig, Finset.mem_subtype, SimpleGraph.mem_neighborFinset, adj_comm]

/-! ### The vertex equivalence and the graph isomorphism -/

/-- The vertex equivalence induced by the explicit partition: a vertex of `X` becomes a point,
any other vertex becomes a block index.  The decision is a hand-written `if`/`else` on
membership in `X`; disjointness of the sides gives the inverse law on block indices and
coverage gives the inverse law on points. -/
def graphIncidenceVertexEquiv (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ) :
    V ≃ Sum (Point X) (Block Y) where
  toFun v :=
    if hv : v ∈ X then Sum.inl ⟨v, hv⟩
    else Sum.inr ⟨v, mem_of_notMem_of_union_eq_univ hcover hv⟩
  invFun s := Sum.elim Subtype.val Subtype.val s
  left_inv v := by
    by_cases hv : v ∈ X
    · simp [dif_pos hv]
    · simp [dif_neg hv]
  right_inv s := by
    rcases s with p | b
    · simp
    · have hbX : b.1 ∉ X := notMem_X_of_mem_Y_of_isBipartiteWith hXY b.2
      simp [dif_neg hbX]

/-- The vertex equivalence sends a vertex of `X` to the corresponding point. -/
theorem graphIncidenceVertexEquiv_of_mem (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ) {v : V}
    (hv : v ∈ X) :
    graphIncidenceVertexEquiv G X Y hXY hcover v = Sum.inl ⟨v, hv⟩ :=
  dif_pos hv

/-- The vertex equivalence sends a vertex outside `X` to the corresponding block index. -/
theorem graphIncidenceVertexEquiv_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V))
    (hcover : X ∪ Y = Finset.univ) {v : V} (hv : v ∉ X) :
    graphIncidenceVertexEquiv G X Y hXY hcover v =
      Sum.inr ⟨v, mem_of_notMem_of_union_eq_univ hcover hv⟩ :=
  dif_neg hv

/-- **The graph isomorphism.**  The partition-induced vertex equivalence is an isomorphism from
`G` onto the Levi graph of the extracted incidence configuration: two vertices on the same side
of the partition are nonadjacent, and a vertex of `X` is adjacent to a vertex of `Y` exactly when
the corresponding point lies in the corresponding block. -/
def graphIncidenceIso (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ) :
    G ≃g (graphIncidenceConfig G X Y).leviGraph where
  toEquiv := graphIncidenceVertexEquiv G X Y hXY hcover
  map_rel_iff' := by
    intro v w
    by_cases hv : v ∈ X
    · by_cases hw : w ∈ X
      · rw [graphIncidenceVertexEquiv_of_mem G X Y hXY hcover hv,
          graphIncidenceVertexEquiv_of_mem G X Y hXY hcover hw]
        simp only [IncidenceConfig.leviGraph]
        constructor
        · intro hfalse
          exact False.elim hfalse
        · intro h
          exact notMem_Y_of_mem_X_of_isBipartiteWith hXY hw
            (hXY.mem_of_mem_adj (by simpa using hv) h)
      · have hwY : w ∈ Y := mem_of_notMem_of_union_eq_univ hcover hw
        rw [graphIncidenceVertexEquiv_of_mem G X Y hXY hcover hv,
          graphIncidenceVertexEquiv_of_notMem G X Y hXY hcover hw]
        simp only [IncidenceConfig.leviGraph]
        exact mem_graphIncidenceConfig_blocks ⟨v, hv⟩ ⟨w, hwY⟩
    · by_cases hw : w ∈ X
      · have hvY : v ∈ Y := mem_of_notMem_of_union_eq_univ hcover hv
        rw [graphIncidenceVertexEquiv_of_notMem G X Y hXY hcover hv,
          graphIncidenceVertexEquiv_of_mem G X Y hXY hcover hw]
        simp only [IncidenceConfig.leviGraph]
        rw [mem_graphIncidenceConfig_blocks ⟨w, hw⟩ ⟨v, hvY⟩]
        exact (SimpleGraph.adj_comm G v w).symm
      · have hvY : v ∈ Y := mem_of_notMem_of_union_eq_univ hcover hv
        have hwY : w ∈ Y := mem_of_notMem_of_union_eq_univ hcover hw
        rw [graphIncidenceVertexEquiv_of_notMem G X Y hXY hcover hv,
          graphIncidenceVertexEquiv_of_notMem G X Y hXY hcover hw]
        simp only [IncidenceConfig.leviGraph]
        constructor
        · intro hfalse
          exact False.elim hfalse
        · intro h
          exact notMem_X_of_mem_Y_of_isBipartiteWith hXY hvY
            (hXY.mem_of_mem_adj' (by simpa using hwY) h)

end Bridge

/-! ### Cycle transport along a graph isomorphism -/

section IsoTransport

variable {V : Type u} {W : Type u}
variable {G : SimpleGraph V} {G' : SimpleGraph W}

/-- A graph isomorphism transports simple cycles of every length: mapping a closed walk along the
isomorphism preserves both the `IsCycle` predicate (the vertex map is injective) and the length,
and the inverse isomorphism transports back. -/
theorem hasSimpleCycleOfLength_iso_iff (e : G ≃g G') (n : ℕ) :
    HasSimpleCycleOfLength G n ↔ HasSimpleCycleOfLength G' n := by
  constructor
  · rintro ⟨v, c, hc, hlen⟩
    exact ⟨e v, c.map e.toHom, hc.map e.toEmbedding.injective,
      by rw [SimpleGraph.Walk.length_map, hlen]⟩
  · rintro ⟨w, c, hc, hlen⟩
    exact ⟨e.symm w, c.map e.symm.toHom, hc.map e.symm.toEmbedding.injective,
      by rw [SimpleGraph.Walk.length_map, hlen]⟩

end IsoTransport

section Transport

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

/-- **Generic cycle transport.**  For every length `n`, the graph `G` has a simple `n`-cycle
exactly when the Levi graph of the extracted configuration does.  This is
`hasSimpleCycleOfLength_iso_iff` applied to the partition-induced isomorphism; no component
quotient and no identification of block indices is involved. -/
theorem hasSimpleCycleOfLength_graphIncidenceConfig_iff
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ) (n : ℕ) :
    HasSimpleCycleOfLength G n ↔
      HasSimpleCycleOfLength (graphIncidenceConfig G X Y).leviGraph n :=
  hasSimpleCycleOfLength_iso_iff (graphIncidenceIso G X Y hXY hcover) n

end Transport

section Degrees

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

/-- The block at `b`, transported back to the ambient vertex type along the subtype embedding, is
exactly the original neighbour finset of `b.1`.  Both sides are finite sets of the same vertices;
this is the counting bridge that avoids any injectivity assumption on neighbourhoods. -/
theorem blocks_map_subtype_eq_neighborFinset
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (b : Block Y) :
    ((graphIncidenceConfig G X Y).blocks b).map
        (Function.Embedding.subtype (fun v : V => v ∈ X)) = G.neighborFinset b.1 :=
  Finset.subtype_map_of_mem fun _ hx =>
    SimpleGraph.isBipartiteWith_neighborFinset_subset' hXY b.2 hx

/-- The block at `b` has exactly the degree of the original vertex `b.1` as its cardinality. -/
theorem card_blocks_eq_degree (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V))
    (b : Block Y) :
    ((graphIncidenceConfig G X Y).blocks b).card = G.degree b.1 := by
  have hmap := Finset.card_map (s := (graphIncidenceConfig G X Y).blocks b)
    (f := Function.Embedding.subtype (fun v : V => v ∈ X))
  rw [blocks_map_subtype_eq_neighborFinset hXY b] at hmap
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hmap
  exact hmap.symm

/-- The blocks incident with a point `p`, transported back to the ambient vertex type along the
subtype embedding, are exactly the original neighbour finset of `p.1`. -/
theorem incidentBlocks_map_subtype_eq_neighborFinset
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (p : Point X) :
    ((graphIncidenceConfig G X Y).incidentBlocks p).map
        (Function.Embedding.subtype (fun v : V => v ∈ Y)) = G.neighborFinset p.1 := by
  have hset : (graphIncidenceConfig G X Y).incidentBlocks p =
      (G.neighborFinset p.1).subtype (fun v => v ∈ Y) := by
    ext b
    simp only [IncidenceConfig.incidentBlocks, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_subtype, mem_graphIncidenceConfig_blocks, SimpleGraph.mem_neighborFinset]
  rw [hset]
  exact Finset.subtype_map_of_mem fun _ hx =>
    SimpleGraph.isBipartiteWith_neighborFinset_subset hXY p.2 hx

/-- The number of blocks incident with a point `p` is exactly the degree of the original vertex
`p.1`.  Block indices are counted with multiplicity, so two block indices with equal
neighbourhoods both contribute. -/
theorem card_incidentBlocks_eq_degree (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V))
    (p : Point X) :
    ((graphIncidenceConfig G X Y).incidentBlocks p).card = G.degree p.1 := by
  have hmap := Finset.card_map (s := (graphIncidenceConfig G X Y).incidentBlocks p)
    (f := Function.Embedding.subtype (fun v : V => v ∈ Y))
  rw [incidentBlocks_map_subtype_eq_neighborFinset hXY p] at hmap
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hmap
  exact hmap.symm

/-- Under `G.IsRegularOfDegree 3` the extracted configuration is `3`-uniform: every block has
exactly three points. -/
theorem isThreeUniform_of_isRegularOfDegree
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hreg : G.IsRegularOfDegree 3) :
    (graphIncidenceConfig G X Y).IsThreeUniform :=
  fun b => by rw [card_blocks_eq_degree hXY b, hreg b.1]

/-- Under `G.IsRegularOfDegree 3` the extracted configuration is `3`-regular: every point lies in
exactly three indexed blocks. -/
theorem isThreeRegular_of_isRegularOfDegree
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hreg : G.IsRegularOfDegree 3) :
    (graphIncidenceConfig G X Y).IsThreeRegular :=
  fun p => by rw [card_incidentBlocks_eq_degree hXY p, hreg p.1]

/-- **The degree-`3` extraction.**  A `3`-regular graph with an explicit bipartition extracts to a
`3`-uniform, `3`-regular incidence configuration whose Levi graph is again regular of degree `3`.
No injectivity of neighbourhoods is assumed. -/
theorem isThreeUniform_and_isThreeRegular_and_leviGraph_isRegularOfDegree
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hreg : G.IsRegularOfDegree 3) :
    (graphIncidenceConfig G X Y).IsThreeUniform ∧
      (graphIncidenceConfig G X Y).IsThreeRegular ∧
      (graphIncidenceConfig G X Y).leviGraph.IsRegularOfDegree 3 :=
  ⟨isThreeUniform_of_isRegularOfDegree hXY hreg,
    isThreeRegular_of_isRegularOfDegree hXY hreg,
    IncidenceConfig.isRegularOfDegree_three _
      (isThreeUniform_of_isRegularOfDegree hXY hreg)
      (isThreeRegular_of_isRegularOfDegree hXY hreg)⟩

end Degrees

section ShortCycles

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

/-- **No `C₄` implies linearity.**  If `G` has no simple `4`-cycle, the extracted configuration is
linear: distinct block indices share at most one point.  The proof transports the `C₄` of a shared
pair to `G` across the partition isomorphism and applies the exact `C₄`/shared-pair theorem
`IncidenceConfig.hasSimpleCycleOfLength_four_iff_hasSharedPair`. -/
theorem isLinear_of_not_hasSimpleCycleOfLength_four
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ)
    (hno4 : ¬ HasSimpleCycleOfLength G 4) :
    (graphIncidenceConfig G X Y).IsLinear := by
  rw [IncidenceConfig.isLinear_iff_not_hasSharedPair]
  intro hpair
  refine hno4 ((hasSimpleCycleOfLength_graphIncidenceConfig_iff hXY hcover 4).mpr ?_)
  exact (IncidenceConfig.hasSimpleCycleOfLength_four_iff_hasSharedPair _).mpr hpair

/-- **A simple `C₆` yields a Berge triangle.**  A simple `6`-cycle of `G` transports to the Levi
graph of the extracted configuration, where
`IncidenceConfig.bergeTriangle_of_hasSimpleCycleOfLength_six` reads off the three points and
three block indices of the Berge triangle. -/
theorem nonempty_bergeTriangle_of_hasSimpleCycleOfLength_six
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ)
    (h6 : HasSimpleCycleOfLength G 6) :
    Nonempty (BergeTriangle (graphIncidenceConfig G X Y)) :=
  IncidenceConfig.bergeTriangle_of_hasSimpleCycleOfLength_six _
    ((hasSimpleCycleOfLength_graphIncidenceConfig_iff hXY hcover 6).mp h6)

end ShortCycles

section SideCardinalities

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

omit [DecidableRel G.Adj] in
/-- The vertex type is the disjoint union of the two sides, so its cardinality is the sum of the
side cardinalities. -/
theorem card_eq_card_add_card_of_union_eq_univ
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ) :
    Fintype.card V = X.card + Y.card := by
  have h1 : Fintype.card V = (X ∪ Y).card := by rw [hcover, Finset.card_univ]
  rw [h1, Finset.card_union_of_disjoint (Finset.disjoint_coe.mp hXY.disjoint)]

omit [DecidableEq V] in
/-- **The two sides have equal cardinality.**  Under `G.IsRegularOfDegree 3` the sum of degrees
over `X` is `X.card * 3` and over `Y` is `Y.card * 3`; bipartiteness makes these sums equal, so
the common factor `3` cancels. -/
theorem card_eq_card_of_isRegularOfDegree
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hreg : G.IsRegularOfDegree 3) :
    X.card = Y.card := by
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq (G := G) (s := X) (t := Y) hXY
  have hX : ∑ v ∈ X, G.degree v = X.card * 3 := by
    rw [Finset.sum_congr rfl (fun v (_ : v ∈ X) => hreg v)]
    simp [Finset.sum_const, smul_eq_mul]
  have hY : ∑ w ∈ Y, G.degree w = Y.card * 3 := by
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ Y) => hreg w)]
    simp [Finset.sum_const, smul_eq_mul]
  have hmul : X.card * 3 = Y.card * 3 := hX.symm.trans (hsum.trans hY)
  exact Nat.mul_right_cancel (by norm_num : 0 < 3) hmul

/-- **Both sides have at most `29` vertices.**  A `3`-regular bipartite graph with at most `58`
vertices has equally many vertices on each side, so each side has at most `29`. -/
theorem card_le_twenty_nine_of_isRegularOfDegree
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ)
    (hreg : G.IsRegularOfDegree 3) (hcard : Fintype.card V ≤ 58) :
    X.card ≤ 29 ∧ Y.card ≤ 29 := by
  have hcardV : Fintype.card V = X.card + Y.card :=
    card_eq_card_add_card_of_union_eq_univ hXY hcover
  have heq : X.card = Y.card := card_eq_card_of_isRegularOfDegree hXY hreg
  omega

end SideCardinalities

section SideTypes

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : Finset V}

/-- **Both sides have at most `29` vertices**, stated for the point and block-index types rather
than for the underlying finsets. -/
theorem card_point_le_twenty_nine_and_card_block_le_twenty_nine_of_isRegularOfDegree
    (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hcover : X ∪ Y = Finset.univ)
    (hreg : G.IsRegularOfDegree 3) (hcard : Fintype.card V ≤ 58) :
    Fintype.card (Point X) ≤ 29 ∧ Fintype.card (Block Y) ≤ 29 := by
  obtain ⟨hX, hY⟩ := card_le_twenty_nine_of_isRegularOfDegree hXY hcover hreg hcard
  exact ⟨by rw [card_point_eq_card X]; exact hX, by rw [card_block_eq_card Y]; exact hY⟩

end SideTypes

end Erdos64