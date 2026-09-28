/-
Erdős–Gyárfás problem 64 — the triangle-rooted reduction for cubic bipartite graphs.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic
Bipartite Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Sections 2
("Incidence configurations and cycle translations") and 3.1 ("The edge-rooted Moore reduction",
Lemma `lem:moore` / Lemma 8).  Graphs here are finite, undirected and simple.

SOURCE CLAIM BOUNDARY.  The source fixes an explicit bipartition `(X, Y)` of a simple cubic
bipartite graph, reads off the incidence structure whose points are `X` and whose blocks are the
neighbourhoods of the vertices of `Y`, and observes that a `C₆` of the graph is exactly a Berge
triangle of that incidence structure while a `C₄` is a shared point-pair.  Section 3.1 then feeds a
graph with no `C₄` and no `C₈` and at most `58` vertices into the Moore reduction, producing a
`C₆`, hence a triangle-rooted linear `3`-uniform `3`-regular incidence configuration on at most
`29` points and `29` blocks.  That configuration is the input of the source's exhaustive
restricted-growth search.

WHAT IS FORMALIZED HERE.  Exactly the *existence* of that triangle-rooted configuration:

* `exists_finset_isBipartiteWith_cover_of_isRegularOfDegree_three` extracts an explicit finite
  bipartition `(X, Y)` with `X ∪ Y = univ` from a bare `G.IsBipartite` under
  `G.IsRegularOfDegree 3`.  The extraction uses only that every vertex has positive degree, hence
  lies in the support, which the bipartition covers; no connectedness is assumed, and the empty
  vertex type is a valid instance (regularity is vacuous and the cover is `∅ = univ`).
* `TriangleRootedConfiguration` packages the exact normal form: an explicit covering bipartition,
  the extracted `graphIncidenceConfig G X Y` together with its `3`-uniformity, `3`-regularity and
  linearity, a `BergeTriangle` of that configuration, and the two cardinality bounds
  `Fintype.card (Point X) ≤ 29`, `Fintype.card (Block Y) ≤ 29`.
* `exists_triangleRootedConfiguration_of_cubic_bipartite` assembles one from a finite cubic
  bipartite graph on at most `58` vertices with no simple `C₄` and no simple `C₈` and a
  nonempty vertex type.  The genuine `C₆` comes from the adopted Moore theorem
  `Erdos64.exists_six_cycle_of_cubic_bipartite` of `Erdos.Erdos64.CubicBipartite`; the remaining
  properties come from the explicit-partition bridge of `Erdos.Erdos64.GraphIncidence`.

NOT FORMALIZED HERE.  This is a structural reduction only.  It does **not** normalize the Berge
triangle into the source's two labelled root orbits, does **not** formalize the restricted-growth
coverage or the static witness certificates of the source's search, does **not** exclude any
triangle-rooted configuration, and does **not** prove the `60`-vertex bound (`thm:main`,
`cor:bound`) or the Erdős–Gyárfás conjecture.  The `≤ 29` fields are upper bounds on the two side
sizes under the stated hypotheses, not a `60`-vertex statement.
-/

import Erdos.Erdos64.GraphIncidence
import Erdos.Erdos64.CubicBipartite

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### Part A — a covering finite bipartition from bare bipartiteness -/

/-- **Covering finite bipartition from bare bipartiteness.**  A finite simple graph that is
bipartite and regular of degree `3` admits an explicit pair of finite sides `X`, `Y` which form a
bipartition and cover the vertex set.  The sides are the `Set.toFinset` images of the set
bipartition supplied by `SimpleGraph.IsBipartite.exists_isBipartiteWith`; coverage holds because
every vertex has degree `3 > 0`, hence lies in `G.support`, which the bipartition contains.  No
connectedness is assumed, and on the empty vertex type the conclusion is `∅ ∪ ∅ = univ`. -/
theorem exists_finset_isBipartiteWith_cover_of_isRegularOfDegree_three
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hbip : G.IsBipartite) :
    ∃ X Y : Finset V,
      G.IsBipartiteWith (X : Set V) (Y : Set V) ∧ X ∪ Y = Finset.univ := by
  classical
  obtain ⟨s, t, hst⟩ := hbip.exists_isBipartiteWith
  refine ⟨s.toFinset, t.toFinset, ?_, ?_⟩
  · simpa only [Set.coe_toFinset] using hst
  · apply Finset.eq_univ_of_forall
    intro v
    have hvdeg : 0 < G.degree v := by
      rw [hreg.degree_eq]
      norm_num
    have hvsupp : v ∈ G.support :=
      (G.degree_pos_iff_mem_support v).mp hvdeg
    have hvst : v ∈ s ∪ t := isBipartiteWith_support_subset hst hvsupp
    have hvst' : v ∈ s ∨ v ∈ t := by
      simpa only [Set.mem_union] using hvst
    rcases hvst' with hvs | hvt
    · exact Finset.mem_union.mpr (Or.inl (by simpa only [Set.mem_toFinset] using hvs))
    · exact Finset.mem_union.mpr (Or.inr (by simpa only [Set.mem_toFinset] using hvt))

/-! ### Part B — the triangle-rooted incidence normal form -/

/-- **Triangle-rooted cubic bipartite configuration.**  The exact normal form produced by the
reduction: an explicit covering bipartition `(X, Y)` of `G`, the extracted incidence configuration
`graphIncidenceConfig G X Y` (points `X`, block indices `Y`) with its `3`-uniformity,
`3`-regularity and linearity, a `BergeTriangle` of that configuration, and the two side-size
bounds `≤ 29`.

Every field is retained information: the bipartition and its cover, the three structural
predicates of the extracted configuration, the triangle, and both cardinality bounds.  The
configuration is recoverable through `TriangleRootedConfiguration.config`. -/
structure TriangleRootedConfiguration (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] where
  /-- The point side of the explicit covering bipartition. -/
  X : Finset V
  /-- The block-index side of the explicit covering bipartition. -/
  Y : Finset V
  /-- The two sides form a bipartition of `G`. -/
  bipartiteWith : G.IsBipartiteWith (X : Set V) (Y : Set V)
  /-- The two sides cover every vertex. -/
  cover : X ∪ Y = Finset.univ
  /-- The extracted configuration is `3`-uniform: every block has three points. -/
  threeUniform : (graphIncidenceConfig G X Y).IsThreeUniform
  /-- The extracted configuration is `3`-regular: every point lies in three indexed blocks. -/
  threeRegular : (graphIncidenceConfig G X Y).IsThreeRegular
  /-- The extracted configuration is linear: distinct blocks share at most one point. -/
  linear : (graphIncidenceConfig G X Y).IsLinear
  /-- The extracted configuration carries a Berge triangle. -/
  triangle : Nonempty (BergeTriangle (graphIncidenceConfig G X Y))
  /-- The point side has at most `29` elements. -/
  pointCard_le : Fintype.card (Point X) ≤ 29
  /-- The block-index side has at most `29` elements. -/
  blockCard_le : Fintype.card (Block Y) ≤ 29

/-- The incidence configuration underlying a triangle-rooted configuration: the explicit
`graphIncidenceConfig` extracted from its bipartition. -/
def TriangleRootedConfiguration.config {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (C : TriangleRootedConfiguration G) :
    IncidenceConfig (Point C.X) (Block C.Y) :=
  graphIncidenceConfig G C.X C.Y

/-- **Existence of the triangle-rooted configuration.**  Every finite simple cubic bipartite graph
on at most `58` vertices with no simple `C₄` and no simple `C₈`, with a nonempty vertex type,
carries a triangle-rooted linear `3`-uniform `3`-regular incidence configuration on at most `29`
points and at most `29` blocks.

The nonemptiness guard `hV` makes the source's standard nonempty-graph convention explicit, since
`G.IsRegularOfDegree 3` is vacuous on the empty vertex type.  The `C₆` is produced by the adopted
Moore theorem `exists_six_cycle_of_cubic_bipartite`, whose exact function hypotheses are read off
from `hno4` and `hno8`; the bipartition comes from Part A; the structural predicates, the Berge
triangle and the two bounds come from the explicit-partition bridge.  This establishes existence
only — it does not normalize the triangle into root orbits, run the restricted-growth search, or
prove the `60`-vertex bound. -/
theorem exists_triangleRootedConfiguration_of_cubic_bipartite
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hV : Nonempty V)
    (hreg : G.IsRegularOfDegree 3)
    (hbip : G.IsBipartite)
    (hno4 : ¬ HasSimpleCycleOfLength G 4)
    (hno8 : ¬ HasSimpleCycleOfLength G 8)
    (hcard : Fintype.card V ≤ 58) :
    Nonempty (TriangleRootedConfiguration G) := by
  classical
  obtain ⟨X, Y, hXY, hcover⟩ :=
    exists_finset_isBipartiteWith_cover_of_isRegularOfDegree_three hreg hbip
  have h4 : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≠ 4 := by
    intro x c hc hlen
    exact hno4 ⟨x, c, hc, hlen⟩
  have h8 : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≠ 8 := by
    intro x c hc hlen
    exact hno8 ⟨x, c, hc, hlen⟩
  obtain ⟨x, c, hc, hlen⟩ :=
    exists_six_cycle_of_cubic_bipartite hV hreg hbip h4 h8 hcard
  have h6 : HasSimpleCycleOfLength G 6 := ⟨x, c, hc, hlen⟩
  obtain ⟨hXcard, hYcard⟩ :=
    card_point_le_twenty_nine_and_card_block_le_twenty_nine_of_isRegularOfDegree
      hXY hcover hreg hcard
  exact ⟨{
    X := X
    Y := Y
    bipartiteWith := hXY
    cover := hcover
    threeUniform := isThreeUniform_of_isRegularOfDegree hXY hreg
    threeRegular := isThreeRegular_of_isRegularOfDegree hXY hreg
    linear := isLinear_of_not_hasSimpleCycleOfLength_four hXY hcover hno4
    triangle := nonempty_bergeTriangle_of_hasSimpleCycleOfLength_six hXY hcover h6
    pointCard_le := hXcard
    blockCard_le := hYcard }⟩

end Erdos64