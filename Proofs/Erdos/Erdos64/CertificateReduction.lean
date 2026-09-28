/-
Erdős–Gyárfás problem 64 — the counterexample-to-search-input bridge.

PROVENANCE.  arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for Cubic Bipartite
Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026), Sections 2 ("Incidence
configurations and cycle translations") and 3.2 (the triangle-rooted reduced search).  Graphs here
are finite, undirected and simple.

SOURCE CLAIM BOUNDARY.  Section 2 translates graph cycles into incidence data: a `C₄` of a cubic
bipartite graph with specified bipartition is exactly a shared point-pair of the extracted
configuration, a `C₆` is exactly a Berge triangle, and more generally a simple graph cycle of
length `2k` is exactly a Berge cycle of *length* `k` of the extracted configuration (a cyclic
sequence of `k` distinct blocks and `k` distinct points with consecutive incidences, realised as a
simple `C_{2k}` of the Levi graph).  Section 3.1's Moore reduction then turns a cubic bipartite
graph with no `C₄` and no `C₈` on at most `58` vertices into a triangle-rooted linear `3`-uniform
`3`-regular configuration; Section 3.2 runs an exhaustive restricted-growth search over the
triangle-rooted configurations that additionally avoid the Berge cycles corresponding to graph
`C₈` and `C₁₆`.

WHAT IS FORMALIZED HERE.  Exactly the missing information that the exhaustive search consumes,
stated as a reusable predicate plus the reduction from a graph hypothesis to a search input:

* `IncidenceConfig.HasBergeCycleLength C k` — the predicate "the configuration `C` has a Berge
  cycle of length `k`", **defined through the Levi graph** as the existence of a simple cycle of
  length `2 * k` (`HasSimpleCycleOfLength C.leviGraph (2 * k)`).  It is a Levi-graph definition,
  not an explicit indexed incidence-sequence witness, and no separate generic equivalence between
  the two presentations is claimed here; the four small cases `k = 2, 3, 4, 8` are recorded as
  unfolding lemmas only.  In particular `k = 4` is graph `C₈` and `k = 8` is graph `C₁₆`.

* `TriangleSearchInput G` — the public search input.  It retains the whole adopted
  `TriangleRootedConfiguration G` through its `model` field (explicit covering bipartition, the
  extracted configuration, `3`-uniformity, `3`-regularity, linearity, a Berge triangle, and both
  `≤ 29` side bounds) and adds exactly the two cycle exclusions searched by the artifact: no Berge
  cycle of length `4` and no Berge cycle of length `8` of `model.config`.

* `exists_triangleSearchInput_of_cubic_bipartite` — from a finite simple cubic bipartite graph
  `G` on a nonempty vertex type with no simple `C₄`, `C₈`, `C₁₆` and `Fintype.card V ≤ 58`, the
  search input exists.  The triangle-rooted configuration `model` comes from the adopted
  `exists_triangleRootedConfiguration_of_cubic_bipartite`; the two exclusions are the exact
  graph↔Levi cycle transports of `hno8` and `hno16` through `model`'s own bipartition and cover,
  normalising `2 * 4 = 8` and `2 * 8 = 16`.  Linearity already rules out graph `C₄` / repeated
  point-pairs, so only `C₈` and `C₁₆` need to be added.

NOT FORMALIZED HERE.  This file formalizes **only** the reduction to a triangle-rooted search
input for a hypothetical cubic bipartite `C₄`/`C₈`/`C₁₆`-free graph on at most `58` vertices.  It
does **not** normalize the two labelled root orbits of Section 3.2, does **not** formalize the
restricted-growth coverage or the static witness certificates of the source's search, does **not**
implement any enumeration or emptiness check of that search, and does **not** prove the `60`-vertex
lower bound (`thm:main`, `cor:bound`) or the Erdős–Gyárfás conjecture.  The `≤ 29` fields remain
upper bounds on the two side sizes under the stated hypotheses, not a `60`-vertex statement.

SOURCE-LEVEL TERMINOLOGY.  Beware the factor of two: the source's graph `C₈` and graph `C₁₆` are
the Berge cycles of *length* `4` and `8` used by the search (equivalently Levi `C₈` and `C₁₆`);
`HasBergeCycleLength C 4` and `HasBergeCycleLength C 8` name the same objects as graph `C₈` and
graph `C₁₆`.
-/

import Erdos.Erdos64.TriangleReduction

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {P B V : Type u}

/-! ### Part A — Berge cycle lengths as Levi cycle lengths -/

namespace IncidenceConfig

/-- **Berge cycle of length `k`.**  An incidence configuration `C` has a Berge cycle of length `k`
when its Levi graph contains a simple cycle of length `2 * k`.  This is the *definition* used
throughout: a Berge cycle is presented through the Levi graph rather than as an explicit cyclic
sequence of `k` distinct blocks and `k` distinct points with consecutive incidences, and no
separate generic equivalence between the two presentations is proved here.  The length convention
is `2 * k` (twice the Berge length), matching the source's translation of a graph cycle of even
length `2k` into a Berge cycle of length `k`; in particular Berge length `4` is graph/Levi `C₈`
and Berge length `8` is graph/Levi `C₁₆`. -/
def HasBergeCycleLength (C : IncidenceConfig P B) (k : Nat) : Prop :=
  HasSimpleCycleOfLength C.leviGraph (2 * k)

/-- The `k = 2` unfolding: a Berge cycle of length `2` is a simple `C₄` of the Levi graph. -/
theorem hasBergeCycleLength_two_iff (C : IncidenceConfig P B) :
    C.HasBergeCycleLength 2 ↔ HasSimpleCycleOfLength C.leviGraph 4 :=
  Iff.rfl

/-- The `k = 3` unfolding: a Berge cycle of length `3` is a Berge triangle, i.e. a simple `C₆` of
the Levi graph. -/
theorem hasBergeCycleLength_three_iff (C : IncidenceConfig P B) :
    C.HasBergeCycleLength 3 ↔ HasSimpleCycleOfLength C.leviGraph 6 :=
  Iff.rfl

/-- The `k = 4` unfolding: a Berge cycle of length `4` is a simple `C₈` of the Levi graph — the
source-level graph `C₈`. -/
theorem hasBergeCycleLength_four_iff (C : IncidenceConfig P B) :
    C.HasBergeCycleLength 4 ↔ HasSimpleCycleOfLength C.leviGraph 8 :=
  Iff.rfl

/-- The `k = 8` unfolding: a Berge cycle of length `8` is a simple `C₁₆` of the Levi graph — the
source-level graph `C₁₆`. -/
theorem hasBergeCycleLength_eight_iff (C : IncidenceConfig P B) :
    C.HasBergeCycleLength 8 ↔ HasSimpleCycleOfLength C.leviGraph 16 :=
  Iff.rfl

end IncidenceConfig

/-! ### Part B — the triangle-rooted search input -/

/-- **The triangle-rooted search input.**  This is the exact object handed to the source's
exhaustive search: a triangle-rooted linear `3`-uniform `3`-regular incidence configuration of the
adopted normal form together with the two Berge-cycle exclusions that the search enumerates under.
The entire reduction is retained through `model` — the explicit covering bipartition, the extracted
configuration `model.config`, `3`-uniformity, `3`-regularity, linearity, a `BergeTriangle`, and the
point/block bounds `≤ 29` are all available as projections of `model` — and the structure adds
exactly the two cycle exclusions, each stated about `model.config` itself:

* `noBergeFour` — no Berge cycle of length `4`, i.e. no simple `C₈` of `model.config.leviGraph`
  (the source-level graph `C₈`);
* `noBergeEight` — no Berge cycle of length `8`, i.e. no simple `C₁₆` of `model.config.leviGraph`
  (the source-level graph `C₁₆`).

The absence of graph `C₄` / repeated point-pairs needs no field here: it is already carried by
`model.linear`, by the exact `C₄`↔shared-pair translation of Section 2. -/
structure TriangleSearchInput (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] where
  /-- The adopted triangle-rooted normal form; all its fields are retained. -/
  model : TriangleRootedConfiguration G
  /-- The configuration carries no Berge cycle of length `4` (no Levi / graph `C₈`). -/
  noBergeFour : ¬ model.config.HasBergeCycleLength 4
  /-- The configuration carries no Berge cycle of length `8` (no Levi / graph `C₁₆`). -/
  noBergeEight : ¬ model.config.HasBergeCycleLength 8

/-! ### Part C — the graph↔Levi cycle transport for the model -/

/-- **Cycle transport for the model's own configuration.**  For the configuration `C.model.config`
extracted from `C`'s bipartition, a Berge cycle of length `k` is exactly a simple cycle of length
`n` in the original graph `G`, whenever `2 * k = n`.  This composes the definition of
`HasBergeCycleLength` with the partition isomorphism transport
`hasSimpleCycleOfLength_graphIncidenceConfig_iff`; the equation `2 * k = n` normalises the factor
of two (`2 * 4 = 8`, `2 * 8 = 16`). -/
theorem hasBergeCycleLength_iff_hasSimpleCycleOfLength
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : TriangleRootedConfiguration G) (k n : Nat) (hkn : 2 * k = n) :
    C.config.HasBergeCycleLength k ↔ HasSimpleCycleOfLength G n := by
  change HasSimpleCycleOfLength (graphIncidenceConfig G C.X C.Y).leviGraph (2 * k) ↔
    HasSimpleCycleOfLength G n
  rw [hkn]
  exact (hasSimpleCycleOfLength_graphIncidenceConfig_iff C.bipartiteWith C.cover n).symm

/-! ### Part D — the search input from a cubic bipartite counterexample -/

/-- **Existence of the triangle-rooted search input.**  Every finite simple cubic bipartite graph
on a nonempty vertex type with no simple `C₄`, no simple `C₈`, no simple `C₁₆` and at most `58`
vertices yields a `TriangleSearchInput`.

The triangle-rooted normal form `model` is produced by the adopted
`exists_triangleRootedConfiguration_of_cubic_bipartite` from `hV`, `hreg`, `hbip`, `hno4`, `hno8`
and `hcard`.  The two added exclusions are the transports
`hasBergeCycleLength_iff_hasSimpleCycleOfLength model 4 8` and `… model 8 16` of `hno8` and
`hno16` through `model`'s own bipartition and cover, with the arithmetic `2 * 4 = 8` and
`2 * 8 = 16` discharged by `norm_num`; both exclusions refer to exactly `model.config`.  Linearity
is inherited from `model` and needs no separate field. -/
theorem exists_triangleSearchInput_of_cubic_bipartite
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hV : Nonempty V)
    (hreg : G.IsRegularOfDegree 3)
    (hbip : G.IsBipartite)
    (hno4 : ¬ HasSimpleCycleOfLength G 4)
    (hno8 : ¬ HasSimpleCycleOfLength G 8)
    (hno16 : ¬ HasSimpleCycleOfLength G 16)
    (hcard : Fintype.card V ≤ 58) :
    Nonempty (TriangleSearchInput G) := by
  obtain ⟨model⟩ :=
    exists_triangleRootedConfiguration_of_cubic_bipartite hV hreg hbip hno4 hno8 hcard
  refine ⟨{ model := model, noBergeFour := ?_, noBergeEight := ?_ }⟩
  · intro h
    exact hno8 ((hasBergeCycleLength_iff_hasSimpleCycleOfLength model 4 8 (by norm_num)).mp h)
  · intro h
    exact hno16 ((hasBergeCycleLength_iff_hasSimpleCycleOfLength model 8 16 (by norm_num)).mp h)

/-! ### Part E — search-input accessors -/

section Accessors

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The extracted configuration of a search input is linear, inherited through `model`. -/
theorem TriangleSearchInput.config_isLinear (S : TriangleSearchInput G) :
    S.model.config.IsLinear :=
  S.model.linear

/-- The extracted configuration of a search input is `3`-uniform, inherited through `model`. -/
theorem TriangleSearchInput.config_isThreeUniform (S : TriangleSearchInput G) :
    S.model.config.IsThreeUniform :=
  S.model.threeUniform

/-- The extracted configuration of a search input is `3`-regular, inherited through `model`. -/
theorem TriangleSearchInput.config_isThreeRegular (S : TriangleSearchInput G) :
    S.model.config.IsThreeRegular :=
  S.model.threeRegular

/-- The extracted configuration of a search input carries a Berge triangle, inherited through
`model`. -/
theorem TriangleSearchInput.nonempty_bergeTriangle (S : TriangleSearchInput G) :
    Nonempty (BergeTriangle S.model.config) :=
  S.model.triangle

/-- The point side of a search input has at most `29` elements, inherited through `model`. -/
theorem TriangleSearchInput.point_card_le (S : TriangleSearchInput G) :
    Fintype.card (Point S.model.X) ≤ 29 :=
  S.model.pointCard_le

/-- The block-index side of a search input has at most `29` elements, inherited through `model`. -/
theorem TriangleSearchInput.block_card_le (S : TriangleSearchInput G) :
    Fintype.card (Block S.model.Y) ≤ 29 :=
  S.model.blockCard_le

/-- The Levi graph of a search input's configuration is regular of degree `3`.  This is derived,
not merely inherited: `3`-uniformity and `3`-regularity of the configuration make every point and
every block-index vertex of `model.config.leviGraph` have degree `3`. -/
theorem TriangleSearchInput.leviGraph_isRegularOfDegree_three (S : TriangleSearchInput G) :
    S.model.config.leviGraph.IsRegularOfDegree 3 :=
  IncidenceConfig.isRegularOfDegree_three S.model.config
    S.model.threeUniform S.model.threeRegular

end Accessors

end Erdos64