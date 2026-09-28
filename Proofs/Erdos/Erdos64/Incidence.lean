/-
Erdős–Gyárfás problem 64 — incidence configurations and short-cycle translations.

PROVENANCE. arXiv:2608.02675, Julius Tranquilli, "A 60-Vertex Lower Bound for
Cubic Bipartite Counterexamples to the Erdős–Gyárfás Conjecture" (2 August 2026),
Section 2 ("Incidence configurations and cycle translations"), Proposition
`prop:incidence` together with the translation lemmas `lem:c4` (`C₄`) and the
Berge-cycle material surrounding them.  Graphs here are finite, undirected and
simple.

SOURCE CLAIM BOUNDARY.  The source's Section 2 records the following.

* Every connected simple cubic bipartite graph with specified bipartition
  `(X, Y)` determines, and is determined by, a `3`-uniform, `3`-regular
  incidence structure on the point set `X` indexed by the block indices `Y`:
  the block of `y` is `N_G(y)`.  The correspondence is between connected finite
  structures whose two sides carry equally many point and indexed-block
  vertices, and holds up to natural relabeling.  Distinct vertices of `Y` stay
  distinct block indices even when two of them have the same neighborhood;
  incidences are a Boolean (decidable) relation.

* In such a structure the incidence ("Levi") graph on `Sum P B` has an edge
  `x – y` exactly when the point `x` lies in the block indexed by `y`; its two
  kinds of vertices form a bipartition.

* (`lem:c4`) The Levi graph contains a simple `4`-cycle if and only if two
  distinct blocks contain the same pair of points; hence linearity is exactly
  the absence of `C₄`.

* A Berge cycle of length `k ≥ 3` is a cyclic sequence of distinct blocks
  `B₀, …, B_{k-1}` and distinct points `p₀, …, p_{k-1}` with `pᵢ ∈ Bᵢ ∩ B_{i+1}`
  (indices modulo `k`), equivalently a simple `C_{2k}` in the Levi graph; in
  particular a `C₆` is a Berge triangle.

This module does not formalize the graph→configuration reading of that
correspondence.  It proves only the configuration→Levi construction and the
listed local translations; the graph→configuration direction and a full
bijection between graphs and incidence configurations are not established
here.

WHAT IS FORMALIZED HERE.  Only that translation layer, as a reusable formal
object for later Lean-checked search:

* `IncidenceConfig P B` — an incidence configuration storing each indexed
  block as a `Finset P`.  The structure is universe-polymorphic and does not
  assume `P` or `B` finite; the source application uses finite `P` and `B`, and
  the reusable API imposes finiteness only on the declarations that require it.
  The incidence relation `p ∈ C.blocks b` is decidable given `[DecidableEq P]`
  (via `Finset` membership).  Block *indices* remain distinct even when
  neighborhoods coincide; nothing in this file identifies equal-neighborhood
  block indices.

* `IncidenceConfig.leviGraph` — the Levi simple graph on `Sum P B`, with edges
  exactly the incident point/block-index pairs, and
  `IncidenceConfig.leviGraph_isBipartiteWith` exhibiting the bipartition
  `Set.range Sum.inl` / `Set.range Sum.inr` (whence
  `IncidenceConfig.leviGraph_isBipartite`).

* `IncidenceConfig.IsThreeUniform`, `IncidenceConfig.IsThreeRegular` and
  `IncidenceConfig.IsLinear` — the three structural predicates, with
  `IncidenceConfig.isRegularOfDegree_three` proving that uniformity plus
  regularity makes the Levi graph `IsRegularOfDegree 3` (both `Sum` cases are
  handled separately, so equal-neighborhood block indices are still counted as
  distinct vertices).

* `IncidenceConfig.hasSimpleCycleOfLength_four_iff_hasSharedPair` — the full
  `C₄` translation of `lem:c4`, together with the one-way consequence
  `IncidenceConfig.not_hasSimpleCycleOfLength_four_of_isLinear` used by search:
  linearity rules out a simple `4`-cycle.

* `Erdos64.BergeTriangle` and
  `IncidenceConfig.BergeTriangle.hasSimpleCycleOfLength_six` — the Berge-triangle
  witness and the construction of an honest `SimpleGraph.Walk.IsCycle` of length
  `6` in the Levi graph.

NOT FORMALIZED HERE.  The source's exhaustive restricted-growth search, its
static witness certificates, its triangle-rooted orbit analysis, and the
`60`-vertex lower bound (`thm:main`, `cor:bound`) are **not** claimed or used
below.  In particular this module contains no enumeration of incidence
configurations and no `60`-vertex theorem; it supplies only the incidence /
short-cycle translation that such a search consumes.  The converse direction of
the `C₆` translation (every Levi `C₆` yields a Berge triangle) is likewise not
proved here; only the construction direction is.
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {P B : Type u}

section Incidence

variable [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

/-- An incidence configuration over a point type `P` and a block-index type `B`: each block
index `b` carries a `Finset P` of points, `C.blocks b`.  The structure is universe-polymorphic
and assumes nothing about `P` or `B`; finiteness enters only through the instances carried by the
declarations that need it (the source application uses finite `P` and `B`).

The incidence relation is the membership `p ∈ C.blocks b`, decidable given `[DecidableEq P]`;
block indices are *not* identified when their blocks coincide, so two equal-neighborhood block
indices are still two distinct vertices of the Levi graph. -/
structure IncidenceConfig (P B : Type u) where
  blocks : B → Finset P

namespace IncidenceConfig

/-- The (decidable) incidence relation: the point `p` lies in the block indexed by `b`. -/
def Inc (C : IncidenceConfig P B) (p : P) (b : B) : Prop :=
  p ∈ C.blocks b

instance (C : IncidenceConfig P B) (p : P) (b : B) : Decidable (C.Inc p b) :=
  inferInstanceAs (Decidable (p ∈ C.blocks b))

/-- The set of block indices whose block contains the point `p`. -/
def incidentBlocks (C : IncidenceConfig P B) (p : P) : Finset B :=
  Finset.univ.filter (fun b => p ∈ C.blocks b)

/-! ### The Levi graph -/

/-- The Levi graph of the incidence configuration: vertices are the points and the block indices,
and an edge joins a point to a block index exactly when the point lies in that block.  It is a
simple graph because an incidence is a Boolean relation: there is at most one edge between a point
and a block index, and no edge within either side. -/
def leviGraph (C : IncidenceConfig P B) : SimpleGraph (Sum P B) where
  Adj u v :=
    match u, v with
    | Sum.inl p, Sum.inr b => p ∈ C.blocks b
    | Sum.inr b, Sum.inl p => p ∈ C.blocks b
    | _, _ => False
  symm := ⟨by rintro (_ | _) (_ | _) h <;> simpa using h⟩
  loopless := ⟨by rintro (_ | _) h <;> simpa using h⟩

/-- A point vertex is adjacent to a block-index vertex in the Levi graph exactly when the point
lies in that block. -/
@[simp]
theorem leviGraph_adj_inl_inr (C : IncidenceConfig P B) (p : P) (b : B) :
    C.leviGraph.Adj (Sum.inl p) (Sum.inr b) ↔ p ∈ C.blocks b :=
  Iff.rfl

/-- A block-index vertex is adjacent to a point vertex in the Levi graph exactly when the point
lies in that block. -/
@[simp]
theorem leviGraph_adj_inr_inl (C : IncidenceConfig P B) (b : B) (p : P) :
    C.leviGraph.Adj (Sum.inr b) (Sum.inl p) ↔ p ∈ C.blocks b :=
  Iff.rfl

instance (C : IncidenceConfig P B) : DecidableRel C.leviGraph.Adj := fun u v => by
  rcases u with p | b <;> rcases v with q | b'
  · exact isFalse (by simp [leviGraph])
  · exact inferInstanceAs (Decidable (p ∈ C.blocks b'))
  · exact inferInstanceAs (Decidable (q ∈ C.blocks b))
  · exact isFalse (by simp [leviGraph])

/-- Adjacency from a point vertex: the neighbours of `Sum.inl p` are exactly the block-index
vertices `Sum.inr b` with `p ∈ C.blocks b`. -/
theorem leviGraph_adj_inl_iff (C : IncidenceConfig P B) (p : P) (v : Sum P B) :
    C.leviGraph.Adj (Sum.inl p) v ↔ ∃ b : B, v = Sum.inr b ∧ p ∈ C.blocks b := by
  constructor
  · intro h
    rcases v with q | b
    · simp [leviGraph] at h
    · exact ⟨b, rfl, h⟩
  · rintro ⟨b, rfl, hb⟩
    simpa [leviGraph] using hb

/-- Adjacency from a block-index vertex: the neighbours of `Sum.inr b` are exactly the point
vertices `Sum.inl p` with `p ∈ C.blocks b`. -/
theorem leviGraph_adj_inr_iff (C : IncidenceConfig P B) (b : B) (v : Sum P B) :
    C.leviGraph.Adj (Sum.inr b) v ↔ ∃ p : P, v = Sum.inl p ∧ p ∈ C.blocks b := by
  constructor
  · intro h
    rcases v with p | b'
    · exact ⟨p, rfl, h⟩
    · simp [leviGraph] at h
  · rintro ⟨p, rfl, hp⟩
    simpa [leviGraph] using hp

/-- The Levi graph is bipartite with the points on one side and the block indices on the other. -/
theorem leviGraph_isBipartiteWith (C : IncidenceConfig P B) :
    C.leviGraph.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨b, hb⟩
    exact Sum.inr_ne_inl hb
  mem_of_adj := by
    intro u v h
    rcases u with p | b <;> rcases v with q | b'
    · simp [leviGraph] at h
    · exact Or.inl ⟨⟨p, rfl⟩, ⟨b', rfl⟩⟩
    · exact Or.inr ⟨⟨b, rfl⟩, ⟨q, rfl⟩⟩
    · simp [leviGraph] at h

/-- The Levi graph is bipartite. -/
theorem leviGraph_isBipartite (C : IncidenceConfig P B) : C.leviGraph.IsBipartite :=
  C.leviGraph_isBipartiteWith.isBipartite

/-! ### Degrees of the Levi graph -/

/-- The neighbours of the point vertex `Sum.inl p` are exactly the block indices containing `p`,
transported along `Sum.inr`. -/
theorem neighborFinset_inl (C : IncidenceConfig P B) (p : P) :
    C.leviGraph.neighborFinset (Sum.inl p) =
      (C.incidentBlocks p).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  classical
  ext v
  rw [SimpleGraph.mem_neighborFinset]
  rcases v with q | b <;> simp [leviGraph, incidentBlocks]

/-- The neighbours of the block-index vertex `Sum.inr b` are exactly the points of the block `b`,
transported along `Sum.inl`. -/
theorem neighborFinset_inr (C : IncidenceConfig P B) (b : B) :
    C.leviGraph.neighborFinset (Sum.inr b) =
      (C.blocks b).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  ext v
  rw [SimpleGraph.mem_neighborFinset]
  rcases v with q | b' <;> simp [leviGraph]

/-- The degree of a point vertex is the number of blocks containing the point. -/
theorem degree_inl (C : IncidenceConfig P B) (p : P) :
    C.leviGraph.degree (Sum.inl p) = (C.incidentBlocks p).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_inl, Finset.card_map]

/-- The degree of a block-index vertex is the number of points in that block. -/
theorem degree_inr (C : IncidenceConfig P B) (b : B) :
    C.leviGraph.degree (Sum.inr b) = (C.blocks b).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_inr, Finset.card_map]

/-! ### Uniformity, regularity, linearity -/

/-- `3`-uniformity: every block contains exactly three points. -/
def IsThreeUniform (C : IncidenceConfig P B) : Prop :=
  ∀ b : B, (C.blocks b).card = 3

/-- `3`-regularity: every point lies in exactly three indexed blocks.  Block indices are counted
with multiplicity, so two equal-neighborhood block indices both count towards a shared point. -/
def IsThreeRegular (C : IncidenceConfig P B) : Prop :=
  ∀ p : P, (C.incidentBlocks p).card = 3

/-- Linearity: distinct block indices share at most one point.  Stated in the equivalent pointwise
form "two points common to both of two distinct blocks must coincide". -/
def IsLinear (C : IncidenceConfig P B) : Prop :=
  ∀ ⦃b₁ b₂ : B⦄, b₁ ≠ b₂ → ∀ ⦃p q : P⦄,
    p ∈ C.blocks b₁ → p ∈ C.blocks b₂ → q ∈ C.blocks b₁ → q ∈ C.blocks b₂ → p = q

/-- Two distinct block indices share two distinct points. -/
def HasSharedPair (C : IncidenceConfig P B) : Prop :=
  ∃ b₁ b₂ : B, b₁ ≠ b₂ ∧ ∃ p q : P, p ≠ q ∧
    p ∈ C.blocks b₁ ∧ p ∈ C.blocks b₂ ∧ q ∈ C.blocks b₁ ∧ q ∈ C.blocks b₂

/-- `3`-uniformity plus `3`-regularity makes the Levi graph regular of degree three.  Both sides of
`Sum P B` are handled separately, so equal-neighborhood block indices remain distinct vertices. -/
theorem isRegularOfDegree_three (C : IncidenceConfig P B) (hU : C.IsThreeUniform)
    (hR : C.IsThreeRegular) : C.leviGraph.IsRegularOfDegree 3 := by
  intro v
  rcases v with p | b
  · rw [degree_inl, hR p]
  · rw [degree_inr, hU b]

/-- Linear configurations admit no shared point pair. -/
theorem not_isLinear_of_hasSharedPair (C : IncidenceConfig P B) (h : C.HasSharedPair) :
    ¬ C.IsLinear := by
  rintro hlin
  obtain ⟨b₁, b₂, hb, p, q, hpq, hp₁, hp₂, hq₁, hq₂⟩ := h
  exact hpq (hlin hb hp₁ hp₂ hq₁ hq₂)

/-- A non-linear configuration has two distinct blocks sharing two distinct points. -/
theorem hasSharedPair_of_not_isLinear (C : IncidenceConfig P B) (h : ¬ C.IsLinear) :
    C.HasSharedPair := by
  by_contra hc
  apply h
  intro b₁ b₂ hb p q hp₁ hp₂ hq₁ hq₂
  by_contra hpq
  exact hc ⟨b₁, b₂, hb, p, q, hpq, hp₁, hp₂, hq₁, hq₂⟩

/-- Linearity is exactly the absence of a shared point pair. -/
theorem isLinear_iff_not_hasSharedPair (C : IncidenceConfig P B) :
    C.IsLinear ↔ ¬ C.HasSharedPair :=
  ⟨fun h hc => C.not_isLinear_of_hasSharedPair hc h,
   fun h => by
     by_contra hlin
     exact h (C.hasSharedPair_of_not_isLinear hlin)⟩

end IncidenceConfig

/-! ### Simple cycles of a fixed length -/

/-- A graph has a *simple cycle of length `n`*: a closed walk at some vertex that is a cycle
(`SimpleGraph.Walk.IsCycle`) and has length `n`. -/
def HasSimpleCycleOfLength {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n

namespace IncidenceConfig

/-! ### The `C₄` translation -/

/-- Two distinct blocks sharing two distinct points produce a simple `4`-cycle in the Levi graph,
namely `p – b₁ – q – b₂ – p`. -/
theorem hasSimpleCycleOfLength_four_of_hasSharedPair (C : IncidenceConfig P B)
    (h : C.HasSharedPair) : HasSimpleCycleOfLength C.leviGraph 4 := by
  obtain ⟨b₁, b₂, hb, p, q, hpq, hp₁, hp₂, hq₁, hq₂⟩ := h
  have e₀ : C.leviGraph.Adj (Sum.inl p) (Sum.inr b₁) := hp₁
  have e₁ : C.leviGraph.Adj (Sum.inr b₁) (Sum.inl q) :=
    (C.leviGraph_adj_inr_inl b₁ q).2 hq₁
  have e₂ : C.leviGraph.Adj (Sum.inl q) (Sum.inr b₂) := hq₂
  have e₃ : C.leviGraph.Adj (Sum.inr b₂) (Sum.inl p) :=
    (C.leviGraph_adj_inr_inl b₂ p).2 hp₂
  have hw₁ : (Walk.cons e₀ (Walk.cons e₁
      (Walk.nil : C.leviGraph.Walk (Sum.inl q) (Sum.inl q)))).IsPath := by
    simp [hpq]
  have hw₂ : (Walk.cons e₂ (Walk.cons e₃
      (Walk.nil : C.leviGraph.Walk (Sum.inl p) (Sum.inl p)))).IsPath := by
    simp [hpq.symm]
  have hdisj : (Walk.cons e₀ (Walk.cons e₁
      (Walk.nil : C.leviGraph.Walk (Sum.inl q) (Sum.inl q)))).support.tail.Disjoint
      (Walk.cons e₂ (Walk.cons e₃
      (Walk.nil : C.leviGraph.Walk (Sum.inl p) (Sum.inl p)))).support.tail := by
    simp [List.disjoint_left, hb, hpq, hpq.symm]
  refine ⟨Sum.inl p,
    (Walk.cons e₀ (Walk.cons e₁
      (Walk.nil : C.leviGraph.Walk (Sum.inl q) (Sum.inl q)))).append
      (Walk.cons e₂ (Walk.cons e₃
      (Walk.nil : C.leviGraph.Walk (Sum.inl p) (Sum.inl p)))), ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.isCycle_append hw₁ hw₂ hdisj (Or.inl (by simp))
  · simp [Walk.length_append]

/-- A simple `4`-cycle in the Levi graph yields two distinct blocks sharing two distinct points.
This is the extraction half of `lem:c4`: the four vertices of the cycle alternate between the two
sides of the bipartition, and the two blocks (respectively two points) are distinct because a cycle
has no repeated vertex. -/
theorem hasSharedPair_of_hasSimpleCycleOfLength_four (C : IncidenceConfig P B)
    (h : HasSimpleCycleOfLength C.leviGraph 4) : C.HasSharedPair := by
  obtain ⟨v, c, hc, hlen⟩ := h
  have hv0 : c.getVert 0 = v := c.getVert_zero
  have hv4 : c.getVert 4 = v := by
    have h' := c.getVert_length
    rw [hlen] at h'
    exact h'
  have hinj := hc.getVert_injOn'
  have h02 : c.getVert 0 ≠ c.getVert 2 := by
    intro hh
    have := hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hh
    omega
  have h13 : c.getVert 1 ≠ c.getVert 3 := by
    intro hh
    have := hinj (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hh
    omega
  have e01 := c.adj_getVert_succ (i := 0) (by omega)
  have e12 := c.adj_getVert_succ (i := 1) (by omega)
  have e23 := c.adj_getVert_succ (i := 2) (by omega)
  have e34 := c.adj_getVert_succ (i := 3) (by omega)
  rw [hv4] at e34
  rcases v with p₀ | b₀
  · rw [hv0] at e01
    obtain ⟨b₁, h1, hp₀b₁⟩ := (leviGraph_adj_inl_iff C p₀ (c.getVert 1)).mp e01
    rw [h1] at e12
    obtain ⟨p₂, h2, hp₂b₁⟩ := (leviGraph_adj_inr_iff C b₁ (c.getVert 2)).mp e12
    rw [h2] at e23
    obtain ⟨b₃, h3, hp₂b₃⟩ := (leviGraph_adj_inl_iff C p₂ (c.getVert 3)).mp e23
    rw [h3] at e34
    have hp₀b₃ : p₀ ∈ C.blocks b₃ := e34
    have hp : p₀ ≠ p₂ := fun hh => h02 (by rw [hv0, h2, hh])
    have hb : b₁ ≠ b₃ := fun hh => h13 (by rw [h1, h3, hh])
    exact ⟨b₁, b₃, hb, p₀, p₂, hp, hp₀b₁, hp₀b₃, hp₂b₁, hp₂b₃⟩
  · rw [hv0] at e01
    obtain ⟨p₁, h1, hp₁b₀⟩ := (leviGraph_adj_inr_iff C b₀ (c.getVert 1)).mp e01
    rw [h1] at e12
    obtain ⟨b₂, h2, hp₁b₂⟩ := (leviGraph_adj_inl_iff C p₁ (c.getVert 2)).mp e12
    rw [h2] at e23
    obtain ⟨p₃, h3, hp₃b₂⟩ := (leviGraph_adj_inr_iff C b₂ (c.getVert 3)).mp e23
    rw [h3] at e34
    have hp₃b₀ : p₃ ∈ C.blocks b₀ := e34
    have hb : b₀ ≠ b₂ := fun hh => h02 (by rw [hv0, h2, hh])
    have hp : p₁ ≠ p₃ := fun hh => h13 (by rw [h1, h3, hh])
    exact ⟨b₀, b₂, hb, p₁, p₃, hp, hp₁b₀, hp₁b₂, hp₃b₀, hp₃b₂⟩

/-- The `C₄` translation of `lem:c4`: the Levi graph contains a simple `4`-cycle if and only if two
distinct blocks contain the same pair of points. -/
theorem hasSimpleCycleOfLength_four_iff_hasSharedPair (C : IncidenceConfig P B) :
    HasSimpleCycleOfLength C.leviGraph 4 ↔ C.HasSharedPair :=
  ⟨C.hasSharedPair_of_hasSimpleCycleOfLength_four,
   C.hasSimpleCycleOfLength_four_of_hasSharedPair⟩

/-- Linearity rules out a simple `4`-cycle in the Levi graph.  This is the direction of the `C₄`
translation consumed by an incremental search: the first rejection test may be taken to be the
linearity test. -/
theorem not_hasSimpleCycleOfLength_four_of_isLinear (C : IncidenceConfig P B) (h : C.IsLinear) :
    ¬ HasSimpleCycleOfLength C.leviGraph 4 :=
  fun hc => C.not_isLinear_of_hasSharedPair
    (C.hasSimpleCycleOfLength_four_iff_hasSharedPair.mp hc) h

end IncidenceConfig

/-! ### The Berge triangle and its Levi `C₆` -/

/-- Cyclic successor on the three-element index type, used to phrase "indices modulo `3`". -/
def cyc3 (i : Fin 3) : Fin 3 := i + 1

/-- A Berge triangle of an incidence configuration: three pairwise distinct points
`p 0, p 1, p 2` and three pairwise distinct block indices `b 0, b 1, b 2` with consecutive
incidences `p i ∈ b i` and `p i ∈ b (i + 1)`, indices read modulo `3`.

This is the `k = 3` case of the source's Berge cycle.  What is proved here is only the implication
from a Berge triangle to a simple `6`-cycle of the Levi graph
(`BergeTriangle.hasSimpleCycleOfLength_six`); the converse, and the resulting equivalence between
this structure and a Levi `C₆`, are not established. -/
structure BergeTriangle (C : IncidenceConfig P B) where
  point : Fin 3 → P
  block : Fin 3 → B
  point_injective : Function.Injective point
  block_injective : Function.Injective block
  incident : ∀ i : Fin 3, point i ∈ C.blocks (block i) ∧ point i ∈ C.blocks (block (cyc3 i))

example : ∃ C : IncidenceConfig (Fin 3) (Fin 3),
    C.IsThreeUniform ∧ C.IsThreeRegular ∧ C.HasSharedPair ∧ Nonempty (BergeTriangle C) := by
  let C : IncidenceConfig (Fin 3) (Fin 3) := ⟨fun _ => Finset.univ⟩
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro b
    simp [C]
  · intro p
    simp [IncidenceConfig.incidentBlocks, C]
  · refine ⟨0, 1, by decide, 0, 1, by decide, ?_⟩
    simp [C]
  · refine ⟨⟨fun i => i, fun i => i, Function.injective_id, Function.injective_id, ?_⟩⟩
    intro i
    simp [C]

example : ∃ C : IncidenceConfig (Fin 3) (Fin 3), C.IsLinear := by
  let C : IncidenceConfig (Fin 3) (Fin 3) := ⟨fun b => {b}⟩
  refine ⟨C, ?_⟩
  intro b₁ b₂ hb p q hp₁ hp₂
  simp [C] at hp₁ hp₂
  exact (hb (hp₁.symm.trans hp₂)).elim

namespace IncidenceConfig

/-- Explicit Berge-triangle data produces a simple `6`-cycle of the Levi graph, namely
`p₀ – b₁ – p₁ – b₂ – p₂ – b₀ – p₀`.  The two halves are paths because all six vertices are
distinct, and their concatenation is a cycle. -/
theorem hasSimpleCycleOfLength_six_of_berge_data (C : IncidenceConfig P B)
    {p₀ p₁ p₂ : P} {b₀ b₁ b₂ : B}
    (hp₀₁ : p₀ ≠ p₁) (hp₁₂ : p₁ ≠ p₂) (hp₀₂ : p₀ ≠ p₂)
    (hb₀₁ : b₀ ≠ b₁) (hb₁₂ : b₁ ≠ b₂) (hb₀₂ : b₀ ≠ b₂)
    (h₀ : p₀ ∈ C.blocks b₁) (h₁ : p₁ ∈ C.blocks b₁) (h₂ : p₁ ∈ C.blocks b₂)
    (h₃ : p₂ ∈ C.blocks b₂) (h₄ : p₂ ∈ C.blocks b₀) (h₅ : p₀ ∈ C.blocks b₀) :
    HasSimpleCycleOfLength C.leviGraph 6 := by
  have e₀ : C.leviGraph.Adj (Sum.inl p₀) (Sum.inr b₁) := h₀
  have e₁ : C.leviGraph.Adj (Sum.inr b₁) (Sum.inl p₁) :=
    (C.leviGraph_adj_inr_inl b₁ p₁).2 h₁
  have e₂ : C.leviGraph.Adj (Sum.inl p₁) (Sum.inr b₂) := h₂
  have e₃ : C.leviGraph.Adj (Sum.inr b₂) (Sum.inl p₂) :=
    (C.leviGraph_adj_inr_inl b₂ p₂).2 h₃
  have e₄ : C.leviGraph.Adj (Sum.inl p₂) (Sum.inr b₀) := h₄
  have e₅ : C.leviGraph.Adj (Sum.inr b₀) (Sum.inl p₀) :=
    (C.leviGraph_adj_inr_inl b₀ p₀).2 h₅
  have hpath₁ : (Walk.cons e₀ (Walk.cons e₁ (Walk.cons e₂
      (Walk.nil : C.leviGraph.Walk (Sum.inr b₂) (Sum.inr b₂))))).IsPath := by
    simp [hp₀₁, hp₁₂, hb₀₁, hb₁₂]
  have hpath₂ : (Walk.cons e₃ (Walk.cons e₄ (Walk.cons e₅
      (Walk.nil : C.leviGraph.Walk (Sum.inl p₀) (Sum.inl p₀))))).IsPath := by
    simp [hp₀₁, hp₀₂, hp₀₂.symm, hb₀₂, hb₀₂.symm]
  have hdisj :
      (Walk.cons e₀ (Walk.cons e₁ (Walk.cons e₂
        (Walk.nil : C.leviGraph.Walk (Sum.inr b₂) (Sum.inr b₂))))).support.tail.Disjoint
      (Walk.cons e₃ (Walk.cons e₄ (Walk.cons e₅
        (Walk.nil : C.leviGraph.Walk (Sum.inl p₀) (Sum.inl p₀))))).support.tail := by
    simp [List.disjoint_left, hp₀₁, hp₀₁.symm, hp₁₂, hp₁₂.symm, hp₀₂, hp₀₂.symm,
      hb₀₁, hb₀₁.symm, hb₁₂, hb₁₂.symm, hb₀₂, hb₀₂.symm]
  refine ⟨Sum.inl p₀,
    (Walk.cons e₀ (Walk.cons e₁ (Walk.cons e₂
      (Walk.nil : C.leviGraph.Walk (Sum.inr b₂) (Sum.inr b₂))))).append
    (Walk.cons e₃ (Walk.cons e₄ (Walk.cons e₅
      (Walk.nil : C.leviGraph.Walk (Sum.inl p₀) (Sum.inl p₀))))), ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.isCycle_append hpath₁ hpath₂ hdisj (Or.inl (by simp))
  · simp [Walk.length_append]

/-- A Berge triangle yields a simple `6`-cycle of the Levi graph. -/
theorem BergeTriangle.hasSimpleCycleOfLength_six {C : IncidenceConfig P B}
    (T : BergeTriangle C) :
    HasSimpleCycleOfLength C.leviGraph 6 := by
  have hcyc0 : cyc3 (0 : Fin 3) = 1 := by decide
  have hcyc1 : cyc3 (1 : Fin 3) = 2 := by decide
  have hcyc2 : cyc3 (2 : Fin 3) = 0 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have i0 := T.incident 0
  have i1 := T.incident 1
  have i2 := T.incident 2
  rw [hcyc0] at i0
  rw [hcyc1] at i1
  rw [hcyc2] at i2
  exact hasSimpleCycleOfLength_six_of_berge_data C
    (T.point_injective.ne h01) (T.point_injective.ne h12) (T.point_injective.ne h02)
    (T.block_injective.ne (by decide : (0 : Fin 3) ≠ 1))
    (T.block_injective.ne (by decide : (1 : Fin 3) ≠ 2))
    (T.block_injective.ne (by decide : (0 : Fin 3) ≠ 2))
    i0.2 i1.1 i1.2 i2.1 i2.2 i0.1

end IncidenceConfig

end Incidence

end Erdos64