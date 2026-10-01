/-
Erdős–Gyárfás problem 64 — fiber expansion: helper layer for the edge-expansion bridge.

CONTEXT. Let `Q` be a finite simple graph on a base type `I` and `G` a finite simple graph on a
type `V`, together with a surjection `pi : V → I`. Think of `G` as a *fiber expansion* of `Q`
along `pi`: every fiber `pi ⁻¹' {i}` is a nonempty connected induced subgraph of `G` with at most
`s` vertices (`s ≥ 1`), and every edge `ij` of `Q` is *witnessed* by an edge `vw` of `G` with
`pi v = i` and `pi w = j`. Extra edges of `G` are allowed, and the fibers may be connected
internally by extra edges.

MAIN RESULT. If `Q` has edge expansion at least `eta > 0` and maximum degree at most `d`,
then `G` has edge expansion at least `eta / (s * (eta + d + 1))`. No bound on the maximum
degree of `G` is required: the extra edges inside the fibers are what makes the fiber size `s`
enter the bound through the factor `s * (eta + d + 1)`.

STATUS OF THIS FILE. This module proves the definition and helper layers and the main bridge
`edgeExpands_of_fiberExpansion`:

* `EdgeCut G S` — the edge cut of a finite vertex set `S`, as the `Finset` of ordered pairs
  `(v, w)` with `v ∈ S`, `w ∉ S` and `G.Adj v w`: each undirected edge leaving `S` is recorded
  exactly once, in the orientation pointing out of `S`.
* `EdgeExpands G eta` — edge expansion in `min` form: `eta * min(|S|, |V \ S|) ≤ |EdgeCut G S|`
  for every finite `S`. This is equivalent to the usual half-order definition and avoids floors.
* `card_le_edgeCut_of_injective` — the witness-counting principle: an injective family of ordered
  pairs that all leave `S` has at most `|EdgeCut G S|` members. It is the counting engine used
  twice by the bridge (crossing edges of partial fibers; lifted edges of the base graph).
* `exists_adj_crossing_of_walk` and `exists_adj_crossing_of_connected_fiber` — induced
  connectedness of a fiber yields an edge of `G` inside that fiber running from `S` to outside
  `S`, whenever the fiber meets both. No crossing-edge hypothesis is assumed anywhere.
* `fiberFinset`, `fullFiber`, `emptyFiber`, `partialFiber` with `@[simp]` membership lemmas, the
  partition `mem_fullFiber_or_mem_partialFiber_or_mem_emptyFiber` (surjectivity of `pi`), the
  disjointness `disjoint_fullFiber_emptyFiber`, and `emptyFiber_subset_sdiff_fullFiber`.
* Fiber counting: `card_le_mul_card_add_card`, `card_le_mul_fullFiber_add_partialFiber`
  (`|S| ≤ s(|F| + |P|)`) and `card_compl_le_mul_emptyFiber_add_partialFiber`
  (`|V \ S| ≤ s(|E| + |P|)`).

* `card_partialFiber_le_edgeCut` counts one connected-fiber crossing edge for each partial fiber.
* `card_edgeCut_fullFiber_le` proves the quotient-cut estimate
  `|EdgeCut Q F| ≤ |EdgeCut G S| + d |P|` by separating edges ending at partial fibers.
* `min_card_le_mul_min_add` combines the two fiber-counting estimates.
* `edgeExpands_of_fiberExpansion` assembles these estimates over the reals and proves the stated
  expansion constant.

SCOPE AND CLAIM BOUNDARY. This module does not construct any fiber expansion, does not formalize
cycles, LPS graphs or subdivisions, proves no existence statement for counterexamples or expander
families, and makes no claim about the Erdős–Gyárfás conjecture or any high-girth theorem.
`EdgeExpands` is a definition; the ground-truth checks below certify that `EdgeCut` and
`EdgeExpands` are not vacuous and not trivially true. The hypotheses of the intended main result
are exactly those listed above, and none of them assumes a crossing edge of a partial fiber, an
inequality `|P| ≤ a/s`, or any counting inequality of the conclusion.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

set_option autoImplicit false

-- The helper layer uses a uniform instance context for the vertex and base types; individual
-- declarations may not use every instance, which is not an error here.
set_option linter.unusedSectionVars false

namespace Erdos64

open SimpleGraph

universe u

/-! ### Edge cuts and edge expansion -/

section EdgeCutDefs

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The **edge cut** of a finite vertex set `S` in a simple graph `G`: the finite set of ordered
pairs `(v, w)` of vertices with `v ∈ S`, `w ∉ S` and `G.Adj v w`. Every undirected edge joining
`S` to its complement is recorded exactly once, in the orientation pointing out of `S`. -/
def EdgeCut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (V × V) :=
  Finset.univ.filter fun e : V × V => e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2

/-- `G` has **edge expansion at least `eta`** if every finite vertex set `S` has at least
`eta * min(|S|, |V \ S|)` edges leaving it. This is the `min` form of the usual half-order
definition of edge expansion; the two forms are equivalent and the `min` form avoids floors. -/
def EdgeExpands (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ) : Prop :=
  ∀ S : Finset V,
    eta * min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) ≤ ((EdgeCut G S).card : ℝ)

/-- Membership in the edge cut, unfolded: the ordered pair `(v, w)` leaves `S` when `v ∈ S`,
`w ∉ S` and `v`, `w` are adjacent in `G`. -/
@[simp] theorem mem_edgeCut {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    {e : V × V} : e ∈ EdgeCut G S ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  simp [EdgeCut]

/-- An ordered pair in the edge cut of `S` is an edge of `G`. -/
theorem edgeCut_adj {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {e : V × V}
    (h : e ∈ EdgeCut G S) : G.Adj e.1 e.2 :=
  (mem_edgeCut.mp h).2.2

/-- The first vertex of an ordered pair in the edge cut of `S` lies in `S`. -/
theorem edgeCut_fst_mem {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {e : V × V}
    (h : e ∈ EdgeCut G S) : e.1 ∈ S :=
  (mem_edgeCut.mp h).1

/-- The second vertex of an ordered pair in the edge cut of `S` lies outside `S`. -/
theorem edgeCut_snd_notMem {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {e : V × V}
    (h : e ∈ EdgeCut G S) : e.2 ∉ S :=
  (mem_edgeCut.mp h).2.1

/-- **Witness counting.** If `g` is an injective assignment of ordered pairs of vertices that all
leave `S`, then there are at most `|EdgeCut G S|` such indices. This is the counting principle
used twice by the fiber-expansion bridge: once for the crossing edges of the partial fibers and
once for the lifted edges of the base graph. -/
theorem card_le_edgeCut_of_injective {α : Type u} [Fintype α] {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Finset V} {g : α → V × V} (hinj : Function.Injective g)
    (hmem : ∀ a, g a ∈ EdgeCut G S) : Fintype.card α ≤ (EdgeCut G S).card := by
  classical
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
    _ = ((Finset.univ : Finset α).image g).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (EdgeCut G S).card := Finset.card_le_card fun e he => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
        exact hmem a

end EdgeCutDefs

/-! ### Crossing edges of connected vertex sets -/

section WalkCrossing

variable {V : Type u}

/-- **Crossing edge of a walk.** If a walk of the graph induced by `T` starts inside `S` and ends
outside `S`, then some edge of the induced graph runs from `S` to its complement. -/
theorem exists_adj_crossing_of_walk {G : SimpleGraph V} [DecidableRel G.Adj] {T : Set V}
    {S : Finset V} {x y : ↥T} (p : (G.induce T).Walk x y) (hx : (x : V) ∈ S)
    (hy : (y : V) ∉ S) :
    ∃ u v : ↥T, G.Adj (u : V) (v : V) ∧ (u : V) ∈ S ∧ (v : V) ∉ S := by
  induction p with
  | nil => exact absurd hx hy
  | cons h p' ih =>
    rename_i u v w
    by_cases hv : ((v : ↥T) : V) ∈ S
    · exact ih hv hy
    · exact ⟨u, v, h, hx, hv⟩

end WalkCrossing

section FiberCrossing

variable {V : Type u} {I : Type u}

/-- **A partial fiber has a crossing edge.** If the induced graph on the fiber of `i` is connected
and the fiber meets both `S` and its complement, then `G` has an edge inside that fiber from `S` to
outside `S`. This is where induced connectedness of the fibers is used; the hypothesis that the
fiber is nonempty is part of `Connected`. -/
theorem exists_adj_crossing_of_connected_fiber {G : SimpleGraph V} [DecidableRel G.Adj]
    {pi : V → I} {S : Finset V} {i : I} (hconn : (G.induce {v | pi v = i}).Connected)
    (hin : ∃ v, pi v = i ∧ v ∈ S) (hout : ∃ v, pi v = i ∧ v ∉ S) :
    ∃ v w, pi v = i ∧ pi w = i ∧ G.Adj v w ∧ v ∈ S ∧ w ∉ S := by
  obtain ⟨a, ha, haS⟩ := hin
  obtain ⟨b, hb, hbS⟩ := hout
  obtain ⟨p⟩ := hconn ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨u, v, huv, huS, hvS⟩ := exists_adj_crossing_of_walk p haS hbS
  exact ⟨u, v, u.2, v.2, huv, huS, hvS⟩

end FiberCrossing

/-! ### The three kinds of fibers -/

section Fibers

variable {V : Type u} [Fintype V] [DecidableEq V] {I : Type u} [Fintype I] [DecidableEq I]

/-- The vertices of `V` whose image under `pi` is `i`. -/
def fiberFinset (pi : V → I) (i : I) : Finset V :=
  Finset.univ.filter fun v => pi v = i

/-- Membership in a fiber. -/
@[simp] theorem mem_fiberFinset {pi : V → I} {i : I} {v : V} :
    v ∈ fiberFinset pi i ↔ pi v = i := by
  simp [fiberFinset]

/-- The base vertices whose **whole fiber** is contained in `S`. -/
def fullFiber (pi : V → I) (S : Finset V) : Finset I :=
  Finset.univ.filter fun i => ∀ v, pi v = i → v ∈ S

/-- The base vertices whose fiber is disjoint from `S`. -/
def emptyFiber (pi : V → I) (S : Finset V) : Finset I :=
  Finset.univ.filter fun i => ∀ v, pi v = i → v ∉ S

/-- The base vertices whose fiber meets both `S` and its complement. -/
def partialFiber (pi : V → I) (S : Finset V) : Finset I :=
  Finset.univ.filter fun i =>
    (∃ v, pi v = i ∧ v ∈ S) ∧ (∃ v, pi v = i ∧ v ∉ S)

/-- Membership in `fullFiber`: the whole fiber of `i` lies in `S`. -/
@[simp] theorem mem_fullFiber {pi : V → I} {S : Finset V} {i : I} :
    i ∈ fullFiber pi S ↔ ∀ v, pi v = i → v ∈ S := by
  simp [fullFiber]

/-- Membership in `emptyFiber`: the fiber of `i` is disjoint from `S`. -/
@[simp] theorem mem_emptyFiber {pi : V → I} {S : Finset V} {i : I} :
    i ∈ emptyFiber pi S ↔ ∀ v, pi v = i → v ∉ S := by
  simp [emptyFiber]

/-- Membership in `partialFiber`: the fiber of `i` meets both `S` and its complement. -/
@[simp] theorem mem_partialFiber {pi : V → I} {S : Finset V} {i : I} :
    i ∈ partialFiber pi S ↔ (∃ v, pi v = i ∧ v ∈ S) ∧ (∃ v, pi v = i ∧ v ∉ S) := by
  simp [partialFiber]

/-- Every base vertex is full, partial or empty. This uses that fibers are nonempty, hence that
`pi` is surjective. -/
theorem mem_fullFiber_or_mem_partialFiber_or_mem_emptyFiber {pi : V → I} {S : Finset V}
    (hpi : Function.Surjective pi) (i : I) :
    i ∈ fullFiber pi S ∨ i ∈ partialFiber pi S ∨ i ∈ emptyFiber pi S := by
  obtain ⟨v, hv⟩ := hpi i
  by_cases hvS : v ∈ S
  · by_cases hall : ∀ w, pi w = i → w ∈ S
    · exact Or.inl (mem_fullFiber.mpr hall)
    · push Not at hall
      exact Or.inr (Or.inl (mem_partialFiber.mpr ⟨⟨v, hv, hvS⟩, hall⟩))
  · by_cases hall : ∀ w, pi w = i → w ∉ S
    · exact Or.inr (Or.inr (mem_emptyFiber.mpr hall))
    · push Not at hall
      exact Or.inr (Or.inl (mem_partialFiber.mpr ⟨hall, ⟨v, hv, hvS⟩⟩))

/-- A fiber cannot be simultaneously contained in `S` and disjoint from `S`, because fibers are
nonempty. -/
theorem disjoint_fullFiber_emptyFiber {pi : V → I} {S : Finset V}
    (hpi : Function.Surjective pi) : Disjoint (fullFiber pi S) (emptyFiber pi S) := by
  rw [Finset.disjoint_left]
  intro i hF hE
  obtain ⟨v, hv⟩ := hpi i
  rw [← hv] at hF hE
  exact (mem_emptyFiber.mp hE v rfl) (mem_fullFiber.mp hF v rfl)

/-- The base vertices of empty fibers are disjoint from the full ones. -/
theorem emptyFiber_subset_sdiff_fullFiber {pi : V → I} {S : Finset V}
    (hpi : Function.Surjective pi) : emptyFiber pi S ⊆ Finset.univ \ fullFiber pi S := by
  intro i hi
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩
  intro hF
  obtain ⟨v, hv⟩ := hpi i
  rw [← hv] at hF hi
  exact (mem_emptyFiber.mp hi v rfl) (mem_fullFiber.mp hF v rfl)

/-! ### Counting vertices through fibers -/

/-- The vertices of `S` lie in the fibers over the full and the partial base vertices: a fiber of
`S` either lies entirely in `S` (full) or has a vertex outside `S` (partial). -/
theorem subset_biUnion_fullFiber_union_partialFiber {pi : V → I} {S : Finset V} :
    S ⊆ (fullFiber pi S ∪ partialFiber pi S).biUnion (fiberFinset pi) := by
  intro v hv
  rw [Finset.mem_biUnion]
  refine ⟨pi v, ?_, mem_fiberFinset.mpr rfl⟩
  by_cases hall : ∀ w, pi w = pi v → w ∈ S
  · exact Finset.mem_union.mpr (Or.inl (mem_fullFiber.mpr hall))
  · push Not at hall
    exact Finset.mem_union.mpr (Or.inr (mem_partialFiber.mpr ⟨⟨v, rfl, hv⟩, hall⟩))

/-- The vertices outside `S` lie in the fibers over the empty and the partial base vertices. -/
theorem subset_biUnion_emptyFiber_union_partialFiber {pi : V → I} {S : Finset V} :
    Finset.univ \ S ⊆ (emptyFiber pi S ∪ partialFiber pi S).biUnion (fiberFinset pi) := by
  intro v hv
  rw [Finset.mem_sdiff] at hv
  rw [Finset.mem_biUnion]
  refine ⟨pi v, ?_, mem_fiberFinset.mpr rfl⟩
  by_cases hall : ∀ w, pi w = pi v → w ∉ S
  · exact Finset.mem_union.mpr (Or.inl (mem_emptyFiber.mpr hall))
  · push Not at hall
    exact Finset.mem_union.mpr (Or.inr (mem_partialFiber.mpr ⟨hall, ⟨v, rfl, hv.2⟩⟩))

/-- **Fiber counting.** If every fiber has at most `s` vertices, then any set of vertices that lies
in the fibers over `A ∪ B` has at most `s * (|A| + |B|)` elements. -/
theorem card_le_mul_card_add_card {pi : V → I} {s : ℕ}
    (hcard : ∀ i : I, (fiberFinset pi i).card ≤ s) {A B : Finset I} {T : Finset V}
    (hsub : T ⊆ (A ∪ B).biUnion (fiberFinset pi)) : T.card ≤ s * (A.card + B.card) := by
  classical
  calc T.card ≤ ((A ∪ B).biUnion (fiberFinset pi)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ A ∪ B, (fiberFinset pi i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A ∪ B, s := Finset.sum_le_sum fun i _ => hcard i
    _ = (A ∪ B).card * s := Finset.sum_const_nat fun _ _ => rfl
    _ ≤ (A.card + B.card) * s := Nat.mul_le_mul_right s (Finset.card_union_le A B)
    _ = s * (A.card + B.card) := Nat.mul_comm _ _

/-- The vertices of `S` number at most `s * (|F| + |P|)`. -/
theorem card_le_mul_fullFiber_add_partialFiber {pi : V → I} {S : Finset V} {s : ℕ}
    (hcard : ∀ i : I, (fiberFinset pi i).card ≤ s) :
    S.card ≤ s * ((fullFiber pi S).card + (partialFiber pi S).card) :=
  card_le_mul_card_add_card hcard subset_biUnion_fullFiber_union_partialFiber

/-- The vertices outside `S` number at most `s * (|E| + |P|)`. -/
theorem card_compl_le_mul_emptyFiber_add_partialFiber {pi : V → I} {S : Finset V} {s : ℕ}
    (hcard : ∀ i : I, (fiberFinset pi i).card ≤ s) :
    (Finset.univ \ S).card ≤ s * ((emptyFiber pi S).card + (partialFiber pi S).card) :=
  card_le_mul_card_add_card hcard subset_biUnion_emptyFiber_union_partialFiber

end Fibers

/-! ### The fiber-expansion bridge -/

/-- Each partial fiber supplies a distinct edge of the cut. -/
theorem card_partialFiber_le_edgeCut {V I : Type u} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {G : SimpleGraph V} [DecidableRel G.Adj]
    {pi : V → I} (hconn : ∀ i, (G.induce {v | pi v = i}).Connected)
    (S : Finset V) :
    (partialFiber pi S).card ≤ (EdgeCut G S).card := by
  classical
  let g : ↥(partialFiber pi S) → V × V := fun i =>
    let h := exists_adj_crossing_of_connected_fiber (hconn i.1)
      (mem_partialFiber.mp i.2).1 (mem_partialFiber.mp i.2).2
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  have hg (i : ↥(partialFiber pi S)) :
      pi (g i).1 = i.1 ∧ pi (g i).2 = i.1 ∧ G.Adj (g i).1 (g i).2 ∧
        (g i).1 ∈ S ∧ (g i).2 ∉ S := by
    exact Classical.choose_spec (Classical.choose_spec
      (exists_adj_crossing_of_connected_fiber (hconn i.1)
        (mem_partialFiber.mp i.2).1 (mem_partialFiber.mp i.2).2))
  have hinj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    rw [← (hg i).1, ← (hg j).1, hij]
  have hmem (i : ↥(partialFiber pi S)) : g i ∈ EdgeCut G S :=
    mem_edgeCut.mpr ⟨(hg i).2.2.2.1, (hg i).2.2.2.2, (hg i).2.2.1⟩
  have hcount := card_le_edgeCut_of_injective hinj hmem
  rw [Fintype.card_coe] at hcount
  exact hcount

/-- The quotient cut from the full fibers is bounded by the graph cut plus the incidences at
partial fibers. -/
theorem card_edgeCut_fullFiber_le {V I : Type u} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {G : SimpleGraph V} [DecidableRel G.Adj]
    {Q : SimpleGraph I} [DecidableRel Q.Adj] {pi : V → I} (hpi : Function.Surjective pi)
    (hlift : ∀ i j, Q.Adj i j → ∃ v w, pi v = i ∧ pi w = j ∧ G.Adj v w)
    (d : ℕ) (hdeg : ∀ i, Q.degree i ≤ d) (S : Finset V) :
    (EdgeCut Q (fullFiber pi S)).card ≤
      (EdgeCut G S).card + d * (partialFiber pi S).card := by
  classical
  let C := EdgeCut Q (fullFiber pi S)
  let P := partialFiber pi S
  let good := C.filter fun e => e.2 ∉ P
  let bad := C.filter fun e => e.2 ∈ P
  have hcover : C ⊆ good ∪ bad := by
    intro e he
    by_cases hp : e.2 ∈ P
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hp⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hp⟩))
  have hC : C.card ≤ good.card + bad.card := by
    calc
      C.card ≤ (good ∪ bad).card := Finset.card_le_card hcover
      _ ≤ good.card + bad.card := Finset.card_union_le _ _
  have hgood : good.card ≤ (EdgeCut G S).card := by
    let lift : ↥good → V × V := fun e =>
      let h := hlift e.1.1 e.1.2 (edgeCut_adj (Finset.mem_filter.mp e.2).1)
      (Classical.choose h, Classical.choose (Classical.choose_spec h))
    have hlift_spec (e : ↥good) :
        pi (lift e).1 = e.1.1 ∧ pi (lift e).2 = e.1.2 ∧ G.Adj (lift e).1 (lift e).2 := by
      exact Classical.choose_spec (Classical.choose_spec
        (hlift e.1.1 e.1.2 (edgeCut_adj (Finset.mem_filter.mp e.2).1)))
    have hinj : Function.Injective lift := by
      intro e f hef
      apply Subtype.ext
      apply Prod.ext
      · rw [← (hlift_spec e).1, ← (hlift_spec f).1, hef]
      · rw [← (hlift_spec e).2.1, ← (hlift_spec f).2.1, hef]
    have hmem (e : ↥good) : lift e ∈ EdgeCut G S := by
      have heC : e.1 ∈ C := (Finset.mem_filter.mp e.2).1
      have heF : e.1.1 ∈ fullFiber pi S := edgeCut_fst_mem heC
      have heNP : e.1.2 ∉ P := (Finset.mem_filter.mp e.2).2
      have heNF : e.1.2 ∉ fullFiber pi S := edgeCut_snd_notMem heC
      have heE : e.1.2 ∈ emptyFiber pi S := by
        rcases mem_fullFiber_or_mem_partialFiber_or_mem_emptyFiber hpi e.1.2 with hF | hP | hE
        · exact False.elim (heNF hF)
        · exact False.elim (heNP hP)
        · exact hE
      exact mem_edgeCut.mpr ⟨mem_fullFiber.mp heF _ (hlift_spec e).1,
        mem_emptyFiber.mp heE _ (hlift_spec e).2.1, (hlift_spec e).2.2⟩
    simpa using card_le_edgeCut_of_injective hinj hmem
  have hbad : bad.card ≤ d * P.card := by
    let incidence : Finset (I × I) := P.biUnion fun j =>
      (Q.neighborFinset j).image fun i => (i, j)
    have hsub : bad ⊆ incidence := by
      intro e he
      have heC : e ∈ C := (Finset.mem_filter.mp he).1
      have heP : e.2 ∈ P := (Finset.mem_filter.mp he).2
      rw [Finset.mem_biUnion]
      refine ⟨e.2, heP, Finset.mem_image.mpr ⟨e.1, ?_, rfl⟩⟩
      rw [Q.mem_neighborFinset]
      exact (Q.adj_comm _ _).mp (edgeCut_adj heC)
    calc
      bad.card ≤ incidence.card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ P, ((Q.neighborFinset j).image fun i => (i, j)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ P, d := Finset.sum_le_sum fun j _ =>
        (Finset.card_image_le.trans ((Q.card_neighborFinset_eq_degree j).trans_le (hdeg j)))
      _ = P.card * d := Finset.sum_const_nat fun _ _ => rfl
      _ = d * P.card := Nat.mul_comm _ _
  exact hC.trans (Nat.add_le_add hgood hbad)

/-- If two pairs of side sizes are bounded through fibers, their minima obey the same bound. -/
theorem min_card_le_mul_min_add {a b f e p s : ℕ}
    (ha : a ≤ s * (f + p)) (hb : b ≤ s * (e + p)) :
    min a b ≤ s * (min f e + p) := by
  rcases le_total f e with hfe | hef
  · calc
      min a b ≤ a := Nat.min_le_left _ _
      _ ≤ s * (f + p) := ha
      _ = s * (min f e + p) := by rw [Nat.min_eq_left hfe]
  · calc
      min a b ≤ b := Nat.min_le_right _ _
      _ ≤ s * (e + p) := hb
      _ = s * (min f e + p) := by rw [Nat.min_eq_right hef]

/-- Edge expansion survives replacement of every base vertex by a connected fiber of size at
most `s`, with the explicit loss `s * (eta + d + 1)`. -/
theorem edgeExpands_of_fiberExpansion {V I : Type u} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : SimpleGraph I) [DecidableRel Q.Adj] (pi : V → I) (hpi : Function.Surjective pi)
    (s d : ℕ) (hs : 1 ≤ s) (hfiber : ∀ i, (fiberFinset pi i).card ≤ s)
    (hconn : ∀ i, (G.induce {v | pi v = i}).Connected)
    (hdeg : ∀ i, Q.degree i ≤ d) (eta : ℝ) (heta : 0 < eta)
    (hQ : EdgeExpands Q eta)
    (hlift : ∀ i j, Q.Adj i j → ∃ v w, pi v = i ∧ pi w = j ∧ G.Adj v w) :
    EdgeExpands G (eta / ((s : ℝ) * (eta + (d : ℝ) + 1))) := by
  classical
  intro S
  let F := fullFiber pi S
  let E := emptyFiber pi S
  let P := partialFiber pi S
  let a : ℕ := min S.card (Finset.univ \ S).card
  let m : ℕ := min F.card ((Finset.univ \ F).card)
  let c : ℕ := (EdgeCut G S).card
  let q : ℕ := (EdgeCut Q F).card
  have hp : P.card ≤ c := card_partialFiber_le_edgeCut hconn S
  have hqcut : q ≤ c + d * P.card := card_edgeCut_fullFiber_le hpi hlift d hdeg S
  have hecomp : E.card ≤ (Finset.univ \ F).card :=
    Finset.card_le_card (emptyFiber_subset_sdiff_fullFiber hpi)
  have hgeom : a ≤ s * (m + P.card) := by
    apply min_card_le_mul_min_add
    · exact card_le_mul_fullFiber_add_partialFiber hfiber
    · exact (card_compl_le_mul_emptyFiber_add_partialFiber hfiber).trans
        (Nat.mul_le_mul_left s (Nat.add_le_add_right hecomp P.card))
  have hqexp : eta * (m : ℝ) ≤ (q : ℝ) := by simpa [m, q] using hQ F
  have hpR : (P.card : ℝ) ≤ (c : ℝ) := by exact_mod_cast hp
  have hqcutR : (q : ℝ) ≤ (c : ℝ) + (d : ℝ) * (P.card : ℝ) := by exact_mod_cast hqcut
  have hgeomR : (a : ℝ) ≤ (s : ℝ) * ((m : ℝ) + (P.card : ℝ)) := by
    exact_mod_cast hgeom
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hcR : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hmain : eta * (a : ℝ) ≤ (s : ℝ) * (eta + (d : ℝ) + 1) * (c : ℝ) := by
    calc
      eta * (a : ℝ) ≤ eta * ((s : ℝ) * ((m : ℝ) + (P.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hgeomR heta.le
      _ = (s : ℝ) * (eta * (m : ℝ) + eta * (P.card : ℝ)) := by ring
      _ ≤ (s : ℝ) * (((c : ℝ) + (d : ℝ) * (P.card : ℝ)) +
          eta * (P.card : ℝ)) := by
        gcongr
        exact hqexp.trans hqcutR
      _ ≤ (s : ℝ) * (((c : ℝ) + (d : ℝ) * (c : ℝ)) + eta * (c : ℝ)) := by
        gcongr
      _ = (s : ℝ) * (eta + (d : ℝ) + 1) * (c : ℝ) := by ring
  have hden : 0 < (s : ℝ) * (eta + (d : ℝ) + 1) := by positivity
  change (eta / ((s : ℝ) * (eta + (d : ℝ) + 1))) *
    (min S.card (Finset.univ \ S).card : ℝ) ≤ ((EdgeCut G S).card : ℝ)
  have hacast : (a : ℝ) = min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) := by
    simp only [a, Nat.cast_min]
  rw [← hacast]
  change (eta / ((s : ℝ) * (eta + (d : ℝ) + 1))) * (a : ℝ) ≤ (c : ℝ)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  calc
    eta * (a : ℝ) ≤ (s : ℝ) * (eta + (d : ℝ) + 1) * (c : ℝ) := hmain
    _ = (c : ℝ) * ((s : ℝ) * (eta + (d : ℝ) + 1)) := by ring

/-! ### Ground truth for the definitions -/

/-- Ground-truth check: in the complete graph on `Fin 2` the edge cut of `{0}` is the single
ordered pair `(0, 1)`. -/
example : EdgeCut (⊤ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2)) =
    ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by decide

/-- Ground-truth check: in the edgeless graph on `Fin 2` the edge cut of `{0}` is empty. -/
example : EdgeCut (⊥ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2)) =
    (∅ : Finset (Fin 2 × Fin 2)) := by decide

/-- Ground-truth check: the edge cut of the full vertex set is empty, since no ordered pair has
its second coordinate outside `univ`. -/
example {G : SimpleGraph (Fin 2)} [DecidableRel G.Adj] :
    EdgeCut G (Finset.univ : Finset (Fin 2)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  exact (edgeCut_snd_notMem he) (Finset.mem_univ e.2)

/-- Ground-truth check: `EdgeExpands` is not trivially true. The edgeless graph on `Fin 2` has no
edge expansion at `1`, because the set `{0}` cuts no edge while `min(|{0}|, |{1}|) = 1`. -/
theorem not_edgeExpands_bot_fin_two : ¬ EdgeExpands (⊥ : SimpleGraph (Fin 2)) 1 := by
  intro h
  have h0 := h ({0} : Finset (Fin 2))
  have hcut : EdgeCut (⊥ : SimpleGraph (Fin 2)) ({0} : Finset (Fin 2)) = ∅ := by decide
  have hcard : ({0} : Finset (Fin 2)).card = 1 := by decide
  have hcomp : (Finset.univ \ ({0} : Finset (Fin 2))).card = 1 := by decide
  rw [hcut, hcard, hcomp, min_self] at h0
  norm_num at h0

end Erdos64
