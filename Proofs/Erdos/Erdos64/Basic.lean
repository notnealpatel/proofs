/-
Erdős–Gyárfás problem 64 — foundational definitions.

PROVENANCE. erdosproblems.com/64 (Erdős–Gyárfás): "Does every graph of minimum
degree at least 3 contain a cycle of length a power of two?" The reduction layer
formalized here follows the opening of the proof of the main theorem of
arXiv:2609.28594 (Lemma 3.2, the minimal-counterexample analysis feeding
Theorem 3.7). Graphs are finite, undirected and simple throughout.

SCOPE. `Basic.lean` and `Reductions.lean` formalize the *reduction* content of
Lemma 3.2 only: the counterexample and lexicographic-minimality predicates, the
cycle-transport and degree bookkeeping lemmas, and the consequences of
minimality recorded there. They do **not** establish Theorem 3.7 of
arXiv:2609.28594 and do not prove the Erdős–Gyárfás conjecture. No existence
theorem for a minimal counterexample is proved here either:
`IsMinimalCounterexample` is a hypothesis consumed by the reduction lemmas, not
a derived fact.

EXACT CLAIM BOUNDARY. This file contains only definitions and their immediate
bookkeeping lemmas:

* `HasPowerOfTwoCycle G` — an honest simple-cycle witness: there is `k ≥ 2` and
  a closed walk `c` at some vertex with `c.IsCycle` (`SimpleGraph.Walk.IsCycle`
  = nonempty edge-simple circuit with no repeated vertex other than the base
  point) and `c.length = 2 ^ k`. The side condition `k ≥ 2` is the equivalent
  *simple-graph* formulation of "cycle of length a power of two", not a literal
  universal convention quoted from arXiv:2609.28594: a simple graph admits no
  cycle of length `2` at all, and `hasPowerOfTwoCycle_iff_exists_pow` shows that
  the quantifier over `k` may be dropped altogether, so both readings of the
  predicate coincide.

* `IsCounterexample G` — `V` is nonempty, every vertex has degree at least 3,
  and there is no power-of-two cycle. The `Nonempty V` conjunct is an explicit
  boundary guard: with an empty vertex type the degree condition is vacuous and
  the empty graph would otherwise qualify, and it is the unique lexicographic
  minimum. It is *not* a consequence of the source's hypotheses; it records
  that the source's "graph of minimum degree at least 3" is nonempty.
  `isCounterexample_iff_minDegree_ge_three` shows the predicate agrees with
  `3 ≤ G.minDegree ∧ ¬ HasPowerOfTwoCycle G`.

* `IsMinimalCounterexample G` — `G` is a counterexample, and every counterexample
  `H` on any finite vertex type in the *same universe* satisfies
  `LexLe (size G) (size H)` for the lexicographic order on
  `(number of vertices, number of edges)`. Minimality is stated directly as
  lexicographic minimality among actual `IsCounterexample`s; no conclusion of
  the reduction lemmas is smuggled into the definition, and no connectedness is
  assumed. The quantification over an arbitrary `Type u` is what makes the
  definition usable at induced-subtype vertex types (`↥({v}ᶜ : Set V)`) and at
  doubled vertex types such as `V × Bool`.

* `degreeThree`, `degreeGeFour` and the corresponding `Finset`s with `simp`
  membership lemmas.

* `LexLt`/`LexLe` on `ℕ × ℕ` with the order lemmas used by the reductions
  (irreflexivity, transitivity, and `LexLe a b ↔ ¬ LexLt b a`, which is the
  form in which minimality is applied).
-/

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### Power-of-two cycles -/

/-- A graph has a **power-of-two cycle** if it has a simple cycle of length `2 ^ k` for some
`k ≥ 2`: there are a vertex `v` and a closed walk `c` at `v` with `c.IsCycle` and
`c.length = 2 ^ k`. -/
def HasPowerOfTwoCycle (G : SimpleGraph V) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 2 ^ k

/-- A cycle of length `2` is impossible in a simple graph, since every cycle has length at least
three. Consequently the bound `k ≥ 2` in `HasPowerOfTwoCycle` is not a restriction: the predicate
agrees with the naive "contains a simple cycle of length `2 ^ k` for some `k`". -/
theorem hasPowerOfTwoCycle_iff_exists_pow (G : SimpleGraph V) :
    HasPowerOfTwoCycle G ↔
      ∃ k : ℕ, ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 2 ^ k := by
  constructor
  · rintro ⟨k, _, v, c, hc, hlen⟩
    exact ⟨k, v, c, hc, hlen⟩
  · rintro ⟨k, v, c, hc, hlen⟩
    have hthree : 3 ≤ c.length := hc.three_le_length
    have hk : 2 ≤ k := by
      rcases k with _ | _ | k <;> omega
    exact ⟨k, hk, v, c, hc, hlen⟩

/-- A graph with no power-of-two cycle has no cycle of length `2 ^ k`, `k ≥ 2`. -/
theorem not_hasPowerOfTwoCycle_iff (G : SimpleGraph V) :
    ¬ HasPowerOfTwoCycle G ↔
      ∀ k : ℕ, 2 ≤ k → ∀ v : V, ∀ c : G.Walk v v, c.IsCycle → c.length ≠ 2 ^ k := by
  constructor
  · intro h k hk v c hc hlen
    exact h ⟨k, hk, v, c, hc, hlen⟩
  · rintro h ⟨k, hk, v, c, hc, hlen⟩
    exact h k hk v c hc hlen

/-! ### Degree predicates -/

/-- `v` has degree exactly `3` in `G`. -/
def degreeThree (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) : Prop :=
  G.degree v = 3

/-- `v` has degree at least `4` in `G`; such vertices are called *high-degree* in the source. -/
def degreeGeFour (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) : Prop :=
  4 ≤ G.degree v

/-- Every vertex of `G` has degree at least `3`. -/
def minDegreeThreeUp (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∀ v : V, 3 ≤ G.degree v

/-- Unfolding lemma for `degreeThree`: it is exactly `G.degree v = 3`. -/
@[simp] theorem degreeThree_iff (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) :
    degreeThree G v ↔ G.degree v = 3 := Iff.rfl

/-- Unfolding lemma for `degreeGeFour`: it is exactly `4 ≤ G.degree v`. -/
@[simp] theorem degreeGeFour_iff (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) :
    degreeGeFour G v ↔ 4 ≤ G.degree v := Iff.rfl

/-- Unfolding lemma for `minDegreeThreeUp`: it is exactly the vertex-wise degree bound. -/
@[simp] theorem minDegreeThreeUp_iff (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    minDegreeThreeUp G ↔ ∀ v : V, 3 ≤ G.degree v := Iff.rfl

/-- A vertex fails to be high-degree exactly when its degree is at most three. -/
theorem not_degreeGeFour_iff (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) :
    ¬ degreeGeFour G v ↔ G.degree v ≤ 3 := by
  simp only [degreeGeFour, not_le]
  omega

/-- A vertex of degree at least three which is not high-degree has degree exactly three: the
negation of `degreeGeFour` upgrades the lower bound to equality. -/
theorem degreeThree_of_three_le_of_not_degreeGeFour (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] {v : V} (h3 : 3 ≤ G.degree v) (h4 : ¬ degreeGeFour G v) :
    degreeThree G v := by
  simp only [degreeGeFour, not_le] at h4
  simp only [degreeThree]
  omega

/-- Converse of `degreeThree_of_three_le_of_not_degreeGeFour`: a vertex of degree at least three
which does not have degree three is a high-degree vertex. -/
theorem degreeGeFour_of_three_le_of_not_degreeThree (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] {v : V} (h3 : 3 ≤ G.degree v) (h : ¬ degreeThree G v) :
    degreeGeFour G v := by
  simp only [degreeThree] at h
  simp only [degreeGeFour]
  omega

/-- The vertices of degree exactly three. -/
def degreeThreeFinset (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 3

/-- The vertices of degree at least four. -/
def degreeGeFourFinset (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 4 ≤ G.degree v

/-- Membership in `degreeThreeFinset` is `degreeThree`. -/
@[simp] theorem mem_degreeThreeFinset {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v : V} : v ∈ degreeThreeFinset G ↔ degreeThree G v := by
  simp [degreeThreeFinset, degreeThree]

/-- Membership in `degreeGeFourFinset` is `degreeGeFour`. -/
@[simp] theorem mem_degreeGeFourFinset {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v : V} : v ∈ degreeGeFourFinset G ↔ degreeGeFour G v := by
  simp [degreeGeFourFinset, degreeGeFour]

/-- The high-degree neighbours of `v`. -/
def highDegreeNeighbors (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => 4 ≤ G.degree w

/-- Membership in `highDegreeNeighbors G v`: a high-degree vertex adjacent to `v`. -/
@[simp] theorem mem_highDegreeNeighbors {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v w : V} : w ∈ highDegreeNeighbors G v ↔ degreeGeFour G w ∧ G.Adj v w := by
  simp [highDegreeNeighbors, and_comm]

/-- The high-degree neighbours of `v` are neighbours of `v`. -/
theorem highDegreeNeighbors_subset_neighborFinset (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] (v : V) :
    highDegreeNeighbors G v ⊆ G.neighborFinset v :=
  Finset.filter_subset _ _

/-! ### Counterexamples -/

/-- `G` is a counterexample to the Erdős–Gyárfás conjecture for this scale: `V` is nonempty,
every vertex has degree at least `3`, and `G` has no simple cycle of length `2 ^ k`, `k ≥ 2`. -/
def IsCounterexample (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  Nonempty V ∧ (∀ v : V, 3 ≤ G.degree v) ∧ ¬ HasPowerOfTwoCycle G

/-- `IsCounterexample` rewritten with the `minDegreeThreeUp` abbreviation. -/
theorem isCounterexample_iff (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    IsCounterexample G ↔
      Nonempty V ∧ minDegreeThreeUp G ∧ ¬ HasPowerOfTwoCycle G :=
  Iff.rfl

/-- The vertex type of a counterexample is nonempty. -/
theorem IsCounterexample.nonempty {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (h : IsCounterexample G) : Nonempty V :=
  h.1

/-- Every vertex of a counterexample has degree at least three. -/
theorem IsCounterexample.degree_ge_three {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (h : IsCounterexample G) (v : V) : 3 ≤ G.degree v :=
  h.2.1 v

/-- A counterexample has no power-of-two cycle. -/
theorem IsCounterexample.not_hasPowerOfTwoCycle {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] (h : IsCounterexample G) : ¬ HasPowerOfTwoCycle G :=
  h.2.2

/-- A counterexample has at least four vertices: a vertex of degree at least three has at least
three neighbours and is not adjacent to itself. -/
theorem IsCounterexample.card_verts_ge_four {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (h : IsCounterexample G) : 4 ≤ Fintype.card V := by
  obtain ⟨v⟩ := h.1
  have hdeg : 3 ≤ G.degree v := h.2.1 v
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  omega

/-- A counterexample has minimum degree at least three, in the `minDegree` formulation. -/
theorem IsCounterexample.minDegree_ge_three {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (h : IsCounterexample G) : 3 ≤ G.minDegree := by
  haveI : Nonempty V := h.1
  exact le_minDegree_of_forall_le_degree G 3 h.2.1

/-- The two natural formulations of "counterexample" agree: the vertex-wise degree condition
together with nonemptiness is equivalent to the minimum degree being at least three. In
particular `IsCounterexample` is not vacuous at the empty vertex type. -/
theorem isCounterexample_iff_minDegree_ge_three (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] :
    IsCounterexample G ↔ 3 ≤ G.minDegree ∧ ¬ HasPowerOfTwoCycle G := by
  constructor
  · intro h
    exact ⟨h.minDegree_ge_three, h.2.2⟩
  · rintro ⟨hmin, hcyc⟩
    refine ⟨?_, ?_, hcyc⟩
    · by_contra hV
      rw [not_nonempty_iff] at hV
      haveI : Subsingleton V := ⟨fun a _ => isEmptyElim a⟩
      rw [minDegree_of_subsingleton] at hmin
      omega
    · intro v
      exact hmin.trans (minDegree_le_degree G v)

/-! ### Lexicographic size and minimal counterexamples -/

/-- The lexicographic size of a finite graph: first the number of vertices, then the number of
edges. -/
def size (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : ℕ × ℕ :=
  (Fintype.card V, G.edgeFinset.card)

/-- Lexicographic strict order on `ℕ × ℕ`: compare first coordinates, then second coordinates. -/
def LexLt (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- Lexicographic non-strict order on `ℕ × ℕ`. -/
def LexLe (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-- `LexLt` is irreflexive. -/
theorem lexLt_irrefl (a : ℕ × ℕ) : ¬ LexLt a a := by
  simp [LexLt]

/-- `LexLt` is transitive. -/
theorem lexLt_trans {a b c : ℕ × ℕ} (hab : LexLt a b) (hbc : LexLt b c) : LexLt a c := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨c₁, c₂⟩ := c
  simp only [LexLt] at hab hbc ⊢
  omega

/-- `LexLe` is reflexive. -/
theorem lexLe_refl (a : ℕ × ℕ) : LexLe a a := by
  simp [LexLe]

/-- `LexLe` is transitive. -/
theorem lexLe_trans {a b c : ℕ × ℕ} (hab : LexLe a b) (hbc : LexLe b c) : LexLe a c := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨c₁, c₂⟩ := c
  simp only [LexLe] at hab hbc ⊢
  omega

/-- Lexicographic `≤` is the negation of the reverse lexicographic `<`. This is the form in
which lexicographic minimality is used: minimality says `LexLe (size G) (size H)`, which rules
out a strictly smaller counterexample. -/
theorem lexLe_iff_not_lexLt (a b : ℕ × ℕ) : LexLe a b ↔ ¬ LexLt b a := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  simp only [LexLe, LexLt]
  omega

/-- `LexLt` implies `LexLe`. -/
theorem LexLt.lexLe {a b : ℕ × ℕ} (h : LexLt a b) : LexLe a b := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  simp only [LexLt] at h
  simp only [LexLe]
  omega

/-- `G` is a **lexicographically minimal counterexample**: it is a counterexample, and every
counterexample on a finite vertex type in the same universe is at least as large as `G` in the
lexicographic order on `(number of vertices, number of edges)`. -/
def IsMinimalCounterexample (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : Prop :=
  IsCounterexample G ∧
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      IsCounterexample H → LexLe (size G) (size H)

/-- A minimal counterexample is a counterexample. -/
theorem IsMinimalCounterexample.isCounterexample {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : IsMinimalCounterexample G) : IsCounterexample G :=
  h.1

/-- Every vertex of a minimal counterexample has degree at least three. -/
theorem IsMinimalCounterexample.degree_ge_three {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : IsMinimalCounterexample G) (v : V) : 3 ≤ G.degree v :=
  h.1.degree_ge_three v

/-- A minimal counterexample has no power-of-two cycle. -/
theorem IsMinimalCounterexample.not_hasPowerOfTwoCycle {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (h : IsMinimalCounterexample G) :
    ¬ HasPowerOfTwoCycle G :=
  h.1.not_hasPowerOfTwoCycle

/-- A minimal counterexample has at least four vertices. -/
theorem IsMinimalCounterexample.card_verts_ge_four {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (h : IsMinimalCounterexample G) :
    4 ≤ Fintype.card V :=
  h.1.card_verts_ge_four

/-- Lexicographic minimality, unpacked: every counterexample is at least as large as `G`. -/
theorem IsMinimalCounterexample.size_le {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : IsMinimalCounterexample G) {W : Type u} [Fintype W]
    [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (hH : IsCounterexample H) :
    LexLe (size G) (size H) :=
  h.2 H hH

/-- Lexicographic minimality, in the negative form used by the reductions: no counterexample is
strictly smaller than `G`. -/
theorem IsMinimalCounterexample.not_size_lexLt {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (h : IsMinimalCounterexample G) {W : Type u} [Fintype W]
    [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (hH : IsCounterexample H) :
    ¬ LexLt (size H) (size G) :=
  (lexLe_iff_not_lexLt (size G) (size H)).mp (h.size_le H hH)

/-- A counterexample with a strictly smaller size in the lexicographic order contradicts
minimality. -/
theorem IsMinimalCounterexample.false_of_size_lexLt {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (h : IsMinimalCounterexample G) {W : Type u}
    [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hH : IsCounterexample H) (hlt : LexLt (size H) (size G)) : False :=
  h.not_size_lexLt H hH hlt

/-- On a fixed vertex type, minimality says that no counterexample has strictly fewer edges. -/
theorem IsMinimalCounterexample.not_edgeFinset_card_lt {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (h : IsMinimalCounterexample G) {H : SimpleGraph V}
    [DecidableRel H.Adj] (hH : IsCounterexample H) : ¬ H.edgeFinset.card < G.edgeFinset.card := by
  intro hlt
  refine h.not_size_lexLt H hH (Or.inr ⟨rfl, ?_⟩)
  simpa [size] using hlt

end Erdos64
