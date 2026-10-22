/-
# Stemock's equitable 4-total-colouring conjecture for cubic graphs of order < 20

Adauto, de Figueiredo, Sasaki and Schneider, *Order 14 is the largest
order for which every 4-total coloring of every cubic graph is equitable*,
arXiv:2609.05259, Conjecture 1.1 and Corollary 5.1, refute Stemock's
claim that every 4-total colouring of a cubic graph of order less than 20
is equitable. The circular ladder `L₁₂ = C₆ □ K₂` has a colouring with
class sizes `(8,8,8,6)`.

Minimality uses Lemmas 3.1 and 3.2 and Theorem 4.1: every 4-total
colouring at orders 6, 8, 10 and 14 is equitable. Equitability means
that every two colour-class sizes differ by at most one.

## Content of this module

* `not_stemockConjecture`: the conjecture is false (witness `L₁₂`).
* `equitable_of_card_lt_twelve_or_eq_fourteen`: every 4-total colouring of a
  cubic graph of order `< 12` or `= 14` is equitable (this covers Theorem 4.1,
  and also the vacuous orders `0, 2, 4` and the odd orders).
* `cor_5_1`: both halves together.
-/
import Mathlib

set_option autoImplicit false

open Finset SimpleGraph

namespace StemockEquitableTotalColouring

/-- A total colouring of `G` with `k` colours: a vertex colouring and an edge
colouring such that adjacent vertices get distinct colours, a vertex and an
incident edge get distinct colours, and two distinct edges sharing a vertex get
distinct colours.  The edge colouring is a total function on `Sym2 V`; only its
values on edges of `G` are constrained or counted. -/
structure TotalColouring {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  /-- The colour of a vertex. -/
  vertexColour : V → Fin k
  /-- The colour of an edge (only values on `G.edgeSet` matter). -/
  edgeColour : Sym2 V → Fin k
  /-- Adjacent vertices receive distinct colours. -/
  adj_ne : ∀ ⦃u v : V⦄, G.Adj u v → vertexColour u ≠ vertexColour v
  /-- A vertex and an incident edge receive distinct colours. -/
  incident_ne : ∀ ⦃u v : V⦄, G.Adj u v → vertexColour u ≠ edgeColour s(u, v)
  /-- Two distinct edges at a common vertex receive distinct colours. -/
  edge_ne : ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj u w → v ≠ w →
    edgeColour s(u, v) ≠ edgeColour s(u, w)

namespace TotalColouring

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- The size `|c_i|` of the colour class `i`: the number of vertices plus the
number of edges of `G` having colour `i`. -/
def classSize (c : TotalColouring G k) (i : Fin k) : ℕ :=
  #{v | c.vertexColour v = i} + #{e ∈ G.edgeFinset | c.edgeColour e = i}

/-- A total colouring is equitable if any two colour classes differ in size by
at most one. -/
def Equitable (c : TotalColouring G k) : Prop :=
  ∀ i j, c.classSize i ≤ c.classSize j + 1

/-- The vertex class `S_i`: vertices of colour `i`. -/
def colourVertices (c : TotalColouring G k) (i : Fin k) : Finset V :=
  {v | c.vertexColour v = i}

/-- The edge class `M_i`: edges of `G` of colour `i`. -/
def colourEdges (c : TotalColouring G k) (i : Fin k) : Finset (Sym2 V) :=
  {e ∈ G.edgeFinset | c.edgeColour e = i}

omit [DecidableEq V] in
/-- `|c_i| = |S_i| + |M_i|`. -/
lemma classSize_eq (c : TotalColouring G k) (i : Fin k) :
    c.classSize i = #(c.colourVertices i) + #(c.colourEdges i) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An edge containing `v` is `s(v, w)` for a neighbour `w` of `v`. -/
lemma exists_adj_of_mem [Fintype G.edgeSet] {e : Sym2 V} (he : e ∈ G.edgeFinset) {v : V}
    (hv : v ∈ e) : ∃ w, G.Adj v w ∧ e = s(v, w) := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
  exact ⟨w, by simpa using he, rfl⟩

/-- In a cubic graph, a vertex `v` is incident to no edge of colour `i` if `v`
has colour `i`, and to exactly one edge of colour `i` otherwise (the four
elements `v` and its three edges use all four colours). -/
lemma card_incident_colour (hG : G.IsRegularOfDegree 3) (c : TotalColouring G 4) (v : V)
    (i : Fin 4) :
    #{e ∈ G.edgeFinset | c.edgeColour e = i ∧ v ∈ e} =
      if c.vertexColour v = i then 0 else 1 := by
  set I := G.incidenceFinset v with hI
  have hIcard : #I = 3 := by rw [hI, card_incidenceFinset_eq_degree, hG v]
  have hmemI : ∀ e, e ∈ I ↔ e ∈ G.edgeFinset ∧ v ∈ e := by
    intro e; rw [hI, incidenceFinset_eq_filter, mem_filter]
  have hfilt : ({e ∈ G.edgeFinset | c.edgeColour e = i ∧ v ∈ e} : Finset _) =
      {e ∈ I | c.edgeColour e = i} := by
    ext e; simp only [mem_filter, hmemI]; tauto
  have hinj : Set.InjOn c.edgeColour I := by
    intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := exists_adj_of_mem ((hmemI e).1 he).1 ((hmemI e).1 he).2
    obtain ⟨b, hb, rfl⟩ := exists_adj_of_mem ((hmemI f).1 hf).1 ((hmemI f).1 hf).2
    by_contra hne
    have hab : a ≠ b := fun h => hne (h ▸ rfl)
    exact c.edge_ne ha hb hab hef
  have hsub : I.image c.edgeColour ⊆ univ.erase (c.vertexColour v) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    obtain ⟨a, ha, rfl⟩ := exists_adj_of_mem ((hmemI e).1 he).1 ((hmemI e).1 he).2
    exact mem_erase.mpr ⟨(c.incident_ne ha).symm, mem_univ _⟩
  have himage : I.image c.edgeColour = univ.erase (c.vertexColour v) := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injOn hinj, hIcard, card_erase_of_mem (mem_univ _)]
    simp
  rw [hfilt]
  split_ifs with hvi
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hei
    obtain ⟨a, ha, rfl⟩ := exists_adj_of_mem ((hmemI e).1 he).1 ((hmemI e).1 he).2
    exact c.incident_ne ha (hvi.trans hei.symm)
  · apply le_antisymm
    · rw [card_le_one]
      intro e he f hf
      rw [mem_filter] at he hf
      exact hinj he.1 hf.1 (he.2.trans hf.2.symm)
    · have hi : i ∈ I.image c.edgeColour := by
        rw [himage]; exact mem_erase.mpr ⟨Ne.symm hvi, mem_univ _⟩
      obtain ⟨e, he, hei⟩ := mem_image.mp hi
      exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hei⟩⟩

/-- Double counting of vertex/edge incidences between a vertex set `s` and the
edge class `M_i`. -/
lemma double_count (c : TotalColouring G k) (i : Fin k) (s : Finset V) :
    ∑ v ∈ s, #{e ∈ G.edgeFinset | c.edgeColour e = i ∧ v ∈ e} =
      ∑ e ∈ c.colourEdges i, #{v ∈ s | v ∈ e} := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s)
    (t := c.colourEdges i) (r := fun v e => v ∈ e)
  simp only [bipartiteAbove, bipartiteBelow, colourEdges, filter_filter] at h
  exact h

omit [DecidableRel G.Adj] in
/-- An edge of `G` has exactly two endpoints. -/
lemma card_mem_edge [Fintype G.edgeSet] {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    #{v | v ∈ e} = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := (mem_edgeFinset.mp he).ne
    have hpair : ({v | v ∈ s(a, b)} : Finset V) = {a, b} := by ext; simp
    rw [hpair, card_pair hab]

/-- An edge has at most one endpoint in a vertex class `S_j` (vertex classes
are independent sets). -/
lemma card_mem_edge_colourVertices_le (c : TotalColouring G k) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (j : Fin k) : #{v ∈ c.colourVertices j | v ∈ e} ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  simp only [colourVertices, mem_filter, mem_univ, true_and] at hx hy
  by_contra hxy
  have hexy : e = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hx.2, hy.2⟩
  have hadj : G.Adj x y := by rw [← mem_edgeSet, ← hexy]; exact mem_edgeFinset.mp he
  exact c.adj_ne hadj (hx.1.trans hy.1.symm)

/-- Decomposition lemma (Lemma 3.1 (ii), (iv) of arXiv:2609.05259): in a cubic
graph of order `n`, `M_i` is a perfect matching of `G - S_i`, so
`2 |M_i| + |S_i| = n`. -/
lemma decomposition (hG : G.IsRegularOfDegree 3) (c : TotalColouring G 4) (i : Fin 4) :
    2 * #(c.colourEdges i) + #(c.colourVertices i) = Fintype.card V := by
  have h := c.double_count i univ
  simp only [card_incident_colour hG] at h
  have hrhs : ∑ e ∈ c.colourEdges i, #({v | v ∈ e} : Finset V) =
      2 * #(c.colourEdges i) := by
    have hcongr : ∑ e ∈ c.colourEdges i, #({v | v ∈ e} : Finset V) =
        ∑ _e ∈ c.colourEdges i, 2 :=
      sum_congr rfl (fun e he => card_mem_edge (mem_filter.mp he).1)
    rw [hcongr, sum_const, smul_eq_mul, mul_comm]
  have hlhs : ∑ v : V, (if c.vertexColour v = i then 0 else 1) =
      #{v | ¬ c.vertexColour v = i} := by
    rw [card_filter]; exact sum_congr rfl (fun v _ => by split_ifs <;> rfl)
  rw [hrhs, hlhs] at h
  rw [← h, colourVertices, add_comm, card_filter_add_card_filter_not, card_univ]

/-- Counting bound (Lemma 3.2 (b) of arXiv:2609.05259, before substituting
`|M_i| = (n - v_i)/2`): for `j ≠ i`, `|S_j| ≤ |M_i|`. -/
lemma card_colourVertices_le (hG : G.IsRegularOfDegree 3) (c : TotalColouring G 4)
    {i j : Fin 4} (hij : j ≠ i) : #(c.colourVertices j) ≤ #(c.colourEdges i) := by
  have h := c.double_count i (c.colourVertices j)
  have hlhs : ∑ v ∈ c.colourVertices j, #{e ∈ G.edgeFinset | c.edgeColour e = i ∧ v ∈ e} =
      #(c.colourVertices j) := by
    rw [card_eq_sum_ones]
    refine sum_congr rfl (fun v hv => ?_)
    have hvj : c.vertexColour v = j := by simpa [colourVertices] using hv
    rw [card_incident_colour hG, if_neg (hvj ▸ hij)]
  rw [hlhs] at h
  rw [h, card_eq_sum_ones (c.colourEdges i)]
  exact sum_le_sum (fun e he => c.card_mem_edge_colourVertices_le (mem_filter.mp he).1 j)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The four vertex classes partition the vertex set. -/
lemma sum_card_colourVertices (c : TotalColouring G 4) :
    #(c.colourVertices 0) + #(c.colourVertices 1) + #(c.colourVertices 2) +
      #(c.colourVertices 3) = Fintype.card V := by
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset V)) (f := c.vertexColour)
    (t := univ) (fun _ _ => mem_univ _)
  rw [card_univ] at h
  rw [h, Fin.sum_univ_four]
  rfl

end TotalColouring

/-- Stemock's conjecture (Conjecture 1.1 of arXiv:2609.05259): every 4-total
colouring of a (finite, simple) cubic graph of order less than 20 is
equitable. -/
def StemockConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → Fintype.card V < 20 → ∀ c : TotalColouring G 4, c.Equitable

/-! ## The circular ladder `L₁₂ = C₆ □ K₂` -/

/-- The circular ladder (prism) `C_m □ K_2`, on vertex set `Fin m × Fin 2`; it is
`L_{2m}` in the notation of the paper. -/
def circularLadder (m : ℕ) : SimpleGraph (Fin m × Fin 2) := cycleGraph m □ ⊤

/-- Adjacency in the circular ladder is decidable (via `boxProd_adj`). -/
instance (m : ℕ) : DecidableRel (circularLadder m).Adj := fun x y =>
  decidable_of_iff ((cycleGraph m).Adj x.1 y.1 ∧ x.2 = y.2 ∨
    (⊤ : SimpleGraph (Fin 2)).Adj x.2 y.2 ∧ x.1 = y.1) boxProd_adj.symm

/-- Vertex colours of the witness: vertex `(i, s)` gets colour `(i + s) mod 3`. -/
def ladderVertexColour {m : ℕ} (x : Fin m × Fin 2) : Fin 4 :=
  ⟨(x.1.val + x.2.val) % 3, by omega⟩

/-- Edge colours of the witness on an ordered pair: rungs get colour `3`, and a
cycle edge gets the third colour of `{0,1,2}` missing at its endpoints. -/
def ladderPairColour {m : ℕ} (x y : Fin m × Fin 2) : Fin 4 :=
  if x.2 = y.2 then
    ⟨(3 - (ladderVertexColour x).val - (ladderVertexColour y).val) % 4, by omega⟩
  else 3

/-- `ladderPairColour` is symmetric. -/
lemma ladderPairColour_comm {m : ℕ} (x y : Fin m × Fin 2) :
    ladderPairColour x y = ladderPairColour y x := by
  unfold ladderPairColour
  split_ifs with h1 h2 h2
  · congr 1; omega
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- Edge colours of the witness, on unordered pairs. -/
def ladderEdgeColour {m : ℕ} : Sym2 (Fin m × Fin 2) → Fin 4 :=
  Sym2.lift ⟨ladderPairColour, ladderPairColour_comm⟩

/-- The non-equitable 4-total colouring of `L₁₂` (cf. Figure 2 of
arXiv:2609.05259); its class sizes are `(8, 8, 8, 6)`. -/
def l12Colouring : TotalColouring (circularLadder 6) 4 where
  vertexColour := ladderVertexColour
  edgeColour := ladderEdgeColour
  adj_ne := by decide
  incident_ne := by decide
  edge_ne := by decide

/-- The same construction on the prism `L₆ = C₃ □ K₂`; class sizes
`(4, 4, 4, 3)`, matching the configuration for order 6 in Section 4. -/
def l6Colouring : TotalColouring (circularLadder 3) 4 where
  vertexColour := ladderVertexColour
  edgeColour := ladderEdgeColour
  adj_ne := by decide
  incident_ne := by decide
  edge_ne := by decide

/-! ### Examples -/

/-- `L₁₂` is cubic. -/
lemma circularLadder_six_isRegular : (circularLadder 6).IsRegularOfDegree 3 := by
  intro v; revert v; decide

/-- `L₆` is cubic. -/
lemma circularLadder_three_isRegular : (circularLadder 3).IsRegularOfDegree 3 := by
  intro v; revert v; decide

example : Fintype.card (Fin 6 × Fin 2) = 12 := rfl
example : (circularLadder 6).edgeFinset.card = 18 := by decide
example : (circularLadder 6).Adj (0, 0) (1, 0) ∧ (circularLadder 6).Adj (5, 0) (0, 0) ∧
    (circularLadder 6).Adj (2, 0) (2, 1) ∧ ¬ (circularLadder 6).Adj (0, 0) (2, 0) ∧
    ¬ (circularLadder 6).Adj (0, 0) (1, 1) := by decide

/-- The colour class configuration of `l12Colouring` is `(8, 8, 8, 6)`. -/
lemma l12Colouring_classSize : List.ofFn l12Colouring.classSize = [8, 8, 8, 6] := by
  decide

example : List.ofFn l6Colouring.classSize = [4, 4, 4, 3] := by decide

/-- The colouring of `L₁₂` is not equitable. -/
lemma l12Colouring_not_equitable : ¬ l12Colouring.Equitable := by
  intro h
  have h03 := h 0 3
  have h0 : l12Colouring.classSize 0 = 8 := by decide
  have h3 : l12Colouring.classSize 3 = 6 := by decide
  omega

/-- The colouring of `L₆` is equitable (consistent with Theorem 4.1). -/
example : l6Colouring.Equitable := by
  intro i j; revert i j; decide

/-! ## Refutation -/

/-- **Stemock's conjecture is false** (Corollary 5.1 of arXiv:2609.05259): the
circular ladder `L₁₂ = C₆ □ K₂`, a cubic graph of order `12 < 20`, has a
non-equitable 4-total colouring. -/
theorem not_stemockConjecture : ¬ StemockConjecture := fun h =>
  l12Colouring_not_equitable
    (h (Fin 6 × Fin 2) (circularLadder 6) circularLadder_six_isRegular (by decide) l12Colouring)

/-! ## Minimality: orders below 12, and order 14 -/

/-- Arithmetic of feasible profiles: if `v_i, m_i` satisfy the decomposition
identities `2 m_i + v_i = n`, `∑ v_i = n` and the counting bounds `v_j ≤ m_i`
(`j ≠ i`), and `n < 12` or `n = 14`, then `v_i + m_i ≤ v_j + m_j + 1`. -/
lemma profile_bound (n : ℕ) (v m : Fin 4 → ℕ) (hsum : v 0 + v 1 + v 2 + v 3 = n)
    (hdec : ∀ i, 2 * m i + v i = n) (hb : ∀ i j, j ≠ i → v j ≤ m i)
    (hn : n < 12 ∨ n = 14) (i j : Fin 4) : v i + m i ≤ v j + m j + 1 := by
  have h0 := hdec 0
  have h1 := hdec 1
  have h2 := hdec 2
  have h3 := hdec 3
  have b01 := hb 0 1 (by decide)
  have b02 := hb 0 2 (by decide)
  have b03 := hb 0 3 (by decide)
  have b10 := hb 1 0 (by decide)
  have b12 := hb 1 2 (by decide)
  have b13 := hb 1 3 (by decide)
  have b20 := hb 2 0 (by decide)
  have b21 := hb 2 1 (by decide)
  have b23 := hb 2 3 (by decide)
  have b30 := hb 3 0 (by decide)
  have b31 := hb 3 1 (by decide)
  have b32 := hb 3 2 (by decide)
  -- Lemma 3.2 (a): `5 v_i ≤ 2 n`.
  have a0 : 5 * v 0 ≤ 2 * n := by omega
  have a1 : 5 * v 1 ≤ 2 * n := by omega
  have a2 : 5 * v 2 ≤ 2 * n := by omega
  have a3 : 5 * v 3 ≤ 2 * n := by omega
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- Every 4-total colouring of a cubic graph of order less than 12, or of order
14, is equitable.  This contains Theorem 4.1 of arXiv:2609.05259 (orders 6, 8,
10, 14); the remaining orders below 12 admit no 4-total colouring of a cubic
graph at all, except order 0 where it is trivial. -/
theorem equitable_of_card_lt_twelve_or_eq_fourteen {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    (hn : Fintype.card V < 12 ∨ Fintype.card V = 14) (c : TotalColouring G 4) :
    c.Equitable := by
  intro i j
  rw [c.classSize_eq, c.classSize_eq]
  exact profile_bound (Fintype.card V) (fun i => #(c.colourVertices i))
    (fun i => #(c.colourEdges i)) c.sum_card_colourVertices (c.decomposition hG)
    (fun _ _ hji => c.card_colourVertices_le hG hji) hn i j

/-- Theorem 4.1 of arXiv:2609.05259: every 4-total colouring of a cubic graph of
order 6, 8, 10 or 14 is equitable. -/
theorem thm_4_1 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    (hn : Fintype.card V ∈ ({6, 8, 10, 14} : Finset ℕ)) (c : TotalColouring G 4) :
    c.Equitable := by
  refine equitable_of_card_lt_twelve_or_eq_fourteen hG ?_ c
  simp only [mem_insert, mem_singleton] at hn
  omega

/-- Corollary 5.1 of arXiv:2609.05259: Stemock's conjecture is false, and `L₁₂`
is a counterexample of smallest order, since every 4-total colouring of a cubic
graph of order less than 12 is equitable. -/
theorem cor_5_1 :
    ¬ StemockConjecture ∧
      (circularLadder 6).IsRegularOfDegree 3 ∧ Fintype.card (Fin 6 × Fin 2) = 12 ∧
      ¬ l12Colouring.Equitable ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsRegularOfDegree 3 → Fintype.card V < 12 →
          ∀ c : TotalColouring G 4, c.Equitable :=
  ⟨not_stemockConjecture, circularLadder_six_isRegular, rfl, l12Colouring_not_equitable,
    fun _ _ _ _ _ hG hn c => equitable_of_card_lt_twelve_or_eq_fourteen hG (Or.inl hn) c⟩

/-- `L₆` is a cubic graph of order 6
carrying a 4-total colouring, and the theorem applies to it. -/
example : l6Colouring.Equitable :=
  thm_4_1 circularLadder_three_isRegular (by decide) l6Colouring

end StemockEquitableTotalColouring
