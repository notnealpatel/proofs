/-
# The List Total Colouring Conjecture is false

## Source

Jonathan A. Noel, "The List Total Colouring Conjecture is False",
arXiv:2609.38417.  Theorem 1.1 (Section 1), proved in Section 2 via
Lemma 2.1 and the argument after it; the total 4-colouring is the table
and Figure 1, the list assignment is Figure 2.

Verbatim (Theorem 1.1): "There exists a simple cubic graph $G$ on $20$
vertices such that $\chi''(G)=4$ and $\chi''_\ell(G)=5$."

The List Total Colouring Conjecture (Borodin--Kostochka--Woodall,
Juvan--Mohar--Skrekovski, Hilton--Johnson) says $\chi''_\ell(G)=\chi''(G)$
for every multigraph $G$.

Recorded 2026-10-21.  Status: proved in the paper.

## What is formalized

* `totalGraph G` (conflict graph of total colourings) and
  `TotalChoosable G k` (every assignment of `k`-element lists of natural
  numbers admits a total colouring from the lists).
* `noelGraph`: the paper's graph (four copies `B_i` of `K_{2,3}` joined by
  the six cross edges `v_{i,j} v_{j,i}`), with blocks indexed by `Fin 4`
  (block `i` here is the paper's `B_{i+1}`).
* `thm_1_1`: `noelGraph` is cubic on 20 vertices, its total chromatic
  number is `4`, and it is not totally `4`-choosable, witnessed by the
  paper's list assignment `noelLists`.
* `not_listTotalColouringConjecture`: the conjecture, in its simple-graph
  form "every finite simple graph is totally `χ''`-choosable", is false.

The upper bound $\chi''_\ell(G)\le 5$ of Theorem 1.1 is the cited
Juvan--Mohar--Skrekovski theorem for cubic graphs; it is not needed for
the refutation and is not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace ListTotalColouringRefutation

open SimpleGraph

section TotalColouring

variable {V : Type*}

/-- Conflict relation of a total colouring of `G`, on the disjoint union of the vertices
and the edges of `G`: two vertices conflict when adjacent, a vertex and an edge conflict when
the vertex is an endpoint of the edge, and two distinct edges conflict when they share an
endpoint. -/
def TotalAdj (G : SimpleGraph V) : V ⊕ G.edgeSet → V ⊕ G.edgeSet → Prop
  | .inl u, .inl w => G.Adj u w
  | .inl u, .inr e => u ∈ (e : Sym2 V)
  | .inr e, .inl u => u ∈ (e : Sym2 V)
  | .inr e, .inr f => e ≠ f ∧ ∃ u, u ∈ (e : Sym2 V) ∧ u ∈ (f : Sym2 V)

/-- The total graph `T(G)`: proper colourings of `T(G)` are exactly the total colourings
of `G`. -/
def totalGraph (G : SimpleGraph V) : SimpleGraph (V ⊕ G.edgeSet) where
  Adj := TotalAdj G
  symm := ⟨by
    rintro (u | e) (w | f) h
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact ⟨Ne.symm h.1, h.2.imp fun _ hu => ⟨hu.2, hu.1⟩⟩⟩
  loopless := ⟨by
    rintro (u | ⟨e, he⟩) h
    · exact G.loopless.irrefl u h
    · exact h.1 rfl⟩

/-- `G` is totally `k`-choosable: for every assignment `L` of lists of exactly `k` colours
(natural numbers) to the vertices and edges of `G`, there is a total colouring `c` of `G`
with `c x ∈ L x` for every element `x`. -/
def TotalChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V ⊕ G.edgeSet → Finset ℕ, (∀ x, (L x).card = k) →
    ∃ c : V ⊕ G.edgeSet → ℕ, (∀ x, c x ∈ L x) ∧ ∀ x y, (totalGraph G).Adj x y → c x ≠ c y

end TotalColouring

/-! ## The counterexample graph -/

/-- Vertices of Noel's graph: the private vertices `a i`, `b i` of the block `B_i` and the
terminal vertices `v i j` (`j ≠ i`) of `B_i`.  Blocks are indexed by `Fin 4`, so block `i`
here is the paper's block `B_{i+1}`. -/
inductive Vert : Type
  | a (i : Fin 4)
  | b (i : Fin 4)
  | v (i j : Fin 4) (h : i ≠ j)
  deriving DecidableEq, Fintype

/-- Adjacency of Noel's graph: `B_i` is a copy of `K_{2,3}` with parts `{a i, b i}` and
`{v i j : j ≠ i}`, and the cross edge between `B_i` and `B_j` joins `v i j` to `v j i`. -/
def NAdj : Vert → Vert → Prop
  | .a i, .v k _ _ => i = k
  | .b i, .v k _ _ => i = k
  | .v k _ _, .a i => i = k
  | .v k _ _, .b i => i = k
  | .v i j _, .v k l _ => i = l ∧ j = k
  | _, _ => False

instance : DecidableRel NAdj := fun x y => by
  cases x <;> cases y <;> unfold NAdj <;> infer_instance

/-- Noel's cubic graph on 20 vertices (House of Graphs 27005). -/
def noelGraph : SimpleGraph Vert where
  Adj := NAdj
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp only [NAdj] at h ⊢ <;> tauto⟩
  loopless := ⟨by
    intro x h
    cases x with
    | a i => exact h
    | b i => exact h
    | v i j hij => exact hij h.1⟩

instance : DecidableRel noelGraph.Adj := inferInstanceAs (DecidableRel NAdj)

example : noelGraph.Adj (.v 0 2 (by decide)) (.v 2 0 (by decide)) := by decide
example : noelGraph.Adj (.a 1) (.v 1 3 (by decide)) := by decide
example : ¬ noelGraph.Adj (.a 1) (.b 1) := by decide
example : ¬ noelGraph.Adj (.a 1) (.v 2 3 (by decide)) := by decide
example : ¬ noelGraph.Adj (.v 0 1 (by decide)) (.v 1 2 (by decide)) := by decide

/-- Noel's graph has 20 vertices. -/
theorem card_vert : Fintype.card Vert = 20 := by decide

/-- Noel's graph is cubic: every vertex has exactly three neighbours. -/
theorem noelGraph_isRegularOfDegree : noelGraph.IsRegularOfDegree 3 := by
  have key : ∀ x : Vert, (Finset.univ.filter (noelGraph.Adj x)).card = 3 := by decide
  intro x
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  exact key x

/-! ## The list assignment of Figure 2 -/

/-- The block containing a vertex. -/
def Vert.blk : Vert → Fin 4
  | .a i => i
  | .b i => i
  | .v i _ _ => i

/-- The list `{1,2,3,4,5} \ {i+1}` given to every vertex and edge of the block `B_{i+1}`. -/
def blockList (i : Fin 4) : Finset ℕ := ({1, 2, 3, 4, 5} : Finset ℕ).erase (i.val + 1)

/-- The list of the cross edge between blocks `i` and `j` (paper indices `i+1`, `j+1`):
the cross edges `B_1B_3` and `B_2B_4` get `{1,2,3,4,5} \ {5}`, and the cross edge
`B_k B_{k+1}` gets `{1,2,3,4,5} \ {k+2}`, indices read cyclically in `{1,2,3,4}`. -/
def crossList (i j : Fin 4) : Finset ℕ :=
  if j = i + 2 then ({1, 2, 3, 4, 5} : Finset ℕ).erase 5
  else if j = i + 1 then ({1, 2, 3, 4, 5} : Finset ℕ).erase ((i + 2 : Fin 4).val + 1)
  else ({1, 2, 3, 4, 5} : Finset ℕ).erase ((j + 2 : Fin 4).val + 1)

/-- The cross-edge list does not depend on the orientation of the edge. -/
theorem crossList_comm (i j : Fin 4) : crossList i j = crossList j i := by
  revert i j; decide

/-- List of the edge `xy`: the block list when both ends lie in one block, and the
cross-edge list otherwise. -/
def edgeListAux (x y : Vert) : Finset ℕ :=
  if x.blk = y.blk then blockList x.blk else crossList x.blk y.blk

/-- `edgeListAux` is symmetric. -/
theorem edgeListAux_comm (x y : Vert) : edgeListAux x y = edgeListAux y x := by
  unfold edgeListAux
  by_cases h : x.blk = y.blk
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h), crossList_comm]

/-- The list of an edge (as an unordered pair). -/
def edgeList (e : Sym2 Vert) : Finset ℕ := Sym2.lift ⟨edgeListAux, edgeListAux_comm⟩ e

/-- The paper's list assignment `L` (Figure 2). -/
def noelLists : Vert ⊕ noelGraph.edgeSet → Finset ℕ
  | .inl x => blockList x.blk
  | .inr e => edgeList e

example : blockList 0 = {2, 3, 4, 5} := by decide
example : edgeList s(.v 0 1 (by decide), .v 1 0 (by decide)) = {1, 2, 4, 5} := by decide
example : edgeList s(.v 0 2 (by decide), .v 2 0 (by decide)) = {1, 2, 3, 4} := by decide
example : edgeList s(.v 0 3 (by decide), .v 3 0 (by decide)) = {1, 3, 4, 5} := by decide
example : edgeList s(.v 1 2 (by decide), .v 2 1 (by decide)) = {1, 2, 3, 5} := by decide
example : edgeList s(.v 1 3 (by decide), .v 3 1 (by decide)) = {1, 2, 3, 4} := by decide
example : edgeList s(.v 2 3 (by decide), .v 3 2 (by decide)) = {2, 3, 4, 5} := by decide
example : edgeList s(.a 2, .v 2 0 (by decide)) = {1, 2, 4, 5} := by decide

/-- Every list of the assignment has exactly four colours. -/
theorem noelLists_card (x : Vert ⊕ noelGraph.edgeSet) : (noelLists x).card = 4 := by
  have hv : ∀ y : Vert, (blockList y.blk).card = 4 := by decide
  have he : ∀ y z : Vert, (edgeListAux y z).card = 4 := by decide
  rcases x with y | ⟨e, -⟩
  · exact hv y
  · induction e using Sym2.ind with
    | h y z => exact he y z

/-! ## Finite lemmas behind the paper's argument -/

/-- `x` is a colour of the palette `{1,2,3,4,5} \ {m}`. -/
def InPal (m x : ℕ) : Prop := 0 < x ∧ x < 6 ∧ x ≠ m

/-- Membership in a block list is membership in the corresponding palette. -/
theorem mem_blockList {i : Fin 4} {x : ℕ} : x ∈ blockList i ↔ InPal (i.val + 1) x := by
  simp only [blockList, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, InPal]
  omega

/-- Every colour of a cross-edge list lies in `{1,2,3,4,5}`. -/
theorem mem_crossList_bounds : ∀ i j : Fin 4, ∀ w ∈ crossList i j, 0 < w ∧ w < 6 := by
  decide

/-- Innermost layer of the exhaustive check of Lemma 2.1 (edges at `b`). -/
def K23Layer3 (m b v1 v2 v3 x1 x2 x3 : ℕ) : Prop :=
  ∀ y1 < 6, (0 < y1 ∧ y1 ≠ m ∧ y1 ≠ b ∧ y1 ≠ v1 ∧ y1 ≠ x1) →
  ∀ y2 < 6, (0 < y2 ∧ y2 ≠ m ∧ y2 ≠ b ∧ y2 ≠ v2 ∧ y2 ≠ x2 ∧ y2 ≠ y1) →
  ∀ y3 < 6, ¬ (0 < y3 ∧ y3 ≠ m ∧ y3 ≠ b ∧ y3 ≠ v3 ∧ y3 ≠ x3 ∧ y3 ≠ y1 ∧ y3 ≠ y2)

set_option synthInstance.maxSize 1000000 in
instance (m b v1 v2 v3 x1 x2 x3 : ℕ) : Decidable (K23Layer3 m b v1 v2 v3 x1 x2 x3) := by
  unfold K23Layer3; infer_instance

/-- Middle layer of the exhaustive check of Lemma 2.1 (edges at `a`). -/
def K23Layer2 (m a b v1 v2 v3 : ℕ) : Prop :=
  ∀ x1 < 6, (0 < x1 ∧ x1 ≠ m ∧ x1 ≠ a ∧ x1 ≠ v1) →
  ∀ x2 < 6, (0 < x2 ∧ x2 ≠ m ∧ x2 ≠ a ∧ x2 ≠ v2 ∧ x2 ≠ x1) →
  ∀ x3 < 6, (0 < x3 ∧ x3 ≠ m ∧ x3 ≠ a ∧ x3 ≠ v3 ∧ x3 ≠ x1 ∧ x3 ≠ x2) →
  K23Layer3 m b v1 v2 v3 x1 x2 x3

set_option synthInstance.maxSize 1000000 in
instance (m a b v1 v2 v3 : ℕ) : Decidable (K23Layer2 m a b v1 v2 v3) := by
  unfold K23Layer2; infer_instance

/-- Outer layer of the exhaustive check of Lemma 2.1 (terminal vertices). -/
def K23Layer1 (m a b : ℕ) : Prop :=
  ∀ v1 < 6, (0 < v1 ∧ v1 ≠ m ∧ v1 ≠ a ∧ v1 ≠ b) →
  ∀ v2 < 6, (0 < v2 ∧ v2 ≠ m ∧ v2 ≠ a ∧ v2 ≠ b) →
  ∀ v3 < 6, (0 < v3 ∧ v3 ≠ m ∧ v3 ≠ a ∧ v3 ≠ b) → K23Layer2 m a b v1 v2 v3

set_option synthInstance.maxSize 1000000 in
instance (m a b : ℕ) : Decidable (K23Layer1 m a b) := by
  unfold K23Layer1; infer_instance

set_option synthInstance.maxSize 1000000 in
/-- Exhaustive check: no total colouring of `K_{2,3}` from a palette `{1,…,5} \ {m}`
gives the two vertices `a ≠ b` of the 2-side different colours. -/
theorem k23_check : ∀ a < 6, ∀ b < 6, (0 < a ∧ 0 < b ∧ a ≠ b) →
    ∀ m < 6, (0 < m ∧ m ≠ a ∧ m ≠ b) → K23Layer1 m a b := by
  decide +kernel

/-- **Lemma 2.1** (for the palettes `{1,…,5} \ {m}` used here): in a total colouring of
`K_{2,3}` with parts `{a, b}` and `{v₁, v₂, v₃}` from the four colours `{1,…,5} \ {m}`, the
vertices `a` and `b` get the same colour.  Here `xₖ`, `yₖ` are the colours of the edges
`a vₖ` and `b vₖ`. -/
theorem k23_same {m a b v1 v2 v3 x1 x2 x3 y1 y2 y3 : ℕ} (hm : 0 < m) (hm6 : m < 6)
    (ha : InPal m a) (hb : InPal m b) (hv1 : InPal m v1) (hv2 : InPal m v2)
    (hv3 : InPal m v3) (hx1 : InPal m x1) (hx2 : InPal m x2) (hx3 : InPal m x3)
    (hy1 : InPal m y1) (hy2 : InPal m y2) (hy3 : InPal m y3)
    (hav1 : v1 ≠ a) (hav2 : v2 ≠ a) (hav3 : v3 ≠ a)
    (hbv1 : v1 ≠ b) (hbv2 : v2 ≠ b) (hbv3 : v3 ≠ b)
    (hx1a : x1 ≠ a) (hx2a : x2 ≠ a) (hx3a : x3 ≠ a)
    (hy1b : y1 ≠ b) (hy2b : y2 ≠ b) (hy3b : y3 ≠ b)
    (hx1v : x1 ≠ v1) (hx2v : x2 ≠ v2) (hx3v : x3 ≠ v3)
    (hy1v : y1 ≠ v1) (hy2v : y2 ≠ v2) (hy3v : y3 ≠ v3)
    (hx21 : x2 ≠ x1) (hx31 : x3 ≠ x1) (hx32 : x3 ≠ x2)
    (hy21 : y2 ≠ y1) (hy31 : y3 ≠ y1) (hy32 : y3 ≠ y2)
    (hyx1 : y1 ≠ x1) (hyx2 : y2 ≠ x2) (hyx3 : y3 ≠ x3) : a = b := by
  by_contra hab
  exact k23_check a ha.2.1 b hb.2.1 ⟨ha.1, hb.1, hab⟩ m hm6 ⟨hm, ha.2.2.symm, hb.2.2.symm⟩
    v1 hv1.2.1 ⟨hv1.1, hv1.2.2, hav1, hbv1⟩ v2 hv2.2.1 ⟨hv2.1, hv2.2.2, hav2, hbv2⟩
    v3 hv3.2.1 ⟨hv3.1, hv3.2.2, hav3, hbv3⟩
    x1 hx1.2.1 ⟨hx1.1, hx1.2.2, hx1a, hx1v⟩ x2 hx2.2.1 ⟨hx2.1, hx2.2.2, hx2a, hx2v, hx21⟩
    x3 hx3.2.1 ⟨hx3.1, hx3.2.2, hx3a, hx3v, hx31, hx32⟩
    y1 hy1.2.1 ⟨hy1.1, hy1.2.2, hy1b, hy1v, hyx1⟩
    y2 hy2.2.1 ⟨hy2.1, hy2.2.2, hy2b, hy2v, hyx2, hy21⟩
    y3 hy3.2.1 ⟨hy3.1, hy3.2.2, hy3b, hy3v, hyx3, hy31, hy32⟩

/-- Inner layer of the exhaustive check behind "the cross edge at `v_{i,j}` has its colour
in `S_i = {m, s}`". -/
def CrossLayer (m s : ℕ) : Prop :=
  ∀ x < 6, (0 < x ∧ x ≠ m ∧ x ≠ s) →
  ∀ y < 6, (0 < y ∧ y ≠ m ∧ y ≠ s ∧ y ≠ x) →
  ∀ z < 6, (0 < z ∧ z ≠ m ∧ z ≠ s ∧ z ≠ x ∧ z ≠ y) →
  ∀ w < 6, (0 < w ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z) → w = m ∨ w = s

set_option synthInstance.maxSize 1000000 in
instance (m s : ℕ) : Decidable (CrossLayer m s) := by
  unfold CrossLayer; infer_instance

set_option synthInstance.maxSize 1000000 in
/-- Exhaustive check behind `cross_mem_pair`. -/
theorem cross_check : ∀ m < 6, ∀ s < 6, (0 < m ∧ 0 < s ∧ s ≠ m) → CrossLayer m s := by
  decide +kernel

/-- If `x, y, z` are three distinct colours of `{1,…,5} \ {m}`, all different from
`s ∈ {1,…,5} \ {m}`, and `w ∈ {1,…,5}` differs from `x, y, z`, then `w ∈ {m, s}`. -/
theorem cross_mem_pair {m s x y z w : ℕ} (hm : 0 < m) (hm6 : m < 6) (hs : InPal m s)
    (hx : InPal m x) (hy : InPal m y) (hz : InPal m z) (hw0 : 0 < w) (hw6 : w < 6)
    (hxs : x ≠ s) (hys : y ≠ s) (hzs : z ≠ s) (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) : w = m ∨ w = s :=
  cross_check m hm6 s hs.2.1 ⟨hm, hs.1, hs.2.2⟩ x hx.2.1 ⟨hx.1, hx.2.2, hxs⟩
    y hy.2.1 ⟨hy.1, hy.2.2, hys, hyx⟩ z hz.2.1 ⟨hz.1, hz.2.2, hzs, hzx, hzy⟩
    w hw6 ⟨hw0, hwx, hwy, hwz⟩

/-- The cross edge between blocks `i` and `j` can take a colour lying in both
`S_i = {i+1, sᵢ}` and `S_j = {j+1, sⱼ}`. -/
def CrossColourable (i j : Fin 4) (si sj : ℕ) : Prop :=
  ∃ w ∈ crossList i j, (w = i.val + 1 ∨ w = si) ∧ (w = j.val + 1 ∨ w = sj)

instance (i j : Fin 4) (si sj : ℕ) : Decidable (CrossColourable i j si sj) := by
  unfold CrossColourable; infer_instance

set_option synthInstance.maxSize 1000000 in
/-- The final step of the paper: for every choice of `sᵢ ∈ {1,…,5} \ {i+1}`, some cross
edge cannot be coloured from `S_i ∩ S_j`. -/
theorem final_check : ∀ s0 < 6, ∀ s1 < 6, ∀ s2 < 6, ∀ s3 < 6,
    (s0 ≠ 1 ∧ s1 ≠ 2 ∧ s2 ≠ 3 ∧ s3 ≠ 4) →
    ¬ (CrossColourable 0 1 s0 s1 ∧ CrossColourable 0 2 s0 s2 ∧ CrossColourable 0 3 s0 s3 ∧
      CrossColourable 1 2 s1 s2 ∧ CrossColourable 1 3 s1 s3 ∧ CrossColourable 2 3 s2 s3) := by
  decide +kernel

/-! ## Named edges and conflicts of Noel's graph -/

/-- The edge `a_i v_{i,j}`. -/
def eA (i j : Fin 4) (h : i ≠ j) : noelGraph.edgeSet :=
  ⟨s(.a i, .v i j h), (mem_edgeSet noelGraph).2 rfl⟩

/-- The edge `b_i v_{i,j}`. -/
def eB (i j : Fin 4) (h : i ≠ j) : noelGraph.edgeSet :=
  ⟨s(.b i, .v i j h), (mem_edgeSet noelGraph).2 rfl⟩

/-- The cross edge `v_{i,j} v_{j,i}`. -/
def eX (i j : Fin 4) (h : i ≠ j) : noelGraph.edgeSet :=
  ⟨s(.v i j h, .v j i h.symm), (mem_edgeSet noelGraph).2 ⟨rfl, rfl⟩⟩

/-- The cross edge does not depend on the orientation. -/
theorem eX_comm (i j : Fin 4) (h : i ≠ j) : eX j i h.symm = eX i j h :=
  Subtype.ext Sym2.eq_swap

/-- Shorthand for the conflict relation of total colourings of Noel's graph. -/
abbrev TAdj : Vert ⊕ noelGraph.edgeSet → Vert ⊕ noelGraph.edgeSet → Prop :=
  (totalGraph noelGraph).Adj

/-- `a_i` and `v_{i,j}` are adjacent vertices. -/
theorem tadj_a_v (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.a i)) (.inl (.v i j h)) := rfl

/-- `b_i` and `v_{i,j}` are adjacent vertices. -/
theorem tadj_b_v (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.b i)) (.inl (.v i j h)) := rfl

/-- `a_i` is an endpoint of `a_i v_{i,j}`. -/
theorem tadj_a_eA (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.a i)) (.inr (eA i j h)) :=
  Sym2.mem_mk_left _ _

/-- `v_{i,j}` is an endpoint of `a_i v_{i,j}`. -/
theorem tadj_v_eA (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.v i j h)) (.inr (eA i j h)) :=
  Sym2.mem_mk_right _ _

/-- `b_i` is an endpoint of `b_i v_{i,j}`. -/
theorem tadj_b_eB (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.b i)) (.inr (eB i j h)) :=
  Sym2.mem_mk_left _ _

/-- `v_{i,j}` is an endpoint of `b_i v_{i,j}`. -/
theorem tadj_v_eB (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.v i j h)) (.inr (eB i j h)) :=
  Sym2.mem_mk_right _ _

/-- `v_{i,j}` is an endpoint of the cross edge `v_{i,j} v_{j,i}`. -/
theorem tadj_v_eX (i j : Fin 4) (h : i ≠ j) : TAdj (.inl (.v i j h)) (.inr (eX i j h)) :=
  Sym2.mem_mk_left _ _

/-- Distinct edges at `a_i` conflict. -/
theorem tadj_eA_eA (i j k : Fin 4) (hj : i ≠ j) (hk : i ≠ k) (hjk : j ≠ k) :
    TAdj (.inr (eA i j hj)) (.inr (eA i k hk)) := by
  refine ⟨fun heq => hjk ?_, .a i, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  have hv := congrArg Subtype.val heq
  simpa [eA] using hv

/-- Distinct edges at `b_i` conflict. -/
theorem tadj_eB_eB (i j k : Fin 4) (hj : i ≠ j) (hk : i ≠ k) (hjk : j ≠ k) :
    TAdj (.inr (eB i j hj)) (.inr (eB i k hk)) := by
  refine ⟨fun heq => hjk ?_, .b i, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  have hv := congrArg Subtype.val heq
  simpa [eB] using hv

/-- `a_i v_{i,j}` and `b_i v_{i,j}` conflict (common endpoint `v_{i,j}`). -/
theorem tadj_eA_eB (i j : Fin 4) (h : i ≠ j) : TAdj (.inr (eA i j h)) (.inr (eB i j h)) := by
  refine ⟨fun heq => ?_, .v i j h, Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩
  have hv := congrArg Subtype.val heq
  simp [eA, eB] at hv

/-- `a_i v_{i,j}` and the cross edge at `v_{i,j}` conflict. -/
theorem tadj_eA_eX (i j : Fin 4) (h : i ≠ j) : TAdj (.inr (eA i j h)) (.inr (eX i j h)) := by
  refine ⟨fun heq => ?_, .v i j h, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
  have hv := congrArg Subtype.val heq
  simp [eA, eX] at hv

/-- `b_i v_{i,j}` and the cross edge at `v_{i,j}` conflict. -/
theorem tadj_eB_eX (i j : Fin 4) (h : i ≠ j) : TAdj (.inr (eB i j h)) (.inr (eX i j h)) := by
  refine ⟨fun heq => ?_, .v i j h, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
  have hv := congrArg Subtype.val heq
  simp [eB, eX] at hv

/-- The edge `a_i v_{i,j}` gets the block list of `B_i`. -/
theorem noelLists_eA (i j : Fin 4) (h : i ≠ j) : noelLists (.inr (eA i j h)) = blockList i := by
  simp [noelLists, eA, edgeList, edgeListAux, Vert.blk]

/-- The edge `b_i v_{i,j}` gets the block list of `B_i`. -/
theorem noelLists_eB (i j : Fin 4) (h : i ≠ j) : noelLists (.inr (eB i j h)) = blockList i := by
  simp [noelLists, eB, edgeList, edgeListAux, Vert.blk]

/-- The cross edge `v_{i,j} v_{j,i}` gets the cross-edge list. -/
theorem noelLists_eX (i j : Fin 4) (h : i ≠ j) :
    noelLists (.inr (eX i j h)) = crossList i j := by
  simp [noelLists, eX, edgeList, edgeListAux, Vert.blk, h]

/-! ## No total colouring from the lists -/

/-- Section 2 of the paper: Noel's graph has no total colouring from the lists `noelLists`. -/
theorem noelLists_not_colourable (c : Vert ⊕ noelGraph.edgeSet → ℕ)
    (hcL : ∀ x, c x ∈ noelLists x) (hcP : ∀ x y, TAdj x y → c x ≠ c y) : False := by
  have hvert : ∀ x : Vert, InPal (x.blk.val + 1) (c (.inl x)) :=
    fun x => mem_blockList.1 (hcL (.inl x))
  have hA : ∀ (i j : Fin 4) (h : i ≠ j), InPal (i.val + 1) (c (.inr (eA i j h))) :=
    fun i j h => mem_blockList.1 (by rw [← noelLists_eA i j h]; exact hcL _)
  have hB : ∀ (i j : Fin 4) (h : i ≠ j), InPal (i.val + 1) (c (.inr (eB i j h))) :=
    fun i j h => mem_blockList.1 (by rw [← noelLists_eB i j h]; exact hcL _)
  have hm : ∀ i : Fin 4, 0 < i.val + 1 ∧ i.val + 1 < 6 := fun i => ⟨by omega, by omega⟩
  -- Lemma 2.1 in every block: `c(a_i) = c(b_i)`.
  have same : ∀ i : Fin 4, c (.inl (.a i)) = c (.inl (.b i)) := by
    intro i
    have h1 : i ≠ i + 1 := by revert i; decide
    have h2 : i ≠ i + 2 := by revert i; decide
    have h3 : i ≠ i + 3 := by revert i; decide
    have h12 : i + 1 ≠ i + 2 := by revert i; decide
    have h13 : i + 1 ≠ i + 3 := by revert i; decide
    have h23 : i + 2 ≠ i + 3 := by revert i; decide
    exact k23_same (hm i).1 (hm i).2 (hvert (.a i)) (hvert (.b i))
      (hvert (.v i _ h1)) (hvert (.v i _ h2)) (hvert (.v i _ h3))
      (hA i _ h1) (hA i _ h2) (hA i _ h3) (hB i _ h1) (hB i _ h2) (hB i _ h3)
      (hcP _ _ (tadj_a_v i _ h1)).symm (hcP _ _ (tadj_a_v i _ h2)).symm
      (hcP _ _ (tadj_a_v i _ h3)).symm
      (hcP _ _ (tadj_b_v i _ h1)).symm (hcP _ _ (tadj_b_v i _ h2)).symm
      (hcP _ _ (tadj_b_v i _ h3)).symm
      (hcP _ _ (tadj_a_eA i _ h1)).symm (hcP _ _ (tadj_a_eA i _ h2)).symm
      (hcP _ _ (tadj_a_eA i _ h3)).symm
      (hcP _ _ (tadj_b_eB i _ h1)).symm (hcP _ _ (tadj_b_eB i _ h2)).symm
      (hcP _ _ (tadj_b_eB i _ h3)).symm
      (hcP _ _ (tadj_v_eA i _ h1)).symm (hcP _ _ (tadj_v_eA i _ h2)).symm
      (hcP _ _ (tadj_v_eA i _ h3)).symm
      (hcP _ _ (tadj_v_eB i _ h1)).symm (hcP _ _ (tadj_v_eB i _ h2)).symm
      (hcP _ _ (tadj_v_eB i _ h3)).symm
      (hcP _ _ (tadj_eA_eA i _ _ h1 h2 h12)).symm (hcP _ _ (tadj_eA_eA i _ _ h1 h3 h13)).symm
      (hcP _ _ (tadj_eA_eA i _ _ h2 h3 h23)).symm
      (hcP _ _ (tadj_eB_eB i _ _ h1 h2 h12)).symm (hcP _ _ (tadj_eB_eB i _ _ h1 h3 h13)).symm
      (hcP _ _ (tadj_eB_eB i _ _ h2 h3 h23)).symm
      (hcP _ _ (tadj_eA_eB i _ h1)).symm (hcP _ _ (tadj_eA_eB i _ h2)).symm
      (hcP _ _ (tadj_eA_eB i _ h3)).symm
  -- The colour of the cross edge `v_{i,j} v_{j,i}` lies in `S_i = {i+1, s_i}`.
  have cross : ∀ (i j : Fin 4) (h : i ≠ j),
      c (.inr (eX i j h)) = i.val + 1 ∨ c (.inr (eX i j h)) = c (.inl (.a i)) := by
    intro i j h
    have hw := mem_crossList_bounds i j _ (by rw [← noelLists_eX i j h]; exact hcL _)
    have hzs : c (.inr (eB i j h)) ≠ c (.inl (.a i)) := by
      rw [same i]; exact (hcP _ _ (tadj_b_eB i j h)).symm
    exact cross_mem_pair (hm i).1 (hm i).2 (hvert (.a i)) (hvert (.v i j h)) (hA i j h)
      (hB i j h) hw.1 hw.2 (hcP _ _ (tadj_a_v i j h)).symm (hcP _ _ (tadj_a_eA i j h)).symm
      hzs (hcP _ _ (tadj_v_eA i j h)).symm (hcP _ _ (tadj_v_eB i j h)).symm
      (hcP _ _ (tadj_eA_eB i j h)).symm (hcP _ _ (tadj_v_eX i j h)).symm
      (hcP _ _ (tadj_eA_eX i j h)).symm (hcP _ _ (tadj_eB_eX i j h)).symm
  -- Hence every cross edge is coloured from `S_i ∩ S_j`.
  have pair : ∀ (i j : Fin 4) (h : i ≠ j),
      CrossColourable i j (c (.inl (.a i))) (c (.inl (.a j))) := by
    intro i j h
    refine ⟨c (.inr (eX i j h)), by rw [← noelLists_eX i j h]; exact hcL _, cross i j h, ?_⟩
    rw [← eX_comm i j h]
    exact cross j i h.symm
  exact final_check _ (hvert (.a 0)).2.1 _ (hvert (.a 1)).2.1 _ (hvert (.a 2)).2.1
    _ (hvert (.a 3)).2.1 ⟨(hvert (.a 0)).2.2, (hvert (.a 1)).2.2, (hvert (.a 2)).2.2,
      (hvert (.a 3)).2.2⟩
    ⟨pair 0 1 (by decide), pair 0 2 (by decide), pair 0 3 (by decide), pair 1 2 (by decide),
      pair 1 3 (by decide), pair 2 3 (by decide)⟩

/-- Noel's graph is not totally `4`-choosable. -/
theorem not_totalChoosable_four : ¬ TotalChoosable noelGraph 4 := by
  intro hch
  obtain ⟨c, hcL, hcP⟩ := hch noelLists noelLists_card
  exact noelLists_not_colourable c hcL hcP

/-! ## The total `4`-colouring of Figure 1 -/

/-- Colours of the terminal vertices, from the paper's table: `termCol i j = c(v_{i+1,j+1})`
(diagonal entries unused). -/
def termCol : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 3, 1], ![1, 0, 3, 2], ![1, 2, 0, 3], ![2, 3, 1, 0]]

/-- The colour of `{1,2,3}` following `t`, cyclically. -/
def nextCol (t : ℕ) : ℕ := t % 3 + 1

/-- The colour of `{1,2,3}` preceding `t`, cyclically. -/
def prevCol (t : ℕ) : ℕ := (t + 1) % 3 + 1

example : (termCol 0 1, termCol 0 2, termCol 0 3) = (2, 3, 1) := rfl
example : (termCol 3 0, termCol 3 1, termCol 3 2) = (2, 3, 1) := rfl
/-- The table is "antisymmetric": adjacent terminals `v_{i,j}`, `v_{j,i}` differ. -/
example : ∀ i j : Fin 4, i ≠ j → termCol i j ≠ termCol j i := by decide
example : (nextCol 1, nextCol 2, nextCol 3) = (2, 3, 1) := rfl
example : (prevCol 1, prevCol 2, prevCol 3) = (3, 1, 2) := rfl

/-- Vertex colours: private vertices get `4`, terminals follow the table. -/
def vertCol : Vert → ℕ
  | .a _ => 4
  | .b _ => 4
  | .v i j _ => termCol i j

/-- Edge colours: `v a_i` gets the successor of `c(v)`, `v b_i` its predecessor, and cross
edges get `4`. -/
def edgeColAux : Vert → Vert → ℕ
  | .a _, .v i j _ => nextCol (termCol i j)
  | .v i j _, .a _ => nextCol (termCol i j)
  | .b _, .v i j _ => prevCol (termCol i j)
  | .v i j _, .b _ => prevCol (termCol i j)
  | _, _ => 4

/-- `edgeColAux` is symmetric. -/
theorem edgeColAux_comm (x y : Vert) : edgeColAux x y = edgeColAux y x := by
  cases x <;> cases y <;> rfl

/-- The paper's total colouring with colours `{1,2,3,4}`. -/
def paperColouring : Vert ⊕ noelGraph.edgeSet → ℕ
  | .inl x => vertCol x
  | .inr e => Sym2.lift ⟨edgeColAux, edgeColAux_comm⟩ (e : Sym2 Vert)

example : paperColouring (.inr (eA 0 1 (by decide))) = 3 := by decide
example : paperColouring (.inr (eB 0 1 (by decide))) = 1 := by decide
example : paperColouring (.inr (eX 0 1 (by decide))) = 4 := by decide

/-- Every colour of `paperColouring` lies in `{1,2,3,4}`. -/
theorem paperColouring_mem (x : Vert ⊕ noelGraph.edgeSet) :
    1 ≤ paperColouring x ∧ paperColouring x ≤ 4 := by
  have hv : ∀ y : Vert, 1 ≤ vertCol y ∧ vertCol y ≤ 4 := by decide
  have he : ∀ y z : Vert, noelGraph.Adj y z → 1 ≤ edgeColAux y z ∧ edgeColAux y z ≤ 4 := by
    decide
  rcases x with y | ⟨e, he'⟩
  · exact hv y
  · induction e using Sym2.ind with
    | h y z => exact he y z ((mem_edgeSet noelGraph).1 he')

/-- `paperColouring` is a proper total colouring of Noel's graph. -/
theorem paperColouring_proper (x y : Vert ⊕ noelGraph.edgeSet) (hxy : TAdj x y) :
    paperColouring x ≠ paperColouring y := by
  have vv : ∀ u w : Vert, noelGraph.Adj u w → vertCol u ≠ vertCol w := by decide
  have ve : ∀ p q : Vert, noelGraph.Adj p q →
      vertCol p ≠ edgeColAux p q ∧ vertCol q ≠ edgeColAux p q := by decide
  have ee : ∀ p q : Vert, noelGraph.Adj p q → ∀ r t : Vert, noelGraph.Adj r t →
      (p = r ∨ p = t ∨ q = r ∨ q = t) → ¬ ((p = r ∧ q = t) ∨ (p = t ∧ q = r)) →
      edgeColAux p q ≠ edgeColAux r t := by decide
  rcases x with u | ⟨e, he⟩ <;> rcases y with w | ⟨f, hf⟩
  · exact vv u w hxy
  · induction f using Sym2.ind with
    | h p q =>
      have hpq := (mem_edgeSet noelGraph).1 hf
      change u ∈ s(p, q) at hxy
      rcases Sym2.mem_iff.1 hxy with rfl | rfl
      · exact (ve _ _ hpq).1
      · exact (ve _ _ hpq).2
  · induction e using Sym2.ind with
    | h p q =>
      have hpq := (mem_edgeSet noelGraph).1 he
      change w ∈ s(p, q) at hxy
      rcases Sym2.mem_iff.1 hxy with rfl | rfl
      · exact Ne.symm (ve _ _ hpq).1
      · exact Ne.symm (ve _ _ hpq).2
  · induction e using Sym2.ind with
    | h p q =>
      induction f using Sym2.ind with
      | h r t =>
        obtain ⟨hne, u, hu1, hu2⟩ := hxy
        have hpq := (mem_edgeSet noelGraph).1 he
        have hrt := (mem_edgeSet noelGraph).1 hf
        have hshare : p = r ∨ p = t ∨ q = r ∨ q = t := by
          rcases Sym2.mem_iff.1 hu1 with rfl | rfl <;>
            rcases Sym2.mem_iff.1 hu2 with h | h <;> simp [h]
        have hdiff : ¬ ((p = r ∧ q = t) ∨ (p = t ∧ q = r)) := by
          intro hsame
          exact hne (Subtype.ext (Sym2.eq_iff.2 hsame))
        exact ee p q hpq r t hrt hshare hdiff

/-- The total graph of Noel's graph is `4`-colourable (Figure 1). -/
theorem totalGraph_colorable_four : (totalGraph noelGraph).Colorable 4 := by
  rw [colorable_iff_exists_bdd_nat_coloring]
  refine ⟨Coloring.mk (fun x => paperColouring x % 4) fun {x y} hxy => ?_, fun x => ?_⟩
  · have h1 := paperColouring_mem x
    have h2 := paperColouring_mem y
    have h3 := paperColouring_proper x y hxy
    omega
  · exact Nat.mod_lt _ (by norm_num)

/-- A vertex and its three incident edges pairwise conflict, so three colours never suffice. -/
theorem totalGraph_not_colorable_three : ¬ (totalGraph noelGraph).Colorable 3 := by
  rintro ⟨C⟩
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have pigeon : ∀ p q r s : Fin 3,
      ¬ (p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s) := by
    decide
  exact pigeon (C (.inl (.a 0))) (C (.inr (eA 0 1 h01))) (C (.inr (eA 0 2 h02)))
    (C (.inr (eA 0 3 h03))) ⟨C.valid (tadj_a_eA 0 1 h01), C.valid (tadj_a_eA 0 2 h02),
    C.valid (tadj_a_eA 0 3 h03), C.valid (tadj_eA_eA 0 1 2 h01 h02 (by decide)),
    C.valid (tadj_eA_eA 0 1 3 h01 h03 (by decide)),
    C.valid (tadj_eA_eA 0 2 3 h02 h03 (by decide))⟩

/-- The total chromatic number of Noel's graph is `4`. -/
theorem totalChromaticNumber_eq_four : (totalGraph noelGraph).chromaticNumber = 4 := by
  have h := (chromaticNumber_eq_iff_colorable_not_colorable (G := totalGraph noelGraph)
    (n := 3)).2 ⟨totalGraph_colorable_four, totalGraph_not_colorable_three⟩
  exact_mod_cast h

/-- Non-vacuity of the conflict relation: with the uniform lists `{1,2,3,4}` Noel's graph *is*
total colourable from the lists (by the paper's colouring), so the failure for `noelLists`
is caused by the lists. -/
theorem uniform_lists_colourable :
    ∃ c : Vert ⊕ noelGraph.edgeSet → ℕ, (∀ x, c x ∈ ({1, 2, 3, 4} : Finset ℕ)) ∧
      ∀ x y, TAdj x y → c x ≠ c y := by
  refine ⟨paperColouring, fun x => ?_, paperColouring_proper⟩
  have h := paperColouring_mem x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Non-vacuity of `TotalChoosable`: the one-vertex graph is totally `1`-choosable. -/
example : TotalChoosable (⊥ : SimpleGraph Unit) 1 := by
  intro L hL
  have hne : ∀ x, (L x).Nonempty := fun x => Finset.card_pos.1 (by rw [hL x]; norm_num)
  refine ⟨fun x => (L x).min' (hne x), fun x => Finset.min'_mem _ _, ?_⟩
  rintro (u | ⟨e, he⟩) (w | ⟨f, hf⟩) h
  · exact absurd h (by simp [totalGraph])
  · simp at hf
  · simp at he
  · simp at he

/-- **Theorem 1.1** (Noel, arXiv:2609.38417), refutation part: there is a simple cubic graph
on `20` vertices whose total chromatic number is `4` but which is not totally `4`-choosable;
hence its list total chromatic number exceeds its total chromatic number.  (The paper's
further bound `χ''_ℓ ≤ 5`, a cited theorem of Juvan–Mohar–Škrekovski, is not formalized.) -/
theorem thm_1_1 :
    Fintype.card Vert = 20 ∧ noelGraph.IsRegularOfDegree 3 ∧
      (totalGraph noelGraph).chromaticNumber = 4 ∧ ¬ TotalChoosable noelGraph 4 :=
  ⟨card_vert, noelGraph_isRegularOfDegree, totalChromaticNumber_eq_four,
    not_totalChoosable_four⟩

/-- The List Total Colouring Conjecture (Borodin–Kostochka–Woodall, Juvan–Mohar–Škrekovski,
Hilton–Johnson), restricted to finite simple graphs: every finite simple graph `G` with total
chromatic number `k` is totally `k`-choosable, i.e. `χ''_ℓ(G) ≤ χ''(G)` (the reverse
inequality always holds). -/
def ListTotalColouringConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
    (totalGraph G).chromaticNumber = k → TotalChoosable G k

/-- **The List Total Colouring Conjecture is false** (Noel, arXiv:2609.38417), already for
finite simple cubic graphs. -/
theorem not_listTotalColouringConjecture : ¬ ListTotalColouringConjecture := fun h =>
  not_totalChoosable_four (h Vert noelGraph 4 totalChromaticNumber_eq_four)

end ListTotalColouringRefutation
