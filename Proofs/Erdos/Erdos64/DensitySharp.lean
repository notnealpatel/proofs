/-
Erdős–Gyárfás problem 64 — the sharp auxiliary-density lemma.

PROVENANCE.  arXiv:2609.28594 (Ducoffe–Dumitru), Section 3.  `Density.lean`
proves the density chain of Theorem 3.7 through the *generic* `2`-degenerate
edge bound `|E(K)| ≤ 2|K| - 3`
(`card_edgeFinset_induce_le_two_mul_card_sub_three`) applied to the doubling
graph `M` of a minimal counterexample, giving `ℓ ≥ 2h + 3` for `h ≥ 2`.  This
file records the sharpening of that edge bound for the *four-cycle-free* graphs
that actually occur as doubling graphs.

SOURCE CLAIM BOUNDARY.  The numerical content formalized here is:

* **(Target A)** A finite simple graph `K` on `n ≥ 6` vertices, every nonempty
  induced subgraph of which has a vertex of degree at most two, and which
  contains no simple `4`-cycle, satisfies `|E(K)| ≤ 2n - 5`.  The bound is
  exactly the `2`-degenerate bound `2n - 3` minus two, and it is sharp: the
  six-vertex cycle plus one chord attains it.  The proof is strong induction
  after the case `n = 6`; the base case peels a vertex `v` of degree at most
  two and needs two five-vertex facts: `|E| ≤ 6` for a four-cycle-free
  five-vertex graph (a double count over the four-vertex induced subgraphs),
  and the fact that a five-vertex graph with six edges and no `4`-cycle has a
  common neighbour for every pair of vertices (the only such graph is the
  friendship graph `F₂`).

* **(Target B)** Applying Target A to `M = doublingGraph G` for a minimal
  counterexample with `h = |H| ≥ 6` gives `|L₂| = |E(M)| ≤ 2h - 5`, sharpening
  `card_degreeThreeTwoHigh_le_two_mul_card_sub_three` of `Density.lean` by two.

* **(Target C)** Combining Target B with the crossing count
  `4h ≤ |L₁| + 2|L₂|`, the partition bound `ℓ ≥ |L₁| + |L₂|`, and the parity of
  the degree sum inside `G[L]` gives `2h + 6 ≤ ℓ` for `h ≥ 6`, one better than
  the `2h + 3` of `Density.lean`.

* **(Target C′)** Target C is available without the restriction `h ≥ 6`, at the cost of an
  explicit order hypothesis `n ≥ 24`: for `h ≤ 5` the vertex partition `ℓ + h = n` alone forces
  `ℓ ≥ n - 5 ≥ 19 ≥ 2h + 6`.  The order bound is a *hypothesis*, not a claim of this file; the
  external fact that counterexamples have order at least `24` is outside its scope.

Nothing is assumed: `HasFourCycle` is an honest simple-cycle witness, the
five-vertex facts are proved by double counting and by a degree case analysis,
and the parity input is the degree-sum identity of the induced graph on `L`.
-/

import Erdos.Erdos64.Density

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### 1. Four-cycles

A `4`-cycle is a closed walk that is a cycle and has length four, i.e. the
`k = 2` case of `HasPowerOfTwoCycle`.  The predicate is kept separate because
`¬ HasPowerOfTwoCycle` is strictly stronger: it also excludes `8`-cycles. -/

/-- `G` has a **simple `4`-cycle**: a closed walk at some vertex which is a cycle and has
length four. -/
def HasFourCycle (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4

/-- A four-cycle is a power-of-two cycle, with exponent `2`. -/
theorem hasPowerOfTwoCycle_of_hasFourCycle {G : SimpleGraph V} (h : HasFourCycle G) :
    HasPowerOfTwoCycle G := by
  obtain ⟨v, c, hc, hlen⟩ := h
  exact ⟨2, by norm_num, v, c, hc, by rw [hlen]; norm_num⟩

/-- A four-cycle of an induced subgraph is a four-cycle of the ambient graph: the walk is mapped
along the inclusion homomorphism, which is injective. -/
theorem hasFourCycle_induce (G : SimpleGraph V) (s : Set V) (h : HasFourCycle (G.induce s)) :
    HasFourCycle G := by
  obtain ⟨v, c, hc, hlen⟩ := h
  let f : G.induce s →g G := ⟨Subtype.val, fun {_ _} hab => SimpleGraph.induce_adj.mp hab⟩
  exact ⟨(v : V), c.map f, hc.map Subtype.val_injective, by
    rw [SimpleGraph.Walk.length_map, hlen]⟩

/-- Deleting vertices cannot create a four-cycle. -/
theorem not_hasFourCycle_induce (G : SimpleGraph V) (s : Set V) (h : ¬ HasFourCycle G) :
    ¬ HasFourCycle (G.induce s) :=
  fun hc => h (hasFourCycle_induce G s hc)

/-- Four pairwise distinct vertices joined cyclically by four edges form a four-cycle.  The two
"diagonal" pairs need only be distinct, not non-adjacent: the walk `a → b → c → d → a` has four
distinct vertices and is therefore a cycle. -/
theorem hasFourCycle_of_four_cycle_adj {α : Type u} (L : SimpleGraph α) {a b c d : α}
    (hab : L.Adj a b) (hbc : L.Adj b c) (hcd : L.Adj c d) (hda : L.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : HasFourCycle L := by
  refine ⟨a, Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil))), ?_, ?_⟩
  · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by simp [Walk.length_cons]⟩
    rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ Walk.not_nil_cons]
    simp only [Walk.support_cons, Walk.support_nil]
    simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
  · simp [Walk.length_cons]

/-! ### 2. Elementary counting helpers -/

/-- Two distinct vertices outside a finset, when it leaves room for two. -/
theorem exists_two_notMem_of_card_le {W : Type u} [Fintype W] [DecidableEq W] (s : Finset W)
    (h : s.card + 2 ≤ Fintype.card W) : ∃ a b : W, a ≠ b ∧ a ∉ s ∧ b ∉ s := by
  classical
  have h1 : s.card < Fintype.card W := by omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
  have h2 : (insert a s).card < Fintype.card W := by
    rw [Finset.card_insert_of_notMem ha]
    omega
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
  have hba : b ≠ a := by
    intro hc
    exact hb (hc ▸ Finset.mem_insert_self a s)
  exact ⟨a, b, hba.symm, ha, fun hc => hb (Finset.mem_insert_of_mem hc)⟩

/-- A vertex outside a finset, when it leaves room for one. -/
theorem exists_notMem_of_card_le {W : Type u} [Fintype W] [DecidableEq W] (s : Finset W)
    (h : s.card < Fintype.card W) : ∃ x : W, x ∉ s := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨x, hx⟩

/-- The cardinality of a finset of three pairwise distinct elements. -/
theorem card_triple {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ({a, b, c} : Finset α).card = 3 := by
  have h1 : a ∉ ({b, c} : Finset α) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset α) := by simp [hbc]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]

/-! ### 3. The non-neighbour finset of a vertex

In a five-vertex graph the non-neighbours of `v` number `4 - d(v)`, so a vertex of degree three
has a unique non-neighbour and a vertex of degree two has exactly two. -/

/-- The set of vertices that are not neighbours of `v`. -/
def nonNeighborFinset {W : Type u} (L : SimpleGraph W) [Fintype W] [DecidableEq W]
    [DecidableRel L.Adj] (v : W) : Finset W :=
  (Finset.univ.erase v).filter fun w => ¬ L.Adj v w

/-- Membership in `nonNeighborFinset`. -/
theorem mem_nonNeighborFinset {W : Type u} {L : SimpleGraph W} [Fintype W] [DecidableEq W]
    [DecidableRel L.Adj] {v w : W} : w ∈ nonNeighborFinset L v ↔ w ≠ v ∧ ¬ L.Adj v w := by
  simp [nonNeighborFinset]

/-- The non-neighbours of `v` number `|V| - 1 - d(v)`. -/
theorem card_nonNeighborFinset {W : Type u} [Fintype W] [DecidableEq W] (L : SimpleGraph W)
    [DecidableRel L.Adj] (v : W) :
    (nonNeighborFinset L v).card = Fintype.card W - 1 - L.degree v := by
  classical
  have hneigh : (Finset.univ.erase v).filter (fun w => L.Adj v w) = L.neighborFinset v := by
    ext w
    rw [Finset.mem_filter, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.2, fun h => ⟨⟨h.ne.symm, Finset.mem_univ w⟩, h⟩⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v)
    (p := fun w : W => L.Adj v w)
  rw [hneigh, SimpleGraph.card_neighborFinset_eq_degree,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hsplit
  simp only [nonNeighborFinset]
  omega

/-- A vertex of degree three in a five-vertex graph has a unique non-neighbour. -/
theorem exists_nonNeighborFinset_eq_singleton {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] (hcard : Fintype.card W = 5) {v : W}
    (hv : L.degree v = 3) : ∃ r : W, nonNeighborFinset L v = {r} :=
  Finset.card_eq_one.mp (by rw [card_nonNeighborFinset, hcard, hv])

/-- Unfolding of the unique non-neighbour of a vertex of degree three. -/
theorem adj_of_nonNeighborFinset_eq_singleton {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] {v r : W} (h : nonNeighborFinset L v = {r}) :
    r ≠ v ∧ ¬ L.Adj v r ∧ ∀ x : W, x ≠ v → x ≠ r → L.Adj v x := by
  have hmem : r ∈ nonNeighborFinset L v := by rw [h]; exact Finset.mem_singleton_self r
  refine ⟨(mem_nonNeighborFinset.mp hmem).1, (mem_nonNeighborFinset.mp hmem).2, ?_⟩
  intro x hxv hxr
  by_contra hcon
  have hx : x ∈ nonNeighborFinset L v := mem_nonNeighborFinset.mpr ⟨hxv, hcon⟩
  rw [h, Finset.mem_singleton] at hx
  exact hxr hx

/-- A vertex whose non-neighbour set is a given pair is adjacent to every other vertex. -/
theorem adj_of_nonNeighborFinset_eq_pair {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] {v x y : W} (h : nonNeighborFinset L v = {x, y}) :
    ∀ z : W, z ≠ v → z ≠ x → z ≠ y → L.Adj v z := by
  intro z hzv hzx hzy
  by_contra hcon
  have hmem : z ∈ nonNeighborFinset L v := mem_nonNeighborFinset.mpr ⟨hzv, hcon⟩
  rw [h, Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem.elim hzx hzy

/-- In a five-vertex graph, two distinct non-neighbours of a vertex of degree two exhaust its
non-neighbour set. -/
theorem nonNeighborFinset_eq_pair {W : Type u} [Fintype W] [DecidableEq W] (L : SimpleGraph W)
    [DecidableRel L.Adj] (hcard : Fintype.card W = 5) {v x y : W}
    (hx : x ∈ nonNeighborFinset L v) (hy : y ∈ nonNeighborFinset L v) (hxy : x ≠ y)
    (hv : L.degree v = 2) : nonNeighborFinset L v = {x, y} := by
  have hsub : ({x, y} : Finset W) ⊆ nonNeighborFinset L v := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [card_nonNeighborFinset, hcard, hv, Finset.card_eq_two.mpr ⟨x, y, hxy, rfl⟩])).symm

/-! ### 4. The four-vertex bound -/

/-- Splitting the edges of `L` by whether they meet `v`: the edges avoiding `v` are the edges of
the induced subgraph on `univ.erase v`, and the edges meeting `v` are counted by the degree. -/
theorem edgeFinset_card_eq_induce_erase_add_degree {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] (v : W) :
    L.edgeFinset.card = (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card
      + L.degree v := by
  classical
  have h := card_filter_edgeFinset_subset_erase L (Finset.univ : Finset W) (Finset.mem_univ v)
  simp only [Finset.subset_univ, Finset.filter_true, Finset.inter_univ] at h
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h
  rw [← card_filter_edgeFinset_toFinset_subset (G := L) (s := Finset.univ.erase v)]
  exact h

/-- **Four-vertex bound.** A graph on exactly four vertices with no `4`-cycle has at most four
edges: with five edges every vertex would have degree at least two, and
`exists_walk_isCycle_length_four_of_card_four` then produces a `4`-cycle. -/
theorem card_edgeFinset_le_four_of_card_four {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] (hcard : Fintype.card W = 4)
    (hcyc : ¬ HasFourCycle L) : L.edgeFinset.card ≤ 4 := by
  classical
  by_contra hle
  have h5 : 5 ≤ L.edgeFinset.card := by omega
  have hdeg : ∀ v : W, 2 ≤ L.degree v := by
    intro v
    have hsplit := edgeFinset_card_eq_induce_erase_add_degree L v
    have hcard3 : Fintype.card ↥(((Finset.univ.erase v : Finset W)) : Set W) = 3 := by
      rw [← Set.toFinset_card, Finset.toFinset_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
        Finset.card_univ, hcard]
    have hle3 : (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card ≤ 3 := by
      have hchoose := SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := L.induce ((Finset.univ.erase v : Finset W) : Set W))
      rw [hcard3] at hchoose
      simpa using hchoose
    omega
  obtain ⟨v, c, hc, hlen⟩ := exists_walk_isCycle_length_four_of_card_four L hcard hdeg
  exact hcyc ⟨v, c, hc, hlen⟩

/-! ### 5. The five-vertex edge bound

Double counting: for a five-vertex graph `L`, summing `|E(L - v)| = |E(L)| - d(v)` over the five
vertices gives `3 |E(L)| = Σ_v |E(L - v)| ≤ 5 · 4`, since each four-vertex induced subgraph has
at most four edges.  Hence `|E(L)| ≤ 6`, with no hypothesis beyond four-cycle-freeness. -/

/-- **Five-vertex bound.** A graph on exactly five vertices with no `4`-cycle has at most six
edges. -/
theorem card_edgeFinset_le_six_of_card_five {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] (hcard : Fintype.card W = 5)
    (hcyc : ¬ HasFourCycle L) : L.edgeFinset.card ≤ 6 := by
  classical
  have hstep : ∀ v : W, L.edgeFinset.card
      = (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card + L.degree v :=
    fun v => edgeFinset_card_eq_induce_erase_add_degree L v
  have hbound : ∀ v : W,
      (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card ≤ 4 := by
    intro v
    refine card_edgeFinset_le_four_of_card_four _ ?_ ?_
    · rw [← Set.toFinset_card, Finset.toFinset_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
        Finset.card_univ, hcard]
    · exact not_hasFourCycle_induce L _ hcyc
  have hsum : (∑ v : W, L.edgeFinset.card)
      = ∑ v : W, ((L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card
        + L.degree v) :=
    Finset.sum_congr rfl fun v _ => hstep v
  have hleft : (∑ v : W, L.edgeFinset.card) = 5 * L.edgeFinset.card := by
    rw [Finset.sum_const, Finset.card_univ, hcard]
    simp
  have hright : (∑ v : W, ((L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card
        + L.degree v))
      = (∑ v : W, (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card)
        + 2 * L.edgeFinset.card := by
    rw [Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hmain : 5 * L.edgeFinset.card
      = (∑ v : W, (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card)
        + 2 * L.edgeFinset.card := by
    rw [← hleft, hsum, hright]
  have hupper : (∑ v : W,
      (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card) ≤ 20 := by
    calc (∑ v : W, (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card)
        ≤ ∑ _v : W, 4 := Finset.sum_le_sum fun v _ => hbound v
      _ = 20 := by rw [Finset.sum_const, Finset.card_univ, hcard]; norm_num
  omega

/-! ### 6. The five-vertex common-neighbour lemma

A five-vertex graph with six edges and no `4`-cycle has a common neighbour for every pair of
vertices.  All degrees are at least two (the four-vertex bound applied to `L - v`), so the degree
sum `12` leaves the degree sequences `(4,2,2,2,2)` and `(3,3,2,2,2)`.  In the first case the
degree-four vertex is a common neighbour of every pair.  In the second case the two degree-three
vertices have a unique non-neighbour each, and either those non-neighbours coincide (which forces
a third vertex of degree three where the count allows only two) or they differ (which produces a
`4`-cycle). -/

/-- **Five-vertex common-neighbour lemma.** A graph on exactly five vertices with six edges and no
`4`-cycle has a common neighbour for every pair of distinct vertices. -/
theorem exists_common_neighbor_of_card_five_card_six {W : Type u} [Fintype W] [DecidableEq W]
    (L : SimpleGraph W) [DecidableRel L.Adj] (hcard : Fintype.card W = 5)
    (hedge : L.edgeFinset.card = 6) (hcyc : ¬ HasFourCycle L) :
    ∀ u w : W, u ≠ w → ∃ x : W, L.Adj u x ∧ L.Adj w x := by
  classical
  have hdeg2 : ∀ v : W, 2 ≤ L.degree v := by
    intro v
    have hsplit := edgeFinset_card_eq_induce_erase_add_degree L v
    have hcard4 : Fintype.card ↥(((Finset.univ.erase v : Finset W)) : Set W) = 4 := by
      rw [← Set.toFinset_card, Finset.toFinset_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
        Finset.card_univ, hcard]
    have hle4 : (L.induce ((Finset.univ.erase v : Finset W) : Set W)).edgeFinset.card ≤ 4 :=
      card_edgeFinset_le_four_of_card_four _ hcard4 (not_hasFourCycle_induce L _ hcyc)
    omega
  have hdeg4 : ∀ v : W, L.degree v ≤ 4 := by
    intro v
    have := L.degree_lt_card_verts v
    omega
  have hsum : (∑ v : W, L.degree v) = 12 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges L, hedge]
  by_cases h4 : ∃ c : W, L.degree c = 4
  · -- a vertex of degree four is a common neighbour of every pair
    obtain ⟨c, hc⟩ := h4
    have hnb : L.neighborFinset c = Finset.univ.erase c := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        rw [SimpleGraph.mem_neighborFinset] at hv
        rw [Finset.mem_erase]
        exact ⟨hv.ne.symm, Finset.mem_univ v⟩
      · rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, hcard,
          SimpleGraph.card_neighborFinset_eq_degree, hc]
    have hadj : ∀ v : W, v ≠ c → L.Adj c v := by
      intro v hv
      have hv' : v ∈ L.neighborFinset c := by
        rw [hnb, Finset.mem_erase]
        exact ⟨hv, Finset.mem_univ v⟩
      exact (SimpleGraph.mem_neighborFinset L c v).mp hv'
    have hstep : ∀ z : W, z ≠ c → ∃ x : W, L.Adj c x ∧ L.Adj z x := by
      intro z hz
      have hzc : L.Adj z c := (hadj z hz).symm
      have hzcN : c ∈ L.neighborFinset z := (SimpleGraph.mem_neighborFinset L z c).mpr hzc
      have hpos : 0 < ((L.neighborFinset z).erase c).card := by
        rw [Finset.card_erase_of_mem hzcN, SimpleGraph.card_neighborFinset_eq_degree]
        have hz2 := hdeg2 z
        omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      have hxc : x ≠ c := (Finset.mem_erase.mp hx).1
      exact ⟨x, hadj x hxc,
        (SimpleGraph.mem_neighborFinset L z x).mp (Finset.mem_of_mem_erase hx)⟩
    intro u w huw
    by_cases huc : u = c
    · subst huc
      obtain ⟨x, h1, h2⟩ := hstep w huw.symm
      exact ⟨x, h1, h2⟩
    · by_cases hwc : w = c
      · subst hwc
        obtain ⟨x, h1, h2⟩ := hstep u huw
        exact ⟨x, h2, h1⟩
      · exact ⟨c, (hadj u huc).symm, (hadj w hwc).symm⟩
  · exfalso
    have hdeg3 : ∀ v : W, L.degree v ≤ 3 := by
      intro v
      by_contra hcon
      have h4v := hdeg4 v
      exact h4 ⟨v, by omega⟩
    have hpt : ∀ v : W, L.degree v = 2 + (if L.degree v = 3 then 1 else 0) := by
      intro v
      have h2 := hdeg2 v
      have h3 := hdeg3 v
      split_ifs with h <;> omega
    have hsum3 : (∑ v : W, L.degree v)
        = ∑ v : W, (2 + (if L.degree v = 3 then 1 else 0)) :=
      Finset.sum_congr rfl fun v _ => hpt v
    have hsum4 : (∑ v : W, (2 + (if L.degree v = 3 then 1 else 0)))
        = 5 * 2 + ∑ v : W, (if L.degree v = 3 then 1 else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard]
      simp
    have hthree : (Finset.univ.filter (fun v : W => L.degree v = 3)).card = 2 := by
      rw [Finset.card_filter]
      omega
    obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.mp hthree
    have hp3 : L.degree p = 3 := by
      have hp : p ∈ Finset.univ.filter (fun v : W => L.degree v = 3) := by
        rw [hpqeq]; exact Finset.mem_insert_self p {q}
      exact (Finset.mem_filter.mp hp).2
    have hq3 : L.degree q = 3 := by
      have hq : q ∈ Finset.univ.filter (fun v : W => L.degree v = 3) := by
        rw [hpqeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
      exact (Finset.mem_filter.mp hq).2
    have hother : ∀ v : W, v ≠ p → v ≠ q → L.degree v = 2 := by
      intro v hvp hvq
      have hv : v ∉ Finset.univ.filter (fun v : W => L.degree v = 3) := by
        rw [hpqeq]; simp [hvp, hvq]
      have hv3 : L.degree v ≠ 3 := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have h2 := hdeg2 v
      have h3 := hdeg3 v
      omega
    obtain ⟨rp, hrp⟩ := exists_nonNeighborFinset_eq_singleton L hcard hp3
    obtain ⟨rq, hrq⟩ := exists_nonNeighborFinset_eq_singleton L hcard hq3
    obtain ⟨hrp_ne_p, hprp, hpall⟩ := adj_of_nonNeighborFinset_eq_singleton L hrp
    obtain ⟨hrq_ne_q, hqrq, hqall⟩ := adj_of_nonNeighborFinset_eq_singleton L hrq
    by_cases hpqadj : L.Adj p q
    · -- `p` and `q` are adjacent
      by_cases hrpq : rp = rq
      · -- their non-neighbours coincide: one of the two remaining vertices has degree three
        have hqrp : ¬ L.Adj q rp := by rw [hrpq]; exact hqrq
        have hr_ne_q : rp ≠ q := fun h => hprp (by rw [h]; exact hpqadj)
        have hr_deg : L.degree rp = 2 := hother rp hrp_ne_p hr_ne_q
        have hpair : nonNeighborFinset L rp = ({p, q} : Finset W) := by
          refine nonNeighborFinset_eq_pair L hcard ?_ ?_ hpq hr_deg
          · exact mem_nonNeighborFinset.mpr ⟨hrp_ne_p.symm, fun h => hprp h.symm⟩
          · exact mem_nonNeighborFinset.mpr ⟨hr_ne_q.symm, fun h => hqrp h.symm⟩
        obtain ⟨a, b, hab, ha, hb⟩ := exists_two_notMem_of_card_le ({p, q, rp} : Finset W) (by
          have h1 := Finset.card_insert_le p ({q, rp} : Finset W)
          have h2 := Finset.card_insert_le q ({rp} : Finset W)
          rw [Finset.card_singleton] at h2
          omega)
        have ha' : a ≠ p ∧ a ≠ q ∧ a ≠ rp := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using ha
        have hb' : b ≠ p ∧ b ≠ q ∧ b ≠ rp := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hb
        have hneigh : ({p, q, rp} : Finset W) ⊆ L.neighborFinset a := by
          intro x hx
          rw [SimpleGraph.mem_neighborFinset]
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (hpall a ha'.1 ha'.2.2).symm
          · exact (hqall a ha'.2.1 (by rw [← hrpq]; exact ha'.2.2)).symm
          · exact (adj_of_nonNeighborFinset_eq_pair L hpair a ha'.2.2 ha'.1 ha'.2.1).symm
        have h3 : 3 ≤ (L.neighborFinset a).card := by
          have hle := Finset.card_le_card hneigh
          rwa [card_triple hpq hrp_ne_p.symm hr_ne_q.symm] at hle
        rw [SimpleGraph.card_neighborFinset_eq_degree, hother a ha'.1 ha'.2.1] at h3
        omega
      · -- their non-neighbours differ: `rp - rq - p - q - rp` is a four-cycle
        have hrp_ne_q : rp ≠ q := fun h => hprp (by rw [h]; exact hpqadj)
        have hrq_ne_p : rq ≠ p := fun h => hqrq (by rw [h]; exact hpqadj.symm)
        have hrp_deg : L.degree rp = 2 := hother rp hrp_ne_p hrp_ne_q
        have hrq_deg : L.degree rq = 2 := hother rq hrq_ne_p hrq_ne_q
        obtain ⟨c, hc⟩ := exists_notMem_of_card_le ({p, q, rp, rq} : Finset W) (by
          have h1 := Finset.card_insert_le p ({q, rp, rq} : Finset W)
          have h2 := Finset.card_insert_le q ({rp, rq} : Finset W)
          have h3 := Finset.card_insert_le rp ({rq} : Finset W)
          rw [Finset.card_singleton] at h3
          omega)
        have hc' : c ≠ p ∧ c ≠ q ∧ c ≠ rp ∧ c ≠ rq := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hc
        have hcp : L.Adj c p := (hpall c hc'.1 hc'.2.2.1).symm
        have hcq : L.Adj c q := (hqall c hc'.2.1 hc'.2.2.2).symm
        have hcdeg : L.degree c = 2 := hother c hc'.1 hc'.2.1
        have hcpair : L.neighborFinset c = ({p, q} : Finset W) := by
          have hsub : ({p, q} : Finset W) ⊆ L.neighborFinset c := by
            intro z hz
            rw [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hzp | hzq
            · rw [hzp]
              exact (SimpleGraph.mem_neighborFinset L c p).mpr hcp
            · rw [hzq]
              exact (SimpleGraph.mem_neighborFinset L c q).mpr hcq
          exact (Finset.eq_of_subset_of_card_le hsub (by
            rw [SimpleGraph.card_neighborFinset_eq_degree, hcdeg,
              Finset.card_eq_two.mpr ⟨p, q, hpq, rfl⟩])).symm
        have hcrp : ¬ L.Adj c rp := by
          intro hcon
          have hmem : rp ∈ L.neighborFinset c := (SimpleGraph.mem_neighborFinset L c rp).mpr hcon
          rw [hcpair, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h
          · exact hrp_ne_p h
          · exact hrp_ne_q h
        have hcrq : ¬ L.Adj c rq := by
          intro hcon
          have hmem : rq ∈ L.neighborFinset c := (SimpleGraph.mem_neighborFinset L c rq).mpr hcon
          rw [hcpair, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h
          · exact hrq_ne_p h
          · exact hrq_ne_q h
        have hpairp : nonNeighborFinset L rp = ({p, c} : Finset W) := by
          refine nonNeighborFinset_eq_pair L hcard ?_ ?_ ?_ hrp_deg
          · exact mem_nonNeighborFinset.mpr ⟨hrp_ne_p.symm, fun h => hprp h.symm⟩
          · exact mem_nonNeighborFinset.mpr ⟨hc'.2.2.1, fun h => hcrp h.symm⟩
          · exact hc'.1.symm
        have hpairq : nonNeighborFinset L rq = ({q, c} : Finset W) := by
          refine nonNeighborFinset_eq_pair L hcard ?_ ?_ ?_ hrq_deg
          · exact mem_nonNeighborFinset.mpr ⟨hrq_ne_q.symm, fun h => hqrq h.symm⟩
          · exact mem_nonNeighborFinset.mpr ⟨hc'.2.2.2, fun h => hcrq h.symm⟩
          · exact hc'.2.1.symm
        have h1 : L.Adj rp rq :=
          adj_of_nonNeighborFinset_eq_pair L hpairp rq (fun h => hrpq h.symm) hrq_ne_p
            (Ne.symm hc'.2.2.2)
        have h2 : L.Adj rq p :=
          adj_of_nonNeighborFinset_eq_pair L hpairq p (Ne.symm hrq_ne_p) hpq hc'.1.symm
        have h4 : L.Adj q rp :=
          (adj_of_nonNeighborFinset_eq_pair L hpairp q (Ne.symm hrp_ne_q) hpq.symm
            hc'.2.1.symm).symm
        exact hcyc (hasFourCycle_of_four_cycle_adj L h1 h2 hpqadj h4 hrp_ne_p hrq_ne_q)
    · -- `p` and `q` are not adjacent, so each is adjacent to both remaining vertices
      have hrp_eq_q : rp = q := by
        have hqmem : q ∈ nonNeighborFinset L p := mem_nonNeighborFinset.mpr ⟨hpq.symm, hpqadj⟩
        rw [hrp, Finset.mem_singleton] at hqmem
        exact hqmem.symm
      have hrq_eq_p : rq = p := by
        have hpmem : p ∈ nonNeighborFinset L q :=
          mem_nonNeighborFinset.mpr ⟨hpq, fun h => hpqadj h.symm⟩
        rw [hrq, Finset.mem_singleton] at hpmem
        exact hpmem.symm
      have hpall' : ∀ x : W, x ≠ p → x ≠ q → L.Adj p x := by
        intro x hxp hxq
        exact hpall x hxp (by rw [hrp_eq_q]; exact hxq)
      have hqall' : ∀ x : W, x ≠ q → x ≠ p → L.Adj q x := by
        intro x hxq hxp
        exact hqall x hxq (by rw [hrq_eq_p]; exact hxp)
      obtain ⟨a, b, hab, ha, hb⟩ := exists_two_notMem_of_card_le ({p, q} : Finset W) (by
        have h1 := Finset.card_insert_le p ({q} : Finset W)
        rw [Finset.card_singleton] at h1
        omega)
      have ha' : a ≠ p ∧ a ≠ q := by simpa [Finset.mem_insert, Finset.mem_singleton] using ha
      have hb' : b ≠ p ∧ b ≠ q := by simpa [Finset.mem_insert, Finset.mem_singleton] using hb
      exact hcyc (hasFourCycle_of_four_cycle_adj L (hpall' a ha'.1 ha'.2).symm
        (hpall' b hb'.1 hb'.2) (hqall' b hb'.2 hb'.1).symm (hqall' a ha'.2 ha'.1) hab hpq)

/-! ### 7. Target A: the sharp edge bound for four-cycle-free `2`-degenerate graphs -/

/-- Induced-subgraph form of the sharp `2`-degenerate edge bound, by strong induction on the
number of vertices.  The step peels a vertex `v` of degree at most two; the case of six
vertices needs the five-vertex common-neighbour lemma to exclude the case where `v` has degree
two and the remainder has six edges. -/
theorem card_edgeFinset_induce_le_two_mul_card_sub_five_finset {W : Type u} [Fintype W]
    [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (hhered : ∀ (t : Finset W), t.Nonempty →
      ∃ v : ↥(t : Set W), (K.induce (t : Set W)).degree v ≤ 2)
    (hcyc : ¬ HasFourCycle K) (s : Finset W) (hcard : 6 ≤ s.card) :
    (K.induce (s : Set W)).edgeFinset.card ≤ 2 * s.card - 5 := by
  classical
  suffices H : ∀ n, ∀ s : Finset W, s.card = n → 6 ≤ s.card →
      (K.induce (s : Set W)).edgeFinset.card ≤ 2 * s.card - 5 from H s.card s rfl hcard
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hvdeg⟩ := hhered s hsne
    have hvmem : (v : W) ∈ s := v.property
    have hsplit : (K.induce (s : Set W)).edgeFinset.card
        = (K.induce ((s.erase (v : W)) : Set W)).edgeFinset.card
          + (K.induce (s : Set W)).degree v := by
      rw [← card_filter_edgeFinset_toFinset_subset (G := K) (s := s),
        ← card_filter_edgeFinset_toFinset_subset (G := K) (s := s.erase (v : W)),
        degree_induce_coe_eq K s v]
      exact card_filter_edgeFinset_subset_erase K s hvmem
    have hcard' : (s.erase (v : W)).card = s.card - 1 := Finset.card_erase_of_mem hvmem
    rcases eq_or_lt_of_le hcard with h6 | h7
    · -- base case: six vertices
      have hs' : (s.erase (v : W)).card = 5 := by rw [hcard', ← h6]
      have hcyc' : ¬ HasFourCycle (K.induce ((s.erase (v : W)) : Set W)) :=
        not_hasFourCycle_induce K _ hcyc
      have hcard5 : Fintype.card ↥(((s.erase (v : W)) : Set W)) = 5 := by
        rw [← Set.toFinset_card, Finset.toFinset_coe, hs']
      have hle6 : (K.induce ((s.erase (v : W)) : Set W)).edgeFinset.card ≤ 6 :=
        card_edgeFinset_le_six_of_card_five _ hcard5 hcyc'
      suffices hfin : (K.induce (s : Set W)).edgeFinset.card ≤ 7 by
        rw [← h6]
        exact hfin
      by_cases h5 : (K.induce ((s.erase (v : W)) : Set W)).edgeFinset.card ≤ 5
      · omega
      · have heq6 : (K.induce ((s.erase (v : W)) : Set W)).edgeFinset.card = 6 := by omega
        by_cases hd1 : ((K.induce (s : Set W)).degree v) ≤ 1
        · omega
        · exfalso
          have hdeg2 : (K.induce (s : Set W)).degree v = 2 := by omega
          -- the two neighbours of `v` inside the five-vertex remainder
          have hneighcard : ((K.induce (s : Set W)).neighborFinset v).card = 2 := by
            rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg2]
          obtain ⟨u, w, huw, huneigh⟩ := Finset.card_eq_two.mp hneighcard
          have hvu : (K.induce (s : Set W)).Adj v u :=
            (SimpleGraph.mem_neighborFinset _ _ _).mp
              (by rw [huneigh]; exact Finset.mem_insert_self u {w})
          have hvw : (K.induce (s : Set W)).Adj v w :=
            (SimpleGraph.mem_neighborFinset _ _ _).mp
              (by rw [huneigh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
          have hu_ne_v : (u : W) ≠ (v : W) := fun h => hvu.ne (Subtype.ext h).symm
          have hw_ne_v : (w : W) ≠ (v : W) := fun h => hvw.ne (Subtype.ext h).symm
          let u' : ↥(((s.erase (v : W)) : Finset W) : Set W) :=
            ⟨(u : W), by rw [Finset.mem_coe, Finset.mem_erase]; exact ⟨hu_ne_v, u.property⟩⟩
          let w' : ↥(((s.erase (v : W)) : Finset W) : Set W) :=
            ⟨(w : W), by rw [Finset.mem_coe, Finset.mem_erase]; exact ⟨hw_ne_v, w.property⟩⟩
          have hu'w' : u' ≠ w' := by
            intro hc
            have h : (u : W) = (w : W) :=
              congrArg (fun z : ↥(((s.erase (v : W)) : Finset W) : Set W) => (z : W)) hc
            exact huw (Subtype.ext h)
          obtain ⟨x, hx1, hx2⟩ := exists_common_neighbor_of_card_five_card_six
            (K.induce ((s.erase (v : W)) : Set W)) hcard5 heq6 hcyc' u' w' hu'w'
          have hvx : (x : W) ≠ (v : W) := by
            have hx := x.property
            rw [Finset.mem_coe, Finset.mem_erase] at hx
            exact hx.1
          have hvuK : K.Adj (v : W) (u : W) := hvu
          have hvwK : K.Adj (v : W) (w : W) := hvw
          have hx1K : K.Adj (u : W) (x : W) := hx1
          have hx2K : K.Adj (w : W) (x : W) := hx2
          exact hcyc (hasFourCycle_of_four_cycle_adj K hvuK hx1K hx2K.symm hvwK.symm hvx.symm
            (fun h => huw (Subtype.ext h)))
    · -- induction step: at least seven vertices
      have hge : 6 ≤ (s.erase (v : W)).card := by rw [hcard']; omega
      have hlt : (s.erase (v : W)).card < n := by rw [hcard', hs]; omega
      have ih' := ih (s.erase (v : W)).card hlt (s.erase (v : W)) rfl hge
      omega

/-- **Target A: sharp `2`-degenerate edge bound.** A finite simple graph all of whose nonempty
induced subgraphs have a vertex of degree at most two, with at least six vertices and no simple
`4`-cycle, has at most `2n - 5` edges.  This sharpens
`card_edgeFinset_induce_le_two_mul_card_sub_three` by two under the four-cycle hypothesis. -/
theorem card_edgeFinset_le_two_mul_card_sub_five {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj]
    (hhered : ∀ (t : Finset W), t.Nonempty →
      ∃ v : ↥(t : Set W), (K.induce (t : Set W)).degree v ≤ 2)
    (hcard : 6 ≤ Fintype.card W) (hcyc : ¬ HasFourCycle K) :
    K.edgeFinset.card ≤ 2 * Fintype.card W - 5 := by
  classical
  have h := card_edgeFinset_induce_le_two_mul_card_sub_five_finset K hhered hcyc Finset.univ
    (by simpa using hcard)
  have hedge : (K.induce (↑(Finset.univ : Finset W) : Set W)).edgeFinset.card = K.edgeFinset.card := by
    rw [← card_filter_edgeFinset_toFinset_subset (G := K) (s := Finset.univ)]
    simp
  rw [hedge, Finset.card_univ] at h
  exact h

/-! ### 8. Target B: the sharp `L₂` bound for a minimal counterexample -/

/-- **Target B: sharp `L₂` bound.** In a minimal counterexample with `h = |H| ≥ 6`, the number
of degree-three vertices with two high-degree neighbours is at most `2h - 5`.  This sharpens
`card_degreeThreeTwoHigh_le_two_mul_card_sub_three` by two, using the four-cycle-freeness of the
doubling graph (`not_hasPowerOfTwoCycle_doublingGraph`). -/
theorem card_degreeThreeTwoHigh_le_two_mul_card_sub_five {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    (h6 : 6 ≤ (degreeGeFourFinset G).card) :
    (degreeThreeTwoHigh G).card ≤ 2 * (degreeGeFourFinset G).card - 5 := by
  classical
  have hhered : ∀ (t : Finset ↥(degreeGeFourFinset G)), t.Nonempty →
      ∃ v : ↥(t : Set ↥(degreeGeFourFinset G)),
        ((doublingGraph G).induce (t : Set ↥(degreeGeFourFinset G))).degree v ≤ 2 := by
    intro t htne
    have hne : Nonempty ↥(t : Set ↥(degreeGeFourFinset G)) := by
      obtain ⟨x, hx⟩ := htne
      exact ⟨⟨x, by simpa using hx⟩⟩
    exact exists_degree_le_two_induce_doublingGraph hmin (t : Set ↥(degreeGeFourFinset G)) hne
  have hcyc : ¬ HasFourCycle (doublingGraph G) := fun h =>
    not_hasPowerOfTwoCycle_doublingGraph hmin.not_hasPowerOfTwoCycle
      (hasPowerOfTwoCycle_of_hasFourCycle h)
  have hbound := card_edgeFinset_le_two_mul_card_sub_five (doublingGraph G) hhered
    (by rw [Fintype.card_coe]; exact h6) hcyc
  rw [Fintype.card_coe] at hbound
  rw [← card_degreeThreeTwoHigh_eq_card_edgeFinset hmin.not_hasPowerOfTwoCycle] at hbound
  exact hbound

/-! ### 9. Target C: the parity refinement `2h + 6 ≤ ℓ`

Every vertex of `L` has degree three, and each of its neighbours lies in `L` or in `H`; so the
degree of `v` inside `G[L]` plus the number of high-degree neighbours of `v` is three.  Summing
over `L` gives `2 |E(G[L])| + (|L₁| + 2|L₂|) = 3ℓ`.  Combined with the crossing count
`4h ≤ |L₁| + 2|L₂|`, the partition bound `ℓ ≥ |L₁| + |L₂|` and Target B, the equality case
`ℓ = 2h + 5` would force `2 |E(G[L])| = 2h + 15`, which is impossible by parity. -/

/-- **Degree sum inside `G[L]`.** In a minimal counterexample, twice the number of edges of the
induced graph on `L`, plus the number of `L`–`H` incidences `|L₁| + 2|L₂|`, equals `3ℓ`. -/
theorem two_mul_card_edgeFinset_induce_degreeThreeFinset_add_incidences {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    2 * (G.induce ((degreeThreeFinset G : Finset V) : Set V)).edgeFinset.card
        + ((degreeThreeOneHigh G).card + 2 * (degreeThreeTwoHigh G).card)
      = 3 * (degreeThreeFinset G).card := by
  classical
  set Lset : Set V := (degreeThreeFinset G : Set V) with hLset
  have hdeg : ∀ v : ↥Lset,
      (G.induce Lset).degree v + (highDegreeNeighbors G (v : V)).card = 3 := by
    intro v
    have hv3 : G.degree (v : V) = 3 := mem_degreeThreeFinset.mp v.property
    have hdisj : Disjoint (G.neighborFinset (v : V) ∩ degreeThreeFinset G)
        (G.neighborFinset (v : V) ∩ degreeGeFourFinset G) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_inter] at hx1 hx2
      have h := disjoint_degreeThreeFinset_degreeGeFourFinset (G := G)
      rw [Finset.disjoint_left] at h
      exact h hx1.2 hx2.2
    have hunion : (G.neighborFinset (v : V) ∩ degreeThreeFinset G)
        ∪ (G.neighborFinset (v : V) ∩ degreeGeFourFinset G) = G.neighborFinset (v : V) := by
      rw [← Finset.inter_union_distrib_left, degreeThreeFinset_union_degreeGeFourFinset hmin,
        Finset.inter_univ]
    have hcard : (G.neighborFinset (v : V) ∩ degreeThreeFinset G).card
        + (G.neighborFinset (v : V) ∩ degreeGeFourFinset G).card = G.degree (v : V) := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion,
        SimpleGraph.card_neighborFinset_eq_degree]
    have hH : (G.neighborFinset (v : V) ∩ degreeGeFourFinset G).card
        = (highDegreeNeighbors G (v : V)).card := by
      congr 1
      rw [← Finset.filter_mem_eq_inter]
      simp only [highDegreeNeighbors]
      exact Finset.filter_congr fun a _ => by simp [mem_degreeGeFourFinset, degreeGeFour]
    have hL : (G.neighborFinset (v : V) ∩ degreeThreeFinset G).card
        = (G.induce Lset).degree v := (degree_induce_coe_eq G (degreeThreeFinset G) v).symm
    omega
  have hsum1 : (∑ v : ↥Lset, (G.induce Lset).degree v)
      + (∑ v : ↥Lset, (highDegreeNeighbors G (v : V)).card)
      = 3 * (degreeThreeFinset G).card := by
    have h1 : (∑ v : ↥Lset,
        ((G.induce Lset).degree v + (highDegreeNeighbors G (v : V)).card))
        = ∑ _v : ↥Lset, 3 := Finset.sum_congr rfl fun v _ => hdeg v
    have hcardL : Fintype.card ↥Lset = (degreeThreeFinset G).card := by
      change Fintype.card ↥(↑(degreeThreeFinset G) : Set V) = (degreeThreeFinset G).card
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardL] at h1
    simp only [smul_eq_mul] at h1
    omega
  have hsum2 : (∑ v : ↥Lset, (highDegreeNeighbors G (v : V)).card)
      = (degreeThreeOneHigh G).card + 2 * (degreeThreeTwoHigh G).card := by
    rw [← Finset.sum_subtype (p := fun v : V => v ∈ Lset) (degreeThreeFinset G)
      (fun v : V => by rw [hLset]; simp) (fun v : V => (highDegreeNeighbors G v).card)]
    exact sum_eq_card_filter_one_add_two_mul_card_filter_two (degreeThreeFinset G)
      (fun v => (highDegreeNeighbors G v).card)
      (fun v hv => card_highDegreeNeighbors_le_two hmin (mem_degreeThreeFinset.mp hv))
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges (G := G.induce Lset), hsum2] at hsum1
  exact hsum1

/-- **Target C: sharp density for `h ≥ 6`.** A minimal counterexample with `h = |H| ≥ 6`
satisfies `2h + 6 ≤ ℓ`, one better than the `2h + 3` of
`two_mul_card_degreeGeFourFinset_add_three_le_card_degreeThreeFinset`.  Equivalently
`2n + 6 ≤ 3ℓ`, i.e. `ℓ ≥ 2n/3 + 2`. -/
theorem two_mul_card_degreeGeFourFinset_add_six_le_card_degreeThreeFinset {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    (h6 : 6 ≤ (degreeGeFourFinset G).card) :
    2 * (degreeGeFourFinset G).card + 6 ≤ (degreeThreeFinset G).card := by
  have hcount := four_mul_card_degreeGeFourFinset_le hmin
  have hL2 := card_degreeThreeTwoHigh_le_two_mul_card_sub_five hmin h6
  have hpart := card_degreeThreeOneHigh_add_card_degreeThreeTwoHigh_le G
  have hparity := two_mul_card_edgeFinset_induce_degreeThreeFinset_add_incidences hmin
  by_contra hcon
  push Not at hcon
  omega

/-- **Target C, order-conditional form.** A minimal counterexample on `n ≥ 24` vertices satisfies
`2h + 6 ≤ ℓ` with *no* restriction on `h = |H|`.  The case split is on `6 ≤ h`: above it the sharp
bound `two_mul_card_degreeGeFourFinset_add_six_le_card_degreeThreeFinset` applies verbatim, and
below it the vertex partition `ℓ + h = n` of `Density.lean` already suffices, because `n ≥ 24` and
`h ≤ 5` force `ℓ = n - h ≥ 19 ≥ 2h + 6`.

SCOPE.  The order hypothesis `24 ≤ Fintype.card V` is an explicit hypothesis, not a theorem of this
file: it stands in for the external fact that a counterexample to the source conjecture has order at
least `24`.  That external fact is neither formalized nor claimed here, so this statement carries no
information about minimal counterexamples of order below `24`; each use site must supply the
hypothesis itself. -/
theorem two_mul_card_degreeGeFourFinset_add_six_le_card_degreeThreeFinset_of_card_verts_ge
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) (hcard : 24 ≤ Fintype.card V) :
    2 * (degreeGeFourFinset G).card + 6 ≤ (degreeThreeFinset G).card := by
  by_cases h6 : 6 ≤ (degreeGeFourFinset G).card
  · exact two_mul_card_degreeGeFourFinset_add_six_le_card_degreeThreeFinset hmin h6
  · have hsmall : (degreeGeFourFinset G).card ≤ 5 := by omega
    have hpart := card_degreeThreeFinset_add_card_degreeGeFourFinset hmin
    omega

end Erdos64
