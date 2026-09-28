/-
Erdős–Gyárfás problem 64 — the numerical density stage.

PROVENANCE. arXiv:2609.28594 (Ducoffe–Dumitru), Section 3, subsections 3.1
(`General bounds`) and 3.2 (`The doubling reduction`); the counting argument in
the proofs of Proposition 3.4 (`prop:density`), Lemma 3.5 (`lem:D`), Corollary
3.6 (`cor:notall`) and Theorem 3.7 (`thm:density`). Graphs are finite, undirected
and simple
throughout; `hmin : Erdos64.IsMinimalCounterexample G` is lexicographic
minimality of `(number of vertices, number of edges)` among the
`Erdos64.IsCounterexample`s (see `Basic.lean`).

SOURCE CLAIM BOUNDARY. For a minimal counterexample `G` the source sets
`L = {v : d(v) = 3}`, `H = {v : d(v) ≥ 4}`, `ℓ = |L|`, `h = |H|`, and
partitions `L = L₀ ⊔ L₁ ⊔ L₂` by the number `i ∈ {0,1,2}` of neighbours in `H`.
The numerical content formalized here is:

* the double count `4h ≤ e(L,H) = |L₁| + 2|L₂|` of Proposition 3.4, equation
  (3.1), together with `|L₁| + |L₂| ≤ ℓ`;
* the `2`-degenerate edge bound `|L₂| = |E(M)| ≤ 2h - 3` for `h ≥ 2`
  (`M = doublingGraph G`), obtained from the hereditary low-degree property of
  `M` proved in `Doubling.lean` and a generic finite-`SimpleGraph` edge bound
  proved below;
* the small cases `h = 0`, `h = 1`, the latter via the source's `n = 5` / `C₄`
  obstruction;
* Corollary 3.6 (`L = L₂` is impossible) in explicit witness form: there is a
  vertex of `L` with at most one high-degree neighbour;
* Theorem 3.7 in the division-free form `2n + 3 ≤ 3ℓ`, which is exactly the
  rational inequality `ℓ ≥ 2n/3 + 1`, together with its `Nat`-division
  corollary.

Nothing about the crossing count, the edge bounds, or the cycle exclusions is
assumed: `M`'s simplicity and edge correspondence (`card_degreeThreeTwoHigh_eq_card_edgeFinset`),
its cycle lifting, and its hereditary `2`-degeneracy are all proved in
`Doubling.lean`, and the remaining counting is proved here. The only hypothesis
consumed is minimality, and it is used exactly where the source uses it.
-/

import Erdos.Erdos64.Doubling
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### 1. The partition of `L` by number of high-degree neighbours

The source partitions `L = {v : d(v) = 3}` into `L₀`, `L₁`, `L₂` according to
the number `i ∈ {0,1,2}` of neighbours of `v` in `H = {v : d(v) ≥ 4}`. The
bound `i ≤ 2` is `card_highDegreeNeighbors_le_two`. -/

/-- `L₀`, the degree-three vertices with no high-degree neighbour. -/
def degreeThreeZeroHigh (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finset V :=
  (degreeThreeFinset G).filter fun v => (highDegreeNeighbors G v).card = 0

/-- `L₁`, the degree-three vertices with exactly one high-degree neighbour. -/
def degreeThreeOneHigh (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Finset V :=
  (degreeThreeFinset G).filter fun v => (highDegreeNeighbors G v).card = 1

/-- Membership in `L₀`. -/
@[simp] theorem mem_degreeThreeZeroHigh {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v : V} : v ∈ degreeThreeZeroHigh G ↔ degreeThree G v ∧ (highDegreeNeighbors G v).card = 0 := by
  simp [degreeThreeZeroHigh]

/-- Membership in `L₁`. -/
@[simp] theorem mem_degreeThreeOneHigh {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {v : V} : v ∈ degreeThreeOneHigh G ↔ degreeThree G v ∧ (highDegreeNeighbors G v).card = 1 := by
  simp [degreeThreeOneHigh]

/-- `L₀` consists of degree-three vertices. -/
theorem degreeThreeZeroHigh_subset_degreeThreeFinset (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : degreeThreeZeroHigh G ⊆ degreeThreeFinset G :=
  Finset.filter_subset _ _

/-- `L₁` consists of degree-three vertices. -/
theorem degreeThreeOneHigh_subset_degreeThreeFinset (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : degreeThreeOneHigh G ⊆ degreeThreeFinset G :=
  Finset.filter_subset _ _

/-- `L₁` and `L₂` are disjoint. -/
theorem disjoint_degreeThreeOneHigh_degreeThreeTwoHigh (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : Disjoint (degreeThreeOneHigh G) (degreeThreeTwoHigh G) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rw [mem_degreeThreeOneHigh] at hv1
  rw [mem_degreeThreeTwoHigh] at hv2
  omega

/-- The two non-`L₀` parts of the partition sit inside `L`, so their sizes add up
to at most `ℓ`. This is the `ℓ ≥ |L₁| + |L₂|` half of the source's chain. -/
theorem card_degreeThreeOneHigh_add_card_degreeThreeTwoHigh_le (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] :
    (degreeThreeOneHigh G).card + (degreeThreeTwoHigh G).card ≤ (degreeThreeFinset G).card := by
  have hdisj := disjoint_degreeThreeOneHigh_degreeThreeTwoHigh G
  have hsub : degreeThreeOneHigh G ∪ degreeThreeTwoHigh G ⊆ degreeThreeFinset G :=
    Finset.union_subset (degreeThreeOneHigh_subset_degreeThreeFinset G)
      (degreeThreeTwoHigh_subset_degreeThreeFinset G)
  calc (degreeThreeOneHigh G).card + (degreeThreeTwoHigh G).card
      = (degreeThreeOneHigh G ∪ degreeThreeTwoHigh G).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (degreeThreeFinset G).card := Finset.card_le_card hsub

/-! ### 2. Double counting the `L`–`H` incidences

`e(L,H)` is symmetric in its two vertex classes, so the number of cross edges
computed from `H` equals the number computed from `L`. The `H` side sees at
least `4` per high-degree vertex (no edge joins two vertices of `H`, and every
neighbour of a high-degree vertex lies in `L`), while the `L` side sees exactly
`|L₁| + 2|L₂|` (a degree-three vertex has at most two high-degree neighbours). -/

/-- Double counting: the number of cross incidences computed class-by-class is
symmetric, because adjacency is symmetric. -/
theorem sum_card_filter_adj_comm (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (A B : Finset V) :
    (∑ a ∈ A, (B.filter fun b => G.Adj a b).card)
      = ∑ b ∈ B, (A.filter fun a => G.Adj b a).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [SimpleGraph.adj_comm]

/-- A sum `∑_{x ∈ s} f x` of a function bounded by `2` on `s` is `|s.filter (f=1)| +
`2|s.filter (f=2)|`. -/
theorem sum_eq_card_filter_one_add_two_mul_card_filter_two {α : Type*} (s : Finset α)
    (f : α → ℕ) (h : ∀ x ∈ s, f x ≤ 2) :
    (∑ x ∈ s, f x)
      = (s.filter fun x => f x = 1).card + 2 * (s.filter fun x => f x = 2).card := by
  have hpt : ∀ x ∈ s, f x = (if f x = 1 then 1 else 0) + 2 * (if f x = 2 then 1 else 0) := by
    intro x hx
    have := h x hx
    split_ifs <;> omega
  have h1 : (∑ x ∈ s, (if f x = 1 then 1 else 0)) = (s.filter fun x => f x = 1).card :=
    (Finset.card_filter (fun x => f x = 1) s).symm
  have h2 : (∑ x ∈ s, 2 * (if f x = 2 then 1 else 0))
      = 2 * (s.filter fun x => f x = 2).card := by
    rw [← Finset.mul_sum]
    congr 1
    exact (Finset.card_filter (fun x => f x = 2) s).symm
  calc (∑ x ∈ s, f x)
      = ∑ x ∈ s, ((if f x = 1 then 1 else 0) + 2 * (if f x = 2 then 1 else 0)) :=
        Finset.sum_congr rfl hpt
    _ = (∑ x ∈ s, (if f x = 1 then 1 else 0)) + ∑ x ∈ s, 2 * (if f x = 2 then 1 else 0) :=
        Finset.sum_add_distrib
    _ = (s.filter fun x => f x = 1).card + 2 * (s.filter fun x => f x = 2).card := by
        rw [h1, h2]

/-- The high-degree vertices adjacent to `v` are precisely the high-degree
neighbours of `v`. -/
theorem filter_degreeGeFourFinset_adj_eq_highDegreeNeighbors (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    (degreeGeFourFinset G).filter (fun a => G.Adj v a) = highDegreeNeighbors G v := by
  ext a
  simp [Finset.mem_filter]

/-- The `H`-class neighbour finset of a vertex of `L` is precisely the set of
neighbours of `a` — every neighbour of a high-degree vertex lies in `L`. -/
theorem filter_degreeThreeFinset_adj_eq_neighborFinset {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    {a : V} (ha : a ∈ degreeGeFourFinset G) :
    (degreeThreeFinset G).filter (fun v => G.Adj a v) = G.neighborFinset a := by
  rw [SimpleGraph.neighborFinset_eq_filter]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hav⟩; exact hav
  · intro hav
    exact ⟨mem_degreeThreeFinset.mpr
      (degreeThree_of_adj_degreeGeFour hmin hav (mem_degreeGeFourFinset.mp ha)), hav⟩

/-- **Proposition 3.4, equation (3.1).** `4h ≤ e(L,H) = |L₁| + 2|L₂|`. Every vertex of
`H` contributes its degree, at least four, to the cross count, while every vertex
of `L` contributes its number of high-degree neighbours, `0`, `1` or `2`. -/
theorem four_mul_card_degreeGeFourFinset_le {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    4 * (degreeGeFourFinset G).card
      ≤ (degreeThreeOneHigh G).card + 2 * (degreeThreeTwoHigh G).card := by
  have hswap := sum_card_filter_adj_comm G (degreeGeFourFinset G) (degreeThreeFinset G)
  have hHsum : (∑ a ∈ degreeGeFourFinset G,
        ((degreeThreeFinset G).filter fun v => G.Adj a v).card)
      = ∑ a ∈ degreeGeFourFinset G, G.degree a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [filter_degreeThreeFinset_adj_eq_neighborFinset hmin ha,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hHge : 4 * (degreeGeFourFinset G).card ≤ ∑ a ∈ degreeGeFourFinset G, G.degree a := by
    calc 4 * (degreeGeFourFinset G).card = ∑ _a ∈ degreeGeFourFinset G, 4 := by
          simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ a ∈ degreeGeFourFinset G, G.degree a :=
          Finset.sum_le_sum fun a ha => mem_degreeGeFourFinset.mp ha
  have hLsum : (∑ v ∈ degreeThreeFinset G,
        ((degreeGeFourFinset G).filter fun a => G.Adj v a).card)
      = ∑ v ∈ degreeThreeFinset G, (highDegreeNeighbors G v).card := by
    apply Finset.sum_congr rfl
    intro v _
    rw [filter_degreeGeFourFinset_adj_eq_highDegreeNeighbors G v]
  have hLbound := sum_eq_card_filter_one_add_two_mul_card_filter_two (degreeThreeFinset G)
    (fun v => (highDegreeNeighbors G v).card)
    (fun v hv => card_highDegreeNeighbors_le_two hmin (mem_degreeThreeFinset.mp hv))
  calc 4 * (degreeGeFourFinset G).card
      ≤ ∑ a ∈ degreeGeFourFinset G, G.degree a := hHge
    _ = ∑ a ∈ degreeGeFourFinset G, ((degreeThreeFinset G).filter fun v => G.Adj a v).card :=
        hHsum.symm
    _ = ∑ v ∈ degreeThreeFinset G, ((degreeGeFourFinset G).filter fun a => G.Adj v a).card :=
        hswap
    _ = ∑ v ∈ degreeThreeFinset G, (highDegreeNeighbors G v).card := hLsum
    _ = (degreeThreeOneHigh G).card + 2 * (degreeThreeTwoHigh G).card := hLbound

/-! ### 3. The `2`-degenerate edge bound

The source's Lemma 3.1 gives `m ≤ 2n - 3κ + ι` for a `2`-degenerate graph with
`κ` components and `ι` isolated vertices; the special case `|E| ≤ 2n - 3` for
`n ≥ 2` is what Lemma 3.5 consumes, and it is proved here by peeling a
degree-`≤ 2` vertex, using `card_edgeFinset_induce_compl_singleton`. -/

/-- Decompose an edge of `K` through a specified incident vertex. -/
theorem exists_eq_pair_of_mem_edgeSet {W : Type u} (K : SimpleGraph W) (v : W) (e : Sym2 W)
    (he : e ∈ K.edgeSet) (hv : v ∈ e) : ∃ u, e = s(v, u) ∧ K.Adj v u := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Sym2.mem_iff] at hv
    rw [SimpleGraph.mem_edgeSet] at he
    rcases hv with h | h
    · subst h; exact ⟨b, rfl, he⟩
    · subst h; exact ⟨a, Sym2.eq_swap, he.symm⟩

/-- The degree of a vertex of `K.induce t` is the size of its neighbour set
intersected with `t`. -/
theorem degree_induce_coe_eq {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (t : Finset W) (v : ↥(t : Set W)) :
    (K.induce (t : Set W)).degree v = (K.neighborFinset (v : W) ∩ t).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij
    (s := (K.induce (t : Set W)).neighborFinset v) (t := K.neighborFinset (v : W) ∩ t)
    (fun w _ => (w : W)) ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨SimpleGraph.induce_adj.mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hw), w.property⟩
  · intro w₁ _ w₂ _ heq
    exact Subtype.ext heq
  · intro w hw
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
    let w' : ↥(t : Set W) := ⟨w, hw.2⟩
    refine ⟨w', ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
    exact hw.1

/-- Splitting the edges inside `t` by whether they contain `v`: the edges not
containing `v` are the edges inside `t.erase v`, and the edges containing `v`
are in bijection with the neighbours of `v` in `t`. -/
theorem card_filter_edgeFinset_subset_erase {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (t : Finset W) {v : W} (hv : v ∈ t) :
    ({e ∈ K.edgeFinset | e.toFinset ⊆ t} : Finset (Sym2 W)).card
      = ({e ∈ K.edgeFinset | e.toFinset ⊆ t.erase v} : Finset (Sym2 W)).card
        + (K.neighborFinset v ∩ t).card := by
  classical
  have hbij : (K.neighborFinset v ∩ t).card
      = ({e ∈ K.edgeFinset | e.toFinset ⊆ t ∧ v ∈ e} : Finset (Sym2 W)).card := by
    refine Finset.card_bij (s := K.neighborFinset v ∩ t)
      (t := ({e ∈ K.edgeFinset | e.toFinset ⊆ t ∧ v ∈ e} : Finset (Sym2 W)))
      (fun u _ => s(v, u)) ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu
      obtain ⟨hvu, hus⟩ := hu
      rw [Finset.mem_filter]
      refine ⟨?_, ?_, ?_⟩
      · exact (SimpleGraph.mem_edgeFinset).mpr ((SimpleGraph.mem_edgeSet K).mpr hvu)
      · rw [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hv, hus⟩
      · rw [Sym2.mem_iff]; exact Or.inl rfl
    · intro u1 _ u2 _ heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, h⟩ | ⟨h, h'⟩
      · exact h
      · exact h'.trans h
    · intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heedge, hesub, hve⟩ := he
      obtain ⟨u, heq, hvu⟩ :=
        exists_eq_pair_of_mem_edgeSet K v e ((SimpleGraph.mem_edgeFinset).mp heedge) hve
      refine ⟨u, ?_, ?_⟩
      · rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        refine ⟨hvu, ?_⟩
        have hu : u ∈ e.toFinset := by
          rw [heq, Sym2.toFinset_mk_eq]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self u)
        exact hesub hu
      · exact heq.symm
  have hsplit : ({e ∈ K.edgeFinset | e.toFinset ⊆ t} : Finset (Sym2 W))
      = ({e ∈ K.edgeFinset | e.toFinset ⊆ t ∧ v ∈ e} : Finset (Sym2 W))
        ∪ ({e ∈ K.edgeFinset | e.toFinset ⊆ t.erase v} : Finset (Sym2 W)) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨he, hsub⟩
      by_cases hve : v ∈ x
      · exact Or.inl ⟨he, hsub, hve⟩
      · refine Or.inr ⟨he, ?_⟩
        rw [Finset.subset_erase]
        exact ⟨hsub, fun hvmem => hve (Sym2.mem_toFinset.mp hvmem)⟩
    · rintro (⟨he, hsub, _⟩ | ⟨he, hsub⟩)
      · exact ⟨he, hsub⟩
      · rw [Finset.subset_erase] at hsub
        exact ⟨he, hsub.1⟩
  have hdisj : Disjoint ({e ∈ K.edgeFinset | e.toFinset ⊆ t ∧ v ∈ e} : Finset (Sym2 W))
      ({e ∈ K.edgeFinset | e.toFinset ⊆ t.erase v} : Finset (Sym2 W)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_filter] at hx1 hx2
    exact Finset.notMem_erase v t (hx2.2 (Sym2.mem_toFinset.mpr hx1.2.2))
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hbij]
  omega

/-- **Finite `2`-degenerate edge bound.** A finite simple graph on `n ≥ 2`
vertices, every nonempty induced subgraph of which has a vertex of degree at most
two, has at most `2n - 3` edges. -/
theorem card_edgeFinset_induce_le_two_mul_card_sub_three {W : Type u} [Fintype W]
    [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (hhered : ∀ (t : Finset W), t.Nonempty →
      ∃ v : ↥(t : Set W), (K.induce (t : Set W)).degree v ≤ 2)
    (t : Finset W) (hcard : 2 ≤ t.card) :
    (K.induce (t : Set W)).edgeFinset.card ≤ 2 * t.card - 3 := by
  classical
  suffices H : ∀ n, ∀ t : Finset W, t.card = n → 2 ≤ t.card →
      (K.induce (t : Set W)).edgeFinset.card ≤ 2 * t.card - 3 from H t.card t rfl hcard
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht hcard2
    rcases eq_or_lt_of_le hcard2 with h2 | h3
    · have hc : t.card = 2 := h2.symm
      calc (K.induce (t : Set W)).edgeFinset.card
          ≤ (Fintype.card ↥(t : Set W)).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
        _ = 1 := by rw [← Set.toFinset_card, Finset.toFinset_coe, hc]; norm_num
        _ = 2 * t.card - 3 := by rw [hc]
    · have htne : t.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hvdeg⟩ := hhered t htne
      have hvmem : (v : W) ∈ t := v.property
      have ht'card : (t.erase (v : W)).card = t.card - 1 := Finset.card_erase_of_mem hvmem
      have ht'ge : 2 ≤ (t.erase (v : W)).card := by rw [ht'card]; omega
      have ht'lt : (t.erase (v : W)).card < n := by rw [ht'card, ht]; omega
      have iht' := ih (t.erase (v : W)).card ht'lt (t.erase (v : W)) rfl ht'ge
      have hsplit : (K.induce (t : Set W)).edgeFinset.card
          = (K.induce (t.erase (v : W) : Set W)).edgeFinset.card
            + (K.induce (t : Set W)).degree v := by
        rw [← card_filter_edgeFinset_toFinset_subset (G := K) (s := t),
          ← card_filter_edgeFinset_toFinset_subset (G := K) (s := t.erase (v : W)),
          degree_induce_coe_eq K t v]
        exact card_filter_edgeFinset_subset_erase K t hvmem
      calc (K.induce (t : Set W)).edgeFinset.card
          = (K.induce (t.erase (v : W) : Set W)).edgeFinset.card
            + (K.induce (t : Set W)).degree v := hsplit
        _ ≤ (2 * (t.erase (v : W)).card - 3) + 2 := add_le_add iht' hvdeg
        _ ≤ 2 * t.card - 3 := by rw [ht'card]; omega

/-- **Lemma 3.5, edge-count part.** For `h ≥ 2`, `|L₂| = |E(M)| ≤ 2h - 3`,
where `M = doublingGraph G` is the source's auxiliary graph on `H`. The
`L₂ ↔ E(M)` cardinality is `card_degreeThreeTwoHigh_eq_card_edgeFinset`; the
hereditary low-degree property is `exists_degree_le_two_induce_doublingGraph`. -/
theorem card_degreeThreeTwoHigh_le_two_mul_card_sub_three {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    (h2 : 2 ≤ (degreeGeFourFinset G).card) :
    (degreeThreeTwoHigh G).card ≤ 2 * (degreeGeFourFinset G).card - 3 := by
  classical
  have hhered : ∀ (t : Finset ↥(degreeGeFourFinset G)), t.Nonempty →
      ∃ v : ↥(t : Set ↥(degreeGeFourFinset G)),
        ((doublingGraph G).induce (t : Set ↥(degreeGeFourFinset G))).degree v ≤ 2 := by
    intro t htne
    have hne : Nonempty ↥(t : Set ↥(degreeGeFourFinset G)) := by
      obtain ⟨x, hx⟩ := htne
      exact ⟨⟨x, by simpa using hx⟩⟩
    exact exists_degree_le_two_induce_doublingGraph hmin (t : Set ↥(degreeGeFourFinset G)) hne
  have hbound := card_edgeFinset_induce_le_two_mul_card_sub_three
    (K := doublingGraph G) hhered (Finset.univ : Finset ↥(degreeGeFourFinset G))
    (by simp only [Finset.card_univ, Fintype.card_coe]; exact h2)
  rw [← card_filter_edgeFinset_toFinset_subset (G := doublingGraph G)
    (s := (Finset.univ : Finset ↥(degreeGeFourFinset G)))] at hbound
  rw [card_degreeThreeTwoHigh_eq_card_edgeFinset hmin.not_hasPowerOfTwoCycle]
  simpa only [Finset.subset_univ, Finset.filter_true, Finset.card_univ,
    Fintype.card_coe] using hbound

/-- **Proposition 3.4, equation (3.1), and Lemma 3.5 chain.** For `h ≥ 2`, `ℓ ≥ 2h + 3`. -/
theorem two_mul_card_degreeGeFourFinset_add_three_le_card_degreeThreeFinset
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) (h2 : 2 ≤ (degreeGeFourFinset G).card) :
    2 * (degreeGeFourFinset G).card + 3 ≤ (degreeThreeFinset G).card := by
  have hcount := four_mul_card_degreeGeFourFinset_le hmin
  have hL2 := card_degreeThreeTwoHigh_le_two_mul_card_sub_three hmin h2
  have hpart := card_degreeThreeOneHigh_add_card_degreeThreeTwoHigh_le G
  omega

/-! ### 4. The partition of the vertex set and the small cases

Every vertex of a minimal counterexample has degree at least three, so it lies in
`L` or in `H`; the two classes are disjoint and union to `V`. -/

/-- `L ∪ H = V` in a minimal counterexample: every vertex has degree at least
three, hence degree exactly three or at least four. -/
theorem degreeThreeFinset_union_degreeGeFourFinset {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    degreeThreeFinset G ∪ degreeGeFourFinset G = Finset.univ := by
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rcases eq_or_lt_of_le (hmin.degree_ge_three v) with h | h
  · left
    rw [mem_degreeThreeFinset]
    exact h.symm
  · right
    rw [mem_degreeGeFourFinset]
    simp only [degreeGeFour]
    omega

/-- `L` and `H` are disjoint. -/
theorem disjoint_degreeThreeFinset_degreeGeFourFinset {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] :
    Disjoint (degreeThreeFinset G) (degreeGeFourFinset G) := by
  rw [Finset.disjoint_left]
  intro v hv3 hv4
  rw [mem_degreeThreeFinset] at hv3
  rw [mem_degreeGeFourFinset] at hv4
  simp only [degreeThree] at hv3
  simp only [degreeGeFour] at hv4
  omega

/-- `ℓ + h = n` in a minimal counterexample. -/
theorem card_degreeThreeFinset_add_card_degreeGeFourFinset {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    (degreeThreeFinset G).card + (degreeGeFourFinset G).card = Fintype.card V := by
  rw [← Finset.card_univ, ← degreeThreeFinset_union_degreeGeFourFinset hmin,
    Finset.card_union_of_disjoint disjoint_degreeThreeFinset_degreeGeFourFinset]

/-- A finite simple graph on exactly four vertices, all of whose degrees are at
least two, contains a `4`-cycle. This is the source's `n = 5` / `C₄`
obstruction, isolated as a reusable graph-theoretic statement. -/
theorem exists_walk_isCycle_length_four_of_card_four {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (hcard : Fintype.card W = 4)
    (hdeg : ∀ v : W, 2 ≤ K.degree v) :
    ∃ v : W, ∃ c : K.Walk v v, c.IsCycle ∧ c.length = 4 := by
  classical
  have hcompl : ∀ v : W, Kᶜ.degree v ≤ 1 := by
    intro v
    rw [SimpleGraph.degree_compl, hcard]
    have := hdeg v
    omega
  have hhelper : ∀ {x y z : W}, Kᶜ.Adj x z → y ≠ z → y ≠ x → K.Adj x y := by
    intro x y z hxz hyz hyx
    by_contra hxy
    have hxy' : Kᶜ.Adj x y := by rw [SimpleGraph.compl_adj]; exact ⟨hyx.symm, hxy⟩
    have hsub : ({y, z} : Finset W) ⊆ Kᶜ.neighborFinset x := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact hxy'
      · exact hxz
    have h2 : 2 ≤ (Kᶜ.neighborFinset x).card := by
      have := Finset.card_le_card hsub
      rwa [(Finset.card_eq_two).mpr ⟨y, z, hyz, rfl⟩] at this
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
    have := hcompl x
    omega
  obtain ⟨a⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hnb : 2 ≤ (K.neighborFinset a).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg a
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp (by omega : 1 < (K.neighborFinset a).card)
  rw [SimpleGraph.mem_neighborFinset] at hb hd
  have hab : K.Adj a b := hb
  have had : K.Adj a d := hd
  have hc : ∃ c : W, c ≠ a ∧ c ≠ b ∧ c ≠ d := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset W) ⊆ ({a, b, d} : Finset W) := by
      intro w _
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      by_cases hwa : w = a
      · exact Or.inl hwa
      · right
        by_cases hwb : w = b
        · exact Or.inl hwb
        · exact Or.inr (h w hwa hwb)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at hle
    have h3 : ({a, b, d} : Finset W).card ≤ 3 := by
      have h1 : ({a, b, d} : Finset W).card ≤ ({b, d} : Finset W).card + 1 :=
        Finset.card_insert_le a _
      have h2 : ({b, d} : Finset W).card ≤ ({d} : Finset W).card + 1 :=
        Finset.card_insert_le b _
      rw [Finset.card_singleton] at h2
      omega
    omega
  obtain ⟨c, hca, hcb, hcd⟩ := hc
  have mk4 : ∀ {x1 x2 x3 x4 : W}, K.Adj x1 x2 → K.Adj x2 x3 → K.Adj x3 x4 → K.Adj x4 x1 →
      x1 ≠ x2 → x1 ≠ x3 → x1 ≠ x4 → x2 ≠ x3 → x2 ≠ x4 → x3 ≠ x4 →
      ∃ v : W, ∃ c : K.Walk v v, c.IsCycle ∧ c.length = 4 := by
    intro x1 x2 x3 x4 h12 h23 h34 h41 h12' h13 h14 h23' h24 h34'
    refine ⟨x1, Walk.cons h12 (Walk.cons h23 (Walk.cons h34 (Walk.cons h41 Walk.nil))), ?_, ?_⟩
    · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      refine ⟨?_, by simp [Walk.length_cons]⟩
      rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ Walk.not_nil_cons]
      simp only [Walk.support_cons, Walk.support_nil]
      simp [h23', h24, h12'.symm, h34', h13.symm, h14.symm]
    · simp [Walk.length_cons]
  by_cases hbc : K.Adj b c
  · by_cases hdc : K.Adj d c
    · exact mk4 hab hbc hdc.symm had.symm hab.ne hca.symm had.ne hbc.ne hbd hdc.ne.symm
    · have hdc' : Kᶜ.Adj d c := by rw [SimpleGraph.compl_adj]; exact ⟨hcd.symm, hdc⟩
      have hdb : K.Adj d b := hhelper hdc' hbc.ne hbd
      have hca' : K.Adj c a := hhelper hdc'.symm had.ne hca.symm
      exact mk4 had hdb hbc hca' had.ne hab.ne hca.symm hbd.symm hcd.symm hbc.ne
  · have hbc' : Kᶜ.Adj b c := by rw [SimpleGraph.compl_adj]; exact ⟨hcb.symm, hbc⟩
    have hbd' : K.Adj b d := hhelper hbc' hcd.symm hbd.symm
    have hcd' : K.Adj c d := hhelper hbc'.symm hbd.symm hcd.symm
    have hca'' : K.Adj c a := hhelper hbc'.symm hab.ne hca.symm
    exact mk4 hab hbd' hcd'.symm hca'' hab.ne had.ne hca.symm hbd hcb.symm hcd.symm

/-- **Theorem 3.7, the `h = 1` case.** If `H` is a single vertex then `n ≥ 6`:
the unique high-degree vertex has at least four neighbours, so `n ≥ 5`, and
`n = 5` would force the four `L`-vertices to induce a `2`-regular graph on four
vertices, i.e. a `C₄ = 2²`-cycle, contradicting that `G` is a counterexample. -/
theorem card_verts_ge_six_of_card_degreeGeFourFinset_eq_one {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    (h1 : (degreeGeFourFinset G).card = 1) :
    6 ≤ Fintype.card V := by
  classical
  obtain ⟨x, hxH⟩ := Finset.card_eq_one.mp h1
  have hxdeg : 4 ≤ G.degree x := by
    have hxmem : x ∈ degreeGeFourFinset G := by rw [hxH]; exact Finset.mem_singleton_self x
    simpa using (mem_degreeGeFourFinset.mp hxmem)
  have hn5 : 5 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts x
    omega
  rcases eq_or_lt_of_le hn5 with h5 | h6
  · exfalso
    -- `x` is adjacent to every other vertex, because it has degree at least four.
    have hnb : G.neighborFinset x = Finset.univ.erase x := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        rw [SimpleGraph.mem_neighborFinset] at hv
        rw [Finset.mem_erase]
        exact ⟨hv.ne.symm, Finset.mem_univ v⟩
      · have hce : (Finset.univ.erase x).card = 4 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
          omega
        rw [hce, SimpleGraph.card_neighborFinset_eq_degree]
        exact hxdeg
    -- every other vertex is a degree-three vertex
    have hL : ∀ v : V, v ≠ x → degreeThree G v := by
      intro v hvx
      have hun := degreeThreeFinset_union_degreeGeFourFinset hmin
      have hvun : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [← hun, Finset.mem_union, hxH, Finset.mem_singleton] at hvun
      rcases hvun with h | h
      · exact mem_degreeThreeFinset.mp h
      · exact absurd h hvx
    -- each vertex of the complement of `{x}` has degree two in the induced graph
    have hdeg2 : ∀ w : ↥({x}ᶜ : Set V), (G.induce {x}ᶜ).degree w = 2 := by
      intro w
      have hwx : (w : V) ≠ x := by
        have hwmem := w.property
        change (w : V) ∉ ({x} : Set V) at hwmem
        simpa only [Set.mem_singleton_iff] using hwmem
      rw [degree_induce_compl_singleton G x w]
      have hxw : G.Adj (w : V) x := by
        have hw' : (w : V) ∈ G.neighborFinset x := by
          rw [hnb, Finset.mem_erase]
          exact ⟨hwx, Finset.mem_univ (w : V)⟩
        exact ((SimpleGraph.mem_neighborFinset G x w).mp hw').symm
      rw [if_pos hxw]
      have h3 : G.degree (w : V) = 3 := hL (w : V) hwx
      omega
    have hcard4 : Fintype.card ↥({x}ᶜ : Set V) = 4 := by
      rw [card_compl_singleton x, ← h5]
    obtain ⟨w, c, hc⟩ := exists_walk_isCycle_length_four_of_card_four (G.induce {x}ᶜ) hcard4
      (fun w => by rw [hdeg2 w])
    exact hmin.not_hasPowerOfTwoCycle
      (hasPowerOfTwoCycle_induce G {x}ᶜ ⟨2, by norm_num, w, c, hc.1, by rw [hc.2]; norm_num⟩)
  · omega

/-- **Theorem 3.7, the `h` bound.** `3h + 3 ≤ n`: the `h = 0` and `h = 1` cases
are direct (`n ≥ 4` and `n ≥ 6`), and for `h ≥ 2` it follows from `ℓ ≥ 2h + 3`
and `n = ℓ + h`. -/
theorem three_mul_card_degreeGeFourFinset_add_three_le_card_verts {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    3 * (degreeGeFourFinset G).card + 3 ≤ Fintype.card V := by
  by_cases h0 : (degreeGeFourFinset G).card = 0
  · rw [h0]
    have := hmin.card_verts_ge_four
    omega
  · by_cases h1 : (degreeGeFourFinset G).card = 1
    · rw [h1]
      exact card_verts_ge_six_of_card_degreeGeFourFinset_eq_one hmin h1
    · have h2 : 2 ≤ (degreeGeFourFinset G).card := by omega
      have hlow := two_mul_card_degreeGeFourFinset_add_three_le_card_degreeThreeFinset hmin h2
      have hpart := card_degreeThreeFinset_add_card_degreeGeFourFinset hmin
      omega

/-! ### 5. Corollary 3.6

`L = L₂` is impossible. In explicit witness form: some degree-three vertex has at
most one high-degree neighbour. -/

/-- **Corollary 3.6.** In a minimal counterexample there is a degree-three vertex
with at most one high-degree neighbour; equivalently `L ≠ L₂`. -/
theorem exists_degreeThree_card_highDegreeNeighbors_le_one {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G) :
    ∃ v : V, degreeThree G v ∧ (highDegreeNeighbors G v).card ≤ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hall : ∀ v : V, degreeThree G v → (highDegreeNeighbors G v).card = 2 := by
    intro v hv
    have hlt := hcon v hv
    have hle := card_highDegreeNeighbors_le_two hmin hv
    omega
  obtain ⟨v0⟩ := hmin.isCounterexample.nonempty
  obtain ⟨w, _, hw3⟩ := exists_adjacent_degreeThree hmin v0
  have hwc : (highDegreeNeighbors G w).card = 2 := hall w hw3
  have hsub : highDegreeNeighbors G w ⊆ degreeGeFourFinset G := by
    intro u hu
    rw [mem_degreeGeFourFinset]
    exact (mem_highDegreeNeighbors.mp hu).1
  have hh2 : 2 ≤ (degreeGeFourFinset G).card := by
    have := Finset.card_le_card hsub
    omega
  have hLeq : degreeThreeFinset G = degreeThreeTwoHigh G := by
    apply Finset.Subset.antisymm
    · intro v hv
      rw [mem_degreeThreeTwoHigh]
      exact ⟨mem_degreeThreeFinset.mp hv, hall v (mem_degreeThreeFinset.mp hv)⟩
    · exact degreeThreeTwoHigh_subset_degreeThreeFinset G
  have hL2 := card_degreeThreeTwoHigh_le_two_mul_card_sub_three hmin hh2
  have hlow := two_mul_card_degreeGeFourFinset_add_three_le_card_degreeThreeFinset hmin hh2
  rw [hLeq] at hlow
  omega

/-! ### 6. Theorem 3.7 -/

/-- **Theorem 3.7** (Ducoffe–Dumitru), division-free form. A minimal
counterexample on `n` vertices satisfies `2n + 3 ≤ 3ℓ`, where `ℓ = |L|`; this is
exactly the rational inequality `ℓ ≥ 2n/3 + 1`. -/
theorem density {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) :
    2 * Fintype.card V + 3 ≤ 3 * (degreeThreeFinset G).card := by
  have h3 := three_mul_card_degreeGeFourFinset_add_three_le_card_verts hmin
  have hpart := card_degreeThreeFinset_add_card_degreeGeFourFinset hmin
  omega

/-- **Theorem 3.7**, `Nat`-division corollary: `ℓ ≥ 2n/3 + 1` with `Nat` floor
division. -/
theorem density_div {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) :
    2 * Fintype.card V / 3 + 1 ≤ (degreeThreeFinset G).card := by
  have h := density hmin
  have hpos : 0 < 3 := by norm_num
  have h2 : 2 * Fintype.card V / 3 ≤ (degreeThreeFinset G).card - 1 :=
    (Nat.div_le_iff_le_mul_add_pred hpos).mpr (by omega)
  omega

/-- **Theorem 3.7**, rational form: `ℓ ≥ 2n/3 + 1` as an inequality in `ℚ`. This
records that the division-free statement `2n + 3 ≤ 3ℓ` is exactly the source's
strict density bound. -/
theorem density_rat {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) :
    (2 * (Fintype.card V : ℚ)) / 3 + 1 ≤ ((degreeThreeFinset G).card : ℚ) := by
  have h := density hmin
  have hcast : (2 * (Fintype.card V : ℚ)) + 3 ≤ 3 * ((degreeThreeFinset G).card : ℚ) := by
    exact_mod_cast h
  linarith

end Erdos64