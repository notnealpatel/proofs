/-
# Upper k-star-forming sets: the bipartite equality conjecture is false

## Source

Rafik Sahbi, "Upper $k$-Star-Forming Sets, $k$-Independence, and Upper
Domination", arXiv:2610.03785 (listing v4), retrieved 2026-10-21.

Section 1 (Definition and Lemma 2.1, the local criterion):

> A set $S\subseteq V(G)$ is $k$-star-forming if, for every
> $v\in V(G)\setminus S$, the graph $G[S\cup\{v\}]$ contains a copy of
> $K_{1,k}$ containing $v$. It is minimal if no proper subset of $S$ is
> $k$-star-forming. The maximum cardinality of a minimal $k$-star-forming set
> is denoted by $SF_k(G)$.

$\beta_k(G)$ is the maximum cardinality of a vertex set inducing maximum
degree less than $k$.

Section 4, Conjecture 4.1 (Bipartite equality), verbatim:

> For every bipartite graph $G$ and every integer $k\ge1$,
> $\beta_k(G)=SF_k(G)$.

Conjecture 4.2 (Bipartite dissociation equality) is its case $k = 2$, and
Section 6, Conjecture 6.2 (Triangle-free case for $k=2$) asserts
$\beta_2(G)=SF_2(G)$ for every triangle-free graph.

## Status

The paper states all three as open conjectures (it proves only
$\beta_k\le SF_k$ (Chellali--Favaron), the complete bipartite case, and the
chain-graph case $k=2$). They are false. This module proves:

* `conj_4_1_false`, `conj_4_2_false`, `conj_6_2_false`: the negations, via
  the connected bipartite graph `G₁` on 10 vertices (graph6 `I?BDbbgu?`) with
  $\beta_2(G_1)=5<6\le SF_2(G_1)$, witnessed by the minimal
  2-star-forming set $\{2,3,4,5,6,7\}$;
* `bipartite_k4_counterexample`: a second bipartite graph `G₂` (graph6
  `I?AFBrw}?`) with $\beta_4(G_2)=7<8\le SF_4(G_2)$.

The counterexamples were found by exhaustive search over connected bipartite
graphs on at most 10 vertices (Sage/nauty, 2026-10-21); the search is
evidence only, the Lean proofs below are self-contained. The upper bounds on
$\beta_k$ are checked by kernel reduction (`decide +kernel`, no
`native_decide`) over bitmasks, with a proved bridge to `Finset`.
-/
import Mathlib

set_option autoImplicit false

namespace UpperStarFormingSetsRefutation

open Finset

section General

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `degIn G S v` is $d_S(v)=|N(v)\cap S|$, the number of neighbours of `v` in `S`. -/
def degIn (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

/-- A set `I` is `k`-independent when it induces maximum degree less than `k`:
every vertex of `I` has fewer than `k` neighbours in `I`. -/
def IsKIndependent (k : ℕ) (I : Finset V) : Prop := ∀ v ∈ I, degIn G I v < k

/-- The literal clause of the definition: the graph $G[S\cup\{v\}]$ contains a
copy of $K_{1,k}$ containing `v`. The copy has centre `c` and a `k`-element leaf
set `L`, all inside `S ∪ {v}`, with `c` adjacent to every leaf. -/
def HasStarThrough [DecidableEq V] (k : ℕ) (S : Finset V) (v : V) : Prop :=
  ∃ c : V, ∃ L : Finset V, c ∉ L ∧ L.card = k ∧ insert c L ⊆ insert v S ∧
    (∀ l ∈ L, G.Adj c l) ∧ v ∈ insert c L

/-- `S` is `k`-star-forming (paper, Section 2): for every vertex `v ∉ S`, the
graph $G[S\cup\{v\}]$ contains a copy of $K_{1,k}$ containing `v`. -/
def IsKStarForming [DecidableEq V] (k : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → HasStarThrough G k S v

/-- The local form of Lemma 2.1: every `v ∉ S` has $d_S(v)\ge k$, or has a
neighbour `u ∈ S` with $d_S(u)\ge k-1$ (written `k ≤ d_S(u) + 1`). -/
def LocalCriterion (k : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → k ≤ degIn G S v ∨ ∃ u ∈ S, G.Adj v u ∧ k ≤ degIn G S u + 1

instance [DecidableEq V] [Fintype V] (k : ℕ) (S : Finset V) :
    Decidable (LocalCriterion G k S) := by
  unfold LocalCriterion; infer_instance

instance (k : ℕ) (I : Finset V) : Decidable (IsKIndependent G k I) := by
  unfold IsKIndependent; infer_instance

/-- Lemma 2.1 of the paper, pointwise: for `v ∉ S`, $G[S\cup\{v\}]$ contains a
$K_{1,k}$ through `v` iff $d_S(v)\ge k$ or some neighbour `u ∈ S` of `v` has
$d_S(u)\ge k-1$. -/
theorem hasStarThrough_iff [DecidableEq V] {k : ℕ} {S : Finset V} {v : V} (hv : v ∉ S) :
    HasStarThrough G k S v ↔
      k ≤ degIn G S v ∨ ∃ u ∈ S, G.Adj v u ∧ k ≤ degIn G S u + 1 := by
  constructor
  · rintro ⟨c, L, hcL, hLk, hsub, hadj, hvin⟩
    by_cases hcv : c = v
    · subst hcv
      left
      have hLS : L ⊆ S.filter (G.Adj c) := by
        intro l hl
        have hl' : l ∈ insert c S := hsub (mem_insert_of_mem hl)
        rcases mem_insert.1 hl' with rfl | hlS
        · exact absurd hl hcL
        · exact mem_filter.2 ⟨hlS, hadj l hl⟩
      simpa [degIn, hLk] using card_le_card hLS
    · right
      have hvL : v ∈ L := by
        rcases mem_insert.1 hvin with h | h
        · exact absurd h.symm hcv
        · exact h
      have hcS : c ∈ S := by
        rcases mem_insert.1 (hsub (mem_insert_self c L)) with h | h
        · exact absurd h hcv
        · exact h
      refine ⟨c, hcS, (hadj v hvL).symm, ?_⟩
      have hLS : L.erase v ⊆ S.filter (G.Adj c) := by
        intro l hl
        obtain ⟨hlv, hl⟩ := mem_erase.1 hl
        rcases mem_insert.1 (hsub (mem_insert_of_mem hl)) with h | h
        · exact absurd h hlv
        · exact mem_filter.2 ⟨h, hadj l hl⟩
      have hcard := card_le_card hLS
      rw [card_erase_of_mem hvL, hLk] at hcard
      unfold degIn
      omega
  · rintro (hdeg | ⟨u, huS, hvu, hdeg⟩)
    · obtain ⟨L, hLsub, hLk⟩ := exists_subset_card_eq hdeg
      refine ⟨v, L, fun hvL => hv (mem_filter.1 (hLsub hvL)).1, hLk, ?_, ?_,
        mem_insert_self v L⟩
      · exact insert_subset_insert v (hLsub.trans (filter_subset _ _))
      · exact fun l hl => (mem_filter.1 (hLsub hl)).2
    · by_cases hk : k ≤ degIn G S v
      · -- reduce to the first case
        obtain ⟨L, hLsub, hLk⟩ := exists_subset_card_eq hk
        refine ⟨v, L, fun hvL => hv (mem_filter.1 (hLsub hvL)).1, hLk, ?_, ?_,
          mem_insert_self v L⟩
        · exact insert_subset_insert v (hLsub.trans (filter_subset _ _))
        · exact fun l hl => (mem_filter.1 (hLsub hl)).2
      · have hk1 : k - 1 ≤ degIn G S u := by omega
        obtain ⟨L, hLsub, hLk⟩ := exists_subset_card_eq hk1
        have hvL : v ∉ L := fun h => hv (mem_filter.1 (hLsub h)).1
        have huL : u ∉ L := fun h => G.loopless.irrefl u (mem_filter.1 (hLsub h)).2
        refine ⟨u, insert v L, ?_, ?_, ?_, ?_, ?_⟩
        · rw [mem_insert, not_or]
          exact ⟨fun h => hv (h ▸ huS), huL⟩
        · rw [card_insert_of_notMem hvL, hLk]
          omega
        · intro x hx
          rcases mem_insert.1 hx with rfl | hx
          · exact mem_insert_of_mem huS
          rcases mem_insert.1 hx with rfl | hx
          · exact mem_insert_self x S
          · exact mem_insert_of_mem (mem_filter.1 (hLsub hx)).1
        · intro l hl
          rcases mem_insert.1 hl with rfl | hl
          · exact hvu.symm
          · exact (mem_filter.1 (hLsub hl)).2
        · exact mem_insert_of_mem (mem_insert_self v L)

/-- Lemma 2.1 of the paper: `S` is `k`-star-forming iff it satisfies the local
criterion. -/
theorem isKStarForming_iff_localCriterion [DecidableEq V] {k : ℕ} {S : Finset V} :
    IsKStarForming G k S ↔ LocalCriterion G k S :=
  forall_congr' fun _ => imp_congr_right fun hv => hasStarThrough_iff G hv

/-- `d_S(v)` is monotone in `S`. -/
theorem degIn_mono {S T : Finset V} (hST : S ⊆ T) (v : V) : degIn G S v ≤ degIn G T v :=
  card_le_card (filter_subset_filter _ hST)

/-- Being `k`-star-forming is upward closed. -/
theorem IsKStarForming.mono [DecidableEq V] {k : ℕ} {S T : Finset V}
    (hS : IsKStarForming G k S) (hST : S ⊆ T) : IsKStarForming G k T := by
  rw [isKStarForming_iff_localCriterion] at hS ⊢
  intro v hvT
  rcases hS v (fun h => hvT (hST h)) with h | ⟨u, huS, hvu, hu⟩
  · exact Or.inl (h.trans (degIn_mono G hST v))
  · exact Or.inr ⟨u, hST huS, hvu, hu.trans (Nat.add_le_add_right (degIn_mono G hST u) 1)⟩

/-- Since the property is upward closed, a `k`-star-forming set none of whose
one-vertex deletions is `k`-star-forming is minimal (no proper subset is
`k`-star-forming). -/
theorem minimal_of_forall_erase [DecidableEq V] {k : ℕ} {S : Finset V}
    (hS : IsKStarForming G k S) (herase : ∀ s ∈ S, ¬ IsKStarForming G k (S.erase s)) :
    Minimal (IsKStarForming G k) S := by
  refine ⟨hS, fun T hT hTS => ?_⟩
  intro s hs
  by_contra hsT
  exact herase s hs (hT.mono G fun x hx => mem_erase.2 ⟨fun h => hsT (h ▸ hx), hTS hx⟩)

/-- $\beta_k(G)$: the maximum cardinality of a `k`-independent set. -/
noncomputable def betaK [Fintype V] (k : ℕ) : ℕ :=
  open Classical in ((univ : Finset (Finset V)).filter (IsKIndependent G k)).sup card

/-- $SF_k(G)$: the maximum cardinality of a minimal `k`-star-forming set. -/
noncomputable def sfK [Fintype V] [DecidableEq V] (k : ℕ) : ℕ :=
  open Classical in
    ((univ : Finset (Finset V)).filter (Minimal (IsKStarForming G k))).sup card

/-- Every `k`-independent set has at most $\beta_k(G)$ vertices. -/
theorem card_le_betaK [Fintype V] {k : ℕ} {I : Finset V} (hI : IsKIndependent G k I) :
    I.card ≤ betaK G k := by
  classical
  unfold betaK
  convert le_sup (f := card) (mem_filter.2 ⟨mem_univ I, hI⟩) using 2

/-- $\beta_k(G)\le b$ as soon as every `k`-independent set has at most `b` vertices. -/
theorem betaK_le [Fintype V] {k b : ℕ} (h : ∀ I : Finset V, IsKIndependent G k I → I.card ≤ b) :
    betaK G k ≤ b := by
  classical
  unfold betaK
  refine Finset.sup_le fun I hI => h I ?_
  convert (mem_filter.1 hI).2

omit [DecidableRel G.Adj] in
/-- Every minimal `k`-star-forming set has at most $SF_k(G)$ vertices. -/
theorem card_le_sfK [Fintype V] [DecidableEq V] {k : ℕ} {S : Finset V}
    (hS : Minimal (IsKStarForming G k) S) : S.card ≤ sfK G k := by
  classical
  unfold sfK
  convert le_sup (f := card) (mem_filter.2 ⟨mem_univ S, hS⟩) using 2

end General

section Mask

variable {n : ℕ}

/-- The bitmask $\sum_{i\in I}2^i$ encoding a set `I` of vertices of `Fin n`. -/
def mask (I : Finset (Fin n)) : ℕ := ∑ i ∈ I, 2 ^ (i : ℕ)

/-- Bit `j` of `mask I` is set iff `j < n` and the vertex `j` lies in `I`. -/
theorem testBit_mask_iff (I : Finset (Fin n)) (j : ℕ) :
    (mask I).testBit j = true ↔ ∃ h : j < n, (⟨j, h⟩ : Fin n) ∈ I := by
  have hsum : mask I = ∑ i ∈ I.map Fin.valEmbedding, 2 ^ i := by
    simp [mask, sum_map]
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, hsum, Finset.toFinset_bitIndices_sum_two_pow,
    mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.isLt, ha⟩
  · rintro ⟨h, hj⟩
    exact ⟨_, hj, rfl⟩

/-- Bit `j` of `mask I` is set iff `j ∈ I`. -/
theorem testBit_mask (I : Finset (Fin n)) (j : Fin n) :
    (mask I).testBit j = true ↔ j ∈ I := by
  rw [testBit_mask_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨j.isLt, h⟩⟩

/-- The bitmask of a subset of `Fin n` is below `2 ^ n`. -/
theorem mask_lt (I : Finset (Fin n)) : mask I < 2 ^ n := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  by_contra h
  obtain ⟨hlt, -⟩ := (testBit_mask_iff I i).1 (by simpa using h)
  omega

/-- The number of indices `u < n` at which `x` has a set bit. -/
def bitCount (n x : ℕ) : ℕ := (List.finRange n).countP fun u : Fin n => x.testBit (u : ℕ)

/-- The cardinality of a filter of `Fin n` is a `List.countP` over `List.finRange n`. -/
theorem card_filter_univ_eq_countP (p : Fin n → Prop) [DecidablePred p] :
    (univ.filter p).card = (List.finRange n).countP p := by
  change Multiset.card (Multiset.filter p ↑(List.finRange n)) = _
  rw [Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter]

/-- The cardinality of `I` is the number of set bits of its mask. -/
theorem card_eq_bitCount (I : Finset (Fin n)) : I.card = bitCount n (mask I) := by
  have hI : I = univ.filter fun u : Fin n => (mask I).testBit u = true := by
    ext u
    simp [testBit_mask]
  conv_lhs => rw [hI]
  rw [card_filter_univ_eq_countP]
  simp only [bitCount, Bool.decide_eq_true]

/-- Boolean test that the set encoded by `m` is `k`-independent in the graph on
`Fin n` whose adjacency rows are the bitmasks `rows`. -/
def indepMask (n : ℕ) (rows : Fin n → ℕ) (k m : ℕ) : Bool :=
  (List.finRange n).all fun v => !(m.testBit v) || decide (bitCount n (m &&& rows v) < k)

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (rows : Fin n → ℕ)

/-- With adjacency rows `rows`, $d_I(v)$ is the bit count of `mask I &&& rows v`. -/
theorem degIn_eq_bitCount (hrows : ∀ i j : Fin n, G.Adj i j ↔ (rows i).testBit j = true)
    (I : Finset (Fin n)) (v : Fin n) :
    degIn G I v = bitCount n (mask I &&& rows v) := by
  have hfilter : I.filter (G.Adj v) =
      univ.filter fun u : Fin n => (mask I &&& rows v).testBit u = true := by
    ext u
    simp [Nat.testBit_and, testBit_mask, hrows]
  unfold degIn
  rw [hfilter, card_filter_univ_eq_countP]
  simp only [bitCount, Bool.decide_eq_true]

/-- `k`-independence of `I` agrees with the Boolean bitmask test on `mask I`. -/
theorem isKIndependent_iff_indepMask
    (hrows : ∀ i j : Fin n, G.Adj i j ↔ (rows i).testBit j = true) (k : ℕ)
    (I : Finset (Fin n)) :
    IsKIndependent G k I ↔ indepMask n rows k (mask I) = true := by
  unfold IsKIndependent indepMask
  simp only [degIn_eq_bitCount G rows hrows, List.all_eq_true, List.mem_finRange,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, forall_const]
  refine ⟨fun h v => ?_, fun h v hv => ?_⟩
  · by_cases hv : v ∈ I
    · exact Or.inr (h v hv)
    · exact Or.inl (Bool.eq_false_iff.2 fun h => hv ((testBit_mask I v).1 h))
  · refine (h v).resolve_left ?_
    simp [(testBit_mask I v).2 hv]

/-- A bitmask enumeration bounding $\beta_k(G)$ from above. -/
theorem betaK_le_of_mask (hrows : ∀ i j : Fin n, G.Adj i j ↔ (rows i).testBit j = true)
    {k b : ℕ} (h : ∀ m < 2 ^ n, indepMask n rows k m = true → bitCount n m ≤ b) :
    betaK G k ≤ b :=
  betaK_le G fun I hI => (card_eq_bitCount I).trans_le
    (h _ (mask_lt I) ((isKIndependent_iff_indepMask G rows hrows k I).1 hI))

end Mask

section Example

/-- The 16 edges of the first counterexample `G₁` (graph6 `I?BDbbgu?`), with
parts `{0,…,4}` and `{5,…,9}`. -/
def edges₁ : List (ℕ × ℕ) :=
  [(0,5),(0,6),(0,8),(0,9),(1,5),(1,7),(1,8),(1,9),(2,6),(2,7),(2,8),(3,6),(3,7),(3,9),
    (4,8),(4,9)]

/-- The bipartite graph `G₁` on `Fin 10` with edge list `edges₁`. -/
def G₁ : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ edges₁

instance : DecidableRel G₁.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (((i : ℕ), (j : ℕ)) ∈ edges₁ ∨ ((j : ℕ), (i : ℕ)) ∈ edges₁)))

/-- Adjacency rows of `G₁` as bitmasks: bit `j` of `rows₁ i` is set iff `i ~ j`. -/
def rows₁ : Fin 10 → ℕ := ![864, 928, 448, 704, 768, 3, 13, 14, 23, 27]

/-- The bitmask rows `rows₁` describe exactly the adjacency of `G₁`. -/
theorem G₁_adj_iff : ∀ i j : Fin 10, G₁.Adj i j ↔ (rows₁ i).testBit j = true := by
  decide

set_option maxRecDepth 100000 in
/-- Kernel enumeration: every bitmask encoding a 2-independent set of `G₁` has at most
five set bits. -/
theorem G₁_mask_check : ∀ m < 2 ^ 10, indepMask 10 rows₁ 2 m = true → bitCount 10 m ≤ 5 := by
  decide +kernel

/-- Ground truth: the neighbourhoods of `G₁` are those listed in the source data,
e.g. $N(0)=\{5,6,8,9\}$ and $N(8)=\{0,1,2,4\}$. -/
example : univ.filter (G₁.Adj 0) = {5, 6, 8, 9} ∧ univ.filter (G₁.Adj 8) = {0, 1, 2, 4} := by
  decide

/-- Ground truth: `G₁` has 16 edges. -/
example : G₁.edgeFinset.card = 16 := by decide

/-- `G₁` is bipartite, with parts `{0,…,4}` and `{5,…,9}`. -/
theorem G₁_colorable : G₁.Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun v => if (v : ℕ) < 5 then (0 : Fin 2) else 1)
    (fun {v w} h => by revert v w; decide)⟩

/-- $\beta_2(G_1)=5$; the part `{0,…,4}` is a 2-independent set of size 5. -/
theorem betaK_G₁ : betaK G₁ 2 = 5 :=
  le_antisymm (betaK_le_of_mask G₁ rows₁ G₁_adj_iff G₁_mask_check)
    (card_le_betaK G₁ (I := {0, 1, 2, 3, 4}) (by decide))

/-- `{2,3,4,5,6,7}` is a minimal 2-star-forming set of `G₁`. -/
theorem minimal_S₁ : Minimal (IsKStarForming G₁ 2) ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) := by
  refine minimal_of_forall_erase G₁ ?_ ?_
  · rw [isKStarForming_iff_localCriterion]
    decide
  · simp only [isKStarForming_iff_localCriterion]
    decide

/-- $SF_2(G_1)\ge 6$. -/
theorem six_le_sfK_G₁ : 6 ≤ sfK G₁ 2 := card_le_sfK G₁ minimal_S₁

/-- The concrete counterexample: `G₁` is bipartite, `{2,3,4,5,6,7}` is a minimal
2-star-forming set, and every 2-independent set of `G₁` has at most 5 vertices.
Hence $\beta_2(G_1)=5<6\le SF_2(G_1)$. -/
theorem G₁_counterexample :
    G₁.Colorable 2 ∧ Minimal (IsKStarForming G₁ 2) ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) ∧
      (∀ I : Finset (Fin 10), IsKIndependent G₁ 2 I → I.card ≤ 5) ∧
      betaK G₁ 2 < sfK G₁ 2 :=
  ⟨G₁_colorable, minimal_S₁, fun _ hI => (card_le_betaK G₁ hI).trans betaK_G₁.le,
    betaK_G₁ ▸ six_le_sfK_G₁⟩

end Example

section ExampleK4

/-- The 18 edges of the second counterexample `G₂` (graph6 `I?AFBrw}?`), with parts
`{0,…,4}` and `{5,…,9}`. -/
def edges₂ : List (ℕ × ℕ) :=
  [(0,5),(0,6),(0,8),(0,9),(1,6),(1,7),(1,8),(1,9),(2,6),(2,7),(2,8),(2,9),(3,7),(3,8),(3,9),
    (4,7),(4,8),(4,9)]

/-- The bipartite graph `G₂` on `Fin 10` with edge list `edges₂`. -/
def G₂ : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ edges₂

instance : DecidableRel G₂.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (((i : ℕ), (j : ℕ)) ∈ edges₂ ∨ ((j : ℕ), (i : ℕ)) ∈ edges₂)))

/-- Adjacency rows of `G₂` as bitmasks: bit `j` of `rows₂ i` is set iff `i ~ j`. -/
def rows₂ : Fin 10 → ℕ := ![864, 960, 960, 896, 896, 1, 7, 30, 31, 31]

/-- The bitmask rows `rows₂` describe exactly the adjacency of `G₂`. -/
theorem G₂_adj_iff : ∀ i j : Fin 10, G₂.Adj i j ↔ (rows₂ i).testBit j = true := by
  decide

/-- Ground truth: `G₂` has 18 edges and $N(5)=\{0\}$. -/
example : G₂.edgeFinset.card = 18 ∧ univ.filter (G₂.Adj 5) = {0} := by decide

set_option maxRecDepth 100000 in
/-- Kernel enumeration: every bitmask encoding a 4-independent set of `G₂` has at most
seven set bits. -/
theorem G₂_mask_check : ∀ m < 2 ^ 10, indepMask 10 rows₂ 4 m = true → bitCount 10 m ≤ 7 := by
  decide +kernel

/-- `G₂` is bipartite, with parts `{0,…,4}` and `{5,…,9}`. -/
theorem G₂_colorable : G₂.Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun v => if (v : ℕ) < 5 then (0 : Fin 2) else 1)
    (fun {v w} h => by revert v w; decide)⟩

/-- $\beta_4(G_2)=7$; `{0,…,6}` is a 4-independent set of size 7. -/
theorem betaK_G₂ : betaK G₂ 4 = 7 :=
  le_antisymm (betaK_le_of_mask G₂ rows₂ G₂_adj_iff G₂_mask_check)
    (card_le_betaK G₂ (I := {0, 1, 2, 3, 4, 5, 6}) (by decide))

/-- `{0,1,2,3,4,5,8,9}` is a minimal 4-star-forming set of `G₂`. -/
theorem minimal_S₂ :
    Minimal (IsKStarForming G₂ 4) ({0, 1, 2, 3, 4, 5, 8, 9} : Finset (Fin 10)) := by
  refine minimal_of_forall_erase G₂ ?_ ?_
  · rw [isKStarForming_iff_localCriterion]
    decide
  · simp only [isKStarForming_iff_localCriterion]
    decide

/-- A second bipartite counterexample to Conjecture 4.1, at `k = 4`: `G₂` is bipartite and
$\beta_4(G_2)=7<8\le SF_4(G_2)$. -/
theorem bipartite_k4_counterexample :
    G₂.Colorable 2 ∧ betaK G₂ 4 = 7 ∧ 8 ≤ sfK G₂ 4 ∧ betaK G₂ 4 < sfK G₂ 4 :=
  ⟨G₂_colorable, betaK_G₂, card_le_sfK G₂ minimal_S₂, betaK_G₂ ▸ card_le_sfK G₂ minimal_S₂⟩

end ExampleK4

/-- Conjecture 4.1 (Bipartite equality) of arXiv:2610.03785 is false: it is not the case
that $\beta_k(G)=SF_k(G)$ for every (finite) bipartite graph `G` and every `k ≥ 1`. -/
theorem conj_4_1_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Colorable 2 →
      ∀ k : ℕ, 1 ≤ k → betaK G k = sfK G k := by
  intro h
  have heq := h 10 G₁ G₁_colorable 2 (by norm_num)
  exact absurd heq G₁_counterexample.2.2.2.ne

/-- Conjecture 4.2 (Bipartite dissociation equality) of arXiv:2610.03785 is false: it is
not the case that $\beta_2(G)=SF_2(G)$ for every (finite) bipartite graph `G`. -/
theorem conj_4_2_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Colorable 2 →
      betaK G 2 = sfK G 2 := by
  intro h
  exact absurd (h 10 G₁ G₁_colorable) G₁_counterexample.2.2.2.ne

/-- Conjecture 6.2 (Triangle-free case for `k = 2`) of arXiv:2610.03785 is false: it is
not the case that $\beta_2(G)=SF_2(G)$ for every (finite) triangle-free graph `G`. -/
theorem conj_6_2_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.CliqueFree 3 →
      betaK G 2 = sfK G 2 := by
  intro h
  exact absurd (h 10 G₁ (G₁_colorable.cliqueFree (by norm_num))) G₁_counterexample.2.2.2.ne

end UpperStarFormingSetsRefutation
