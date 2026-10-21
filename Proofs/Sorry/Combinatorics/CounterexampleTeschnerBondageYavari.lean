/-
  A Counterexample to Teschner's Bondage-Number Conjecture (Yavari).
  Source: arXiv:2609.04257 (Yavari, 2026), Theorem 1.1, proved via
  Proposition 3.2 (gamma(G) = 6), Proposition 4.1 (b(G) <= 5, via
  F_5 and H = G - {0,6}), Proposition 4.2 (exact four-edge
  certificate) and Lemma 2.2 (bundle criterion).  Graph: eq. (3.1).
  Recorded 2026-10-21.

  Conjecture refuted (Teschner 1995; Conjecture 3.6.3 of Xu's
  bondage survey arXiv:1204.4010), verbatim from the paper:

    "Every finite simple graph G with at least one edge satisfies
     b(G) <= (3/2) Delta(G)."

  Paper's Theorem 1.1, verbatim:

    "There exists a connected cubic bipartite graph G such that
     gamma(G)=6 and b(G)=5.  Consequently, b(G)=5>9/2=(3/2)Delta(G),
     so Conjecture 1.1 is false."

  Status in the paper: proved (gamma(G) = 6 and b(G) <= 5 by hand;
  b(G) >= 5 by an exhaustive computation over the 17,550 four-edge
  subsets, verifier in the paper's appendix).  The paper is an
  unreviewed preprint.

  Formalization.  `domNum` and `bondage` mirror the paper's
  definitions (domination number, eq. (2.1) bondage number) with
  `sInf`.  The finite part is kernel-checked with `decide +kernel`
  (no `native_decide`) on Nat-bitmask checkers whose soundness is
  proved here:
  * `check5`: no 5-multiset of vertices has closed neighbourhoods
    covering all 18 vertices (gamma(G) >= 6);
  * `inner4 a`, a < 27: for every multiset {a >= b >= c >= d} of edge
    indices, some certificate set D (one of 55 minimum dominating
    sets, chosen greedily) has no bundle B(D,x) inside {a,b,c,d}
    (Lemma 2.2 of the paper); the certificate data `certs` is
    validated against `G` by `certs_sound`.
  The four-edge computation is split into 27 declarations so each
  kernel check stays small.  Cold elaboration: about 60 s, 2.8 GB.

  Main results (no `sorry`; axioms propext, Classical.choice,
  Quot.sound only): `domNum_G` (gamma(G) = 6),
  `domNum_deleteEdges_F5` (gamma(G - F_5) = 7),
  `domNum_deleteEdges_of_card_le_four` (gamma(G - F) = 6 for every
  finset F of at most four unordered pairs), `bondage_G` (b(G) = 5),
  `maxDegree_G`, `thm_1_1`, and `teschner_conjecture_false`.
-/
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
-- Elaborate declarations sequentially: the 30 kernel computations below then run one
-- at a time, which keeps peak memory low.
set_option Elab.async false

namespace CounterexampleTeschnerBondageYavari

open Finset SimpleGraph

/-! ## Domination number and bondage number -/

/-- `D` dominates `H`: every vertex lies in `D` or has a neighbour in `D`. -/
def IsDominating {V : Type*} (H : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ d ∈ D, H.Adj v d

/-- The domination number `γ(H)`: the least cardinality of a dominating set. -/
noncomputable def domNum {V : Type*} (H : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, D.card = k ∧ IsDominating H D}

/-- The bondage number `b(H)` (paper eq. (2.1)): the least `|F|`, `F ⊆ E(H)`,
with `γ(H - F) > γ(H)`. -/
noncomputable def bondage {V : Type*} (H : SimpleGraph V) : ℕ :=
  sInf {k | ∃ F : Finset (Sym2 V), (F : Set (Sym2 V)) ⊆ H.edgeSet ∧ F.card = k ∧
    domNum H < domNum (H.deleteEdges F)}

/-- Any dominating set bounds the domination number from above. -/
theorem domNum_le_card {V : Type*} (H : SimpleGraph V) (D : Finset V)
    (hD : IsDominating H D) : domNum H ≤ D.card :=
  Nat.sInf_le ⟨D, rfl, hD⟩

/-- A lower bound on every dominating set is a lower bound on `γ`. -/
theorem le_domNum {V : Type*} [Fintype V] (H : SimpleGraph V) (k : ℕ)
    (h : ∀ D : Finset V, IsDominating H D → k ≤ D.card) : k ≤ domNum H := by
  have hne : {k | ∃ D : Finset V, D.card = k ∧ IsDominating H D}.Nonempty :=
    ⟨_, Finset.univ, rfl, fun v => Or.inl (Finset.mem_univ v)⟩
  refine le_csInf hne ?_
  rintro _ ⟨D, rfl, hD⟩
  exact h D hD

/-- A dominating set of `H - s` (edges in `s` deleted) also dominates `H`. -/
theorem IsDominating.of_deleteEdges {V : Type*} {H : SimpleGraph V} {s : Set (Sym2 V)}
    {D : Finset V} (hD : IsDominating (H.deleteEdges s) D) : IsDominating H D := by
  intro v
  rcases hD v with hv | ⟨d, hd, hadj⟩
  · exact Or.inl hv
  · exact Or.inr ⟨d, hd, (SimpleGraph.deleteEdges_adj.mp hadj).1⟩

/-! ## The graph of paper eq. (3.1) -/

/-- The 27 edges of eq. (3.1), as pairs of vertex labels in `{0, …, 17}`. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 6), (0, 10), (0, 16), (1, 8), (1, 11), (1, 12),
   (2, 4), (2, 5), (2, 13), (3, 4), (3, 5), (3, 9),
   (4, 16), (5, 11), (6, 7), (6, 13), (7, 8), (7, 14),
   (8, 13), (9, 10), (9, 14), (10, 15), (11, 15),
   (12, 15), (12, 17), (14, 17), (16, 17)]

/-- The 18-vertex cubic bipartite graph `G` of eq. (3.1): `u ~ v` iff `{u, v}` is listed. -/
def G : SimpleGraph (Fin 18) where
  Adj u v := (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by decide⟩

/-- Adjacency in `G` is decided by membership in `edgeList`. -/
instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList))

example : G.Adj 0 6 ∧ G.Adj 6 0 ∧ G.Adj 17 16 ∧ ¬ G.Adj 0 1 ∧ ¬ G.Adj 4 4 := by decide

/-- The five-edge set `F₅` of eq. (4.1): all edges at the adjacent vertices `0` and `6`. -/
def F5 : Finset (Sym2 (Fin 18)) := {s(0, 6), s(0, 10), s(0, 16), s(6, 7), s(6, 13)}

/-! ## Bounded Boolean quantifiers (kernel-friendly) -/

/-- `allLT n f = true` iff `f k = true` for every `k < n`. -/
def allLT (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => f k && acc) n

/-- Boolean `∃` over a list, by the list recursor. -/
def anyL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ acc => f h || acc) l

/-- Boolean `∀` over a list, by the list recursor. -/
def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ acc => f h && acc) l

/-- `allLT n f` is the bounded universal quantifier `∀ k < n, f k`. -/
theorem allLT_iff (n : ℕ) (f : ℕ → Bool) : allLT n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allLT]
  | succ n ih =>
    show (f n && allLT n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- `anyL l f` is the Boolean `∃ x ∈ l, f x`. -/
theorem anyL_iff {α : Type} (l : List α) (f : α → Bool) :
    anyL l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp [anyL]
  | cons h t ih =>
    show (f h || anyL t f) = true ↔ _
    rw [Bool.or_eq_true, ih]
    simp

/-- `allL l f` is the Boolean `∀ x ∈ l, f x`. -/
theorem allL_iff {α : Type} (l : List α) (f : α → Bool) :
    allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allL]
  | cons h t ih =>
    show (f h && allL t f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    simp

example : allLT 3 (fun k => decide (k < 3)) = true ∧ allLT 4 (fun k => decide (k < 3)) = false :=
  by decide

/-! ## Gamma(G) ≥ 6: closed-neighbourhood masks -/

/-- Closed-neighbourhood bitmasks `N[v]` of `G`, indexed by `v`. -/
def nbMasks : List ℕ :=
  [66625, 6402, 8244, 568, 65564, 2092, 8385, 16832, 8578, 17928, 34305, 34850, 167938, 8516, 148096, 39936, 196625, 217088]

/-- The closed-neighbourhood mask of vertex `v` (zero outside `{0, …, 17}`). -/
def nb (v : ℕ) : ℕ := nbMasks.getD v 0

/-- Bit `u` of `nb v` is set iff `u ∈ N[v]`. -/
theorem nb_testBit_iff : ∀ u v : Fin 18, (nb v.val).testBit u.val = true ↔ (u = v ∨ G.Adj u v) := by
  decide +kernel

/-- `m` has all 18 vertex bits set. -/
def covers (m : ℕ) : Bool := allLT 18 fun u => m.testBit u

/-- No multiset `{a ≥ b ≥ c ≥ d ≥ e}` of vertices has closed neighbourhoods covering `V(G)`. -/
def check5 : Bool :=
  allLT 18 fun a => allLT (a + 1) fun b => allLT (b + 1) fun c => allLT (c + 1) fun d =>
    allLT (d + 1) fun e => !covers (nb a ||| nb b ||| nb c ||| nb d ||| nb e)

/-- Kernel computation: `check5` holds (8 568 five-sets, with repetitions 26 334 tuples). -/
theorem check5_eq_true : check5 = true := by decide +kernel

/-- Every finset of naturals of size at most five below `N > 0` lies inside a
non-increasing 5-tuple below `N`. -/
theorem exists_desc5 (S : Finset ℕ) (N : ℕ) (hN : 0 < N) (hS : ∀ x ∈ S, x < N)
    (hcard : S.card ≤ 5) :
    ∃ a < N, ∃ b < a + 1, ∃ c < b + 1, ∃ d < c + 1, ∃ e < d + 1,
      ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  have hp : (S.sort (· ≥ ·)).Pairwise (· ≥ ·) := Finset.pairwise_sort S _
  have hlen : (S.sort (· ≥ ·)).length = S.card := Finset.length_sort _
  have hmem : ∀ x, x ∈ S.sort (· ≥ ·) ↔ x ∈ S := fun x => Finset.mem_sort _
  generalize S.sort (· ≥ ·) = l at hp hlen hmem
  have hlt : ∀ x ∈ l, x < N := fun x hx => hS x ((hmem x).mp hx)
  simp only [← hmem]
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, List.length_cons,
      List.length_nil, forall_eq_or_imp, forall_eq, or_false, and_true,
      List.Pairwise.nil] at hp hlen hlt ⊢
  · exact ⟨0, hN, 0, by omega, 0, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt, 0, by omega, 0, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, 0, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, c, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, c, by omega, d, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, c, by omega, d, by omega, e, by omega, by simp⟩
  · omega

/-- **Proposition 3.2, lower half.** No set of at most five vertices dominates `G`. -/
theorem not_isDominating_of_card_le_five (D : Finset (Fin 18)) (hD : D.card ≤ 5) :
    ¬ IsDominating G D := by
  intro hdom
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, hsub⟩ :=
    exists_desc5 (D.map Fin.valEmbedding) 18 (by norm_num) (by simp) (by simpa using hD)
  have h5 : (!covers (nb a ||| nb b ||| nb c ||| nb d ||| nb e)) = true :=
    (allLT_iff _ _).mp ((allLT_iff _ _).mp ((allLT_iff _ _).mp ((allLT_iff _ _).mp
      ((allLT_iff _ _).mp check5_eq_true a ha) b hb) c hc) d hd) e he
  have key : ∀ w ∈ D, ∀ u : Fin 18, (u = w ∨ G.Adj u w) →
      (nb a ||| nb b ||| nb c ||| nb d ||| nb e).testBit u = true := by
    intro w hw u huw
    have hbit := (nb_testBit_iff u w).mpr huw
    have hwS : w.val ∈ D.map Fin.valEmbedding := Finset.mem_map_of_mem _ hw
    rcases hsub _ hwS with h | h | h | h | h <;> simp [← h, hbit]
  have hcov : covers (nb a ||| nb b ||| nb c ||| nb d ||| nb e) = true := by
    rw [covers, allLT_iff]
    intro u hu
    rcases hdom ⟨u, hu⟩ with hmem | ⟨w, hw, hadj⟩
    · exact key _ hmem ⟨u, hu⟩ (Or.inl rfl)
    · exact key w hw ⟨u, hu⟩ (Or.inr hadj)
  simp [hcov] at h5

/-- A minimum dominating set of `G` (the first certificate set). -/
theorem isDominating_D6 : IsDominating G {0, 1, 2, 3, 14, 15} := by
  unfold IsDominating
  decide

/-- **Proposition 3.2.** `γ(G) = 6`. -/
theorem domNum_G : domNum G = 6 := by
  apply le_antisymm
  · exact (domNum_le_card G _ isDominating_D6).trans (by decide)
  · apply le_domNum
    intro D hD
    by_contra hlt
    exact not_isDominating_of_card_le_five D (by omega) hD

/-! ## `γ(G - F₅) = 7` (Proposition 4.1) -/

/-- Domination in `G - F₅`, unfolded to adjacency in `G` avoiding `F₅`. -/
theorem isDominating_deleteEdges_F5_iff (D : Finset (Fin 18)) :
    IsDominating (G.deleteEdges (F5 : Set (Sym2 (Fin 18)))) D ↔
      ∀ v, v ∈ D ∨ ∃ d ∈ D, G.Adj v d ∧ s(v, d) ∉ F5 := by
  simp only [IsDominating, SimpleGraph.deleteEdges_adj, Finset.mem_coe]

/-- The seven-set `{0, 6} ∪ A`, `A = {1, 2, 4, 10, 14}` of eq. (4.2), dominates `G - F₅`. -/
theorem isDominating_deleteEdges_F5_seven :
    IsDominating (G.deleteEdges (F5 : Set (Sym2 (Fin 18)))) {0, 6, 1, 2, 4, 10, 14} := by
  rw [isDominating_deleteEdges_F5_iff]
  decide

/-- Vertex `6` has no neighbour in `G - F₅`. -/
theorem not_adj_six_deleteEdges_F5 : ∀ v : Fin 18, ¬ (G.Adj v 6 ∧ s(v, 6) ∉ F5) := by decide

/-- Vertex `0` has no neighbour in `G - F₅`. -/
theorem not_adj_zero_deleteEdges_F5 : ∀ v : Fin 18, ¬ (G.Adj v 0 ∧ s(v, 0) ∉ F5) := by decide

/-- **Proposition 4.1.** `γ(G - F₅) = 7`. -/
theorem domNum_deleteEdges_F5 : domNum (G.deleteEdges (F5 : Set (Sym2 (Fin 18)))) = 7 := by
  apply le_antisymm
  · exact (domNum_le_card _ _ isDominating_deleteEdges_F5_seven).trans (by decide)
  · apply le_domNum
    intro D hD
    rw [isDominating_deleteEdges_F5_iff] at hD
    have h0 : (0 : Fin 18) ∈ D := by
      rcases hD 0 with h | ⟨d, _, hadj, hF⟩
      · exact h
      · exact absurd ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩ (not_adj_zero_deleteEdges_F5 d)
    have h6 : (6 : Fin 18) ∈ D := by
      rcases hD 6 with h | ⟨d, _, hadj, hF⟩
      · exact h
      · exact absurd ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩ (not_adj_six_deleteEdges_F5 d)
    have hdomG : IsDominating G (D.erase 6) := by
      intro v
      by_cases hv6 : v = 6
      · subst hv6
        exact Or.inr ⟨0, Finset.mem_erase.mpr ⟨by decide, h0⟩, by decide⟩
      rcases hD v with hv | ⟨d, hd, hadj, hF⟩
      · exact Or.inl (Finset.mem_erase.mpr ⟨hv6, hv⟩)
      · have hd6 : d ≠ 6 := by
          rintro rfl
          exact not_adj_six_deleteEdges_F5 v ⟨hadj, hF⟩
        exact Or.inr ⟨d, Finset.mem_erase.mpr ⟨hd6, hd⟩, hadj⟩
    have hcard : (D.erase 6).card + 1 = D.card := Finset.card_erase_add_one h6
    by_contra hlt
    exact not_isDominating_of_card_le_five (D.erase 6) (by omega) hdomG

/-! ## Four deleted edges never suffice (Proposition 4.2, Lemma 2.2) -/

/-- The unordered edge with index `i` in `edgeList` (junk `s(0, 0)` past the end). -/
def edgeSym (i : ℕ) : Sym2 (Fin 18) :=
  match edgeList[i]? with
  | some pq => s(Fin.ofNat 18 pq.1, Fin.ofNat 18 pq.2)
  | none => s(0, 0)

example : edgeSym 0 = s(0, 6) ∧ edgeSym 26 = s(16, 17) := by decide

/-- The 27 listed edges are pairwise distinct. -/
theorem edgeSym_injOn : ∀ i < 27, ∀ j < 27, edgeSym i = edgeSym j → i = j := by
  decide +kernel

/-- A certificate: a vertex set `D` (labels) and its bundle masks `(x, mask)`. -/
structure Cert where
  /-- The candidate dominating set, as vertex labels. -/
  D : List ℕ
  /-- For each `x ∉ D`, the mask of edge indices joining `x` to `D`. -/
  bundles : List (ℕ × ℕ)

/-- The 55 certificate sets `D` (minimum dominating sets of `G`, greedy order), each with
its bundle masks `(x, B(D, x))` for `x ∉ D`; bit `i` of a mask is edge `edgeList[i]`. -/
def certs : List Cert :=
  [⟨[0, 1, 2, 3, 14, 15],
      [(4, 576), (5, 1152), (6, 1), (7, 131072), (8, 8), (9, 1050624), (10, 2097154), (11, 4194320), (12, 8388640), (13, 256), (16, 4), (17, 33554432)]⟩,
    ⟨[4, 7, 10, 11, 13, 17],
      [(0, 2), (1, 16), (2, 320), (3, 512), (5, 8192), (6, 49152), (8, 327680), (9, 524288), (12, 16777216), (14, 33685504), (15, 6291456), (16, 67112960)]⟩,
    ⟨[5, 6, 8, 9, 15, 16],
      [(0, 5), (1, 8), (2, 128), (3, 3072), (4, 4096), (7, 81920), (10, 2621440), (11, 4202496), (12, 8388608), (13, 294912), (14, 1048576), (17, 67108864)]⟩,
    ⟨[0, 2, 7, 9, 11, 12],
      [(1, 48), (3, 2048), (4, 64), (5, 8320), (6, 16385), (8, 65536), (10, 524290), (13, 256), (14, 1179648), (15, 12582912), (16, 4), (17, 16777216)]⟩,
    ⟨[1, 5, 10, 13, 14, 16],
      [(0, 6), (2, 384), (3, 1024), (4, 4096), (6, 32768), (7, 131072), (8, 262152), (9, 1572864), (11, 8208), (12, 32), (15, 2097152), (17, 100663296)]⟩,
    ⟨[0, 2, 3, 8, 15, 17],
      [(1, 8), (4, 576), (5, 1152), (6, 1), (7, 65536), (9, 2048), (10, 2097154), (11, 4194304), (12, 25165824), (13, 262400), (14, 33554432), (16, 67108868)]⟩,
    ⟨[1, 4, 5, 6, 10, 17],
      [(0, 3), (2, 192), (3, 1536), (7, 16384), (8, 8), (9, 524288), (11, 8208), (12, 16777248), (13, 32768), (14, 33554432), (15, 2097152), (16, 67112960)]⟩,
    ⟨[0, 4, 5, 8, 12, 14],
      [(1, 40), (2, 192), (3, 1536), (6, 1), (7, 196608), (9, 1048576), (10, 2), (11, 8192), (13, 262144), (15, 8388608), (16, 4100), (17, 50331648)]⟩,
    ⟨[1, 2, 7, 9, 15, 16],
      [(0, 4), (3, 2048), (4, 4160), (5, 128), (6, 16384), (8, 65544), (10, 2621440), (11, 4194320), (12, 8388640), (13, 256), (14, 1179648), (17, 67108864)]⟩,
    ⟨[3, 6, 10, 11, 13, 17],
      [(0, 3), (1, 16), (2, 256), (4, 512), (5, 9216), (7, 16384), (8, 262144), (9, 526336), (12, 16777216), (14, 33554432), (15, 6291456), (16, 67108864)]⟩,
    ⟨[4, 6, 8, 9, 11, 17],
      [(0, 1), (1, 24), (2, 64), (3, 2560), (5, 8192), (7, 81920), (10, 524288), (12, 16777216), (13, 294912), (14, 34603008), (15, 4194304), (16, 67112960)]⟩,
    ⟨[0, 3, 11, 12, 13, 14],
      [(1, 48), (2, 256), (4, 512), (5, 9216), (6, 32769), (7, 131072), (8, 262144), (9, 1050624), (10, 2), (15, 12582912), (16, 4), (17, 50331648)]⟩,
    ⟨[2, 5, 7, 10, 12, 16],
      [(0, 6), (1, 32), (3, 1024), (4, 4160), (6, 16384), (8, 65536), (9, 524288), (11, 8192), (13, 256), (14, 131072), (15, 10485760), (17, 83886080)]⟩,
    ⟨[0, 4, 11, 13, 14, 15],
      [(1, 16), (2, 320), (3, 512), (5, 8192), (6, 32769), (7, 131072), (8, 262144), (9, 1048576), (10, 2097154), (12, 8388608), (16, 4100), (17, 33554432)]⟩,
    ⟨[1, 2, 4, 7, 10, 17],
      [(0, 2), (3, 512), (5, 128), (6, 16384), (8, 65544), (9, 524288), (11, 16), (12, 16777248), (13, 256), (14, 33685504), (15, 2097152), (16, 67112960)]⟩,
    ⟨[5, 7, 9, 12, 13, 16],
      [(0, 4), (1, 32), (2, 384), (3, 3072), (4, 4096), (6, 49152), (8, 327680), (10, 524288), (11, 8192), (14, 1179648), (15, 8388608), (17, 83886080)]⟩,
    ⟨[0, 3, 5, 8, 12, 14],
      [(1, 40), (2, 128), (4, 512), (6, 1), (7, 196608), (9, 1050624), (10, 2), (11, 8192), (13, 262144), (15, 8388608), (16, 4), (17, 50331648)]⟩,
    ⟨[0, 2, 8, 9, 15, 17],
      [(1, 8), (3, 2048), (4, 64), (5, 128), (6, 1), (7, 65536), (10, 2621442), (11, 4194304), (12, 25165824), (13, 262400), (14, 34603008), (16, 67108868)]⟩,
    ⟨[0, 4, 8, 9, 11, 17],
      [(1, 24), (2, 64), (3, 2560), (5, 8192), (6, 1), (7, 65536), (10, 524290), (12, 16777216), (13, 262144), (14, 34603008), (15, 4194304), (16, 67112964)]⟩,
    ⟨[0, 2, 7, 9, 11, 17],
      [(1, 16), (3, 2048), (4, 64), (5, 8320), (6, 16385), (8, 65536), (10, 524290), (12, 16777216), (13, 256), (14, 34734080), (15, 4194304), (16, 67108868)]⟩,
    ⟨[1, 2, 3, 6, 10, 17],
      [(0, 3), (4, 576), (5, 1152), (7, 16384), (8, 8), (9, 526336), (11, 16), (12, 16777248), (13, 33024), (14, 33554432), (15, 2097152), (16, 67108864)]⟩,
    ⟨[1, 5, 13, 14, 15, 16],
      [(0, 4), (2, 384), (3, 1024), (4, 4096), (6, 32768), (7, 131072), (8, 262152), (9, 1048576), (10, 2097152), (11, 4202512), (12, 8388640), (17, 100663296)]⟩,
    ⟨[1, 2, 6, 9, 12, 16],
      [(0, 5), (3, 2048), (4, 4160), (5, 128), (7, 16384), (8, 8), (10, 524288), (11, 16), (13, 33024), (14, 1048576), (15, 8388608), (17, 83886080)]⟩,
    ⟨[1, 4, 6, 10, 11, 14],
      [(0, 3), (2, 64), (3, 512), (5, 8192), (7, 147456), (8, 8), (9, 1572864), (12, 32), (13, 32768), (15, 6291456), (16, 4096), (17, 33554432)]⟩,
    ⟨[5, 7, 8, 9, 15, 16],
      [(0, 4), (1, 8), (2, 128), (3, 3072), (4, 4096), (6, 16384), (10, 2621440), (11, 4202496), (12, 8388608), (13, 262144), (14, 1179648), (17, 67108864)]⟩,
    ⟨[1, 5, 6, 10, 14, 16],
      [(0, 7), (2, 128), (3, 1024), (4, 4096), (7, 147456), (8, 8), (9, 1572864), (11, 8208), (12, 32), (13, 32768), (15, 2097152), (17, 100663296)]⟩,
    ⟨[0, 2, 3, 8, 11, 17],
      [(1, 24), (4, 576), (5, 9344), (6, 1), (7, 65536), (9, 2048), (10, 2), (12, 16777216), (13, 262400), (14, 33554432), (15, 4194304), (16, 67108868)]⟩,
    ⟨[4, 6, 8, 10, 11, 17],
      [(0, 3), (1, 24), (2, 64), (3, 512), (5, 8192), (7, 81920), (9, 524288), (12, 16777216), (13, 294912), (14, 33554432), (15, 6291456), (16, 67112960)]⟩,
    ⟨[5, 7, 8, 10, 12, 16],
      [(0, 6), (1, 40), (2, 128), (3, 1024), (4, 4096), (6, 16384), (9, 524288), (11, 8192), (13, 262144), (14, 131072), (15, 10485760), (17, 83886080)]⟩,
    ⟨[5, 8, 9, 13, 15, 16],
      [(0, 4), (1, 8), (2, 384), (3, 3072), (4, 4096), (6, 32768), (7, 65536), (10, 2621440), (11, 4202496), (12, 8388608), (14, 1048576), (17, 67108864)]⟩,
    ⟨[0, 2, 5, 8, 12, 14],
      [(1, 40), (3, 1024), (4, 64), (6, 1), (7, 196608), (9, 1048576), (10, 2), (11, 8192), (13, 262400), (15, 8388608), (16, 4), (17, 50331648)]⟩,
    ⟨[3, 4, 6, 7, 12, 15],
      [(0, 1), (1, 32), (2, 64), (5, 1024), (8, 65536), (9, 2048), (10, 2097152), (11, 4194304), (13, 32768), (14, 131072), (16, 4096), (17, 16777216)]⟩,
    ⟨[1, 3, 10, 13, 14, 16],
      [(0, 6), (2, 256), (4, 4608), (5, 1024), (6, 32768), (7, 131072), (8, 262152), (9, 1574912), (11, 16), (12, 32), (15, 2097152), (17, 100663296)]⟩,
    ⟨[0, 1, 2, 7, 9, 12],
      [(3, 2048), (4, 64), (5, 128), (6, 16385), (8, 65544), (10, 524290), (11, 16), (13, 256), (14, 1179648), (15, 8388608), (16, 4), (17, 16777216)]⟩,
    ⟨[0, 3, 5, 8, 15, 17],
      [(1, 8), (2, 128), (4, 512), (6, 1), (7, 65536), (9, 2048), (10, 2097154), (11, 4202496), (12, 25165824), (13, 262144), (14, 33554432), (16, 67108868)]⟩,
    ⟨[3, 8, 10, 11, 13, 17],
      [(0, 2), (1, 24), (2, 256), (4, 512), (5, 9216), (6, 32768), (7, 65536), (9, 526336), (12, 16777216), (14, 33554432), (15, 6291456), (16, 67108864)]⟩,
    ⟨[3, 11, 13, 14, 15, 16],
      [(0, 4), (1, 16), (2, 256), (4, 4608), (5, 9216), (6, 32768), (7, 131072), (8, 262144), (9, 1050624), (10, 2097152), (12, 8388608), (17, 100663296)]⟩,
    ⟨[5, 10, 12, 13, 14, 16],
      [(0, 6), (1, 32), (2, 384), (3, 1024), (4, 4096), (6, 32768), (7, 131072), (8, 262144), (9, 1572864), (11, 8192), (15, 10485760), (17, 117440512)]⟩,
    ⟨[0, 1, 4, 11, 13, 14],
      [(2, 320), (3, 512), (5, 8192), (6, 32769), (7, 131072), (8, 262152), (9, 1048576), (10, 2), (12, 32), (15, 4194304), (16, 4100), (17, 33554432)]⟩,
    ⟨[1, 2, 6, 9, 11, 16],
      [(0, 5), (3, 2048), (4, 4160), (5, 8320), (7, 16384), (8, 8), (10, 524288), (12, 32), (13, 33024), (14, 1048576), (15, 4194304), (17, 67108864)]⟩,
    ⟨[7, 9, 11, 12, 13, 16],
      [(0, 4), (1, 48), (2, 256), (3, 2048), (4, 4096), (5, 8192), (6, 49152), (8, 327680), (10, 524288), (14, 1179648), (15, 12582912), (17, 83886080)]⟩,
    ⟨[0, 2, 8, 9, 11, 12],
      [(1, 56), (3, 2048), (4, 64), (5, 8320), (6, 1), (7, 65536), (10, 524290), (13, 262400), (14, 1048576), (15, 12582912), (16, 4), (17, 16777216)]⟩,
    ⟨[0, 4, 5, 12, 13, 14],
      [(1, 32), (2, 448), (3, 1536), (6, 32769), (7, 131072), (8, 262144), (9, 1048576), (10, 2), (11, 8192), (15, 8388608), (16, 4100), (17, 50331648)]⟩,
    ⟨[1, 2, 4, 6, 10, 14],
      [(0, 3), (3, 512), (5, 128), (7, 147456), (8, 8), (9, 1572864), (11, 16), (12, 32), (13, 33024), (15, 2097152), (16, 4096), (17, 33554432)]⟩,
    ⟨[1, 2, 5, 7, 10, 17],
      [(0, 2), (3, 1024), (4, 64), (6, 16384), (8, 65544), (9, 524288), (11, 8208), (12, 16777248), (13, 256), (14, 33685504), (15, 2097152), (16, 67108864)]⟩,
    ⟨[1, 4, 5, 10, 13, 14],
      [(0, 2), (2, 448), (3, 1536), (6, 32768), (7, 131072), (8, 262152), (9, 1572864), (11, 8208), (12, 32), (15, 2097152), (16, 4096), (17, 33554432)]⟩,
    ⟨[0, 2, 5, 7, 9, 12],
      [(1, 32), (3, 3072), (4, 64), (6, 16385), (8, 65536), (10, 524290), (11, 8192), (13, 256), (14, 1179648), (15, 8388608), (16, 4), (17, 16777216)]⟩,
    ⟨[0, 3, 8, 13, 15, 17],
      [(1, 8), (2, 256), (4, 512), (5, 1024), (6, 32769), (7, 65536), (9, 2048), (10, 2097154), (11, 4194304), (12, 25165824), (14, 33554432), (16, 67108868)]⟩,
    ⟨[0, 4, 5, 8, 9, 12],
      [(1, 40), (2, 192), (3, 3584), (6, 1), (7, 65536), (10, 524290), (11, 8192), (13, 262144), (14, 1048576), (15, 8388608), (16, 4100), (17, 16777216)]⟩,
    ⟨[0, 4, 5, 8, 14, 15],
      [(1, 8), (2, 192), (3, 1536), (6, 1), (7, 196608), (9, 1048576), (10, 2097154), (11, 4202496), (12, 8388608), (13, 262144), (16, 4100), (17, 33554432)]⟩,
    ⟨[1, 4, 6, 9, 11, 17],
      [(0, 1), (2, 64), (3, 2560), (5, 8192), (7, 16384), (8, 8), (10, 524288), (12, 16777248), (13, 32768), (14, 34603008), (15, 4194304), (16, 67112960)]⟩,
    ⟨[1, 5, 7, 10, 13, 16],
      [(0, 6), (2, 384), (3, 1024), (4, 4096), (6, 49152), (8, 327688), (9, 524288), (11, 8208), (12, 32), (14, 131072), (15, 2097152), (17, 67108864)]⟩,
    ⟨[2, 6, 8, 9, 11, 17],
      [(0, 1), (1, 24), (3, 2048), (4, 64), (5, 8320), (7, 81920), (10, 524288), (12, 16777216), (13, 295168), (14, 34603008), (15, 4194304), (16, 67108864)]⟩,
    ⟨[3, 8, 13, 14, 15, 16],
      [(0, 4), (1, 8), (2, 256), (4, 4608), (5, 1024), (6, 32768), (7, 196608), (9, 1050624), (10, 2097152), (11, 4194304), (12, 8388608), (17, 100663296)]⟩,
    ⟨[4, 5, 6, 8, 9, 12],
      [(0, 1), (1, 40), (2, 192), (3, 3584), (7, 81920), (10, 524288), (11, 8192), (13, 294912), (14, 1048576), (15, 8388608), (16, 4096), (17, 16777216)]⟩]


/-- If `edgeList[i] = (x, y)` then `edgeSym i` is the unordered pair `{x, y}`. -/
theorem edgeSym_of_getElem? {i x y : ℕ} (h : edgeList[i]? = some (x, y)) (hx : x < 18)
    (hy : y < 18) : edgeSym i = s(⟨x, hx⟩, ⟨y, hy⟩) := by
  rw [edgeSym, h]
  simp [Fin.ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Certificate validity, checked on labels: each `D` lists at most six vertices, every
vertex outside `D` has a recorded bundle, and every bit `i` of a bundle mask of `x` is a
listed edge `edgeList[i]` joining `x` to a vertex of `D`. -/
theorem certs_sound : ∀ C ∈ certs, C.D.length ≤ 6 ∧
    ∀ v : Fin 18, v.val ∈ C.D ∨ ∃ p ∈ C.bundles, p.1 = v.val ∧ p.2 < 2 ^ 27 ∧
      ∀ i < 27, p.2.testBit i = true → ∃ w ∈ C.D, w < 18 ∧
        (edgeList[i]? = some (v.val, w) ∨ edgeList[i]? = some (w, v.val)) := by
  decide +kernel

/-- Some certificate survives the deletion of the edge-index set encoded by mask `T`
(Lemma 2.2: no bundle lies inside the deleted set). -/
def goodT (T : ℕ) : Bool :=
  anyL certs fun C => allL C.bundles fun p => !Nat.beq (p.2 &&& T) p.2

/-- All non-increasing 4-tuples `a ≥ b ≥ c ≥ d` of edge indices with top entry `a`
are survived by some certificate. -/
def inner4 (a : ℕ) : Bool :=
  allLT (a + 1) fun b => allLT (b + 1) fun c => allLT (c + 1) fun d =>
    goodT (2 ^ a ||| 2 ^ b ||| 2 ^ c ||| 2 ^ d)

/-- Kernel computation: the four-edge check for top edge index 0. -/
theorem inner4_0 : inner4 0 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 1. -/
theorem inner4_1 : inner4 1 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 2. -/
theorem inner4_2 : inner4 2 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 3. -/
theorem inner4_3 : inner4 3 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 4. -/
theorem inner4_4 : inner4 4 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 5. -/
theorem inner4_5 : inner4 5 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 6. -/
theorem inner4_6 : inner4 6 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 7. -/
theorem inner4_7 : inner4 7 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 8. -/
theorem inner4_8 : inner4 8 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 9. -/
theorem inner4_9 : inner4 9 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 10. -/
theorem inner4_10 : inner4 10 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 11. -/
theorem inner4_11 : inner4 11 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 12. -/
theorem inner4_12 : inner4 12 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 13. -/
theorem inner4_13 : inner4 13 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 14. -/
theorem inner4_14 : inner4 14 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 15. -/
theorem inner4_15 : inner4 15 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 16. -/
theorem inner4_16 : inner4 16 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 17. -/
theorem inner4_17 : inner4 17 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 18. -/
theorem inner4_18 : inner4 18 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 19. -/
theorem inner4_19 : inner4 19 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 20. -/
theorem inner4_20 : inner4 20 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 21. -/
theorem inner4_21 : inner4 21 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 22. -/
theorem inner4_22 : inner4 22 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 23. -/
theorem inner4_23 : inner4 23 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 24. -/
theorem inner4_24 : inner4 24 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 25. -/
theorem inner4_25 : inner4 25 = true := by decide +kernel

/-- Kernel computation: the four-edge check for top edge index 26. -/
theorem inner4_26 : inner4 26 = true := by decide +kernel

/-- The four-edge check holds for every top edge index. -/
theorem inner4_all : ∀ a < 27, inner4 a = true := by
  intro a ha
  interval_cases a
  exacts [inner4_0, inner4_1, inner4_2, inner4_3, inner4_4, inner4_5, inner4_6, inner4_7, inner4_8, inner4_9, inner4_10, inner4_11, inner4_12, inner4_13, inner4_14, inner4_15, inner4_16, inner4_17, inner4_18, inner4_19, inner4_20, inner4_21, inner4_22, inner4_23, inner4_24, inner4_25, inner4_26]

/-- Every finset of naturals of size at most four below `N > 0` lies inside a
non-increasing 4-tuple below `N`. -/
theorem exists_desc4 (S : Finset ℕ) (N : ℕ) (hN : 0 < N) (hS : ∀ x ∈ S, x < N)
    (hcard : S.card ≤ 4) :
    ∃ a < N, ∃ b < a + 1, ∃ c < b + 1, ∃ d < c + 1,
      ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = d := by
  have hp : (S.sort (· ≥ ·)).Pairwise (· ≥ ·) := Finset.pairwise_sort S _
  have hlen : (S.sort (· ≥ ·)).length = S.card := Finset.length_sort _
  have hmem : ∀ x, x ∈ S.sort (· ≥ ·) ↔ x ∈ S := fun x => Finset.mem_sort _
  generalize S.sort (· ≥ ·) = l at hp hlen hmem
  have hlt : ∀ x ∈ l, x < N := fun x hx => hS x ((hmem x).mp hx)
  simp only [← hmem]
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, List.length_cons,
      List.length_nil, forall_eq_or_imp, forall_eq, or_false, and_true,
      List.Pairwise.nil] at hp hlen hlt ⊢
  · exact ⟨0, hN, 0, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt, 0, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, 0, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, c, by omega, 0, by omega, by simp⟩
  · exact ⟨a, hlt.1, b, by omega, c, by omega, d, by omega, by simp⟩
  · omega

/-- **Proposition 4.2, upper half.** After deleting any at most four edges (any four
unordered pairs, edges of `G` or not), some set of at most six vertices still dominates. -/
theorem exists_isDominating_deleteEdges (F : Finset (Sym2 (Fin 18))) (hF : F.card ≤ 4) :
    ∃ D : Finset (Fin 18), D.card ≤ 6 ∧
      IsDominating (G.deleteEdges (F : Set (Sym2 (Fin 18)))) D := by
  set S : Finset ℕ := (Finset.range 27).filter (fun i => edgeSym i ∈ F) with hSdef
  have hScard : S.card ≤ 4 := by
    refine le_trans (Finset.card_le_card_of_injOn edgeSym ?_ ?_) hF
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact edgeSym_injOn i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hsub⟩ := exists_desc4 S 27 (by norm_num)
    (fun x hx => Finset.mem_range.mp (Finset.mem_filter.mp hx).1) hScard
  set T : ℕ := 2 ^ a ||| 2 ^ b ||| 2 ^ c ||| 2 ^ d with hT
  have hgood : goodT T = true :=
    (allLT_iff _ _).mp ((allLT_iff _ _).mp ((allLT_iff _ _).mp (inner4_all a ha) b hb) c hc) d hd
  rw [goodT, anyL_iff] at hgood
  obtain ⟨C, hC, hCgood⟩ := hgood
  rw [allL_iff] at hCgood
  obtain ⟨hlenC, hcovC⟩ := certs_sound C hC
  have hcardC : (Finset.univ.filter fun v : Fin 18 => v.val ∈ C.D).card ≤ 6 := by
    calc (Finset.univ.filter fun v : Fin 18 => v.val ∈ C.D).card
        ≤ C.D.toFinset.card := by
          refine Finset.card_le_card_of_injOn Fin.val ?_ Fin.val_injective.injOn
          intro v hv
          simpa using hv
      _ ≤ C.D.length := List.toFinset_card_le _
      _ ≤ 6 := hlenC
  refine ⟨_, hcardC, ?_⟩
  intro v
  rcases hcovC v with hv | ⟨p, hp, hpv, hplt, hbits⟩
  · exact Or.inl (by simp [hv])
  · have hbits' : ∀ i < 27, p.2.testBit i = true →
        ∃ w : Fin 18, w.val ∈ C.D ∧ G.Adj v w ∧ edgeSym i = s(v, w) := by
      intro i hi hbit
      obtain ⟨w, hwD, hw18, hvw | hwv⟩ := hbits i hi hbit
      · exact ⟨⟨w, hw18⟩, hwD, Or.inl (List.mem_of_getElem? hvw),
          edgeSym_of_getElem? hvw v.isLt hw18⟩
      · exact ⟨⟨w, hw18⟩, hwD, Or.inr (List.mem_of_getElem? hwv),
          (edgeSym_of_getElem? hwv hw18 v.isLt).trans Sym2.eq_swap⟩
    have hne : (p.2 &&& T) ≠ p.2 := by
      intro heq
      have h := hCgood p hp
      rw [heq] at h
      simp at h
    obtain ⟨i, hi⟩ : ∃ i, (p.2 &&& T).testBit i ≠ p.2.testBit i := by
      by_contra h
      exact hne (Nat.eq_of_testBit_eq fun j => not_not.mp fun hj => h ⟨j, hj⟩)
    rw [Nat.testBit_land] at hi
    have hpi : p.2.testBit i = true ∧ T.testBit i = false := by
      cases h1 : p.2.testBit i <;> cases h2 : T.testBit i <;> simp_all
    have hi27 : i < 27 := by
      by_contra h
      replace h := not_lt.mp h
      have hfalse := Nat.testBit_lt_two_pow (lt_of_lt_of_le hplt (Nat.pow_le_pow_right (by norm_num) h))
      simp_all
    obtain ⟨w, hwD, hadj, hedge⟩ := hbits' i hi27 hpi.1
    have hiS : i ∉ S := by
      intro hiS
      have hTi : T.testBit i = true := by
        rcases hsub i hiS with rfl | rfl | rfl | rfl <;> simp [hT, Nat.testBit_two_pow]
      simp_all
    have hnotF : s(v, w) ∉ F := by
      rw [← hedge]
      intro hF'
      exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi27, hF'⟩)
    exact Or.inr ⟨w, by simp [hwD], SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hnotF⟩⟩

/-- **Proposition 4.2.** Deleting at most four edges never changes `γ(G) = 6`. -/
theorem domNum_deleteEdges_of_card_le_four (F : Finset (Sym2 (Fin 18))) (hF : F.card ≤ 4) :
    domNum (G.deleteEdges (F : Set (Sym2 (Fin 18)))) = 6 := by
  apply le_antisymm
  · obtain ⟨D, hD6, hD⟩ := exists_isDominating_deleteEdges F hF
    exact (domNum_le_card _ D hD).trans hD6
  · apply le_domNum
    intro D hD
    rw [← domNum_G]
    exact domNum_le_card G D hD.of_deleteEdges

/-! ## The bondage number and the refutation -/

/-- `F₅` consists of five edges of `G`. -/
theorem F5_subset_edgeSet : (F5 : Set (Sym2 (Fin 18))) ⊆ G.edgeSet := by
  intro e he
  simp only [F5, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Theorem 1.1, bondage half.** `b(G) = 5`. -/
theorem bondage_G : bondage G = 5 := by
  have hF5 : 5 ∈ {k | ∃ F : Finset (Sym2 (Fin 18)), (F : Set (Sym2 (Fin 18))) ⊆ G.edgeSet ∧
      F.card = k ∧ domNum G < domNum (G.deleteEdges (F : Set (Sym2 (Fin 18))))} :=
    ⟨F5, F5_subset_edgeSet, by decide, by rw [domNum_G, domNum_deleteEdges_F5]; norm_num⟩
  apply le_antisymm
  · exact Nat.sInf_le hF5
  · refine le_csInf ⟨5, hF5⟩ ?_
    rintro k ⟨F, -, rfl, hlt⟩
    by_contra h
    rw [domNum_deleteEdges_of_card_le_four F (by omega), domNum_G] at hlt
    exact lt_irrefl _ hlt

/-- `G` has exactly the 27 edges of eq. (3.1). -/
theorem card_edgeFinset_G : G.edgeFinset.card = 27 := by decide +kernel

/-- `G` is cubic (Proposition 3.1). -/
theorem degree_G (v : Fin 18) : G.degree v = 3 := by
  revert v
  decide +kernel

/-- `Δ(G) = 3`. -/
theorem maxDegree_G : G.maxDegree = 3 :=
  le_antisymm (G.maxDegree_le_of_forall_degree_le 3 fun v => (degree_G v).le)
    ((degree_G 0).symm.le.trans (G.degree_le_maxDegree 0))

/-- **Theorem 1.1 (arXiv:2609.04257).** The graph `G` of eq. (3.1) has `γ(G) = 6`,
`Δ(G) = 3` and `b(G) = 5 > 9/2 = (3/2)Δ(G)`. -/
theorem thm_1_1 :
    domNum G = 6 ∧ G.maxDegree = 3 ∧ bondage G = 5 ∧ 3 * G.maxDegree < 2 * bondage G := by
  refine ⟨domNum_G, maxDegree_G, bondage_G, ?_⟩
  rw [maxDegree_G, bondage_G]
  norm_num

/-- **Teschner's conjecture is false.** It is not true that every finite simple graph
`H` with at least one edge satisfies `b(H) ≤ (3/2) Δ(H)` (stated as `2 b(H) ≤ 3 Δ(H)`). -/
theorem teschner_conjecture_false :
    ¬ ∀ (V : Type) [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj],
      H.edgeSet.Nonempty → 2 * bondage H ≤ 3 * H.maxDegree := by
  intro h
  have hG := h (Fin 18) G ⟨s(0, 6), by decide⟩
  rw [bondage_G, maxDegree_G] at hG
  norm_num at hG

end CounterexampleTeschnerBondageYavari
