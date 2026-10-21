/-
  Counterexample to the Bougard-Joret Conjecture.
  Source: arXiv:2608.18828, Joyentanuj Das and Sayan Gupta,
  "Counterexample to the Bougard--Joret Conjecture".  The refuted
  conjecture is eq. (conjecture) of the introduction (= Bougard and
  Joret 2008, Conjecture 1 in Section 6; also Liu-Ning Conj. 3.1).
  The refutation is Theorem thm:boundary (Section 3, case
  alpha = k - 1) and Proposition prop:smallest (Section 4).
  Recorded 2026-10-21.

  Definitions, verbatim from the paper (Section 2):

    "A graph is k-connected if it has more than k vertices and
     deleting any set of fewer than k vertices leaves a connected
     graph."
    "let f(n,alpha,k) denote the minimum size of a k-connected graph
     of order n and independence number alpha."

  Conjecture (Bougard-Joret), for n >= 2 alpha, n >= alpha + k,
  alpha >= 2, k >= 3:

    "f(n,alpha,k) = ceil(nk/2)  when n <= k alpha,
     f(n,alpha,k) = t(n,alpha) + ceil(k alpha/2)  when n > k alpha."

  Paper's claim (abstract / Theorem thm:boundary), verbatim:

    "In particular, for every k >= 4, f(2k-1,k-1,k) = k^2-1, whereas
     the conjectured value is k^2 - floor(k/2)."
    "The smallest-order failure has parameters (n,alpha,k) = (7,3,4)"
    "f(7,3,4)=15, while (conjecture) predicts 14."

  Status in the paper: proved (elementary).  This module proves the
  refutation of the first regime completely:
  * `card_edgeFinset_lower`: every k-connected graph on 2k-1
    vertices with independence number k-1 has at least k^2-1 edges
    (the general boundary bound `boundary_lower`:
    alpha k + (k - 1) <= e(G) when n = alpha + k and alpha < k);
  * `isLeast_edgeCounts`: the bound is attained, so
    f(2k-1,k-1,k) = k^2-1 for k >= 2.  The witness is
    K_1 join K_{k-1,k-1}, i.e. the paper's extremal family
    complement-of-K_{k-1} join T with T the star of order k;
  * `ceil_lt`: ceil((2k-1)k/2) < k^2-1 for k >= 4;
  * `not_bougardJoretFirstRegime`: the first regime of the
    conjecture is false (instance (7,3,4)), and
    `bougardJoret_counterexample` gives the failure for every k >= 4.
  No `sorry`.  Mathlib has no vertex-connectivity predicate, so
  `IsKConnected` transcribes the paper's definition.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.BougardJoretCounterexample


variable {V : Type*}

/-- The paper's `k`-connectivity (Section 2): `G` has more than `k` vertices
and deleting any set `X` of fewer than `k` vertices leaves a connected graph
(the subgraph induced on the complement of `X`). -/
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

/-- Step (1) of Theorem thm:boundary: if `S` is independent and
`|V| = |S| + k` in a `k`-connected graph, then every vertex of `S` is adjacent
to every vertex outside `S`.  (Otherwise deleting the fewer than `k`
neighbours of `s` isolates `s` from `t`.) -/
theorem adj_of_mem_of_not_mem [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hc : IsKConnected G k) {S : Finset V} (hS : G.IsIndepSet S)
    (hcard : Fintype.card V = S.card + k) {s t : V} (hs : s ∈ S) (ht : t ∉ S) :
    G.Adj s t := by
  by_contra hst
  set X := G.neighborFinset s with hX
  have hXsub : X ⊆ (Sᶜ).erase t := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    rw [Finset.mem_erase, Finset.mem_compl]
    refine ⟨fun hxt => hst (hxt ▸ hx), fun hxS => ?_⟩
    exact hS hs hxS (G.ne_of_adj hx) hx
  have hXcard : X.card < k := by
    have h1 := Finset.card_le_card hXsub
    rw [Finset.card_erase_of_mem (Finset.mem_compl.mpr ht), Finset.card_compl] at h1
    have hk : 0 < k := by
      have := Finset.card_pos.mpr ⟨t, Finset.mem_compl.mpr ht⟩
      rw [Finset.card_compl] at this
      omega
    omega
  have hconn := hc.2 X hXcard
  have hsX : s ∈ ((X : Set V)ᶜ) := by
    simp [hX]
  have htX : t ∈ ((X : Set V)ᶜ) := by
    simp [hX, hst]
  have hne : (⟨s, hsX⟩ : ↥((X : Set V)ᶜ)) ≠ ⟨t, htX⟩ := by
    intro h
    exact ht (Subtype.mk.inj h ▸ hs)
  obtain ⟨p⟩ := hconn.preconnected ⟨s, hsX⟩ ⟨t, htX⟩
  obtain ⟨w, hw, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
  have hadj : G.Adj s w.1 := hw
  exact w.2 (by simpa [hX] using hadj)


/-- Edge decomposition: if every vertex of `S` is adjacent to every vertex
outside `S`, then `G` has at least `|S| (|V| - |S|)` cross edges plus the edges
of the subgraph induced on the complement of `S`. -/
theorem card_mul_add_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hadj : ∀ s ∈ S, ∀ t ∉ S, G.Adj s t) :
    S.card * (Fintype.card V - S.card) + Nat.card (G.induce ((S : Set V)ᶜ)).edgeSet
      ≤ #G.edgeFinset := by
  let T : Set V := (S : Set V)ᶜ
  let f : (↥(S : Set V) × ↥T) ⊕ (G.induce T).edgeSet → G.edgeSet := fun x =>
    match x with
    | Sum.inl p => ⟨s(p.1.1, p.2.1), hadj p.1.1 p.1.2 p.2.1 p.2.2⟩
    | Sum.inr e => (SimpleGraph.Embedding.induce T).mapEdgeSet e
  have hmemT : ∀ (e : (G.induce T).edgeSet) (v : V),
      v ∈ ((SimpleGraph.Embedding.induce T).mapEdgeSet e : Sym2 V) → v ∈ T := by
    intro e v hv
    simp only [SimpleGraph.Embedding.mapEdgeSet, Function.Embedding.coeFn_mk,
      SimpleGraph.Hom.mapEdgeSet_coe, Sym2.mem_map] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact x.2
  have hinj : Function.Injective f := by
    rintro (⟨a, b⟩ | e) (⟨a', b'⟩ | e') h
    · have h' : s(a.1, b.1) = s(a'.1, b'.1) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Subtype.ext h1, Subtype.ext h2]
      · exact absurd (h1 ▸ b'.2) (not_not.mpr a.2)
    · have h' : s(a.1, b.1) = ((SimpleGraph.Embedding.induce T).mapEdgeSet e' : Sym2 V) :=
        congrArg Subtype.val h
      exact absurd (hmemT e' a.1 (h' ▸ Sym2.mem_mk_left _ _)) (not_not.mpr a.2)
    · have h' : s(a'.1, b'.1) = ((SimpleGraph.Embedding.induce T).mapEdgeSet e : Sym2 V) :=
        (congrArg Subtype.val h).symm
      exact absurd (hmemT e a'.1 (h' ▸ Sym2.mem_mk_left _ _)) (not_not.mpr a'.2)
    · exact congrArg Sum.inr ((SimpleGraph.Embedding.induce T).mapEdgeSet.injective h)
  have hle := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := G.edgeSet),
    ← SimpleGraph.edgeFinset_card] at hle
  have hS : Nat.card ↥(S : Set V) = S.card := by simp
  have hT : Nat.card ↥T = Fintype.card V - S.card := by
    simp only [T]
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp
  rw [hS, hT] at hle
  exact hle


/-- The complement of a finset, as a type, has `|V| - |S|` elements. -/
theorem natCard_compl_coe [Fintype V] [DecidableEq V] (S : Finset V) :
    Nat.card ↥((S : Set V)ᶜ) = Fintype.card V - S.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  simp

/-- Lower bound of Theorem thm:boundary on the boundary `n = alpha + k` with
`alpha < k` (that is, `d = k - alpha >= 1`): a `k`-connected graph of order
`alpha + k` with independence number `alpha` has at least
`alpha k + (k - 1)` edges. -/
theorem boundary_lower [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α k : ℕ} (hV : Fintype.card V = α + k) (hα : G.indepNum = α) (hαk : α < k)
    (hc : IsKConnected G k) : α * k + (k - 1) ≤ #G.edgeFinset := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  rw [hα] at hS
  have hcard : Fintype.card V = S.card + k := by rw [hS.card_eq, hV]
  have hadj : ∀ s ∈ S, ∀ t ∉ S, G.Adj s t := fun s hs t ht =>
    adj_of_mem_of_not_mem G hc hS.isIndepSet hcard hs ht
  have hcount := card_mul_add_le G S hadj
  have hconn : (G.induce ((S : Set V)ᶜ)).Connected := hc.2 S (hS.card_eq ▸ hαk)
  have htree := hconn.card_vert_le_card_edgeSet_add_one
  rw [natCard_compl_coe] at htree
  rw [hS.card_eq] at hcount htree
  have hk : Fintype.card V - α = k := by omega
  rw [hk] at hcount htree
  omega

/-- **Bougard-Joret counterexample, lower bound** (arXiv:2608.18828,
Theorem thm:boundary with `alpha = k - 1`): every `k`-connected graph on
`2k - 1` vertices with independence number `k - 1` has at least `k^2 - 1`
edges.  The order and independence hypotheses are written subtraction-free as
`|V| + 1 = 2k` and `indepNum + 1 = k`. -/
theorem card_edgeFinset_lower (k : ℕ) (hk : 1 ≤ k) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V + 1 = 2 * k) (hα : G.indepNum + 1 = k) (hc : IsKConnected G k) :
    k ^ 2 - 1 ≤ #G.edgeFinset := by
  have h := boundary_lower G (α := k - 1) (k := k) (by omega) (by omega) (by omega) hc
  have : (k - 1) * k + (k - 1) = k ^ 2 - 1 := by
    cases k with
    | zero => omega
    | succ n =>
      rw [Nat.add_sub_cancel, eq_comm, Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (Nat.succ_pos n))]
      rw [Nat.succ_eq_add_one]
      ring
  omega


/-- The set of edge counts of `k`-connected graphs of order `n` with
independence number `alpha`; the paper's `f(n, alpha, k)` is its least
element, so `f(n, alpha, k) = m` is `IsLeast (edgeCounts n alpha k) m`. -/
def edgeCounts (n α k : ℕ) : Set ℕ :=
  {m | ∃ G : SimpleGraph (Fin n), IsKConnected G k ∧ G.indepNum = α ∧ Nat.card G.edgeSet = m}

/-- The first regime of the Bougard-Joret conjecture (eq. (conjecture) of
arXiv:2608.18828, Conjecture 1 of Bougard-Joret 2008): for `n >= 2 alpha`,
`n >= alpha + k`, `alpha >= 2`, `k >= 3` and `n <= k alpha`, the minimum
`f(n, alpha, k)` exists and equals `ceil(nk/2) = (nk + 1) / 2`. -/
def BougardJoretFirstRegime : Prop :=
  ∀ n α k : ℕ, 2 * α ≤ n → α + k ≤ n → 2 ≤ α → 3 ≤ k → n ≤ k * α →
    IsLeast (edgeCounts n α k) ((n * k + 1) / 2)

/-- The conjectured value: `ceil((2k-1)k/2) = k^2 - floor(k/2)`. -/
theorem ceil_eq (k : ℕ) : ((2 * k - 1) * k + 1) / 2 = k ^ 2 - k / 2 := by
  have h : (2 * k - 1) * k = 2 * (k * k) - k := by
    rw [Nat.sub_mul, one_mul, mul_assoc]
  rw [h, pow_two]
  have : k ≤ k * k := Nat.le_mul_self k
  omega

/-- For `k >= 4` the conjectured value `ceil((2k-1)k/2)` is strictly below
`k^2 - 1`. -/
theorem ceil_lt (k : ℕ) (hk : 4 ≤ k) : ((2 * k - 1) * k + 1) / 2 < k ^ 2 - 1 := by
  rw [ceil_eq k, pow_two]
  have : 4 * k ≤ k * k := Nat.mul_le_mul_right k hk
  omega

/-- Every edge count of an admissible graph at `(2k-1, k-1, k)` is at least
`k^2 - 1`. -/
theorem le_of_mem_edgeCounts {k m : ℕ} (hk : 1 ≤ k) (hm : m ∈ edgeCounts (2 * k - 1) (k - 1) k) :
    k ^ 2 - 1 ≤ m := by
  classical
  obtain ⟨G, hc, hα, rfl⟩ := hm
  have h := card_edgeFinset_lower k hk G (by rw [Fintype.card_fin]; omega) (by omega) hc
  rwa [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]

/-- For `k >= 4`, `ceil((2k-1)k/2)` is not the minimum edge count at
`(2k-1, k-1, k)`. -/
theorem not_isLeast (k : ℕ) (hk : 4 ≤ k) :
    ¬ IsLeast (edgeCounts (2 * k - 1) (k - 1) k) (((2 * k - 1) * k + 1) / 2) := by
  intro h
  have h1 := le_of_mem_edgeCounts (by omega) h.1
  have h2 := ceil_lt k hk
  omega

/-- **The first regime of the Bougard-Joret conjecture is false**
(arXiv:2608.18828), refuted at `(n, alpha, k) = (7, 3, 4)`. -/
theorem not_bougardJoretFirstRegime : ¬ BougardJoretFirstRegime := by
  intro h
  exact not_isLeast 4 le_rfl
    (h 7 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))


/-- The extremal witness on `Fin n`: vertex `0` is adjacent to every other
vertex, and two nonzero vertices are adjacent iff their parities differ.  For
`n = 2k - 1` this is `K_1 join K_{k-1,k-1}`, i.e. the paper's
`complement(K_{k-1}) join T` with `T` the star of order `k` (odd vertices form
the independent `K_{k-1}` complement, `0` and the even vertices form `T`). -/
def witness (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (i.val = 0 ∨ j.val = 0 ∨ i.val % 2 ≠ j.val % 2)
  symm := ⟨fun i j h => ⟨h.1.symm, by omega⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Adjacency in `witness n` is decidable. -/
instance (n : ℕ) : DecidableRel (witness n).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i.val = 0 ∨ j.val = 0 ∨ i.val % 2 ≠ j.val % 2)))

example : (witness 7).Adj 0 5 := by decide
example : (witness 7).Adj 1 2 := by decide
example : ¬ (witness 7).Adj 1 3 := by decide
example : ¬ (witness 7).Adj 2 4 := by decide
example : #(witness 7).edgeFinset = 15 := by decide

/-- The `j`-th vertex `2j + 1 + b` of the side of parity `b`: odd vertices for
`b = 0`, nonzero even vertices for `b = 1`. -/
def side (k b : ℕ) (hb : b < 2) : Fin (k - 1) → Fin (2 * k - 1) := fun j =>
  ⟨2 * j.val + 1 + b, by have := j.2; omega⟩

/-- `side` is injective. -/
theorem side_injective (k b : ℕ) (hb : b < 2) : Function.Injective (side k b hb) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [side] at this
  exact Fin.ext (by omega)

/-- The image of `side k b` is the set of nonzero vertices of parity
`(b + 1) % 2`. -/
theorem mem_side_iff (k b : ℕ) (hb : b < 2) (i : Fin (2 * k - 1)) :
    i ∈ Finset.univ.image (side k b hb) ↔ i.val ≠ 0 ∧ i.val % 2 = (b + 1) % 2 := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, -, rfl⟩
    simp only [side]
    omega
  · rintro ⟨h0, h2⟩
    refine ⟨⟨(i.val - 1) / 2, by have := i.2; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
    simp only [side]
    omega

/-- Each side has `k - 1` vertices. -/
theorem card_side (k b : ℕ) (hb : b < 2) :
    #(Finset.univ.image (side k b hb)) = k - 1 := by
  rw [Finset.card_image_of_injective _ (side_injective k b hb), Finset.card_univ, Fintype.card_fin]


/-- Unfolding adjacency of the witness. -/
theorem witness_adj_iff {n : ℕ} (i j : Fin n) :
    (witness n).Adj i j ↔ i ≠ j ∧ (i.val = 0 ∨ j.val = 0 ∨ i.val % 2 ≠ j.val % 2) := Iff.rfl

/-- The witness on `2k - 1` vertices has independence number `k - 1`. -/
theorem witness_indepNum (k : ℕ) (hk : 2 ≤ k) : (witness (2 * k - 1)).indepNum = k - 1 := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := (witness (2 * k - 1)).exists_isNIndepSet_indepNum
    rw [← hS.card_eq]
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hpair : ∀ y ∈ S, y ≠ x → ¬ (witness (2 * k - 1)).Adj x y := fun y hy hne =>
      hS.isIndepSet hx hy (Ne.symm hne)
    by_cases hx0 : x.val = 0
    · have hsub : S ⊆ {x} := by
        intro y hy
        rw [Finset.mem_singleton]
        by_contra hne
        exact hpair y hy hne ⟨Ne.symm hne, Or.inl hx0⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    · have hb : (x.val + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hsub : S ⊆ Finset.univ.image (side k ((x.val + 1) % 2) hb) := by
        intro y hy
        rw [mem_side_iff]
        by_cases hne : y = x
        · subst hne
          omega
        · have h := hpair y hy hne
          rw [witness_adj_iff] at h
          omega
      have := Finset.card_le_card hsub
      rwa [card_side] at this
  · have hind : (witness (2 * k - 1)).IsIndepSet
        (Finset.univ.image (side k 0 (by norm_num)) : Set (Fin (2 * k - 1))) := by
      intro i hi j hj hne hadj
      rw [Finset.mem_coe, mem_side_iff] at hi hj
      rw [witness_adj_iff] at hadj
      omega
    have := hind.card_le_indepNum
    rwa [card_side] at this


/-- A nonzero vertex of the witness has degree at most `k`. -/
theorem witness_degree_le (k : ℕ) (i : Fin (2 * k - 1)) (hi : i.val ≠ 0) :
    (witness (2 * k - 1)).degree i ≤ k := by
  have hb : i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hpos : 0 < 2 * k - 1 := by have := i.2; omega
  have hsub : (witness (2 * k - 1)).neighborFinset i ⊆
      insert ⟨0, hpos⟩ (Finset.univ.image (side k (i.val % 2) hb)) := by
    intro j hj
    rw [SimpleGraph.mem_neighborFinset, witness_adj_iff] at hj
    rw [Finset.mem_insert, mem_side_iff]
    by_cases hj0 : j.val = 0
    · exact Or.inl (Fin.ext hj0)
    · right
      omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc #((witness (2 * k - 1)).neighborFinset i)
      ≤ #(insert ⟨0, hpos⟩ (Finset.univ.image (side k (i.val % 2) hb))) :=
        Finset.card_le_card hsub
    _ ≤ #(Finset.univ.image (side k (i.val % 2) hb)) + 1 := Finset.card_insert_le _ _
    _ = k := by rw [card_side]; have := i.2; omega

/-- Arithmetic step of the handshake bound for the witness. -/
theorem edge_arith (k D R E : ℕ) (hk : 2 ≤ k) (hsum : D + R = 2 * E) (h0 : D ≤ 2 * k - 2)
    (hr : R ≤ (2 * k - 1 - 1) * k) : E ≤ k ^ 2 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
  have e1 : 2 * (t + 2) - 1 - 1 = 2 * (t + 1) := by omega
  have e2 : 2 * (t + 2) - 2 = 2 * (t + 1) := by omega
  have e3 : (t + 2) ^ 2 - 1 = (t + 1) * (t + 3) := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  rw [e1] at hr
  rw [e2] at h0
  rw [e3]
  nlinarith

/-- The witness on `2k - 1` vertices has at most `k^2 - 1` edges. -/
theorem witness_card_edgeFinset_le (k : ℕ) (hk : 2 ≤ k) :
    #(witness (2 * k - 1)).edgeFinset ≤ k ^ 2 - 1 := by
  have hpos : 0 < 2 * k - 1 := by omega
  let z : Fin (2 * k - 1) := ⟨0, hpos⟩
  have hsum := (witness (2 * k - 1)).sum_degrees_eq_twice_card_edges
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)] at hsum
  have h0 : (witness (2 * k - 1)).degree z ≤ 2 * k - 2 := by
    have := (witness (2 * k - 1)).degree_lt_card_verts z
    rw [Fintype.card_fin] at this
    omega
  have hrest := Finset.sum_le_card_nsmul (Finset.univ.erase z)
    (fun v => (witness (2 * k - 1)).degree v) k (fun v hv =>
      witness_degree_le k v (fun h => (Finset.mem_erase.mp hv).1 (Fin.ext h)))
  rw [smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
    Fintype.card_fin] at hrest
  exact edge_arith k _ _ _ hk hsum h0 hrest


/-- A set of fewer than `k` vertices containing `0` misses a vertex of each
side. -/
theorem exists_side_not_mem (k b : ℕ) (hb : b < 2) (X : Finset (Fin (2 * k - 1)))
    (hX : #X < k) (hpos : 0 < 2 * k - 1) (h0 : (⟨0, hpos⟩ : Fin (2 * k - 1)) ∈ X) :
    ∃ a ∈ Finset.univ.image (side k b hb), a ∉ X := by
  by_contra hcon
  push Not at hcon
  have hsub : insert ⟨0, hpos⟩ (Finset.univ.image (side k b hb)) ⊆ X :=
    Finset.insert_subset h0 hcon
  have hnot : (⟨0, hpos⟩ : Fin (2 * k - 1)) ∉ Finset.univ.image (side k b hb) := by
    rw [mem_side_iff]
    exact fun h => h.1 rfl
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, card_side] at this
  omega

/-- The witness on `2k - 1` vertices is `k`-connected. -/
theorem witness_isKConnected (k : ℕ) (hk : 2 ≤ k) : IsKConnected (witness (2 * k - 1)) k := by
  refine ⟨by rw [Fintype.card_fin]; omega, fun X hX => ?_⟩
  have hpos : 0 < 2 * k - 1 := by omega
  let z : Fin (2 * k - 1) := ⟨0, hpos⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  by_cases hz : z ∈ X
  · obtain ⟨a, haS, haX⟩ := exists_side_not_mem k 0 (by norm_num) X hX hpos hz
    obtain ⟨b, hbS, hbX⟩ := exists_side_not_mem k 1 (by norm_num) X hX hpos hz
    rw [mem_side_iff] at haS hbS
    have hab :
        (witness (2 * k - 1)).induce ((X : Set (Fin (2 * k - 1)))ᶜ) |>.Adj ⟨a, haX⟩ ⟨b, hbX⟩ :=
      show (witness (2 * k - 1)).Adj a b from ⟨fun h => by subst h; omega, by omega⟩
    refine ⟨⟨a, haX⟩, fun w => ?_⟩
    have hw0 : w.1.val ≠ 0 := fun h => w.2 (show w.1 ∈ X from (Fin.ext h : w.1 = z) ▸ hz)
    by_cases hwa : w = ⟨a, haX⟩
    · rw [hwa]
    by_cases hpar : w.1.val % 2 = 1
    · have hbw : (witness (2 * k - 1)).induce ((X : Set (Fin (2 * k - 1)))ᶜ) |>.Adj ⟨b, hbX⟩ w :=
        show (witness (2 * k - 1)).Adj b w.1 from ⟨fun h => by rw [← h] at hpar; omega, by omega⟩
      exact hab.reachable.trans hbw.reachable
    · have haw : (witness (2 * k - 1)).induce ((X : Set (Fin (2 * k - 1)))ᶜ) |>.Adj ⟨a, haX⟩ w :=
        show (witness (2 * k - 1)).Adj a w.1 from ⟨fun h => by rw [← h] at hpar; omega, by omega⟩
      exact haw.reachable
  · refine ⟨⟨z, hz⟩, fun w => ?_⟩
    by_cases hwz : w = ⟨z, hz⟩
    · rw [hwz]
    · have hzw : (witness (2 * k - 1)).induce ((X : Set (Fin (2 * k - 1)))ᶜ) |>.Adj ⟨z, hz⟩ w :=
        show (witness (2 * k - 1)).Adj z w.1 from
          ⟨fun h => hwz (Subtype.ext h.symm), Or.inl rfl⟩
      exact hzw.reachable


/-- **Exact value** (arXiv:2608.18828, Theorem thm:boundary,
`alpha = k - 1`): `f(2k-1, k-1, k) = k^2 - 1` for `k >= 2`. -/
theorem isLeast_edgeCounts (k : ℕ) (hk : 2 ≤ k) :
    IsLeast (edgeCounts (2 * k - 1) (k - 1) k) (k ^ 2 - 1) := by
  refine ⟨⟨witness (2 * k - 1), witness_isKConnected k hk, witness_indepNum k hk, ?_⟩,
    fun m hm => le_of_mem_edgeCounts (by omega) hm⟩
  have hlow := card_edgeFinset_lower k (by omega) (witness (2 * k - 1))
    (by rw [Fintype.card_fin]; omega)
    (by rw [witness_indepNum k hk]; omega) (witness_isKConnected k hk)
  have hup := witness_card_edgeFinset_le k hk
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

/-- **Smallest failure** (arXiv:2608.18828, Proposition prop:smallest):
`f(7, 3, 4) = 15`, while the conjectured value `ceil(7 * 4 / 2)` is `14`. -/
theorem isLeast_edgeCounts_seven : IsLeast (edgeCounts 7 3 4) 15 ∧ (7 * 4 + 1) / 2 = 14 :=
  ⟨isLeast_edgeCounts 4 (by norm_num), by norm_num⟩

/-- **Counterexample to the Bougard-Joret conjecture** (arXiv:2608.18828):
for every `k >= 4`, the triple `(n, alpha, k) = (2k-1, k-1, k)` is admissible and
in the first regime (`2 alpha <= n`, `alpha + k <= n`, `2 <= alpha`, `3 <= k`,
`n <= k alpha`), `f(2k-1, k-1, k) = k^2 - 1`, and the conjectured value
`ceil((2k-1)k/2)` is strictly smaller. -/
theorem bougardJoret_counterexample (k : ℕ) (hk : 4 ≤ k) :
    2 * (k - 1) ≤ 2 * k - 1 ∧ (k - 1) + k ≤ 2 * k - 1 ∧ 2 ≤ k - 1 ∧ 3 ≤ k ∧
      2 * k - 1 ≤ k * (k - 1) ∧
      IsLeast (edgeCounts (2 * k - 1) (k - 1) k) (k ^ 2 - 1) ∧
      ((2 * k - 1) * k + 1) / 2 < k ^ 2 - 1 := by
  have hreg : 2 * k - 1 ≤ k * (k - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 4 := ⟨k - 4, by omega⟩
    have e : (t + 4) * (t + 4 - 1) = (t + 4) * (t + 3) := by rfl
    have e2 : 2 * (t + 4) - 1 = 2 * t + 7 := by omega
    rw [e, e2]
    nlinarith
  exact ⟨by omega, by omega, by omega, by omega, hreg, isLeast_edgeCounts k (by omega),
    ceil_lt k hk⟩

/-- Satisfiability of the hypotheses of `card_edgeFinset_lower` at `k = 4`. -/
example : 15 ≤ #(witness 7).edgeFinset :=
  card_edgeFinset_lower 4 (by norm_num) (witness 7) (by rw [Fintype.card_fin])
    (by rw [witness_indepNum 4 (by norm_num)]) (witness_isKConnected 4 (by norm_num))

end Candidates.BougardJoretCounterexample
