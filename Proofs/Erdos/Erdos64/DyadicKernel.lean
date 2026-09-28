/-
Erdős–Gyárfás problem 64 — the nonuniform dyadic-kernel exclusion.

PROVENANCE. arXiv:2609.28594, Theorem 3.8 and its "uniform mechanism" for the
auxiliary graph `M`; the mechanism is made *nonuniform* here, because the
corridors of the subdivision are allowed to have different lengths.  Graphs are
finite, undirected and simple throughout.  `G` is a finite simple graph and
`hmin : Erdos64.IsMinimalCounterexample G` (see `Basic.lean`) is lexicographic
minimality of `(number of vertices, number of edges)` among the
`Erdos64.IsCounterexample`s; `doublingGraph G` is the auxiliary simple graph of
`Doubling.lean` on the high-degree vertex type `↥(degreeGeFourFinset G)`.

SOURCE CLAIM BOUNDARY.  What is proved here is **not** the Erdős–Gyárfás
conjecture and **not** a global strengthening of Theorem 3.8.  It is the
`M`-specific statement that the finite check of Theorem 3.8 survives when the
corridors replacing the edges of a candidate `K` have *arbitrary positive
integer lengths*: the hypothesis that *every* power-of-two-length cycle of `K`
lifts to a power-of-two-length closed walk of `M` is refuted.  The excluded
statement is genuinely stronger than the uniform one: with unequal corridor
lengths a power-of-two cycle of `K` need not lift to a power-of-two closed walk,
and it is exactly this loss of uniformity that is quantified here.

WHAT IS FORMALIZED HERE.

* `SubdivisionCertificate M K` — the smallest honest encoding of "K is a
  subdivision subgraph of M with positive-length corridors".  Its data are an
  injective branch map `K → M`, a corridor walk `M.Walk (branch d.fst)
  (branch d.snd)` for every dart `d` of `K` (with the reversal consistency
  `corridor d.symm = (corridor d).reverse`), and the corridor *interior* as an
  explicit list of vertices with the support equation
  `(corridor d).support = branch d.fst :: (interior d ++ [branch d.snd])`.
  Its conditions are that interiors are listed without repetition, that no
  branch vertex lies in any interior, and that interiors of distinct `K`-edges
  are disjoint.  Positivity of the corridor length is *derived*, not assumed:
  the support equation forces `(corridor d).length = (interior d).length + 1 ≥ 1`.
  Corridors are walks in the simple graph `M`; no multigraph is introduced and
  no parallel edge is silently admitted, since distinct `K`-edges are required
  to have disjoint interiors.

* `SubdivisionCertificate.liftWalk` — the concatenation of the corridors of a
  walk of `K`, built edge by edge, and `SubdivisionCertificate.isCycle_liftWalk`,
  which *proves* (does not assume) that the lift of a simple cycle of `K` is a
  simple cycle of `M` of length equal to the sum of the corridor lengths; the
  proof is the support computation
  `(liftWalk p).support = [branch u] ++ interior ++ … ++ [branch v]` together
  with the disjointness and no-branch-vertex conditions.
  `SubdivisionCertificate.corridorLength_reverse` records that the total
  corridor length is a function of the *undirected* cycle.

* `SubdivisionCertificate.corridorLength_not_powerOfTwo` — the generic
  M-specific extension of Theorem 3.8: if `M` has no power-of-two cycle, then a
  power-of-two-length cycle of `K` has corridor length that is not a power of
  two.

* `exists_powerOfTwoCycle_corridorLength_not_powerOfTwo` and
  `not_forall_corridorLength_powerOfTwo` — the exclusion for
  `M = doublingGraph G` over a minimal counterexample.  Minimality is used only
  where the source uses it, and the numerical input
  `|V(K)| ≤ |H| < |V(G)|` is *derived*: injectivity of the branch map gives
  `|V(K)| ≤ |H|`, and a degree-three vertex (i.e. `L ≠ ∅`) gives `|H| < |V(G)|`.
  The injective branch map also disposes of the degenerate case `H = ∅` — then
  `V(K)` is empty as well — so no case split is needed and no "smaller
  counterexample" property is assumed.

No `sorry`, no `axiom`, no `native_decide`.  Axiom dependencies of every public
result are audited in a separate throwaway module.
-/

import Erdos.Erdos64.Doubling
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {X : Type u} {B : Type u}

/-! ### 1. The subdivision certificate -/

/-- A **subdivision certificate** for a finite simple graph `K` inside a finite
simple graph `M`: `K` is represented as a subdivision subgraph of `M`.

The branch vertices of `K` are mapped injectively into `M` by `branch`.  Every
oriented edge (dart) `d` of `K` is replaced by a *corridor* — a walk of `M` from
`branch d.fst` to `branch d.snd` — whose interior vertices are recorded in the
list `interior d`, in such a way that

* `(corridor d).support = branch d.fst :: (interior d ++ [branch d.snd])`, so the
  corridor consists of its two branch endpoints and its interior, and has
  positive length `(interior d).length + 1`;
* interiors are listed without repetition (`interior_nodup`);
* no branch vertex occurs in an interior (`branch_notMem_interior`);
* interiors of distinct edges of `K` are disjoint (`interior_disjoint`), so
  corridors meet only at branch vertices;
* a corridor and its reverse describe the same undirected corridor
  (`corridor_symm`, `interior_symm`).

Corridors are ordinary walks of the simple graph `M`; in particular the same
edge of `M` may not be used by two different corridors, because such a shared
edge would put a common vertex in both interiors. -/
structure SubdivisionCertificate (M : SimpleGraph X) (K : SimpleGraph B) where
  /-- The branch map sending a vertex of `K` to its subdivision vertex in `M`. -/
  branch : B → X
  /-- Branch vertices are pairwise distinct. -/
  branch_injective : Function.Injective branch
  /-- The corridor replacing an oriented edge of `K`. -/
  corridor : ∀ d : K.Dart, M.Walk (branch d.fst) (branch d.snd)
  /-- Reversing a dart reverses its corridor. -/
  corridor_symm : ∀ d : K.Dart, corridor d.symm = (corridor d).reverse
  /-- The interior vertices of a corridor, in order. -/
  interior : K.Dart → List X
  /-- Reversing a dart reverses its interior. -/
  interior_symm : ∀ d : K.Dart, interior d.symm = (interior d).reverse
  /-- A corridor interior visits no vertex twice. -/
  interior_nodup : ∀ d : K.Dart, (interior d).Nodup
  /-- The corridor visits exactly its two branch endpoints and its interior. -/
  support_corridor : ∀ d : K.Dart,
    (corridor d).support = branch d.fst :: (interior d ++ [branch d.snd])
  /-- No branch vertex is an interior vertex of a corridor. -/
  branch_notMem_interior : ∀ (d : K.Dart) (b : B), branch b ∉ interior d
  /-- Corridors of distinct edges of `K` have disjoint interiors. -/
  interior_disjoint : ∀ d d' : K.Dart, d.edge ≠ d'.edge → (interior d).Disjoint (interior d')

namespace SubdivisionCertificate

variable {M : SimpleGraph X} {K : SimpleGraph B}

/-- The dart of `K` determined by an adjacency proof. -/
abbrev dartOfAdj {u v : B} (h : K.Adj u v) : K.Dart := Dart.mk (u, v) h

/-- A corridor is nonempty: its support contains both endpoints, so its length is
`(interior d).length + 1 ≥ 1`.  Positivity of the corridor length is therefore
derived from the support equation, not assumed. -/
theorem one_le_length_corridor (S : SubdivisionCertificate M K) (d : K.Dart) :
    1 ≤ (S.corridor d).length := by
  have h := Walk.length_support (S.corridor d)
  rw [S.support_corridor d] at h
  simp only [List.length_cons, List.length_append] at h
  omega

/-- A corridor is a simple path of `M`: its support is repetition-free. -/
theorem corridor_isPath (S : SubdivisionCertificate M K) (d : K.Dart) :
    (S.corridor d).IsPath := by
  rw [Walk.isPath_def, S.support_corridor d, List.nodup_cons, List.nodup_append']
  refine ⟨?_, S.interior_nodup d, List.nodup_singleton _, ?_⟩
  · rw [List.mem_append, not_or]
    exact ⟨S.branch_notMem_interior d d.fst, by
      simp only [List.mem_singleton]
      exact fun h => Dart.fst_ne_snd d (S.branch_injective h)⟩
  · intro x hx
    simp only [List.mem_singleton]
    exact fun h => S.branch_notMem_interior d d.snd (h ▸ hx)

/-- The lift of a walk of `K`: each dart is replaced by its corridor, oriented
along the walk. -/
noncomputable def liftWalk (S : SubdivisionCertificate M K) :
    ∀ {u v : B}, K.Walk u v → M.Walk (S.branch u) (S.branch v)
  | _, _, .nil => .nil
  | _, _, .cons h p => (S.corridor (dartOfAdj h)).append (liftWalk S p)

/-- The equation defining `liftWalk` on a single step. -/
theorem liftWalk_cons (S : SubdivisionCertificate M K) {u v w : B} (h : K.Adj u v)
    (p : K.Walk v w) :
    S.liftWalk (.cons h p) = (S.corridor (dartOfAdj h)).append (S.liftWalk p) := rfl

/-- Support of a lifted step: the branch vertex, its corridor interior, and then
the lifted tail. -/
theorem support_liftWalk_cons (S : SubdivisionCertificate M K) {u v w : B} (h : K.Adj u v)
    (p : K.Walk v w) :
    (S.liftWalk (.cons h p)).support =
      (S.branch u :: S.interior (dartOfAdj h)) ++ (S.liftWalk p).support := by
  rw [liftWalk_cons, Walk.support_append, S.support_corridor (dartOfAdj h),
    ← Walk.cons_tail_support (S.liftWalk p)]
  simp only [List.cons_append, List.append_assoc, List.tail_cons, List.nil_append]

/-- **Vertices of a lifted walk.**  Every vertex of `(liftWalk p).support` is
either the branch image of a vertex of `p`, or an interior vertex of the corridor
of one of the darts of `p`. -/
theorem exists_of_mem_support_liftWalk (S : SubdivisionCertificate M K) :
    ∀ {u v : B} (p : K.Walk u v) {x : X}, x ∈ (S.liftWalk p).support →
      (∃ z ∈ p.support, S.branch z = x) ∨ ∃ d ∈ p.darts, x ∈ S.interior d
  | u, _, .nil, x, hx => by
    simp only [liftWalk, Walk.support_nil, List.mem_singleton] at hx
    exact Or.inl ⟨u, by simp, hx.symm⟩
  | u, v, .cons h q, x, hx => by
    rw [support_liftWalk_cons, List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | hx
    · exact Or.inl ⟨u, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · exact Or.inr ⟨dartOfAdj h, by
        rw [Walk.darts_cons]; exact List.mem_cons.mpr (Or.inl rfl), hx⟩
    · rcases exists_of_mem_support_liftWalk S q hx with ⟨z, hz, hbz⟩ | ⟨d, hd, hxm⟩
      · exact Or.inl ⟨z, List.mem_cons.mpr (Or.inr hz), hbz⟩
      · exact Or.inr ⟨d, by
          rw [Walk.darts_cons]; exact List.mem_cons.mpr (Or.inr hd), hxm⟩

/-- **Lifting preserves simplicity.**  The lift of a simple path of `K` has a
repetition-free support, because its branch vertices are distinct, the corridor
interiors are repetition-free and pairwise disjoint, and no interior contains a
branch vertex. -/
theorem nodup_support_liftWalk_of_isPath (S : SubdivisionCertificate M K) :
    ∀ {u v : B} {p : K.Walk u v}, p.IsPath → (S.liftWalk p).support.Nodup
  | _, _, .nil, _ => by simp [liftWalk]
  | u, w, .cons (v := v) h q, hp => by
    obtain ⟨hq, hu⟩ := (Walk.cons_isPath_iff h q).mp hp
    have hedge : s(u, v) ∉ q.edges := by
      have htr := hp.isTrail.edges_nodup
      rw [Walk.edges_cons] at htr
      exact (List.nodup_cons.mp htr).1
    rw [support_liftWalk_cons, List.nodup_append]
    refine ⟨List.nodup_cons.mpr ⟨S.branch_notMem_interior _ u, S.interior_nodup _⟩,
      nodup_support_liftWalk_of_isPath S hq, ?_⟩
    intro x hx y hy hxy
    subst hxy
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rcases S.exists_of_mem_support_liftWalk q hy with ⟨z, hz, hbz⟩ | ⟨d, hd, hxm⟩
      · exact hu (S.branch_injective hbz ▸ hz)
      · exact S.branch_notMem_interior d u hxm
    · rcases S.exists_of_mem_support_liftWalk q hy with ⟨z, hz, hbz⟩ | ⟨d, hd, hxm⟩
      · exact S.branch_notMem_interior (dartOfAdj h) z (hbz ▸ hx)
      · exact S.interior_disjoint (dartOfAdj h) d (by
          intro heq
          exact hedge (by
            rw [← Dart.edge_mk (p := (u, v)) h, heq]
            exact List.mem_map.mpr ⟨d, hd, rfl⟩)) hx hxm

/-- The length of a lifted walk is the sum of the corridor lengths of its darts. -/
theorem length_liftWalk_eq_sum (S : SubdivisionCertificate M K) :
    ∀ {u v : B} (p : K.Walk u v),
      (S.liftWalk p).length = (p.darts.map fun d => (S.corridor d).length).sum
  | _, _, .nil => by simp [liftWalk]
  | _, _, .cons h q => by
    rw [liftWalk_cons, Walk.length_append, length_liftWalk_eq_sum S q, Walk.darts_cons]
    simp only [List.map_cons, List.sum_cons]

/-- A lifted walk is at least as long as the walk it lifts. -/
theorem le_length_liftWalk (S : SubdivisionCertificate M K) :
    ∀ {u v : B} (p : K.Walk u v), p.length ≤ (S.liftWalk p).length
  | _, _, .nil => by simp [liftWalk]
  | _, _, .cons h q => by
    rw [liftWalk_cons, Walk.length_append, Walk.length_cons]
    have h1 := S.one_le_length_corridor (dartOfAdj h)
    have h2 := le_length_liftWalk S q
    omega

/-- **Corridors over a simple cycle concatenate to a simple cycle of the summed
length.**  If `C` is a simple cycle of `K`, then `liftWalk C` is a simple cycle
of `M` whose length is the sum of the corridor lengths of the darts of `C`. -/
theorem isCycle_liftWalk (S : SubdivisionCertificate M K) {u : B} {C : K.Walk u u}
    (hC : C.IsCycle) : (S.liftWalk C).IsCycle := by
  cases C with
  | nil => exact absurd hC Walk.not_isCycle_nil
  | @cons _ v _ h p =>
    obtain ⟨hp, hedge⟩ := (Walk.cons_isCycle_iff p h).mp hC
    have hlen3 : 3 ≤ (Walk.cons h p).length := hC.three_le_length
    have hnotnil : ¬ ((S.corridor (dartOfAdj h)).append (S.liftWalk p)).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.length_append]
      have h1 := S.one_le_length_corridor (dartOfAdj h)
      omega
    refine (Walk.isCycle_iff_isPath_tail_and_le_length).mpr ⟨?_, ?_⟩
    · rw [liftWalk_cons]
      have hsupport :
          (((S.corridor (dartOfAdj h)).append (S.liftWalk p)).support.tail) =
            (S.corridor (dartOfAdj h)).support.tail ++ (S.liftWalk p).support.tail :=
        Walk.tail_support_append _ _
      apply Walk.IsPath.mk'
      rw [Walk.support_tail_of_not_nil _ hnotnil, hsupport]
      apply List.nodup_append.mpr
      refine ⟨?_, ?_, ?_⟩
      · exact (S.corridor_isPath (dartOfAdj h)).support_nodup.tail
      · exact (nodup_support_liftWalk_of_isPath S hp).tail
      · intro x hx y hy hxy
        subst hxy
        have hxb : x ∈ (S.liftWalk p).support := List.mem_of_mem_tail hy
        have hbv : S.branch v ∉ (S.liftWalk p).support.tail := by
          have h := nodup_support_liftWalk_of_isPath S hp
          rw [← Walk.cons_tail_support (S.liftWalk p)] at h
          exact (List.nodup_cons.mp h).1
        have hx' := hx
        rw [S.support_corridor (dartOfAdj h), List.tail_cons] at hx'
        rcases List.mem_append.mp hx' with hxil | hxbv
        · rcases S.exists_of_mem_support_liftWalk p hxb with ⟨z, hz, hbz⟩ | ⟨d, hd, hxm⟩
          · exact S.branch_notMem_interior (dartOfAdj h) z (hbz ▸ hxil)
          · exact S.interior_disjoint (dartOfAdj h) d (by
              intro heq
              exact hedge (by
                rw [← Dart.edge_mk (p := (u, v)) h, heq]
                exact List.mem_map.mpr ⟨d, hd, rfl⟩)) hxil hxm
        · exact hbv (List.mem_singleton.mp hxbv ▸ hy)
    · rw [liftWalk_cons, Walk.length_append]
      have h1 := S.one_le_length_corridor (dartOfAdj h)
      have h2 := le_length_liftWalk S p
      simp only [Walk.length_cons] at hlen3
      omega

/-- The total corridor length of a walk of `K`: the sum of the lengths of the
corridors of its darts, equivalently the length of its lift. -/
noncomputable def corridorLength (S : SubdivisionCertificate M K) {u v : B} (p : K.Walk u v) : ℕ :=
  (S.liftWalk p).length

/-- The total corridor length is a function of the *undirected* cycle: reversing
the traversal does not change it.  This is what makes the notion independent of
the orientation of the corridors. -/
theorem corridorLength_reverse (S : SubdivisionCertificate M K) {u v : B} (p : K.Walk u v) :
    S.corridorLength p.reverse = S.corridorLength p := by
  rw [corridorLength, corridorLength, length_liftWalk_eq_sum S p.reverse,
    length_liftWalk_eq_sum S p, Walk.darts_reverse, List.map_reverse, List.sum_reverse,
    List.map_map]
  refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
  rcases d with ⟨⟨a, b⟩, hab⟩
  have hsymm := congrArg Walk.length (S.corridor_symm (Dart.mk (a, b) hab))
  simpa only [Function.comp_apply, Dart.symm_mk, Walk.length_reverse] using hsymm

/-- The total corridor length of a walk is at least its length. -/
theorem length_le_corridorLength (S : SubdivisionCertificate M K) {u v : B} (p : K.Walk u v) :
    p.length ≤ S.corridorLength p :=
  le_length_liftWalk S p

/-- **Nonuniform dyadic-kernel exclusion (generic form).**  Let `M` be a graph
without a power-of-two cycle, and let `K` be a subdivision subgraph of `M` in the
sense of `SubdivisionCertificate`.  Then no simple cycle of `K` of length a power
of two can have total corridor length a power of two: the corridors of such a
cycle concatenate to a simple cycle of `M` of that length, which `M` does not
have. -/
theorem corridorLength_not_powerOfTwo (S : SubdivisionCertificate M K)
    (hM : ¬ HasPowerOfTwoCycle M) {k : ℕ} (hk : 2 ≤ k) {u : B} {C : K.Walk u u}
    (hC : C.IsCycle) (hlen : C.length = 2 ^ k) (j : ℕ) : S.corridorLength C ≠ 2 ^ j := by
  intro hj
  have hcyc : (S.liftWalk C).IsCycle := S.isCycle_liftWalk hC
  have h4 : 4 ≤ 2 ^ j := by
    have h2 : 2 ^ 2 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := h2
      _ = C.length := hlen.symm
      _ ≤ S.corridorLength C := S.length_le_corridorLength C
      _ = 2 ^ j := hj
  have hj2 : 2 ≤ j := by
    rcases j with _ | _ | j
    · norm_num at h4
    · norm_num at h4
    · omega
  exact hM ⟨j, hj2, S.branch u, S.liftWalk C, hcyc, hj⟩

end SubdivisionCertificate

/-! ### 2. The nonuniform exclusion over a minimal counterexample

Here `M = doublingGraph G` is the auxiliary graph of `Doubling.lean`, which has
no power-of-two cycle by `not_hasPowerOfTwoCycle_doublingGraph`. -/

section Erdos64

variable {V : Type u}

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- There are strictly fewer high-degree vertices than vertices of a minimal
counterexample: `H = {v : d(v) ≥ 4}` is a proper subset.  The properness is the
existence of a degree-three vertex, i.e. `L ≠ ∅`. -/
theorem card_degreeGeFourFinset_lt_card (hmin : IsMinimalCounterexample G) :
    (degreeGeFourFinset G).card < Fintype.card V := by
  rw [← Finset.card_univ]
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩)
  obtain ⟨v, hv⟩ := exists_notMem_degreeGeFourFinset hmin
  intro heq
  exact hv (heq ▸ Finset.mem_univ v)

/-- `L = {v : d(v) = 3}` is nonempty in a minimal counterexample: some vertex has
a neighbour of degree exactly three. -/
theorem degreeThreeFinset_nonempty (hmin : IsMinimalCounterexample G) :
    (degreeThreeFinset G).Nonempty := by
  obtain ⟨v⟩ := hmin.isCounterexample.nonempty
  obtain ⟨w, _, hw⟩ := exists_adjacent_degreeThree hmin v
  exact ⟨w, by simpa using hw⟩

/-- The branch map of a subdivision certificate injects `K` into the high-degree
vertex set, so `|V(K)| ≤ |H|`.  In particular, if `H` is empty then `K` has no
vertices. -/
theorem card_le_card_degreeGeFourFinset {K : SimpleGraph B} [Fintype B]
    (S : SubdivisionCertificate (doublingGraph G) K) :
    Fintype.card B ≤ Fintype.card ↥(degreeGeFourFinset G) :=
  Fintype.card_le_of_injective S.branch S.branch_injective

/-- The numerical input `|V(K)| ≤ |H| < |V(G)|` used by the exclusion, with the
degenerate case `H = ∅` handled by injectivity of the branch map. -/
theorem card_lt_card_of_subdivision {K : SimpleGraph B} [Fintype B]
    (hmin : IsMinimalCounterexample G)
    (S : SubdivisionCertificate (doublingGraph G) K) :
    Fintype.card B < Fintype.card V := by
  refine lt_of_le_of_lt (card_le_card_degreeGeFourFinset S) ?_
  rw [Fintype.card_coe]
  exact card_degreeGeFourFinset_lt_card hmin

/-- **Minimality produces a power-of-two cycle.**  A nonempty graph of minimum
degree at least three that is a subdivision subgraph of the auxiliary graph of a
minimal counterexample must contain a cycle of length a power of two; otherwise
it would be a strictly smaller counterexample, contradicting minimality. -/
theorem exists_pow_cycle_of_subdivision (hmin : IsMinimalCounterexample G)
    {K : SimpleGraph B} [Fintype B] [DecidableEq B] [DecidableRel K.Adj] [Nonempty B]
    (hKdeg : 3 ≤ K.minDegree) (S : SubdivisionCertificate (doublingGraph G) K) :
    HasPowerOfTwoCycle K := by
  by_contra hK
  have hcounter : IsCounterexample K :=
    ⟨inferInstance, fun v => hKdeg.trans (minDegree_le_degree K v), hK⟩
  exact hmin.false_of_size_lexLt K hcounter
    (lexLt_size_of_card_verts_lt K (card_lt_card_of_subdivision hmin S))

/-- **Nonuniform dyadic-kernel exclusion over a minimal counterexample,
existence form.**  A nonempty finite simple graph `K` of minimum degree at least
three that is a subdivision subgraph of the auxiliary graph of a minimal
counterexample `G` has a simple cycle of power-of-two length whose total corridor
length is not a power of two. -/
theorem exists_powerOfTwoCycle_corridorLength_not_powerOfTwo
    (hmin : IsMinimalCounterexample G) {K : SimpleGraph B} [Fintype B] [DecidableEq B]
    [DecidableRel K.Adj]
    [Nonempty B] (hKdeg : 3 ≤ K.minDegree)
    (S : SubdivisionCertificate (doublingGraph G) K) :
    ∃ (k : ℕ) (_ : 2 ≤ k) (u : B) (C : K.Walk u u),
      C.IsCycle ∧ C.length = 2 ^ k ∧ ∀ j : ℕ, S.corridorLength C ≠ 2 ^ j := by
  obtain ⟨k, hk, u, C, hC, hlen⟩ := exists_pow_cycle_of_subdivision hmin hKdeg S
  by_cases hex : ∃ j : ℕ, S.corridorLength C = 2 ^ j
  · obtain ⟨j, hj⟩ := hex
    exact absurd hj (S.corridorLength_not_powerOfTwo
      (not_hasPowerOfTwoCycle_doublingGraph hmin.not_hasPowerOfTwoCycle) hk hC hlen j)
  · exact ⟨k, hk, u, C, hC, hlen, fun j hj => hex ⟨j, hj⟩⟩

/-- **Nonuniform dyadic-kernel exclusion over a minimal counterexample,
impossibility form.**  It is impossible that *every* simple cycle of `K` of
power-of-two length should have total corridor length a power of two. -/
theorem not_forall_corridorLength_powerOfTwo (hmin : IsMinimalCounterexample G)
    {K : SimpleGraph B} [Fintype B] [DecidableEq B] [DecidableRel K.Adj] [Nonempty B]
    (hKdeg : 3 ≤ K.minDegree) (S : SubdivisionCertificate (doublingGraph G) K) :
    ¬ ∀ (k : ℕ), 2 ≤ k → ∀ (u : B) (C : K.Walk u u),
        C.IsCycle → C.length = 2 ^ k → ∃ j : ℕ, S.corridorLength C = 2 ^ j := by
  intro h
  obtain ⟨k, hk, u, C, hC, hlen, hne⟩ :=
    exists_powerOfTwoCycle_corridorLength_not_powerOfTwo hmin hKdeg S
  obtain ⟨j, hj⟩ := h k hk u C hC hlen
  exact hne j hj

end Erdos64

end Erdos64