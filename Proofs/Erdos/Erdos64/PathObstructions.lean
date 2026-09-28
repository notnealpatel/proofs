/-
Erdős–Gyárfás problem 64 — the shared-high-neighbour path obstruction.

PROVENANCE. This module records an elementary local cycle-formation mechanism
used in this repository's investigation of Erdős–Gyárfás problem 64: a simple
path together with a single vertex adjacent to both of its endpoints closes up
into a genuine simple cycle. When the path has length `2 ^ k - 2`, the resulting
cycle has length `2 ^ k`, so in a graph without power-of-two cycles the
configuration cannot occur. This is a local observation, not an attribution: no
claim is made that Ducoffe–Dumitru (arXiv:2609.28594) state the generic
formulation below, and no step of that source's argument is cited for it.

FINITENESS. The generic lemmas are stated over an arbitrary vertex type `V` and
assume no finiteness: `exists_isCycle_of_common_neighbor`,
`hasPowerOfTwoCycle_of_common_neighbor` and `false_of_common_neighbor` apply to
any `SimpleGraph V`. Finiteness enters only in the Erdős 64 specialization below,
because the predicates that specialization consumes (`IsCounterexample`, and
`degreeThree` / `degreeGeFour` in `Basic.lean`) carry `[Fintype V]`. All graphs
here are undirected and simple.

SCOPE. Two layers are formalized.

* The generic graph layer makes no reference to the Erdős 64 predicates. If
  `p : G.Walk a b` is a simple path (`p.IsPath`), the endpoints `a`, `b` are
  distinct, a vertex `c` lies outside `p.support`, and `c` is adjacent to both
  `a` and `b`, then adjoining the two `c`-edges to `p` yields a closed walk at
  `c` that `IsCycle` and whose length is `p.length + 2`
  (`exists_isCycle_of_common_neighbor`). The cycle is exhibited explicitly and
  is *proved* to be a cycle via `SimpleGraph.Walk.IsPath.isCycle_append`; nothing
  is assumed. Consequently, if `p.length + 2 = 2 ^ k` with `2 ≤ k`, the graph has
  a power-of-two cycle (`hasPowerOfTwoCycle_of_common_neighbor`), so the
  configuration is impossible under `¬ HasPowerOfTwoCycle G`
  (`false_of_common_neighbor`). Subtraction is avoided: the length input is
  stated as `p.length + 2 = 2 ^ k`.

* The Erdős 64 specialization (`false_of_degreeThree_path_degreeGeFour_common_neighbor`)
  consumes `IsCounterexample G` (or, more precisely, only its no-power-of-two-cycle
  field) and the degree data of this repository's specialization: every vertex of
  `p.support` has degree exactly `3`, and the common neighbour `c` has degree at
  least `4` and is adjacent to both endpoints. The hypothesis
  `∀ v ∈ p.support, degreeThree G v` forces `c ∉ p.support` automatically, since a
  single vertex cannot have degree both `3` and at least `4`; minimality is *not*
  required. This is a local obstruction, not a
  global structural theorem: it excludes one configuration, and no claim is made
  here about the Erdős–Gyárfás conjecture or about the existence of a minimal
  counterexample.
-/

import Erdos.Erdos64.Basic

set_option autoImplicit false

namespace Erdos64

open SimpleGraph

universe u

variable {V : Type u}

/-! ### Generic graph lemma: a path plus a common neighbour closes up -/

/-- **Cycle formation from a common neighbour.** Let `p : G.Walk a b` be a simple path with
distinct endpoints `a ≠ b`, let `c ∉ p.support` be outside the path, and suppose `c` is adjacent
to both endpoints (`G.Adj c a` and `G.Adj c b`). Then the closed walk obtained by adjoining the
two `c`-edges to `p` is a genuine simple cycle at `c` of length `p.length + 2`.

The walk is built explicitly as `(Walk.cons hca p).append (Walk.cons hcb.symm Walk.nil)`; that it
is a cycle is proved from `Walk.IsPath.isCycle_append`, so the non-repetition of vertices is a
conclusion, not a hypothesis. The exponent `k` is carried only through the length equation
`p.length + 2 = 2 ^ k`; no subtraction is used. -/
theorem exists_isCycle_of_common_neighbor {G : SimpleGraph V} {a b c : V} {p : G.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b) (hcp : c ∉ p.support)
    (hca : G.Adj c a) (hcb : G.Adj c b) {k : ℕ} (hlen : p.length + 2 = 2 ^ k) :
    ∃ q : G.Walk c c, q.IsCycle ∧ q.length = 2 ^ k := by
  have hbc : b ≠ c := fun h => hcp (h ▸ p.end_mem_support)
  have hp₁ : (Walk.cons hca p).IsPath := (Walk.cons_isPath_iff hca p).2 ⟨hp, hcp⟩
  have hq₁ : (Walk.cons hcb.symm (Walk.nil : G.Walk c c)).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨Walk.IsPath.nil, by simpa using hbc⟩
  have hdisj : (Walk.cons hca p).support.tail.Disjoint
      (Walk.cons hcb.symm (Walk.nil : G.Walk c c)).support.tail := by
    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons]
    intro x hx hx'
    rw [List.mem_singleton] at hx'
    subst hx'
    exact hcp hx
  have hlong : 1 < (Walk.cons hca p).length ∨
      1 < (Walk.cons hcb.symm (Walk.nil : G.Walk c c)).length := by
    left
    have hpos : 0 < p.length := Nat.pos_of_ne_zero fun hz => hab (Walk.eq_of_length_eq_zero hz)
    rw [Walk.length_cons]
    omega
  have hcyc : ((Walk.cons hca p).append (Walk.cons hcb.symm (Walk.nil : G.Walk c c))).IsCycle :=
    hp₁.isCycle_append hq₁ hdisj hlong
  refine ⟨_, hcyc, ?_⟩
  rw [Walk.length_append, Walk.length_cons, Walk.length_cons, Walk.length_nil]
  omega

/-- **The common-neighbour configuration produces a power-of-two cycle.** Under the hypotheses of
`exists_isCycle_of_common_neighbor`, if additionally `2 ≤ k`, the graph `G` has a power-of-two
cycle: the closed walk constructed there is a simple cycle of length `2 ^ k`, which is exactly
the witness required by `HasPowerOfTwoCycle`. -/
theorem hasPowerOfTwoCycle_of_common_neighbor {G : SimpleGraph V} {a b c : V} {p : G.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b) (hcp : c ∉ p.support)
    (hca : G.Adj c a) (hcb : G.Adj c b) {k : ℕ} (hk : 2 ≤ k)
    (hlen : p.length + 2 = 2 ^ k) : HasPowerOfTwoCycle G := by
  obtain ⟨q, hq, hlen'⟩ := exists_isCycle_of_common_neighbor hp hab hcp hca hcb hlen
  exact ⟨k, hk, c, q, hq, hlen'⟩

/-- **The common-neighbour configuration is impossible without a power-of-two cycle.** If `G` has
no power-of-two cycle, then no simple path `p` with distinct endpoints, a vertex `c` outside
`p.support` adjacent to both endpoints, and `p.length + 2 = 2 ^ k` with `2 ≤ k` can exist. This
is the obstruction form in which the lemma is consumed. -/
theorem false_of_common_neighbor {G : SimpleGraph V} {a b c : V} {p : G.Walk a b}
    (hG : ¬ HasPowerOfTwoCycle G) (hp : p.IsPath) (hab : a ≠ b) (hcp : c ∉ p.support)
    (hca : G.Adj c a) (hcb : G.Adj c b) {k : ℕ} (hk : 2 ≤ k)
    (hlen : p.length + 2 = 2 ^ k) : False :=
  hG (hasPowerOfTwoCycle_of_common_neighbor hp hab hcp hca hcb hk hlen)

/-! ### Erdős 64 specialization -/

/-- **Shared high-degree neighbour of the endpoints of a degree-three path is impossible.** In a
counterexample `G` (`IsCounterexample G`, used only through its no-power-of-two-cycle field),
there is no simple path `p` with distinct endpoints such that every vertex of `p.support` has
degree exactly `3`, together with a vertex `c` of degree at least `4` adjacent to both endpoints
and satisfying `p.length + 2 = 2 ^ k` for some `2 ≤ k`.

The high degree of `c` together with the degree-three hypothesis on the path's vertices forces
`c ∉ p.support`, so the generic obstruction `false_of_common_neighbor` applies. Minimality is not
needed: counterexample status suffices. -/
theorem false_of_degreeThree_path_degreeGeFour_common_neighbor {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] (hG : IsCounterexample G) {a b c : V} {p : G.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b) (hdeg : ∀ v ∈ p.support, degreeThree G v)
    (hc : degreeGeFour G c) (hca : G.Adj c a) (hcb : G.Adj c b) {k : ℕ} (hk : 2 ≤ k)
    (hlen : p.length + 2 = 2 ^ k) : False := by
  have hcp : c ∉ p.support := fun hmem => by
    have h3 : G.degree c = 3 := hdeg c hmem
    have h4 : 4 ≤ G.degree c := hc
    omega
  exact false_of_common_neighbor hG.not_hasPowerOfTwoCycle hp hab hcp hca hcb hk hlen

end Erdos64