import Erdos.Erdos64.Basic
import Erdos.Erdos64.BipartiteRepair

/-!
# Proper bipartite regions in a vertex-minimal E64 counterexample

This is a conditional exclusion, not a proof of E64 or of counterexample existence.
The explicit `hminimal` hypothesis covers all finite nonempty vertex types in the
ambient universe, including the actual vertex type produced by full bipartite repair.
The existing lexicographically minimal counterexample interface also supplies it.

All cycle witnesses are genuine `Walk.IsCycle` witnesses. The existing dyadic
predicate uses exponents at least two; `hasPowerOfTwoCycle_iff_one_le` verifies
its equivalence to the exponent-at-least-one contract. No connectivity, cubicity,
or lower degree bound on the region is assumed: its exceptional vertices may have
degree zero or one. This excludes regions only when supplied; it does not force
such a region to exist. Density and cut-root reductions remain outside this result.
-/

set_option autoImplicit false
universe u

namespace Erdos64.BipartiteRegionExclusion

open SimpleGraph
open scoped Classical

/-- The standard E64 predicate is equivalent to a genuine dyadic cycle with exponent
at least one: a simple graph has no genuine cycle of length two (or one). -/
theorem hasPowerOfTwoCycle_iff_one_le {V : Type u} (G : SimpleGraph V) :
    HasPowerOfTwoCycle G ↔
      ∃ k : ℕ, 1 ≤ k ∧ ∃ x, ∃ w : G.Walk x x, w.IsCycle ∧ w.length = 2 ^ k := by
  constructor
  · rintro ⟨k, hk, x, w, hw, hlen⟩
    exact ⟨k, by omega, x, w, hw, hlen⟩
  · rintro ⟨k, _, x, w, hw, hlen⟩
    exact (hasPowerOfTwoCycle_iff_exists_pow G).mpr ⟨k, x, w, hw, hlen⟩

/-- A globally vertex-minimal counterexample cannot contain a proper induced region
with a proper Bool coloring, at most two vertices of ordinary degree at most two,
and a vertex of ordinary degree at least three. `hminimal` is an explicit conditional
hypothesis, not the conjecture: it applies only to graphs of strictly smaller order.
It quantifies over `Type u`, so it covers the repair witness's vertex universe.
The region's C4-freeness is derived from the ambient dyadic-cycle exclusion. -/
theorem proper_induced_region_excluded {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hCE : IsCounterexample G)
    (hminimal : ∀ (W : Type u) [Fintype W] [Nonempty W] (Q : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ v, 3 ≤ Q.degree v) → HasPowerOfTwoCycle Q)
    (s : Finset V) (hproper : s.card < Fintype.card V)
    (c : ↥(s : Set V) → Bool)
    (hc : ∀ ⦃x y⦄, (G.induce (s : Set V)).Adj x y → c x ≠ c y)
    (hlow : (Finset.univ.filter (fun v : ↥(s : Set V) =>
      (G.induce (s : Set V)).degree v ≤ 2)).card ≤ 2)
    (hhigh : ∃ v : ↥(s : Set V), 3 ≤ (G.induce (s : Set V)).degree v) : False := by
  classical
  let B := G.induce (s : Set V)
  have hC4 : ¬ ∃ x, ∃ w : B.Walk x x, w.IsCycle ∧ w.length = 4 := by
    intro hcycle
    obtain ⟨x, w, hw, hlen⟩ := TwoDefectCore.cycle_induce_transport G (s : Set V) hcycle
    exact hCE.not_hasPowerOfTwoCycle ⟨2, le_rfl, x, w, hw, hlen⟩
  have hsne : Nonempty ↥(s : Set V) := by
    obtain ⟨v, _⟩ := hhigh
    exact ⟨v⟩
  letI : Nonempty ↥(s : Set V) := hsne
  obtain ⟨R⟩ := BipartiteRepair.exists_repair B c hc hC4 hlow hhigh
  letI : Fintype R.Vertex := R.vertices
  letI : Nonempty R.Vertex := R.inhabited
  have horder : Fintype.card R.Vertex < Fintype.card V := by
    have hcard : Fintype.card ↥(s : Set V) = s.card := Fintype.card_coe s
    exact R.order_le.trans_lt (hcard.trans_lt hproper)
  obtain ⟨k, hk, x, w, hw, hlen⟩ := hminimal R.Vertex R.graph horder R.min_degree
  have heven : Even (2 ^ k) :=
    (Nat.even_pow' (by omega : k ≠ 0)).mpr (by decide)
  have hBcycle : ∃ y, ∃ p : B.Walk y y, p.IsCycle ∧ p.length = 2 ^ k :=
    R.even_cycles (2 ^ k) heven ⟨x, w, hw, hlen⟩
  obtain ⟨y, p, hp, hplen⟩ := TwoDefectCore.cycle_induce_transport G (s : Set V) hBcycle
  exact hCE.not_hasPowerOfTwoCycle ⟨k, hk, y, p, hp, hplen⟩

/-- Strong subset exclusion: in a globally vertex-minimal counterexample, no proper
finite induced vertex subset has a proper Bool coloring together with the two-defect
ordinary-degree bound and a high-degree vertex. This is conditional on `hminimal`;
there is no assertion that a counterexample or such a region exists. -/
theorem not_exists_proper_bipartite_region {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hCE : IsCounterexample G)
    (hminimal : ∀ (W : Type u) [Fintype W] [Nonempty W] (Q : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ v, 3 ≤ Q.degree v) → HasPowerOfTwoCycle Q)
    (s : Finset V) (hproper : s.card < Fintype.card V) :
    ¬ ∃ c : ↥(s : Set V) → Bool,
      (∀ ⦃x y⦄, (G.induce (s : Set V)).Adj x y → c x ≠ c y) ∧
      (Finset.univ.filter (fun v : ↥(s : Set V) =>
        (G.induce (s : Set V)).degree v ≤ 2)).card ≤ 2 ∧
      (∃ v : ↥(s : Set V), 3 ≤ (G.induce (s : Set V)).degree v) := by
  rintro ⟨c, hc, hlow, hhigh⟩
  exact proper_induced_region_excluded G hCE hminimal s hproper c hc hlow hhigh

/-- The existing lexicographic minimal-counterexample interface supplies global vertex
minimality, hence excludes the same proper induced bipartite regions. Minimality and
counterexample existence are hypotheses only, not proved here. -/
theorem not_exists_proper_bipartite_region_of_minimal {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) (s : Finset V) (hproper : s.card < Fintype.card V) :
    ¬ ∃ c : ↥(s : Set V) → Bool,
      (∀ ⦃x y⦄, (G.induce (s : Set V)).Adj x y → c x ≠ c y) ∧
      (Finset.univ.filter (fun v : ↥(s : Set V) =>
        (G.induce (s : Set V)).degree v ≤ 2)).card ≤ 2 ∧
      (∃ v : ↥(s : Set V), 3 ≤ (G.induce (s : Set V)).degree v) := by
  classical
  apply not_exists_proper_bipartite_region G hmin.isCounterexample ?_ s hproper
  intro W _ _ Q horder hdegree
  by_contra hfree
  have hQ : IsCounterexample Q := ⟨inferInstance, hdegree, hfree⟩
  exact hmin.not_size_lexLt Q hQ (Or.inl horder)

end Erdos64.BipartiteRegionExclusion
