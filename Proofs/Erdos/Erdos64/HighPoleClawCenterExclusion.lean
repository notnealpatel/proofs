import Erdos.Erdos64.HighPoleOrderReduction
import Erdos.Erdos64.HighPoleFisherRepresentation
import Erdos.Erdos64.TriangleIncidenceOrderReduction
import Erdos.Erdos64.TriangleIncidenceCycleLiftFinal

set_option autoImplicit false

namespace Erdos64.HighPoleClawCenterExclusion

open SimpleGraph Erdos64.UniqueCubicClawCenter

universe u

/-- A globally order-minimal counterexample with a unique claw center
and independent high-degree vertices has an actual power-of-two cycle in the
original graph, via its partial Fisher core or triangle-incidence graph. -/
theorem hasPowerOfTwoCycle_original {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    HasPowerOfTwoCycle G := by
  classical
  by_cases hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b
  · have hcore := HighPoleOrderReduction.fisher_hasPowerOfTwoCycle
      G hG hminimal hc hu hN hHIGH
    let e := HighPoleFisherRepresentation.coreIso G hG hc hu hN
    obtain ⟨n, hn, a, p, hp, hlen⟩ := hcore
    refine ⟨n, hn, e a, p.map e.toHom, ?_, ?_⟩
    · exact SimpleGraph.Walk.IsCycle.map e.injective hp
    · simpa only [SimpleGraph.Walk.length_map] using hlen
  · push_neg at hN
    obtain ⟨a, b, ha, hb, hab⟩ := hN
    have hv := TriangleIncidenceLocal.center_degree_ge_four G hG hc ha hb hab
    let D := TriangleIncidence.actualModel G hG hu hHIGH hv
    have hcore := TriangleIncidence.auxiliary_hasPowerOfTwoCycle
      G hG hminimal hc hu hHIGH ha hb hab
    obtain ⟨n, hn, x, c, hc', hlen⟩ := hcore
    have hfour : 4 ≤ c.length := by
      rw [hlen]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
    obtain ⟨y, p, hp, hlen'⟩ := TriangleIncidence.Model.exists_doubled_cycle D c hc' hfour
    refine ⟨n + 1, by omega, y, p, hp, ?_⟩
    rw [hlen', hlen, pow_succ, Nat.mul_comm]

/-- Global order minimality excludes an original counterexample with a unique
claw center and independent high-degree vertices;
there is no restriction on the center degree. -/
theorem false_of_unique_claw_center {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    False := by
  exact hG.not_hasPowerOfTwoCycle
    (hasPowerOfTwoCycle_original G hG hminimal hc hu hHIGH)

end Erdos64.HighPoleClawCenterExclusion
