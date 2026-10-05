import Erdos.Erdos64.HighPoleOrderReduction
import Erdos.Erdos64.HighPoleFisherRepresentation

set_option autoImplicit false

namespace Erdos64.HighPoleClawCenterExclusion

open SimpleGraph Erdos64.UniqueCubicClawCenter

universe u

/-- A globally order-minimal counterexample with a unique claw center,
independent center neighbors, and independent high-degree vertices has an actual
power-of-two cycle in the original graph, via its canonical partial Fisher core. -/
theorem hasPowerOfTwoCycle_original {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    HasPowerOfTwoCycle G := by
  classical
  have hcore := HighPoleOrderReduction.fisher_hasPowerOfTwoCycle
    G hG hminimal hc hu hN hHIGH
  let e := HighPoleFisherRepresentation.coreIso G hG hc hu hN
  obtain ⟨n, hn, a, p, hp, hlen⟩ := hcore
  refine ⟨n, hn, e a, p.map e.toHom, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsCycle.map e.injective hp
  · simpa only [SimpleGraph.Walk.length_map] using hlen

/-- Global order minimality excludes an original counterexample with a unique
claw center, independent center neighbors, and independent high-degree vertices;
there is no restriction on the center degree. -/
theorem false_of_unique_claw_center {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    False := by
  exact hG.not_hasPowerOfTwoCycle
    (hasPowerOfTwoCycle_original G hG hminimal hc hu hN hHIGH)

end Erdos64.HighPoleClawCenterExclusion
