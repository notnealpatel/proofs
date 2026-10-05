import Erdos.Erdos64.HighPoleRootSuppression
import Erdos.Erdos64.HighPoleMatching
import Erdos.Erdos64.PartialFisherCycle

set_option autoImplicit false

namespace Erdos64.HighPoleOrderReduction

open SimpleGraph Erdos64.UniqueCubicClawCenter

universe u

/-- Global order minimality gives a power-of-two cycle in the actual standard
suppression of the canonical completion root, without a pole-degree restriction. -/
theorem suppressed_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    [DecidableRel (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).Adj] :
    HasPowerOfTwoCycle
      (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))) := by
  letI := HighPoleRootSuppression.suppression_nonempty G hG hclaw hunique hN
  have horder := HighPoleRootSuppression.suppression_card_lt_original
    G hG hclaw hunique hN
  have hdegree : ∀ x : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)),
      3 ≤ (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).degree x := by
    intro x
    rw [HighPoleRootSuppression.suppression_degree_eq G hG hclaw hunique hN]
    exact x.property
  exact hminimal _ horder hdegree

/-- Under independence of original high-degree vertices, the actual partial Fisher
core of the canonical suppressed root has a power-of-two cycle. The cycle need not
meet the canonical retained pole. -/
theorem fisher_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    [DecidableRel (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).Adj] :
    HasPowerOfTwoCycle (PartialFisherCore.G
      (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v)))
      (HighPoleRootSuppression.retainedPole G hG hclaw hunique hN)
      (HighPoleMatching.M G hG hclaw)) := by
  let K := RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))
  let z := HighPoleRootSuppression.retainedPole G hG hclaw hunique hN
  let M := HighPoleMatching.M G hG hclaw
  have hz : z.val = HighPoleRootGeometry.poleRoot G hG hclaw :=
    HighPoleRootSuppression.retainedPole_val G hG hclaw hunique hN
  have hdegree : ∀ x, x ≠ z → K.degree x = 3 := by
    intro x hx
    have hxval : x.val ≠ HighPoleRootGeometry.poleRoot G hG hclaw := by
      intro he
      exact hx (Subtype.ext (he.trans hz.symm))
    exact HighPoleRootSuppression.suppression_nonpole_degree G hG hclaw hunique hN x hxval
  have hmatch : ∀ x y w, M.Adj x y → M.Adj x w → y = w :=
    HighPoleMatching.M_matching G hG hclaw hunique hN hHIGH
  have hpole : ∀ x, ¬ M.Adj z x := fun x =>
    HighPoleMatching.M_avoids_pole G hG hclaw z x hz
  exact PartialFisherCycle.hasPowerOfTwoCycle_lift K M z hdegree hmatch hpole
    (suppressed_hasPowerOfTwoCycle G hG hminimal hclaw hunique hN)

end Erdos64.HighPoleOrderReduction
