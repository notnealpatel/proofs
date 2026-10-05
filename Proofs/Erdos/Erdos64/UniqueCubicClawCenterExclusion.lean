import Erdos.Erdos64.UniqueCubicClawCenterPoleRootArms
import Erdos.Erdos64.UniqueCubicClawCenterSuppression
import Erdos.Erdos64.UniqueCubicClawCenterDyadicLift

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- Global order minimality applies to the entire suppressed cubic graph, including
cycles in components not containing the pole root. This is the input to the remaining
ordinary-cycle lifting argument, not the full claw-center exclusion. -/
theorem suppressed_hasPowerOfTwoCycle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v : V} [DecidableRel (completion G v).Adj]
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    [DecidableRel (suppression (cliqueRoot (completion G v))).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v) :
    HasPowerOfTwoCycle (suppression (cliqueRoot (completion G v))) := by
  let R := completion G v
  let H := cliqueRoot R
  let K := suppression H
  letI := completion_nonempty G hclaw
  have hD : StrongDiamondFree R := completion_strongDiamondFree G hG hv
  have hcf : ∀ x, ¬ Claw R x := completion_claw_free G hunique
  have hmin : ∀ x, 3 ≤ R.degree x := completion_min_degree G hG hv hclaw
  obtain ⟨z, hz, hz3, harms⟩ := exists_pole_root_with_cubic_arms G hG hv hclaw hunique
  have hdegrees : ∀ a, H.degree a = 2 ∨ H.degree a = 3 :=
    cliqueRoot_degree_two_or_three R hD hcf hmin
  have hno22 : ∀ a b, H.Adj a b → H.degree a = 2 → H.degree b = 2 → False := by
    intro a b hab ha hb
    exact cliqueRoot_no_adjacent_degree_two R hD hcf hmin hab ha hb
  have htri : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False := by
    intro a b c hab hbc hca
    exact cliqueRoot_triangle_free R hD hcf hmin hab hbc hca
  have hparallel : ∀ a b p q, H.degree a = 3 → H.degree b = 3 → a ≠ b →
      H.degree p = 2 → H.degree q = 2 → p ≠ q →
      H.Adj a p → H.Adj p b → H.Adj a q → H.Adj q b → False := by
    intro a b p q ha hb hab hp hq hpq hap hpb haq hqb
    exact completion_root_parallel_impossible G hG hv hclaw hunique hz hz3 harms
      hab hpq hp hq hap hpb hqb.symm haq.symm
  have hKdegree : ∀ x, K.degree x = 3 :=
    suppression_degree_three H hdegrees hno22 htri hparallel
  letI := suppression_nonempty H hz3
  have horder : Fintype.card (SuppressionNode H) < Fintype.card V :=
    completion_suppression_order_lt G hG hv hclaw hunique
  exact hminimal K horder (fun x => by rw [hKdegree x])

/-- A globally order-minimal counterexample with independent original vertices
of degree at least four cannot have a unique claw center of degree three. All
suppression and doubled-cycle witnesses are constructed from the original graph. -/
theorem unique_cubic_claw_center_false {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    (hv : G.degree v = 3) : False := by
  classical
  obtain ⟨k, hk, x, p, hp, hplen⟩ :=
    suppressed_hasPowerOfTwoCycle G hG hminimal hv hclaw hunique
  obtain ⟨y, q, hq, hqlen⟩ := suppression_cycle_lifts G hG hHIGH hv hclaw hunique p hp hk hplen
  have hcycle : HasPowerOfTwoCycle G := by
    refine ⟨k + 1, by omega, y, q, hq, ?_⟩
    rw [hqlen, hplen, pow_succ, Nat.mul_comm]
  exact hG.2.2 hcycle

end Erdos64.UniqueCubicClawCenter
