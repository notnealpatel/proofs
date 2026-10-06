import Erdos.Erdos64.TwoCubicClawCentersContractedCycleLift

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersExclusion

open SimpleGraph UniqueCubicClawCenter TwoCubicClawCentersQuotient
  TwoCubicClawCentersContraction

universe u

/-- An order-minimal alleged counterexample with independent original vertices of
degree at least four and exactly two cubic claw centers has an original simple cycle
of power-of-two length. Both auxiliaries and the selected literal cycle are constructed
internally; minimality is applied without inherited side-class restrictions. -/
theorem two_cubic_claw_centers_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {u v : V} (huv : u ≠ v) (hcu : Claw G u) (hcv : Claw G v)
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) : HasPowerOfTwoCycle G := by
  classical
  have hUV := roots_adjacent_of_minimal G hG hminimal huv hCenters hcu hcv hdu hdv hHIGH
  let J := contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)
  letI : DecidableRel J.Adj := Classical.decRel J.Adj
  have hJ : HasPowerOfTwoCycle J := contracted_auxiliary_hasPowerOfTwoCycle G hG hminimal
    huv hCenters hcu hcv hdu hdv hHIGH hUV
  obtain ⟨k, hk, x, p, hp, hplen⟩ := hJ
  have hlen : 4 ≤ p.length := by
    have hpow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    norm_num at hpow
    omega
  obtain ⟨a, q, hq, hqlen⟩ := contracted_cycle_lifts G hG huv hCenters hcu hcv hdu hdv
    hHIGH hUV p hp hlen
  refine ⟨k + 1, by omega, a, q, hq, ?_⟩
  rw [hqlen, hplen, pow_succ, Nat.mul_comm]

/-- An order-minimal counterexample with independent original vertices of degree
at least four cannot have exactly two distinct claw centers, both of degree three.
The hypotheses concern only the original graph and unrestricted smaller-order minimality. -/
theorem two_cubic_claw_centers_false {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {u v : V} (huv : u ≠ v) (hcu : Claw G u) (hcv : Claw G v)
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) : False := by
  exact hG.not_hasPowerOfTwoCycle
    (two_cubic_claw_centers_hasPowerOfTwoCycle G hG hminimal hHIGH huv hcu hcv hCenters hdu hdv)

end Erdos64.TwoCubicClawCentersExclusion
