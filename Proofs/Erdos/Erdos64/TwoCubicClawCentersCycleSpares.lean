import Erdos.Erdos64.TwoCubicClawCentersCyclePorts

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

section

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCounterexample G) {u v : V} (huv : u ≠ v)
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)

include hG huv hCenters hcu hcv hdu hdv

/-- A spare at a triangle turn cannot equal another turn's used port when the selected
incidences reciprocate. Unlike global port injectivity, this is support-aware. -/
theorem third_ne_other_port {x y z t s : Node G} {a : V}
    (hx : IsTriangle G x) (hxt : x ≠ t) (hts : (auxiliary G u v).Adj t s)
    (ha : a ∈ triangle G x)
    (hay : a ≠ chosenPort G u v x y) (haz : a ≠ chosenPort G u v x z)
    (hrecip : s = x → t = y ∨ t = z) : a ≠ chosenPort G u v t s := by
  intro he
  have hax : a ∈ members G u v x := by
    cases x with
    | inl i => exact hx.elim
    | inr A => exact ha
  have hat : a ∈ members G u v t := he.symm ▸ port_mem G hG hts
  have ce := connector_of_overlap G hxt hax hat
  obtain ⟨A, B, _, ht⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv ce
  have hsx : s = x := by
    have cs := chosen_connector G hG hts
    rw [← he] at cs
    subst t
    exact connector_neighbor_unique G hG huv hCenters hcu hcv hdu hdv cs ce.symm
  have hport : a = chosenPort G u v x t := (chosenPort_eq G hG ce).symm
  rcases hrecip hsx with hty | htz
  · exact hay (by simpa only [hty] using hport)
  · exact haz (by simpa only [htz] using hport)

/-- A spare distinct from its own incoming and outgoing ports is fresh from every used
port of a simple auxiliary cycle, even if it is shared with an off-cycle triangle. -/
theorem cycle_spare_ne_ports {m : ℕ}
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    {i : Fin (m + 1)} {a : V} (hi : IsTriangle G (c i))
    (ha : a ∈ triangle G (c i))
    (hap : a ≠ chosenPort G u v (c i) (c (i - 1)))
    (han : a ≠ chosenPort G u v (c i) (c (i + 1))) (j : Fin (m + 1)) :
    a ≠ chosenPort G u v (c j) (c (j - 1)) ∧
      a ≠ chosenPort G u v (c j) (c (j + 1)) := by
  by_cases hij : i = j
  · subst j
    exact ⟨hap, han⟩
  have hprev : (auxiliary G u v).Adj (c j) (c (j - 1)) := by
    simpa only [sub_add_cancel] using (hadj (j - 1)).symm
  constructor
  · apply third_ne_other_port G hG huv hCenters hcu hcv hdu hdv hi
      (fun he => hij (hc he)) hprev ha hap han
    intro he
    have hji : j = i + 1 := by
      simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) (hc he)
    exact Or.inr (congrArg c hji)
  · apply third_ne_other_port G hG huv hCenters hcu hcv hdu hdv hi
      (fun he => hij (hc he)) (hadj j) ha hap han
    intro he
    have hji : j = i - 1 := by
      simpa only [add_sub_cancel_right] using congrArg (fun t : Fin (m + 1) => t - 1) (hc he)
    exact Or.inl (congrArg c hji)

/-- A spare at a node incident to a used zero connector belongs to no other node.
HIGH prevents that triangle from having a second shared port. -/
theorem private_of_zero
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {x y : Node G} {a b : V} (he : Connector G u v x y b b)
    (ha : a ∈ members G u v x) (hab : a ≠ b) :
    ∀ t, t ≠ x → a ∉ members G u v t := by
  intro t htx hat
  have ce := connector_of_overlap G htx.symm ha hat
  have hyt := zero_connector_unique G hG huv hCenters hcu hcv hdu hdv hHIGH he ce
  subst t
  have heq := (connector_ports_unique G hG he ce).1
  exact hab heq.symm

end

end Erdos64.TwoCubicClawCentersQuotient
