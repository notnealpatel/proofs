import Erdos.Erdos64.TwoCubicClawCentersMatching
import Erdos.Erdos64.UniqueCubicClawCenterCycleIndex

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

/-- Triangle nodes, as opposed to the two retained singleton roots. -/
def IsTriangle {V : Type u} (G : SimpleGraph V) : Node G → Prop
  | .inl _ => False
  | .inr _ => True

example {V : Type u} (G : SimpleGraph V) (i : ULift.{u} Bool) :
    ¬ IsTriangle G (.inl i) := id

example {V : Type u} (G : SimpleGraph V) (s : Triangle G) :
    IsTriangle G (.inr s) := True.intro

/-- The actual triangle carried by a node, empty at either singleton root. -/
def triangle {V : Type u} (G : SimpleGraph V) : Node G → Finset V
  | .inl _ => ∅
  | .inr s => s.val

example {V : Type u} (G : SimpleGraph V) (i : ULift.{u} Bool) :
    triangle G (.inl i) = ∅ := rfl

example {V : Type u} (G : SimpleGraph V) (s : Triangle G) :
    triangle G (.inr s) = s.val := rfl

section

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCounterexample G) {u v : V} (huv : u ≠ v)
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)

include hG

/-- A chosen port belongs to its source node's original label set. -/
theorem port_mem {x y : Node G} (hxy : (auxiliary G u v).Adj x y) :
    chosenPort G u v x y ∈ members G u v x := (chosen_connector G hG hxy).2.1

/-- At a triangle node, a chosen port belongs to its actual triangle. -/
theorem port_mem_triangle {x y : Node G} (hx : IsTriangle G x)
    (hxy : (auxiliary G u v).Adj x y) : chosenPort G u v x y ∈ triangle G x := by
  cases x with
  | inl i => exact hx.elim
  | inr s => exact port_mem G hG hxy

include huv hCenters hcu hcv hdu hdv

/-- Distinct triangle incidences have distinct actual ports. -/
theorem ports_ne {x y z : Node G} (hx : IsTriangle G x)
    (hxy : (auxiliary G u v).Adj x y) (hxz : (auxiliary G u v).Adj x z)
    (hyz : y ≠ z) : chosenPort G u v x y ≠ chosenPort G u v x z := by
  intro he
  cases x with
  | inl i => exact hx.elim
  | inr s =>
    have cy := chosen_connector G hG hxy
    have cz := chosen_connector G hG hxz
    rw [← he] at cz
    exact hyz (connector_neighbor_unique G hG huv hCenters hcu hcv hdu hdv cy cz)

/-- Equal ports at distinct source nodes occur only on the reciprocal zero connector. -/
theorem port_collision {x y t s : Node G} (hxt : x ≠ t)
    (hxy : (auxiliary G u v).Adj x y) (hts : (auxiliary G u v).Adj t s)
    (he : chosenPort G u v x y = chosenPort G u v t s) :
    y = t ∧ s = x ∧ chosenPort G u v x y = chosenPort G u v y x := by
  have cy := chosen_connector G hG hxy
  have cs := chosen_connector G hG hts
  have ha := cy.2.1
  have ht : chosenPort G u v x y ∈ members G u v t := he.symm ▸ cs.2.1
  have cz := connector_of_overlap G hxt ha ht
  obtain ⟨A, B, hx, ht⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv cz
  have hyt : y = t := by
    subst x
    exact connector_neighbor_unique G hG huv hCenters hcu hcv hdu hdv cy cz
  have hsx : s = x := by
    subst t
    have cr := cz.symm
    rw [he] at cr
    exact connector_neighbor_unique G hG huv hCenters hcu hcv hdu hdv cs cr
  refine ⟨hyt, hsx, ?_⟩
  subst y
  exact (chosenPort_eq G hG cz).trans (chosenPort_eq G hG cz.symm).symm

/-- Incoming ports of a simple auxiliary cycle are pairwise distinct. -/
theorem incoming_injective {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)}
    (he : chosenPort G u v (c i) (c (i - 1)) =
      chosenPort G u v (c j) (c (j - 1))) : i = j := by
  by_cases hij : i = j
  · exact hij
  have hprev (t : Fin (m + 1)) : (auxiliary G u v).Adj (c t) (c (t - 1)) := by
    simpa only [sub_add_cancel] using (hadj (t - 1)).symm
  obtain ⟨hp, hq, _⟩ := port_collision G hG huv hCenters hcu hcv hdu hdv
    (fun h => hij (hc h)) (hprev i) (hprev j) he
  have hp' : i = j + 1 := by
    simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) (hc hp)
  have hq' : j = i + 1 := by
    simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) (hc hq)
  exact False.elim (CycleIndex.succ_succ_ne m hm i (by rw [← hq', ← hp']))

/-- Ordinary outgoing ports of a simple auxiliary cycle are pairwise distinct. -/
theorem outgoing_injective {m : ℕ}
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)}
    (hi : chosenPort G u v (c i) (c (i + 1)) ≠ chosenPort G u v (c (i + 1)) (c i))
    (he : chosenPort G u v (c i) (c (i + 1)) =
      chosenPort G u v (c j) (c (j + 1))) : i = j := by
  by_cases hij : i = j
  · exact hij
  exact (hi (port_collision G hG huv hCenters hcu hcv hdu hdv
    (fun h => hij (hc h)) (hadj i) (hadj j) he).2.2).elim

/-- The two cycle ports of a triangle turn are distinct. -/
theorem cycle_ports_ne {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    {i : Fin (m + 1)} (hi : IsTriangle G (c i)) :
    chosenPort G u v (c i) (c (i - 1)) ≠ chosenPort G u v (c i) (c (i + 1)) := by
  have hprev : (auxiliary G u v).Adj (c i) (c (i - 1)) := by
    simpa only [sub_add_cancel] using (hadj (i - 1)).symm
  apply ports_ne G hG huv hCenters hcu hcv hdu hdv hi hprev (hadj i)
  intro he
  have hindex' : i = i + 1 + 1 := by
    simpa only [sub_add_cancel] using congrArg (fun t : Fin (m + 1) => t + 1) (hc he)
  exact CycleIndex.succ_succ_ne m hm i hindex'.symm

/-- An incoming triangle-turn port cannot equal an ordinary outgoing port. -/
theorem incoming_ne_outgoing {m : ℕ} (hm : 3 ≤ m + 1)
    (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1)))
    {i j : Fin (m + 1)} (hi : IsTriangle G (c i))
    (hj : chosenPort G u v (c j) (c (j + 1)) ≠ chosenPort G u v (c (j + 1)) (c j)) :
    chosenPort G u v (c i) (c (i - 1)) ≠ chosenPort G u v (c j) (c (j + 1)) := by
  intro he
  by_cases hij : i = j
  · subst j
    exact cycle_ports_ne G hG huv hCenters hcu hcv hdu hdv hm c hc hadj hi he
  have hprev : (auxiliary G u v).Adj (c i) (c (i - 1)) := by
    simpa only [sub_add_cancel] using (hadj (i - 1)).symm
  obtain ⟨hp, hq, hz⟩ := port_collision G hG huv hCenters hcu hcv hdu hdv
    (fun h => hij (hc h)) hprev (hadj j) he
  exact hj (by simpa only [hp, hq] using hz.symm)

end

end Erdos64.TwoCubicClawCentersQuotient
