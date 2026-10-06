import Erdos.Erdos64.TwoCubicClawCentersDegree

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence TriangleIncidenceLocal

universe u

/-- The chosen actual port of an incidence; a nonedge receives the first center label. -/
noncomputable def chosenPort {V : Type u} (G : SimpleGraph V) (u v : V)
    (x y : Node G) : V := by
  classical
  exact if h : (auxiliary G u v).Adj x y then Classical.choose h else u

example {V : Type u} (G : SimpleGraph V) (u v : V) (x y : Node G)
    (h : ¬ (auxiliary G u v).Adj x y) : chosenPort G u v x y = u := by
  simp [chosenPort, h]

/-- Chosen ports agree with every actual connector witness. -/
theorem chosenPort_eq {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} {x y : Node G} {a b : V} (h : Connector G u v x y a b) :
    chosenPort G u v x y = a := by
  classical
  have hadj : (auxiliary G u v).Adj x y := ⟨a, b, h⟩
  rw [chosenPort, dif_pos hadj]
  exact (connector_ports_unique G hG
    (Classical.choose_spec (Classical.choose_spec hadj)) h).1

/-- Both directions of an auxiliary edge choose its actual connector ports. -/
theorem chosen_connector {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} {x y : Node G} (h : (auxiliary G u v).Adj x y) :
    Connector G u v x y (chosenPort G u v x y) (chosenPort G u v y x) := by
  obtain ⟨a, b, he⟩ := h
  rw [chosenPort_eq G hG he, chosenPort_eq G hG he.symm]
  exact he

/-- An equal-port connector represents a high original vertex, not an ordinary edge. -/
theorem equal_connector_high {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a : V} (huv : u ≠ v) (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    {x y : Node G} (h : Connector G u v x y a a) : 4 ≤ G.degree a := by
  have hmin := hG.degree_ge_three a
  have hne := zero_port_not_cubic G hG huv hcu hcv hdu hdv h
  omega

/-- Equal-port connectors only join actual triangle nodes; neither cubic root is incident. -/
theorem equal_connector_triangles {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a : V} (huv : u ≠ v) (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    {x y : Node G} (h : Connector G u v x y a a) :
    ∃ s t : Triangle G, x = .inr s ∧ y = .inr t := by
  have hn := zero_port_not_cubic G hG huv hcu hcv hdu hdv h
  have hx : ∃ s : Triangle G, x = .inr s := by
    cases x with
    | inl i =>
      rcases i with ⟨i⟩
      cases i
      · exact (hn (h.2.1 ▸ hdu)).elim
      · exact (hn (h.2.1 ▸ hdv)).elim
    | inr s => exact ⟨s, rfl⟩
  have hy : ∃ t : Triangle G, y = .inr t := by
    cases y with
    | inl i =>
      rcases i with ⟨i⟩
      cases i
      · exact (hn (h.2.2.1 ▸ hdu)).elim
      · exact (hn (h.2.2.1 ▸ hdv)).elim
    | inr t => exact ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  exact ⟨s, t, hs, ht⟩

/-- A shared original vertex between distinct auxiliary nodes forces their zero connector. -/
theorem connector_of_overlap {V : Type u} (G : SimpleGraph V)
    {u v a : V} {x y : Node G} (hxy : x ≠ y)
    (hx : a ∈ members G u v x) (hy : a ∈ members G u v y) :
    Connector G u v x y a a := ⟨hxy, hx, hy, Or.inl rfl⟩

/-- HIGH makes the equal-port connectors a matching: each node has at most one target. -/
theorem zero_connector_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {x y z : Node G} {a b : V}
    (hy : Connector G u v x y a a) (hz : Connector G u v x z b b) : y = z := by
  obtain ⟨s, t, hx, _⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv hy
  subst x
  by_cases hab : a = b
  · subst b
    exact connector_neighbor_unique G hG huv hCenters hcu hcv hdu hdv hy hz
  · exact (hHIGH a b
      (equal_connector_high G hG huv hcu hcv hdu hdv hy)
      (equal_connector_high G hG huv hcu hcv hdu hdv hz)
      (s.property.isClique hy.2.1 hz.2.1 hab)).elim

/-- The chosen zero connector at a node is unique, expressing the actual matching. -/
theorem chosen_zero_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {x y z : Node G} (hxy : (auxiliary G u v).Adj x y)
    (hy : chosenPort G u v x y = chosenPort G u v y x)
    (hxz : (auxiliary G u v).Adj x z)
    (hz : chosenPort G u v x z = chosenPort G u v z x) : y = z := by
  have cy := chosen_connector G hG hxy
  have cz := chosen_connector G hG hxz
  rw [← hy] at cy
  rw [← hz] at cz
  exact zero_connector_unique G hG huv hCenters hcu hcv hdu hdv hHIGH cy cz

end Erdos64.TwoCubicClawCentersQuotient
