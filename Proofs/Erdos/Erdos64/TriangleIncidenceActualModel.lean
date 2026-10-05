import Erdos.Erdos64.TriangleIncidencePorts

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

/-- The chosen original port of an auxiliary incidence; nonedges receive the root label. -/
noncomputable def chosenPort {V : Type u} (G : SimpleGraph V) (v : V)
    (x y : Node G) : V := by
  classical
  exact if h : (auxiliary G v).Adj x y then Classical.choose h else v

example {V : Type u} (G : SimpleGraph V) (v : V) (x y : Node G)
    (h : ¬ (auxiliary G v).Adj x y) : chosenPort G v x y = v := by
  simp [chosenPort, h]

/-- The chosen port agrees with every actual connector witness. -/
theorem chosenPort_eq {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} {x y : Node G} {a b : V} (h : Connector G v x y a b) :
    chosenPort G v x y = a := by
  classical
  have hadj : (auxiliary G v).Adj x y := ⟨a, b, h⟩
  rw [chosenPort, dif_pos hadj]
  exact (connector_ports_unique G hG (Classical.choose_spec (Classical.choose_spec hadj)) h).1

/-- Both directions of an auxiliary incidence choose its actual original connector ports. -/
theorem chosen_connector {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} {x y : Node G} (h : (auxiliary G v).Adj x y) :
    Connector G v x y (chosenPort G v x y) (chosenPort G v y x) := by
  obtain ⟨a, b, hab⟩ := h
  rw [chosenPort_eq G hG hab, chosenPort_eq G hG hab.symm]
  exact hab

/-- An equal-port connector at a triangle represents a high original vertex. -/
theorem equal_connector_high {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hv : 4 ≤ G.degree v) {s : Triangle G} {y : Node G} {a : V}
    (h : Connector G v (some s) y a a) : 4 ≤ G.degree a := by
  cases y with
  | none =>
    have hav : a = v := h.2.2.1
    rw [hav]
    exact hv
  | some t =>
    have hmin := hG.degree_ge_three a
    have hne : G.degree a ≠ 3 := by
      intro ha
      have hst := triangle_eq_of_degree_three G hG ha s t h.2.1 h.2.2.1
      exact h.1 (congrArg some hst)
    omega

/-- The root has a zero connector to every actual triangle containing it. -/
theorem root_connector {V : Type u} (G : SimpleGraph V) {v : V}
    (s : Triangle G) (hs : v ∈ s.val) : Connector G v none (some s) v v := by
  exact ⟨by simp, rfl, hs, Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩⟩

/-- Distinct triangles containing the root have no auxiliary edge between them. -/
theorem root_triangles_nonadjacent {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (s t : Triangle G) (hs : v ∈ s.val) (ht : v ∈ t.val) :
    ¬ (auxiliary G v).Adj (some s) (some t) := by
  rintro ⟨a, b, hab⟩
  rcases hab.2.2.2 with ⟨heq, hzero⟩ | ⟨hav, hbv, eab⟩
  · subst b
    have hav : a ≠ v := by simpa using hzero
    have hst := triangle_eq_of_two_common_vertices G hG s t hav hab.2.1 hs hab.2.2.1 ht
    exact hab.1 (congrArg some hst)
  · exact false_of_shared_vertex_and_ordinary G hG s t hs ht hab.2.1 hab.2.2.1 eab

/-- The actual triangle-incidence auxiliary graph satisfies the generic cycle-lift model. -/
noncomputable def actualModel {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hv : 4 ≤ G.degree v) : Model G (auxiliary G v) v none := by
  classical
  refine {
    triangle := fun x => match x with | none => ∅ | some s => s.val
    root_triangle := rfl
    triangle_clique := ?_
    port := chosenPort G v
    root_port := ?_
    port_mem := ?_
    port_injective := ?_
    port_surjective := ?_
    connector := ?_
    zero_unique := ?_
    root_mem_iff := ?_
    overlap := ?_
    root_leaves_nonadjacent := ?_ }
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some s => exact s.property
  · intro y hy
    exact (chosen_connector G hG hy).2.1
  · intro x y hx hy
    cases x with
    | none => exact (hx rfl).elim
    | some s => exact (chosen_connector G hG hy).2.1
  · intro x y z hx hxy hxz heq
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      have hy := chosen_connector G hG hxy
      have hz := chosen_connector G hG hxz
      rw [← heq] at hz
      exact connector_neighbor_unique G hG hu hy hz
  · intro x a hx ha
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      obtain ⟨y, b, hab⟩ := incidence_exists G hG hu s ha
      exact ⟨y, ⟨a, b, hab⟩, chosenPort_eq G hG hab⟩
  · intro x y hxy
    rcases (chosen_connector G hG hxy).2.2.2 with ⟨heq, hz⟩ | ⟨hx, hy, hedge⟩
    · exact Or.inl heq
    · exact Or.inr hedge.1
  · intro x y z hx hxy hzero hxz hzero'
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      have hy := chosen_connector G hG hxy
      have hz := chosen_connector G hG hxz
      rw [← hzero] at hy
      rw [← hzero'] at hz
      have hhighy := equal_connector_high G hG hv hy
      have hhighz := equal_connector_high G hG hv hz
      by_cases heq : chosenPort G v (some s) y = chosenPort G v (some s) z
      · rw [← heq] at hz
        exact connector_neighbor_unique G hG hu hy hz
      · exact (hHIGH _ _ hhighy hhighz (s.property.isClique hy.2.1 hz.2.1 heq)).elim
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      constructor
      · intro hs
        have h := root_connector G s hs
        exact ⟨⟨v, v, h⟩, (chosenPort_eq G hG h).trans (chosenPort_eq G hG h.symm).symm⟩
      · rintro ⟨hadj, heq⟩
        have h := chosen_connector G hG hadj
        have hroot : chosenPort G v none (some s) = v := h.2.1
        have hport : chosenPort G v (some s) none = v := heq.symm.trans hroot
        simpa only [members, Finset.mem_coe, hport] using h.2.2.1
  · intro x y a hx hy hxy hax hay
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      cases y with
      | none => exact (hy rfl).elim
      | some t =>
        by_cases hav : a = v
        · subst a
          have hs := root_connector G s hax
          have ht := root_connector G t hay
          exact Or.inr ⟨rfl, ⟨v, v, hs⟩,
            (chosenPort_eq G hG hs).trans (chosenPort_eq G hG hs.symm).symm,
            ⟨v, v, ht⟩, (chosenPort_eq G hG ht).trans (chosenPort_eq G hG ht.symm).symm⟩
        · have h : Connector G v (some s) (some t) a a :=
            ⟨hxy, hax, hay, Or.inl ⟨rfl, Or.inl hav⟩⟩
          exact Or.inl ⟨⟨a, a, h⟩,
            (chosenPort_eq G hG h).trans (chosenPort_eq G hG h.symm).symm,
            chosenPort_eq G hG h⟩
  · intro x y hx hzero hy hzero'
    cases x with
    | none => exact ((auxiliary G v).irrefl hx).elim
    | some s =>
      cases y with
      | none => exact ((auxiliary G v).irrefl hy).elim
      | some t =>
        have hs := chosen_connector G hG hx
        have ht := chosen_connector G hG hy
        have hrootx : chosenPort G v none (some s) = v := hs.2.1
        have hrooty : chosenPort G v none (some t) = v := ht.2.1
        have hxs : v ∈ s.val := by
          have hp := hzero.symm.trans hrootx
          simpa only [members, Finset.mem_coe, hp] using hs.2.2.1
        have hyt : v ∈ t.val := by
          have hp := hzero'.symm.trans hrooty
          simpa only [members, Finset.mem_coe, hp] using ht.2.2.1
        exact root_triangles_nonadjacent G hG s t hxs hyt

example {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCounterexample G) {v : V} (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hv : 4 ≤ G.degree v) :
    (actualModel G hG hu hHIGH hv).port = chosenPort G v := rfl

end Erdos64.TriangleIncidence
