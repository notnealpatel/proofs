import Erdos.Erdos64.TriangleIncidencePorts

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal
open TriangleIncidence

universe u

/-- The two-center auxiliary carrier consists of two roots and all actual triangles. -/
abbrev Node {V : Type u} (G : SimpleGraph V) := ULift.{u} Bool ⊕ Triangle G

example {V : Type u} (G : SimpleGraph V) : Node G = (ULift.{u} Bool ⊕ Triangle G) := rfl

/-- A root represents its original center; a triangle represents its actual vertices. -/
def members {V : Type u} (G : SimpleGraph V) (u v : V) : Node G → Set V
  | .inl ⟨false⟩ => {u}
  | .inl ⟨true⟩ => {v}
  | .inr s => s.val

example {V : Type u} (G : SimpleGraph V) (u v a : V) :
    a ∈ members G u v (.inl ⟨false⟩) ↔ a = u := Iff.rfl

example {V : Type u} (G : SimpleGraph V) (u v a : V) :
    a ∈ members G u v (.inl ⟨true⟩) ↔ a = v := Iff.rfl

example {V : Type u} (G : SimpleGraph V) (u v a : V) (s : Triangle G) :
    a ∈ members G u v (.inr s) ↔ a ∈ s.val := Iff.rfl

/-- A cubic claw center belongs to no actual triangle. -/
theorem center_not_mem_triangle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V}
    (hd : G.degree x = 3) (hc : Claw G x) (s : Triangle G) : x ∉ s.val := by
  intro hx
  obtain ⟨a, b, _, _, _, ha, hb, hab, _⟩ := triangle_vertices G s hx
  exact poles_nonadjacent G hd hc ha hb hab

/-- Every vertex other than the two designated centers is nonclaw. -/
theorem not_claw_of_ne_centers {V : Type u} (G : SimpleGraph V) {u v a : V}
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v) (hau : a ≠ u) (hav : a ≠ v) :
    ¬ Claw G a := by
  intro hc
  rcases hCenters a hc with hu | hv
  · exact hau hu
  · exact hav hv

/-- Every noncenter original vertex has degree three or four. -/
theorem degree_three_or_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hau : a ≠ u) (hav : a ≠ v) : G.degree a = 3 ∨ G.degree a = 4 := by
  exact degree_three_or_four_of_not_claw G hG
    (not_claw_of_ne_centers G hCenters hau hav)

/-- Both endpoints of an edge outside all actual triangles are cubic. -/
theorem ordinary_endpoint_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a b : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (he : NontriangleEdge G a b) : G.degree a = 3 := by
  by_cases hau : a = u
  · exact hau ▸ hdu
  by_cases hav : a = v
  · exact hav ▸ hdv
  rcases degree_three_or_four G hG hCenters hau hav with hd | hd
  · exact hd
  · obtain ⟨s, ha, hb⟩ := edge_in_triangle_of_degree_four G hG hd
      (not_claw_of_ne_centers G hCenters hau hav) he.1
    exact (he.2 s ha hb).elim

/-- Every noncenter belongs to an actual triangle, even when its degree is four. -/
theorem noncenter_triangle_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hau : a ≠ u) (hav : a ≠ v) : ∃ s : Triangle G, a ∈ s.val := by
  have hn := not_claw_of_ne_centers G hCenters hau hav
  have hm : 2 < (G.neighborFinset a).card := hG.degree_ge_three a
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hm
  have hax := (G.mem_neighborFinset a x).mp hx
  have hay := (G.mem_neighborFinset a y).mp hy
  have haz := (G.mem_neighborFinset a z).mp hz
  rcases edge_of_not_claw G hn hxy hxz hyz hax hay haz with he | he | he
  · obtain ⟨s, ha, _, _⟩ := exists_triangle_of_edges G hax hay he
    exact ⟨s, ha⟩
  · obtain ⟨s, ha, _, _⟩ := exists_triangle_of_edges G hax haz he
    exact ⟨s, ha⟩
  · obtain ⟨s, ha, _, _⟩ := exists_triangle_of_edges G hay haz he
    exact ⟨s, ha⟩

/-- Every original vertex is represented on the two-center auxiliary carrier. -/
theorem members_cover {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v) (a : V) :
    ∃ x : Node G, a ∈ members G u v x := by
  by_cases hau : a = u
  · exact ⟨.inl ⟨false⟩, hau⟩
  by_cases hav : a = v
  · exact ⟨.inl ⟨true⟩, hav⟩
  obtain ⟨s, hs⟩ := noncenter_triangle_exists G hG hCenters hau hav
  exact ⟨.inr s, hs⟩

/-- A cubic original vertex labels only one auxiliary node. Degree-four vertices are
intentionally excluded: they can belong to two actual triangles. -/
theorem member_node_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a : V} (huv : u ≠ v) (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) (hda : G.degree a = 3)
    {x y : Node G} (hx : a ∈ members G u v x) (hy : a ∈ members G u v y) :
    x = y := by
  cases x with
  | inl i =>
    rcases i with ⟨i⟩
    cases i <;> cases y with
    | inl j =>
      rcases j with ⟨j⟩
      cases j <;> simp only [members, Set.mem_singleton_iff] at hx hy
      all_goals first | rfl | exact (huv (hx.symm.trans hy)).elim |
        exact (huv (hy.symm.trans hx)).elim
    | inr s =>
      simp only [members, Set.mem_singleton_iff] at hx hy
      subst a
      first | exact (center_not_mem_triangle G hdu hcu s hy).elim |
        exact (center_not_mem_triangle G hdv hcv s hy).elim
  | inr s =>
    cases y with
    | inl j =>
      rcases j with ⟨j⟩
      cases j <;> simp only [members, Set.mem_singleton_iff] at hx hy
      all_goals subst a
      all_goals first | exact (center_not_mem_triangle G hdu hcu s hx).elim |
        exact (center_not_mem_triangle G hdv hcv s hx).elim
    | inr t =>
      exact congrArg Sum.inr (triangle_eq_of_degree_three G hG hda s t hx hy)

/-- A connector carries two actual ports; equal ports are shared triangle vertices,
and unequal ports are original edges outside triangles. -/
def Connector {V : Type u} (G : SimpleGraph V) (u v : V)
    (x y : Node G) (a b : V) : Prop :=
  x ≠ y ∧ a ∈ members G u v x ∧ b ∈ members G u v y ∧
    (a = b ∨ NontriangleEdge G a b)

example {V : Type u} (G : SimpleGraph V) (u v : V)
    (x y : Node G) (a b : V) : Connector G u v x y a b ↔
      x ≠ y ∧ a ∈ members G u v x ∧ b ∈ members G u v y ∧
        (a = b ∨ NontriangleEdge G a b) := Iff.rfl

/-- Reversing a connector exchanges its actual ports. -/
theorem Connector.symm {V : Type u} {G : SimpleGraph V} {u v a b : V}
    {x y : Node G} (h : Connector G u v x y a b) : Connector G u v y x b a := by
  refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
  rcases h.2.2.2 with he | he
  · exact Or.inl he.symm
  · exact Or.inr he.symm

/-- The actual two-center incidence graph records both shared vertices and ordinary edges. -/
def auxiliary {V : Type u} (G : SimpleGraph V) (u v : V) : SimpleGraph (Node G) where
  Adj x y := ∃ a b, Connector G u v x y a b
  symm := ⟨by
    intro x y h
    obtain ⟨a, b, he⟩ := h
    exact ⟨b, a, he.symm⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, b, he⟩ := h
    exact he.1 rfl⟩

example {V : Type u} (G : SimpleGraph V) (u v : V) (x y : Node G) :
    (auxiliary G u v).Adj x y ↔ ∃ a b, Connector G u v x y a b := Iff.rfl

/-- Every high noncenter vertex in a triangle belongs to a second triangle. -/
theorem other_triangle_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {a : V} (hn : ¬ Claw G a)
    (ha : 4 ≤ G.degree a) (s : Triangle G) (hs : a ∈ s.val) :
    ∃ t : Triangle G, t ≠ s ∧ a ∈ t.val := by
  classical
  have hfour : G.degree a = 4 := by
    rcases degree_three_or_four_of_not_claw G hG hn with h | h
    · omega
    · exact h
  obtain ⟨x, y, hxy, hxa, hya, eax, eay, exy, hmem⟩ := triangle_vertices G s hs
  let n := ((G.neighborFinset a).erase x).erase y
  have hmx : x ∈ G.neighborFinset a := (G.mem_neighborFinset a x).mpr eax
  have hmy : y ∈ (G.neighborFinset a).erase x := by simp [hxy.symm, eay]
  have hcx := Finset.card_erase_add_one hmx
  have hcy := Finset.card_erase_add_one hmy
  have hncard : n.card = 2 := by
    change (((G.neighborFinset a).erase x).erase y).card = 2
    change (G.neighborFinset a).card = 4 at hfour
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < n.card)
  have hb' : b ≠ y ∧ b ≠ x ∧ G.Adj a b := by simpa [n] using hb
  have hbs : b ∉ s.val := by
    intro h
    rcases (hmem b).mp h with hba | hbx | hby
    · exact hb'.2.2.ne hba.symm
    · exact hb'.2.1 hbx
    · exact hb'.1 hby
  obtain ⟨t, hta, htb⟩ := edge_in_triangle_of_degree_four G hG hfour hn hb'.2.2
  refine ⟨t, ?_, hta⟩
  intro hts
  subst t
  exact hbs htb


/-- Ports of an ordinary edge cannot be represented by the same auxiliary node. -/
theorem nodes_ne_of_ordinary_edge {V : Type u} (G : SimpleGraph V)
    {u v a b : V} {x y : Node G} (hx : a ∈ members G u v x)
    (hy : b ∈ members G u v y) (he : NontriangleEdge G a b) : x ≠ y := by
  intro hxy
  subst y
  cases x with
  | inl i =>
    rcases i with ⟨i⟩
    cases i <;> simp only [members, Set.mem_singleton_iff] at hx hy
    all_goals exact he.1.ne (hx.trans hy.symm)
  | inr s => exact he.2 s hx hy

/-- Every port of an actual triangle supplies a connector in the two-center graph. -/
theorem incidence_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (s : Triangle G) {a : V} (ha : a ∈ s.val) :
    ∃ y b, Connector G u v (.inr s) y a b := by
  have hau : a ≠ u := by
    intro he
    subst a
    exact center_not_mem_triangle G hdu hcu s ha
  have hav : a ≠ v := by
    intro he
    subst a
    exact center_not_mem_triangle G hdv hcv s ha
  rcases degree_three_or_four G hG hCenters hau hav with hd | hd
  · obtain ⟨b, he, _⟩ := TriangleIncidence.ordinary_neighbor_exists_unique G hG hd s ha
    obtain ⟨y, hy⟩ := members_cover G hG hCenters b
    exact ⟨y, b, nodes_ne_of_ordinary_edge G ha hy he, ha, hy, Or.inr he⟩
  · obtain ⟨t, hts, ht⟩ := other_triangle_exists G hG
      (not_claw_of_ne_centers G hCenters hau hav) (by omega) s ha
    refine ⟨.inr t, a, ?_, ha, ht, Or.inl rfl⟩
    intro he
    exact hts (Sum.inr.inj he).symm

/-- Every edge at a cubic root is ordinary and is represented by an auxiliary connector. -/
theorem root_incidence_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v b : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hdu : G.degree u = 3) (heb : G.Adj u b) :
    ∃ y, Connector G u v (.inl ⟨false⟩) y u b := by
  have he : NontriangleEdge G u b := by
    refine ⟨heb, ?_⟩
    intro s hs
    exact (center_not_mem_triangle G hdu hcu s hs).elim
  obtain ⟨y, hy⟩ := members_cover G hG hCenters b
  exact ⟨y, nodes_ne_of_ordinary_edge G rfl hy he, rfl, hy, Or.inr he⟩

/-- Every pair of two-center auxiliary nodes has uniquely determined actual ports. -/
theorem connector_ports_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} {x y : Node G} {a b c d : V}
    (h : Connector G u v x y a b) (h' : Connector G u v x y c d) :
    a = c ∧ b = d := by
  rcases h with ⟨hxy, ha, hb, hk⟩
  rcases h' with ⟨_, hc, hd, hk'⟩
  cases x with
  | inl i =>
    have hac : a = c := by
      rcases i with ⟨i⟩
      cases i <;> exact ha.trans hc.symm
    subst c
    cases y with
    | inl j =>
      rcases j with ⟨j⟩
      cases j <;> exact ⟨rfl, hb.trans hd.symm⟩
    | inr t =>
      rcases hk with hab | eab <;> rcases hk' with had | ead
      · exact ⟨rfl, hab.symm.trans had⟩
      · exact (ead.2 t (hab.symm ▸ hb) hd).elim
      · exact (eab.2 t (had.symm ▸ hd) hb).elim
      · exact ⟨rfl, ordinary_same_start G t hb hd eab ead⟩
  | inr s =>
    cases y with
    | inl j =>
      have hbd : b = d := by
        rcases j with ⟨j⟩
        cases j <;> exact hb.trans hd.symm
      subst d
      rcases hk with hab | eab <;> rcases hk' with hcb | ecb
      · exact ⟨hab.trans hcb.symm, rfl⟩
      · exact (ecb.2 s hc (hab ▸ ha)).elim
      · exact (eab.2 s ha (hcb ▸ hc)).elim
      · exact ⟨ordinary_same_start G s ha hc eab.symm ecb.symm, rfl⟩
    | inr t =>
      rcases hk with hab | eab <;> rcases hk' with hcd | ecd
      · subst b
        subst d
        have hac : a = c := by
          by_contra hnac
          exact hxy (congrArg Sum.inr
            (triangle_eq_of_two_common_vertices G hG s t hnac ha hc hb hd))
        exact ⟨hac, hac⟩
      · subst b
        exact (false_of_shared_vertex_and_ordinary G hG s t ha hb hc hd ecd).elim
      · subst d
        exact (false_of_shared_vertex_and_ordinary G hG s t hc hd ha hb eab).elim
      · exact ordinary_parallel G hG s t ha hc hb hd eab ecd

/-- A shared port cannot be cubic; its distinct nodes would otherwise coincide. -/
theorem zero_port_not_cubic {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v a : V} (huv : u ≠ v) (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    {x y : Node G} (h : Connector G u v x y a a) : G.degree a ≠ 3 := by
  intro hd
  exact h.1 (member_node_unique G hG huv hcu hcv hdu hdv hd h.2.1 h.2.2.1)

/-- At a triangle, an actual port determines a unique connector target. -/
theorem connector_neighbor_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    {s : Triangle G} {y z : Node G} {a b c : V}
    (h : Connector G u v (.inr s) y a b)
    (h' : Connector G u v (.inr s) z a c) : y = z := by
  have hau : a ≠ u := by
    intro he
    subst a
    exact center_not_mem_triangle G hdu hcu s h.2.1
  have hav : a ≠ v := by
    intro he
    subst a
    exact center_not_mem_triangle G hdv hcv s h.2.1
  rcases h.2.2.2 with hab | eab <;> rcases h'.2.2.2 with hac | eac
  · subst b
    subst c
    cases y with
    | inl i =>
      rcases i with ⟨i⟩
      cases i
      · exact (hau h.2.2.1).elim
      · exact (hav h.2.2.1).elim
    | inr t =>
      cases z with
      | inl i =>
        rcases i with ⟨i⟩
        cases i
        · exact (hau h'.2.2.1).elim
        · exact (hav h'.2.2.1).elim
      | inr r =>
        rcases at_most_two_triangles G hG
          (not_claw_of_ne_centers G hCenters hau hav) s t r
          h.2.1 h.2.2.1 h'.2.2.1 with hst | hsr | htr
        · exact (h.1 (congrArg Sum.inr hst)).elim
        · exact (h'.1 (congrArg Sum.inr hsr)).elim
        · exact congrArg Sum.inr htr
  · subst b
    exact (zero_port_not_cubic G hG huv hcu hcv hdu hdv h
      (ordinary_endpoint_degree_three G hG hCenters hdu hdv eac)).elim
  · subst c
    exact (zero_port_not_cubic G hG huv hcu hcv hdu hdv h'
      (ordinary_endpoint_degree_three G hG hCenters hdu hdv eab)).elim
  · have hda := ordinary_endpoint_degree_three G hG hCenters hdu hdv eab
    obtain ⟨d, _, huniq⟩ := TriangleIncidence.ordinary_neighbor_exists_unique G hG hda s h.2.1
    have hbc : b = c := (huniq b eab).trans (huniq c eac).symm
    subst c
    exact member_node_unique G hG huv hcu hcv hdu hdv
      (ordinary_endpoint_degree_three G hG hCenters hdu hdv eab.symm) h.2.2.1 h'.2.2.1

example {V : Type u} (G : SimpleGraph V) : Nonempty (Node G) :=
  ⟨.inl ⟨false⟩⟩

example :
    let r : Fin 8 → Fin 8 → Prop := fun a b =>
      (a.val, b.val) ∈ [(0, 1), (0, 2), (0, 5), (1, 3), (1, 6), (2, 3),
        (2, 4), (3, 4), (4, 7), (5, 6), (5, 7), (6, 7)]
    let G := SimpleGraph.fromRel r
    letI : DecidableRel G.Adj := fun a b =>
      show Decidable (a ≠ b ∧ (r a b ∨ r b a)) from inferInstance
    (0 : Fin 8) ≠ 1 ∧ Claw G 0 ∧ Claw G 1 ∧
      (∀ w, Claw G w → w = 0 ∨ w = 1) ∧
      (∀ w, G.degree w = 3) ∧
      (∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) := by
  intro r G
  letI : DecidableRel G.Adj := fun a b =>
    show Decidable (a ≠ b ∧ (r a b ∨ r b a)) from inferInstance
  dsimp only [Claw]
  decide

/-- Every edge at the second cubic root is ordinary and represented in the auxiliary. -/
theorem second_root_incidence_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v b : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcv : Claw G v) (hdv : G.degree v = 3) (heb : G.Adj v b) :
    ∃ y, Connector G u v (.inl ⟨true⟩) y v b := by
  have he : NontriangleEdge G v b := by
    refine ⟨heb, ?_⟩
    intro s hs
    exact (center_not_mem_triangle G hdv hcv s hs).elim
  obtain ⟨y, hy⟩ := members_cover G hG hCenters b
  exact ⟨y, nodes_ne_of_ordinary_edge G rfl hy he, rfl, hy, Or.inr he⟩

end Erdos64.TwoCubicClawCentersQuotient
