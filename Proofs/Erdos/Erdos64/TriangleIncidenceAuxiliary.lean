import Erdos.Erdos64.TriangleIncidenceTriangles

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

/-- The auxiliary carrier consists of the root and the original actual triangles. -/
abbrev Node {V : Type u} (G : SimpleGraph V) := Option (Triangle G)

example {V : Type u} (G : SimpleGraph V) : Node G = Option (Triangle G) := rfl

/-- Original vertices represented by a node: the root represents `v`, and a
triangle node represents its three vertices. -/
def members {V : Type u} (G : SimpleGraph V) (v : V) : Node G → Set V
  | none => {v}
  | some s => s.val

example {V : Type u} (G : SimpleGraph V) (v a : V) :
    a ∈ members G v none ↔ a = v := Iff.rfl

example {V : Type u} (G : SimpleGraph V) (v a : V) (s : Triangle G) :
    a ∈ members G v (some s) ↔ a ∈ s.val := Iff.rfl

/-- An ordinary connector is an original edge which belongs to no actual triangle. -/
def NontriangleEdge {V : Type u} (G : SimpleGraph V) (a b : V) : Prop :=
  G.Adj a b ∧ ∀ s : Triangle G, a ∈ s.val → b ∉ s.val

example {V : Type u} (G : SimpleGraph V) (a b : V) :
    NontriangleEdge G a b ↔
      G.Adj a b ∧ ¬ ∃ s : Triangle G, a ∈ s.val ∧ b ∈ s.val := by
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    rintro ⟨s, ha, hb⟩
    exact hn s ha hb
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    intro s ha hb
    exact hn ⟨s, ha, hb⟩

/-- Ordinary connector edges are symmetric. -/
theorem NontriangleEdge.symm {V : Type u} {G : SimpleGraph V} {a b : V}
    (h : NontriangleEdge G a b) : NontriangleEdge G b a := by
  refine ⟨h.1.symm, ?_⟩
  intro s hb ha
  exact h.2 s ha hb

/-- A connector carries its two original ports. Equal ports represent an off-root
shared vertex or a root-star incidence; unequal ports represent an ordinary edge. -/
def Connector {V : Type u} (G : SimpleGraph V) (v : V)
    (x y : Node G) (a b : V) : Prop :=
  x ≠ y ∧ a ∈ members G v x ∧ b ∈ members G v y ∧
    ((a = b ∧ (a ≠ v ∨ x = none ∨ y = none)) ∨
      ((a ≠ v ∨ x = none) ∧ (b ≠ v ∨ y = none) ∧ NontriangleEdge G a b))

example {V : Type u} (G : SimpleGraph V) (v : V)
    (x y : Node G) (a b : V) :
    Connector G v x y a b ↔
      x ≠ y ∧ a ∈ members G v x ∧ b ∈ members G v y ∧
        ((a = b ∧ (a ≠ v ∨ x = none ∨ y = none)) ∨
          ((a ≠ v ∨ x = none) ∧ (b ≠ v ∨ y = none) ∧ NontriangleEdge G a b)) := Iff.rfl

/-- Reversing a connector exchanges its two ports. -/
theorem Connector.symm {V : Type u} {G : SimpleGraph V} {v : V}
    {x y : Node G} {a b : V} (h : Connector G v x y a b) :
    Connector G v y x b a := by
  refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
  rcases h.2.2.2 with ⟨hab, hkind⟩ | ⟨hav, hbv, hedge⟩
  · refine Or.inl ⟨hab.symm, ?_⟩
    rcases hkind with hav | hx | hy
    · exact Or.inl (hab ▸ hav)
    · exact Or.inr (Or.inr hx)
    · exact Or.inr (Or.inl hy)
  · exact Or.inr ⟨hbv, hav, hedge.symm⟩

/-- The simple triangle-incidence graph records ordinary connectors and zero
connectors, rather than induced adjacency of representative original vertices. -/
def auxiliary {V : Type u} (G : SimpleGraph V) (v : V) : SimpleGraph (Node G) where
  Adj x y := ∃ a b, Connector G v x y a b
  symm := ⟨by
    intro x y h
    obtain ⟨a, b, hab⟩ := h
    exact ⟨b, a, hab.symm⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, b, hab⟩ := h
    exact hab.1 rfl⟩

example {V : Type u} (G : SimpleGraph V) (v : V) (x y : Node G) :
    (auxiliary G v).Adj x y ↔ ∃ a b, Connector G v x y a b := Iff.rfl

/-- An endpoint different from the unique claw center of an ordinary connector
has original degree three. -/
theorem ordinary_endpoint_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a b : V} (hu : ∀ w, Claw G w → w = v) (ha : a ≠ v)
    (hedge : NontriangleEdge G a b) : G.degree a = 3 := by
  rcases degree_three_or_four_off_center G hG hu ha with hthree | hfour
  · exact hthree
  · obtain ⟨s, hsa, hsb⟩ := edge_in_triangle_of_degree_four G hG hfour
      (fun hc => ha (hu a hc)) hedge.1
    exact (hedge.2 s hsa hsb).elim

/-- Each cubic vertex of an actual triangle has exactly one ordinary connector. -/
theorem ordinary_neighbor_exists_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {a : V} (ha : G.degree a = 3) (s : Triangle G) (hsa : a ∈ s.val) :
    ∃ b, NontriangleEdge G a b ∧ ∀ c, NontriangleEdge G a c → c = b := by
  classical
  obtain ⟨x, y, hxy, hxa, hya, eax, eay, exy, hmem⟩ := triangle_vertices G s hsa
  let t := ((G.neighborFinset a).erase x).erase y
  have hmx : x ∈ G.neighborFinset a := (G.mem_neighborFinset a x).mpr eax
  have hmy : y ∈ (G.neighborFinset a).erase x := by simp [hxy.symm, eay]
  have hcx := Finset.card_erase_add_one hmx
  have hcy := Finset.card_erase_add_one hmy
  have ht : t.card = 1 := by
    change (((G.neighborFinset a).erase x).erase y).card = 1
    change (G.neighborFinset a).card = 3 at ha
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  have hb' : b ≠ y ∧ b ≠ x ∧ G.Adj a b := by simpa [t] using hb
  have hordinary : NontriangleEdge G a b := by
    refine ⟨hb'.2.2, ?_⟩
    intro r hra hrb
    have heq := triangle_eq_of_degree_three G hG ha r s hra hsa
    subst r
    rcases (hmem b).mp hrb with hba | hbx | hby
    · exact hb'.2.2.ne hba.symm
    · exact hb'.2.1 hbx
    · exact hb'.1 hby
  refine ⟨b, hordinary, ?_⟩
  intro c hc
  have hneighbors := neighbors_eq_claw_leaves G ha hxy hb'.2.1.symm hb'.1.symm
    eax eay hb'.2.2
  rcases (hneighbors c).mp hc.1 with hcx | hcy | hcb
  · exact (hc.2 s hsa ((hmem c).mpr (Or.inr (Or.inl hcx)))).elim
  · exact (hc.2 s hsa ((hmem c).mpr (Or.inr (Or.inr hcy)))).elim
  · exact hcb

end Erdos64.TriangleIncidence
