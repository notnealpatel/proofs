import Erdos.Erdos64.TriangleIncidenceLocal
import Erdos.Erdos64.TriangleIncidenceModel

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

/-- An actual three-vertex clique of the original graph. -/
abbrev Triangle {V : Type u} (G : SimpleGraph V) :=
  {s : Finset V // G.IsNClique 3 s}

example {V : Type u} (G : SimpleGraph V) :
    Triangle G = {s : Finset V // G.IsNClique 3 s} := rfl

/-- The actual triangle carrier is finite. -/
noncomputable instance triangleFintype {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Fintype (Triangle G) := Fintype.ofFinite _

/-- Removing a specified vertex from an actual triangle leaves its two other vertices. -/
theorem triangle_vertices {V : Type u} (G : SimpleGraph V)
    (s : Triangle G) {x : V} (hx : x ∈ s.val) :
    ∃ a b, a ≠ b ∧ a ≠ x ∧ b ≠ x ∧
      G.Adj x a ∧ G.Adj x b ∧ G.Adj a b ∧
      ∀ y, y ∈ s.val ↔ y = x ∨ y = a ∨ y = b := by
  classical
  have hcard : (s.val.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, s.property.card_eq]
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ s.val.erase x := by rw [heq]; simp
  have hb : b ∈ s.val.erase x := by rw [heq]; simp
  have ha' := Finset.mem_erase.mp ha
  have hb' := Finset.mem_erase.mp hb
  have hset : s.val = insert x ({a, b} : Finset V) := by
    rw [← heq, Finset.insert_erase hx]
  refine ⟨a, b, hab, ha'.1, hb'.1, ?_, ?_, ?_, ?_⟩
  · exact s.property.isClique hx ha'.2 ha'.1.symm
  · exact s.property.isClique hx hb'.2 hb'.1.symm
  · exact s.property.isClique ha'.2 hb'.2 hab
  · intro y
    rw [hset]
    simp

/-- A cubic original vertex belongs to at most one actual triangle. -/
theorem triangle_eq_of_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x : V} (hx : G.degree x = 3) (s t : Triangle G)
    (hs : x ∈ s.val) (ht : x ∈ t.val) : s = t := by
  classical
  obtain ⟨a, b, hab, hax, hbx, hxa, hxb, eab, hmems⟩ := triangle_vertices G s hs
  obtain ⟨c, d, hcd, hcx, hdx, hxc, hxd, ecd, hmemt⟩ := triangle_vertices G t ht
  have hpairs := neighbor_edge_eq_at_degree_three G hG hx hxa hxb eab hxc hxd ecd
  apply Subtype.ext
  ext y
  rw [hmems, hmemt]
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · tauto

/-- Distinct actual triangles cannot contain two common vertices. -/
theorem triangle_eq_of_two_common_vertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (s t : Triangle G) {x y : V} (hxy : x ≠ y)
    (hsx : x ∈ s.val) (hsy : y ∈ s.val)
    (htx : x ∈ t.val) (hty : y ∈ t.val) : s = t := by
  classical
  obtain ⟨a, b, hab, hax, hbx, hxa, hxb, eab, hmems⟩ := triangle_vertices G s hsx
  obtain ⟨c, d, hcd, hcx, hdx, hxc, hxd, ecd, hmemt⟩ := triangle_vertices G t htx
  have hy1 : y = a ∨ y = b := by
    rcases (hmems y).mp hsy with hyx | hya | hyb
    · exact (hxy hyx.symm).elim
    · exact Or.inl hya
    · exact Or.inr hyb
  have hy2 : y = c ∨ y = d := by
    rcases (hmemt y).mp hty with hyx | hyc | hyd
    · exact (hxy hyx.symm).elim
    · exact Or.inl hyc
    · exact Or.inr hyd
  rcases hy1 with rfl | rfl <;> rcases hy2 with h | h
  · subst c
    have hbd' : b = d := neighborhood_matching G hG hxb hxa hxd eab.symm ecd
    subst d
    apply Subtype.ext
    ext z
    rw [hmems, hmemt]
  · subst d
    have hbc' : b = c := neighborhood_matching G hG hxb hxa hxc eab.symm ecd.symm
    subst c
    apply Subtype.ext
    ext z
    rw [hmems, hmemt]
    tauto
  · subst c
    have had' : a = d := neighborhood_matching G hG hxa hxb hxd eab ecd
    subst d
    apply Subtype.ext
    ext z
    rw [hmems, hmemt]
    tauto
  · subst d
    have hac' : a = c := neighborhood_matching G hG hxa hxb hxc eab ecd.symm
    subst c
    apply Subtype.ext
    ext z
    rw [hmems, hmemt]

/-- Three pairwise adjacent original vertices determine an actual triangle. -/
theorem exists_triangle_of_edges {V : Type u} (G : SimpleGraph V)
    {x a b : V} (ha : G.Adj x a) (hb : G.Adj x b) (hab : G.Adj a b) :
    ∃ s : Triangle G, x ∈ s.val ∧ a ∈ s.val ∧ b ∈ s.val := by
  classical
  let s : Finset V := {x, a, b}
  have hs : G.IsNClique 3 s := by
    constructor
    · intro z hz w hw hzw
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz hw
      rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      all_goals simp_all [SimpleGraph.adj_comm]
    · simp [s, ha.ne, hb.ne, hab.ne]
  exact ⟨⟨s, hs⟩, by simp [s], by simp [s], by simp [s]⟩

/-- Every incident edge at a degree-four nonclaw vertex belongs to a triangle. -/
theorem edge_in_triangle_of_degree_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x y : V} (hx : G.degree x = 4) (hn : ¬ Claw G x) (hy : G.Adj x y) :
    ∃ s : Triangle G, x ∈ s.val ∧ y ∈ s.val := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
    ha, hb, hc, hd, eab, ecd, hneighbors, hnac, hnad, hnbc, hnbd⟩ :=
    exists_two_triangles_at_degree_four G hG hx hn
  obtain ⟨s, hsx, hsa, hsb⟩ := exists_triangle_of_edges G ha hb eab
  obtain ⟨t, htx, htc, htd⟩ := exists_triangle_of_edges G hc hd ecd
  rcases (hneighbors y).mp hy with rfl | rfl | rfl | rfl
  · exact ⟨s, hsx, hsa⟩
  · exact ⟨s, hsx, hsb⟩
  · exact ⟨t, htx, htc⟩
  · exact ⟨t, htx, htd⟩

/-- Under HIGH and a high distinguished root, every triangle has two distinct cubic
vertices different from the root. -/
theorem two_low_vertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} (hv : 4 ≤ G.degree v) (s : Triangle G) :
    ∃ a b, a ∈ s.val ∧ b ∈ s.val ∧ a ≠ b ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ a ≠ v ∧ b ≠ v := by
  classical
  have hpos : 0 < s.val.card := by rw [s.property.card_eq]; decide
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨a, b, hab, hax, hbx, ha, hb, eab, hmem⟩ := triangle_vertices G s hx
  have hma : a ∈ s.val := (hmem a).mpr (Or.inr (Or.inl rfl))
  have hmb : b ∈ s.val := (hmem b).mpr (Or.inr (Or.inr rfl))
  have hne : ∀ z, G.degree z = 3 → z ≠ v := by
    intro z hz h
    subst z
    omega
  by_cases hxh : 4 ≤ G.degree x
  · have hal := neighbor_degree_three G hG hHIGH hxh ha
    have hbl := neighbor_degree_three G hG hHIGH hxh hb
    exact ⟨a, b, hma, hmb, hab, hal, hbl, hne a hal, hne b hbl⟩
  by_cases hah : 4 ≤ G.degree a
  · have hxl := neighbor_degree_three G hG hHIGH hah ha.symm
    have hbl := neighbor_degree_three G hG hHIGH hah eab
    exact ⟨x, b, hx, hmb, hbx.symm, hxl, hbl, hne x hxl, hne b hbl⟩
  · have hxmin := hG.degree_ge_three x
    have hamin := hG.degree_ge_three a
    have hxl : G.degree x = 3 := by omega
    have hal : G.degree a = 3 := by omega
    exact ⟨x, a, hx, hma, hax.symm, hxl, hal, hne x hxl, hne a hal⟩

end Erdos64.TriangleIncidence
