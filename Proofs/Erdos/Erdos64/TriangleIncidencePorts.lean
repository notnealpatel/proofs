import Erdos.Erdos64.TriangleIncidenceSimple

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

private theorem distinct_other_vertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {s t : Triangle G} (hst : s ≠ t) {a x y : V}
    (hsa : a ∈ s.val) (hta : a ∈ t.val)
    (hsx : x ∈ s.val) (hty : y ∈ t.val) (hxa : x ≠ a) (hya : y ≠ a) : x ≠ y := by
  intro hxy
  subst y
  exact hst (triangle_eq_of_two_common_vertices G hG s t hxa.symm hsa hsx hta hty)

/-- A nonclaw original vertex belongs to at most two distinct actual triangles. -/
theorem at_most_two_triangles {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {a : V} (hn : ¬ Claw G a) (s t r : Triangle G)
    (hs : a ∈ s.val) (ht : a ∈ t.val) (hr : a ∈ r.val) :
    s = t ∨ s = r ∨ t = r := by
  classical
  by_contra hnot
  have hst : s ≠ t := fun h => hnot (Or.inl h)
  have hsr : s ≠ r := fun h => hnot (Or.inr (Or.inl h))
  have htr : t ≠ r := fun h => hnot (Or.inr (Or.inr h))
  obtain ⟨x, y, hxy, hxa, hya, eax, eay, exy, hmems⟩ := triangle_vertices G s hs
  obtain ⟨b, c, hbc, hba, hca, eab, eac, ebc, hmemt⟩ := triangle_vertices G t ht
  obtain ⟨d, e, hde, hda, hea, ead, eae, ede, hmemr⟩ := triangle_vertices G r hr
  have hsx := (hmems x).mpr (Or.inr (Or.inl rfl))
  have hsy := (hmems y).mpr (Or.inr (Or.inr rfl))
  have htb := (hmemt b).mpr (Or.inr (Or.inl rfl))
  have htc := (hmemt c).mpr (Or.inr (Or.inr rfl))
  have hrd := (hmemr d).mpr (Or.inr (Or.inl rfl))
  exact false_of_edge_and_three_other_neighbors G hG hn eax eay eab eac ead exy
    (distinct_other_vertices G hG hst hs ht hsy htb hya hba)
    (distinct_other_vertices G hG hst hs ht hsy htc hya hca)
    (distinct_other_vertices G hG hsr hs hr hsy hrd hya hda)
    (distinct_other_vertices G hG hst hs ht hsx htb hxa hba)
    (distinct_other_vertices G hG hst hs ht hsx htc hxa hca)
    (distinct_other_vertices G hG hsr hs hr hsx hrd hxa hda)
    hbc
    (distinct_other_vertices G hG htr ht hr htb hrd hba hda)
    (distinct_other_vertices G hG htr ht hr htc hrd hca hda)

/-- Every high noncenter vertex in a triangle belongs to a second triangle. -/
theorem other_triangle_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a : V} (hu : ∀ w, Claw G w → w = v) (hav : a ≠ v)
    (ha : 4 ≤ G.degree a) (s : Triangle G) (hs : a ∈ s.val) :
    ∃ t : Triangle G, t ≠ s ∧ a ∈ t.val := by
  classical
  have hn : ¬ Claw G a := fun hc => hav (hu a hc)
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

/-- Every cubic noncenter vertex lies in an actual triangle. -/
theorem cubic_triangle_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a : V} (hu : ∀ w, Claw G w → w = v) (hav : a ≠ v)
    (ha : G.degree a = 3) : ∃ s : Triangle G, a ∈ s.val := by
  obtain ⟨x, y, eax, eay, exy, huniq⟩ := exists_unique_triangle_at_degree_three G hG ha
    (fun hc => hav (hu a hc))
  obtain ⟨s, hsa, hsx, hsy⟩ := exists_triangle_of_edges G eax eay exy
  exact ⟨s, hsa⟩

/-- Every original vertex of an actual triangle supplies an auxiliary incidence. -/
theorem incidence_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hu : ∀ w, Claw G w → w = v)
    (s : Triangle G) {a : V} (hsa : a ∈ s.val) :
    ∃ y b, Connector G v (some s) y a b := by
  classical
  by_cases hav : a = v
  · subst a
    exact ⟨none, v, by
      refine ⟨by simp, hsa, rfl, Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩⟩⟩
  rcases degree_three_or_four_off_center G hG hu hav with hthree | hfour
  · obtain ⟨b, eab, huniq⟩ := ordinary_neighbor_exists_unique G hG hthree s hsa
    by_cases hbv : b = v
    · subst b
      exact ⟨none, v, by
        refine ⟨by simp, hsa, rfl, Or.inr ⟨Or.inl hav, Or.inr rfl, eab⟩⟩⟩
    · have hbl := ordinary_endpoint_degree_three G hG hu hbv eab.symm
      obtain ⟨t, htb⟩ := cubic_triangle_exists G hG hu hbv hbl
      have hst : s ≠ t := by
        intro h
        subst t
        exact eab.2 s hsa htb
      exact ⟨some t, b, by
        refine ⟨by simpa using hst, hsa, htb, Or.inr ⟨Or.inl hav, Or.inl hbv, eab⟩⟩⟩
  · obtain ⟨t, hts, hta⟩ := other_triangle_exists G hG hu hav (by omega) s hsa
    exact ⟨some t, a, by
      refine ⟨by simpa using hts.symm, hsa, hta, Or.inl ⟨rfl, Or.inl hav⟩⟩⟩

/-- A cubic nonroot original vertex can label only one auxiliary node. -/
theorem member_node_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a : V} (hav : a ≠ v) (ha : G.degree a = 3)
    {x y : Node G} (hx : a ∈ members G v x) (hy : a ∈ members G v y) : x = y := by
  cases x with
  | none => exact (hav hx).elim
  | some s =>
    cases y with
    | none => exact (hav hy).elim
    | some t => exact congrArg some (triangle_eq_of_degree_three G hG ha s t hx hy)

private theorem zero_target_of_root_port {V : Type u} (G : SimpleGraph V)
    {v : V} {s : Triangle G} {y : Node G}
    (h : Connector G v (some s) y v v)
    (hz : v ≠ v ∨ some s = none ∨ y = none) : y = none := by
  rcases hz with hbad | hbad | hy
  · exact (hbad rfl).elim
  · cases hbad
  · exact hy

private theorem zero_cubic_impossible {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a : V} (hav : a ≠ v) (ha : G.degree a = 3)
    {s : Triangle G} {y : Node G} (h : Connector G v (some s) y a a) : False := by
  have hnodes := member_node_unique G hG hav ha h.2.1 h.2.2.1
  exact h.1 hnodes

/-- Distinct incidences of a triangle have distinct original ports. -/
theorem connector_neighbor_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hu : ∀ w, Claw G w → w = v)
    {s : Triangle G} {y z : Node G} {a b c : V}
    (h : Connector G v (some s) y a b) (h' : Connector G v (some s) z a c) : y = z := by
  classical
  rcases h.2.2.2 with ⟨hab, hz⟩ | ⟨hav, hbv, eab⟩ <;>
    rcases h'.2.2.2 with ⟨hac, hz'⟩ | ⟨hav', hcv, eac⟩
  · subst b
    subst c
    by_cases hav : a = v
    · subst a
      exact (zero_target_of_root_port G h hz).trans (zero_target_of_root_port G h' hz').symm
    · cases y with
      | none => exact (hav h.2.2.1).elim
      | some t =>
        cases z with
        | none => exact (hav h'.2.2.1).elim
        | some r =>
          have hn : ¬ Claw G a := fun hc => hav (hu a hc)
          rcases at_most_two_triangles G hG hn s t r h.2.1 h.2.2.1 h'.2.2.1
            with hst | hsr | htr
          · exact (h.1 (congrArg some hst)).elim
          · exact (h'.1 (congrArg some hsr)).elim
          · exact congrArg some htr
  · subst b
    have hav'' : a ≠ v := by simpa using hav'
    have hal := ordinary_endpoint_degree_three G hG hu hav'' eac
    exact (zero_cubic_impossible G hG hav'' hal h).elim
  · subst c
    have hav'' : a ≠ v := by simpa using hav
    have hal := ordinary_endpoint_degree_three G hG hu hav'' eab
    exact (zero_cubic_impossible G hG hav'' hal h').elim
  · have hav'' : a ≠ v := by simpa using hav
    have hal := ordinary_endpoint_degree_three G hG hu hav'' eab
    obtain ⟨d, ead, huniq⟩ := ordinary_neighbor_exists_unique G hG hal s h.2.1
    have hbc : b = c := (huniq b eab).trans (huniq c eac).symm
    subst c
    by_cases hbv' : b = v
    · subst b
      have hy : y = none := by simpa using hbv
      have hz : z = none := by simpa using hcv
      exact hy.trans hz.symm
    · have hbl := ordinary_endpoint_degree_three G hG hu hbv' eab.symm
      exact member_node_unique G hG hbv' hbl h.2.2.1 h'.2.2.1

end Erdos64.TriangleIncidence
