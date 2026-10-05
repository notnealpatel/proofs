import Erdos.Erdos64.TriangleIncidenceAuxiliary

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

/-- Two vertices of a triangle have a third vertex different from both. -/
theorem triangle_third {V : Type u} (G : SimpleGraph V) (s : Triangle G)
    {a b : V} (ha : a ∈ s.val) (hb : b ∈ s.val) (hab : a ≠ b) :
    ∃ c, c ∈ s.val ∧ c ≠ a ∧ c ≠ b := by
  obtain ⟨c, d, hcd, hca, hda, eac, ead, ecd, hmem⟩ := triangle_vertices G s ha
  rcases (hmem b).mp hb with hba | hbc | hbd
  · exact (hab hba.symm).elim
  · refine ⟨d, (hmem d).mpr (Or.inr (Or.inr rfl)), hda, ?_⟩
    exact fun hdb => hcd (hbc.symm.trans hdb.symm)
  · refine ⟨c, (hmem c).mpr (Or.inr (Or.inl rfl)), hca, ?_⟩
    exact fun hcb => hcd (hcb.trans hbd)

/-- Two ordinary edges with a common endpoint cannot end in the same triangle. -/
theorem ordinary_same_start {V : Type u} (G : SimpleGraph V) (s : Triangle G)
    {a b c : V} (hb : b ∈ s.val) (hc : c ∈ s.val)
    (eab : NontriangleEdge G a b) (eac : NontriangleEdge G a c) : b = c := by
  by_contra hbc
  have ebc := s.property.isClique hb hc hbc
  obtain ⟨t, hta, htb, htc⟩ := exists_triangle_of_edges G eab.1 eac.1 ebc
  exact eab.2 t hta htb

/-- Distinct actual triangles admit at most one ordinary connector between them. -/
theorem ordinary_parallel {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (s t : Triangle G) {a b c d : V}
    (ha : a ∈ s.val) (hc : c ∈ s.val) (hb : b ∈ t.val) (hd : d ∈ t.val)
    (eab : NontriangleEdge G a b) (ecd : NontriangleEdge G c d) :
    a = c ∧ b = d := by
  have hac : a = c := by
    by_contra hnac
    have hnbd : b ≠ d := by
      intro hbd
      subst d
      exact hnac (ordinary_same_start G s ha hc eab.symm ecd.symm)
    have hnad : a ≠ d := by
      intro had
      subst d
      exact eab.2 t hd hb
    have hnbc : b ≠ c := by
      intro hbc
      subst c
      exact eab.2 s ha hc
    exact not_four_cycle G hG eab.1.ne hnad hnac hnbd hnbc ecd.1.ne.symm
      eab.1 (t.property.isClique hb hd hnbd) ecd.1.symm
      (s.property.isClique hc ha (Ne.symm hnac))
  subst c
  exact ⟨rfl, ordinary_same_start G t hb hd eab ecd⟩

/-- A shared triangle vertex and an ordinary connector between its triangles
would yield an original four-cycle. -/
theorem false_of_shared_vertex_and_ordinary {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (s t : Triangle G) {a b c : V}
    (hsa : a ∈ s.val) (hta : a ∈ t.val)
    (hsb : b ∈ s.val) (htc : c ∈ t.val) (ebc : NontriangleEdge G b c) : False := by
  have hac : a ≠ c := by
    intro h
    subst c
    exact ebc.2 s hsb hsa
  have hab : a ≠ b := by
    intro h
    subst b
    exact ebc.2 t hta htc
  obtain ⟨d, hsd, hda, hdb⟩ := triangle_third G s hsa hsb hab
  have hdc : d ≠ c := by
    intro h
    subst c
    exact ebc.2 s hsb hsd
  exact not_four_cycle G hG hda.symm hab hac hdb hdc ebc.1.ne
    (s.property.isClique hsa hsd hda.symm)
    (s.property.isClique hsd hsb hdb) ebc.1
    (t.property.isClique htc hta hac.symm)

/-- Every pair of auxiliary nodes has uniquely determined connector ports. -/
theorem connector_ports_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} {x y : Node G} {a b c d : V}
    (h : Connector G v x y a b) (h' : Connector G v x y c d) :
    a = c ∧ b = d := by
  rcases h with ⟨hxy, ha, hb, hkind⟩
  rcases h' with ⟨hxy', hc, hd, hkind'⟩
  cases x with
  | none =>
    have hav : a = v := ha
    have hcv : c = v := hc
    subst a
    subst c
    cases y with
    | none => exact (hxy rfl).elim
    | some t =>
      change b ∈ t.val at hb
      change d ∈ t.val at hd
      rcases hkind with ⟨hvb, hz⟩ | ⟨hav, hbv, eab⟩ <;>
        rcases hkind' with ⟨hvd, hz'⟩ | ⟨hcv, hdv, ecd⟩
      · exact ⟨rfl, hvb.symm.trans hvd⟩
      · exact (ecd.2 t (hvb.symm ▸ hb) hd).elim
      · exact (eab.2 t (hvd.symm ▸ hd) hb).elim
      · exact ⟨rfl, ordinary_same_start G t hb hd eab ecd⟩
  | some s =>
    change a ∈ s.val at ha
    change c ∈ s.val at hc
    cases y with
    | none =>
      have hbv : b = v := hb
      have hdv : d = v := hd
      subst b
      subst d
      rcases hkind with ⟨hav, hz⟩ | ⟨hav', hbv, eab⟩ <;>
        rcases hkind' with ⟨hcv, hz'⟩ | ⟨hcv', hdv, ecd⟩
      · exact ⟨hav.trans hcv.symm, rfl⟩
      · exact (ecd.2 s hc (hav ▸ ha)).elim
      · exact (eab.2 s ha (hcv ▸ hc)).elim
      · exact ⟨ordinary_same_start G s ha hc eab.symm ecd.symm, rfl⟩
    | some t =>
      change b ∈ t.val at hb
      change d ∈ t.val at hd
      rcases hkind with ⟨hab, hz⟩ | ⟨hav, hbv, eab⟩ <;>
        rcases hkind' with ⟨hcd, hz'⟩ | ⟨hcv, hdv, ecd⟩
      · subst b
        subst d
        have hac : a = c := by
          by_contra hnac
          have hst := triangle_eq_of_two_common_vertices G hG s t hnac ha hc hb hd
          exact hxy (congrArg some hst)
        exact ⟨hac, hac⟩
      · subst b
        exact (false_of_shared_vertex_and_ordinary G hG s t ha hb hc hd ecd).elim
      · subst d
        exact (false_of_shared_vertex_and_ordinary G hG s t hc hd ha hb eab).elim
      · exact ordinary_parallel G hG s t ha hc hb hd eab ecd

end Erdos64.TriangleIncidence
