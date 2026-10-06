import Erdos.Erdos64.TriangleIncidencePorts
import Erdos.Erdos64.TriangleIncidenceCycleLiftFinal

set_option autoImplicit false

namespace Erdos64.ClawFreeMinimalExclusion

open SimpleGraph UniqueCubicClawCenter TriangleIncidence TriangleIncidenceLocal

universe u

/-- A zero-root connector joins two distinct actual triangles at a shared vertex
or across an original edge belonging to no triangle. -/
def Connector {V : Type u} (G : SimpleGraph V) (s t : Triangle G) (a b : V) : Prop :=
  s ≠ t ∧ a ∈ s.val ∧ b ∈ t.val ∧ (a = b ∨ NontriangleEdge G a b)

example {V : Type u} (G : SimpleGraph V) (s t : Triangle G) (a b : V) :
    Connector G s t a b ↔
      s ≠ t ∧ a ∈ s.val ∧ b ∈ t.val ∧ (a = b ∨ NontriangleEdge G a b) := Iff.rfl

/-- Reversing a zero-root connector reverses its original labels. -/
theorem Connector.symm {V : Type u} {G : SimpleGraph V} {s t : Triangle G}
    {a b : V} (h : Connector G s t a b) : Connector G t s b a := by
  refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
  exact h.2.2.2.elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)

/-- The zero-root kernel has all actual triangles as its vertices. -/
def kernel {V : Type u} (G : SimpleGraph V) : SimpleGraph (Triangle G) where
  Adj s t := ∃ a b, Connector G s t a b
  symm := ⟨by
    rintro s t ⟨a, b, h⟩
    exact ⟨b, a, h.symm⟩⟩
  loopless := ⟨by
    rintro s ⟨a, b, h⟩
    exact h.1 rfl⟩

example {V : Type u} (G : SimpleGraph V) (s t : Triangle G) :
    (kernel G).Adj s t ↔ ∃ a b, Connector G s t a b := Iff.rfl

/-- Ordinary edges at nonclaw vertices have cubic endpoints. -/
theorem ordinary_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x) {a b : V} (he : NontriangleEdge G a b) :
    G.degree a = 3 := by
  exact ordinary_endpoint_degree_three G hG
    (v := b) (fun x hx => (hNoClaw x hx).elim) he.1.ne he

/-- Every vertex of a claw-free counterexample lies in an actual triangle. -/
theorem vertex_triangle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x) (a : V) : ∃ s : Triangle G, a ∈ s.val := by
  rcases degree_three_or_four_of_not_claw G hG (hNoClaw a) with hthree | hfour
  · obtain ⟨x, y, hx, hy, hxy, huniq⟩ :=
      exists_unique_triangle_at_degree_three G hG hthree (hNoClaw a)
    obtain ⟨s, hsa, hsx, hsy⟩ := exists_triangle_of_edges G hx hy hxy
    exact ⟨s, hsa⟩
  · obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw,
        hx, hy, hz, hw, exy, ezw, hneighbors, hnxz, hnxw, hnyz, hnyw⟩ :=
      exists_two_triangles_at_degree_four G hG hfour (hNoClaw a)
    obtain ⟨s, hsa, hsx, hsy⟩ := exists_triangle_of_edges G hx hy exy
    exact ⟨s, hsa⟩

/-- A high vertex in an actual triangle belongs to a second actual triangle. -/
theorem second_triangle {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x) {a : V} (ha : 4 ≤ G.degree a)
    (s : Triangle G) (hs : a ∈ s.val) : ∃ t : Triangle G, t ≠ s ∧ a ∈ t.val := by
  obtain ⟨x, y, hxy, hxa, hya, hx, hy, exy, hmem⟩ := triangle_vertices G s hs
  exact other_triangle_exists G hG (v := x)
    (fun z hz => (hNoClaw z hz).elim) hxa.symm ha s hs

/-- Every triangle port has a zero-root connector to another actual triangle. -/
theorem connector_exists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x) (s : Triangle G) {a : V} (hs : a ∈ s.val) :
    ∃ t b, Connector G s t a b := by
  rcases degree_three_or_four_of_not_claw G hG (hNoClaw a) with hthree | hfour
  · obtain ⟨b, he, huniq⟩ := ordinary_neighbor_exists_unique G hG hthree s hs
    obtain ⟨t, ht⟩ := vertex_triangle G hG hNoClaw b
    have hst : s ≠ t := by
      intro hst
      subst t
      exact he.2 s hs ht
    exact ⟨t, b, hst, hs, ht, Or.inr he⟩
  · obtain ⟨t, hts, ht⟩ := second_triangle G hG hNoClaw (by omega) s hs
    exact ⟨t, a, hts.symm, hs, ht, Or.inl rfl⟩

/-- Between two triangle nodes, connector labels are uniquely determined. -/
theorem connector_labels_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {s t : Triangle G} {a b c d : V}
    (h : Connector G s t a b) (h' : Connector G s t c d) : a = c ∧ b = d := by
  rcases h.2.2.2 with hab | he <;> rcases h'.2.2.2 with hcd | he'
  · subst b
    subst d
    have hac : a = c := by
      by_contra hn
      exact h.1 (triangle_eq_of_two_common_vertices G hG s t hn
        h.2.1 h'.2.1 h.2.2.1 h'.2.2.1)
    exact ⟨hac, hac⟩
  · subst b
    exact (false_of_shared_vertex_and_ordinary G hG s t
      h.2.1 h.2.2.1 h'.2.1 h'.2.2.1 he').elim
  · subst d
    exact (false_of_shared_vertex_and_ordinary G hG s t
      h'.2.1 h'.2.2.1 h.2.1 h.2.2.1 he).elim
  · exact ordinary_parallel G hG s t h.2.1 h'.2.1 h.2.2.1 h'.2.2.1 he he'

/-- A shared-vertex connector cannot use a cubic original vertex. -/
theorem zero_not_cubic {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {s t : Triangle G} {a : V} (h : Connector G s t a a) : G.degree a ≠ 3 := by
  intro ha
  exact h.1 (triangle_eq_of_degree_three G hG ha s t h.2.1 h.2.2.1)

/-- At a fixed triangle port the connector target is unique. -/
theorem connector_target_unique {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x) {s t r : Triangle G} {a b c : V}
    (h : Connector G s t a b) (h' : Connector G s r a c) : t = r := by
  rcases h.2.2.2 with hab | he <;> rcases h'.2.2.2 with hac | he'
  · subst b
    subst c
    rcases at_most_two_triangles G hG (hNoClaw a) s t r
      h.2.1 h.2.2.1 h'.2.2.1 with hst | hsr | htr
    · exact (h.1 hst).elim
    · exact (h'.1 hsr).elim
    · exact htr
  · subst b
    exact (zero_not_cubic G hG h (ordinary_degree_three G hG hNoClaw he')).elim
  · subst c
    exact (zero_not_cubic G hG h' (ordinary_degree_three G hG hNoClaw he)).elim
  · have ha := ordinary_degree_three G hG hNoClaw he
    obtain ⟨d, hed, huniq⟩ := ordinary_neighbor_exists_unique G hG ha s h.2.1
    have hbc : b = c := (huniq b he).trans (huniq c he').symm
    subst c
    exact triangle_eq_of_degree_three G hG
      (ordinary_degree_three G hG hNoClaw he.symm) t r h.2.2.1 h'.2.2.1

/-- Each actual triangle has two distinct cubic labels under HIGH. -/
theorem two_cubic_labels {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (s : Triangle G) :
    ∃ a b, a ∈ s.val ∧ b ∈ s.val ∧ a ≠ b ∧ G.degree a = 3 ∧ G.degree b = 3 := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property.card_eq]; decide)
  obtain ⟨a, b, hab, hax, hbx, ha, hb, eab, hmem⟩ := triangle_vertices G s hx
  have hma : a ∈ s.val := (hmem a).mpr (Or.inr (Or.inl rfl))
  have hmb : b ∈ s.val := (hmem b).mpr (Or.inr (Or.inr rfl))
  by_cases hxh : 4 ≤ G.degree x
  · exact ⟨a, b, hma, hmb, hab, neighbor_degree_three G hG hHIGH hxh ha,
      neighbor_degree_three G hG hHIGH hxh hb⟩
  by_cases hah : 4 ≤ G.degree a
  · exact ⟨x, b, hx, hmb, hbx.symm, neighbor_degree_three G hG hHIGH hah ha.symm,
      neighbor_degree_three G hG hHIGH hah eab⟩
  · have hxmin := hG.degree_ge_three x
    have hamin := hG.degree_ge_three a
    exact ⟨x, a, hx, hma, hax.symm, by omega, by omega⟩

/-- The triangle kernel is strictly smaller than the original graph under HIGH. -/
theorem card_kernel_lt {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hT : Nonempty (Triangle G)) : Fintype.card (Triangle G) < Fintype.card V := by
  classical
  choose a b ha hb hab hda hdb using two_cubic_labels G hG hHIGH
  have hinj : Function.Injective a := by
    intro s t hst
    have hat : a s ∈ t.val := hst ▸ ha t
    exact triangle_eq_of_degree_three G hG (hda s) s t (ha s) hat
  obtain ⟨t⟩ := hT
  have hnot : ¬ Function.Surjective a := by
    intro hsurj
    obtain ⟨s, hs⟩ := hsurj (b t)
    have hbs : b t ∈ s.val := hs ▸ ha s
    have hst := triangle_eq_of_degree_three G hG (hdb t) s t hbs (hb t)
    subst s
    exact hab t hs
  exact Fintype.card_lt_of_injective_not_surjective a hinj hnot

/-- A kernel incidence chooses its unique original label; nonedges use a default label. -/
noncomputable def port {V : Type u} (G : SimpleGraph V) (v : V)
    (s t : Triangle G) : V := by
  classical
  exact if h : (kernel G).Adj s t then Classical.choose h else v

example {V : Type u} (G : SimpleGraph V) (v : V) (s t : Triangle G)
    (h : ¬ (kernel G).Adj s t) : port G v s t = v := by
  simp [port, h]

/-- The chosen label agrees with every connector witness. -/
theorem port_eq {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (v : V) {s t : Triangle G} {a b : V} (h : Connector G s t a b) :
    port G v s t = a := by
  have hadj : (kernel G).Adj s t := ⟨a, b, h⟩
  rw [port, dif_pos hadj]
  exact (connector_labels_unique G hG
    (Classical.choose_spec (Classical.choose_spec hadj)) h).1

/-- Both chosen labels form the actual connector. -/
theorem port_connector {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (v : V) {s t : Triangle G} (h : (kernel G).Adj s t) :
    Connector G s t (port G v s t) (port G v t s) := by
  obtain ⟨a, b, hab⟩ := h
  rw [port_eq G hG v hab, port_eq G hG v hab.symm]
  exact hab

/-- Every actual triangle has precisely three distinct kernel incidences. -/
theorem kernel_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x) (v : V) (s : Triangle G) :
    letI : DecidableRel (kernel G).Adj := Classical.decRel _
    (kernel G).degree s = 3 := by
  classical
  let f : (kernel G).neighborSet s → {a : V // a ∈ s.val} := fun t =>
    ⟨port G v s t.val, (port_connector G hG v t.property).2.1⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro t r heq
      apply Subtype.ext
      have he : port G v s t.val = port G v s r.val := congrArg Subtype.val heq
      have ht := port_connector G hG v t.property
      have hr := port_connector G hG v r.property
      rw [← he] at hr
      exact connector_target_unique G hG hNoClaw ht hr
    · intro a
      obtain ⟨t, b, ht⟩ := connector_exists G hG hNoClaw s a.property
      exact ⟨⟨t, a.val, b, ht⟩, Subtype.ext (port_eq G hG v ht)⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f hbij)
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe, s.property.card_eq] at hcard
  exact hcard

/-- Adding an isolated vertex is the standard graph map along `Option.some`. -/
def addIsolated {A : Type u} (Q : SimpleGraph A) : SimpleGraph (Option A) :=
  Q.map Option.some

example {A : Type u} (Q : SimpleGraph A) (a b : A) :
    (addIsolated Q).Adj (some a) (some b) ↔ Q.Adj a b := by
  simp only [addIsolated]
  rw [SimpleGraph.map_adj' Option.some]
  constructor
  · rintro ⟨hne, x, y, hxy, hx, hy⟩
    cases Option.some.inj hx
    cases Option.some.inj hy
    exact hxy
  · intro hab
    exact ⟨fun he => hab.ne (Option.some.inj he), a, b, hab, rfl, rfl⟩

private theorem isolated_none_left {A : Type u} (Q : SimpleGraph A) (a : Option A) :
    ¬ (addIsolated Q).Adj none a := by
  simp only [addIsolated]
  rw [SimpleGraph.map_adj' Option.some]
  simp

private theorem isolated_none_right {A : Type u} (Q : SimpleGraph A) (a : Option A) :
    ¬ (addIsolated Q).Adj a none := by
  simp only [addIsolated]
  rw [SimpleGraph.map_adj' Option.some]
  simp

private theorem isolated_some_adj {A : Type u} (Q : SimpleGraph A) (a b : A) :
    (addIsolated Q).Adj (some a) (some b) ↔ Q.Adj a b := by
  simp only [addIsolated]
  rw [SimpleGraph.map_adj' Option.some]
  constructor
  · rintro ⟨hne, x, y, hxy, hx, hy⟩
    cases Option.some.inj hx
    cases Option.some.inj hy
    exact hxy
  · intro hab
    exact ⟨fun he => hab.ne (Option.some.inj he), a, b, hab, rfl, rfl⟩

/-- The isolated extension sends real vertices to their `some` labels. -/
def someHom {A : Type u} (Q : SimpleGraph A) : Q →g addIsolated Q where
  toFun := Option.some
  map_rel' := by
    intro a b hab
    exact (isolated_some_adj Q a b).mpr hab

example {A : Type u} (Q : SimpleGraph A) (a : A) : someHom Q a = some a := rfl

/-- The rootless triangle representation becomes the accepted generic lift model
by adjoining isolated dummy vertices to both graphs. -/
noncomputable def isolatedModel {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hNoClaw : ∀ x, ¬ Claw G x)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (v : V) : Model (addIsolated G) (addIsolated (kernel G)) none none := by
  classical
  let emb : V ↪ Option V := ⟨Option.some, Option.some_injective V⟩
  let tri : Option (Triangle G) → Finset (Option V) := fun x =>
    match x with
    | none => ∅
    | some s => s.val.map emb
  let prt : Option (Triangle G) → Option (Triangle G) → Option V := fun x y =>
    match x, y with
    | some s, some t => some (port G v s t)
    | _, _ => none
  have hmem : ∀ (s : Triangle G) (a : V), some a ∈ tri (some s) ↔ a ∈ s.val := by
    intro s a
    simp [tri, emb]
  have hnone : ∀ s : Triangle G, none ∉ tri (some s) := by
    intro s
    simp [tri, emb]
  refine {
    triangle := tri
    root_triangle := rfl
    triangle_clique := ?_
    port := prt
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
    | some s => exact s.property.map (f := emb)
  · intro y hy
    exact (isolated_none_left (kernel G) y hy).elim
  · intro x y hx hxy
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      cases y with
      | none => exact (isolated_none_right (kernel G) (some s) hxy).elim
      | some t =>
        exact (hmem s _).mpr
          (port_connector G hG v ((isolated_some_adj (kernel G) s t).mp hxy)).2.1
  · intro x y z hx hxy hxz heq
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      cases y with
      | none => exact (isolated_none_right (kernel G) (some s) hxy).elim
      | some t =>
        cases z with
        | none => exact (isolated_none_right (kernel G) (some s) hxz).elim
        | some r =>
          have ht := port_connector G hG v ((isolated_some_adj (kernel G) s t).mp hxy)
          have hr := port_connector G hG v ((isolated_some_adj (kernel G) s r).mp hxz)
          have he : port G v s t = port G v s r := Option.some.inj heq
          rw [← he] at hr
          exact congrArg some (connector_target_unique G hG hNoClaw ht hr)
  · intro x a hx ha
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      cases a with
      | none => exact (hnone s ha).elim
      | some a =>
        obtain ⟨t, b, ht⟩ := connector_exists G hG hNoClaw s ((hmem s a).mp ha)
        exact ⟨some t, (isolated_some_adj (kernel G) s t).mpr ⟨a, b, ht⟩,
          congrArg some (port_eq G hG v ht)⟩
  · intro x y hxy
    cases x with
    | none => exact (isolated_none_left (kernel G) y hxy).elim
    | some s =>
      cases y with
      | none => exact (isolated_none_right (kernel G) (some s) hxy).elim
      | some t =>
        have ht := port_connector G hG v ((isolated_some_adj (kernel G) s t).mp hxy)
        exact ht.2.2.2.elim (fun he => Or.inl (congrArg some he))
          (fun he => Or.inr ((isolated_some_adj G _ _).mpr he.1))
  · intro x y z hx hxy hzero hxz hzero'
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      cases y with
      | none => exact (isolated_none_right (kernel G) (some s) hxy).elim
      | some t =>
        cases z with
        | none => exact (isolated_none_right (kernel G) (some s) hxz).elim
        | some r =>
          have ht := port_connector G hG v ((isolated_some_adj (kernel G) s t).mp hxy)
          have hr := port_connector G hG v ((isolated_some_adj (kernel G) s r).mp hxz)
          have he : port G v s t = port G v t s := Option.some.inj hzero
          have he' : port G v s r = port G v r s := Option.some.inj hzero'
          rw [← he] at ht
          rw [← he'] at hr
          have hmint := hG.degree_ge_three (port G v s t)
          have hminr := hG.degree_ge_three (port G v s r)
          have hnt := zero_not_cubic G hG ht
          have hnr := zero_not_cubic G hG hr
          have hight : 4 ≤ G.degree (port G v s t) := by omega
          have highr : 4 ≤ G.degree (port G v s r) := by omega
          by_cases hp : port G v s t = port G v s r
          · rw [← hp] at hr
            exact congrArg some (connector_target_unique G hG hNoClaw ht hr)
          · exact (hHIGH _ _ hight highr (s.property.isClique ht.2.1 hr.2.1 hp)).elim
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      exact iff_of_false (hnone s) (fun h => isolated_none_left (kernel G) _ h.1)
  · intro x y a hx hy hxy hax hay
    cases x with
    | none => exact (hx rfl).elim
    | some s =>
      cases y with
      | none => exact (hy rfl).elim
      | some t =>
        cases a with
        | none => exact (hnone s hax).elim
        | some a =>
          have hst : s ≠ t := fun he => hxy (congrArg some he)
          have ht : Connector G s t a a :=
            ⟨hst, (hmem s a).mp hax, (hmem t a).mp hay, Or.inl rfl⟩
          exact Or.inl ⟨(isolated_some_adj (kernel G) s t).mpr ⟨a, a, ht⟩,
            congrArg some ((port_eq G hG v ht).trans (port_eq G hG v ht.symm).symm),
            congrArg some (port_eq G hG v ht)⟩
  · intro x y hx hzero hy hzero'
    exact (isolated_none_left (kernel G) x hx).elim

set_option backward.isDefEq.respectTransparency.types false in
/-- A cycle in the isolated extension descends to an original literal cycle,
with unchanged length; the induced-subgraph step excludes the dummy vertex. -/
theorem cycle_descends {V : Type u} (G : SimpleGraph V) {a : Option V}
    (p : (addIsolated G).Walk a a) (hp : p.IsCycle) :
    ∃ b, ∃ q : G.Walk b b, q.IsCycle ∧ q.length = p.length := by
  classical
  have ha : a ≠ none := by
    intro he
    subst a
    cases p with
    | nil => exact hp.ne_nil rfl
    | cons h p => exact isolated_none_left G _ h
  have hsupp : ∀ {x y : Option V} (w : (addIsolated G).Walk x y), x ≠ none →
      ∀ z ∈ w.support, z ≠ none := by
    intro x y w
    induction w with
    | nil =>
      intro hx z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hx
    | @cons x y z h w ih =>
      intro hx t ht
      have hy : y ≠ none := by
        intro he
        subst y
        exact isolated_none_right G x h
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
      rcases ht with he | ht
      · exact he ▸ hx
      · exact ih hy t ht
  let S : Set (Option V) := Set.range (@Option.some V)
  have hS : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    have hn := hsupp p ha x hx
    cases x with
    | none => exact (hn rfl).elim
    | some x => exact ⟨x, rfl⟩
  let w := p.induce S hS
  have hw : w.IsCycle := by
    dsimp only [w]
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    rw [SimpleGraph.Walk.map_induce]
    exact hp
  let e : S → V := fun x => Classical.choose x.property
  have he : ∀ x : S, some (e x) = x.val := fun x => Classical.choose_spec x.property
  let f : (addIsolated G).induce S →g G := {
    toFun := e
    map_rel' := by
      intro x y hxy
      have h : (addIsolated G).Adj (some (e x)) (some (e y)) := by
        rw [he x, he y]
        exact hxy
      exact (isolated_some_adj G _ _).mp h }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.val = some (e x) := (he x).symm
      _ = some (e y) := congrArg some hxy
      _ = y.val := he y
  refine ⟨f ⟨a, hS a p.start_mem_support⟩, w.map f,
    SimpleGraph.Walk.IsCycle.map hf hw, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  change (p.induce S hS).length = p.length
  have hlength : ∀ {x y : Option V} (q : (addIsolated G).Walk x y)
      (hq : ∀ z ∈ q.support, z ∈ S), (q.induce S hq).length = q.length := by
    intro x y q
    induction q with
    | nil => intro hq; rfl
    | cons h q ih =>
      intro hq
      simp only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.length_cons]
      rw [ih]
  exact hlength p hS

/-- Unrestricted smaller-order minimality and HIGH force a power-of-two cycle
in the original claw-free graph, without assuming that graph is cubic. -/
theorem hasPowerOfTwoCycle_original {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hNoClaw : ∀ x, ¬ Claw G x) : HasPowerOfTwoCycle G := by
  classical
  let v : V := Classical.choice inferInstance
  obtain ⟨s, hs⟩ := vertex_triangle G hG hNoClaw v
  letI : Nonempty (Triangle G) := ⟨s⟩
  letI : DecidableRel (kernel G).Adj := Classical.decRel _
  have hcard := card_kernel_lt G hG hHIGH inferInstance
  have hdegree : ∀ t, 3 ≤ (kernel G).degree t := by
    intro t
    exact (kernel_degree G hG hNoClaw v t).ge
  obtain ⟨n, hn, x, p, hp, hlen⟩ := hminimal (kernel G) hcard hdegree
  let D := isolatedModel G hG hNoClaw hHIGH v
  have hp' : (p.map (someHom (kernel G))).IsCycle :=
    SimpleGraph.Walk.IsCycle.map (Option.some_injective _) hp
  have hfour : 4 ≤ (p.map (someHom (kernel G))).length := by
    rw [SimpleGraph.Walk.length_map, hlen]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  obtain ⟨a, q, hq, hq_len⟩ := D.exists_doubled_cycle
    (p.map (someHom (kernel G))) hp' hfour
  obtain ⟨b, r, hr, hr_len⟩ := cycle_descends G q hq
  refine ⟨n + 1, by omega, b, r, hr, ?_⟩
  rw [hr_len, hq_len, SimpleGraph.Walk.length_map, hlen, pow_succ, Nat.mul_comm]

/-- A globally order-minimal counterexample with independent high-degree vertices
cannot have zero induced claw centers, even when the original graph is noncubic. -/
theorem false_of_no_claw_center {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hNoClaw : ∀ x, ¬ Claw G x) : False := by
  exact hG.not_hasPowerOfTwoCycle
    (hasPowerOfTwoCycle_original G hG hminimal hHIGH hNoClaw)

end Erdos64.ClawFreeMinimalExclusion
