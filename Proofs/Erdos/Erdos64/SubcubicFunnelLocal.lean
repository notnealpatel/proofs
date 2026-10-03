import Erdos.Erdos64.SubcubicFunnelFoundation

set_option autoImplicit false

namespace Erdos64.SubcubicFunnel
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- Three distinct known neighbors exhaust a subcubic vertex's neighbors.
The exhaustion is derived from the standard finite neighbor-finset cardinality. -/
theorem neighbor_eq_of_three [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) {v a b c x : V}
    (hd : [a, b, c].Nodup) (ha : G.Adj v a) (hb : G.Adj v b)
    (hc : G.Adj v c) (hx : G.Adj v x) : x = a ∨ x = b ∨ x = c := by
  classical
  let ns : Finset V := [a, b, c].toFinset
  have hn : ns.card = 3 := by
    simpa [ns] using List.toFinset_card_of_nodup hd
  have hs : ns ⊆ G.neighborFinset v := by
    intro y hy
    simp only [ns, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · simpa using ha
    · simpa using hb
    · simpa using hc
  have he : ns = G.neighborFinset v := Finset.eq_of_subset_of_card_le hs (by
    change G.degree v ≤ ns.card
    rw [hn]
    exact hdeg v)
  have hxns : x ∈ ns := he.symm ▸ (show x ∈ G.neighborFinset v by simpa using hx)
  simpa [ns] using hxns

/-- Distance greater than two excludes an endpoint edge and any common neighbor.
The ENat distance remains meaningful even before reachability is supplied. -/
theorem separation_of_edist (h : 2 < G.edist s t) :
    s ≠ t ∧ ¬ G.Adj s t ∧ ∀ v, ¬ (G.Adj s v ∧ G.Adj t v) := by
  obtain ⟨hne, hedge, hcommon⟩ := G.two_lt_edist_iff.mp h
  refine ⟨hne, hedge, ?_⟩
  intro v hv
  have hm : v ∈ G.commonNeighbors s t := hv
  rw [hcommon] at hm
  exact hm

/-- C4-freeness makes edges inside an endpoint neighborhood a matching. -/
theorem partner_unique (h4 : ¬ HasSimpleCycleOfLength G 4)
    {r x a b : V} (hrx : G.Adj r x) (hra : G.Adj r a) (hrb : G.Adj r b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b :=
  common_neighbor_unique h4 hrx.ne hra hxa hrb hxb

/-- C4-freeness makes all edges between the two endpoint neighborhoods a matching
at the first side. -/
theorem cross_unique_right (h4 : ¬ HasSimpleCycleOfLength G 4)
    (hsep : 2 < G.edist s t) {a c d : V} (hsa : G.Adj s a)
    (htc : G.Adj t c) (htd : G.Adj t d) (hac : G.Adj a c) (had : G.Adj a d) : c = d := by
  have hat : a ≠ t := by
    intro he
    subst a
    exact (separation_of_edist hsep).2.1 hsa
  exact common_neighbor_unique h4 hat hac htc had htd

/-- C4-freeness makes all edges between the two endpoint neighborhoods a matching
at the last side. -/
theorem cross_unique_left (h4 : ¬ HasSimpleCycleOfLength G 4)
    (hsep : 2 < G.edist s t) {a b c : V} (htc : G.Adj t c)
    (hsa : G.Adj s a) (hsb : G.Adj s b) (hac : G.Adj a c) (hbc : G.Adj b c) : a = b := by
  have hcs : c ≠ s := by
    intro he
    subst c
    exact (separation_of_edist hsep).2.1 htc.symm
  exact common_neighbor_unique h4 hcs hac.symm hsa hbc.symm hsb

/-- A clean path has its middle outside both endpoint neighborhoods. -/
def Path4.Clean (p : Path4 G s t) : Prop :=
  ¬ G.Adj s p.middle ∧ ¬ G.Adj t p.middle

/-- Ground truth for the clean classification: its middle is outside the two
endpoints and their neighborhoods. The endpoint exclusions follow from simplicity. -/
theorem Path4.clean_iff (p : Path4 G s t) :
    p.Clean ↔ p.middle ≠ s ∧ p.middle ≠ t ∧
      ¬ G.Adj s p.middle ∧ ¬ G.Adj t p.middle := by
  have hi := (p.internal_iff p.middle).mp (Or.inr (Or.inl rfl))
  simp only [Path4.Clean]
  exact ⟨fun hc => ⟨hi.2.1, hi.2.2, hc⟩, fun hc => hc.2.2⟩

/-- Every four-path is either clean, a left detour, or a right detour; distance
separation prevents the middle from lying in both endpoint neighborhoods. -/
theorem Path4.classes (hsep : 2 < G.edist s t) (p : Path4 G s t) :
    p.Clean ∨ (G.Adj s p.middle ∧ ¬ G.Adj t p.middle) ∨
      (G.Adj t p.middle ∧ ¬ G.Adj s p.middle) := by
  have hn := (separation_of_edist hsep).2.2 p.middle
  simp only [Path4.Clean]
  tauto

/-- A path middle has only one possible first endpoint neighbor. -/
theorem first_unique (h4 : ¬ HasSimpleCycleOfLength G 4)
    (p : Path4 G s t) {a : V}
    (hsa : G.Adj s a) (ham : G.Adj a p.middle) : a = p.first := by
  have hms := ((p.internal_iff p.middle).mp (Or.inr (Or.inl rfl))).2.1
  exact common_neighbor_unique h4 hms ham.symm hsa p.edge₁.symm p.edge₀

/-- A path middle has only one possible last endpoint neighbor. -/
theorem last_unique (h4 : ¬ HasSimpleCycleOfLength G 4)
    (p : Path4 G s t) {c : V}
    (htc : G.Adj t c) (hmc : G.Adj p.middle c) : c = p.last := by
  have hmt := ((p.internal_iff p.middle).mp (Or.inr (Or.inl rfl))).2.2
  exact common_neighbor_unique h4 hmt hmc htc p.edge₂ p.edge₃.symm

/-- Equal endpoint-neighbor labels force equal middle vertices. -/
theorem middle_unique (h4 : ¬ HasSimpleCycleOfLength G 4)
    (p q : Path4 G s t) (hf : p.first = q.first) (hl : p.last = q.last) :
    p.middle = q.middle := by
  have hfl : p.first ≠ p.last := by
    have hd := p.distinct
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hd
    grind
  exact common_neighbor_unique h4 hfl p.edge₁ p.edge₂.symm
    (hf ▸ q.edge₁) (hl ▸ q.edge₂.symm)

/-- Pairwise intersection of clean paths reduces to intersection of their
bipartite endpoint-neighbor labels. -/
theorem clean_labels_intersect (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p q : Path4 G s t) (hp : p.Clean) (hq : q.Clean) :
    p.first = q.first ∨ p.last = q.last := by
  obtain ⟨z, hz, hzq⟩ := p.internal_intersects h8 q
  have hsp := p.edge₀
  have hsq := q.edge₀
  have htp := p.edge₃.symm
  have htq := q.edge₃.symm
  have hsep_p := (separation_of_edist hsep).2.2 p.first
  have hsep_q := (separation_of_edist hsep).2.2 q.first
  have hmid : p.middle = q.middle → p.first = q.first := by
    intro he
    exact (first_unique h4 p q.edge₀ (he.symm ▸ q.edge₁)).symm
  simp only [Path4.Internal] at hz hzq
  simp only [Path4.Clean] at hp hq
  grind

/-- The labels of all clean paths form a star: all have the first neighbor of a
fixed clean path, or all have its last neighbor. This quantifies over the entire
path family, not a selected collection. -/
theorem clean_star (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p : Path4 G s t) (hp : p.Clean) :
    (∀ q : Path4 G s t, q.Clean → q.first = p.first) ∨
    (∀ q : Path4 G s t, q.Clean → q.last = p.last) := by
  classical
  by_cases hf : ∀ q : Path4 G s t, q.Clean → q.first = p.first
  · exact Or.inl hf
  · right
    push Not at hf
    obtain ⟨q, hq, hqf⟩ := hf
    have hqp := clean_labels_intersect h4 h8 hsep q p hq hp
    have hql : q.last = p.last := hqp.resolve_left hqf
    intro r hr
    have hrp := clean_labels_intersect h4 h8 hsep r p hr hp
    have hrq := clean_labels_intersect h4 h8 hsep r q hr hq
    rcases hrp with hrf | hrl
    · rcases hrq with hrfq | hrlq
      · exact False.elim (hqf (hrfq.symm.trans hrf))
      · exact hrlq.trans hql
    · exact hrl

/-- The A-middle of a left detour cannot be the first vertex of a clean path:
its three detour neighbors exhaust its degree. -/
theorem left_middle_ne_clean_first [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (p q : Path4 G s t)
    (hp : p.Clean) (hq : G.Adj s q.middle) : q.middle ≠ p.first := by
  intro he
  have hd : [s, q.first, q.last].Nodup := by
    have hqdist := q.distinct
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hqdist ⊢
    grind
  have hed : G.Adj q.middle p.middle := he ▸ p.edge₁
  have hn := neighbor_eq_of_three hdeg hd hq.symm q.edge₁.symm q.edge₂ hed
  have hpm := ((p.internal_iff p.middle).mp (Or.inr (Or.inl rfl))).2.1
  have hqs := q.edge₀
  have hqt := q.edge₃.symm
  simp only [Path4.Clean] at hp
  grind

/-- The C-middle of a right detour cannot be the last vertex of a clean path. -/
theorem right_middle_ne_clean_last [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (p q : Path4 G s t)
    (hp : p.Clean) (hq : G.Adj t q.middle) : q.middle ≠ p.last := by
  intro he
  have hd : [t, q.first, q.last].Nodup := by
    have hqdist := q.distinct
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hqdist ⊢
    grind
  have hed : G.Adj q.middle p.middle := he ▸ p.edge₂.symm
  have hn := neighbor_eq_of_three hdeg hd hq.symm q.edge₁.symm q.edge₂ hed
  have hpm := ((p.internal_iff p.middle).mp (Or.inr (Or.inl rfl))).2.2
  have hqs := q.edge₀
  have hqt := q.edge₃.symm
  simp only [Path4.Clean] at hp
  grind

/-- Every path meets a clean path at an equal first or equal last neighbor.
Detour-middle saturation is the extra ingredient beyond the clean-star lemma. -/
theorem labels_intersect_clean [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p q : Path4 G s t) (hp : p.Clean) :
    q.first = p.first ∨ q.last = p.last := by
  obtain ⟨z, hzp, hzq⟩ := p.internal_intersects h8 q
  have hsp := p.edge₀
  have hsq := q.edge₀
  have htp := p.edge₃.symm
  have htq := q.edge₃.symm
  have hsep_p := (separation_of_edist hsep).2.2 p.first
  have hsep_q := (separation_of_edist hsep).2.2 q.first
  have hqmfirst : q.middle ≠ p.first := by
    intro he
    exact left_middle_ne_clean_first hdeg p q hp (he.symm ▸ p.edge₀) he
  have hqmlast : q.middle ≠ p.last := by
    intro he
    exact right_middle_ne_clean_last hdeg p q hp (he.symm ▸ p.edge₃.symm) he
  have hmid : p.middle = q.middle → q.first = p.first := by
    intro he
    exact first_unique h4 p q.edge₀ (he.symm ▸ q.edge₁)
  simp only [Path4.Internal] at hzp hzq
  simp only [Path4.Clean] at hp
  grind

/-- Two clean paths with equal first and different last vertices force that
first vertex into every path in the full family. -/
theorem common_first_of_two_clean [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p q : Path4 G s t) (hp : p.Clean) (hq : q.Clean)
    (hf : p.first = q.first) (hl : p.last ≠ q.last) :
    ∀ r : Path4 G s t, r.Internal p.first := by
  intro r
  have hrp := labels_intersect_clean hdeg h4 h8 hsep p r hp
  have hrq := labels_intersect_clean hdeg h4 h8 hsep q r hq
  simp only [Path4.Internal]
  grind

/-- The symmetric two-clean star conclusion, centered at the last neighbor. -/
theorem common_last_of_two_clean [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p q : Path4 G s t) (hp : p.Clean) (hq : q.Clean)
    (hl : p.last = q.last) (hf : p.first ≠ q.first) :
    ∀ r : Path4 G s t, r.Internal p.last := by
  intro r
  have hrp := labels_intersect_clean hdeg h4 h8 hsep p r hp
  have hrq := labels_intersect_clean hdeg h4 h8 hsep q r hq
  simp only [Path4.Internal]
  grind

end Erdos64.SubcubicFunnel
