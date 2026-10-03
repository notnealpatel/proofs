import Erdos.Erdos64.SubcubicFunnelLocal

set_option autoImplicit false
namespace Erdos64.SubcubicFunnel
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- Reversing a four-path swaps its endpoint neighbors and retains its middle. -/
def Path4.reverse (p : Path4 G s t) : Path4 G t s :=
  ⟨p.last, p.middle, p.first, p.edge₃.symm, p.edge₂.symm, p.edge₁.symm,
    p.edge₀.symm, by
      have hd := p.distinct
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hd ⊢
      grind⟩

/-- Reversal preserves the internal vertex set. -/
theorem Path4.reverse_internal (p : Path4 G s t) (z : V) :
    p.reverse.Internal z ↔ p.Internal z := by
  simp [Path4.Internal, Path4.reverse, or_comm, or_left_comm]

/-- Reversal preserves the clean-path condition. -/
theorem Path4.reverse_clean (p : Path4 G s t) : p.reverse.Clean ↔ p.Clean := by
  simp [Path4.Clean, Path4.reverse, and_comm]

/-- In a subcubic C4-free graph, an endpoint neighborhood has at most one
partner edge. This derives the cardinal restriction from standard degree. -/
theorem partner_edge_eq [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    {r a b c d : V} (ha : G.Adj r a) (hb : G.Adj r b) (hab : G.Adj a b)
    (hc : G.Adj r c) (hd : G.Adj r d) (hcd : G.Adj c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  by_cases hca : c = a
  · subst c
    exact Or.inl ⟨rfl, partner_unique h4 ha hd hb hcd hab⟩
  by_cases hcb : c = b
  · subst c
    exact Or.inr ⟨rfl, partner_unique h4 hb hd ha hcd hab.symm⟩
  have hn : [a, b, c].Nodup := by simp [hab.ne, Ne.symm hca, Ne.symm hcb]
  have he := neighbor_eq_of_three hdeg hn ha hb hc hd
  rcases he with hda | hdb | hdc
  · subst d
    have hbc := partner_unique h4 ha hb hc hab hcd.symm
    exact False.elim (hcb hbc.symm)
  · subst d
    have hac := partner_unique h4 hb ha hc hab.symm hcd.symm
    exact False.elim (hca hac.symm)
  · exact False.elim (hcd.ne hdc.symm)

/-- A fixed left detour contains the two A-vertices of every left detour. -/
theorem left_partner_eq [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (p q : Path4 G s t) (hp : G.Adj s p.middle) (hq : G.Adj s q.middle) :
    (q.first = p.first ∧ q.middle = p.middle) ∨
      (q.first = p.middle ∧ q.middle = p.first) :=
  partner_edge_eq hdeg h4 p.edge₀ hp p.edge₁ q.edge₀ hq q.edge₁

/-- A fixed right detour contains the two C-vertices of every right detour. -/
theorem right_partner_eq [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (p q : Path4 G s t) (hp : G.Adj t p.middle) (hq : G.Adj t q.middle) :
    (q.middle = p.middle ∧ q.last = p.last) ∨
      (q.middle = p.last ∧ q.last = p.middle) :=
  partner_edge_eq hdeg h4 hp p.edge₃.symm p.edge₂ hq q.edge₃.symm q.edge₂

/-- A right detour whose A-vertex is outside a fixed left partner pair forces
all detours through the fixed left path's C-vertex. This is the finite interval
Helly step, written directly in matching coordinates. -/
theorem common_last_of_outside_right [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (hclean : ∀ q : Path4 G s t, ¬ q.Clean)
    (p r : Path4 G s t) (hp : G.Adj s p.middle) (hr : G.Adj t r.middle)
    (hf : r.first ≠ p.first) (hm : r.first ≠ p.middle) :
    ∀ q : Path4 G s t, q.Internal p.last := by
  have hsepall := (separation_of_edist hsep).2.2
  have hsp := p.edge₀
  have htp := p.edge₃.symm
  have hsr := r.edge₀
  have htr := r.edge₃.symm
  obtain ⟨z, hzp, hzr⟩ := p.internal_intersects h8 r
  have hmatch : p.last = r.middle → p.middle = r.first := by
    intro he
    exact cross_unique_left h4 hsep hr hp r.edge₀ (he ▸ p.edge₂) r.edge₁
  have hl : p.last = r.last := by
    have hs₁ := hsepall p.first
    have hs₂ := hsepall p.middle
    have hs₃ := hsepall r.first
    simp only [Path4.Internal] at hzp hzr
    grind
  intro q
  rcases q.classes hsep with hc | hleft | hright
  · exact False.elim (hclean q hc)
  · have hpair := left_partner_eq hdeg h4 p q hp hleft.1
    obtain ⟨w, hwq, hwr⟩ := q.internal_intersects h8 r
    have hqs := q.edge₀
    have hqt := q.edge₃.symm
    have hmatchq : q.last = r.middle → q.middle = r.first := by
      intro he
      exact cross_unique_left h4 hsep hr hleft.1 r.edge₀ (he ▸ q.edge₂) r.edge₁
    have hs₁ := hsepall q.first
    have hs₂ := hsepall q.middle
    have hs₃ := hsepall r.first
    simp only [Path4.Internal] at hwq hwr ⊢
    grind
  · have hpair := right_partner_eq hdeg h4 r q hr hright.1
    simp only [Path4.Internal]
    grind

/-- The zero-clean path family has an endpoint-neighbor funnel, in the presence
of a left detour. The proof is the reviewed linear-forest Helly argument reduced
to the two possible partner orientations. -/
theorem zero_clean_funnel_of_left [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (hclean : ∀ q : Path4 G s t, ¬ q.Clean)
    (p : Path4 G s t) (hp : G.Adj s p.middle) :
    ∃ z, (G.Adj s z ∨ G.Adj t z) ∧ ∀ q : Path4 G s t, q.Internal z := by
  classical
  by_cases hout : ∃ r : Path4 G s t, G.Adj t r.middle ∧
      r.first ≠ p.first ∧ r.first ≠ p.middle
  · obtain ⟨r, hr, hf, hm⟩ := hout
    exact ⟨p.last, Or.inr p.edge₃.symm,
      common_last_of_outside_right hdeg h4 h8 hsep hclean p r hp hr hf hm⟩
  have hin : ∀ r : Path4 G s t, G.Adj t r.middle →
      r.first = p.first ∨ r.first = p.middle := by grind
  by_cases hex : ∃ r : Path4 G s t, G.Adj t r.middle
  · obtain ⟨r, hr⟩ := hex
    have hrin := hin r hr
    refine ⟨r.first, Or.inl r.edge₀, ?_⟩
    intro q
    rcases q.classes hsep with hc | hleft | hright
    · exact False.elim (hclean q hc)
    · have hpair := left_partner_eq hdeg h4 p q hp hleft.1
      simp only [Path4.Internal]
      grind
    · have hqin := hin q hright.1
      have hpair := right_partner_eq hdeg h4 r q hr hright.1
      have heq : q.first = r.first := by
        by_contra hne
        have ha : G.Adj r.first q.first := by
          have hedge := p.edge₁
          have hedgesym := p.edge₁.symm
          grind
        rcases hpair with he | he
        · have hqedge : G.Adj q.first r.middle := he.1 ▸ q.edge₁
          exact hne (cross_unique_left h4 hsep hr q.edge₀ r.edge₀ hqedge r.edge₁)
        · have hqedge : G.Adj r.last q.first := (he.1 ▸ q.edge₁).symm
          have hdist := r.distinct
          simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hdist
          have hnefl : r.first ≠ r.last := by grind
          have hmid := common_neighbor_unique h4 hnefl r.edge₁ r.edge₂.symm ha hqedge
          have hsepall := (separation_of_edist hsep).2.2 q.first
          have hs := q.edge₀
          grind
      exact Or.inl heq.symm
  · refine ⟨p.first, Or.inl p.edge₀, ?_⟩
    intro q
    rcases q.classes hsep with hc | hleft | hright
    · exact False.elim (hclean q hc)
    · have hpair := left_partner_eq hdeg h4 p q hp hleft.1
      simp only [Path4.Internal]
      grind
    · exact False.elim (hex ⟨q, hright.1⟩)

/-- Reversing twice restores the original tuple. -/
theorem Path4.reverse_reverse (p : Path4 G s t) : p.reverse.reverse = p := by
  cases p
  rfl

/-- Without clean paths, the full nonempty family has an endpoint-neighbor
funnel. Reversal covers the all-right initial orientation. -/
theorem zero_clean_funnel [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (hclean : ∀ q : Path4 G s t, ¬ q.Clean) (p : Path4 G s t) :
    ∃ z, (G.Adj s z ∨ G.Adj t z) ∧ ∀ q : Path4 G s t, q.Internal z := by
  rcases p.classes hsep with hc | hl | hr
  · exact False.elim (hclean p hc)
  · exact zero_clean_funnel_of_left hdeg h4 h8 hsep hclean p hl.1
  · have hsep' : 2 < G.edist t s := by simpa only [G.edist_comm] using hsep
    have hclean' : ∀ q : Path4 G t s, ¬ q.Clean := by
      intro q hq
      exact hclean q.reverse (q.reverse_clean.mpr hq)
    obtain ⟨z, hz, hall⟩ := zero_clean_funnel_of_left hdeg h4 h8 hsep' hclean'
      p.reverse hr.1
    refine ⟨z, hz.symm, fun q => ?_⟩
    exact (q.reverse_internal z).mp (hall q.reverse)

end Erdos64.SubcubicFunnel
