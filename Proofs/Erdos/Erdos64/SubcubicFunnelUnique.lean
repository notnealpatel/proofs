import Erdos.Erdos64.SubcubicFunnelZero
import Erdos.Erdos64.SubcubicFunnelH7

set_option autoImplicit false
namespace Erdos64.SubcubicFunnel
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- Two paths avoiding opposite labels of a clean path must be left and right
detours, with a common cross edge. The alternatives are excluded by saturation,
matching uniqueness, or the genuine eight-cycle intersection lemma. -/
theorem clean_detours [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p l r : Path4 G s t) (hp : p.Clean)
    (hl : ¬ l.Internal p.last) (hr : ¬ r.Internal p.first) :
    l.first = p.first ∧ r.last = p.last ∧ G.Adj s l.middle ∧
      G.Adj t r.middle ∧ l.middle = r.first ∧ l.last = r.middle := by
  have hlab := labels_intersect_clean hdeg h4 h8 hsep p l hp
  have hrab := labels_intersect_clean hdeg h4 h8 hsep p r hp
  have hlf : l.first = p.first := by simp only [Path4.Internal] at hl; grind
  have hrc : r.last = p.last := by simp only [Path4.Internal] at hr; grind
  have hll : l.last ≠ p.last := by simp only [Path4.Internal] at hl; grind
  have hrf : r.first ≠ p.first := by simp only [Path4.Internal] at hr; grind
  have hlnc : ¬ l.Clean := by
    intro hc
    have hall := common_first_of_two_clean hdeg h4 h8 hsep p l hp hc hlf.symm hll.symm
    exact hr (hall r)
  have hrnc : ¬ r.Clean := by
    intro hc
    have hall := common_last_of_two_clean hdeg h4 h8 hsep p r hp hc hrc.symm hrf.symm
    exact hl (hall l)
  have hsepall := (separation_of_edist hsep).2.2
  have hls := l.edge₀
  have hlt := l.edge₃.symm
  have hrs := r.edge₀
  have hrt := r.edge₃.symm
  have hnl := right_middle_ne_clean_last hdeg p l hp
  have hnr := left_middle_ne_clean_first hdeg p r hp
  obtain ⟨z, hzl, hzr⟩ := l.internal_intersects h8 r
  have horient : G.Adj s l.middle ∧ G.Adj t r.middle := by
    rcases l.classes hsep with hc | hleft | hright
    · exact False.elim (hlnc hc)
    · rcases r.classes hsep with hc | hrleft | hrright
      · exact False.elim (hrnc hc)
      · have hpair := left_partner_eq hdeg h4 l r hleft.1 hrleft.1
        have hne := hnr hrleft.1
        grind
      · exact ⟨hleft.1, hrright.1⟩
    · rcases r.classes hsep with hc | hrleft | hrright
      · exact False.elim (hrnc hc)
      · have hn₁ := hnl hright.1
        have hn₂ := hnr hrleft.1
        have hs₁ := hsepall l.first
        have hs₂ := hsepall l.middle
        have hs₃ := hsepall r.first
        have hs₄ := hsepall r.middle
        simp only [Path4.Internal] at hzl hzr
        grind
      · have hpair := right_partner_eq hdeg h4 l r hright.1 hrright.1
        have hne := hnl hright.1
        grind
  have hcross₁ : l.middle = r.first → l.last = r.middle := by
    intro he
    exact cross_unique_right h4 hsep horient.1 l.edge₃.symm horient.2
      l.edge₂ (he ▸ r.edge₁)
  have hcross₂ : l.last = r.middle → l.middle = r.first := by
    intro he
    exact cross_unique_left h4 hsep horient.2 horient.1 r.edge₀
      (he ▸ l.edge₂) r.edge₁
  have hpair : l.middle = r.first ∧ l.last = r.middle := by
    have hs₁ := hsepall l.first
    have hs₂ := hsepall l.middle
    have hs₃ := hsepall r.first
    have hs₄ := hsepall l.last
    have htm := horient.2
    have hsm := horient.1
    simp only [Path4.Internal] at hzl hzr
    grind
  exact ⟨hlf, hrc, horient.1, horient.2, hpair⟩

/-- Seven distinct vertices with the H7 edges induce exactly H7: the four
nonport outer vertices are degree-saturated, and separation excludes the remaining
port/middle chords. No chordlessness premise is assumed. -/
theorem alignedH7_of_nine_edges [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) {a d b c e : V}
    (hd : [s, t, a, d, b, c, e].Nodup)
    (hsep : 2 < G.edist s t) (hb : ¬ G.Adj s b ∧ ¬ G.Adj t b)
    (hsa : G.Adj s a) (hsd : G.Adj s d) (had : G.Adj a d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (htc : G.Adj t c)
    (hte : G.Adj t e) (hce : G.Adj c e) (hde : G.Adj d e) :
    AlignedH7 G s t := by
  let f : Fin 7 → V := ![s, t, a, d, b, c, e]
  have hdist := hd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hdist
  have hi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> norm_num [f] at he ⊢ <;> grind
  have hna : ∀ x, G.Adj a x → x = s ∨ x = d ∨ x = b := by
    intro x hx
    exact neighbor_eq_of_three hdeg (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
      grind) hsa.symm had hab hx
  have hnd : ∀ x, G.Adj d x → x = s ∨ x = a ∨ x = e := by
    intro x hx
    exact neighbor_eq_of_three hdeg (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
      grind) hsd.symm had.symm hde hx
  have hnc : ∀ x, G.Adj c x → x = t ∨ x = b ∨ x = e := by
    intro x hx
    exact neighbor_eq_of_three hdeg (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
      grind) htc.symm hbc.symm hce hx
  have hne : ∀ x, G.Adj e x → x = t ∨ x = c ∨ x = d := by
    intro x hx
    exact neighbor_eq_of_three hdeg (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
      grind) hte.symm hce.symm hde.symm hx
  have hseparation := separation_of_edist hsep
  have hsym : ∀ x y, G.Adj x y → G.Adj y x := fun _ _ h => h.symm
  apply alignedH7_iff.mpr
  refine ⟨f, hi, rfl, rfl, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [f, h7_adj_iff] <;> grind

/-- A clean path with detours avoiding its two endpoint-neighbor labels yields
an aligned induced H7. The seven vertices and all nine edges are extracted from
actual simple four-paths. -/
theorem alignedH7_of_clean_avoiding [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) (h4 : ¬ HasSimpleCycleOfLength G 4)
    (h8 : ¬ HasSimpleCycleOfLength G 8) (hsep : 2 < G.edist s t)
    (p l r : Path4 G s t) (hp : p.Clean)
    (hl : ¬ l.Internal p.last) (hr : ¬ r.Internal p.first) :
    AlignedH7 G s t := by
  obtain ⟨hlf, hrc, hsm, htm, hmf, hlm⟩ := clean_detours hdeg h4 h8 hsep p l r hp hl hr
  have hd : [s, t, p.first, l.middle, p.middle, p.last, r.middle].Nodup := by
    have hpdist := p.distinct
    have hldist := l.distinct
    have hrdist := r.distinct
    have hsepall := (separation_of_edist hsep).2.2
    have hsp := p.edge₀
    have htp := p.edge₃.symm
    simp only [Path4.Clean] at hp
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
      at hpdist hldist hrdist ⊢
    grind
  exact alignedH7_of_nine_edges hdeg hd hsep hp p.edge₀ hsm
    (hlf ▸ l.edge₁) p.edge₁ p.edge₂ p.edge₃.symm htm
    (hrc ▸ r.edge₂.symm) (hlm ▸ l.edge₂)

end Erdos64.SubcubicFunnel
