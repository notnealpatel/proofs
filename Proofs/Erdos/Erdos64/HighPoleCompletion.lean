import Erdos.Erdos64.UniqueCubicClawCenter

set_option autoImplicit false

namespace Erdos64.HighPoleCompletion

open SimpleGraph Erdos64.UniqueCubicClawCenter

universe u

/-- Outside the deleted vertex, two distinct neighbors of a pole are adjacent
when its neighborhood is independent and no other vertex is a claw center. -/
theorem external_neighbors_adj {V : Type u} (G : SimpleGraph V) {v p a b : V}
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    (hp : G.Adj v p) (ha : G.Adj p a) (hb : G.Adj p b)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b) : G.Adj a b := by
  have hva : ¬ G.Adj v a := fun hva => hNind p a hp hva ha
  have hvb : ¬ G.Adj v b := fun hvb => hNind p b hp hvb hb
  by_contra hnab
  have hclaw : Claw G p :=
    ⟨v, a, b, hav.symm, hbv.symm, hab, hp.symm, ha, hb, hva, hvb, hnab⟩
  exact hp.ne (hunique p hclaw).symm

/-- Every original neighbor of the unique claw center has degree three,
without any degree bound on that center, if its neighborhood is independent. -/
theorem pole_degree_three {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b) :
    ∀ p, G.Adj v p → G.degree p = 3 := by
  classical
  intro p hp
  let s := (G.neighborFinset p).erase v
  have hsmall : s.card ≤ 2 := by
    by_contra hnot
    have hlarge : 2 < s.card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlarge
    have ha' : a ≠ v ∧ G.Adj p a := by simpa [s] using ha
    have hb' : b ≠ v ∧ G.Adj p b := by simpa [s] using hb
    have hc' : c ≠ v ∧ G.Adj p c := by simpa [s] using hc
    have eab := external_neighbors_adj G hunique hNind hp ha'.2 hb'.2 ha'.1 hb'.1 hab
    have ebc := external_neighbors_adj G hunique hNind hp hb'.2 hc'.2 hb'.1 hc'.1 hbc
    exact not_four_cycle G hG ha'.2.ne hb'.2.ne hc'.2.ne hab hac hbc
      ha'.2 eab ebc hc'.2.symm
  have hmem : v ∈ G.neighborFinset p := (G.mem_neighborFinset p v).mpr hp.symm
  have hcount : s.card + 1 = G.degree p := Finset.card_erase_add_one hmem
  have hmin := hG.degree_ge_three p
  omega

/-- An induced diamond is excluded: two adjacent centers cannot have two
 distinct, nonadjacent common neighbors. Four-cliques are allowed. -/
def InducedDiamondFree {V : Type u} (R : SimpleGraph V) : Prop :=
  ∀ a b c d, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
    R.Adj b c → R.Adj b d → ¬ R.Adj c d → False

example : InducedDiamondFree (⊤ : SimpleGraph (Fin 4)) := by
  intro a b c d hcd _ _ _ _ _ hncd
  exact hncd (by simpa using hcd)

example : ¬ InducedDiamondFree ({
    Adj := fun x y : Fin 4 => x ≠ y ∧ ¬ ((x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2))
    symm := ⟨by intro x y h; exact ⟨h.1.symm, by tauto⟩⟩
    loopless := ⟨by intro x h; exact h.1 rfl⟩ } : SimpleGraph (Fin 4)) := by
  intro h
  exact h 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- Completing any deleted vertex of a counterexample creates no induced
 diamond. No bound on its degree, independent neighborhood, or unique claw
 center is required. -/
theorem completion_inducedDiamondFree {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V} :
    InducedDiamondFree (completion G v) := by
  intro a b c d hcd eab eac ead ebc ebd hncd
  have ne_val : ∀ {s t : {x : V // x ≠ v}}, s ≠ t → s.val ≠ t.val := by
    intro s t hne heq
    exact hne (Subtype.ext heq)
  have hnab : ¬ (G.Adj v a.val ∧ G.Adj v b.val) := by
    rintro ⟨ha, hb⟩
    have hc := completion_common_poles G hG eab.ne ha hb eac.symm ebc.symm
    have hd := completion_common_poles G hG eab.ne ha hb ead.symm ebd.symm
    exact hncd ((completion_adj_iff G v c d).mpr (Or.inr ⟨hcd, hc, hd⟩))
  have hnac : ¬ (G.Adj v a.val ∧ G.Adj v c.val) := by
    rintro ⟨ha, hc⟩
    exact hnab ⟨ha, completion_common_poles G hG eac.ne ha hc eab.symm ebc⟩
  have hnad : ¬ (G.Adj v a.val ∧ G.Adj v d.val) := by
    rintro ⟨ha, hd⟩
    exact hnab ⟨ha, completion_common_poles G hG ead.ne ha hd eab.symm ebd⟩
  have hnbc : ¬ (G.Adj v b.val ∧ G.Adj v c.val) := by
    rintro ⟨hb, hc⟩
    exact hnab ⟨completion_common_poles G hG ebc.ne hb hc eab eac, hb⟩
  have hnbd : ¬ (G.Adj v b.val ∧ G.Adj v d.val) := by
    rintro ⟨hb, hd⟩
    exact hnab ⟨completion_common_poles G hG ebd.ne hb hd eab ead, hb⟩
  have old_of_not_pair : ∀ {s t : {x : V // x ≠ v}},
      ¬ (G.Adj v s.val ∧ G.Adj v t.val) →
      (completion G v).Adj s t → G.Adj s.val t.val := by
    intro s t hnot he
    rcases (completion_adj_iff G v s t).mp he with hold | ⟨_, hs, ht⟩
    · exact hold
    · exact False.elim (hnot ⟨hs, ht⟩)
  exact not_four_cycle G hG (ne_val eac.ne) (ne_val eab.ne) (ne_val ead.ne)
    (ne_val ebc.ne.symm) (ne_val hcd) (ne_val ebd.ne)
    (old_of_not_pair hnac eac) (old_of_not_pair hnbc ebc).symm
    (old_of_not_pair hnbd ebd) (old_of_not_pair hnad ead).symm

private theorem original_nonadjacent_neighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G) (x : V) :
    ∃ a b, G.Adj x a ∧ G.Adj x b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  classical
  have hlarge : 2 < (G.neighborFinset x).card := by
    have hmin := hG.degree_ge_three x
    change 2 < G.degree x
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlarge
  have ea := (G.mem_neighborFinset x a).mp ha
  have eb := (G.mem_neighborFinset x b).mp hb
  have ec := (G.mem_neighborFinset x c).mp hc
  by_cases eab : G.Adj a b
  · by_cases ebc : G.Adj b c
    · by_cases eac : G.Adj a c
      · exact False.elim (not_four_cycle G hG ea.ne eb.ne ec.ne hab hac hbc
          ea eab ebc ec.symm)
      · exact ⟨a, c, ea, ec, hac, eac⟩
    · exact ⟨b, c, eb, ec, hbc, ebc⟩
  · exact ⟨a, b, ea, eb, hab, eab⟩

/-- Every surviving vertex has two distinct nonadjacent neighbors in the
completion, provided the deleted vertex's original neighborhood is independent.
Neither cubicity nor uniqueness of a claw center is needed. -/
theorem completion_nonsimplicial {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b) :
    ∀ x : {x : V // x ≠ v}, ∃ a b,
      (completion G v).Adj x a ∧ (completion G v).Adj x b ∧
      a ≠ b ∧ ¬ (completion G v).Adj a b := by
  classical
  intro x
  by_cases hx : G.Adj v x.val
  · have hvlarge : 1 < (G.neighborFinset v).card := by
      have hvmin := hG.degree_ge_three v
      change 1 < G.degree v
      omega
    obtain ⟨q, hqmem, hqx⟩ := Finset.exists_mem_ne hvlarge x.val
    have hq := (G.mem_neighborFinset v q).mp hqmem
    have hxlarge : 1 < (G.neighborFinset x.val).card := by
      have hxmin := hG.degree_ge_three x.val
      change 1 < G.degree x.val
      omega
    obtain ⟨a, hamem, hav⟩ := Finset.exists_mem_ne hxlarge v
    have ha := (G.mem_neighborFinset x.val a).mp hamem
    have hna : ¬ G.Adj v a := fun hva => hNind x.val a hx hva ha
    let q' : {x : V // x ≠ v} := ⟨q, hq.ne.symm⟩
    let a' : {x : V // x ≠ v} := ⟨a, hav⟩
    have hxq : x ≠ q' := fun heq => hqx (congrArg Subtype.val heq).symm
    have hqa : q' ≠ a' := by
      intro heq
      have hval : q = a := congrArg Subtype.val heq
      exact hna (hval ▸ hq)
    refine ⟨q', a', Or.inr ⟨hxq, hx, hq⟩, Or.inl ha, hqa, ?_⟩
    intro he
    rcases (completion_adj_iff G v q' a').mp he with hold | ⟨_, _, hpole⟩
    · exact no_two_pole_neighbors G hG hav hx hq hqx.symm ha.symm hold.symm
    · exact hna hpole
  · obtain ⟨a, b, ha, hb, hab, hnab⟩ := original_nonadjacent_neighbors G hG x.val
    have hav : a ≠ v := by
      intro heq
      exact hx (heq ▸ ha.symm)
    have hbv : b ≠ v := by
      intro heq
      exact hx (heq ▸ hb.symm)
    let a' : {x : V // x ≠ v} := ⟨a, hav⟩
    let b' : {x : V // x ≠ v} := ⟨b, hbv⟩
    have hab' : a' ≠ b' := fun heq => hab (congrArg Subtype.val heq)
    refine ⟨a', b', Or.inl ha, Or.inl hb, hab', ?_⟩
    intro he
    rcases (completion_adj_iff G v a' b').mp he with hold | ⟨_, hpa, hpb⟩
    · exact hnab hold
    · exact no_two_pole_neighbors G hG x.property hpa hpb hab ha hb

end Erdos64.HighPoleCompletion
