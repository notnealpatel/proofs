import Erdos.Erdos64.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Unique cubic claw-center exclusion: construction frontier

This module currently proves the original pole calculation and the full pole-triangle
completion's nonemptiness, minimum degree, claw-freeness, and diamond/four-clique exclusion.
It constructs a finite canonical root from all inclusion-maximal Mathlib cliques, proves
exactly two incident root nodes per completed-graph vertex and exactly one per graph edge,
and proves that the root is triangle-free, has degrees two or three, and has no adjacent
degree-two nodes. Root-pole-arm bookkeeping, suppression, and the arbitrary-cycle lift remain
open, so this module does not export the requested full original-hypothesis `False` theorem.
It is an unadopted formalization frontier, not a completed branch exclusion.
-/

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter

open SimpleGraph

universe u

/-- An induced claw centered at `v`: three distinct, pairwise nonadjacent neighbors. -/
def Claw {V : Type u} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧
    ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c

example : Claw ({
    Adj := fun x y : Fin 4 => (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)
    symm := ⟨by intro x y h; exact h.elim Or.inr Or.inl⟩
    loopless := ⟨by intro x; simp⟩ } : SimpleGraph (Fin 4)) 0 := by
  exact ⟨1, 2, 3, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Four distinct vertices joined in cyclic order form a forbidden ordinary four-cycle. -/
theorem not_four_cycle {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eab : G.Adj a b) (ebc : G.Adj b c)
    (ecd : G.Adj c d) (eda : G.Adj d a) : False := by
  let t : G.Walk a a := .cons eab (.cons ebc (.cons ecd (.cons eda .nil)))
  have ht : t.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [t, Walk.isPath_def, hbc, hbd, hcd,
        Ne.symm hab, Ne.symm hac, Ne.symm had]
    · simp [t]
  exact hG.not_hasPowerOfTwoCycle ⟨2, by decide, a, t, ht, rfl⟩

/-- The three leaves of a cubic claw exhaust the center's neighborhood. -/
theorem neighbors_eq_claw_leaves {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v a b c : V}
    (hv : G.degree v = 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) :
    ∀ x, G.Adj v x ↔ x = a ∨ x = b ∨ x = c := by
  classical
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (G.mem_neighborFinset v _).mpr ha
    · exact (G.mem_neighborFinset v _).mpr hb
    · exact (G.mem_neighborFinset v _).mpr hc
  have hcard : ({a, b, c} : Finset V).card = (G.neighborFinset v).card := by
    simpa [hab, hac, hbc] using hv.symm
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  intro x
  rw [← G.mem_neighborFinset, ← heq]
  simp

/-- Any two neighbors of a cubic induced-claw center are nonadjacent. -/
theorem poles_nonadjacent {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} (hv : G.degree v = 3) (hclaw : Claw G v)
    {p q : V} (hp : G.Adj v p) (hq : G.Adj v q) : ¬ G.Adj p q := by
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ := hclaw
  have hleaves := neighbors_eq_claw_leaves G hv hab hac hbc ha hb hc
  rcases (hleaves p).mp hp with rfl | rfl | rfl <;>
    rcases (hleaves q).mp hq with rfl | rfl | rfl
  all_goals simp_all [SimpleGraph.adj_comm]

/-- External neighbors of a pole form a clique when the cubic claw center is unique. -/
theorem external_neighbors_adj {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v p a b : V}
    (hv : G.degree v = 3) (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v) (hp : G.Adj v p)
    (ha : G.Adj p a) (hb : G.Adj p b)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b) : G.Adj a b := by
  have hva : ¬ G.Adj v a := by
    intro hva
    exact poles_nonadjacent G hv hclaw hp hva ha
  have hvb : ¬ G.Adj v b := by
    intro hvb
    exact poles_nonadjacent G hv hclaw hp hvb hb
  by_contra hnab
  have hsecond : Claw G p :=
    ⟨v, a, b, hav.symm, hbv.symm, hab, hp.symm, ha, hb, hva, hvb, hnab⟩
  exact hp.ne (hunique p hsecond).symm

/-- Every neighbor of the unique cubic claw center has original degree three. -/
theorem pole_degree_three {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    (hv : G.degree v = 3) (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v) {p : V} (hp : G.Adj v p) :
    G.degree p = 3 := by
  classical
  let s := (G.neighborFinset p).erase v
  have hsmall : s.card ≤ 2 := by
    by_contra hnot
    have hlarge : 2 < s.card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlarge
    have ha' : a ≠ v ∧ G.Adj p a := by simpa [s] using ha
    have hb' : b ≠ v ∧ G.Adj p b := by simpa [s] using hb
    have hc' : c ≠ v ∧ G.Adj p c := by simpa [s] using hc
    have eab := external_neighbors_adj G hv hclaw hunique hp ha'.2 hb'.2 ha'.1 hb'.1 hab
    have ebc := external_neighbors_adj G hv hclaw hunique hp hb'.2 hc'.2 hb'.1 hc'.1 hbc
    exact not_four_cycle G hG ha'.2.ne hb'.2.ne hc'.2.ne hab hac hbc
      ha'.2 eab ebc hc'.2.symm
  have hmem : v ∈ G.neighborFinset p := (G.mem_neighborFinset p v).mpr hp.symm
  have hcount : s.card + 1 = G.degree p := by
    exact Finset.card_erase_add_one hmem
  have hmin := hG.degree_ge_three p
  omega

/-- Two different poles cannot have a common neighbor other than the center. -/
theorem no_two_pole_neighbors {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v x p q : V}
    (hx : x ≠ v) (hp : G.Adj v p) (hq : G.Adj v q) (hpq : p ≠ q)
    (hxp : G.Adj x p) (hxq : G.Adj x q) : False := by
  exact not_four_cycle G hG hp.ne hx.symm hq.ne hxp.ne.symm hpq hxq.ne
    hp hxp.symm hxq hq.symm

/-- The deleted-vertex type is finite without exposing decidable equality in public hypotheses. -/
noncomputable instance deletedFintype {V : Type u} [Fintype V] (v : V) :
    Fintype {x : V // x ≠ v} := Fintype.ofFinite _

/-- Delete `v` and complete its original neighborhood to a triangle (when it is cubic). -/
def completion {V : Type u} (G : SimpleGraph V) (v : V) :
    SimpleGraph {x : V // x ≠ v} where
  Adj x y := G.Adj x.val y.val ∨ (x ≠ y ∧ G.Adj v x.val ∧ G.Adj v y.val)
  symm := ⟨by
    intro x y h
    rcases h with hold | ⟨hne, hx, hy⟩
    · exact Or.inl hold.symm
    · exact Or.inr ⟨hne.symm, hy, hx⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with hold | ⟨hne, _, _⟩
    · exact G.irrefl hold
    · exact hne rfl⟩

/-- Completion adds precisely edges between distinct original neighbors of the deleted vertex. -/
theorem completion_adj_iff {V : Type u} (G : SimpleGraph V) (v : V)
    (x y : {x : V // x ≠ v}) :
    (completion G v).Adj x y ↔
      G.Adj x.val y.val ∨ (x ≠ y ∧ G.Adj v x.val ∧ G.Adj v y.val) := Iff.rfl

/-- A completed-graph nonedge is an original-graph nonedge. -/
theorem old_nonadjacent {V : Type u} (G : SimpleGraph V) {v : V}
    {x y : {x : V // x ≠ v}} (h : ¬ (completion G v).Adj x y) :
    ¬ G.Adj x.val y.val := fun hxy => h (Or.inl hxy)

/-- In the completion, three independent vertices include two nonpoles. -/
theorem independent_triple_two_nonpoles {V : Type u} (G : SimpleGraph V) {v : V}
    {a b c : {x : V // x ≠ v}}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnab : ¬ (completion G v).Adj a b)
    (hnac : ¬ (completion G v).Adj a c)
    (hnbc : ¬ (completion G v).Adj b c) :
    (¬ G.Adj v a.val ∧ ¬ G.Adj v b.val) ∨
    (¬ G.Adj v a.val ∧ ¬ G.Adj v c.val) ∨
    (¬ G.Adj v b.val ∧ ¬ G.Adj v c.val) := by
  by_cases ha : G.Adj v a.val
  · have hb : ¬ G.Adj v b.val := fun hb => hnab (Or.inr ⟨hab, ha, hb⟩)
    have hc : ¬ G.Adj v c.val := fun hc => hnac (Or.inr ⟨hac, ha, hc⟩)
    exact Or.inr (Or.inr ⟨hb, hc⟩)
  · by_cases hb : G.Adj v b.val
    · have hc : ¬ G.Adj v c.val := fun hc => hnbc (Or.inr ⟨hbc, hb, hc⟩)
      exact Or.inr (Or.inl ⟨ha, hc⟩)
    · exact Or.inl ⟨ha, hb⟩

/-- Completing the unique cubic claw center removes every induced claw. -/
theorem completion_claw_free {V : Type u} (G : SimpleGraph V) {v : V}
    (hunique : ∀ w, Claw G w → w = v) :
    ∀ x, ¬ Claw (completion G v) x := by
  intro x hclaw
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ := hclaw
  have ne_val : ∀ {s t : {x : V // x ≠ v}}, s ≠ t → s.val ≠ t.val := by
    intro s t hne heq
    exact hne (Subtype.ext heq)
  have lift_edge : ∀ {y : {x : V // x ≠ v}}, (completion G v).Adj x y →
      (¬ G.Adj v x.val ∨ ¬ G.Adj v y.val) → G.Adj x.val y.val := by
    intro y h hnot
    rcases h with hold | ⟨_, hx, hy⟩
    · exact hold
    · exact False.elim (hnot.elim (fun hn => hn hx) (fun hn => hn hy))
  by_cases hx : G.Adj v x.val
  · have pair_claw : ∀ {s t : {x : V // x ≠ v}}, s ≠ t →
        (completion G v).Adj x s → (completion G v).Adj x t →
        ¬ (completion G v).Adj s t → ¬ G.Adj v s.val → ¬ G.Adj v t.val → False := by
      intro s t hne hs ht hnst hns hnt
      have hold : Claw G x.val :=
        ⟨v, s.val, t.val, s.property.symm, t.property.symm, ne_val hne,
          hx.symm, lift_edge hs (Or.inr hns), lift_edge ht (Or.inr hnt),
          hns, hnt, old_nonadjacent G hnst⟩
      exact x.property (hunique x.val hold)
    rcases independent_triple_two_nonpoles G hab hac hbc hnab hnac hnbc with
      ⟨hna, hnb⟩ | ⟨hna, hnc⟩ | ⟨hnb, hnc⟩
    · exact pair_claw hab ha hb hnab hna hnb
    · exact pair_claw hac ha hc hnac hna hnc
    · exact pair_claw hbc hb hc hnbc hnb hnc
  · have hold : Claw G x.val :=
      ⟨a.val, b.val, c.val, ne_val hab, ne_val hac, ne_val hbc,
        lift_edge ha (Or.inl hx), lift_edge hb (Or.inl hx), lift_edge hc (Or.inl hx),
        old_nonadjacent G hnab, old_nonadjacent G hnac, old_nonadjacent G hnbc⟩
    exact x.property (hunique x.val hold)

/-- Completion of the empty graph remains empty: no poles means no added edges. -/
theorem completion_bot {V : Type u} (v : V) :
    completion (⊥ : SimpleGraph V) v = ⊥ := by
  ext x y
  simp [completion]

/-- Completion never reduces the degree of a vertex of a cubic claw graph. -/
theorem degree_le_completion_degree {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} [DecidableRel (completion G v).Adj]
    (hv : G.degree v = 3) (hclaw : Claw G v) (x : {x : V // x ≠ v}) :
    G.degree x.val ≤ (completion G v).degree x := by
  classical
  by_cases hx : G.Adj v x.val
  · obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ := hclaw
    have hex : ∃ p : V, G.Adj v p ∧ x.val ≠ p := by
      by_cases hxa : x.val = a
      · exact ⟨b, hb, hxa ▸ hab⟩
      · exact ⟨a, ha, hxa⟩
    obtain ⟨p, hp, hxp⟩ := hex
    let f : G.neighborSet x.val → (completion G v).neighborSet x := fun y =>
      if hy : y.val = v then
        ⟨⟨p, hp.ne.symm⟩, Or.inr ⟨fun heq => hxp (congrArg Subtype.val heq), hx, hp⟩⟩
      else ⟨⟨y.val, hy⟩, Or.inl y.property⟩
    have hf : Function.Injective f := by
      intro s t hst
      have hval := congrArg (fun y : (completion G v).neighborSet x => y.val.val) hst
      by_cases hs : s.val = v <;> by_cases ht : t.val = v
      · exact Subtype.ext (hs.trans ht.symm)
      · have hpt : p = t.val := by simpa [f, hs, ht] using hval
        have hn := poles_nonadjacent G hv
          ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ hx hp
        have htadj : G.Adj x.val t.val := t.property
        rw [← hpt] at htadj
        exact False.elim (hn htadj)
      · have hsp : s.val = p := by simpa [f, hs, ht] using hval
        have hn := poles_nonadjacent G hv
          ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ hx hp
        have hsadj : G.Adj x.val s.val := s.property
        rw [hsp] at hsadj
        exact False.elim (hn hsadj)
      · exact Subtype.ext (by simpa [f, hs, ht] using hval)
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf
  · let f : G.neighborSet x.val → (completion G v).neighborSet x := fun y =>
      ⟨⟨y.val, by
        intro hy
        have he : G.Adj y.val x.val := y.property.symm
        rw [hy] at he
        exact hx he⟩, Or.inl y.property⟩
    have hf : Function.Injective f := by
      intro s t hst
      exact Subtype.ext (congrArg (fun y : (completion G v).neighborSet x => y.val.val) hst)
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf

/-- The full pole-triangle completion has minimum degree at least three. -/
theorem completion_min_degree {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} [DecidableRel (completion G v).Adj]
    (hG : IsCounterexample G) (hv : G.degree v = 3) (hclaw : Claw G v) :
    ∀ x, 3 ≤ (completion G v).degree x := by
  intro x
  exact (hG.degree_ge_three x.val).trans (degree_le_completion_degree G hv hclaw x)

/-- At a nonpole, every edge in the completion is an original edge. -/
theorem completion_adj_old_of_nonpole {V : Type u} (G : SimpleGraph V) {v : V}
    {x y : {x : V // x ≠ v}} (hx : ¬ G.Adj v x.val)
    (hxy : (completion G v).Adj x y) : G.Adj x.val y.val := by
  rcases hxy with hold | ⟨_, hpole, _⟩
  · exact hold
  · exact False.elim (hx hpole)

/-- A completed-graph common neighbor of two poles is itself a pole. -/
theorem completion_common_poles {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V}
    {x p q : {x : V // x ≠ v}} (hpq : p ≠ q)
    (hp : G.Adj v p.val) (hq : G.Adj v q.val)
    (hxp : (completion G v).Adj x p) (hxq : (completion G v).Adj x q) :
    G.Adj v x.val := by
  by_contra hx
  have hpq' : p.val ≠ q.val := fun heq => hpq (Subtype.ext heq)
  exact no_two_pole_neighbors G hG x.property hp hq hpq'
    (completion_adj_old_of_nonpole G hx hxp) (completion_adj_old_of_nonpole G hx hxq)

/-- A cubic center cannot have four distinct poles. -/
theorem not_four_poles {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v a b c d : V} (hv : G.degree v = 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) (hd : G.Adj v d) : False := by
  classical
  have hsub : ({a, b, c, d} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset v _).mpr ha
    · exact (G.mem_neighborFinset v _).mpr hb
    · exact (G.mem_neighborFinset v _).mpr hc
    · exact (G.mem_neighborFinset v _).mpr hd
  have hle := Finset.card_le_card hsub
  have hsize : ({a, b, c, d} : Finset V).card = 4 := by simp [hab, hac, had, hbc, hbd, hcd]
  change ({a, b, c, d} : Finset V).card ≤ G.degree v at hle
  rw [hsize, hv] at hle
  omega

/-- Completion has no four distinct vertices spanning a diamond, even with its sixth edge.
Consequently it has neither an induced diamond nor a four-clique. -/
theorem completion_no_diamond {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V} (hv : G.degree v = 3)
    {a b c d : {x : V // x ≠ v}}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eab : (completion G v).Adj a b) (ebc : (completion G v).Adj b c)
    (ecd : (completion G v).Adj c d) (eda : (completion G v).Adj d a)
    (eac : (completion G v).Adj a c) : False := by
  have ne_val : ∀ {s t : {x : V // x ≠ v}}, s ≠ t → s.val ≠ t.val := by
    intro s t hne heq
    exact hne (Subtype.ext heq)
  have hall : G.Adj v a.val → G.Adj v c.val → False := by
    intro ha hc
    have hb := completion_common_poles G hG hac ha hc eab.symm ebc
    have hd := completion_common_poles G hG hac ha hc eda ecd.symm
    exact not_four_poles G hv (ne_val hab) (ne_val hac) (ne_val had)
      (ne_val hbc) (ne_val hbd) (ne_val hcd) ha hb hc hd
  have hnab : ¬ (G.Adj v a.val ∧ G.Adj v b.val) := by
    rintro ⟨ha, hb⟩
    exact hall ha (completion_common_poles G hG hab ha hb eac.symm ebc.symm)
  have hnbc : ¬ (G.Adj v b.val ∧ G.Adj v c.val) := by
    rintro ⟨hb, hc⟩
    exact hall (completion_common_poles G hG hbc hb hc eab eac) hc
  have hncd : ¬ (G.Adj v c.val ∧ G.Adj v d.val) := by
    rintro ⟨hc, hd⟩
    exact hall (completion_common_poles G hG hcd hc hd eac eda.symm) hc
  have hnda : ¬ (G.Adj v d.val ∧ G.Adj v a.val) := by
    rintro ⟨hd, ha⟩
    exact hall ha (completion_common_poles G hG had.symm hd ha ecd eac.symm)
  have old_of_not_pair : ∀ {s t : {x : V // x ≠ v}},
      ¬ (G.Adj v s.val ∧ G.Adj v t.val) →
      (completion G v).Adj s t → G.Adj s.val t.val := by
    intro s t hnot he
    rcases he with hold | ⟨_, hs, ht⟩
    · exact hold
    · exact False.elim (hnot ⟨hs, ht⟩)
  exact not_four_cycle G hG (ne_val hab) (ne_val hac) (ne_val had)
    (ne_val hbc) (ne_val hbd) (ne_val hcd)
    (old_of_not_pair hnab eab) (old_of_not_pair hnbc ebc)
    (old_of_not_pair hncd ecd) (old_of_not_pair hnda eda)

/-- An induced claw supplies a surviving vertex after its center is deleted. -/
theorem completion_nonempty {V : Type u} (G : SimpleGraph V) {v : V}
    (hclaw : Claw G v) : Nonempty {x : V // x ≠ v} := by
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩ := hclaw
  exact ⟨⟨a, ha.ne.symm⟩⟩

/-- On the neighborhood of a completed-graph vertex, equality-or-adjacency is transitive.
This is the local equivalence relation used to construct the two incident maximal cliques. -/
theorem completion_neighbor_relation_transitive {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hv : G.degree v = 3) (x : {x : V // x ≠ v}) :
    ∀ a b c : (completion G v).neighborSet x,
      (a = b ∨ (completion G v).Adj a.val b.val) →
      (b = c ∨ (completion G v).Adj b.val c.val) →
      a = c ∨ (completion G v).Adj a.val c.val := by
  intro a b c hab hbc
  rcases hab with rfl | eab
  · exact hbc
  rcases hbc with rfl | ebc
  · exact Or.inr eab
  by_cases hac : a = c
  · exact Or.inl hac
  have hac' : a.val ≠ c.val := fun heq => hac (Subtype.ext heq)
  have ea : (completion G v).Adj x a.val := a.property
  have eb : (completion G v).Adj x b.val := b.property
  have ec : (completion G v).Adj x c.val := c.property
  have hfalse := completion_no_diamond G hG hv ea.ne eb.ne ec.ne
    eab.ne hac' ebc.ne ea eab ebc ec.symm eb
  exact False.elim hfalse

/-- A graph is strongly diamond-free when no four distinct vertices span five edges.
The sixth edge is unrestricted, so four-cliques are excluded too. -/
def StrongDiamondFree {V : Type u} (R : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    R.Adj a b → R.Adj b c → R.Adj c d → R.Adj d a → R.Adj a c → False

example : StrongDiamondFree (⊥ : SimpleGraph (Fin 4)) := by
  intro a b c d hab hac had hbc hbd hcd eab ebc ecd eda eac
  exact eab

example : ¬ StrongDiamondFree (⊤ : SimpleGraph (Fin 4)) := by
  unfold StrongDiamondFree
  decide

/-- The completed graph satisfies the strong, ordinary five-edge diamond exclusion. -/
theorem completion_strongDiamondFree {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsCounterexample G) {v : V} (hv : G.degree v = 3) :
    StrongDiamondFree (completion G v) := by
  intro a b c d hab hac had hbc hbd hcd eab ebc ecd eda eac
  exact completion_no_diamond G hG hv hab hac had hbc hbd hcd eab ebc ecd eda eac

/-- The canonical clique containing an edge consists of its endpoints and common neighbors. -/
def edgeClique {V : Type u} (R : SimpleGraph V) (x y : V) : Set V :=
  {z | z = x ∨ z = y ∨ (R.Adj x z ∧ R.Adj y z)}

example : edgeClique (⊥ : SimpleGraph (Fin 3)) 0 1 = {0, 1} := by
  ext z
  simp [edgeClique]

/-- In a strongly diamond-free graph, an edge has at most one common neighbor. -/
theorem common_neighbor_unique {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x y a b : V} (hxy : R.Adj x y)
    (hxa : R.Adj x a) (hya : R.Adj y a) (hxb : R.Adj x b) (hyb : R.Adj y b) :
    a = b := by
  by_contra hab
  exact hD x a y b hxa.ne hxy.ne hxb.ne hya.ne.symm hab hyb.ne
    hxa hya.symm hyb hxb.symm hxy

/-- The canonical set associated to an edge is a clique. -/
theorem edgeClique_isClique {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x y : V} (hxy : R.Adj x y) :
    R.IsClique (edgeClique R x y) := by
  intro a ha b hb hab
  rcases ha with rfl | rfl | ⟨hxa, hya⟩
  · rcases hb with rfl | rfl | ⟨hxb, hyb⟩
    · exact False.elim (hab rfl)
    · exact hxy
    · exact hxb
  · rcases hb with rfl | rfl | ⟨hxb, hyb⟩
    · exact hxy.symm
    · exact False.elim (hab rfl)
    · exact hyb
  · rcases hb with rfl | rfl | ⟨hxb, hyb⟩
    · exact hxa.symm
    · exact hya.symm
    · exact False.elim (hab (common_neighbor_unique R hD hxy hxa hya hxb hyb))

/-- Every clique containing the endpoints of an edge lies in its canonical edge clique. -/
theorem clique_subset_edgeClique {V : Type u} (R : SimpleGraph V) {x y : V}
    {C : Set V} (hC : R.IsClique C) (hx : x ∈ C) (hy : y ∈ C) :
    C ⊆ edgeClique R x y := by
  intro z hz
  by_cases hzx : z = x
  · exact Or.inl hzx
  by_cases hzy : z = y
  · exact Or.inr (Or.inl hzy)
  exact Or.inr (Or.inr ⟨hC hx hz (Ne.symm hzx), hC hy hz (Ne.symm hzy)⟩)

/-- The canonical edge clique is inclusion-maximal, not merely maximum among some family. -/
theorem edgeClique_maximal {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x y : V} (hxy : R.Adj x y) :
    Maximal R.IsClique (edgeClique R x y) := by
  apply SimpleGraph.isMaximalClique_iff.mpr
  refine ⟨edgeClique_isClique R hD hxy, ?_⟩
  intro C hC hsub
  exact clique_subset_edgeClique R hC (hsub (Or.inl rfl)) (hsub (Or.inr (Or.inl rfl)))

/-- An edge belongs to exactly one inclusion-maximal clique, its canonical edge clique. -/
theorem maximal_clique_eq_edgeClique {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x y : V} (hxy : R.Adj x y)
    {C : Set V} (hC : Maximal R.IsClique C) (hx : x ∈ C) (hy : y ∈ C) :
    C = edgeClique R x y := by
  have hC' := SimpleGraph.isMaximalClique_iff.mp hC
  have hsub := clique_subset_edgeClique R hC'.1 hx hy
  exact Set.Subset.antisymm hsub (hC'.2 _ (edgeClique_isClique R hD hxy) hsub)

/-- Minimum degree three and strong diamond exclusion supply two nonadjacent neighbors. -/
theorem exists_nonadjacent_neighbors {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) {x : V} (hdegree : 3 ≤ R.degree x) :
    ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b := by
  classical
  have hlarge : 2 < (R.neighborFinset x).card := by
    change 2 < R.degree x
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlarge
  have ea : R.Adj x a := (R.mem_neighborFinset x a).mp ha
  have eb : R.Adj x b := (R.mem_neighborFinset x b).mp hb
  have ec : R.Adj x c := (R.mem_neighborFinset x c).mp hc
  by_cases eab : R.Adj a b
  · by_cases eac : R.Adj a c
    · by_cases ebc : R.Adj b c
      · exact False.elim (hD x a b c ea.ne eb.ne ec.ne hab hac hbc ea eab ebc ec.symm eb)
      · exact ⟨b, c, eb, ec, hbc, ebc⟩
    · exact ⟨a, c, ea, ec, hac, eac⟩
  · exact ⟨a, b, ea, eb, hab, eab⟩

/-- Two nonadjacent neighbors determine the two classes covering a claw-free neighborhood. -/
theorem neighbor_mem_two_edgeCliques {V : Type u} (R : SimpleGraph V)
    (hclaw : ∀ x, ¬ Claw R x) {x a b y : V}
    (ha : R.Adj x a) (hb : R.Adj x b) (hab : a ≠ b) (hnab : ¬ R.Adj a b)
    (hy : R.Adj x y) : y ∈ edgeClique R x a ∨ y ∈ edgeClique R x b := by
  by_cases hya : y = a
  · exact Or.inl (Or.inr (Or.inl hya))
  by_cases hyb : y = b
  · exact Or.inr (Or.inr (Or.inl hyb))
  by_cases eay : R.Adj a y
  · exact Or.inl (Or.inr (Or.inr ⟨hy, eay⟩))
  by_cases eby : R.Adj b y
  · exact Or.inr (Or.inr (Or.inr ⟨hy, eby⟩))
  exact False.elim (hclaw x
    ⟨a, b, y, hab, Ne.symm hya, Ne.symm hyb, ha, hb, hy, hnab, eay, eby⟩)

/-- A maximal clique through a vertex contains another vertex whenever that vertex has a neighbor. -/
theorem maximal_clique_other_vertex {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x a : V} (ha : R.Adj x a)
    {C : Set V} (hC : Maximal R.IsClique C) (_hx : x ∈ C) :
    ∃ y ∈ C, y ≠ x := by
  by_contra hnone
  have hsingleton : ∀ y ∈ C, y = x := by
    intro y hy
    by_contra hne
    exact hnone ⟨y, hy, hne⟩
  have hsub : C ⊆ edgeClique R x a := by
    intro y hy
    exact Or.inl (hsingleton y hy)
  have hext := (SimpleGraph.isMaximalClique_iff.mp hC).2 _ (edgeClique_isClique R hD ha) hsub
  have haC : a ∈ C := hext (Or.inr (Or.inl rfl))
  exact ha.ne (hsingleton a haC).symm

/-- Every vertex belongs to exactly two inclusion-maximal cliques; both edge and triangle
cliques are retained. The conclusion lists the entire incidence fiber. -/
theorem exactly_two_maximal_cliques {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) (x : V) :
    ∃ C D : Set V, Maximal R.IsClique C ∧ Maximal R.IsClique D ∧ C ≠ D ∧
      x ∈ C ∧ x ∈ D ∧ ∀ E : Set V, Maximal R.IsClique E →
        (x ∈ E ↔ E = C ∨ E = D) := by
  obtain ⟨a, b, ha, hb, hab, hnab⟩ := exists_nonadjacent_neighbors R hD (hdegree x)
  let C := edgeClique R x a
  let D := edgeClique R x b
  have hC : Maximal R.IsClique C := edgeClique_maximal R hD ha
  have hD' : Maximal R.IsClique D := edgeClique_maximal R hD hb
  have hne : C ≠ D := by
    intro heq
    have haD : a ∈ D := by
      rw [← heq]
      exact Or.inr (Or.inl rfl)
    rcases haD with hax | hab' | ⟨_, hba⟩
    · exact ha.ne hax.symm
    · exact hab hab'
    · exact hnab hba.symm
  refine ⟨C, D, hC, hD', hne, Or.inl rfl, Or.inl rfl, ?_⟩
  intro E hE
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := maximal_clique_other_vertex R hD ha hE hx
    have exy : R.Adj x y := (SimpleGraph.isMaximalClique_iff.mp hE).1 hx hy hyx.symm
    have heqE := maximal_clique_eq_edgeClique R hD exy hE hx hy
    rcases neighbor_mem_two_edgeCliques R hclaw ha hb hab hnab exy with hyC | hyD
    · have heqC := maximal_clique_eq_edgeClique R hD exy hC (Or.inl rfl) hyC
      exact Or.inl (heqE.trans heqC.symm)
    · have heqD := maximal_clique_eq_edgeClique R hD exy hD' (Or.inl rfl) hyD
      exact Or.inr (heqE.trans heqD.symm)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inl rfl

/-- A maximal clique in a nonempty graph is nonempty, independently of cardinal maximality. -/
theorem maximal_clique_nonempty {V : Type u} [Nonempty V] (R : SimpleGraph V)
    {C : Set V} (hC : Maximal R.IsClique C) : C.Nonempty := by
  by_contra hnone
  obtain ⟨x⟩ := ‹Nonempty V›
  have hsub : C ⊆ {x} := by
    intro y hy
    exact False.elim (hnone ⟨y, hy⟩)
  have hext := (SimpleGraph.isMaximalClique_iff.mp hC).2 {x} (R.isClique_singleton x) hsub
  exact hnone ⟨x, hext (Set.mem_singleton x)⟩

/-- An edge clique has two vertices or three vertices, according as a common neighbor exists. -/
theorem edgeClique_pair_or_triple {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x y : V} (hxy : R.Adj x y) :
    edgeClique R x y = {x, y} ∨
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ edgeClique R x y = {x, y, z} := by
  classical
  by_cases hex : ∃ z : V, R.Adj x z ∧ R.Adj y z
  · obtain ⟨z, hxz, hyz⟩ := hex
    refine Or.inr ⟨z, hxz.ne, hyz.ne, ?_⟩
    ext w
    change (w = x ∨ w = y ∨ (R.Adj x w ∧ R.Adj y w)) ↔ (w = x ∨ w = y ∨ w = z)
    constructor
    · rintro (h | h | ⟨hxw, hyw⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (common_neighbor_unique R hD hxy hxw hyw hxz hyz))
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hxz, hyz⟩)
  · left
    ext w
    change (w = x ∨ w = y ∨ (R.Adj x w ∧ R.Adj y w)) ↔ (w = x ∨ w = y)
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hex ⟨w, h⟩)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- All inclusion-maximal cliques in the present geometry are edges or triangles. -/
theorem maximal_clique_pair_or_triple {V : Type u} [Fintype V] [Nonempty V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (hD : StrongDiamondFree R)
    (hdegree : ∀ x, 3 ≤ R.degree x) {C : Set V} (hC : Maximal R.IsClique C) :
    ∃ x y : V, x ≠ y ∧ (C = {x, y} ∨ ∃ z : V, x ≠ z ∧ y ≠ z ∧ C = {x, y, z}) := by
  obtain ⟨x, hx⟩ := maximal_clique_nonempty R hC
  obtain ⟨a, b, ha, hb, hab, hnab⟩ := exists_nonadjacent_neighbors R hD (hdegree x)
  obtain ⟨y, hy, hyx⟩ := maximal_clique_other_vertex R hD ha hC hx
  have hxy : R.Adj x y := (SimpleGraph.isMaximalClique_iff.mp hC).1 hx hy hyx.symm
  have heq := maximal_clique_eq_edgeClique R hD hxy hC hx hy
  refine ⟨x, y, hxy.ne, ?_⟩
  rw [heq]
  exact edgeClique_pair_or_triple R hD hxy

/-- Nodes of the root are all inclusion-maximal Mathlib cliques, including size-two cliques. -/
abbrev RootNode {V : Type u} (R : SimpleGraph V) := {C : Set V // Maximal R.IsClique C}

/-- Root nodes are finite because the entire powerset of a finite vertex type is finite. -/
noncomputable instance rootNodeFintype {V : Type u} [Fintype V] (R : SimpleGraph V) :
    Fintype (RootNode R) := Fintype.ofFinite _

/-- Two root nodes are adjacent exactly when they are distinct and share a vertex label. -/
def cliqueRoot {V : Type u} (R : SimpleGraph V) : SimpleGraph (RootNode R) where
  Adj C D := C ≠ D ∧ ∃ x : V, x ∈ C.val ∧ x ∈ D.val
  symm := ⟨by
    rintro C D ⟨hne, x, hxC, hxD⟩
    exact ⟨hne.symm, x, hxD, hxC⟩⟩
  loopless := ⟨by rintro C ⟨hne, _⟩; exact hne rfl⟩

/-- The root adjacency definition uses intersection of distinct inclusion-maximal cliques. -/
theorem cliqueRoot_adj_iff {V : Type u} (R : SimpleGraph V) (C D : RootNode R) :
    (cliqueRoot R).Adj C D ↔ C ≠ D ∧ (C.val ∩ D.val).Nonempty := Iff.rfl

/-- Distinct maximal cliques intersect in at most one vertex, so root edges have unique labels. -/
theorem root_intersection_unique {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {C D : RootNode R} (hne : C ≠ D)
    {x y : V} (hxC : x ∈ C.val) (hxD : x ∈ D.val)
    (hyC : y ∈ C.val) (hyD : y ∈ D.val) : x = y := by
  by_contra hxy
  have exy : R.Adj x y := (SimpleGraph.isMaximalClique_iff.mp C.property).1 hxC hyC hxy
  have heqC := maximal_clique_eq_edgeClique R hD exy C.property hxC hyC
  have heqD := maximal_clique_eq_edgeClique R hD exy D.property hxD hyD
  exact hne (Subtype.ext (heqC.trans heqD.symm))

/-- Every original vertex labels exactly two distinct root nodes and no others. -/
theorem exactly_two_root_nodes {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) (x : V) :
    ∃ C D : RootNode R, C ≠ D ∧ x ∈ C.val ∧ x ∈ D.val ∧
      ∀ E : RootNode R, x ∈ E.val ↔ E = C ∨ E = D := by
  obtain ⟨C, D, hC, hD', hne, hxC, hxD, hfiber⟩ := exactly_two_maximal_cliques R hD hclaw hdegree x
  refine ⟨⟨C, hC⟩, ⟨D, hD'⟩, fun heq => hne (congrArg Subtype.val heq), hxC, hxD, ?_⟩
  intro E
  rw [hfiber E.val E.property]
  constructor
  · rintro (heq | heq)
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr (Subtype.ext heq)
  · rintro (heq | heq)
    · exact Or.inl (congrArg Subtype.val heq)
    · exact Or.inr (congrArg Subtype.val heq)

/-- For an edge in the original graph, exactly one root node contains both endpoint labels. -/
theorem exactly_one_root_node_of_adj {V : Type u} (R : SimpleGraph V)
    (hD : StrongDiamondFree R) {x y : V} (hxy : R.Adj x y) :
    ∃! C : RootNode R, x ∈ C.val ∧ y ∈ C.val := by
  let C : RootNode R := ⟨edgeClique R x y, edgeClique_maximal R hD hxy⟩
  refine ⟨C, ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩, ?_⟩
  intro D hmem
  exact Subtype.ext (maximal_clique_eq_edgeClique R hD hxy D.property hmem.1 hmem.2)

/-- Once two root nodes through a label are known, they exhaust that label's incidence fiber. -/
theorem root_incidence_exhausted {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) {x : V} {C D E : RootNode R}
    (hne : C ≠ D) (hxC : x ∈ C.val) (hxD : x ∈ D.val) (hxE : x ∈ E.val) :
    E = C ∨ E = D := by
  obtain ⟨A, B, hAB, hxA, hxB, hfiber⟩ := exactly_two_root_nodes R hD hclaw hdegree x
  have hC := (hfiber C).mp hxC
  have hD' := (hfiber D).mp hxD
  have hE := (hfiber E).mp hxE
  rcases hC with rfl | rfl <;> rcases hD' with rfl | rfl <;> rcases hE with rfl | rfl
  all_goals simp_all

/-- Three pairwise distinct root nodes cannot all contain one label. -/
theorem no_three_root_nodes {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) {x : V} {C D E : RootNode R}
    (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E)
    (hxC : x ∈ C.val) (hxD : x ∈ D.val) (hxE : x ∈ E.val) : False := by
  rcases root_incidence_exhausted R hD hclaw hdegree hCD hxC hxD hxE with heq | heq
  · exact hCE heq.symm
  · exact hDE heq.symm

/-- The canonical clique root is triangle-free. -/
theorem cliqueRoot_triangle_free {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) {A B C : RootNode R}
    (hAB : (cliqueRoot R).Adj A B) (hBC : (cliqueRoot R).Adj B C)
    (hCA : (cliqueRoot R).Adj C A) : False := by
  obtain ⟨a, haA, haB⟩ := hAB.2
  obtain ⟨b, hbB, hbC⟩ := hBC.2
  obtain ⟨c, hcC, hcA⟩ := hCA.2
  have hab : a ≠ b := by
    intro heq
    rw [← heq] at hbC
    exact no_three_root_nodes R hD hclaw hdegree hAB.1 hCA.1.symm hBC.1 haA haB hbC
  have hbc : b ≠ c := by
    intro heq
    rw [← heq] at hcA
    exact no_three_root_nodes R hD hclaw hdegree hAB.1 hCA.1.symm hBC.1 hcA hbB hbC
  have eab : R.Adj a b := (SimpleGraph.isMaximalClique_iff.mp B.property).1 haB hbB hab
  have ebc : R.Adj b c := (SimpleGraph.isMaximalClique_iff.mp C.property).1 hbC hcC hbc
  have heqB := maximal_clique_eq_edgeClique R hD eab B.property haB hbB
  have hcB : c ∈ B.val := by
    rw [heqB]
    by_cases hac : a = c
    · exact Or.inl hac.symm
    · have eac : R.Adj a c := (SimpleGraph.isMaximalClique_iff.mp A.property).1 haA hcA hac
      exact Or.inr (Or.inr ⟨eac, ebc⟩)
  have heqB' := maximal_clique_eq_edgeClique R hD ebc B.property hbB hcB
  have heqC := maximal_clique_eq_edgeClique R hD ebc C.property hbC hcC
  exact hBC.1 (Subtype.ext (heqB'.trans heqC.symm))

/-- A root clique's member-label type is finite with its original canonical vertex semantics. -/
noncomputable instance rootMemberFintype {V : Type u} [Fintype V] (R : SimpleGraph V)
    (C : RootNode R) : Fintype C.val := Fintype.ofFinite _

/-- The neighbors of a root node are in bijection with the labels belonging to its clique. -/
theorem root_neighbor_bijection {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) (C : RootNode R) :
    Nonempty ((cliqueRoot R).neighborSet C ≃ C.val) := by
  classical
  have hex (D : (cliqueRoot R).neighborSet C) :
      ∃ x : V, x ∈ C.val ∧ x ∈ D.val.val := D.property.2
  let f : (cliqueRoot R).neighborSet C → C.val :=
    fun D => ⟨Classical.choose (hex D), (Classical.choose_spec (hex D)).1⟩
  have hmem (D : (cliqueRoot R).neighborSet C) : (f D).val ∈ D.val.val :=
    (Classical.choose_spec (hex D)).2
  have hf : Function.Injective f := by
    intro D E heq
    have hval : (f D).val = (f E).val := congrArg Subtype.val heq
    have hxD : (f E).val ∈ D.val.val := by rw [← hval]; exact hmem D
    have hxC : (f E).val ∈ C.val := (f E).property
    rcases root_incidence_exhausted R hD hclaw hdegree D.property.1 hxC hxD (hmem E) with hEC | hED
    · exact False.elim (E.property.1 hEC.symm)
    · exact Subtype.ext hED.symm
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨A, B, hAB, hxA, hxB, hfiber⟩ := exactly_two_root_nodes R hD hclaw hdegree x.val
    have hother : ∃ D : RootNode R, C ≠ D ∧ x.val ∈ D.val := by
      rcases (hfiber C).mp x.property with hCA | hCB
      · refine ⟨B, ?_, hxB⟩
        rw [hCA]
        exact hAB
      · refine ⟨A, ?_, hxA⟩
        rw [hCB]
        exact hAB.symm
    obtain ⟨D, hCD, hxD⟩ := hother
    let D' : (cliqueRoot R).neighborSet C := ⟨D, hCD, x.val, x.property, hxD⟩
    refine ⟨D', Subtype.ext ?_⟩
    exact root_intersection_unique R hD hCD (f D').property (hmem D') x.property hxD
  exact ⟨Equiv.ofBijective f ⟨hf, hsurj⟩⟩

/-- Root degree is exactly the number of member labels of its maximal clique. -/
theorem cliqueRoot_degree_eq_card {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) (C : RootNode R) :
    (cliqueRoot R).degree C = Fintype.card C.val := by
  obtain ⟨e⟩ := root_neighbor_bijection R hD hclaw hdegree C
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr e

/-- Every node of the root has degree two or three, including maximal edge cliques. -/
theorem cliqueRoot_degree_two_or_three {V : Type u} [Fintype V] [Nonempty V]
    (R : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x) (C : RootNode R) :
    (cliqueRoot R).degree C = 2 ∨ (cliqueRoot R).degree C = 3 := by
  classical
  rw [cliqueRoot_degree_eq_card R hD hclaw hdegree C, ← Set.toFinset_card]
  obtain ⟨x, y, hxy, hpair | ⟨z, hxz, hyz, htriple⟩⟩ :=
    maximal_clique_pair_or_triple R hD hdegree C.property
  · left
    have hfin : C.val.toFinset = {x, y} := by
      ext w
      simp [hpair]
    rw [hfin]
    simp [hxy]
  · right
    have hfin : C.val.toFinset = {x, y, z} := by
      ext w
      simp [htriple]
    rw [hfin]
    simp [hxy, hxz, hyz]

/-- Adjacent root nodes cannot both have degree two, because their shared label
would have at most two neighbors in the original graph. -/
theorem cliqueRoot_no_adjacent_degree_two
    {V : Type u} [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] [DecidableRel (cliqueRoot R).Adj]
    (hD : StrongDiamondFree R) (hclaw : ∀ x, ¬ Claw R x)
    (hdegree : ∀ x, 3 ≤ R.degree x)
    {C D : RootNode R} (hCD : (cliqueRoot R).Adj C D)
    (hC : (cliqueRoot R).degree C = 2)
    (hDtwo : (cliqueRoot R).degree D = 2) : False := by
  classical
  obtain ⟨hne, x, hxC, hxD⟩ := hCD
  have hcardC : C.val.toFinset.card = 2 := by
    calc
      C.val.toFinset.card = Fintype.card C.val := Set.toFinset_card C.val
      _ = (cliqueRoot R).degree C :=
        (cliqueRoot_degree_eq_card R hD hclaw hdegree C).symm
      _ = 2 := hC
  have hcardD : D.val.toFinset.card = 2 := by
    calc
      D.val.toFinset.card = Fintype.card D.val := Set.toFinset_card D.val
      _ = (cliqueRoot R).degree D :=
        (cliqueRoot_degree_eq_card R hD hclaw hdegree D).symm
      _ = 2 := hDtwo
  have hxCf : x ∈ C.val.toFinset := by simpa using hxC
  have hxDf : x ∈ D.val.toFinset := by simpa using hxD
  have heraseC : (C.val.toFinset.erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxCf, hcardC]
  have heraseD : (D.val.toFinset.erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxDf, hcardD]
  have hsubset :
      R.neighborFinset x ⊆ C.val.toFinset.erase x ∪ D.val.toFinset.erase x := by
    intro y hy
    have hxy : R.Adj x y := (R.mem_neighborFinset x y).mp hy
    have hyx : y ≠ x := hxy.ne.symm
    let E : RootNode R := ⟨edgeClique R x y, edgeClique_maximal R hD hxy⟩
    have hxE : x ∈ E.val := Or.inl rfl
    have hyE : y ∈ E.val := Or.inr (Or.inl rfl)
    rcases root_incidence_exhausted R hD hclaw hdegree hne hxC hxD hxE with hEC | hED
    · have hyC : y ∈ C.val := by simpa only [hEC] using hyE
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_erase.mpr ⟨hyx, by simpa using hyC⟩))
    · have hyD : y ∈ D.val := by simpa only [hED] using hyE
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_erase.mpr ⟨hyx, by simpa using hyD⟩))
  have hbound : R.degree x ≤ 2 := by
    have hle := Finset.card_le_card hsubset
    have hunion := Finset.card_union_le (C.val.toFinset.erase x) (D.val.toFinset.erase x)
    change (R.neighborFinset x).card ≤ 2
    omega
  have hmin := hdegree x
  omega

end Erdos64.UniqueCubicClawCenter
