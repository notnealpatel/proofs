import Erdos.Erdos64.UniqueCubicClawCenter

set_option autoImplicit false

namespace Erdos64.TriangleIncidenceLocal

open SimpleGraph UniqueCubicClawCenter

universe u

/-- Two neighbors of any vertex cannot have a second common neighbor in its neighborhood. -/
theorem neighborhood_matching {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c)
    (hab : G.Adj a b) (hbc : G.Adj b c) : a = c := by
  by_contra hac
  exact no_two_pole_neighbors G hG hb.ne.symm ha hc hac hab.symm hbc

/-- At a nonclaw vertex, three distinct neighbors contain an edge. -/
theorem edge_of_not_claw {V : Type u} (G : SimpleGraph V)
    {x a b c : V} (hx : ¬ Claw G x)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  by_contra hn
  have hnab : ¬ G.Adj a b := fun h => hn (Or.inl h)
  have hnac : ¬ G.Adj a c := fun h => hn (Or.inr (Or.inl h))
  have hnbc : ¬ G.Adj b c := fun h => hn (Or.inr (Or.inr h))
  exact hx ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hnab, hnac, hnbc⟩

/-- A neighborhood edge and three other neighbors force a claw or a four-cycle. -/
theorem false_of_edge_and_three_other_neighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x a b c d e : V} (hx : ¬ Claw G x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (he : G.Adj x e)
    (hab : G.Adj a b) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : False := by
  have hnac : ¬ G.Adj a c := by
    intro h
    exact hbc (neighborhood_matching G hG hb ha hc hab.symm h)
  have hnad : ¬ G.Adj a d := by
    intro h
    exact hbd (neighborhood_matching G hG hb ha hd hab.symm h)
  have hnae : ¬ G.Adj a e := by
    intro h
    exact hbe (neighborhood_matching G hG hb ha he hab.symm h)
  have ecd : G.Adj c d := by
    rcases edge_of_not_claw G hx hac had hcd ha hc hd with h | h | h
    · exact (hnac h).elim
    · exact (hnad h).elim
    · exact h
  have ece : G.Adj c e := by
    rcases edge_of_not_claw G hx hac hae hce ha hc he with h | h | h
    · exact (hnac h).elim
    · exact (hnae h).elim
    · exact h
  exact hde (neighborhood_matching G hG hd hc he ecd.symm ece)

private theorem degree_le_four_of_edge {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x a b : V} (hx : ¬ Claw G x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hab : G.Adj a b) :
    G.degree x ≤ 4 := by
  classical
  let s := (G.neighborFinset x).erase a
  let t := s.erase b
  have hma : a ∈ G.neighborFinset x := (G.mem_neighborFinset x a).mpr ha
  have hmb : b ∈ s := by
    simp [s, hab.ne.symm, hb]
  have hca : s.card + 1 = G.degree x := Finset.card_erase_add_one hma
  have hcb : t.card + 1 = s.card := Finset.card_erase_add_one hmb
  by_contra hlarge
  have ht : 2 < t.card := by omega
  obtain ⟨c, hc, d, hd, e, he, hcd, hce, hde⟩ := Finset.two_lt_card.mp ht
  have hc' : c ≠ b ∧ c ≠ a ∧ G.Adj x c := by simpa [t, s] using hc
  have hd' : d ≠ b ∧ d ≠ a ∧ G.Adj x d := by simpa [t, s] using hd
  have he' : e ≠ b ∧ e ≠ a ∧ G.Adj x e := by simpa [t, s] using he
  exact false_of_edge_and_three_other_neighbors G hG hx ha hb hc'.2.2 hd'.2.2 he'.2.2
    hab hc'.1.symm hd'.1.symm he'.1.symm hc'.2.1.symm hd'.2.1.symm he'.2.1.symm
    hcd hce hde

/-- Every nonclaw vertex of a counterexample has degree three or four. -/
theorem degree_three_or_four_of_not_claw {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x : V} (hx : ¬ Claw G x) : G.degree x = 3 ∨ G.degree x = 4 := by
  classical
  have hmin := hG.degree_ge_three x
  have ht : 2 < (G.neighborFinset x).card := by
    change 2 < G.degree x
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp ht
  have ha' := (G.mem_neighborFinset x a).mp ha
  have hb' := (G.mem_neighborFinset x b).mp hb
  have hc' := (G.mem_neighborFinset x c).mp hc
  have hmax : G.degree x ≤ 4 := by
    rcases edge_of_not_claw G hx hab hac hbc ha' hb' hc' with eab | eac | ebc
    · exact degree_le_four_of_edge G hG hx ha' hb' eab
    · exact degree_le_four_of_edge G hG hx ha' hc' eac
    · exact degree_le_four_of_edge G hG hx hb' hc' ebc
  omega

/-- Away from the unique claw center, degrees are exactly three or four. -/
theorem degree_three_or_four_off_center {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v x : V} (hu : ∀ w, Claw G w → w = v) (hx : x ≠ v) :
    G.degree x = 3 ∨ G.degree x = 4 := by
  apply degree_three_or_four_of_not_claw G hG
  exact fun hc => hx (hu x hc)

/-- At a cubic vertex, all neighborhood edges have the same unordered endpoints. -/
theorem neighbor_edge_eq_at_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x a b d e : V} (hx : G.degree x = 3)
    (ha : G.Adj x a) (hb : G.Adj x b) (hab : G.Adj a b)
    (hd : G.Adj x d) (he : G.Adj x e) (hde : G.Adj d e) :
    (d = a ∧ e = b) ∨ (d = b ∧ e = a) := by
  classical
  let s := ((G.neighborFinset x).erase a).erase b
  have hma : a ∈ G.neighborFinset x := (G.mem_neighborFinset x a).mpr ha
  have hmb : b ∈ (G.neighborFinset x).erase a := by
    simp [hab.ne.symm, hb]
  have hca := Finset.card_erase_add_one hma
  have hcb := Finset.card_erase_add_one hmb
  have hs : s.card = 1 := by
    change (((G.neighborFinset x).erase a).erase b).card = 1
    change (G.neighborFinset x).card = 3 at hx
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hc' : c ≠ b ∧ c ≠ a ∧ G.Adj x c := by simpa [s] using hc
  have hneighbors := neighbors_eq_claw_leaves G hx hab.ne hc'.2.1.symm hc'.1.symm
    ha hb hc'.2.2
  have hnac : ¬ G.Adj a c := by
    intro h
    exact hc'.1.symm (neighborhood_matching G hG hb ha hc'.2.2 hab.symm h)
  have hnbc : ¬ G.Adj b c := by
    intro h
    exact hc'.2.1.symm (neighborhood_matching G hG ha hb hc'.2.2 hab h)
  rcases (hneighbors d).mp hd with rfl | rfl | rfl <;>
    rcases (hneighbors e).mp he with rfl | rfl | rfl
  all_goals simp_all [SimpleGraph.adj_comm]

/-- A cubic nonclaw vertex lies in exactly one triangle, expressed by its two other vertices. -/
theorem exists_unique_triangle_at_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x : V} (hx : G.degree x = 3) (hn : ¬ Claw G x) :
    ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b ∧
      ∀ d e, G.Adj x d → G.Adj x e → G.Adj d e →
        (d = a ∧ e = b) ∨ (d = b ∧ e = a) := by
  classical
  have ht : 2 < (G.neighborFinset x).card := by
    change 2 < G.degree x
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp ht
  have ha' := (G.mem_neighborFinset x a).mp ha
  have hb' := (G.mem_neighborFinset x b).mp hb
  have hc' := (G.mem_neighborFinset x c).mp hc
  have hpair : ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b := by
    rcases edge_of_not_claw G hn hab hac hbc ha' hb' hc' with eab | eac | ebc
    · exact ⟨a, b, ha', hb', eab⟩
    · exact ⟨a, c, ha', hc', eac⟩
    · exact ⟨b, c, hb', hc', ebc⟩
  obtain ⟨d, e, hd, he, hde⟩ := hpair
  refine ⟨d, e, hd, he, hde, ?_⟩
  intro a b ha hb hab
  exact neighbor_edge_eq_at_degree_three G hG hx hd he hde ha hb hab

/-- At a degree-four nonclaw vertex, the neighborhood consists of two disjoint edges. -/
theorem exists_two_triangles_at_degree_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {x : V} (hx : G.degree x = 4) (hn : ¬ Claw G x) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj x a ∧ G.Adj x b ∧ G.Adj x c ∧ G.Adj x d ∧
      G.Adj a b ∧ G.Adj c d ∧
      (∀ y, G.Adj x y ↔ y = a ∨ y = b ∨ y = c ∨ y = d) ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
  classical
  have ht : 2 < (G.neighborFinset x).card := by
    change 2 < G.degree x
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp ht
  have ha' := (G.mem_neighborFinset x a).mp ha
  have hb' := (G.mem_neighborFinset x b).mp hb
  have hc' := (G.mem_neighborFinset x c).mp hc
  have hpair : ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b := by
    rcases edge_of_not_claw G hn hab hac hbc ha' hb' hc' with eab | eac | ebc
    · exact ⟨a, b, ha', hb', eab⟩
    · exact ⟨a, c, ha', hc', eac⟩
    · exact ⟨b, c, hb', hc', ebc⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hpair
  let s := ((G.neighborFinset x).erase a).erase b
  have hma : a ∈ G.neighborFinset x := (G.mem_neighborFinset x a).mpr ha
  have hmb : b ∈ (G.neighborFinset x).erase a := by simp [hab.ne.symm, hb]
  have hca := Finset.card_erase_add_one hma
  have hcb := Finset.card_erase_add_one hmb
  have hs : s.card = 2 := by
    change (((G.neighborFinset x).erase a).erase b).card = 2
    change (G.neighborFinset x).card = 4 at hx
    omega
  obtain ⟨c, d, hcd, hset⟩ := Finset.card_eq_two.mp hs
  have hc : c ∈ s := by rw [hset]; simp
  have hd : d ∈ s := by rw [hset]; simp
  have hc' : c ≠ b ∧ c ≠ a ∧ G.Adj x c := by simpa [s] using hc
  have hd' : d ≠ b ∧ d ≠ a ∧ G.Adj x d := by simpa [s] using hd
  have hnac : ¬ G.Adj a c := by
    intro h
    exact hc'.1.symm (neighborhood_matching G hG hb ha hc'.2.2 hab.symm h)
  have hnad : ¬ G.Adj a d := by
    intro h
    exact hd'.1.symm (neighborhood_matching G hG hb ha hd'.2.2 hab.symm h)
  have hnbc : ¬ G.Adj b c := by
    intro h
    exact hc'.2.1.symm (neighborhood_matching G hG ha hb hc'.2.2 hab h)
  have hnbd : ¬ G.Adj b d := by
    intro h
    exact hd'.2.1.symm (neighborhood_matching G hG ha hb hd'.2.2 hab h)
  have ecd : G.Adj c d := by
    rcases edge_of_not_claw G hn hc'.2.1.symm hd'.2.1.symm hcd ha hc'.2.2 hd'.2.2
      with h | h | h
    · exact (hnac h).elim
    · exact (hnad h).elim
    · exact h
  have hneighbors : ∀ y, G.Adj x y ↔ y = a ∨ y = b ∨ y = c ∨ y = d := by
    intro y
    constructor
    · intro hy
      by_cases hya : y = a
      · exact Or.inl hya
      by_cases hyb : y = b
      · exact Or.inr (Or.inl hyb)
      have hys : y ∈ s := by simp [s, hya, hyb, hy]
      rw [hset] at hys
      exact Or.inr (Or.inr (by simpa using hys))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hc'.2.2
      · exact hd'.2.2
  exact ⟨a, b, c, d, hab.ne, hc'.2.1.symm, hd'.2.1.symm, hc'.1.symm,
    hd'.1.symm, hcd, ha, hb, hc'.2.2, hd'.2.2, hab, ecd, hneighbors,
    hnac, hnad, hnbc, hnbd⟩

/-- A claw center whose neighborhood contains an edge has degree at least four. -/
theorem center_degree_ge_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a b : V} (hc : Claw G v)
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : G.Adj a b) :
    4 ≤ G.degree v := by
  have hmin := hG.degree_ge_three v
  have hne : G.degree v ≠ 3 := by
    intro hv
    exact poles_nonadjacent G hv hc ha hb hab
  omega

/-- Under HIGH, every neighbor of a high vertex has degree exactly three. -/
theorem neighbor_degree_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v a : V} (hv : 4 ≤ G.degree v) (ha : G.Adj v a) :
    G.degree a = 3 := by
  have hmin := hG.degree_ge_three a
  have hnot : ¬ 4 ≤ G.degree a := fun hh => hHIGH v a hv hh ha
  omega

end Erdos64.TriangleIncidenceLocal
