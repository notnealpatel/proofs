import Erdos.Erdos64.TwoCubicClawCentersDegree
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence TriangleIncidenceLocal

universe u

/-- Under HIGH, every actual triangle has two distinct cubic original vertices. -/
theorem two_low_vertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (s : Triangle G) :
    ∃ a b, a ∈ s.val ∧ b ∈ s.val ∧ a ≠ b ∧ G.degree a = 3 ∧ G.degree b = 3 := by
  classical
  have hpos : 0 < s.val.card := by rw [s.property.card_eq]; decide
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨a, b, hab, hax, hbx, ha, hb, eab, hmem⟩ := triangle_vertices G s hx
  have hma : a ∈ s.val := (hmem a).mpr (Or.inr (Or.inl rfl))
  have hmb : b ∈ s.val := (hmem b).mpr (Or.inr (Or.inr rfl))
  by_cases hxh : 4 ≤ G.degree x
  · exact ⟨a, b, hma, hmb, hab,
      neighbor_degree_three G hG hHIGH hxh ha,
      neighbor_degree_three G hG hHIGH hxh hb⟩
  by_cases hah : 4 ≤ G.degree a
  · exact ⟨x, b, hx, hmb, hbx.symm,
      neighbor_degree_three G hG hHIGH hah ha.symm,
      neighbor_degree_three G hG hHIGH hah eab⟩
  · have hxmin := hG.degree_ge_three x
    have hamin := hG.degree_ge_three a
    exact ⟨x, a, hx, hma, hax.symm, by omega, by omega⟩

/-- The two-center original hypotheses force the existence of an actual triangle. -/
theorem triangle_nonempty {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hdu : G.degree u = 3) : Nonempty (Triangle G) := by
  classical
  have hcard : ({v} : Finset V).card < (G.neighborFinset u).card := by
    change ({v} : Finset V).card < G.degree u
    simp [hdu]
  obtain ⟨a, ha, hav⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hea := (G.mem_neighborFinset u a).mp ha
  have hav' : a ≠ v := by simpa using hav
  obtain ⟨s, _⟩ := noncenter_triangle_exists G hG hCenters hea.ne.symm hav'
  exact ⟨s⟩

/-- The actual two-root auxiliary has strictly smaller order than the original graph.
Its triangle representatives are cubic; a second cubic port of one triangle is omitted. -/
theorem card_node_lt {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    Fintype.card (Node G) < Fintype.card V := by
  classical
  have hpairs := fun s : Triangle G => two_low_vertices G hG hHIGH s
  choose a b ha hb hab hda hdb using hpairs
  have hau (s : Triangle G) : a s ≠ u := by
    intro he
    exact center_not_mem_triangle G hdu hcu s (he ▸ ha s)
  have hav (s : Triangle G) : a s ≠ v := by
    intro he
    exact center_not_mem_triangle G hdv hcv s (he ▸ ha s)
  let f : Node G → V
    | .inl ⟨false⟩ => u
    | .inl ⟨true⟩ => v
    | .inr s => a s
  have hinj : Function.Injective f := by
    intro s t he
    cases s with
    | inl i =>
      rcases i with ⟨i⟩
      cases i <;> cases t with
      | inl j =>
        rcases j with ⟨j⟩
        cases j
        all_goals first | rfl | exact (huv he).elim | exact (huv he.symm).elim
      | inr t =>
        first | exact ((hau t) he.symm).elim | exact ((hav t) he.symm).elim
    | inr s =>
      cases t with
      | inl j =>
        rcases j with ⟨j⟩
        cases j
        · exact ((hau s) he).elim
        · exact ((hav s) he).elim
      | inr t =>
        have hat : a s ∈ t.val := by
          change a s = a t at he
          rw [he]
          exact ha t
        exact congrArg Sum.inr (triangle_eq_of_degree_three G hG (hda s) s t (ha s) hat)
  obtain ⟨t⟩ := triangle_nonempty G hG hCenters hdu
  have hnot : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨s, hs⟩ := hsurj (b t)
    cases s with
    | inl i =>
      rcases i with ⟨i⟩
      cases i
      · change u = b t at hs
        exact center_not_mem_triangle G hdu hcu t (hs.symm ▸ hb t)
      · change v = b t at hs
        exact center_not_mem_triangle G hdv hcv t (hs.symm ▸ hb t)
    | inr s =>
      change a s = b t at hs
      have hbs : b t ∈ s.val := by rw [← hs]; exact ha s
      have heq := triangle_eq_of_degree_three G hG (hdb t) s t hbs (hb t)
      subst s
      exact hab t hs
  exact Fintype.card_lt_of_injective_not_surjective f hinj hnot

/-- Unrestricted smaller-order minimality supplies a dyadic cycle in the internally
constructed actual two-center auxiliary. No original side class is imposed on it. -/
theorem auxiliary_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b) :
    HasPowerOfTwoCycle (auxiliary G u v) := by
  letI : Nonempty (Node G) := ⟨.inl ⟨false⟩⟩
  apply hminimal (auxiliary G u v) (card_node_lt G hG huv hCenters hcu hcv hdu hdv hHIGH)
  intro x
  exact (auxiliary_cubic G hG huv hCenters hcu hcv hdu hdv x).ge

end Erdos64.TwoCubicClawCentersQuotient
