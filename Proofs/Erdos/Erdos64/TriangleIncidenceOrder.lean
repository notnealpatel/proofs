import Erdos.Erdos64.TriangleIncidenceTriangles
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter

universe u

/-- With HIGH and a high root, the root together with the actual triangle nodes
has strictly fewer elements than the original vertex set, provided a triangle exists. -/
theorem card_node_lt {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    {v : V} (hv : 4 ≤ G.degree v) (hT : Nonempty (Triangle G)) :
    Fintype.card (Option (Triangle G)) < Fintype.card V := by
  classical
  have hpairs := fun s : Triangle G => two_low_vertices G hG hHIGH hv s
  choose a b ha hb hab hda hdb hav hbv using hpairs
  let f : Option (Triangle G) → V := fun t =>
    match t with
    | none => v
    | some s => a s
  have hinj : Function.Injective f := by
    intro s t hst
    cases s with
    | none =>
      cases t with
      | none => rfl
      | some t => exact ((hav t) hst.symm).elim
    | some s =>
      cases t with
      | none => exact ((hav s) hst).elim
      | some t =>
        have hat : a s ∈ t.val := by
          change a s = a t at hst
          rw [hst]
          exact ha t
        have heq := triangle_eq_of_degree_three G hG (hda s) s t (ha s) hat
        exact congrArg some heq
  obtain ⟨t⟩ := hT
  have hnot : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨s, hs⟩ := hsurj (b t)
    cases s with
    | none => exact ((hbv t) hs.symm).elim
    | some s =>
      change a s = b t at hs
      have hbs : b t ∈ s.val := by
        rw [← hs]
        exact ha s
      have heq := triangle_eq_of_degree_three G hG (hdb t) s t hbs (hb t)
      subst s
      exact (hab t) hs
  exact Fintype.card_lt_of_injective_not_surjective f hinj hnot

end Erdos64.TriangleIncidence
