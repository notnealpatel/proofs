import Erdos.Erdos64.TriangleIncidenceDegree
import Erdos.Erdos64.TriangleIncidenceOrder

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

/-- Unrestricted smaller-order minimality gives a dyadic cycle in the actual
triangle-incidence graph when the unique claw center has adjacent neighbors. -/
theorem auxiliary_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W] (Q : SimpleGraph W)
      [DecidableRel Q.Adj], Fintype.card W < Fintype.card V →
        (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {v a b : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : G.Adj a b) :
    HasPowerOfTwoCycle (auxiliary G v) := by
  classical
  have hv := center_degree_ge_four G hG hc ha hb hab
  obtain ⟨s, hsa, hsb, hsc⟩ := exists_triangle_of_edges G ha hb hab
  have hT : Nonempty (Triangle G) := ⟨s⟩
  have hcard := card_node_lt G hG hHIGH hv hT
  have hdegree := auxiliary_degree_ge_three G hG hc hu hHIGH hv
  exact hminimal (auxiliary G v) hcard hdegree

end Erdos64.TriangleIncidence
