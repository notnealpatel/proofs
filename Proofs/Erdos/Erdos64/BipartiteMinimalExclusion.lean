import Erdos.Erdos64.BipartiteMinimalCubic
import Erdos.Erdos64.BipartiteCubicVertexRepair

/-!
# Conditional exclusion of properly Bool-colored minimal counterexamples

Global vertex minimality ranges over all finite nonempty ordinary minimum-degree-three
simple graphs in the same universe, not just bipartite or cubic graphs. The repair
has strictly fewer vertices and transports every even genuine cycle at exactly its
length. No counterexample existence, arbitrary bipartite E64 theorem, unconditional
E64 closure, novelty, or WLOG claim is asserted.

The counterexample hypotheses have no known concrete model. Their conjunction with
proper coloring and global minimality is precisely what this module disproves;
a joint satisfiability example for that conjunction would contradict the result.
-/

set_option autoImplicit false
universe u

namespace Erdos64.BipartiteMinimalExclusion

open SimpleGraph
open scoped Classical

/-- A counterexample globally vertex-minimal among all finite nonempty ordinary
minimum-degree-three simple graphs in `Type u` cannot admit a proper Bool coloring.
Cubicity and a strictly smaller repair are consequences of the hypotheses, and an
exact-length lift of an even dyadic cycle contradicts the counterexample predicate. -/
theorem proper_coloring_excluded {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hCE : IsCounterexample G)
    (hminimal : ∀ (W : Type u) [Fintype W] [Nonempty W] (Q : SimpleGraph W),
      Fintype.card W < Fintype.card V → (∀ v, 3 ≤ Q.degree v) → HasPowerOfTwoCycle Q)
    (c : V → Bool) (hc : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) : False := by
  classical
  have hpos : 0 < Fintype.card V := by
    have hfour := hCE.card_verts_ge_four
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hd : G.degree v = 3 :=
    BipartiteMinimalCubic.degree_eq_three G hCE hminimal c hc v
  obtain ⟨R, horder⟩ :=
    @BipartiteCubicVertexRepair.exists_repair V inferInstance G c hc
      (fun x => by
        convert hCE.degree_ge_three x using 1
        congr 1
        exact Subsingleton.elim _ _) v (by
        convert hd using 1
        congr 1
        exact Subsingleton.elim _ _)
  letI : Fintype R.Vertex := R.vertices
  letI : Nonempty R.Vertex := R.inhabited
  obtain ⟨k, hk, x, w, hw, hlen⟩ :=
    hminimal R.Vertex R.graph horder R.min_degree
  have heven : Even (2 ^ k) :=
    (Nat.even_pow' (by omega : k ≠ 0)).mpr (by decide)
  obtain ⟨y, p, hp, hplen⟩ := R.even_cycles (2 ^ k) heven ⟨x, w, hw, hlen⟩
  exact hCE.not_hasPowerOfTwoCycle ⟨k, hk, y, p, hp, hplen⟩

/-- The existing lexicographic minimal-counterexample hypothesis supplies global
vertex minimality, hence excludes every proper Bool coloring. This conditional
statement neither asserts a counterexample exists nor proves E64 unconditionally. -/
theorem not_exists_proper_coloring_of_minimal {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) :
    ¬ ∃ c : V → Bool, ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y := by
  classical
  rintro ⟨c, hc⟩
  apply proper_coloring_excluded G hmin.isCounterexample ?_ c hc
  intro W _ _ Q horder hdegree
  by_contra hfree
  have hQ : IsCounterexample Q := ⟨inferInstance, hdegree, hfree⟩
  exact hmin.not_size_lexLt Q hQ (Or.inl horder)

end Erdos64.BipartiteMinimalExclusion
