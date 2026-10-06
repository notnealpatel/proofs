import Erdos.Erdos64.TwoCubicClawCentersContraction

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TwoCubicClawCentersContraction

universe u

/-- The adjacent auxiliary roots have no common neighbor at all. Root looplessness
and the original four-cycle exclusion also exclude every triangle neighbor in common. -/
theorem roots_no_common_neighbor {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩))
    (x : Node G) (hU : (auxiliary G u v).Adj (.inl ⟨false⟩) x)
    (hV : (auxiliary G u v).Adj (.inl ⟨true⟩) x) : False := by
  cases x with
  | inl r =>
    rcases r with ⟨r⟩
    cases r
    · exact hU.ne rfl
    · exact hV.ne rfl
  | inr A =>
    exact adjacent_roots_no_common_triangle G hG huv hCenters hcu hcv hdu hdv hUV A hU hV

/-- The two external neighbors of each auxiliary root form four distinct nodes. -/
theorem four_external_neighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq (Node G)] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩)) :
    (((auxiliary G u v).neighborFinset (.inl ⟨false⟩)).erase (.inl ⟨true⟩) ∪
      ((auxiliary G u v).neighborFinset (.inl ⟨true⟩)).erase (.inl ⟨false⟩)).card = 4 := by
  classical
  exact card_external_neighbors (auxiliary G u v) _ _ hUV
    (auxiliary_first_root_degree G hG huv hCenters hcu hcv hdu hdv)
    (auxiliary_second_root_degree G hG huv hCenters hcu hcv hdu hdv)
    (roots_no_common_neighbor G hG huv hCenters hcu hcv hdu hdv hUV)

/-- The root-contracted auxiliary has minimum degree three: the retained root has
four distinct neighbors and all other vertices retain their cubic degree. -/
theorem contracted_auxiliary_min_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩))
    [DecidableRel (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)).Adj]
    (x : {a : Node G // a ≠ .inl ⟨true⟩}) :
    3 ≤ (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)).degree x := by
  classical
  have hcommon := roots_no_common_neighbor G hG huv hCenters hcu hcv hdu hdv hUV
  by_cases hx : x.val = .inl ⟨false⟩
  · have he : x = ⟨.inl ⟨false⟩, roots_ne G⟩ := Subtype.ext hx
    rw [he, degree_root (auxiliary G u v) _ _ (roots_ne G) hUV
      (auxiliary_first_root_degree G hG huv hCenters hcu hcv hdu hdv)
      (auxiliary_second_root_degree G hG huv hCenters hcu hcv hdu hdv) hcommon]
    decide
  · rw [degree_nonroot (auxiliary G u v) _ _ (roots_ne G) hcommon x hx,
      auxiliary_cubic G hG huv hCenters hcu hcv hdu hdv x.val]

/-- Unrestricted original order minimality supplies a dyadic cycle after contracting
only the auxiliary root edge. No inherited HIGH or claw condition is imposed on this graph. -/
theorem contracted_auxiliary_hasPowerOfTwoCycle {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    (hminimal : ∀ {W : Type u} [Fintype W] [Nonempty W]
      (Q : SimpleGraph W) [DecidableRel Q.Adj],
      Fintype.card W < Fintype.card V → (∀ x, 3 ≤ Q.degree x) → HasPowerOfTwoCycle Q)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v) (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩))
    [DecidableRel (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)).Adj] :
    HasPowerOfTwoCycle (contracted (auxiliary G u v) (.inl ⟨false⟩) (.inl ⟨true⟩)) := by
  classical
  letI : Nonempty {a : Node G // a ≠ .inl ⟨true⟩} := ⟨⟨.inl ⟨false⟩, roots_ne G⟩⟩
  have horder : Fintype.card {a : Node G // a ≠ .inl ⟨true⟩} < Fintype.card V :=
    lt_trans (Fintype.card_subtype_lt (p := fun a : Node G => a ≠ .inl ⟨true⟩)
      (x := .inl ⟨true⟩) (by intro hn; exact hn rfl))
      (card_node_lt G hG huv hCenters hcu hcv hdu hdv hHIGH)
  exact hminimal _ horder
    (contracted_auxiliary_min_degree G hG huv hCenters hcu hcv hdu hdv hUV)

end Erdos64.TwoCubicClawCentersQuotient
