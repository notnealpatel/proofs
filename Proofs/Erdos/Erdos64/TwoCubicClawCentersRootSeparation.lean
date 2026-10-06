import Erdos.Erdos64.TwoCubicClawCentersCycleLift

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

/-- The original vertex represented by either singleton root. -/
def rootVertex {V : Type u} (u v : V) (r : ULift.{u} Bool) : V :=
  if r.down then v else u

example {V : Type u} (u v : V) : rootVertex u v ⟨false⟩ = u := rfl
example {V : Type u} (u v : V) : rootVertex u v ⟨true⟩ = v := rfl

section

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsCounterexample G) {u v : V} (huv : u ≠ v)
    (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)

include hG

/-- Every chosen port at a singleton root is the corresponding original center. -/
theorem root_port {r : ULift.{u} Bool} {x : Node G}
    (hx : (auxiliary G u v).Adj (.inl r) x) :
    chosenPort G u v (.inl r) x = rootVertex u v r := by
  have hp := port_mem G hG hx
  rcases r with ⟨r⟩
  cases r <;> exact hp

include huv hcu hcv hdu hdv

/-- A connector incident to a singleton root is an ordinary original edge. -/
theorem root_connector_edge {r : ULift.{u} Bool} {x : Node G}
    (hx : (auxiliary G u v).Adj (.inl r) x) :
    NontriangleEdge G (rootVertex u v r) (chosenPort G u v x (.inl r)) := by
  have ce := chosen_connector G hG hx
  rcases ce.2.2.2 with hz | he
  · have cz := ce
    rw [← hz] at cz
    obtain ⟨A, B, hr, _⟩ := equal_connector_triangles G hG huv hcu hcv hdu hdv cz
    cases hr
  · simpa only [root_port G hG hx] using he

omit hG huv in
/-- A singleton root's original center does not belong to an actual triangle. -/
theorem root_not_mem_triangle (r : ULift.{u} Bool) (A : Triangle G) :
    rootVertex u v r ∉ A.val := by
  rcases r with ⟨r⟩
  cases r
  · exact center_not_mem_triangle G hdu hcu A
  · exact center_not_mem_triangle G hdv hcv A

include hCenters

/-- Distinct triangle neighbors of the same retained root have disjoint original labels;
otherwise that root and the shared triangle label lie on an original four-cycle. -/
theorem root_neighbors_disjoint {r : ULift.{u} Bool} {A B : Triangle G}
    (hA : (auxiliary G u v).Adj (.inl r) (.inr A))
    (hB : (auxiliary G u v).Adj (.inl r) (.inr B)) (hAB : A ≠ B) :
    Disjoint A.val B.val := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  let b := chosenPort G u v (.inr A) (.inl r)
  let d := chosenPort G u v (.inr B) (.inl r)
  have eb := root_connector_edge G hG huv hcu hcv hdu hdv hA
  have ed := root_connector_edge G hG huv hcu hcv hdu hdv hB
  have hdb : G.degree b = 3 := ordinary_endpoint_degree_three G hG hCenters hdu hdv eb.symm
  have hdd : G.degree d = 3 := ordinary_endpoint_degree_three G hG hCenters hdu hdv ed.symm
  have hmb : b ∈ A.val := port_mem G hG hA.symm
  have hmd : d ∈ B.val := port_mem G hG hB.symm
  have hbd : b ≠ d := by
    intro he
    have heq := member_node_unique G hG huv hcu hcv hdu hdv hdb
      (x := .inr A) (y := .inr B) hmb (he.symm ▸ hmd)
    exact hAB (Sum.inr.inj heq)
  have hab : a ≠ b := by
    intro he
    have heq := member_node_unique G hG huv hcu hcv hdu hdv hdb
      (x := .inr A) (y := .inr B) (he ▸ ha) (he ▸ hb)
    exact hAB (Sum.inr.inj heq)
  have had : a ≠ d := by
    intro he
    have heq := member_node_unique G hG huv hcu hcv hdu hdv hdd
      (x := .inr A) (y := .inr B) (he ▸ ha) (he ▸ hb)
    exact hAB (Sum.inr.inj heq)
  have haw : a ≠ rootVertex u v r := fun he =>
    root_not_mem_triangle G hcu hcv hdu hdv r A (he ▸ ha)
  exact no_two_pole_neighbors G hG haw eb.1 ed.1 hbd
    (A.property.isClique ha hmb hab) (B.property.isClique hb hmd had)

/-- Adjacent retained roots have no common triangle neighbor; a common triangle
would complete their original edge into an original four-cycle. -/
theorem adjacent_roots_no_common_triangle
    (hUV : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inl ⟨true⟩))
    (A : Triangle G)
    (hA : (auxiliary G u v).Adj (.inl ⟨false⟩) (.inr A))
    (hB : (auxiliary G u v).Adj (.inl ⟨true⟩) (.inr A)) : False := by
  let a := chosenPort G u v (.inr A) (.inl ⟨false⟩)
  let b := chosenPort G u v (.inr A) (.inl ⟨true⟩)
  have ea := root_connector_edge G hG huv hcu hcv hdu hdv hA
  have eb := root_connector_edge G hG huv hcu hcv hdu hdv hB
  have euv := (root_connector_edge G hG huv hcu hcv hdu hdv hUV).1
  rw [root_port G hG hUV.symm] at euv
  have ha : a ∈ A.val := port_mem G hG hA.symm
  have hb : b ∈ A.val := port_mem G hG hB.symm
  have hab : a ≠ b := ports_ne G hG huv hCenters hcu hcv hdu hdv True.intro
    hA.symm hB.symm (by
      intro he
      have hbool := congrArg ULift.down (Sum.inl.inj he)
      cases hbool)
  have hub : u ≠ b := fun he => center_not_mem_triangle G hdu hcu A (he.symm ▸ hb)
  have hav : a ≠ v := fun he => center_not_mem_triangle G hdv hcv A (he ▸ ha)
  have hbv : b ≠ v := fun he => center_not_mem_triangle G hdv hcv A (he ▸ hb)
  exact not_four_cycle G hG ea.1.ne hub huv hab hav hbv ea.1
    (A.property.isClique ha hb hab) eb.1.symm euv.symm

end

end Erdos64.TwoCubicClawCentersQuotient
