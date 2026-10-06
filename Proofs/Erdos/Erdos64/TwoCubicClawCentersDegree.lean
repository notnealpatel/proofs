import Erdos.Erdos64.TwoCubicClawCentersQuotient

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

/-- Adjacency of the actual two-center incidence is classically decidable. -/
noncomputable instance auxiliaryDecidableRel {V : Type u} (G : SimpleGraph V) (u v : V) :
    DecidableRel (auxiliary G u v).Adj := Classical.decRel _

/-- Every actual triangle has exactly three distinct auxiliary neighbors, one per port. -/
theorem auxiliary_triangle_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) (s : Triangle G) :
    (auxiliary G u v).degree (.inr s) = 3 := by
  classical
  have hex (y : (auxiliary G u v).neighborSet (.inr s)) :
      ∃ a : {a : V // a ∈ s.val}, ∃ b, Connector G u v (.inr s) y.val a.val b := by
    obtain ⟨a, b, he⟩ := y.property
    exact ⟨⟨a, he.2.1⟩, b, he⟩
  let f : (auxiliary G u v).neighborSet (.inr s) → {a : V // a ∈ s.val} :=
    fun y => Classical.choose (hex y)
  have hf (y : (auxiliary G u v).neighborSet (.inr s)) :
      ∃ b, Connector G u v (.inr s) y.val (f y).val b := Classical.choose_spec (hex y)
  have hinj : Function.Injective f := by
    intro y z heq
    obtain ⟨b, hb⟩ := hf y
    obtain ⟨c, hc⟩ := hf z
    have hport := congrArg Subtype.val heq
    rw [hport] at hb
    exact Subtype.ext (connector_neighbor_unique G hG huv hCenters hcu hcv hdu hdv hb hc)
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨y, b, he⟩ := incidence_exists G hG hCenters hcu hcv hdu hdv s a.property
    let yy : (auxiliary G u v).neighborSet (.inr s) := ⟨y, a.val, b, he⟩
    obtain ⟨c, hc⟩ := hf yy
    refine ⟨yy, Subtype.ext ?_⟩
    exact (connector_ports_unique G hG hc he).1
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe, s.property.card_eq] at hcard
  exact hcard

private theorem singleton_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    (x : Node G) (r : V) (hdr : G.degree r = 3)
    (hmem : ∀ a, a ∈ members G u v x ↔ a = r)
    (hex : ∀ b, G.Adj r b → ∃ y, Connector G u v x y r b) :
    (auxiliary G u v).degree x = 3 := by
  classical
  have hports (y : (auxiliary G u v).neighborSet x) :
      ∃ b : G.neighborSet r, Connector G u v x y.val r b.val := by
    obtain ⟨a, b, he⟩ := y.property
    have har := (hmem a).mp he.2.1
    subst a
    have heb : G.Adj r b := by
      rcases he.2.2.2 with hrb | hrb
      · subst b
        exact (zero_port_not_cubic G hG huv hcu hcv hdu hdv he hdr).elim
      · exact hrb.1
    exact ⟨⟨b, heb⟩, he⟩
  let f : (auxiliary G u v).neighborSet x → G.neighborSet r :=
    fun y => Classical.choose (hports y)
  have hf (y : (auxiliary G u v).neighborSet x) :
      Connector G u v x y.val r (f y).val := Classical.choose_spec (hports y)
  have hinj : Function.Injective f := by
    intro y z heq
    have hy := hf y
    have hz := hf z
    have hport := congrArg Subtype.val heq
    rw [hport] at hy
    have hd : G.degree (f z).val = 3 := by
      rcases hz.2.2.2 with hrb | hrb
      · rw [← hrb]
        exact hdr
      · exact ordinary_endpoint_degree_three G hG hCenters hdu hdv hrb.symm
    exact Subtype.ext (member_node_unique G hG huv hcu hcv hdu hdv hd hy.2.2.1 hz.2.2.1)
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨y, he⟩ := hex b.val b.property
    let yy : (auxiliary G u v).neighborSet x := ⟨y, r, b.val, he⟩
    exact ⟨yy, Subtype.ext (connector_ports_unique G hG (hf yy) he).2⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree,
    hdr] at hcard
  exact hcard

/-- The first root retains its three original neighbors in the actual auxiliary. -/
theorem auxiliary_first_root_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) :
    (auxiliary G u v).degree (.inl ⟨false⟩) = 3 := by
  exact singleton_degree G hG huv hCenters hcu hcv hdu hdv (.inl ⟨false⟩) u hdu
    (fun _ => Iff.rfl) (fun _ he => root_incidence_exists G hG hCenters hcu hdu he)

/-- The second root retains its three original neighbors in the actual auxiliary. -/
theorem auxiliary_second_root_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) :
    (auxiliary G u v).degree (.inl ⟨true⟩) = 3 := by
  exact singleton_degree G hG huv hCenters hcu hcv hdu hdv (.inl ⟨true⟩) v hdv
    (fun _ => Iff.rfl) (fun _ he => second_root_incidence_exists G hG hCenters hcv hdv he)

/-- The actual auxiliary is cubic, without any cubicity assumption on the original graph. -/
theorem auxiliary_cubic {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) :
    ∀ x, (auxiliary G u v).degree x = 3 := by
  intro x
  cases x with
  | inl i =>
    rcases i with ⟨i⟩
    cases i
    · exact auxiliary_first_root_degree G hG huv hCenters hcu hcv hdu hdv
    · exact auxiliary_second_root_degree G hG huv hCenters hcu hcv hdu hdv
  | inr s => exact auxiliary_triangle_degree G hG huv hCenters hcu hcv hdu hdv s

end Erdos64.TwoCubicClawCentersQuotient
