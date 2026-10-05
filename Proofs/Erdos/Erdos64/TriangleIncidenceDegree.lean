import Erdos.Erdos64.TriangleIncidenceActualModel

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph UniqueCubicClawCenter TriangleIncidenceLocal

universe u

/-- Auxiliary adjacency is classically decidable without an additional public binder. -/
noncomputable instance auxiliaryDecidableRel {V : Type u} (G : SimpleGraph V) (v : V) :
    DecidableRel (auxiliary G v).Adj := Classical.decRel _

/-- An actual triangle node in the auxiliary graph has degree exactly three. -/
theorem auxiliary_triangle_degree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hv : 4 ≤ G.degree v) (s : Triangle G) :
    (auxiliary G v).degree (some s) = 3 := by
  classical
  let D := actualModel G hG hu hHIGH hv
  let f : (auxiliary G v).neighborSet (some s) → {a : V // a ∈ s.val} := fun y =>
    ⟨chosenPort G v (some s) y.val, D.port_mem (some s) y.val (by simp) y.property⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact D.port_injective (some s) x.val y.val (by simp) x.property y.property
        (congrArg Subtype.val hxy)
    · intro a
      obtain ⟨y, hy, heq⟩ := D.port_surjective (some s) a.val (by simp) a.property
      exact ⟨⟨y, hy⟩, Subtype.ext heq⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f hbij)
  rw [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_coe, s.property.card_eq] at hcard
  exact hcard

/-- A cubic neighbor of the original root gives an auxiliary neighbor at its triangle. -/
theorem auxiliary_root_adj {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v a : V} (ha : G.degree a = 3) (hva : G.Adj v a)
    (s : Triangle G) (hsa : a ∈ s.val) : (auxiliary G v).Adj none (some s) := by
  classical
  by_cases hsv : v ∈ s.val
  · exact ⟨v, v, root_connector G s hsv⟩
  · have hordinary : NontriangleEdge G v a := by
      refine ⟨hva, ?_⟩
      intro t htv hta
      have hts := triangle_eq_of_degree_three G hG ha t s hta hsa
      subst t
      exact hsv htv
    exact ⟨v, a, by
      refine ⟨by simp, rfl, hsa, Or.inr ⟨Or.inr rfl, Or.inl hva.ne.symm, hordinary⟩⟩⟩

/-- The three leaves of the original claw give three distinct auxiliary root neighbors. -/
theorem auxiliary_root_degree_ge_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hv : 4 ≤ G.degree v) : 3 ≤ (auxiliary G v).degree none := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hva, hvb, hvc, hnab, hnac, hnbc⟩ := hc
  have hal := neighbor_degree_three G hG hHIGH hv hva
  have hbl := neighbor_degree_three G hG hHIGH hv hvb
  have hcl := neighbor_degree_three G hG hHIGH hv hvc
  obtain ⟨s, hsa⟩ := cubic_triangle_exists G hG hu hva.ne.symm hal
  obtain ⟨t, htb⟩ := cubic_triangle_exists G hG hu hvb.ne.symm hbl
  obtain ⟨r, hrc⟩ := cubic_triangle_exists G hG hu hvc.ne.symm hcl
  have hst : s ≠ t := by
    intro heq
    subst t
    exact hnab (s.property.isClique hsa htb hab)
  have hsr : s ≠ r := by
    intro heq
    subst r
    exact hnac (s.property.isClique hsa hrc hac)
  have htr : t ≠ r := by
    intro heq
    subst r
    exact hnbc (t.property.isClique htb hrc hbc)
  have hsub : ({some s, some t, some r} : Finset (Node G)) ⊆
      (auxiliary G v).neighborFinset none := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ((auxiliary G v).mem_neighborFinset none _).mpr
        (auxiliary_root_adj G hG hal hva s hsa)
    · exact ((auxiliary G v).mem_neighborFinset none _).mpr
        (auxiliary_root_adj G hG hbl hvb t htb)
    · exact ((auxiliary G v).mem_neighborFinset none _).mpr
        (auxiliary_root_adj G hG hcl hvc r hrc)
  have hcard := Finset.card_le_card hsub
  simpa [hst, hsr, htr] using hcard

/-- The auxiliary triangle-incidence graph has minimum degree at least three. -/
theorem auxiliary_degree_ge_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {v : V} (hc : Claw G v) (hu : ∀ w, Claw G w → w = v)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    (hv : 4 ≤ G.degree v) : ∀ x, 3 ≤ (auxiliary G v).degree x := by
  intro x
  cases x with
  | none => exact auxiliary_root_degree_ge_three G hG hc hu hHIGH hv
  | some s => exact (auxiliary_triangle_degree G hG hu hHIGH hv s).ge

end Erdos64.TriangleIncidence
