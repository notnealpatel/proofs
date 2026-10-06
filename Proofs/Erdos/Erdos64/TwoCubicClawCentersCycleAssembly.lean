import Erdos.Erdos64.TwoCubicClawCentersCyclePorts
import Erdos.Erdos64.TriangleIncidenceThreeSlots

set_option autoImplicit false

namespace Erdos64.TwoCubicClawCentersQuotient

open SimpleGraph UniqueCubicClawCenter TriangleIncidence

universe u

noncomputable local instance cycleAssemblyPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Distinct members of an actual triangle are adjacent in the original graph. -/
theorem triangle_adj {V : Type u} (G : SimpleGraph V) {x : Node G} {a b : V}
    (hx : IsTriangle G x) (ha : a ∈ triangle G x) (hb : b ∈ triangle G x)
    (hab : a ≠ b) : G.Adj a b := by
  cases x with
  | inl i => exact hx.elim
  | inr s => exact s.property.isClique ha hb hab

/-- At a singleton root, all incidence ports equal its original center label. -/
theorem root_ports_eq {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} {x y z : Node G} (hx : ¬ IsTriangle G x)
    (hxy : (auxiliary G u v).Adj x y) (hxz : (auxiliary G u v).Adj x z) :
    chosenPort G u v x y = chosenPort G u v x z := by
  have hy := (chosen_connector G hG hxy).2.1
  have hz := (chosen_connector G hG hxz).2.1
  cases x with
  | inl i =>
    rcases i with ⟨i⟩
    cases i <;> exact hy.trans hz.symm
  | inr s => exact (hx True.intro).elim

/-- A selected set of fresh, distinct triangle spares produces an original simple cycle.
Its length counts the selected detours, triangle turns, and ordinary connectors literally. -/
theorem exists_cycle_of_spares {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsCounterexample G)
    {u v : V} (huv : u ≠ v) (hCenters : ∀ w, Claw G w → w = u ∨ w = v)
    (hcu : Claw G u) (hcv : Claw G v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3)
    {m : ℕ} (hm : 3 ≤ m + 1) (c : Fin (m + 1) → Node G) (hc : Function.Injective c)
    (hadj : ∀ i, (auxiliary G u v).Adj (c i) (c (i + 1))) (T : Finset (Fin (m + 1)))
    (s : Fin (m + 1) → V)
    (hTtri : ∀ i ∈ T, IsTriangle G (c i))
    (hsp : ∀ i ∈ T, s i ∈ triangle G (c i) ∧
      s i ≠ chosenPort G u v (c i) (c (i - 1)) ∧ s i ≠ chosenPort G u v (c i) (c (i + 1)))
    (hfresh : ∀ i ∈ T, ∀ j, s i ≠ chosenPort G u v (c j) (c (j - 1)) ∧
      s i ≠ chosenPort G u v (c j) (c (j + 1)))
    (hinj : Set.InjOn s (↑T : Set (Fin (m + 1))))
    (hlen : 3 ≤ T.card + (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
      (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
        chosenPort G u v (c (i + 1)) (c i))).card) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧
      p.length = T.card + (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
        (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
          chosenPort G u v (c (i + 1)) (c i))).card := by
  classical
  let I : Fin (m + 1) → V := fun i => chosenPort G u v (c i) (c (i - 1))
  let O : Fin (m + 1) → V := fun i => chosenPort G u v (c i) (c (i + 1))
  let L : Fin (m + 1) → Fin 3 → V := fun i r =>
    if r = 0 then I i else if r = 1 then (if i ∈ T then s i else I i) else O i
  have hprev (i : Fin (m + 1)) : (auxiliary G u v).Adj (c i) (c (i - 1)) := by
    simpa only [sub_add_cancel] using (hadj (i - 1)).symm
  have hroot (i : Fin (m + 1)) (hi : ¬ IsTriangle G (c i)) : I i = O i := by
    exact root_ports_eq G hG hi (hprev i) (hadj i)
  have hturn (i : Fin (m + 1)) : I i ≠ O i ↔ IsTriangle G (c i) := by
    constructor
    · intro h
      by_contra hi
      exact h (hroot i hi)
    · exact cycle_ports_ne G hG huv hCenters hcu hcv hdu hdv hm c hc hadj
  have hconn (i : Fin (m + 1)) : I (i + 1) = chosenPort G u v (c (i + 1)) (c i) := by
    simp only [I, add_sub_cancel_right]
  have hstep : ∀ i r, L i r = threeSlotNext L i r ∨
      G.Adj (L i r) (threeSlotNext L i r) := by
    intro i r
    fin_cases r
    · by_cases hi : i ∈ T
      · right
        simpa [L, threeSlotNext, hi] using triangle_adj G (hTtri i hi)
          (port_mem_triangle G hG (hTtri i hi) (hprev i)) (hsp i hi).1 (hsp i hi).2.1.symm
      · left
        simp [L, threeSlotNext, hi]
    · by_cases hi : i ∈ T
      · right
        simpa [L, threeSlotNext, hi] using triangle_adj G (hTtri i hi)
          (hsp i hi).1 (port_mem_triangle G hG (hTtri i hi) (hadj i)) (hsp i hi).2.2
      · by_cases hr : IsTriangle G (c i)
        · right
          simpa [L, threeSlotNext, hi] using triangle_adj G hr
            (port_mem_triangle G hG hr (hprev i)) (port_mem_triangle G hG hr (hadj i))
            (cycle_ports_ne G hG huv hCenters hcu hcv hdu hdv hm c hc hadj hr)
        · left
          simpa [L, threeSlotNext, hi] using hroot i hr
    · simpa [L, threeSlotNext, I, O] using (chosen_connector G hG (hadj i)).2.2.2.imp_right (fun h => h.1)
  have hclass (i : Fin (m + 1)) (r : Fin 3)
      (hd : L i r ≠ threeSlotNext L i r) :
      (L i r = I i ∧ IsTriangle G (c i) ∧ r = (if i ∈ T then 0 else 1)) ∨
      (L i r = s i ∧ i ∈ T ∧ r = 1) ∨
      (L i r = O i ∧ O i ≠ I (i + 1) ∧ r = 2) := by
    fin_cases r
    · by_cases hi : i ∈ T
      · exact Or.inl ⟨by simp [L], hTtri i hi, by simp [hi]⟩
      · exact False.elim (hd (by simp [L, threeSlotNext, hi]))
    · by_cases hi : i ∈ T
      · exact Or.inr (Or.inl ⟨by simp [L, hi], hi, rfl⟩)
      · refine Or.inl ⟨by simp [L, hi], ?_, by simp [hi]⟩
        apply (hturn i).mp
        simpa [L, threeSlotNext, hi] using hd
    · exact Or.inr (Or.inr ⟨by simp [L], by simpa [L, threeSlotNext] using hd, rfl⟩)
  have hdepart : ∀ i r j t, L i r ≠ threeSlotNext L i r →
      L j t ≠ threeSlotNext L j t → L i r = L j t → i = j ∧ r = t := by
    intro i r j t hi hj he
    rcases hclass i r hi with ⟨hir, hri, hr⟩ | ⟨hir, hTi, hr⟩ | ⟨hir, hOi, hr⟩ <;>
      rcases hclass j t hj with ⟨hjt, hrj, ht⟩ | ⟨hjt, hTj, ht⟩ | ⟨hjt, hOj, ht⟩
    · have hij : i = j := incoming_injective G hG huv hCenters hcu hcv hdu hdv hm c hc hadj
        (hir.symm.trans (he.trans hjt))
      exact ⟨hij, by simp only [hr, ht, hij]⟩
    · exact False.elim ((hfresh j hTj i).1 (hjt.symm.trans (he.symm.trans hir)))
    · exact False.elim (incoming_ne_outgoing G hG huv hCenters hcu hcv hdu hdv hm c hc hadj hri
        (by simpa only [O, hconn] using hOj) (hir.symm.trans (he.trans hjt)))
    · exact False.elim ((hfresh i hTi j).1 (hir.symm.trans (he.trans hjt)))
    · have hij : i = j := hinj hTi hTj (hir.symm.trans (he.trans hjt))
      exact ⟨hij, hr.trans ht.symm⟩
    · exact False.elim ((hfresh i hTi j).2 (hir.symm.trans (he.trans hjt)))
    · exact False.elim (incoming_ne_outgoing G hG huv hCenters hcu hcv hdu hdv hm c hc hadj hrj
        (by simpa only [O, hconn] using hOi) (hjt.symm.trans (he.symm.trans hir)))
    · exact False.elim ((hfresh j hTj i).2 (hjt.symm.trans (he.symm.trans hir)))
    · have hij : i = j := outgoing_injective G hG huv hCenters hcu hcv hdu hdv c hc hadj
        (by simpa only [O, hconn] using hOi)
        (hir.symm.trans (he.trans hjt))
      exact ⟨hij, hr.trans ht.symm⟩
  have hcount0 : (Finset.univ.filter (fun i => L i 0 ≠ L i 1)) = T := by
    ext i
    by_cases hi : i ∈ T
    · simp [L, I, hi, (hsp i hi).2.1.symm]
    · simp [L, hi]
  have hcount1 : (Finset.univ.filter (fun i => L i 1 ≠ L i 2)) =
      Finset.univ.filter (fun i => IsTriangle G (c i)) := by
    ext i
    by_cases hi : i ∈ T
    · simp [L, O, hi, (hsp i hi).2.2, hTtri i hi]
    · simp [L, hi, hturn i]
  have hcount2 : (Finset.univ.filter (fun i => L i 2 ≠ L (i + 1) 0)) =
      Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
        chosenPort G u v (c (i + 1)) (c i)) := by
    ext i
    simp [L, I, O]
  have htotal : (Finset.univ.filter (fun i => L i 0 ≠ L i 1)).card +
      (Finset.univ.filter (fun i => L i 1 ≠ L i 2)).card +
      (Finset.univ.filter (fun i => L i 2 ≠ L (i + 1) 0)).card =
        T.card + (Finset.univ.filter (fun i => IsTriangle G (c i))).card +
          (Finset.univ.filter (fun i => chosenPort G u v (c i) (c (i + 1)) ≠
            chosenPort G u v (c (i + 1)) (c i))).card := by
    rw [hcount0, hcount1, hcount2]
  obtain ⟨p, hp, hlength⟩ := exists_cycle_of_three_slots G m L hstep hdepart
    (by rw [htotal]; exact hlen)
  exact ⟨L 0 0, p, hp, hlength.trans htotal⟩

end Erdos64.TwoCubicClawCentersQuotient
