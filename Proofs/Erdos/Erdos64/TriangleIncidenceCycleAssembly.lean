import Erdos.Erdos64.TriangleIncidenceCycleLift
import Erdos.Erdos64.TriangleIncidenceThreeSlots

set_option autoImplicit false

namespace Erdos64.TriangleIncidence

open SimpleGraph

noncomputable local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u w

variable {V : Type u} {W : Type w} {G : SimpleGraph V} {K : SimpleGraph W}
  {v : V} {root : W}

/-- A simple incidence cycle lifts to a cycle of twice its length when distinct,
fresh triangle spares compensate for zero connectors and the root turn. -/
theorem Model.exists_doubled_cycle_of_spares (D : Model G K v root) {m : ℕ}
    (hm : 3 ≤ m + 1) (c : Fin (m + 1) → W) (hc : Function.Injective c)
    (hadj : ∀ i, K.Adj (c i) (c (i + 1))) (T : Finset (Fin (m + 1)))
    (s : Fin (m + 1) → V)
    (hTroot : ∀ i ∈ T, c i ≠ root)
    (hsp : ∀ i ∈ T, s i ∈ D.triangle (c i) ∧
      s i ≠ D.port (c i) (c (i - 1)) ∧ s i ≠ D.port (c i) (c (i + 1)))
    (hfresh : ∀ i ∈ T, ∀ j, s i ≠ D.port (c j) (c (j - 1)) ∧
      s i ≠ D.port (c j) (c (j + 1)))
    (hinj : Set.InjOn s (↑T : Set (Fin (m + 1))))
    (hcard : T.card =
      (Finset.univ.filter (fun i => D.port (c i) (c (i + 1)) =
        D.port (c (i + 1)) (c i))).card +
      (Finset.univ.filter (fun i => c i = root)).card) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 2 * (m + 1) := by
  classical
  let I : Fin (m + 1) → V := fun i => D.port (c i) (c (i - 1))
  let O : Fin (m + 1) → V := fun i => D.port (c i) (c (i + 1))
  let L : Fin (m + 1) → Fin 3 → V := fun i r =>
    if r = 0 then I i else if r = 1 then (if i ∈ T then s i else I i) else O i
  have hprev (i : Fin (m + 1)) : K.Adj (c i) (c (i - 1)) := by
    simpa only [sub_add_cancel] using (hadj (i - 1)).symm
  have hroot (i : Fin (m + 1)) (hi : c i = root) : I i = O i := by
    dsimp only [I, O]
    rw [hi, D.root_port _ (hi ▸ hprev i), D.root_port _ (hi ▸ hadj i)]
  have hturn (i : Fin (m + 1)) : I i ≠ O i ↔ c i ≠ root := by
    constructor
    · intro h he
      exact h (hroot i he)
    · exact D.cycle_ports_ne hm c hc hadj
  have hconn (i : Fin (m + 1)) : I (i + 1) = D.port (c (i + 1)) (c i) := by
    simp only [I, add_sub_cancel_right]
  have hstep : ∀ i r, L i r = threeSlotNext L i r ∨
      G.Adj (L i r) (threeSlotNext L i r) := by
    intro i r
    fin_cases r
    · by_cases hi : i ∈ T
      · right
        simpa [L, threeSlotNext, hi] using D.triangle_adj (hTroot i hi)
          (D.port_mem _ _ (hTroot i hi) (hprev i)) (hsp i hi).1 (hsp i hi).2.1.symm
      · left
        simp [L, threeSlotNext, hi]
    · by_cases hi : i ∈ T
      · right
        simpa [L, threeSlotNext, hi] using D.triangle_adj (hTroot i hi)
          (hsp i hi).1 (D.port_mem _ _ (hTroot i hi) (hadj i)) (hsp i hi).2.2
      · by_cases hr : c i = root
        · left
          simpa [L, threeSlotNext, hi] using hroot i hr
        · right
          simpa [L, threeSlotNext, hi] using D.triangle_adj hr
            (D.port_mem _ _ hr (hprev i)) (D.port_mem _ _ hr (hadj i))
            (D.cycle_ports_ne hm c hc hadj hr)
    · simpa [L, threeSlotNext, I, O] using D.connector _ _ (hadj i)
  have hclass (i : Fin (m + 1)) (r : Fin 3)
      (hd : L i r ≠ threeSlotNext L i r) :
      (L i r = I i ∧ c i ≠ root ∧ r = (if i ∈ T then 0 else 1)) ∨
      (L i r = s i ∧ i ∈ T ∧ r = 1) ∨
      (L i r = O i ∧ O i ≠ I (i + 1) ∧ r = 2) := by
    fin_cases r
    · by_cases hi : i ∈ T
      · exact Or.inl ⟨by simp [L], hTroot i hi, by simp [hi]⟩
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
    · have hij : i = j := D.incoming_injective hm c hc hadj hri hrj
        (hir.symm.trans (he.trans hjt))
      exact ⟨hij, by simp only [hr, ht, hij]⟩
    · exact False.elim ((hfresh j hTj i).1 (hjt.symm.trans (he.symm.trans hir)))
    · exact False.elim (D.incoming_ne_outgoing hm c hc hadj hri
        (by simpa only [O, hconn] using hOj) (hir.symm.trans (he.trans hjt)))
    · exact False.elim ((hfresh i hTi j).1 (hir.symm.trans (he.trans hjt)))
    · have hij : i = j := hinj hTi hTj (hir.symm.trans (he.trans hjt))
      exact ⟨hij, hr.trans ht.symm⟩
    · exact False.elim ((hfresh i hTi j).2 (hir.symm.trans (he.trans hjt)))
    · exact False.elim (D.incoming_ne_outgoing hm c hc hadj hrj
        (by simpa only [O, hconn] using hOi) (hjt.symm.trans (he.symm.trans hir)))
    · exact False.elim ((hfresh j hTj i).2 (hjt.symm.trans (he.symm.trans hir)))
    · have hij : i = j := D.outgoing_injective c hc hadj
        (by simpa only [O, hconn] using hOi) (by simpa only [O, hconn] using hOj)
        (hir.symm.trans (he.trans hjt))
      exact ⟨hij, hr.trans ht.symm⟩
  have hcount0 : (Finset.univ.filter (fun i => L i 0 ≠ L i 1)) = T := by
    ext i
    by_cases hi : i ∈ T
    · simp [L, I, hi, (hsp i hi).2.1.symm]
    · simp [L, hi]
  have hcount1 : (Finset.univ.filter (fun i => L i 1 ≠ L i 2)) =
      Finset.univ.filter (fun i => c i ≠ root) := by
    ext i
    by_cases hi : i ∈ T
    · simp [L, O, hi, (hsp i hi).2.2, hTroot i hi]
    · simp [L, hi, hturn i]
  have hcount2 : (Finset.univ.filter (fun i => L i 2 ≠ L (i + 1) 0)) =
      Finset.univ.filter (fun i => D.port (c i) (c (i + 1)) ≠
        D.port (c (i + 1)) (c i)) := by
    ext i
    simp [L, I, O]
  have htotal : (Finset.univ.filter (fun i => L i 0 ≠ L i 1)).card +
      (Finset.univ.filter (fun i => L i 1 ≠ L i 2)).card +
      (Finset.univ.filter (fun i => L i 2 ≠ L (i + 1) 0)).card = 2 * (m + 1) := by
    rw [hcount0, hcount1, hcount2, hcard]
    have hroots := (Finset.univ : Finset (Fin (m + 1))).card_filter_add_card_filter_not
      (fun i => c i = root)
    have hzeros := (Finset.univ : Finset (Fin (m + 1))).card_filter_add_card_filter_not
      (fun i => D.port (c i) (c (i + 1)) = D.port (c (i + 1)) (c i))
    simp only [Finset.card_univ, Fintype.card_fin, ne_eq] at hroots hzeros ⊢
    omega
  obtain ⟨p, hp, hlen⟩ := exists_cycle_of_three_slots G m L hstep hdepart
    (by rw [htotal]; omega)
  exact ⟨L 0 0, p, hp, hlen.trans htotal⟩

end Erdos64.TriangleIncidence
