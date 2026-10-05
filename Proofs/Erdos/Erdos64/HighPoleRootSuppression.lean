import Erdos.Erdos64.HighPoleRootGeometry
import Erdos.Erdos64.RetainedDegreeSuppression
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace Erdos64.HighPoleRootSuppression

open SimpleGraph Erdos64.UniqueCubicClawCenter
open Erdos64.HighPoleRootGeometry Erdos64.GeneralRootIncidence

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem nonsimp (hG : IsCounterexample G) {v : V}
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b) :
    ∀ x : {x : V // x ≠ v}, ∃ a b, (completion G v).Adj x a ∧
      (completion G v).Adj x b ∧ a ≠ b ∧ ¬ (completion G v).Adj a b := by
  intro x
  obtain ⟨a, b, ha, hb, hab, hn⟩ :=
    HighPoleCompletion.completion_nonsimplicial G hG hN x
  exact ⟨a, b, ha, hb, hab, hn⟩

private theorem nonsimp' (hG : IsCounterexample G) {v : V}
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b) :
    ∀ x : {x : V // x ≠ v}, ∃ a b, a ≠ b ∧ (completion G v).Adj x a ∧
      (completion G v).Adj x b ∧ ¬ (completion G v).Adj a b := by
  intro x
  obtain ⟨a, b, ha, hb, hab, hn⟩ := nonsimp G hG hN x
  exact ⟨a, b, hab, ha, hb, hn⟩

/-- The actual clique root of the completion has minimum degree two. -/
theorem root_min_degree2 (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A : RootNode (completion G v)) : 2 ≤ (cliqueRoot (completion G v)).degree A := by
  letI := completion_nonempty G hc
  exact root_min_degree _ (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) (nonsimp' G hG hN) A

/-- The actual clique root of the completion has no triangle. -/
theorem root_triangle_free (hG : IsCounterexample G) {v : V}
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    (A B C : RootNode (completion G v))
    (hAB : (cliqueRoot (completion G v)).Adj A B)
    (hBC : (cliqueRoot (completion G v)).Adj B C)
    (hCA : (cliqueRoot (completion G v)).Adj C A) : False :=
  ClawDiamondRoot.cliqueRoot_triangle_free _
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) (nonsimp G hG hN) hAB hBC hCA

private theorem two_labels (hG : IsCounterexample G) {v : V}
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A : RootNode (completion G v)) (hA : (cliqueRoot (completion G v)).degree A = 2)
    (p : {x : V // x ≠ v}) (hp : p ∈ A.val) :
    ∃ a, ∀ w ∈ A.val, w = p ∨ w = a := by
  classical
  have hc : A.val.toFinset.card = 2 := by
    rw [Set.toFinset_card, ← degree_eq_card _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonsimp' G hG hN)]
    exact hA
  have he : (A.val.toFinset.erase p).card = 1 := by
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hp), hc]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp he
  refine ⟨a, ?_⟩
  intro w hw
  by_cases hwp : w = p
  · exact Or.inl hwp
  · have hm := Finset.mem_erase.mpr ⟨hwp, Set.mem_toFinset.mpr hw⟩
    rw [ha] at hm
    exact Or.inr (Finset.mem_singleton.mp hm)

/-- Two degree-two vertices in the actual clique root cannot be adjacent. -/
theorem root_degreeTwo_independent (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A B : RootNode (completion G v)) (hAB : (cliqueRoot (completion G v)).Adj A B)
    (hA : (cliqueRoot (completion G v)).degree A = 2)
    (hB : (cliqueRoot (completion G v)).degree B = 2) : False := by
  classical
  let P := poleRoot G hG hc
  have hP : 3 ≤ (cliqueRoot (completion G v)).degree P := by
    rw [poleRoot_degree G hG hc hu hN]
    exact hG.degree_ge_three v
  have hAP : A ≠ P := by intro he; rw [he] at hA; omega
  have hBP : B ≠ P := by intro he; rw [he] at hB; omega
  obtain ⟨p, hpA, hpB⟩ := hAB.2
  have hnp : ¬ G.Adj v p.val := by
    intro hp
    rcases ClawDiamondRoot.root_incidence_exhausted _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonsimp G hG hN) hAB.1 hpA hpB
      (show p ∈ P.val from hp) with he | he
    · exact hAP he.symm
    · exact hBP he.symm
  obtain ⟨a, ha⟩ := two_labels G hG hu hN A hA p hpA
  obtain ⟨b, hb⟩ := two_labels G hG hu hN B hB p hpB
  have hsub : G.neighborFinset p.val ⊆ {a.val, b.val} := by
    intro w hw
    have epw := (G.mem_neighborFinset p.val w).mp hw
    have hwv : w ≠ v := by intro he; subst w; exact hnp epw.symm
    let w' : {x : V // x ≠ v} := ⟨w, hwv⟩
    have eqpw : (completion G v).Adj p w' := Or.inl epw
    let E : RootNode (completion G v) :=
      ⟨edgeClique (completion G v) p w',
        ClawDiamondRoot.edgeClique_maximal _
          (HighPoleCompletion.completion_inducedDiamondFree G hG) eqpw⟩
    have hpE : p ∈ E.val := Or.inl rfl
    have hwE : w' ∈ E.val := Or.inr (Or.inl rfl)
    have hf := ClawDiamondRoot.root_incidence_exhausted _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonsimp G hG hN) hAB.1 hpA hpB hpE
    have hwab : w' = a ∨ w' = b := by
      rcases hf with he | he
      · rcases ha w' (he ▸ hwE) with hp | hwa
        · exact False.elim (eqpw.ne hp.symm)
        · exact Or.inl hwa
      · rcases hb w' (he ▸ hwE) with hp | hwb
        · exact False.elim (eqpw.ne hp.symm)
        · exact Or.inr hwb
    rcases hwab with he | he
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val he))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg Subtype.val he)))
  have hlo := hG.degree_ge_three p.val
  have hhi := Finset.card_le_card hsub
  have hc2 : ({a.val, b.val} : Finset V).card ≤ 2 := by
    by_cases he : a.val = b.val
    · simp [he]
    · simp [he]
  change G.degree p.val ≤ _ at hhi
  omega

private theorem labels_ne (hG : IsCounterexample G) {v : V}
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    {A B C D : RootNode (completion G v)}
    (e : (cliqueRoot (completion G v)).Adj A B)
    (f : (cliqueRoot (completion G v)).Adj C D)
    (hn : (C ≠ A ∧ C ≠ B) ∨ (D ≠ A ∧ D ≠ B)) :
    intersectionLabel _ e ≠ intersectionLabel _ f := by
  intro he
  have hxA := label_mem_left _ e
  have hxB := label_mem_right _ e
  rw [he] at hxA hxB
  rcases hn with ⟨hCA, hCB⟩ | ⟨hDA, hDB⟩
  · exact ClawDiamondRoot.no_three_root_nodes _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonsimp G hG hN)
      e.1 hCA.symm hCB.symm hxA hxB (label_mem_left _ f)
  · exact ClawDiamondRoot.no_three_root_nodes _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonsimp G hG hN)
      e.1 hDA.symm hDB.symm hxA hxB (label_mem_right _ f)

/-- Distinct endpoints in the actual root have at most one degree-two middle vertex. -/
theorem root_degreeTwo_middle_unique (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A B C D : RootNode (completion G v)) (hAB : A ≠ B)
    (hC : (cliqueRoot (completion G v)).degree C = 2)
    (hD : (cliqueRoot (completion G v)).degree D = 2)
    (eAC : (cliqueRoot (completion G v)).Adj A C)
    (eCB : (cliqueRoot (completion G v)).Adj C B)
    (eAD : (cliqueRoot (completion G v)).Adj A D)
    (eDB : (cliqueRoot (completion G v)).Adj D B) : C = D := by
  classical
  by_contra hCD
  let P := poleRoot G hG hc
  have hP : 3 ≤ (cliqueRoot (completion G v)).degree P := by
    rw [poleRoot_degree G hG hc hu hN]
    exact hG.degree_ge_three v
  have hCP : C ≠ P := by intro he; rw [he] at hC; omega
  have hDP : D ≠ P := by intro he; rw [he] at hD; omega
  have hAP : A ≠ P := by
    intro he
    have hd := pole_arm_degree_three G hG hc hu hN C (by simpa only [he] using eAC)
    omega
  have hBP : B ≠ P := by
    intro he
    have hd := pole_arm_degree_three G hG hc hu hN C (by simpa only [he] using eCB.symm)
    omega
  let x := intersectionLabel _ eAC
  let y := intersectionLabel _ eCB
  let z := intersectionLabel _ eDB.symm
  let t := intersectionLabel _ eAD.symm
  have hxy : x ≠ y := labels_ne G hG hu hN eAC eCB (Or.inr ⟨hAB.symm, eCB.1.symm⟩)
  have hxz : x ≠ z := labels_ne G hG hu hN eAC eDB.symm (Or.inl ⟨hAB.symm, eCB.1.symm⟩)
  have hxt : x ≠ t := labels_ne G hG hu hN eAC eAD.symm (Or.inl ⟨eAD.1.symm, Ne.symm hCD⟩)
  have hyz : y ≠ z := labels_ne G hG hu hN eCB eDB.symm (Or.inr ⟨Ne.symm hCD, eDB.1⟩)
  have hyt : y ≠ t := labels_ne G hG hu hN eCB eAD.symm (Or.inr ⟨eAC.1, hAB⟩)
  have hzt : z ≠ t := labels_ne G hG hu hN eDB.symm eAD.symm (Or.inr ⟨hAB, eAD.1⟩)
  have ne_val : ∀ {s t : {x : V // x ≠ v}}, s ≠ t → s.val ≠ t.val := by
    intro s t hn he
    exact hn (Subtype.ext he)
  exact not_four_cycle G hG (ne_val hxy) (ne_val hxz) (ne_val hxt)
    (ne_val hyz) (ne_val hyt) (ne_val hzt)
    (nonpole_adj_original G hG hc C hCP (label_mem_right _ eAC) (label_mem_left _ eCB) hxy)
    (nonpole_adj_original G hG hc B hBP (label_mem_right _ eCB) (label_mem_left _ eDB.symm) hyz)
    (nonpole_adj_original G hG hc D hDP (label_mem_right _ eDB.symm) (label_mem_left _ eAD.symm) hzt)
    (nonpole_adj_original G hG hc A hAP (label_mem_right _ eAD.symm) (label_mem_left _ eAC) hxt.symm)

/-- The canonical pole is an actual retained vertex of degree at least three. -/
noncomputable def retainedPole (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)) :=
  ⟨poleRoot G hG hc, by
    rw [poleRoot_degree G hG hc hu hN]
    exact hG.degree_ge_three v⟩

/-- The retained pole has exactly the canonical neighborhood root as its value. -/
theorem retainedPole_val (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    (retainedPole G hG hc hu hN).val = poleRoot G hG hc := rfl

/-- Standard suppression of the actual completion root is nonempty. -/
theorem suppression_nonempty (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    Nonempty (RetainedDegreeSuppression.Retained (cliqueRoot (completion G v))) :=
  ⟨retainedPole G hG hc hu hN⟩

/-- Actual standard suppression preserves every retained root degree; the four
structural gates are proved from the original graph, not supplied as hypotheses. -/
theorem suppression_degree_eq (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    [DecidableRel (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).Adj]
    (x : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v))) :
    (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).degree x =
      (cliqueRoot (completion G v)).degree x.val :=
  RetainedDegreeSuppression.degree_eq _ (root_min_degree2 G hG hc hu hN)
    (root_degreeTwo_independent G hG hc hu hN) (root_triangle_free G hG hu hN)
    (root_degreeTwo_middle_unique G hG hc hu hN) x

/-- The pole degree in the suppressed graph is the original center degree. -/
theorem suppression_pole_degree (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    [DecidableRel (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).Adj] :
    (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).degree
      (retainedPole G hG hc hu hN) = G.degree v := by
  rw [suppression_degree_eq G hG hc hu hN, retainedPole_val]
  exact poleRoot_degree G hG hc hu hN

/-- Every ordinary retained root has degree three after standard suppression. -/
theorem suppression_nonpole_degree (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    [DecidableRel (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).Adj]
    (x : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
    (hx : x.val ≠ poleRoot G hG hc) :
    (RetainedDegreeSuppression.suppression (cliqueRoot (completion G v))).degree x = 3 := by
  rw [suppression_degree_eq G hG hc hu hN]
  rcases nonpole_degree_two_or_three G hG hc hu hN x.val hx with htwo | hthree
  · have hge := x.property
    omega
  · exact hthree

/-- The actual clique root has fewer nodes than there are surviving original labels. -/
theorem root_card_lt_survivor (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    Fintype.card (RootNode (completion G v)) < Fintype.card {x : V // x ≠ v} := by
  classical
  have hP : 2 < (cliqueRoot (completion G v)).degree (poleRoot G hG hc) := by
    rw [poleRoot_degree G hG hc hu hN]
    have hlo := hG.degree_ge_three v
    omega
  have hsum : (∑ _A : RootNode (completion G v), 2) <
      ∑ A : RootNode (completion G v), (cliqueRoot (completion G v)).degree A :=
    Finset.sum_lt_sum (fun A _ => root_min_degree2 G hG hc hu hN A)
      ⟨poleRoot G hG hc, Finset.mem_univ _, hP⟩
  have hcount := sum_degrees_eq_twice_card (completion G v)
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) (nonsimp' G hG hN)
  rw [hcount] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

/-- Standard suppression of the actual root has strictly fewer vertices than the
original counterexample, without an order or minimality assumption. -/
theorem suppression_card_lt_original (hG : IsCounterexample G) {v : V} (hc : Claw G v)
    (hu : ∀ w, Claw G w → w = v)
    (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    Fintype.card (RetainedDegreeSuppression.Retained (cliqueRoot (completion G v))) <
      Fintype.card V := by
  have hret := RetainedDegreeSuppression.card_le (cliqueRoot (completion G v))
  have hroot := root_card_lt_survivor G hG hc hu hN
  have hsurv := Fintype.card_subtype_le (fun x : V => x ≠ v)
  omega

end Erdos64.HighPoleRootSuppression
