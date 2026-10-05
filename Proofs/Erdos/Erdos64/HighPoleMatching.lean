import Erdos.Erdos64.HighPoleRootGeometry
import Erdos.Erdos64.RetainedDegreeSuppression

set_option autoImplicit false

namespace Erdos64.HighPoleMatching

open SimpleGraph Erdos64.UniqueCubicClawCenter
open Erdos64.HighPoleRootGeometry

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Direct ordinary edges on the actual retained root carrier, excluding the canonical pole.
No degree-two intermediate or suppressed edge is selected. -/
def M (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    SimpleGraph (RetainedDegreeSuppression.Retained (cliqueRoot (completion G v))) where
  Adj A B := A.val ≠ poleRoot G hG hclaw ∧ B.val ≠ poleRoot G hG hclaw ∧
    (cliqueRoot (completion G v)).Adj A.val B.val
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.ne rfl⟩

/-- The selected graph uses exactly direct ordinary root edges. -/
theorem M_adj_iff (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A B : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v))) :
    (M G hG hclaw).Adj A B ↔ A.val ≠ poleRoot G hG hclaw ∧
      B.val ≠ poleRoot G hG hclaw ∧ (cliqueRoot (completion G v)).Adj A.val B.val := Iff.rfl

private theorem nonSim (hG : IsCounterexample G) {v : V}
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b) :
    ∀ x : {x : V // x ≠ v}, ∃ a b, a ≠ b ∧ (completion G v).Adj x a ∧
      (completion G v).Adj x b ∧ ¬ (completion G v).Adj a b := by
  intro x
  obtain ⟨a, b, ha, hb, hab, hn⟩ :=
    HighPoleCompletion.completion_nonsimplicial G hG hNind x
  exact ⟨a, b, hab, ha, hb, hn⟩

/-- Ordinary retained root nodes have degree exactly three in the canonical root. -/
theorem ordinary_degree_three (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
    (hA : A.val ≠ poleRoot G hG hclaw) :
    (cliqueRoot (completion G v)).degree A.val = 3 := by
  have hlo := A.property
  rcases nonpole_degree_two_or_three G hG hclaw hunique hNind A.val hA with htwo | hthree
  · omega
  · exact hthree

/-- Two distinct ordinary retained cliques sharing a label supply four distinct
original neighbors of that label. -/
theorem shared_label_degree_ge_four (hG : IsCounterexample G) {v : V}
    (hclaw : Claw G v) (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A B : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
    (hA : A.val ≠ poleRoot G hG hclaw) (hB : B.val ≠ poleRoot G hG hclaw)
    (hne : A.val ≠ B.val) (p : {x : V // x ≠ v})
    (hpA : p ∈ A.val.val) (hpB : p ∈ B.val.val) : 4 ≤ G.degree p.val := by
  classical
  have hD := HighPoleCompletion.completion_inducedDiamondFree G hG (v := v)
  have card_three (C : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
      (hC : C.val ≠ poleRoot G hG hclaw) : C.val.val.toFinset.card = 3 := by
    rw [Set.toFinset_card, ← GeneralRootIncidence.degree_eq_card _ hD
      (completion_claw_free G hunique) (nonSim G hG hNind)]
    exact ordinary_degree_three G hG hclaw hunique hNind C hC
  let s := A.val.val.toFinset.erase p
  let t := B.val.val.toFinset.erase p
  have hs : s.card = 2 := by
    have he := Finset.card_erase_add_one (Set.mem_toFinset.mpr hpA)
    have hc := card_three A hA
    dsimp [s]
    omega
  have ht : t.card = 2 := by
    have he := Finset.card_erase_add_one (Set.mem_toFinset.mpr hpB)
    have hc := card_three B hB
    dsimp [t]
    omega
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' : x ≠ p ∧ x ∈ A.val.val := by simpa [s] using hx
    have hy' : x ≠ p ∧ x ∈ B.val.val := by simpa [t] using hy
    exact hx'.1 (ClawDiamondRoot.root_intersection_unique _ hD hne
      hx'.2 hy'.2 hpA hpB)
  have hc : (s ∪ t).card = 4 := by rw [Finset.card_union_of_disjoint hdis, hs, ht]
  have hsub : (s ∪ t).image Subtype.val ⊆ G.neighborFinset p.val := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply (G.mem_neighborFinset _ _).mpr
    rcases Finset.mem_union.mp hy with hy | hy
    · have hy' : y ≠ p ∧ y ∈ A.val.val := by simpa [s] using hy
      exact nonpole_adj_original G hG hclaw A.val hA hpA hy'.2 hy'.1.symm
    · have hy' : y ≠ p ∧ y ∈ B.val.val := by simpa [t] using hy
      exact nonpole_adj_original G hG hclaw B.val hB hpB hy'.2 hy'.1.symm
  have himage : ((s ∪ t).image Subtype.val).card = 4 :=
    (Finset.card_image_of_injective _ Subtype.val_injective).trans hc
  have hbound := Finset.card_le_card hsub
  rw [himage] at hbound
  exact hbound

/-- Independence of the original high-degree vertices forces the direct ordinary
retained-edge graph to be a matching: every vertex has at most one neighbor. -/
theorem M_matching (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    (hHIGH : ∀ a b, 4 ≤ G.degree a → 4 ≤ G.degree b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A B C : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
    (hAB : (M G hG hclaw).Adj A B) (hAC : (M G hG hclaw).Adj A C) : B = C := by
  classical
  by_contra hBC
  have hBC' : B.val ≠ C.val := fun he => hBC (Subtype.ext he)
  obtain ⟨p, hpA, hpB⟩ := hAB.2.2.2
  obtain ⟨q, hqA, hqC⟩ := hAC.2.2.2
  have hpq : p ≠ q := by
    intro he
    have hpC : p ∈ C.val.val := he ▸ hqC
    exact ClawDiamondRoot.no_three_root_nodes _
      (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hunique)
      (HighPoleCompletion.completion_nonsimplicial G hG hNind)
      hAB.2.2.1 hAC.2.2.1 hBC' hpA hpB hpC
  have hp4 : 4 ≤ G.degree p.val := shared_label_degree_ge_four G hG hclaw
    hunique hNind A B hAB.1 hAB.2.1 hAB.2.2.1 p hpA hpB
  have hq4 : 4 ≤ G.degree q.val := shared_label_degree_ge_four G hG hclaw
    hunique hNind A C hAC.1 hAC.2.1 hAC.2.2.1 q hqA hqC
  exact hHIGH p.val q.val hp4 hq4
    (nonpole_adj_original G hG hclaw A.val hAB.1 hpA hqA hpq)

/-- The selected graph avoids every retained wrapper of the actual canonical pole. -/
theorem M_avoids_pole (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (P A : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
    (hP : P.val = poleRoot G hG hclaw) : ¬ (M G hG hclaw).Adj P A := by
  intro h
  exact h.1 hP

/-- Every selected edge lies in standard suppression through its direct-edge branch. -/
theorem M_le_suppression (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    M G hG hclaw ≤ RetainedDegreeSuppression.suppression (cliqueRoot (completion G v)) := by
  intro A B h
  exact ⟨fun he => h.2.2.ne (congrArg Subtype.val he), Or.inl h.2.2⟩

/-- The canonical pole really is retained, using its original degree and minimum degree three. -/
theorem pole_retained (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    3 ≤ (cliqueRoot (completion G v)).degree (poleRoot G hG hclaw) := by
  rw [poleRoot_degree G hG hclaw hunique hNind]
  exact hG.degree_ge_three v

/-- The actual retained pole witnesses that the selected graph's carrier is nonempty. -/
theorem retained_nonempty (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj] :
    Nonempty (RetainedDegreeSuppression.Retained (cliqueRoot (completion G v))) :=
  ⟨⟨poleRoot G hG hclaw, pole_retained G hG hclaw hunique hNind⟩⟩

/-- Both endpoints of a selected edge are automatically ordinary degree-three root nodes. -/
theorem M_endpoints_degree_three (hG : IsCounterexample G) {v : V} (hclaw : Claw G v)
    (hunique : ∀ w, Claw G w → w = v)
    (hNind : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)
    [DecidableRel (cliqueRoot (completion G v)).Adj]
    (A B : RetainedDegreeSuppression.Retained (cliqueRoot (completion G v)))
    (hAB : (M G hG hclaw).Adj A B) :
    (cliqueRoot (completion G v)).degree A.val = 3 ∧
      (cliqueRoot (completion G v)).degree B.val = 3 :=
  ⟨ordinary_degree_three G hG hclaw hunique hNind A hAB.1,
    ordinary_degree_three G hG hclaw hunique hNind B hAB.2.1⟩

end Erdos64.HighPoleMatching
