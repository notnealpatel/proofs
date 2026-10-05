import Erdos.Erdos64.HighPoleMatching
import Erdos.Erdos64.HighPoleRootSuppression
import Erdos.Erdos64.RetainedSuppressionIncidence
import Erdos.Erdos64.PartialFisherCore

set_option autoImplicit false

noncomputable section
namespace Erdos64.HighPoleFisherRepresentation

open SimpleGraph Erdos64.UniqueCubicClawCenter
open Erdos64.HighPoleRootGeometry Erdos64.GeneralRootIncidence
open Erdos64.HighPoleRootSuppression

attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (hG : IsCounterexample G) {v : V} (hc : Claw G v)
variable (hu : ∀ w, Claw G w → w = v)
variable (hN : ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b)

private abbrev Q := completion G v
private abbrev H := cliqueRoot (Q G (v := v))
private abbrev K := RetainedDegreeSuppression.suppression (H G (v := v))
private abbrev z := retainedPole G hG hc hu hN

include hG hN in
private theorem nonSim : ∀ x : {x : V // x ≠ v}, ∃ a b,
    a ≠ b ∧ (Q G).Adj x a ∧ (Q G).Adj x b ∧ ¬ (Q G).Adj a b := by
  intro x
  obtain ⟨a,b,ha,hb,hab,hn⟩ :=
    HighPoleCompletion.completion_nonsimplicial G hG hN x
  exact ⟨a,b,hab,ha,hb,hn⟩

private def inc (A : RetainedDegreeSuppression.Retained (H G (v := v))) :=
  RetainedSuppressionIncidence.incidenceEquiv (H G)
    (root_min_degree2 G hG hc hu hN)
    (root_degreeTwo_independent G hG hc hu hN)
    (root_triangle_free G hG hu hN)
    (root_degreeTwo_middle_unique G hG hc hu hN) A

private def lab (A : RootNode (Q G (v := v))) :=
  rootNeighborEquiv (Q G)
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) (nonSim G hG hN) A

/-- An ordinary suppressed incidence is labeled by its actual first root edge,
then by the unique original vertex shared by the two root cliques. -/
def ordinaryLabel (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN)) :
    {x : V // x ≠ v} :=
  (lab G hG hu hN p.val.1.val (inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩)).val

/-- The ordinary label belongs to its first retained root clique, as required
by the standard clique-root intersection labeling. -/
theorem ordinaryLabel_mem_first
    (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN)) :
    ordinaryLabel G hG hc hu hN p ∈ p.val.1.val.val :=
  (lab G hG hu hN p.val.1.val (inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩)).property

/-- The ordinary label also belongs to the actual first-step root, which may
be a degree-two root omitted from the retained carrier. -/
theorem ordinaryLabel_mem_firstStep
    (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN)) :
    ordinaryLabel G hG hc hu hN p ∈
      (inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩).val.val :=
  label_mem_right (Q G) (inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩).property

/-- The literal pole is labeled by the original claw center; ordinary ports use
concrete first-edge incidences, not an arbitrary neighbor equivalence. -/
def portLabel (p : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN)) : V :=
  match p with
  | none => v
  | some p => (ordinaryLabel G hG hc hu hN p).val

/-- The distinguished empty port represents exactly the original center. -/
theorem portLabel_none : portLabel G hG hc hu hN none = v := rfl

/-- Ordinary ports represent survivor vertices, never the removed center. -/
theorem portLabel_some_ne (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN)) :
    portLabel G hG hc hu hN (some p) ≠ v :=
  (ordinaryLabel G hG hc hu hN p).property

private theorem inc_direct (A B : RetainedDegreeSuppression.Retained (H G (v := v)))
    (hAB : (K G).Adj A B) (hd : (H G).Adj A.val B.val) :
    (inc G hG hc hu hN A ⟨B,hAB⟩).val = B.val := by
  exact RetainedSuppressionIncidence.firstStep_eq_of_spec (H G)
    (root_triangle_free G hG hu hN)
    (root_degreeTwo_middle_unique G hG hc hu hN) A B hAB ⟨hd, Or.inl rfl⟩

private theorem ordinaryLabel_direct
    (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN))
    (hd : (H G).Adj p.val.1.val p.val.2.val) :
    ordinaryLabel G hG hc hu hN p = intersectionLabel (Q G) hd := by
  let w := inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩
  have hw : w.val = p.val.2.val := inc_direct G hG hc hu hN _ _ _ hd
  change intersectionLabel (Q G) w.property = intersectionLabel (Q G) hd
  apply label_unique (Q G) (HighPoleCompletion.completion_inducedDiamondFree G hG)
  · exact label_mem_left (Q G) hd
  · rw [hw]
    exact label_mem_right (Q G) hd

/-- Reversing a direct ordinary root edge preserves the actual original label.
This needs no matching hypothesis. -/
theorem portLabel_eq_of_rel
    (a b : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN))
    (hab : PartialFisherCore.PortRel (K G) (z G hG hc hu hN)
      (HighPoleMatching.M G hG hc) a b) :
    portLabel G hG hc hu hN a = portLabel G hG hc hu hN b := by
  rcases hab with he | hr
  · exact congrArg (portLabel G hG hc hu hN) he
  cases a with
  | none => cases b <;> exact False.elim hr
  | some p =>
    cases b with
    | none => exact False.elim hr
    | some r =>
      have hd := hr.2.2.2.2
      have hd' : (H G).Adj r.val.1.val r.val.2.val := by
        rw [← hr.2.1, ← hr.1]
        exact hd.symm
      change (ordinaryLabel G hG hc hu hN p).val =
        (ordinaryLabel G hG hc hu hN r).val
      rw [ordinaryLabel_direct G hG hc hu hN p hd,
        ordinaryLabel_direct G hG hc hu hN r hd']
      apply congrArg Subtype.val
      apply label_unique (Q G) (HighPoleCompletion.completion_inducedDiamondFree G hG)
      · simpa only [← hr.1] using label_mem_right (Q G) hd'
      · simpa only [← hr.2.1] using label_mem_left (Q G) hd'

/-- The canonical port labeling descends through exactly the actual direct-edge
contractions to vertices of the literal original graph. -/
def quotientLabel : PartialFisherCore.QuotientVertex (K G (v := v))
    (z G hG hc hu hN) (HighPoleMatching.M G hG hc) → V :=
  Quotient.lift (portLabel G hG hc hu hN) (portLabel_eq_of_rel G hG hc hu hN)

/-- Descending to the quotient does not change any concrete port label. -/
theorem quotientLabel_q (p : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN)) :
    quotientLabel G hG hc hu hN
      (PartialFisherCore.q (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) p) =
      portLabel G hG hc hu hN p := rfl

include hG hu hN in
private theorem label_collision {A B C D : RootNode (Q G (v := v))}
    (eAB : (H G).Adj A B) (eCD : (H G).Adj C D)
    (he : intersectionLabel (Q G) eAB = intersectionLabel (Q G) eCD) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  have hxC : intersectionLabel (Q G) eAB ∈ C.val := by
    rw [he]
    exact label_mem_left (Q G) eCD
  have hxD : intersectionLabel (Q G) eAB ∈ D.val := by
    rw [he]
    exact label_mem_right (Q G) eCD
  have hn : ∀ x : {x : V // x ≠ v}, ∃ a b,
      (Q G).Adj x a ∧ (Q G).Adj x b ∧ a ≠ b ∧ ¬ (Q G).Adj a b := by
    intro x
    obtain ⟨a,b,hab,ha,hb,hnab⟩ := nonSim G hG hN x
    exact ⟨a,b,ha,hb,hab,hnab⟩
  have hC := ClawDiamondRoot.root_incidence_exhausted (Q G)
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) hn eAB.1
    (label_mem_left (Q G) eAB) (label_mem_right (Q G) eAB) hxC
  have hD := ClawDiamondRoot.root_incidence_exhausted (Q G)
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) hn eAB.1
    (label_mem_left (Q G) eAB) (label_mem_right (Q G) eAB) hxD
  rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
  · exact False.elim (eCD.1 rfl)
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact False.elim (eCD.1 rfl)

private theorem rel_of_ordinaryLabel_eq
    (p r : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN))
    (he : ordinaryLabel G hG hc hu hN p = ordinaryLabel G hG hc hu hN r) :
    PartialFisherCore.PortRel (K G) (z G hG hc hu hN)
      (HighPoleMatching.M G hG hc) (some p) (some r) := by
  rcases p with ⟨⟨A,B⟩,hp,hAB⟩
  rcases r with ⟨⟨C,D⟩,hr,hCD⟩
  let w := inc G hG hc hu hN A ⟨B,hAB⟩
  let t := inc G hG hc hu hN C ⟨D,hCD⟩
  change intersectionLabel (Q G) w.property = intersectionLabel (Q G) t.property at he
  rcases label_collision G hG hu hN w.property t.property he with hs | hx
  · have hAC : A = C := Subtype.ext hs.1
    subst C
    have hwt : w = t := Subtype.ext hs.2
    have hBD : B = D := congrArg Subtype.val ((inc G hG hc hu hN A).injective hwt)
    subst D
    exact Or.inl rfl
  · have hw := RetainedSuppressionIncidence.incidenceEquiv_spec (H G)
      (root_min_degree2 G hG hc hu hN) (root_degreeTwo_independent G hG hc hu hN)
      (root_triangle_free G hG hu hN) (root_degreeTwo_middle_unique G hG hc hu hN)
      A ⟨B,hAB⟩
    have ht := RetainedSuppressionIncidence.incidenceEquiv_spec (H G)
      (root_min_degree2 G hG hc hu hN) (root_degreeTwo_independent G hG hc hu hN)
      (root_triangle_free G hG hu hN) (root_degreeTwo_middle_unique G hG hc hu hN)
      C ⟨D,hCD⟩
    have hCB : C = B := by
      apply Subtype.ext
      rcases hw.2 with hd | ⟨h2,_⟩
      · exact hx.2.symm.trans hd
      · have hg := C.property
        change (H G).degree w.val = 2 at h2
        rw [hx.2] at h2
        omega
    have hAD : A = D := by
      apply Subtype.ext
      rcases ht.2 with hd | ⟨h2,_⟩
      · exact hx.1.trans hd
      · have hg := A.property
        change (H G).degree t.val = 2 at h2
        rw [← hx.1] at h2
        omega
    apply Or.inr
    refine ⟨hAD,hCB.symm,?_,?_,?_⟩
    · exact fun hh => hp (Subtype.ext hh)
    · exact fun hh => hr (hCB.trans (Subtype.ext hh))
    · have eAw : (H G).Adj A.val w.val := w.property
      simpa only [← hCB, ← hx.2] using eAw

/-- Equality of literal original labels is exactly equality in the canonical
partial Fisher quotient, without any assumption that M is a matching. -/
theorem portLabel_eq_iff
    (a b : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN)) :
    portLabel G hG hc hu hN a = portLabel G hG hc hu hN b ↔
    PartialFisherCore.PortRel (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) a b := by
  constructor
  · intro he
    cases a with
    | none =>
      cases b with
      | none => exact Or.inl rfl
      | some r => exact False.elim (portLabel_some_ne G hG hc hu hN r he.symm)
    | some p =>
      cases b with
      | none => exact False.elim (portLabel_some_ne G hG hc hu hN p he)
      | some r =>
        exact rel_of_ordinaryLabel_eq G hG hc hu hN p r (Subtype.ext he)
  · exact portLabel_eq_of_rel G hG hc hu hN a b

/-- No two distinct quotient vertices receive the same original vertex label. -/
theorem quotientLabel_injective : Function.Injective (quotientLabel G hG hc hu hN) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p r he
  exact Quotient.sound ((portLabel_eq_iff G hG hc hu hN p r).mp he)

private theorem exists_ordinary_root (x : {x : V // x ≠ v}) :
    ∃ A : RetainedDegreeSuppression.Retained (H G),
      A ≠ z G hG hc hu hN ∧ x ∈ A.val.val := by
  have hn : ∀ x : {x : V // x ≠ v}, ∃ a b,
      (Q G).Adj x a ∧ (Q G).Adj x b ∧ a ≠ b ∧ ¬ (Q G).Adj a b := by
    intro x
    obtain ⟨a,b,hab,ha,hb,hnab⟩ := nonSim G hG hN x
    exact ⟨a,b,ha,hb,hab,hnab⟩
  obtain ⟨A,B,hAB,hxA,hxB,_⟩ := ClawDiamondRoot.exactly_two_root_nodes (Q G)
    (HighPoleCompletion.completion_inducedDiamondFree G hG)
    (completion_claw_free G hu) hn x
  have eAB : (H G).Adj A B := ⟨hAB,x,hxA,hxB⟩
  by_cases hAP : A = poleRoot G hG hc
  · have hdB : (H G).degree B = 3 :=
      pole_arm_degree_three G hG hc hu hN B (hAP ▸ eAB)
    refine ⟨⟨B,by omega⟩,?_,hxB⟩
    exact fun he => hAB (hAP.trans (congrArg Subtype.val he).symm)
  by_cases hBP : B = poleRoot G hG hc
  · have hdA : (H G).degree A = 3 :=
      pole_arm_degree_three G hG hc hu hN A (hBP ▸ eAB.symm)
    refine ⟨⟨A,by omega⟩,?_,hxA⟩
    exact fun he => hAP (congrArg Subtype.val he)
  by_cases hA : 3 ≤ (H G).degree A
  · exact ⟨⟨A,hA⟩,fun he => hAP (congrArg Subtype.val he),hxA⟩
  · have hA2 : (H G).degree A = 2 := by
      have hmin : 2 ≤ (H G).degree A := root_min_degree2 G hG hc hu hN A
      omega
    have hB : 3 ≤ (H G).degree B := by
      have hmin : 2 ≤ (H G).degree B := root_min_degree2 G hG hc hu hN B
      have hn2 : (H G).degree B ≠ 2 := root_degreeTwo_independent G hG hc hu hN A B eAB hA2
      omega
    exact ⟨⟨B,hB⟩,fun he => hBP (congrArg Subtype.val he),hxB⟩

/-- Every original survivor is the actual label of an ordinary suppressed port. -/
theorem exists_portLabel (x : {x : V // x ≠ v}) :
    ∃ p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN),
      ordinaryLabel G hG hc hu hN p = x := by
  obtain ⟨A,hA,hxA⟩ := exists_ordinary_root G hG hc hu hN x
  let w := (lab G hG hu hN A.val).symm ⟨x,hxA⟩
  let b := (inc G hG hc hu hN A).symm w
  let p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN) :=
    ⟨(A,b.val),hA,b.property⟩
  refine ⟨p,?_⟩
  change (lab G hG hu hN A.val (inc G hG hc hu hN A b)).val = x
  rw [(inc G hG hc hu hN A).apply_symm_apply w]
  exact congrArg Subtype.val ((lab G hG hu hN A.val).apply_symm_apply ⟨x,hxA⟩)

/-- The canonical quotient labeling covers every vertex of the literal original graph. -/
theorem quotientLabel_surjective : Function.Surjective (quotientLabel G hG hc hu hN) := by
  intro x
  by_cases hx : x = v
  · subst x
    exact ⟨PartialFisherCore.q (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) none,rfl⟩
  · obtain ⟨p,hp⟩ := exists_portLabel G hG hc hu hN ⟨x,hx⟩
    refine ⟨PartialFisherCore.q (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) (some p),?_⟩
    exact congrArg Subtype.val hp

/-- The actual original vertices and the actual canonical partial Fisher quotient
vertices are in bijection, with no HIGH or matching assumption. -/
def vertexEquiv : PartialFisherCore.QuotientVertex (K G (v := v))
    (z G hG hc hu hN) (HighPoleMatching.M G hG hc) ≃ V :=
  Equiv.ofBijective (quotientLabel G hG hc hu hN)
    ⟨quotientLabel_injective G hG hc hu hN,quotientLabel_surjective G hG hc hu hN⟩

/-- The canonical vertex equivalence evaluates to the concrete label on every port. -/
theorem vertexEquiv_q (p : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN)) :
    vertexEquiv G hG hc hu hN
      (PartialFisherCore.q (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) p) =
      portLabel G hG hc hu hN p := rfl

private theorem inc_spec (A B : RetainedDegreeSuppression.Retained (H G (v := v)))
    (hAB : (K G).Adj A B) :
    RetainedSuppressionIncidence.FirstStep (H G) A B
      (inc G hG hc hu hN A ⟨B,hAB⟩).val :=
  RetainedSuppressionIncidence.incidenceEquiv_spec (H G)
    (root_min_degree2 G hG hc hu hN) (root_degreeTwo_independent G hG hc hu hN)
    (root_triangle_free G hG hu hN) (root_degreeTwo_middle_unique G hG hc hu hN) A ⟨B,hAB⟩

private theorem inc_corridor (A B : RetainedDegreeSuppression.Retained (H G (v := v)))
    (hAB : (K G).Adj A B) (E : RootNode (Q G))
    (hE : (H G).degree E = 2) (eAE : (H G).Adj A.val E) (eEB : (H G).Adj E B.val) :
    (inc G hG hc hu hN A ⟨B,hAB⟩).val = E :=
  RetainedSuppressionIncidence.firstStep_eq_of_spec (H G)
    (root_triangle_free G hG hu hN) (root_degreeTwo_middle_unique G hG hc hu hN)
    A B hAB ⟨eAE,Or.inr ⟨hE,eEB⟩⟩

private theorem ordinaryLabel_corridor
    (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN))
    (E : RootNode (Q G)) (hE : (H G).degree E = 2)
    (eAE : (H G).Adj p.val.1.val E) (eEB : (H G).Adj E p.val.2.val) :
    ordinaryLabel G hG hc hu hN p ∈ E.val := by
  have hm := ordinaryLabel_mem_firstStep G hG hc hu hN p
  have hw := inc_corridor G hG hc hu hN _ _ p.property.2 E hE eAE eEB
  rw [hw] at hm
  exact hm

private theorem generator_adj
    (a b : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN))
    (hne : portLabel G hG hc hu hN a ≠ portLabel G hG hc hu hN b)
    (hab : PartialFisherCore.FisherRel (K G) (z G hG hc hu hN) a b) :
    G.Adj (portLabel G hG hc hu hN a) (portLabel G hG hc hu hN b) := by
  cases a with
  | none =>
    cases b with
    | none => exact False.elim hab
    | some p =>
      have hz : p.val.2 = z G hG hc hu hN := hab.1
      let w := inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩
      have hw : w.val = poleRoot G hG hc := by
        rcases (inc_spec G hG hc hu hN _ _ p.property.2).2 with hd | ⟨h2,ewz⟩
        · exact hd.trans (congrArg Subtype.val hz)
        · have ePw : (H G).Adj (poleRoot G hG hc) w.val := by
            have hpole : p.val.2.val = poleRoot G hG hc := congrArg Subtype.val hz
            exact (congrArg (fun X => (H G).Adj X w.val) hpole).mp ewz.symm
          have h3 : (H G).degree w.val = 3 := pole_arm_degree_three G hG hc hu hN w.val ePw
          change (H G).degree w.val = 2 at h2
          omega
      have hm := ordinaryLabel_mem_firstStep G hG hc hu hN p
      change ordinaryLabel G hG hc hu hN p ∈ w.val.val at hm
      rw [hw] at hm
      exact hm
  | some p =>
    cases b with
    | none => exact False.elim hab
    | some r =>
      have hpr : ordinaryLabel G hG hc hu hN p ≠ ordinaryLabel G hG hc hu hN r :=
        fun he => hne (congrArg Subtype.val he)
      rcases hab with htri | hcon
      · have hr := ordinaryLabel_mem_first G hG hc hu hN r
        rw [← htri.1] at hr
        exact nonpole_adj_original G hG hc p.val.1.val
          (fun he => p.property.1 (Subtype.ext he))
          (ordinaryLabel_mem_first G hG hc hu hN p) hr hpr
      · have hd : ¬ (H G).Adj p.val.1.val p.val.2.val := by
          intro hd
          have hM : (HighPoleMatching.M G hG hc).Adj p.val.1 p.val.2 :=
            ⟨fun he => p.property.1 (Subtype.ext he),
             fun he => r.property.1 (hcon.2.1.symm.trans (Subtype.ext he)),hd⟩
          exact hne (portLabel_eq_of_rel G hG hc hu hN (some p) (some r)
            (Or.inr ⟨hcon.1,hcon.2.1,hM⟩))
        rcases p.property.2.2 with hd' | ⟨E,hE,eAE,eEB⟩
        · exact False.elim (hd hd')
        · have hEP : E ≠ poleRoot G hG hc := by
            intro he
            have hg := (z G hG hc hu hN).property
            change 3 ≤ (H G).degree (poleRoot G hG hc) at hg
            rw [he] at hE
            omega
          have erE : (H G).Adj r.val.1.val E := by
            simpa only [hcon.2.1] using eEB.symm
          have eEr : (H G).Adj E r.val.2.val := by
            simpa only [hcon.1] using eAE.symm
          exact nonpole_adj_original G hG hc E hEP
            (ordinaryLabel_corridor G hG hc hu hN p E hE eAE eEB)
            (ordinaryLabel_corridor G hG hc hu hN r E hE erE eEr) hpr

/-- Every actual partial Fisher quotient edge represents an edge of the literal
original graph; contracted loops are excluded by the map adjacency relation. -/
theorem quotientLabel_adj
    (a b : PartialFisherCore.QuotientVertex (K G (v := v))
      (z G hG hc hu hN) (HighPoleMatching.M G hG hc))
    (hab : (PartialFisherCore.G (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc)).Adj a b) :
    G.Adj (quotientLabel G hG hc hu hN a) (quotientLabel G hG hc hu hN b) := by
  rcases hab with ⟨hne,p,r,hpr,hp,hr⟩
  have hlabels : portLabel G hG hc hu hN p ≠ portLabel G hG hc hu hN r := by
    intro he
    apply hne
    rw [← hp,← hr]
    exact Quotient.sound ((portLabel_eq_iff G hG hc hu hN p r).mp he)
  have hrel := (SimpleGraph.fromRel_adj _ p r).mp hpr
  rw [← hp,← hr]
  rcases hrel.2 with hforward | hbackward
  · exact generator_adj G hG hc hu hN p r hlabels hforward
  · exact (generator_adj G hG hc hu hN r p hlabels.symm hbackward).symm

private abbrev q₀ := PartialFisherCore.q (K G (v := v)) (z G hG hc hu hN) (HighPoleMatching.M G hG hc)
private abbrev core := PartialFisherCore.G (K G (v := v)) (z G hG hc hu hN) (HighPoleMatching.M G hG hc)

private theorem exists_port_at (A : RetainedDegreeSuppression.Retained (H G (v := v)))
    (hA : A ≠ z G hG hc hu hN) (x : {x : V // x ≠ v}) (hxA : x ∈ A.val.val) :
    ∃ p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN),
      p.val.1 = A ∧ ordinaryLabel G hG hc hu hN p = x := by
  let w := (lab G hG hu hN A.val).symm ⟨x,hxA⟩
  let b := (inc G hG hc hu hN A).symm w
  let p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN) :=
    ⟨(A,b.val),hA,b.property⟩
  refine ⟨p,rfl,?_⟩
  change (lab G hG hu hN A.val (inc G hG hc hu hN A b)).val = x
  rw [(inc G hG hc hu hN A).apply_symm_apply w]
  exact congrArg Subtype.val ((lab G hG hu hN A.val).apply_symm_apply ⟨x,hxA⟩)

private theorem spoke_of_original (x : {x : V // x ≠ v}) (hvx : G.Adj v x.val) :
    ∃ p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN),
      ordinaryLabel G hG hc hu hN p = x ∧
      (core G hG hc hu hN).Adj (q₀ G hG hc hu hN none) (q₀ G hG hc hu hN (some p)) := by
  obtain ⟨A,hA,hxA⟩ := exists_ordinary_root G hG hc hu hN x
  have eAP : (H G).Adj A.val (poleRoot G hG hc) :=
    ⟨fun he => hA (Subtype.ext he),x,hxA,hvx⟩
  have eAz : (K G).Adj A (z G hG hc hu hN) := ⟨hA,Or.inl eAP⟩
  let p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN) :=
    ⟨(A,z G hG hc hu hN),hA,eAz⟩
  refine ⟨p,?_,?_⟩
  · rw [ordinaryLabel_direct G hG hc hu hN p eAP]
    exact label_unique (Q G) (HighPoleCompletion.completion_inducedDiamondFree G hG) eAP hxA hvx
  · exact PartialFisherCore.pole_spoke (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) A eAz.symm

private theorem triangle_of_original
    (x y : {x : V // x ≠ v}) (hxy : x ≠ y)
    (E : RootNode (Q G)) (hEP : E ≠ poleRoot G hG hc)
    (hxE : x ∈ E.val) (hyE : y ∈ E.val) (hE : (H G).degree E = 3) :
    ∃ p r : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN),
      ordinaryLabel G hG hc hu hN p = x ∧ ordinaryLabel G hG hc hu hN r = y ∧
      (core G hG hc hu hN).Adj (q₀ G hG hc hu hN (some p)) (q₀ G hG hc hu hN (some r)) := by
  let A : RetainedDegreeSuppression.Retained (H G) := ⟨E,by omega⟩
  have hA : A ≠ z G hG hc hu hN := fun he => hEP (congrArg Subtype.val he)
  obtain ⟨p,hpA,hpx⟩ := exists_port_at G hG hc hu hN A hA x hxE
  obtain ⟨r,hrA,hry⟩ := exists_port_at G hG hc hu hN A hA y hyE
  refine ⟨p,r,hpx,hry,?_⟩
  apply PartialFisherCore.quotienttriangleedge (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc) A p r hpA hrA
  intro he
  apply hxy
  exact hpx.symm.trans ((congrArg (ordinaryLabel G hG hc hu hN) he).trans hry)

private theorem ordinaryLabel_corridor_eq
    (p : PartialFisherCore.OrdinaryPort (K G (v := v)) (z G hG hc hu hN))
    (E : RootNode (Q G)) (hE : (H G).degree E = 2)
    (eAE : (H G).Adj p.val.1.val E) (eEB : (H G).Adj E p.val.2.val)
    (x : {x : V // x ≠ v}) (hxA : x ∈ p.val.1.val.val) (hxE : x ∈ E.val) :
    ordinaryLabel G hG hc hu hN p = x := by
  let w := inc G hG hc hu hN p.val.1 ⟨p.val.2,p.property.2⟩
  change intersectionLabel (Q G) w.property = x
  apply label_unique (Q G) (HighPoleCompletion.completion_inducedDiamondFree G hG)
  · exact hxA
  · have hw : w.val = E := inc_corridor G hG hc hu hN _ _ p.property.2 E hE eAE eEB
    rw [hw]
    exact hxE

private theorem connector_of_original
    (x y : {x : V // x ≠ v}) (hxy : x ≠ y)
    (E : RootNode (Q G)) (hxE : x ∈ E.val) (hyE : y ∈ E.val)
    (hE : (H G).degree E = 2) :
    ∃ p r : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN),
      ordinaryLabel G hG hc hu hN p = x ∧ ordinaryLabel G hG hc hu hN r = y ∧
      (core G hG hc hu hN).Adj (q₀ G hG hc hu hN (some p)) (q₀ G hG hc hu hN (some r)) := by
  let a := (lab G hG hu hN E).symm ⟨x,hxE⟩
  let b := (lab G hG hu hN E).symm ⟨y,hyE⟩
  have eEA : (H G).Adj E a.val := a.property
  have eEB : (H G).Adj E b.val := b.property
  have hxA : x ∈ a.val.val :=
    rootNeighborEquiv_symm_mem (Q G) (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonSim G hG hN) E ⟨x,hxE⟩
  have hyB : y ∈ b.val.val :=
    rootNeighborEquiv_symm_mem (Q G) (HighPoleCompletion.completion_inducedDiamondFree G hG)
      (completion_claw_free G hu) (nonSim G hG hN) E ⟨y,hyE⟩
  have ha : 3 ≤ (H G).degree a.val := by
    have hmin : 2 ≤ (H G).degree a.val := root_min_degree2 G hG hc hu hN a.val
    have hn2 : (H G).degree a.val ≠ 2 := root_degreeTwo_independent G hG hc hu hN E a.val eEA hE
    omega
  have hb : 3 ≤ (H G).degree b.val := by
    have hmin : 2 ≤ (H G).degree b.val := root_min_degree2 G hG hc hu hN b.val
    have hn2 : (H G).degree b.val ≠ 2 := root_degreeTwo_independent G hG hc hu hN E b.val eEB hE
    omega
  have hAP : a.val ≠ poleRoot G hG hc := by
    intro he
    have h3 : (H G).degree E = 3 := pole_arm_degree_three G hG hc hu hN E (he ▸ eEA.symm)
    omega
  have hBP : b.val ≠ poleRoot G hG hc := by
    intro he
    have h3 : (H G).degree E = 3 := pole_arm_degree_three G hG hc hu hN E (he ▸ eEB.symm)
    omega
  have hAB : a.val ≠ b.val := by
    intro he
    have hyA : y ∈ a.val.val := (congrArg (fun T => y ∈ T.val) he).mpr hyB
    exact hxy (ClawDiamondRoot.root_intersection_unique (Q G)
      (HighPoleCompletion.completion_inducedDiamondFree G hG) eEA.1 hxE hxA hyE hyA)
  let A : RetainedDegreeSuppression.Retained (H G) := ⟨a.val,ha⟩
  let B : RetainedDegreeSuppression.Retained (H G) := ⟨b.val,hb⟩
  have hAz : A ≠ z G hG hc hu hN := fun he => hAP (congrArg Subtype.val he)
  have hBz : B ≠ z G hG hc hu hN := fun he => hBP (congrArg Subtype.val he)
  have eAB : (K G).Adj A B := by
    refine ⟨?_,Or.inr ⟨E,hE,eEA.symm,eEB⟩⟩
    intro he
    have hv : A.val = B.val := congrArg Subtype.val he
    exact hAB hv
  have hM : ¬ (HighPoleMatching.M G hG hc).Adj A B := by
    intro hm
    exact root_triangle_free G hG hu hN _ _ _ eEA.symm eEB hm.2.2.symm
  let p : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN) := ⟨(A,B),hAz,eAB⟩
  let r : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN) := ⟨(B,A),hBz,eAB.symm⟩
  refine ⟨p,r,?_,?_,?_⟩
  · exact ordinaryLabel_corridor_eq G hG hc hu hN p E hE eEA.symm eEB x hxA hxE
  · exact ordinaryLabel_corridor_eq G hG hc hu hN r E hE eEB.symm eEA y hyB hyE
  · exact PartialFisherCore.noncontracted_connector_edge (K G) (z G hG hc hu hN)
      (HighPoleMatching.M G hG hc) A B hAz hBz eAB hM

private theorem survivor_edge (x y : {x : V // x ≠ v}) (hab : G.Adj x.val y.val) :
    ∃ p r : PartialFisherCore.OrdinaryPort (K G) (z G hG hc hu hN),
      ordinaryLabel G hG hc hu hN p = x ∧ ordinaryLabel G hG hc hu hN r = y ∧
      (core G hG hc hu hN).Adj (q₀ G hG hc hu hN (some p)) (q₀ G hG hc hu hN (some r)) := by
  have hxy : x ≠ y := fun he => hab.ne (congrArg Subtype.val he)
  have eQ : (Q G).Adj x y := Or.inl hab
  obtain ⟨E,⟨hxE,hyE⟩,_⟩ := ClawDiamondRoot.exactly_one_root_node_of_adj (Q G)
    (HighPoleCompletion.completion_inducedDiamondFree G hG) eQ
  have hEP : E ≠ poleRoot G hG hc := by
    intro he
    rw [he] at hxE hyE
    exact hN x.val y.val hxE hyE hab
  rcases nonpole_degree_two_or_three G hG hc hu hN E hEP with h2 | h3
  · exact connector_of_original G hG hc hu hN x y hxy E hxE hyE h2
  · exact triangle_of_original G hG hc hu hN x y hxy E hEP hxE hyE h3

/-- Every literal original edge is represented by an actual partial Fisher
quotient edge, using only the canonical root and suppression constructions. -/
theorem adj_of_quotientLabel_adj
    (a b : PartialFisherCore.QuotientVertex (K G (v := v))
      (z G hG hc hu hN) (HighPoleMatching.M G hG hc))
    (hab : G.Adj (quotientLabel G hG hc hu hN a) (quotientLabel G hG hc hu hN b)) :
    (PartialFisherCore.G (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc)).Adj a b := by
  by_cases hx : quotientLabel G hG hc hu hN a = v
  · have hy : quotientLabel G hG hc hu hN b ≠ v := fun he => hab.ne (hx.trans he.symm)
    have hvy : G.Adj v (quotientLabel G hG hc hu hN b) := by
      simpa only [hx] using hab
    obtain ⟨p,hp,e⟩ := spoke_of_original G hG hc hu hN ⟨quotientLabel G hG hc hu hN b,hy⟩ hvy
    have ha : a = q₀ G hG hc hu hN none := quotientLabel_injective G hG hc hu hN hx
    have hb : q₀ G hG hc hu hN (some p) = b :=
      quotientLabel_injective G hG hc hu hN (congrArg Subtype.val hp)
    rw [ha,← hb]
    exact e
  by_cases hy : quotientLabel G hG hc hu hN b = v
  · have hvx : G.Adj v (quotientLabel G hG hc hu hN a) := by
      simpa only [hy] using hab.symm
    obtain ⟨p,hp,e⟩ := spoke_of_original G hG hc hu hN ⟨quotientLabel G hG hc hu hN a,hx⟩ hvx
    have hb : b = q₀ G hG hc hu hN none := quotientLabel_injective G hG hc hu hN hy
    have ha : q₀ G hG hc hu hN (some p) = a :=
      quotientLabel_injective G hG hc hu hN (congrArg Subtype.val hp)
    rw [← ha,hb]
    exact e.symm
  · obtain ⟨p,r,hp,hr,e⟩ := survivor_edge G hG hc hu hN
      ⟨quotientLabel G hG hc hu hN a,hx⟩ ⟨quotientLabel G hG hc hu hN b,hy⟩ hab
    have ha : q₀ G hG hc hu hN (some p) = a :=
      quotientLabel_injective G hG hc hu hN (congrArg Subtype.val hp)
    have hb : q₀ G hG hc hu hN (some r) = b :=
      quotientLabel_injective G hG hc hu hN (congrArg Subtype.val hr)
    rw [← ha,← hb]
    exact e

/-- Adjacency in the actual canonical partial Fisher quotient is exactly
adjacency in the literal original graph under its concrete vertex labels. -/
theorem quotientLabel_adj_iff
    (a b : PartialFisherCore.QuotientVertex (K G (v := v))
      (z G hG hc hu hN) (HighPoleMatching.M G hG hc)) :
    (PartialFisherCore.G (K G) (z G hG hc hu hN) (HighPoleMatching.M G hG hc)).Adj a b ↔
      G.Adj (quotientLabel G hG hc hu hN a) (quotientLabel G hG hc hu hN b) :=
  ⟨quotientLabel_adj G hG hc hu hN a b,adj_of_quotientLabel_adj G hG hc hu hN a b⟩

/-- The actual canonical partial Fisher quotient is isomorphic to the literal
original graph. No HIGH, minimality, connectivity, or representation certificate
is required. -/
def coreIso : (PartialFisherCore.G (K G (v := v)) (z G hG hc hu hN)
    (HighPoleMatching.M G hG hc)) ≃g G where
  toEquiv := vertexEquiv G hG hc hu hN
  map_rel_iff' := fun {a b} => (quotientLabel_adj_iff G hG hc hu hN a b).symm

/-- The literal original graph is isomorphic to its actual canonical partially
contracted Fisher graph, without assuming that the canonical M is a matching. -/
def originalIso : G ≃g (PartialFisherCore.G (K G (v := v)) (z G hG hc hu hN)
    (HighPoleMatching.M G hG hc)) :=
  (coreIso G hG hc hu hN).symm

/-- The canonical graph isomorphism sends each concrete port class to precisely
its actual original-graph label. -/
theorem coreIso_q (p : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN)) :
    coreIso G hG hc hu hN (q₀ G hG hc hu hN p) = portLabel G hG hc hu hN p := rfl

/-- Applying the original-to-core isomorphism to a concrete port's original
label recovers that exact quotient port class. -/
theorem originalIso_portLabel (p : PartialFisherCore.Port (K G (v := v)) (z G hG hc hu hN)) :
    originalIso G hG hc hu hN (portLabel G hG hc hu hN p) = q₀ G hG hc hu hN p :=
  (coreIso G hG hc hu hN).symm_apply_apply (q₀ G hG hc hu hN p)

end Erdos64.HighPoleFisherRepresentation
