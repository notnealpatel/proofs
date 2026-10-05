import Erdos.Erdos64.ClawDiamondRoot
import Mathlib.Data.Fintype.BigOperators

/-!
Generic incidence counting for the canonical maximal-clique root. This is the
standard clique-root incidence description of a line graph, with no bound on
clique size. The joint C₄ witness for the hypotheses is checked in ClawDiamondRoot.
-/

set_option autoImplicit false

namespace Erdos64.GeneralRootIncidence

open SimpleGraph
open Erdos64.UniqueCubicClawCenter (Claw RootNode cliqueRoot)
open Erdos64.ClawDiamondRoot

universe u

variable {V : Type u} (R : SimpleGraph V)
variable (hDiamond : ∀ a b c d : V, c ≠ d → R.Adj a b → R.Adj a c → R.Adj a d →
  R.Adj b c → R.Adj b d → ¬ R.Adj c d → False)
variable (hClaw : ∀ x, ¬ Claw R x)
variable (hNonSim : ∀ x, ∃ a b : V, a ≠ b ∧ R.Adj x a ∧ R.Adj x b ∧ ¬ R.Adj a b)

include hNonSim in
private theorem nonsimplicial (x : V) :
    ∃ a b : V, R.Adj x a ∧ R.Adj x b ∧ a ≠ b ∧ ¬ R.Adj a b := by
  obtain ⟨a, b, hab, hxa, hxb, hnab⟩ := hNonSim x
  exact ⟨a, b, hxa, hxb, hab, hnab⟩

/-- The label of a root edge is its unique shared original vertex. -/
noncomputable def intersectionLabel {A B : RootNode R}
    (hAB : (cliqueRoot R).Adj A B) : V := Classical.choose hAB.2

/-- The root-edge label belongs to the left maximal clique. -/
theorem label_mem_left {A B : RootNode R} (hAB : (cliqueRoot R).Adj A B) :
    intersectionLabel R hAB ∈ A.val := (Classical.choose_spec hAB.2).1

/-- The root-edge label belongs to the right maximal clique. -/
theorem label_mem_right {A B : RootNode R} (hAB : (cliqueRoot R).Adj A B) :
    intersectionLabel R hAB ∈ B.val := (Classical.choose_spec hAB.2).2

include hDiamond in
/-- Any common member of the endpoints is the selected edge label. -/
theorem label_unique {A B : RootNode R} (hAB : (cliqueRoot R).Adj A B)
    {x : V} (hxA : x ∈ A.val) (hxB : x ∈ B.val) :
    intersectionLabel R hAB = x :=
  root_intersection_unique R hDiamond hAB.1
    (label_mem_left R hAB) (label_mem_right R hAB) hxA hxB

include hDiamond in
/-- Reversing the root edge preserves its label. -/
theorem label_symm {A B : RootNode R} (hAB : (cliqueRoot R).Adj A B) :
    intersectionLabel R hAB.symm = intersectionLabel R hAB :=
  label_unique R hDiamond hAB.symm (label_mem_right R hAB) (label_mem_left R hAB)

include hDiamond hClaw hNonSim in
private theorem label_bijective (A : RootNode R) :
    Function.Bijective (fun B : (cliqueRoot R).neighborSet A =>
      (⟨intersectionLabel R B.property, label_mem_left R B.property⟩ : A.val)) := by
  constructor
  · intro B C heq
    have hval : intersectionLabel R B.property = intersectionLabel R C.property :=
      congrArg Subtype.val heq
    have hxB : intersectionLabel R C.property ∈ B.val.val := by
      rw [← hval]
      exact label_mem_right R B.property
    rcases root_incidence_exhausted R hDiamond hClaw (nonsimplicial R hNonSim)
        B.property.1 (label_mem_left R C.property) hxB (label_mem_right R C.property)
        with hCA | hCB
    · exact False.elim (C.property.1 hCA.symm)
    · exact Subtype.ext hCB.symm
  · intro x
    obtain ⟨C, D, hCD, hxC, hxD, hfiber⟩ :=
      exactly_two_root_nodes R hDiamond hClaw (nonsimplicial R hNonSim) x.val
    have hother : ∃ B : RootNode R, A ≠ B ∧ x.val ∈ B.val := by
      rcases (hfiber A).mp x.property with hAC | hAD
      · exact ⟨D, hAC ▸ hCD, hxD⟩
      · exact ⟨C, hAD ▸ hCD.symm, hxC⟩
    obtain ⟨B, hAB, hxB⟩ := hother
    let B' : (cliqueRoot R).neighborSet A := ⟨B, hAB, x.val, x.property, hxB⟩
    exact ⟨B', Subtype.ext (label_unique R hDiamond B'.property x.property hxB)⟩

/-- Root neighbors correspond bijectively to the original labels in that root clique. -/
noncomputable def rootNeighborEquiv (A : RootNode R) :
    (cliqueRoot R).neighborSet A ≃ {x : V // x ∈ A.val} :=
  Equiv.ofBijective _ (label_bijective R hDiamond hClaw hNonSim A)

/-- The forward equivalence sends a neighbor to the unique intersection label. -/
theorem rootNeighborEquiv_apply (A : RootNode R) (B : (cliqueRoot R).neighborSet A) :
    (rootNeighborEquiv R hDiamond hClaw hNonSim A B).val =
      intersectionLabel R B.property := rfl

include hDiamond hClaw hNonSim in
/-- A root node's degree is exactly its maximal clique's cardinality. -/
theorem degree_eq_card [Fintype V] [DecidableRel (cliqueRoot R).Adj] (A : RootNode R) :
    (cliqueRoot R).degree A = Fintype.card {x : V // x ∈ A.val} := by
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_congr (rootNeighborEquiv R hDiamond hClaw hNonSim A)

include hDiamond hClaw hNonSim in
/-- The inverse equivalence picks the other root clique through the given label. -/
theorem rootNeighborEquiv_symm_mem (A : RootNode R) (x : A.val) :
    x.val ∈ ((rootNeighborEquiv R hDiamond hClaw hNonSim A).symm x).val.val := by
  let e := rootNeighborEquiv R hDiamond hClaw hNonSim A
  have hlabel : intersectionLabel R (e.symm x).property = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  rw [← hlabel]
  exact label_mem_right R (e.symm x).property

include hDiamond hNonSim in
/-- In a nonempty original graph, every maximal root clique contains two distinct labels.
Nonemptiness excludes the empty maximal clique of the empty graph. -/
theorem root_has_two_labels [Nonempty V] (A : RootNode R) :
    ∃ x y : A.val, x ≠ y := by
  have hne : A.val.Nonempty := by
    by_contra hn
    have hempty : A.val = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    let v : V := Classical.choice inferInstance
    have hsub : ({v} : Set V) ⊆ A.val :=
      (SimpleGraph.isMaximalClique_iff.mp A.property).2 _
        (R.isClique_singleton v) (by rw [hempty]; exact Set.empty_subset _)
    have hv : v ∈ A.val := hsub (Set.mem_singleton v)
    simp [hempty] at hv
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, b, hab, hxa, hxb, hnab⟩ := hNonSim x
  obtain ⟨y, hy, hyx⟩ := maximal_clique_other_vertex R hDiamond hxa A.property hx
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun heq => hyx (congrArg Subtype.val heq).symm⟩

include hDiamond hClaw hNonSim in
/-- Every root node has degree at least two when the original vertex type is nonempty. -/
theorem root_min_degree [Fintype V] [Nonempty V]
    [DecidableRel (cliqueRoot R).Adj] (A : RootNode R) :
    2 ≤ (cliqueRoot R).degree A := by
  rw [degree_eq_card R hDiamond hClaw hNonSim A]
  have hcard : 1 < Fintype.card {x : V // x ∈ A.val} :=
    Fintype.one_lt_card_iff.mpr (root_has_two_labels R hDiamond hNonSim A)
  exact hcard

/-- Root incidence fibers are finite as subtypes of the finite maximal-clique root. -/
noncomputable instance incidenceFiberFintype [Fintype V] (x : V) :
    Fintype {A : RootNode R // x ∈ A.val} := Fintype.ofFinite _

include hDiamond hClaw hNonSim in
/-- The incidence fiber of any original label has cardinality exactly two. -/
theorem incidence_card_two [Fintype V] (x : V) :
    Fintype.card {A : RootNode R // x ∈ A.val} = 2 := by
  classical
  obtain ⟨A, B, hAB, hxA, hxB, hfiber⟩ :=
    exactly_two_root_nodes R hDiamond hClaw (nonsimplicial R hNonSim) x
  calc
    Fintype.card {A : RootNode R // x ∈ A.val} = ({A, B} : Finset (RootNode R)).card :=
      Fintype.card_of_subtype _ (fun C => by simpa only [Finset.mem_insert,
        Finset.mem_singleton] using (hfiber C).symm)
    _ = 2 := Finset.card_pair hAB

/-- Swapping the node and label identifies the two ways to enumerate root incidences. -/
noncomputable def incidenceSwap :
    (Σ A : RootNode R, {x : V // x ∈ A.val}) ≃
      (Σ x : V, {A : RootNode R // x ∈ A.val}) where
  toFun p := ⟨p.2.val, p.1, p.2.property⟩
  invFun p := ⟨p.2.val, p.1, p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Incidence swapping preserves both the label and the node. -/
theorem incidenceSwap_apply (A : RootNode R) (x : A.val) :
    incidenceSwap R ⟨A, x⟩ = ⟨x.val, A, x.property⟩ := rfl

include hDiamond hClaw hNonSim in
/-- The sum of root degrees equals twice the number of original labels. -/
theorem sum_degrees_eq_twice_card [Fintype V] [DecidableRel (cliqueRoot R).Adj] :
    ∑ A : RootNode R, (cliqueRoot R).degree A = 2 * Fintype.card V := by
  classical
  calc
    ∑ A : RootNode R, (cliqueRoot R).degree A =
        ∑ A : RootNode R, Fintype.card A.val := by
      apply Finset.sum_congr rfl
      intro A hA
      exact degree_eq_card R hDiamond hClaw hNonSim A
    _ = Fintype.card (Σ A : RootNode R, {x : V // x ∈ A.val}) :=
      Fintype.card_sigma.symm
    _ = Fintype.card (Σ x : V, {A : RootNode R // x ∈ A.val}) :=
      Fintype.card_congr (incidenceSwap R)
    _ = ∑ x : V, Fintype.card {A : RootNode R // x ∈ A.val} := Fintype.card_sigma
    _ = ∑ _x : V, 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact incidence_card_two R hDiamond hClaw hNonSim x
    _ = 2 * Fintype.card V := by simp [Nat.mul_comm]

end Erdos64.GeneralRootIncidence
