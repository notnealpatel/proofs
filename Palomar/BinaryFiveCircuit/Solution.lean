import BilinearComplexity.BinaryFiveCircuitTheorem

/-!
# Binary five-circuit ambient classification solution

The independent model and satisfiability theorem below are repeated verbatim
from Challenge. This module does not import Challenge. The Bridge namespace
identifies the thirteen labels, proves exact intrinsic-move equivalence,
transports paths with unchanged vertices and metrics, and proves that the
independent orbit characterization is equivalent to the source presentation/
orientation/factorwise-GL action-witness predicate on exactly the headline
domain. The final theorem uses this checked equivalence and path transport.

AI assistance was material; no human review or novelty is claimed.
-/

set_option autoImplicit false

namespace Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCarrier

/-- The binary field. -/
abbrev F2 : Type := ZMod 2

example : (1 : F2) + 1 = 0 := by decide

end Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCarrier

namespace Palomar.BinaryFiveCircuit.Model.BinaryCircuit

/-- A scheme is a finite set, so duplicate terms are not retained. -/
abbrev Scheme (α : Type*) := Finset α

universe u

/-- A finite path whose indices record its initial and terminal schemes. -/
inductive MovePath {α : Type u} (R : Scheme α → Scheme α → Prop) :
    Scheme α → Scheme α → Type u
  | singleton (D : Scheme α) : MovePath R D D
  | snoc {D E F : Scheme α} : MovePath R D E → R E F → MovePath R D F

namespace MovePath

/-- The number of edges in a path. -/
def length {α : Type*} {R : Scheme α → Scheme α → Prop} :
    {D E : Scheme α} → MovePath R D E → ℕ
  | _, _, .singleton _ => 0
  | _, _, .snoc path _ => length (R := R) path + 1

/-- The ordered list of states visited by a path. -/
def vertices {α : Type*} {R : Scheme α → Scheme α → Prop} :
    {D E : Scheme α} → MovePath R D E → List (Scheme α)
  | _, _, .singleton D => [D]
  | _, E, .snoc path _ => vertices (R := R) path ++ [E]

/-- The greatest state cardinality visited by a path. -/
def altitude {α : Type*} {R : Scheme α → Scheme α → Prop} :
    {D E : Scheme α} → MovePath R D E → ℕ
  | _, _, .singleton D => D.card
  | _, E, .snoc path _ => max (altitude (R := R) path) E.card

example {α : Type*} {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    (MovePath.singleton D : MovePath R D D).length = 0 := by simp [length]

example {α : Type*} {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    (MovePath.singleton D : MovePath R D D).vertices = [D] := by simp [vertices]

example {α : Type*} {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    (MovePath.singleton D : MovePath R D D).altitude = D.card := by simp [altitude]

end MovePath

/-- A state is an actual vertex of the displayed path. -/
def PathVertex {α : Type*} {R : Scheme α → Scheme α → Prop}
    {D E : Scheme α} (path : MovePath R D E) (X : Scheme α) : Prop :=
  X ∈ path.vertices

example {α : Type*} {R : Scheme α → Scheme α → Prop} (D : Scheme α) :
    PathVertex (MovePath.singleton D : MovePath R D D) D := by
  simp [PathVertex, MovePath.vertices]

end Palomar.BinaryFiveCircuit.Model.BinaryCircuit

namespace Palomar.BinaryFiveCircuit.Model.BinaryAmbientCarrier

open scoped TensorProduct BigOperators
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCarrier

universe u v w

/-- A vector equipped with evidence that it is nonzero. -/
abbrev NonzeroVector (U : Type u) [Zero U] := {x : U // x ≠ 0}

/-- A pure-tensor carrier point represented by three nonzero factors. -/
abbrev Carrier (U : Type u) (V : Type v) (W : Type w)
    [Zero U] [Zero V] [Zero W] :=
  NonzeroVector U × NonzeroVector V × NonzeroVector W

/-- An ambient state is a finite set of pure-tensor carrier points. -/
abbrev State (U : Type u) (V : Type v) (W : Type w)
    [Zero U] [Zero V] [Zero W] := Finset (Carrier U V W)

/-- Evaluate a carrier point as a nested pure tensor. -/
def tensorEvaluation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    (t : Carrier U V W) : U ⊗[F2] (V ⊗[F2] W) :=
  t.1.1 ⊗ₜ (t.2.1.1 ⊗ₜ t.2.2.1)

example (u v w : F2) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    tensorEvaluation (⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩) = u ⊗ₜ (v ⊗ₜ w) := rfl

/-- Evaluate a state by summing its nested pure tensors. -/
def stateEvaluation
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    (D : State U V W) : U ⊗[F2] (V ⊗[F2] W) :=
  ∑ t ∈ D, tensorEvaluation t

example : stateEvaluation (∅ : State F2 F2 F2) = 0 := by
  simp [stateEvaluation]

/-- The span of all first factors occurring in a state. -/
def firstSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)] (D : State U V W) : Submodule F2 U :=
  Submodule.span F2 ((fun t : Carrier U V W => t.1.1) '' (D : Set (Carrier U V W)))

/-- The span of all second factors occurring in a state. -/
def secondSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)] (D : State U V W) : Submodule F2 V :=
  Submodule.span F2 ((fun t : Carrier U V W => t.2.1.1) '' (D : Set (Carrier U V W)))

/-- The span of all third factors occurring in a state. -/
def thirdSpan
    {U : Type u} {V : Type v} {W : Type w}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module F2 U] [Module F2 V] [Module F2 W]
    [DecidableEq (Carrier U V W)] (D : State U V W) : Submodule F2 W :=
  Submodule.span F2 ((fun t : Carrier U V W => t.2.2.1) '' (D : Set (Carrier U V W)))

example : firstSpan (∅ : State F2 F2 F2) = ⊥ := by simp [firstSpan]
example : secondSpan (∅ : State F2 F2 F2) = ⊥ := by simp [secondSpan]
example : thirdSpan (∅ : State F2 F2 F2) = ⊥ := by simp [thirdSpan]

end Palomar.BinaryFiveCircuit.Model.BinaryAmbientCarrier

namespace Palomar.BinaryFiveCircuit.Model.BinaryAmbientMoves

open Palomar.BinaryFiveCircuit.Model.BinaryAmbientCarrier
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCarrier

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- A first-mode split replaces one term by two fresh terms whose first factors
sum to the original and whose other factors are unchanged. -/
def GeneratedFirstSplit
    (source outputLeft outputRight : Carrier U V W) (D E : State U V W) : Prop :=
  source ∈ D ∧ outputLeft ≠ outputRight ∧
  outputLeft ∉ D.erase source ∧ outputRight ∉ D.erase source ∧
  source.1.1 = outputLeft.1.1 + outputRight.1.1 ∧
  outputLeft.2.1.1 = source.2.1.1 ∧ outputRight.2.1.1 = source.2.1.1 ∧
  outputLeft.2.2.1 = source.2.2.1 ∧ outputRight.2.2.1 = source.2.2.1 ∧
  E = insert outputLeft (insert outputRight (D.erase source))

/-- A third-mode flip is the displayed binary shear on two terms sharing their
third factor, with exact finite-set replacement. -/
def SourceThirdFlip
    (sourceLeft sourceRight targetLeft targetRight : Carrier U V W)
    (D E : State U V W) : Prop :=
  sourceLeft ∈ D ∧ sourceRight ∈ D ∧ sourceLeft ≠ sourceRight ∧
  targetLeft ∉ (D.erase sourceLeft).erase sourceRight ∧
  targetRight ∉ (D.erase sourceLeft).erase sourceRight ∧ targetLeft ≠ targetRight ∧
  sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
  targetLeft.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
  targetLeft.2.1.1 = sourceLeft.2.1.1 ∧ targetLeft.2.2.1 = sourceLeft.2.2.1 ∧
  targetRight.1.1 = sourceRight.1.1 ∧
  targetRight.2.1.1 = sourceRight.2.1.1 - sourceLeft.2.1.1 ∧
  targetRight.2.2.1 = sourceLeft.2.2.1 ∧
  E = insert targetLeft (insert targetRight ((D.erase sourceLeft).erase sourceRight))

/-- A directed reduction merges two terms sharing their second and third
factors, adding their first factors. -/
def DirectedNarrowPairReduction
    (sourceLeft sourceRight target : Carrier U V W) (D E : State U V W) : Prop :=
  sourceLeft ∈ D ∧ sourceRight ∈ D ∧ sourceLeft ≠ sourceRight ∧
  target ∉ (D.erase sourceLeft).erase sourceRight ∧
  sourceRight.2.1.1 = sourceLeft.2.1.1 ∧
  sourceRight.2.2.1 = sourceLeft.2.2.1 ∧
  target.1.1 = sourceLeft.1.1 + sourceRight.1.1 ∧
  target.2.1.1 = sourceLeft.2.1.1 ∧ target.2.2.1 = sourceLeft.2.2.1 ∧
  E = insert target ((D.erase sourceLeft).erase sourceRight)

/-- The three directed intrinsic move forms in one ordered choice of modes. -/
inductive Move : State U V W → State U V W → Prop
  | generatedFirstSplit {source outputLeft outputRight : Carrier U V W} {D E} :
      GeneratedFirstSplit source outputLeft outputRight D E → Move D E
  | sourceThirdFlip {sourceLeft sourceRight targetLeft targetRight : Carrier U V W} {D E} :
      SourceThirdFlip sourceLeft sourceRight targetLeft targetRight D E → Move D E
  | directedNarrowPairReduction {sourceLeft sourceRight target : Carrier U V W} {D E} :
      DirectedNarrowPairReduction sourceLeft sourceRight target D E → Move D E

/-- Reorder a `(W,U,V)` term into `(U,V,W)`. -/
def permuteBCATerm (t : Carrier W U V) : Carrier U V W := (t.2.1, t.2.2, t.1)
/-- Reorder a `(V,W,U)` term into `(U,V,W)`. -/
def permuteCABTerm (t : Carrier V W U) : Carrier U V W := (t.2.2, t.1, t.2.1)
/-- Reorder a `(U,W,V)` term into `(U,V,W)`. -/
def permuteACBTerm (t : Carrier U W V) : Carrier U V W := (t.1, t.2.2, t.2.1)
/-- Reorder a `(W,V,U)` term into `(U,V,W)`. -/
def permuteCBATerm (t : Carrier W V U) : Carrier U V W := (t.2.2, t.2.1, t.1)
/-- Reorder a `(V,U,W)` term into `(U,V,W)`. -/
def permuteBACTerm (t : Carrier V U W) : Carrier U V W := (t.2.1, t.1, t.2.2)

/-- Reorder a `(W,U,V)` state into `(U,V,W)`. -/
def permuteBCAState (D : State W U V) : State U V W := D.image permuteBCATerm
/-- Reorder a `(V,W,U)` state into `(U,V,W)`. -/
def permuteCABState (D : State V W U) : State U V W := D.image permuteCABTerm
/-- Reorder a `(U,W,V)` state into `(U,V,W)`. -/
def permuteACBState (D : State U W V) : State U V W := D.image permuteACBTerm
/-- Reorder a `(W,V,U)` state into `(U,V,W)`. -/
def permuteCBAState (D : State W V U) : State U V W := D.image permuteCBATerm
/-- Reorder a `(V,U,W)` state into `(U,V,W)`. -/
def permuteBACState (D : State V U W) : State U V W := D.image permuteBACTerm

/-- An intrinsic move in any simultaneous permutation of the three factor modes. -/
inductive AllModeMove : State U V W → State U V W → Prop
  | abc {D E} : Move D E → AllModeMove D E
  | bca {D₀ E₀ : State W U V} {D E} : Move D₀ E₀ →
      D = permuteBCAState D₀ → E = permuteBCAState E₀ → AllModeMove D E
  | cab {D₀ E₀ : State V W U} {D E} : Move D₀ E₀ →
      D = permuteCABState D₀ → E = permuteCABState E₀ → AllModeMove D E
  | acb {D₀ E₀ : State U W V} {D E} : Move D₀ E₀ →
      D = permuteACBState D₀ → E = permuteACBState E₀ → AllModeMove D E
  | cba {D₀ E₀ : State W V U} {D E} : Move D₀ E₀ →
      D = permuteCBAState D₀ → E = permuteCBAState E₀ → AllModeMove D E
  | bac {D₀ E₀ : State V U W} {D E} : Move D₀ E₀ →
      D = permuteBACState D₀ → E = permuteBACState E₀ → AllModeMove D E

example (source outputLeft outputRight : Carrier U V W) (D E : State U V W) :
    GeneratedFirstSplit source outputLeft outputRight D E →
      source ∈ D := fun h => h.1

example (sourceLeft sourceRight target : Carrier U V W) (D E : State U V W) :
    DirectedNarrowPairReduction sourceLeft sourceRight target D E →
      sourceLeft ∈ D := fun h => h.1

example (t : Carrier W U V) : (permuteBCATerm t).1 = t.2.1 := rfl
example (t : Carrier V W U) : permuteCABTerm t = (t.2.2, t.1, t.2.1) := rfl
example (t : Carrier U W V) : permuteACBTerm t = (t.1, t.2.2, t.2.1) := rfl
example (t : Carrier W V U) : permuteCBATerm t = (t.2.2, t.2.1, t.1) := rfl
example (t : Carrier V U W) : permuteBACTerm t = (t.2.1, t.1, t.2.2) := rfl
example (D : State W U V) : permuteBCAState D = D.image permuteBCATerm := rfl
example (D : State V W U) : permuteCABState D = D.image permuteCABTerm := rfl
example (D : State U W V) : permuteACBState D = D.image permuteACBTerm := rfl
example (D : State W V U) : permuteCBAState D = D.image permuteCBATerm := rfl
example (D : State V U W) : permuteBACState D = D.image permuteBACTerm := rfl

end Palomar.BinaryFiveCircuit.Model.BinaryAmbientMoves

namespace Palomar.BinaryFiveCircuit.Model.NormalizedBinaryProfileOrientation

/-- The four unordered exact factor-span profiles of binary five-circuits. -/
inductive CanonicalProfileFamily
  | family221 | family411 | family321 | family222
  deriving DecidableEq

end Palomar.BinaryFiveCircuit.Model.NormalizedBinaryProfileOrientation

namespace Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCoverageCompiler

open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryProfileOrientation

/-- The row-index type for each canonical family: `3 + 1 + 6 + 3 = 13`. -/
def FamilyRowIndex : CanonicalProfileFamily → Type
  | .family221 => Fin 3
  | .family411 => Fin 1
  | .family321 => Fin 6
  | .family222 => Fin 3

example : Nonempty (FamilyRowIndex .family411) := by
  change Nonempty (Fin 1)
  exact ⟨0⟩

end Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCoverageCompiler

namespace Palomar.BinaryFiveCircuit.Model.NormalizedBinaryOrbitClassification

open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCoverageCompiler

/-- A canonical family together with one of its thirteen total orbit rows. -/
def OrbitLabel := Sigma FamilyRowIndex

example : Nonempty OrbitLabel := by
  refine ⟨⟨.family221, ?_⟩⟩
  change Fin 3
  exact 0

end Palomar.BinaryFiveCircuit.Model.NormalizedBinaryOrbitClassification

namespace Palomar.BinaryFiveCircuit.Model.BinaryFiveCircuitCompiler

open Palomar.BinaryFiveCircuit.Model.BinaryAmbientCarrier
open Palomar.BinaryFiveCircuit.Model.BinaryCircuit
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCarrier
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCoverageCompiler
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryOrbitClassification
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryProfileOrientation

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Two distinct terms are adjacent when at least two corresponding factors agree. -/
def AmbientPairAdjacent (x y : Carrier U V W) : Prop :=
  x ≠ y ∧ ((x.1 = y.1 ∧ x.2.1 = y.2.1) ∨
    (x.1 = y.1 ∧ x.2.2 = y.2.2) ∨
    (x.2.1 = y.2.1 ∧ x.2.2 = y.2.2))

/-- Pair adjacency is decidable from equality in the three ambient factors. -/
instance ambientPairAdjacentDecidable (x y : Carrier U V W) :
    Decidable (AmbientPairAdjacent x y) := by
  unfold AmbientPairAdjacent
  infer_instance

/-- The number of ordered adjacent pairs from one state to another. -/
def ambientCrossCount (A B : State U V W) : ℕ :=
  ((A ×ˢ B).filter fun xy : Carrier U V W × Carrier U V W =>
    AmbientPairAdjacent xy.1 xy.2).card

/-- The internal-right and left-to-right pair-agreement statistics. -/
def ambientRelationInvariant (A B : State U V W) : ℕ × ℕ :=
  (ambientCrossCount B B, ambientCrossCount A B)

/-- The unordered factor dimensions attached to a canonical family. -/
def familyDimensions : CanonicalProfileFamily → List ℕ
  | .family221 => [2, 2, 1]
  | .family411 => [4, 1, 1]
  | .family321 => [3, 2, 1]
  | .family222 => [2, 2, 2]

/-- The complete pair-agreement invariant attached to each selected orbit row. -/
def selectedInvariant : OrbitLabel → ℕ × ℕ
  | ⟨.family221, i⟩ => ([(0, 4), (2, 2), (4, 2)].get i)
  | ⟨.family411, i⟩ => ([(6, 6)].get i)
  | ⟨.family321, i⟩ => ([(6, 0), (2, 2), (2, 0), (2, 3), (2, 1), (0, 2)].get i)
  | ⟨.family222, i⟩ => ([(2, 0), (2, 1), (0, 2)].get i)

example (x : Carrier U V W) : ¬ AmbientPairAdjacent x x := by simp [AmbientPairAdjacent]
example : ambientCrossCount (∅ : State U V W) ∅ = 0 := by simp [ambientCrossCount]
example : ambientRelationInvariant (∅ : State U V W) ∅ = (0, 0) := by
  simp [ambientRelationInvariant, ambientCrossCount]
example : familyDimensions .family321 = [3, 2, 1] := rfl
example : selectedInvariant
    (⟨.family221, (by change Fin 3; exact 0)⟩ : OrbitLabel) = (0, 4) := rfl

/-- Orbit membership characterized by the label's unordered exact factor-span
dimensions and its two pair-agreement counts. On disjoint equal-evaluation
`2/3` endpoints in finite-dimensional ambients, `Solution.lean` proves this is
equivalent to existence of an exact-span presentation and an oriented
factorwise-GL action witness from the label's selected row. -/
def AmbientInOrbit (label : OrbitLabel) (A B : State U V W) : Prop :=
  List.Perm
      [Module.finrank F2 (firstSpan (A ∪ B)),
        Module.finrank F2 (secondSpan (A ∪ B)),
        Module.finrank F2 (thirdSpan (A ∪ B))]
      (familyDimensions label.1) ∧
    ambientRelationInvariant A B = selectedInvariant label

/-- A state is confined when each projected factor span lies in that of `K`. -/
def AmbientFactorSpanConfined (K X : State U V W) : Prop :=
  firstSpan X ≤ firstSpan K ∧ secondSpan X ≤ secondSpan K ∧ thirdSpan X ≤ thirdSpan K

/-- A path is confined when every visited state's three factor spans lie in
those generated by the designated ambient state. -/
def AmbientPathFactorSpanConfined
    {R : State U V W → State U V W → Prop} {D E : State U V W}
    (path : MovePath R D E) (K : State U V W) : Prop :=
  ∀ X, PathVertex path X → AmbientFactorSpanConfined K X

example (label : OrbitLabel) (A B : State U V W) :
    AmbientInOrbit label A B ↔
      List.Perm
        [Module.finrank F2 (firstSpan (A ∪ B)),
          Module.finrank F2 (secondSpan (A ∪ B)),
          Module.finrank F2 (thirdSpan (A ∪ B))]
        (familyDimensions label.1) ∧
      ambientRelationInvariant A B = selectedInvariant label := Iff.rfl

example (D : State U V W) : AmbientFactorSpanConfined D D :=
  ⟨le_rfl, le_rfl, le_rfl⟩

example (D : State U V W) :
    AmbientPathFactorSpanConfined
      (MovePath.singleton D : MovePath
        (Palomar.BinaryFiveCircuit.Model.BinaryAmbientMoves.AllModeMove
          (U := U) (V := V) (W := W)) D D) D := by
  intro X hX
  have hXD : X = D := by
    simpa [PathVertex, MovePath.vertices] using hX
  subst X
  exact ⟨le_rfl, le_rfl, le_rfl⟩

end Palomar.BinaryFiveCircuit.Model.BinaryFiveCircuitCompiler

namespace Palomar.BinaryFiveCircuit

open Model.BinaryAmbientCarrier Model.NormalizedBinaryCarrier
open scoped TensorProduct

/-- All four endpoint hypotheses hold jointly in the concrete ambient space
`F2^4 × F2 × F2`: the four basis vectors and their sum give five distinct terms. -/
theorem hypotheses_satisfiable : ∃ A B : State (Fin 4 → F2) F2 F2,
    A.card = 2 ∧ B.card = 3 ∧ Disjoint A B ∧
      stateEvaluation A = stateEvaluation B := by
  let u0 : Fin 4 → F2 := ![1, 0, 0, 0]
  let u1 : Fin 4 → F2 := ![0, 1, 0, 0]
  let u2 : Fin 4 → F2 := ![0, 0, 1, 0]
  let u3 : Fin 4 → F2 := ![0, 0, 0, 1]
  let u4 : Fin 4 → F2 := ![1, 1, 1, 1]
  let t0 : Carrier (Fin 4 → F2) F2 F2 :=
    (⟨u0, by decide⟩, ⟨1, one_ne_zero⟩, ⟨1, one_ne_zero⟩)
  let t1 : Carrier (Fin 4 → F2) F2 F2 :=
    (⟨u1, by decide⟩, ⟨1, one_ne_zero⟩, ⟨1, one_ne_zero⟩)
  let t2 : Carrier (Fin 4 → F2) F2 F2 :=
    (⟨u2, by decide⟩, ⟨1, one_ne_zero⟩, ⟨1, one_ne_zero⟩)
  let t3 : Carrier (Fin 4 → F2) F2 F2 :=
    (⟨u3, by decide⟩, ⟨1, one_ne_zero⟩, ⟨1, one_ne_zero⟩)
  let t4 : Carrier (Fin 4 → F2) F2 F2 :=
    (⟨u4, by decide⟩, ⟨1, one_ne_zero⟩, ⟨1, one_ne_zero⟩)
  let A : State (Fin 4 → F2) F2 F2 := {t0, t1}
  let B : State (Fin 4 → F2) F2 F2 := {t2, t3, t4}
  refine ⟨A, B, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · have hu : u0 + u1 = u2 + (u3 + u4) := by decide
    calc
      stateEvaluation A = tensorEvaluation t0 + tensorEvaluation t1 := by
        simp [A, stateEvaluation, t0, t1, u0, u1]
      _ = tensorEvaluation t2 + (tensorEvaluation t3 + tensorEvaluation t4) := by
        change u0 ⊗ₜ[F2] ((1 : F2) ⊗ₜ[F2] (1 : F2)) +
          u1 ⊗ₜ[F2] ((1 : F2) ⊗ₜ[F2] (1 : F2)) =
          u2 ⊗ₜ[F2] ((1 : F2) ⊗ₜ[F2] (1 : F2)) +
          (u3 ⊗ₜ[F2] ((1 : F2) ⊗ₜ[F2] (1 : F2)) +
            u4 ⊗ₜ[F2] ((1 : F2) ⊗ₜ[F2] (1 : F2)))
        simpa only [TensorProduct.add_tmul] using
          congrArg (fun x => x ⊗ₜ[F2] ((1 : F2) ⊗ₜ[F2] (1 : F2))) hu
      _ = stateEvaluation B := by
        simp [B, stateEvaluation, t2, t3, t4, u2, u3, u4]

#check @hypotheses_satisfiable

end Palomar.BinaryFiveCircuit

namespace Palomar.BinaryFiveCircuit.Bridge

open Model.BinaryAmbientCarrier Model.BinaryCircuit Model.BinaryFiveCircuitCompiler
open Model.NormalizedBinaryCarrier Model.NormalizedBinaryOrbitClassification
open Model.NormalizedBinaryProfileOrientation

/-- Identify the independent four-family type with the source family type. -/
def familyEquiv : CanonicalProfileFamily ≃
    BilinearComplexity.NormalizedBinaryProfileOrientation.CanonicalProfileFamily where
  toFun
    | .family221 => .family221
    | .family411 => .family411
    | .family321 => .family321
    | .family222 => .family222
  invFun
    | .family221 => .family221
    | .family411 => .family411
    | .family321 => .family321
    | .family222 => .family222
  left_inv f := by cases f <;> rfl
  right_inv f := by cases f <;> rfl

example : familyEquiv .family221 = .family221 := rfl

/-- Identify independent labels with the source's same thirteen family/row labels. -/
def labelEquiv : OrbitLabel ≃
    BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel where
  toFun
    | ⟨.family221, i⟩ => ⟨.family221, i⟩
    | ⟨.family411, i⟩ => ⟨.family411, i⟩
    | ⟨.family321, i⟩ => ⟨.family321, i⟩
    | ⟨.family222, i⟩ => ⟨.family222, i⟩
  invFun
    | ⟨.family221, i⟩ => ⟨.family221, i⟩
    | ⟨.family411, i⟩ => ⟨.family411, i⟩
    | ⟨.family321, i⟩ => ⟨.family321, i⟩
    | ⟨.family222, i⟩ => ⟨.family222, i⟩
  left_inv l := by rcases l with ⟨f, i⟩; cases f <;> rfl
  right_inv l := by rcases l with ⟨f, i⟩; cases f <;> rfl

example : labelEquiv (⟨.family221, (0 : Fin 3)⟩ : OrbitLabel) =
    ⟨.family221, (0 : Fin 3)⟩ := rfl

/-- The label equivalence preserves its family component. -/
theorem labelEquiv_family (l : OrbitLabel) : (labelEquiv l).1 = familyEquiv l.1 := by
  rcases l with ⟨f, i⟩
  cases f <;> rfl

/-- The displayed family dimensions are the source canonical dimensions. -/
theorem familyDimensions_source (f : CanonicalProfileFamily) :
    familyDimensions f = [(familyEquiv f).profile.first,
      (familyEquiv f).profile.second, (familyEquiv f).profile.third] := by
  cases f <;> rfl

/-- The literal row table equals the source's kernel-checked semantic row counts. -/
theorem selectedInvariant_source (l : OrbitLabel) : selectedInvariant l =
    BilinearComplexity.NormalizedBinaryOrbitInvariants.relationInvariant
      (labelEquiv l).selectedEndpoints := by
  rcases l with ⟨f, i⟩
  cases f with
  | family221 =>
    change Fin 3 at i
    have h := BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows_eq.1
    have hi := congrArg (fun xs : List (ℕ × ℕ) => xs[i.val]?) h
    apply Option.some.inj
    fin_cases i <;> simpa [BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows,
      selectedInvariant, labelEquiv, BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel.selectedEndpoints,
      ] using hi.symm
  | family411 =>
    change Fin 1 at i
    have h := BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows_eq.2.1
    have hi := congrArg (fun xs : List (ℕ × ℕ) => xs[i.val]?) h
    apply Option.some.inj
    fin_cases i
    simpa [BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows,
      selectedInvariant, labelEquiv,
      BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel.selectedEndpoints] using hi.symm
  | family321 =>
    change Fin 6 at i
    have h := BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows_eq.2.2.1
    have hi := congrArg (fun xs : List (ℕ × ℕ) => xs[i.val]?) h
    apply Option.some.inj
    fin_cases i <;> simpa [BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows,
      selectedInvariant, labelEquiv, BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel.selectedEndpoints,
      ] using hi.symm
  | family222 =>
    change Fin 3 at i
    have h := BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows_eq.2.2.2
    have hi := congrArg (fun xs : List (ℕ × ℕ) => xs[i.val]?) h
    apply Option.some.inj
    fin_cases i <;> simpa [BilinearComplexity.NormalizedBinaryOrbitInvariants.actualRows,
      selectedInvariant, labelEquiv, BilinearComplexity.NormalizedBinaryOrbitClassification.OrbitLabel.selectedEndpoints,
      ] using hi.symm

universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- The independent ordered moves are exactly the source's intrinsic algebraic laws. -/
theorem move_iff {D E : State U V W} :
    Model.BinaryAmbientMoves.Move D E ↔ BilinearComplexity.BinaryAmbientMoves.Move D E := by
  constructor <;> intro h <;> cases h with
  | generatedFirstSplit h => exact .generatedFirstSplit h
  | sourceThirdFlip h => exact .sourceThirdFlip h
  | directedNarrowPairReduction h => exact .directedNarrowPairReduction h

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- The independent six-mode move relation agrees with the source relation. -/
theorem allModeMove_iff {D E : State U V W} :
    Model.BinaryAmbientMoves.AllModeMove D E ↔
      BilinearComplexity.BinaryAmbientMoves.AllModeMove D E := by
  constructor
  · intro h
    cases h with
    | abc h => exact .abc (move_iff.mp h)
    | bca h hD hE => exact .bca (move_iff.mp h) hD hE
    | cab h hD hE => exact .cab (move_iff.mp h) hD hE
    | acb h hD hE => exact .acb (move_iff.mp h) hD hE
    | cba h hD hE => exact .cba (move_iff.mp h) hD hE
    | bac h hD hE => exact .bac (move_iff.mp h) hD hE
  · intro h
    cases h with
    | abc h => exact .abc (move_iff.mpr h)
    | bca h hD hE => exact .bca (move_iff.mpr h) hD hE
    | cab h hD hE => exact .cab (move_iff.mpr h) hD hE
    | acb h hD hE => exact .acb (move_iff.mpr h) hD hE
    | cba h hD hE => exact .cba (move_iff.mpr h) hD hE
    | bac h hD hE => exact .bac (move_iff.mpr h) hD hE

#check @labelEquiv_family
#check @familyDimensions_source
#check @selectedInvariant_source
#check @move_iff
#check @allModeMove_iff

end Palomar.BinaryFiveCircuit.Bridge

namespace Palomar.BinaryFiveCircuit.Bridge

open Model.BinaryAmbientCarrier Model.BinaryCircuit Model.BinaryFiveCircuitCompiler
open Model.NormalizedBinaryCarrier Model.NormalizedBinaryOrbitClassification
open Model.NormalizedBinaryProfileOrientation
open BilinearComplexity.BinaryAmbientMoveTransport

universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Translate source paths edge by edge, without changing any state. -/
def pathFromSource : {D E : State U V W} →
    BilinearComplexity.BinaryCircuit.MovePath
      BilinearComplexity.BinaryAmbientMoves.AllModeMove D E →
    MovePath Model.BinaryAmbientMoves.AllModeMove D E
  | _, _, .singleton X => .singleton X
  | _, _, .snoc p h => .snoc (pathFromSource p) (allModeMove_iff.mpr h)

example (D : State U V W) : pathFromSource
    (BilinearComplexity.BinaryCircuit.MovePath.singleton D :
      BilinearComplexity.BinaryCircuit.MovePath
        BilinearComplexity.BinaryAmbientMoves.AllModeMove D D) = .singleton D := by
  simp only [pathFromSource]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Path translation preserves the exact number of edges. -/
theorem pathFromSource_length {D E : State U V W}
    (p : BilinearComplexity.BinaryCircuit.MovePath
      BilinearComplexity.BinaryAmbientMoves.AllModeMove D E) :
    (pathFromSource p).length = p.length := by
  induction p with
  | singleton => simp only [pathFromSource, MovePath.length,
      BilinearComplexity.BinaryCircuit.MovePath.length]
  | snoc p h ih => simp only [pathFromSource, MovePath.length,
      BilinearComplexity.BinaryCircuit.MovePath.length, ih]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Path translation preserves the exact maximum visited cardinality. -/
theorem pathFromSource_altitude {D E : State U V W}
    (p : BilinearComplexity.BinaryCircuit.MovePath
      BilinearComplexity.BinaryAmbientMoves.AllModeMove D E) :
    (pathFromSource p).altitude = p.altitude := by
  induction p with
  | singleton => simp only [pathFromSource, MovePath.altitude,
      BilinearComplexity.BinaryCircuit.MovePath.altitude]
  | snoc p h ih => simp only [pathFromSource, MovePath.altitude,
      BilinearComplexity.BinaryCircuit.MovePath.altitude, ih]

omit [Module F2 U] [Module F2 V] [Module F2 W] in
/-- Path translation preserves the complete ordered list of vertices. -/
theorem pathFromSource_vertices {D E : State U V W}
    (p : BilinearComplexity.BinaryCircuit.MovePath
      BilinearComplexity.BinaryAmbientMoves.AllModeMove D E) :
    (pathFromSource p).vertices = p.vertices := by
  induction p with
  | singleton => simp only [pathFromSource, MovePath.vertices,
      BilinearComplexity.BinaryCircuit.MovePath.vertices]
  | snoc p h ih => simp only [pathFromSource, MovePath.vertices,
      BilinearComplexity.BinaryCircuit.MovePath.vertices, ih]

/-- Span confinement is reflected and preserved by the unchanged vertices. -/
theorem pathFromSource_confined {D E : State U V W}
    (p : BilinearComplexity.BinaryCircuit.MovePath
      BilinearComplexity.BinaryAmbientMoves.AllModeMove D E) (K : State U V W) :
    AmbientPathFactorSpanConfined (pathFromSource p) K ↔
      BilinearComplexity.BinaryFiveCircuitCompiler.AmbientPathFactorSpanConfined p K := by
  unfold AmbientPathFactorSpanConfined PathVertex
  rw [pathFromSource_vertices]
  rfl

omit [DecidableEq U] [DecidableEq V] [DecidableEq W] in
/-- Injective coordinate embeddings preserve and reflect the pair-adjacency predicate. -/
theorem adjacent_map_iff {p : BilinearComplexity.NormalizedBinaryCarrier.Profile}
    (f : CoordinateEmbedding p U V W)
    (x y : BilinearComplexity.NormalizedBinaryCarrier.Carrier p) :
    AmbientPairAdjacent (mapTerm f x) (mapTerm f y) ↔
      BilinearComplexity.NormalizedBinaryOrbitInvariants.PairAdjacent x y := by
  have hf : Function.Injective (mapNonzeroVector f.first f.first_injective) := by
    intro a b h
    exact Subtype.ext (f.first_injective (congrArg Subtype.val h))
  have hs : Function.Injective (mapNonzeroVector f.second f.second_injective) := by
    intro a b h
    exact Subtype.ext (f.second_injective (congrArg Subtype.val h))
  have ht : Function.Injective (mapNonzeroVector f.third f.third_injective) := by
    intro a b h
    exact Subtype.ext (f.third_injective (congrArg Subtype.val h))
  change (mapTerm f x ≠ mapTerm f y ∧ _) ↔ (x ≠ y ∧ _)
  apply and_congr
  · exact not_congr (mapTerm_injective f).eq_iff
  · simp only [mapTerm, hf.eq_iff, hs.eq_iff, ht.eq_iff]

/-- Adjacent-pair counts are unchanged by injective coordinate embeddings. -/
theorem crossCount_map {p : BilinearComplexity.NormalizedBinaryCarrier.Profile}
    (f : CoordinateEmbedding p U V W)
    (A B : BilinearComplexity.NormalizedBinaryCarrier.State p) :
    ambientCrossCount (mapState f A) (mapState f B) =
      BilinearComplexity.NormalizedBinaryOrbitInvariants.crossCount A B := by
  classical
  unfold ambientCrossCount BilinearComplexity.NormalizedBinaryOrbitInvariants.crossCount
  apply Eq.symm
  apply Finset.card_bij (fun xy _ => (mapTerm f xy.1, mapTerm f xy.2))
  · intro xy hxy
    rw [Finset.mem_filter] at hxy ⊢
    exact ⟨Finset.mem_product.mpr
      ⟨(mapState_mem f).mpr (Finset.mem_product.mp hxy.1).1,
        (mapState_mem f).mpr (Finset.mem_product.mp hxy.1).2⟩,
      (adjacent_map_iff f xy.1 xy.2).mpr hxy.2⟩
  · intro x hx y hy hmap
    exact Prod.ext (mapTerm_injective f (congrArg Prod.fst hmap))
      (mapTerm_injective f (congrArg Prod.snd hmap))
  · intro xy hxy
    rw [Finset.mem_filter] at hxy
    obtain ⟨x, hxA, hxx⟩ := Finset.mem_image.mp (Finset.mem_product.mp hxy.1).1
    obtain ⟨y, hyB, hyy⟩ := Finset.mem_image.mp (Finset.mem_product.mp hxy.1).2
    have hmap : (mapTerm f x, mapTerm f y) = xy := Prod.ext hxx hyy
    have hadj : BilinearComplexity.NormalizedBinaryOrbitInvariants.PairAdjacent x y := by
      apply (adjacent_map_iff f x y).mp
      rw [hxx, hyy]
      exact hxy.2
    exact ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hxA, hyB⟩, hadj⟩, hmap⟩

/-- Normalizing through any exact-span presentation preserves the two counts. -/
theorem invariant_normalized {A B : State U V W}
    (P : BilinearComplexity.BinaryAmbientNormalization.ExactSpanPresentation A B) :
    ambientRelationInvariant A B =
      BilinearComplexity.NormalizedBinaryOrbitInvariants.relationInvariant
        (BilinearComplexity.BinaryAmbientNormalization.normalizedEndpoints P) := by
  let f := BilinearComplexity.BinaryFiveCircuitCompiler.exactSpanCoordinateEmbedding P
  have hA := BilinearComplexity.BinaryFiveCircuitCompiler.mapState_normalizedLeft P
  have hB := BilinearComplexity.BinaryFiveCircuitCompiler.mapState_normalizedRight P
  have hx := crossCount_map f (BilinearComplexity.BinaryAmbientNormalization.normalizedLeft P)
    (BilinearComplexity.BinaryAmbientNormalization.normalizedRight P)
  have hy := crossCount_map f (BilinearComplexity.BinaryAmbientNormalization.normalizedRight P)
    (BilinearComplexity.BinaryAmbientNormalization.normalizedRight P)
  dsimp only [f] at hx hy
  rw [hA, hB] at hx
  rw [hB] at hy
  exact Prod.ext hy hx

/-- A source mode permutation gives the corresponding permutation of dimension lists. -/
theorem profile_perm (o : BilinearComplexity.Scheme.Action.Orientation)
    (p : BilinearComplexity.NormalizedBinaryCarrier.Profile) :
    List.Perm [p.first, p.second, p.third]
      [(BilinearComplexity.NormalizedBinaryModePermutation.permProfile o p).first,
        (BilinearComplexity.NormalizedBinaryModePermutation.permProfile o p).second,
        (BilinearComplexity.NormalizedBinaryModePermutation.permProfile o p).third] := by
  cases o <;> apply List.perm_iff_count.mpr <;> intro n <;>
    simp only [BilinearComplexity.Scheme.Action.Orientation.firstDim,
      BilinearComplexity.Scheme.Action.Orientation.secondDim,
      BilinearComplexity.Scheme.Action.Orientation.thirdDim,
      List.count_cons, List.count_nil] <;> omega

/-- Every source action-witness orbit has the displayed dimension/count characterization. -/
theorem ambientInOrbit_of_source (l : OrbitLabel) {A B : State U V W}
    (h : BilinearComplexity.BinaryFiveCircuitCompiler.AmbientInOrbit (labelEquiv l) A B) :
    AmbientInOrbit l A B := by
  obtain ⟨P, hP⟩ := h
  have hinv := BilinearComplexity.NormalizedBinaryOrbitClassification.selectedInvariant_eq_of_inOrbit
    (labelEquiv l) _ hP
  refine ⟨?_, (invariant_normalized P).trans (hinv.symm.trans (selectedInvariant_source l).symm)⟩
  obtain ⟨choice, hfamily, hwitness⟩ := hP
  change List.Perm [Module.finrank F2 (BilinearComplexity.BinaryAmbientCarrier.firstSpan (A ∪ B)),
    Module.finrank F2 (BilinearComplexity.BinaryAmbientCarrier.secondSpan (A ∪ B)),
    Module.finrank F2 (BilinearComplexity.BinaryAmbientCarrier.thirdSpan (A ∪ B))] _
  rw [← P.first_eq_finrank, ← P.second_eq_finrank, ← P.third_eq_finrank,
    familyDimensions_source, ← labelEquiv_family, hfamily, ← choice.profile_eq]
  exact profile_perm choice.orientation P.profile

#check @pathFromSource_length
#check @pathFromSource_altitude
#check @pathFromSource_vertices
#check @pathFromSource_confined
#check @adjacent_map_iff
#check @crossCount_map
#check @invariant_normalized
#check @profile_perm
#check @ambientInOrbit_of_source

end Palomar.BinaryFiveCircuit.Bridge
namespace Palomar.BinaryFiveCircuit.Bridge

open Model.BinaryAmbientCarrier Model.BinaryCircuit Model.BinaryFiveCircuitCompiler
open Model.NormalizedBinaryCarrier Model.NormalizedBinaryOrbitClassification
open Model.NormalizedBinaryProfileOrientation

universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module F2 U] [Module F2 V] [Module F2 W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- Distinct labels have different dimension profiles or different within-family counts. -/
theorem invariant_label_unique {A B : State U V W} {l k : OrbitLabel}
    (hl : AmbientInOrbit l A B) (hk : AmbientInOrbit k A B) : l = k := by
  rcases l with ⟨f, i⟩
  rcases k with ⟨g, j⟩
  have hp : List.Perm (familyDimensions f) (familyDimensions g) := hl.1.symm.trans hk.1
  have hfg : f = g := by
    cases f <;> cases g
    all_goals first | rfl | (exfalso; revert hp; decide)
  subst g
  have hinj : ∀ f : CanonicalProfileFamily, Function.Injective
      (fun i : Model.NormalizedBinaryCoverageCompiler.FamilyRowIndex f =>
        selectedInvariant (⟨f, i⟩ : OrbitLabel)) := by
    intro f
    cases f <;> dsimp only [Model.NormalizedBinaryCoverageCompiler.FamilyRowIndex]
    all_goals decide +kernel
  exact congrArg (fun i => (⟨f, i⟩ : OrbitLabel)) ((hinj f) (hl.2.symm.trans hk.2))

/-- On precisely the theorem's ambient domain, the independent characterization
is equivalent to the source's existential exact-span presentation, orientation,
and factorwise-GL action-witness semantics. The reverse implication uses source
coverage, not an assumed certificate or an unproved completeness assertion. -/
theorem ambientInOrbit_iff_source
    [FiniteDimensional F2 U] [FiniteDimensional F2 V] [FiniteDimensional F2 W]
    {A B : State U V W}
    (hA : A.card = 2) (hB : B.card = 3) (hd : Disjoint A B)
    (he : stateEvaluation A = stateEvaluation B) (l : OrbitLabel) :
    AmbientInOrbit l A B ↔
      BilinearComplexity.BinaryFiveCircuitCompiler.AmbientInOrbit (labelEquiv l) A B := by
  constructor
  · intro hl
    obtain ⟨s, hs, _⟩ :=
      (BilinearComplexity.BinaryFiveCircuitTheorem.finiteDimensional_ambient_fiveCircuit_classification
        hA hB hd he).1
    have hm : AmbientInOrbit (labelEquiv.symm s) A B :=
      ambientInOrbit_of_source _ (by simpa only [Equiv.apply_symm_apply] using hs)
    have hls : l = labelEquiv.symm s := invariant_label_unique hl hm
    simpa only [hls, Equiv.apply_symm_apply] using hs
  · exact ambientInOrbit_of_source l

#check @invariant_label_unique
#check @ambientInOrbit_iff_source
#print axioms ambientInOrbit_iff_source

end Palomar.BinaryFiveCircuit.Bridge

namespace Palomar.BinaryFiveCircuit

open Palomar.BinaryFiveCircuit.Model.BinaryAmbientCarrier
open Palomar.BinaryFiveCircuit.Model.BinaryCircuit
open Palomar.BinaryFiveCircuit.Model.BinaryFiveCircuitCompiler
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryCarrier
open Palomar.BinaryFiveCircuit.Model.NormalizedBinaryOrbitClassification

/-- Every finite-dimensional binary ambient disjoint `2/3` equal-evaluation
relation has exactly one semantic orbit label and has forward and reverse
all-mode paths of length at most three and altitude at most four, with every
visited factor confined to the spans generated by the five endpoint terms. -/
theorem finiteDimensional_ambient_fiveCircuit_classification
    {U V W : Type*}
    [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    [FiniteDimensional F2 U] [FiniteDimensional F2 V]
    [FiniteDimensional F2 W]
    {A B : State U V W}
    (hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
    (hEvaluation : stateEvaluation A = stateEvaluation B) :
    (∃! label : OrbitLabel, AmbientInOrbit label A B) ∧
      ∃ forward : MovePath
          (Palomar.BinaryFiveCircuit.Model.BinaryAmbientMoves.AllModeMove
            (U := U) (V := V) (W := W)) A B,
        ∃ reverse : MovePath
            (Palomar.BinaryFiveCircuit.Model.BinaryAmbientMoves.AllModeMove
              (U := U) (V := V) (W := W)) B A,
          forward.length ≤ 3 ∧ reverse.length ≤ 3 ∧
          forward.altitude ≤ 4 ∧ reverse.altitude ≤ 4 ∧
          AmbientPathFactorSpanConfined forward (A ∪ B) ∧
          AmbientPathFactorSpanConfined reverse (A ∪ B) := by
  obtain ⟨⟨s, hs, hunique⟩, forward, reverse, hf, hr, hfa, hra, hfc, hrc⟩ :=
    BilinearComplexity.BinaryFiveCircuitTheorem.finiteDimensional_ambient_fiveCircuit_classification
      hA hB hDisjoint hEvaluation
  have hlabel : AmbientInOrbit (Bridge.labelEquiv.symm s) A B :=
    (Bridge.ambientInOrbit_iff_source hA hB hDisjoint hEvaluation _).mpr
      (by simpa only [Equiv.apply_symm_apply] using hs)
  refine ⟨⟨Bridge.labelEquiv.symm s, hlabel, ?_⟩,
    Bridge.pathFromSource forward, Bridge.pathFromSource reverse, ?_⟩
  · intro k hk
    apply Bridge.labelEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact hunique _ ((Bridge.ambientInOrbit_iff_source hA hB hDisjoint hEvaluation k).mp hk)
  · exact ⟨(Bridge.pathFromSource_length forward).trans_le hf,
      (Bridge.pathFromSource_length reverse).trans_le hr,
      (Bridge.pathFromSource_altitude forward).trans_le hfa,
      (Bridge.pathFromSource_altitude reverse).trans_le hra,
      (Bridge.pathFromSource_confined forward (A ∪ B)).mpr hfc,
      (Bridge.pathFromSource_confined reverse (A ∪ B)).mpr hrc⟩

#check @finiteDimensional_ambient_fiveCircuit_classification

end Palomar.BinaryFiveCircuit

#print axioms Palomar.BinaryFiveCircuit.hypotheses_satisfiable
#print axioms Palomar.BinaryFiveCircuit.finiteDimensional_ambient_fiveCircuit_classification
