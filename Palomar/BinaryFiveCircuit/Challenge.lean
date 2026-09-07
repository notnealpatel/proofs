import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Binary five-circuit ambient classification challenge

This file gives a project-independent model of the headline.  States are finite
sets of triples of nonzero factors over `𝔽₂`, evaluation is the sum of their
nested pure tensors, and paths consist of the three intrinsic split/flip/reduce
moves in any of the six mode orders. The independent model lives under
`Palomar.BinaryFiveCircuit.Model`, not under the imported source's namespaces.
Its thirteen labels are characterized by factor-span dimensions and two
pair-agreement counts. `Solution.lean` repeats these definitions verbatim and
proves their equivalence to the source's existential exact-span presentation,
mode-orientation, and factorwise-GL action-witness semantics on exactly the
headline domain. This completeness is proved, not assumed.

A concrete `F2^4 × F2 × F2` example jointly satisfies all endpoint hypotheses.
The sole proof hole is the selected ambient classification theorem.
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
  sorry

#check @finiteDimensional_ambient_fiveCircuit_classification

end Palomar.BinaryFiveCircuit
