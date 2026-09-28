/-
The released side-29 triangle-certificate body visitor.  This module composes the already verified
scheduler and one-record decoder into the depth-first traversal of the certificate body.  It says
nothing about headers, roots, EOF acceptance, orbit coverage, or restricted-growth completeness.
-/

import Erdos.Erdos64.TriangleRecordAction

set_option autoImplicit false

namespace Erdos64

/-- The six counters maintained by the released body visitor.  Expanded states are deliberately
not stored: as in the released checker they are derived as `states - 1`. -/
structure VisitCounts where
  /-- Recursive states entered. -/
  states : Nat
  /-- Scheduled candidates attempted. -/
  attempted : Nat
  /-- Candidates rejected structurally. -/
  structural : Nat
  /-- Checked C8 rejections. -/
  c8 : Nat
  /-- Checked C16 rejections. -/
  c16 : Nat
  /-- Completed configurations encountered. -/
  completions : Nat
  deriving DecidableEq, Repr

/-- Componentwise addition of visitor counters. -/
def VisitCounts.add (x y : VisitCounts) : VisitCounts :=
  ⟨x.states + y.states, x.attempted + y.attempted, x.structural + y.structural,
    x.c8 + y.c8, x.c16 + y.c16, x.completions + y.completions⟩

/-- The zero visitor counters. -/
def VisitCounts.zero : VisitCounts := ⟨0, 0, 0, 0, 0, 0⟩

/-- Increment the entered-state counter exactly once. -/
def VisitCounts.bumpState (x : VisitCounts) : VisitCounts := { x with states := x.states + 1 }

/-- Increment the attempted-candidate counter exactly once. -/
def VisitCounts.bumpAttempted (x : VisitCounts) : VisitCounts :=
  { x with attempted := x.attempted + 1 }

/-- Increment the structural-rejection counter exactly once. -/
def VisitCounts.bumpStructural (x : VisitCounts) : VisitCounts :=
  { x with structural := x.structural + 1 }

/-- Increment the C8-rejection counter exactly once. -/
def VisitCounts.bumpC8 (x : VisitCounts) : VisitCounts := { x with c8 := x.c8 + 1 }

/-- Increment the C16-rejection counter exactly once. -/
def VisitCounts.bumpC16 (x : VisitCounts) : VisitCounts := { x with c16 := x.c16 + 1 }

/-- Increment the completed-configuration counter exactly once. -/
def VisitCounts.bumpCompletion (x : VisitCounts) : VisitCounts :=
  { x with completions := x.completions + 1 }

/-- Expanded states, derived rather than stored. -/
def VisitCounts.expanded (x : VisitCounts) : Nat := x.states - 1

example : VisitCounts.zero.add ⟨1, 2, 3, 4, 5, 6⟩ = ⟨1, 2, 3, 4, 5, 6⟩ := rfl
example : VisitCounts.zero.bumpState.bumpAttempted.bumpStructural = ⟨1, 1, 1, 0, 0, 0⟩ := rfl
example : (⟨4, 0, 0, 0, 0, 0⟩ : VisitCounts).expanded = 3 := rfl

/-- The accumulated counters and exact byte cursor returned by a traversal. -/
structure VisitSummary where
  /-- Accumulated body counters. -/
  counts : VisitCounts
  /-- Exact cursor at success or first error. -/
  cursor : ByteCursor
  deriving DecidableEq, Repr

/-- Body-visitor failures.  Completion records both the block count and introduced-point count. -/
inductive VisitError
  | decode (reason : DecodeError)
  | completion (blocks introduced : Nat)
  deriving DecidableEq, Repr

/-- A total body visit returns either success or the first failure, always with exact accounting. -/
inductive VisitResult
  | ok (summary : VisitSummary)
  | error (reason : VisitError) (summary : VisitSummary)
  deriving DecidableEq, Repr

/-- The invariant used by the side-29 traversal. -/
def TraversalInvariant {m : Nat} (s : SearchState m) : Prop := StateInvariant s ∧ m ≤ 29

/-- Ground truth: the released orbit-one root satisfies the traversal invariant. -/
example : TraversalInvariant orbitOneState := ⟨orbitOne_stateInvariant, by decide⟩

/-- All introduced points strictly before a frame's start are already full. -/
def PrefixFull {m : Nat} (s : SearchState m) (start : SearchPoint) : Prop :=
  ∀ q : SearchPoint, q < start → q.val < s.introduced.val → pointDegree s q = 3

/-- Full-prefix validity is decidable because the point type is finite. -/
instance instDecidablePrefixFull {m : Nat} (s : SearchState m) (start : SearchPoint) :
    Decidable (PrefixFull s start) := by
  unfold PrefixFull
  infer_instance

/-- A recursive visitor frame.  The prefix condition justifies never restarting before `start`. -/
structure VisitFrame (m : Nat) where
  /-- Immutable search state at this recursion depth. -/
  state : SearchState m
  /-- State validity and the fixed side-29 block cap. -/
  invariant : TraversalInvariant state
  /-- First point at which the scheduler searches. -/
  start : SearchPoint
  /-- Last attempted pair at `start`, if any. -/
  cursor : SearchCursor
  /-- Points before `start` need not be searched again. -/
  prefixFull : PrefixFull state start

/-- Installing a clean candidate while below the cap preserves the traversal invariant. -/
theorem traversalInvariant_install {m : Nat} {s : SearchState m} {t : SearchBlock}
    (hinv : TraversalInvariant s) (hdisc : CandidateDiscipline s.introduced t)
    (hclean : CleanStructuralOK s t) (hm : m < 29) :
    TraversalInvariant (s.install t hdisc) := by
  exact ⟨stateInvariant_install s t hinv.1 hdisc hclean, by omega⟩

/-- Installing a clean selected-point candidate preserves fullness of every earlier point. -/
theorem prefixFull_install {m : Nat} {s : SearchState m} {start p : SearchPoint}
    {t : SearchBlock} (_hinv : StateInvariant s) (hprefix : PrefixFull s start)
    (hadvance : advancePoint s start = some p) (hdisc : CandidateDiscipline s.introduced t)
    (hclean : CleanStructuralOK s t) : PrefixFull (s.install t hdisc) p := by
  intro q hqp hqintroduced
  have hpintroduced : p.val < s.introduced.val := (advancePoint_spec hadvance).2.1
  have hqpval : q.val < p.val := hqp
  have hqold : q.val < s.introduced.val := lt_trans hqpval hpintroduced
  have hqfull : pointDegree s q = 3 := by
    by_cases hqs : q < start
    · exact hprefix q hqs hqold
    · have hstartq : start ≤ q := le_of_not_gt hqs
      exact advancePoint_skipped hadvance hstartq hqp
  have hqnotmem : q ∉ t.points := by
    intro hmem
    have hqlt : pointDegree s q < 3 := hclean.1 q hmem
    omega
  rw [pointDegree_install s t hdisc q, if_neg hqnotmem]
  exact hqfull

/-- Ground truth for prefix fullness at the orbit-one fixture's start. -/
example : PrefixFull orbitOneState (1 : SearchPoint) := by decide

/-- Process a candidate list from left to right.  The callback is the well-founded recursive
visitor at a strictly smaller outer rank; exposing it makes the immutable-parent continuation and
its exact counter/stream accounting explicit. -/
def visitCandidates (m : Nat) (frame : VisitFrame m) (p : SearchPoint)
    (hadvance : advancePoint frame.state frame.start = some p) (hm : m < 29)
    (c16Enabled : Bool) (todo : List SearchBlock)
    (hall : ∀ t ∈ todo, CandidateDiscipline frame.state.introduced t)
    (counts : VisitCounts) (cursor : ByteCursor)
    (recur : ∀ n : Nat, 29 - n < 29 - m → VisitFrame n → Bool → ByteCursor → VisitResult) :
    VisitResult :=
  match todo with
  | [] => .ok ⟨counts, cursor⟩
  | t :: tail =>
      let hdisc := hall t (by simp)
      let attempted := counts.bumpAttempted
      match decodeCandidate frame.state t frame.invariant.1 hdisc c16Enabled cursor with
      | .error reason next => .error (.decode reason) ⟨attempted, next⟩
      | .ok .structural next =>
          visitCandidates m frame p hadvance hm c16Enabled tail
            (fun u hu => hall u (by simp [hu])) attempted.bumpStructural next recur
      | .ok (.checked (.c8 ids witness)) next =>
          visitCandidates m frame p hadvance hm c16Enabled tail
            (fun u hu => hall u (by simp [hu])) attempted.bumpC8 next recur
      | .ok (.checked (.c16 code ids witness)) next =>
          visitCandidates m frame p hadvance hm c16Enabled tail
            (fun u hu => hall u (by simp [hu])) attempted.bumpC16 next recur
      | .ok (.checked (.expansion clean)) next =>
          let child : VisitFrame (m + 1) :=
            { state := frame.state.install t hdisc
              invariant := traversalInvariant_install frame.invariant hdisc clean hm
              start := p
              cursor := some (t.b, t.c)
              prefixFull := prefixFull_install frame.invariant.1 frame.prefixFull
                hadvance hdisc clean }
          match recur (m + 1) (by omega) child c16Enabled next with
          | .error reason summary =>
              .error reason ⟨attempted.add summary.counts, summary.cursor⟩
          | .ok summary =>
              visitCandidates m frame p hadvance hm c16Enabled tail
                (fun u hu => hall u (by simp [hu])) (attempted.add summary.counts)
                summary.cursor recur
termination_by todo.length

private def visitBody (m : Nat)
    (recur : ∀ n : Nat, 29 - n < 29 - m → VisitFrame n → Bool → ByteCursor → VisitResult)
    (frame : VisitFrame m) (c16Enabled : Bool) (stream : ByteCursor) : VisitResult :=
  let entered := VisitCounts.zero.bumpState
  let schedule := candidateSchedule frame.state frame.start frame.cursor
  match hp : advancePoint frame.state frame.start with
  | none =>
      if m = frame.state.introduced.val then
        .error (.completion m frame.state.introduced.val) ⟨entered.bumpCompletion, stream⟩
      else .ok ⟨entered, stream⟩
  | some p =>
      if hcap : 29 ≤ m then .ok ⟨entered, stream⟩
      else
        have hadvance : advancePoint frame.state frame.start = some p := hp
        visitCandidates m frame p hadvance (by omega) c16Enabled schedule.candidates
          (fun t ht => candidateSchedule_discipline frame.state frame.start frame.cursor ht)
          entered stream recur

private def visitImpl : (m : Nat) → VisitFrame m → Bool → ByteCursor → VisitResult :=
  (measure (fun m : Nat => 29 - m)).wf.fix
    (C := fun m => VisitFrame m → Bool → ByteCursor → VisitResult)
    (fun m recur frame enabled stream => visitBody m recur frame enabled stream)

/-- Execute the released side-29 certificate-body traversal in depth-first candidate order. -/
def visit {m : Nat} (frame : VisitFrame m) (c16Enabled : Bool) (stream : ByteCursor) : VisitResult :=
  visitImpl m frame c16Enabled stream

/-- Unfold one visitor state; recursive calls are precisely at the next block count. -/
theorem visit_eq {m : Nat} (frame : VisitFrame m) (c16Enabled : Bool) (stream : ByteCursor) :
    visit frame c16Enabled stream =
      visitBody m (fun n _h => visitImpl n) frame c16Enabled stream := by
  rw [visit, visitImpl, WellFounded.fix_eq]
  congr 1

/-- Expose one visitor equation without exposing the well-founded implementation. -/
def visitStep {m : Nat} (frame : VisitFrame m) (c16Enabled : Bool)
    (stream : ByteCursor) : VisitResult :=
  visitBody m (fun n _h => visitImpl n) frame c16Enabled stream

/-- The public visitor is extensionally its single-state interface equation. -/
theorem visit_eq_step {m : Nat} (frame : VisitFrame m) (c16Enabled : Bool)
    (stream : ByteCursor) : visit frame c16Enabled stream = visitStep frame c16Enabled stream := by
  exact visit_eq frame c16Enabled stream

/-- Ground truth: the interface is exactly the private one-state equation. -/
example {m : Nat} (frame : VisitFrame m) (enabled : Bool) (stream : ByteCursor) :
    visitStep frame enabled stream =
      visitBody m (fun n _h => visitImpl n) frame enabled stream := rfl

/-- The orbit-one fixture frame begins at point `1` after candidate cursor `(2,4)`. -/
def orbitOneRootFrame : VisitFrame 4 where
  state := orbitOneState
  invariant := ⟨orbitOne_stateInvariant, by decide⟩
  start := 1
  cursor := some (2, 4)
  prefixFull := by decide

/-- Ground truth for the orbit-one frame fields. -/
example : orbitOneRootFrame.state.introduced.val = 7 ∧ orbitOneRootFrame.start = 1 ∧
    orbitOneRootFrame.cursor = some (2, 4) := by decide

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- If no unfinished point remains and blocks equal introduced points, completion takes precedence
(including at the block cap), increments only `states` and `completions`, and consumes no byte. -/
theorem visit_completion_precedes_cap {m : Nat} (frame : VisitFrame m) (enabled : Bool)
    (stream : ByteCursor) (hnone : advancePoint frame.state frame.start = none)
    (hcomplete : m = frame.state.introduced.val) :
    visit frame enabled stream =
      .error (.completion m frame.state.introduced.val) ⟨⟨1, 0, 0, 0, 0, 1⟩, stream⟩ := by
  rw [visit_eq]
  unfold visitBody
  split
  · rename_i hsel
    simp [hcomplete, VisitCounts.zero, VisitCounts.bumpState,
      VisitCounts.bumpCompletion]
  · rename_i p hsel
    rw [hsel] at hnone
    simp at hnone

/-- Defensive interpreter equation for a terminal non-completion. Such a branch is retained to
match the total C++ control flow; this theorem does not assert that its hypotheses are reachable
from a valid traversal frame. -/
theorem visit_defensive_terminal_cursor_unchanged {m : Nat} (frame : VisitFrame m) (enabled : Bool)
    (stream : ByteCursor) (hnone : advancePoint frame.state frame.start = none)
    (hincomplete : m ≠ frame.state.introduced.val) :
    visit frame enabled stream = .ok ⟨⟨1, 0, 0, 0, 0, 0⟩, stream⟩ := by
  rw [visit_eq]
  unfold visitBody
  split
  · rename_i hsel
    simp [hincomplete, VisitCounts.zero, VisitCounts.bumpState]
  · rename_i p hsel
    rw [hsel] at hnone
    simp at hnone

/-- Defensive interpreter equation for a selected state already at the block cap. This branch is
retained to match the total C++ control flow; this theorem does not assert that its hypotheses are
reachable from a valid traversal frame. -/
theorem visit_defensive_cap_cursor_unchanged {m : Nat} (frame : VisitFrame m) (enabled : Bool)
    (stream : ByteCursor) {p : SearchPoint}
    (hpoint : advancePoint frame.state frame.start = some p) (hcap : 29 ≤ m) :
    visit frame enabled stream = .ok ⟨⟨1, 0, 0, 0, 0, 0⟩, stream⟩ := by
  rw [visit_eq]
  unfold visitBody
  split
  · rename_i hsel
    rw [hsel] at hpoint
    simp at hpoint
  · rename_i p' hsel
    simp [hcap, VisitCounts.zero, VisitCounts.bumpState]

/-- The local decoder rejects the scheduled structural fixture `{3,4,6}` without consuming a
byte; the associated local counter updates increment exactly attempted and structural. This is not
a `visitCandidates` execution theorem. -/
theorem orbitOne_structural_decoder_fixture :
    decodeCandidate orbitOneState orbitOneInvalidCandidate orbitOne_stateInvariant
        orbitOneInvalidCandidate_discipline true ⟨[], 0⟩ = .ok .structural ⟨[], 0⟩ ∧
      VisitCounts.zero.bumpAttempted.bumpStructural = ⟨0, 1, 1, 0, 0, 0⟩ := by
  constructor
  · exact decodeCandidate_structural_unchanged orbitOne_stateInvariant
      orbitOneInvalidCandidate_discipline true ⟨[], 0⟩
      orbitOneInvalidCandidate_cppStructurallyInvalid
  · rfl

/-- The official expansion's dependent child frame: same selected point, cursor `(7,8)`. -/
def orbitOneExpansionChild : VisitFrame 5 where
  state := orbitOneState.install orbitOneExpansionCandidate orbitOneExpansion_discipline
  invariant := traversalInvariant_install ⟨orbitOne_stateInvariant, by decide⟩
    orbitOneExpansion_discipline
    (clean_of_structurally_valid orbitOne_stateInvariant orbitOneExpansion_valid) (by decide)
  start := 1
  cursor := some (7, 8)
  prefixFull := prefixFull_install orbitOne_stateInvariant orbitOneRootFrame.prefixFull (by decide)
    orbitOneExpansion_discipline
    (clean_of_structurally_valid orbitOne_stateInvariant orbitOneExpansion_valid)

/-- Local expansion handoff data: decoding consumes its tag, while the separately constructed
five-block child has introduced count nine, the same selected start, and cursor `(7,8)`. This is not
a `visitCandidates` execution theorem. -/
theorem orbitOne_expansion_handoff :
    decodeRecord 4 true ⟨[0x20], 0⟩ =
        .ok (.expansion : WireRecord 4) ⟨[0x20], 1⟩ ∧
      orbitOneExpansionChild.state.introduced.val = 9 ∧
      orbitOneExpansionChild.start = 1 ∧ orbitOneExpansionChild.cursor = some (7, 8) := by
  decide

/-- Expected component-level result data for the first-C8-then-EOF regression fixture. -/
def orbitOneFirstC8ThenEofComponentExpected : VisitResult :=
  .error (.decode (.eof 4)) ⟨⟨1, 2, 0, 1, 0, 0⟩, ⟨officialFirstC8Bytes, 4⟩⟩

example : orbitOneFirstC8ThenEofComponentExpected =
    .error (.decode (.eof 4)) ⟨⟨1, 2, 0, 1, 0, 0⟩, ⟨officialFirstC8Bytes, 4⟩⟩ := rfl

/-- Component-level regression evidence: the orbit-one record decoder consumes the four-byte C8
record, a subsequent byte read fails at EOF position four, and the corresponding local counter
updates have the expected values. This theorem does not claim equality of `visit` or `visitStep`. -/
theorem orbitOne_firstC8_then_eof_equations :
    decodeRecord 4 true ⟨officialFirstC8Bytes, 0⟩ =
        .ok (.c8 orbitOneIds) ⟨officialFirstC8Bytes, 4⟩ ∧
      readByte ⟨officialFirstC8Bytes, 4⟩ =
        .error (.eof 4) ⟨officialFirstC8Bytes, 4⟩ ∧
      VisitCounts.zero.bumpState.bumpAttempted.bumpC8.bumpAttempted =
        ⟨1, 2, 0, 1, 0, 0⟩ := by
  exact ⟨officialFirstC8_decode, by decide, rfl⟩

end Erdos64
