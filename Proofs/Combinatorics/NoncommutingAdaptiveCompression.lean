import Combinatorics.NoncommutingSignedCompression

set_option autoImplicit false

namespace NoncommutingAdaptiveCompression

open NoncommutingSignedCompression NoncommutingFiber

/-- The coordinate pair obtained by dropping axis `i`. -/
def pairProjection (i : Fin 3) (p : ℤ × ℤ × ℤ) : ℤ × ℤ :=
  if i = 0 then p.2 else if i = 1 then (p.1,p.2.2) else (p.1,p.2.1)

example : (pairProjection 0 (2,3,4), pairProjection 1 (2,3,4),
    pairProjection 2 (2,3,4)) = ((3,4),(2,4),(2,3)) := by decide

/-- Four cube points with at most three points in each coordinate-pair projection. -/
def Invariant (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  S ⊆ cube ∧ S.card = 4 ∧ ∀ i : Fin 3, (S.image (pairProjection i)).card ≤ 3

instance (S : Finset (ℤ × ℤ × ℤ)) : Decidable (Invariant S) :=
  inferInstanceAs (Decidable (S ⊆ cube ∧ S.card = 4 ∧
    ∀ i : Fin 3, (S.image (pairProjection i)).card ≤ 3))

example : Invariant witness := by decide

private theorem finite_closure :
    ∀ S ∈ cube.powerset, Invariant S →
      ∀ (i : Fin 3) (b : Bool), Invariant (compress i b S) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 4000000 in
      decide

/-- Each actual compression preserves the combined geometric invariant.
The finite proof ranges over every subset of the eight-point cube, not a
preselected reachable family. -/
theorem invariant_compress (S : Finset (ℤ × ℤ × ℤ)) (hS : Invariant S)
    (i : Fin 3) (b : Bool) : Invariant (compress i b S) :=
  finite_closure S (Finset.mem_powerset.mpr hS.1) hS i b

/-- The bit of corner `s` on axis `i`. -/
def bit (s : Bool × Bool × Bool) (i : Fin 3) : Bool :=
  if i = 0 then s.1 else if i = 1 then s.2.1 else s.2.2

example : (bit (true,false,true) 0, bit (true,false,true) 1,
    bit (true,false,true) 2) = (true,false,true) := by decide

private theorem finite_terminal :
    ∀ S ∈ cube.powerset, Invariant S → ∀ s : Bool × Bool × Bool,
      (∀ i : Fin 3, compress i (bit s i) S = S) → S = ball s := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 4000000 in
      decide

/-- Within the invariant, simultaneous compression towards any common corner
forces precisely its radius-one ball. -/
theorem terminal_eq_ball (S : Finset (ℤ × ℤ × ℤ)) (hS : Invariant S)
    (s : Bool × Bool × Bool) (hfixed : ∀ i : Fin 3, compress i (bit s i) S = S) :
    S = ball s :=
  finite_terminal S (Finset.mem_powerset.mpr hS.1) hS s hfixed

/-- Execute an arbitrary finite list of actual signed axis compressions, in
list order. Axes may repeat and the orientation may change at every step. -/
def chain (actions : List (Fin 3 × Bool)) (S : Finset (ℤ × ℤ × ℤ)) :
    Finset (ℤ × ℤ × ℤ) :=
  actions.foldl (fun T a => compress a.1 a.2 T) S

example (S : Finset (ℤ × ℤ × ℤ)) : chain [] S = S := rfl
example : chain [(0,false),(1,true)] {(1,0,0)} = {(0,1,0)} := by decide

/-- Every finite sequence preserves the invariant, with no restriction on
repeated axes or changing directions. -/
theorem invariant_chain (actions : List (Fin 3 × Bool))
    (S : Finset (ℤ × ℤ × ℤ)) (hS : Invariant S) : Invariant (chain actions S) := by
  induction actions generalizing S with
  | nil => exact hS
  | cons a rest ih =>
    exact ih (compress a.1 a.2 S) (invariant_compress S hS a.1 a.2)

/-- The actual witness satisfies the projection invariant. -/
theorem invariant_witness : Invariant witness := by decide

/-- Every adaptive finite compression endpoint of the witness remains four
cube points whose three pair projections each have cardinality at most three. -/
theorem invariant_endpoint (actions : List (Fin 3 × Bool)) :
    Invariant (chain actions witness) :=
  invariant_chain actions witness invariant_witness

/-- If any finite, arbitrarily chosen sequence terminates simultaneously
compressed towards a common corner, its endpoint is that corner's ball.
Its actual mixed sum has cardinality eighteen and strictly exceeds the
witness's seventeen. No convergence or intermediate monotonicity is asserted. -/
theorem adaptive_terminal_increase (actions : List (Fin 3 × Bool))
    (s : Bool × Bool × Bool)
    (hfixed : ∀ i : Fin 3,
      compress i (bit s i) (chain actions witness) = chain actions witness) :
    chain actions witness = ball s ∧
      (mixedSum (chain actions witness)).card = 18 ∧
      (mixedSum witness).card < (mixedSum (chain actions witness)).card := by
  have heq : chain actions witness = ball s :=
    terminal_eq_ball (chain actions witness) (invariant_endpoint actions) s hfixed
  have hcard : (mixedSum (chain actions witness)).card = 18 := by
    rw [heq, mixedSum_ball_card]
  exact ⟨heq, hcard, by rw [mixedSum_witness_card, hcard]; decide⟩

/-- The empty action list is not terminal at any corner for this witness. -/
theorem empty_not_terminal (s : Bool × Bool × Bool) :
    ¬ (∀ i : Fin 3, compress i (bit s i) (chain [] witness) = chain [] witness) := by
  rcases s with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- A concrete terminal sequence demonstrates joint satisfiability of the
consumer's hypotheses: compress lower on axes zero, one, then two. -/
theorem lower_pass_terminal :
    ∀ i : Fin 3,
      compress i (bit (false,false,false) i)
          (chain [(0,false),(1,false),(2,false)] witness) =
        chain [(0,false),(1,false),(2,false)] witness := by decide

example :
    chain [(0,false),(1,false),(2,false)] witness = ball (false,false,false) ∧
      (mixedSum (chain [(0,false),(1,false),(2,false)] witness)).card = 18 ∧
      (mixedSum witness).card <
        (mixedSum (chain [(0,false),(1,false),(2,false)] witness)).card :=
  adaptive_terminal_increase _ _ lower_pass_terminal

end NoncommutingAdaptiveCompression
