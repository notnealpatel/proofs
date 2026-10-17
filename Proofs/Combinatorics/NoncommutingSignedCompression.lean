import Combinatorics.NoncommutingFiber

set_option autoImplicit false

namespace NoncommutingSignedCompression

open NoncommutingFiber

/-- The four-point binary-cube witness, in integer coordinates. -/
def witness : Finset (ℤ × ℤ × ℤ) :=
  {(0,0,0), (0,0,1), (0,1,1), (1,0,0)}

example : witness.card = 4 := by decide

/-- The actual independent-image mixed sum of the witness has seventeen points. -/
theorem mixedSum_witness_card : (mixedSum witness).card = 17 := by decide

/-- The binary cube, regarded as a finite subset of integer three-space. -/
def cube : Finset (ℤ × ℤ × ℤ) := {0,1} ×ˢ ({0,1} ×ˢ {0,1})

example : cube.card = 8 := by decide

/-- Coordinate number `i`, with the axes numbered zero, one, two. -/
def coord (i : Fin 3) (p : ℤ × ℤ × ℤ) : ℤ :=
  if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2

example : (coord 0 (2,3,4), coord 1 (2,3,4), coord 2 (2,3,4)) = (2,3,4) := by decide

/-- Reflect axis `i` about its binary midpoint; on the cube this interchanges its two levels. -/
def flip (i : Fin 3) (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if i = 0 then (1-p.1,p.2.1,p.2.2)
  else if i = 1 then (p.1,1-p.2.1,p.2.2) else (p.1,p.2.1,1-p.2.2)

example : (flip 0 (0,1,0), flip 1 (0,1,0), flip 2 (0,1,0)) =
    ((1,1,0),(0,0,0),(0,1,1)) := by decide

/-- Binary fiber sorting towards level `b` (`false` means lower, `true` upper).
For a cube subset, the preferred level is occupied when either point of its
axis fiber is occupied, and the other level precisely when both are occupied.
Thus a fiber of size zero, one, or two becomes the corresponding initial or
terminal segment. This formula is only intended as fiber compression on the
binary cube, not on arbitrary integer sets. -/
def compress (i : Fin 3) (b : Bool) (S : Finset (ℤ × ℤ × ℤ)) :
    Finset (ℤ × ℤ × ℤ) :=
  ((S ∪ S.image (flip i)).filter (fun p => coord i p = if b then 1 else 0)) ∪
  ((S ∩ S.image (flip i)).filter (fun p => coord i p = if b then 0 else 1))

example : compress 0 false {(1,0,0)} = {(0,0,0)} := by decide
example : compress 0 true {(0,0,0)} = {(1,0,0)} := by decide
example : compress 0 false {(0,0,0),(1,0,0)} = {(0,0,0),(1,0,0)} := by decide
example : compress 0 true ∅ = ∅ := by decide

/-- The integer corner represented by three orientation bits. -/
def corner (s : Bool × Bool × Bool) : ℤ × ℤ × ℤ :=
  (if s.1 then 1 else 0, if s.2.1 then 1 else 0, if s.2.2 then 1 else 0)

example : corner (true,false,true) = (1,0,1) := rfl

/-- The radius-one Hamming ball consists of its corner and its three single-axis neighbors. -/
def ball (s : Bool × Bool × Bool) : Finset (ℤ × ℤ × ℤ) :=
  {corner s, flip 0 (corner s), flip 1 (corner s), flip 2 (corner s)}

example : ball (false,false,false) = {(0,0,0),(1,0,0),(0,1,0),(0,0,1)} := by decide

/-- Perform the three indicated axis compressions in order, with one fixed orientation. -/
def run (s : Bool × Bool × Bool) (i j k : Fin 3)
    (S : Finset (ℤ × ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  let b := fun a : Fin 3 => if a = 0 then s.1 else if a = 1 then s.2.1 else s.2.2
  compress k (b k) (compress j (b j) (compress i (b i) S))

example : run (false,false,false) 0 1 2 {(1,1,1)} = {(0,0,0)} := by decide

/-- The witness is a four-point subset of the binary cube. -/
theorem witness_domain_card : witness ⊆ cube ∧ witness.card = 4 := by decide

/-- Every fixed orientation and every order using each axis once sends the
same witness to the radius-one Hamming ball about that orientation's corner. -/
theorem run_witness (s : Bool × Bool × Bool) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    run s i j k witness = ball s := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [ne_eq, not_true_eq_false] at hij hik hjk
  all_goals
    rcases s with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;> decide

/-- All eight radius-one corner balls have actual mixed-sum cardinality eighteen. -/
theorem mixedSum_ball_card (s : Bool × Bool × Bool) : (mixedSum (ball s)).card = 18 := by
  rcases s with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- Reflecting the same axis twice restores every integer point. -/
theorem flip_flip (i : Fin 3) (p : ℤ × ℤ × ℤ) : flip i (flip i p) = p := by
  rcases p with ⟨x,y,z⟩
  fin_cases i <;> simp [flip]

private theorem mem_flip_image (i : Fin 3) (S : Finset (ℤ × ℤ × ℤ))
    (p : ℤ × ℤ × ℤ) : p ∈ S.image (flip i) ↔ flip i p ∈ S := by
  constructor
  · intro hp
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hp
    have hflip := congrArg (flip i) heq
    rw [flip_flip] at hflip
    exact hflip ▸ hq
  · intro hp
    exact Finset.mem_image.mpr ⟨flip i p, hp, flip_flip i p⟩

/-- Exact occupancy rule for fiber sorting: the preferred level takes the union
of the two fiber occupancies, and the opposite level takes their intersection.
On the binary cube these are the only two levels, so this is precisely the
same-cardinality lower/upper segment operation on each two-point fiber. -/
theorem mem_compress (i : Fin 3) (b : Bool) (S : Finset (ℤ × ℤ × ℤ))
    (p : ℤ × ℤ × ℤ) :
    p ∈ compress i b S ↔
      (coord i p = (if b then 1 else 0) ∧ (p ∈ S ∨ flip i p ∈ S)) ∨
      (coord i p = (if b then 0 else 1) ∧ p ∈ S ∧ flip i p ∈ S) := by
  simp only [compress, Finset.mem_union, Finset.mem_filter, Finset.mem_inter,
    mem_flip_image]
  tauto

/-- Every endpoint remains a four-point subset of the binary cube. -/
theorem ball_domain_card (s : Bool × Bool × Bool) : ball s ⊆ cube ∧ (ball s).card = 4 := by
  rcases s with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- The same four-point cube witness defeats all 48 fixed signed compression
mechanisms: every orientation and every ordering of the three distinct axes
strictly increases the actual independent-image mixed sum from 17 to 18. -/
theorem all_fixed_signed_compressions_increase (s : Bool × Bool × Bool)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    witness ⊆ cube ∧ witness.card = 4 ∧
      run s i j k witness = ball s ∧
      (mixedSum witness).card = 17 ∧
      (mixedSum (run s i j k witness)).card = 18 ∧
      (mixedSum witness).card < (mixedSum (run s i j k witness)).card := by
  have hrun := run_witness s i j k hij hik hjk
  have houtput : (mixedSum (run s i j k witness)).card = 18 := by
    rw [hrun, mixedSum_ball_card]
  exact ⟨witness_domain_card.1, witness_domain_card.2, hrun,
    mixedSum_witness_card, houtput, by rw [mixedSum_witness_card, houtput]; decide⟩

/-- Even a data-dependent choice among these 48 mechanisms cannot give a
nonincreasing mixed sum on every cube subset: no such choice works on this
single witness. This says nothing about adaptive exchanges or orientations
changed between steps. -/
theorem no_nonincreasing_choice_on_witness :
    ¬ ∃ (s : Bool × Bool × Bool) (i j k : Fin 3),
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (mixedSum (run s i j k witness)).card ≤ (mixedSum witness).card := by
  rintro ⟨s,i,j,k,hij,hik,hjk,hle⟩
  have h := all_fixed_signed_compressions_increase s i j k hij hik hjk
  exact (Nat.not_le_of_lt h.2.2.2.2.2) hle

example : (false,false,false) ∈ ({(false,false,false)} : Finset (Bool × Bool × Bool)) ∧
    (0 : Fin 3) ≠ 1 ∧ (0 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 2 := by decide

example : (mixedSum witness).card <
    (mixedSum (run (false,false,false) 0 1 2 witness)).card :=
  (all_fixed_signed_compressions_increase (false,false,false) 0 1 2
    (by decide) (by decide) (by decide)).2.2.2.2.2

end NoncommutingSignedCompression
