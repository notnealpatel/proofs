import Mathlib

/-!
# Exact doubling for addition chains with at most two binary ones

This standalone challenge defines ordinary addition chains directly. Lists are
stored with the most recently computed value first. Each new value is the sum
of two earlier values; repeated values and equal summands are permitted.
The length counts additions, not list elements. The selected result concerns
only positive integers with at most two binary ones, not an unrestricted
Slizkov or Knuth–Stolarsky conjecture.
-/

set_option autoImplicit false

namespace Palomar.TwoBitAdditionChains

/-! ## Independent addition-chain model -/

/-- An addition chain, stored in reverse order, starts with `1` and is extended
only by adding two already present values. The two summands may coincide. -/
inductive IsAddChain : List ℕ → Prop
  | one : IsAddChain [1]
  | add {c : List ℕ} {a b : ℕ} (ha : a ∈ c) (hb : b ∈ c) (hc : IsAddChain c) :
      IsAddChain ((a + b) :: c)

example : IsAddChain [1] := .one
example : IsAddChain [2, 1] := .add (a := 1) (b := 1) (by simp) (by simp) .one
example : IsAddChain [3, 2, 1] :=
  .add (a := 2) (b := 1) (by simp) (by simp)
    (.add (a := 1) (b := 1) (by simp) (by simp) .one)
example : ¬IsAddChain [] := by
  intro h
  cases h

/-- Every addition chain contains its initial value `1`. -/
theorem IsAddChain.one_mem {c : List ℕ} (hc : IsAddChain c) : 1 ∈ c := by
  induction hc with
  | one => exact List.mem_cons_self
  | add _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Every value produced by an addition chain is positive. -/
theorem IsAddChain.one_le_of_mem {c : List ℕ} (hc : IsAddChain c) :
    ∀ x ∈ c, 1 ≤ x := by
  induction hc with
  | one =>
    intro x hx
    rw [List.mem_singleton] at hx
    omega
  | @add c a b ha _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hsum | htail
    · have ha_pos : 1 ≤ a := ih a ha
      omega
    · exact ih x htail

/-- The number of additions in a reversed chain is the length of its tail.
The empty non-chain has the totalized value `0`. -/
def chainSteps (c : List ℕ) : ℕ := c.tail.length

example : chainSteps [] = 0 := rfl
example : chainSteps [1] = 0 := rfl
example : chainSteps [3, 2, 1] = 2 := rfl

/-- Chains reaching `n` are precisely addition chains with head `n`. -/
abbrev AdditionChain (n : ℕ) : Type :=
  {c : List ℕ // IsAddChain c ∧ c.head? = some n}

example : Nonempty (AdditionChain 3) :=
  ⟨⟨[3, 2, 1], .add (a := 2) (b := 1) (by simp) (by simp)
    (.add (a := 1) (b := 1) (by simp) (by simp) .one), rfl⟩⟩

private theorem exists_chain_succ : ∀ n : ℕ, ∃ c : List ℕ, IsAddChain ((n + 1) :: c)
  | 0 => ⟨[], .one⟩
  | n + 1 => by
    obtain ⟨c, hc⟩ := exists_chain_succ n
    exact ⟨(n + 1) :: c, .add List.mem_cons_self hc.one_mem hc⟩

/-- Every positive target has a genuine addition chain, for example the chain
that repeatedly adds `1`. Thus the shortest-length infimum is nonempty. -/
theorem additionChain_nonempty {n : ℕ} (hn : 0 < n) : Nonempty (AdditionChain n) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨c, hc⟩ := exists_chain_succ n
    exact ⟨⟨(n + 1) :: c, hc, rfl⟩⟩

/-- No addition chain reaches zero: all its values are positive. -/
theorem additionChain_zero_isEmpty : IsEmpty (AdditionChain 0) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp c.property.2
  have hzero_mem : 0 ∈ c.val := by rw [htail]; exact List.mem_cons_self
  have hzero_pos : 1 ≤ (0 : ℕ) := c.property.1.one_le_of_mem 0 hzero_mem
  omega

/-- The shortest addition-chain length is the infimum of actual chain lengths.
For positive targets it is attained. At `n = 0` the indexing type is empty,
and the totalized natural infimum has the junk value `0`. -/
noncomputable def l (n : ℕ) : ℕ :=
  ⨅ c : AdditionChain n, chainSteps c.val

/-- Every actual chain bounds the shortest length from above. -/
theorem l_le_chainSteps {n : ℕ} (c : AdditionChain n) : l n ≤ chainSteps c.val :=
  Nat.sInf_le (Set.mem_range_self c)

/-- For a positive target, some actual chain attains the shortest length. -/
theorem exists_chainSteps_eq_l {n : ℕ} (hn : 0 < n) :
    ∃ c : AdditionChain n, chainSteps c.val = l n := by
  letI : Nonempty (AdditionChain n) := additionChain_nonempty hn
  exact Nat.sInf_mem (Set.range_nonempty _)

example : l 0 = 0 := by
  letI : IsEmpty (AdditionChain 0) := additionChain_zero_isEmpty
  exact Nat.iInf_of_empty _

example : l 1 = 0 :=
  Nat.le_zero.mp (l_le_chainSteps ⟨[1], .one, rfl⟩)

/-- Binary weight is the number of `1` digits, using Mathlib's list of their
positions. This is an abbreviation of `n.bitIndices.length`, not a new count. -/
abbrev binaryWeight (n : ℕ) : ℕ := n.bitIndices.length

example : binaryWeight 0 = 0 := by decide
example : binaryWeight 1 = 1 := by decide
example : binaryWeight 9 = 2 := by decide
example : binaryWeight 7 = 3 := by decide

-- Jointly satisfiable guards: the one-bit boundary and two separated ones.
example : 0 < 1 ∧ binaryWeight 1 ≤ 2 := by decide
example : 0 < 9 ∧ binaryWeight 9 ≤ 2 := by decide
example : Nonempty (AdditionChain 9) := additionChain_nonempty (by decide)
example : ¬(0 < (0 : ℕ)) := by decide
example : ¬binaryWeight 7 ≤ 2 := by decide

/-! ## Selected theorem -/

/-- Doubling costs exactly one additional addition for every positive target
with at most two binary ones. This is a bounded-family theorem only. -/
theorem l_two_mul_eq_add_one_of_binaryWeight_le_two {k : ℕ} (hk : 0 < k)
    (hv : binaryWeight k ≤ 2) : l (2 * k) = l k + 1 := by
  sorry

set_option pp.fullNames true in
#check @Palomar.TwoBitAdditionChains.l_two_mul_eq_add_one_of_binaryWeight_le_two
#print axioms Palomar.TwoBitAdditionChains.l_two_mul_eq_add_one_of_binaryWeight_le_two

end Palomar.TwoBitAdditionChains
