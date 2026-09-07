import NumberComplexity.KnuthStolarsky

/-!
# Optimal addition chains with at most two binary ones

A positive number of binary weight at most two is a power of two or a sum
`2 ^ a + 2 ^ b` with `a < b`.  In the latter case, the doubling chain through
`2 ^ b` already contains `2 ^ a`, so one final addition gives a chain of
length `b + 1`.  The elementary doubling bound proves this chain optimal.

These results use neither the archived Knuth–Stolarsky conjecture nor any
finite enumeration of chains.  Together with `l_two_pow`, they provide the
exact two-bit lengths needed by `SlizkovDoubling`.
-/

set_option autoImplicit false

namespace NumberComplexity

private theorem two_pow_mem_twoPowChain_of_le {a b : ℕ} (hab : a ≤ b) :
    2 ^ a ∈ twoPowChain b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact two_pow_mem_twoPowChain 0
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst a
      exact two_pow_mem_twoPowChain (b + 1)
    · exact List.mem_cons_of_mem _ (ih (by omega))

/-- A number with exactly two binary ones, in positions `a < b`, has shortest
addition-chain length `b + 1`: double through `2 ^ b`, then add `2 ^ a`.
The lower bound follows because `b` additions cannot reach beyond `2 ^ b`. -/
theorem l_two_pow_add_two_pow (a b : ℕ) (hab : a < b) :
    l (2 ^ a + 2 ^ b) = b + 1 := by
  have hchain : IsAddChain ((2 ^ a + 2 ^ b) :: twoPowChain b) :=
    .add (two_pow_mem_twoPowChain_of_le hab.le) (two_pow_mem_twoPowChain b)
      (isAddChain_twoPowChain b)
  have hupper : l (2 ^ a + 2 ^ b) ≤ b + 1 :=
    l_le_of_isAddChain _ hchain rfl (by rw [chainSteps_cons, length_twoPowChain])
  have hpos : 0 < (2 : ℕ) ^ a := Nat.two_pow_pos a
  have hbound : 2 ^ a + 2 ^ b ≤ 2 ^ l (2 ^ a + 2 ^ b) :=
    le_two_pow_l _ (by positivity)
  have hlower : b + 1 ≤ l (2 ^ a + 2 ^ b) := by
    by_contra h
    have hexp : l (2 ^ a + 2 ^ b) ≤ b := by omega
    have hpow : (2 : ℕ) ^ l (2 ^ a + 2 ^ b) ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by decide) hexp
    omega
  exact Nat.le_antisymm hupper hlower

/-- The sum of two powers in distinct binary positions has binary weight two.
This includes separated, not just adjacent, positions. -/
theorem binaryWeight_two_pow_add_two_pow (a b : ℕ) (hab : a < b) :
    binaryWeight (2 ^ a + 2 ^ b) = 2 := by
  have hsorted : ([a, b] : List ℕ).SortedLT := by
    simpa [List.sortedLT_iff_pairwise] using hab
  have hbits : (2 ^ a + 2 ^ b : ℕ).bitIndices = [a, b] := by
    simpa using Nat.bitIndices_sum_map_two_pow hsorted
  change (2 ^ a + 2 ^ b : ℕ).bitIndices.length = 2
  rw [hbits]
  rfl

/-- Every positive number of binary weight at most two is either a power of
two or a sum of two powers in distinct, increasing binary positions. -/
theorem eq_two_pow_or_sum_of_binaryWeight_le_two {n : ℕ} (hn : 0 < n)
    (hv : binaryWeight n ≤ 2) :
    (∃ a : ℕ, n = 2 ^ a) ∨ ∃ a b : ℕ, a < b ∧ n = 2 ^ a + 2 ^ b := by
  have hsum := Nat.sum_map_two_pow_bitIndices n
  have hsorted := Nat.bitIndices_sorted (n := n)
  change n.bitIndices.length ≤ 2 at hv
  cases hbits : n.bitIndices with
  | nil =>
    simp only [hbits, List.map_nil, List.sum_nil] at hsum
    omega
  | cons a tail =>
    cases tail with
    | nil =>
      left
      refine ⟨a, ?_⟩
      simpa [hbits] using hsum.symm
    | cons b rest =>
      have hrest : rest = [] := by
        rw [hbits, List.length_cons, List.length_cons] at hv
        exact List.length_eq_zero_iff.mp (by omega)
      subst rest
      right
      refine ⟨a, b, ?_, ?_⟩
      · simpa [hbits, List.sortedLT_iff_pairwise] using hsorted
      · simpa [hbits] using hsum.symm

/-! ## Satisfiability and boundary checks

The parameters range over the inhabited type `ℕ`.  `n = 1` realizes the
one-bit boundary, while `n = 5` realizes two separated ones.  The positivity
hypothesis excludes the empty bit list at `n = 0`.
-/

example : (0 : ℕ) ≤ 2 ∧ 2 ^ 0 ∈ twoPowChain 2 :=
  ⟨by decide, two_pow_mem_twoPowChain_of_le (by decide)⟩

example : (0 : ℕ) < 2 ∧ l (2 ^ 0 + 2 ^ 2) = 3 :=
  ⟨by decide, l_two_pow_add_two_pow 0 2 (by decide)⟩

example : (0 : ℕ) < 2 ∧ binaryWeight (2 ^ 0 + 2 ^ 2) = 2 :=
  ⟨by decide, binaryWeight_two_pow_add_two_pow 0 2 (by decide)⟩

example : 0 < 1 ∧ binaryWeight 1 ≤ 2 := by decide
example : 0 < 5 ∧ binaryWeight 5 ≤ 2 := by decide
example : ¬binaryWeight 7 ≤ 2 := by decide

example : (∃ a : ℕ, 5 = 2 ^ a) ∨ ∃ a b : ℕ, a < b ∧ 5 = 2 ^ a + 2 ^ b :=
  eq_two_pow_or_sum_of_binaryWeight_le_two (by decide) (by decide)

#check @l_two_pow_add_two_pow
#check @binaryWeight_two_pow_add_two_pow
#check @eq_two_pow_or_sum_of_binaryWeight_le_two
#print axioms l_two_pow_add_two_pow
#print axioms binaryWeight_two_pow_add_two_pow
#print axioms eq_two_pow_or_sum_of_binaryWeight_le_two

end NumberComplexity
