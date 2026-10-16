import NumberComplexity.OneSmallStep

/-!
# Optimal addition chains for three binary ones

Doubling through the largest binary position and adding the two remaining
powers gives an upper bound two steps beyond that position. The one-small-step
lower bound proves optimality. This does not classify chains with two small steps.
-/

set_option autoImplicit false

namespace NumberComplexity

private theorem threeBit_two_pow_mem {a c : ℕ} (hac : a ≤ c) :
    2 ^ a ∈ twoPowChain c := by
  induction c with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact two_pow_mem_twoPowChain 0
  | succ c ih =>
    by_cases heq : a = c + 1
    · subst a
      exact two_pow_mem_twoPowChain (c + 1)
    · exact List.mem_cons_of_mem _ (ih (by omega))

/-- Three distinct increasing binary positions give binary weight exactly three. -/
theorem binaryWeight_three_two_pow (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    binaryWeight (2 ^ a + 2 ^ b + 2 ^ c) = 3 := by
  have hsorted : ([a, b, c] : List ℕ).SortedLT := by
    simp [List.sortedLT_iff_pairwise, hab, hbc, lt_trans hab hbc]
  have hbits : (2 ^ a + 2 ^ b + 2 ^ c : ℕ).bitIndices = [a, b, c] := by
    simpa [Nat.add_assoc] using Nat.bitIndices_sum_map_two_pow hsorted
  change (2 ^ a + 2 ^ b + 2 ^ c : ℕ).bitIndices.length = 3
  rw [hbits]
  rfl

/-- The logarithmic position of a three-bit sum is its largest exponent. -/
theorem log_three_two_pow (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    Nat.log 2 (2 ^ a + 2 ^ b + 2 ^ c) = c := by
  have habpow : (2 : ℕ) ^ a < 2 ^ b :=
    (Nat.pow_lt_pow_iff_right (by decide)).mpr hab
  have hbcPow : (2 : ℕ) ^ (b + 1) ≤ 2 ^ c :=
    Nat.pow_le_pow_right (by decide) hbc
  have hsmall : (2 : ℕ) ^ a + 2 ^ b < 2 ^ c := by
    rw [pow_succ] at hbcPow
    omega
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact Nat.le_add_left _ _
  · rw [pow_succ]
    omega

/-- A three-bit sum has optimal addition-chain length two beyond its largest
binary position: double to `2 ^ c`, then add `2 ^ b` and `2 ^ a`. -/
theorem l_three_two_pow (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    l (2 ^ a + 2 ^ b + 2 ^ c) = c + 2 := by
  have hfirst : IsAddChain ((2 ^ c + 2 ^ b) :: twoPowChain c) :=
    .add (two_pow_mem_twoPowChain c) (threeBit_two_pow_mem hbc.le)
      (isAddChain_twoPowChain c)
  have hchain : IsAddChain
      (((2 ^ c + 2 ^ b) + 2 ^ a) :: (2 ^ c + 2 ^ b) :: twoPowChain c) :=
    .add (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (threeBit_two_pow_mem (by omega))) hfirst
  have hupper' : l ((2 ^ c + 2 ^ b) + 2 ^ a) ≤ c + 2 :=
    l_le_of_isAddChain _ hchain rfl
      (by rw [chainSteps_cons, List.length_cons, length_twoPowChain])
  have heq : (2 : ℕ) ^ c + 2 ^ b + 2 ^ a = 2 ^ a + 2 ^ b + 2 ^ c := by omega
  have hupper : l (2 ^ a + 2 ^ b + 2 ^ c) ≤ c + 2 := by
    simpa only [heq] using hupper'
  have hlower := log_add_two_le_l_of_three_le_binaryWeight
    (show 0 < 2 ^ a + 2 ^ b + 2 ^ c by positivity)
    (show 3 ≤ binaryWeight (2 ^ a + 2 ^ b + 2 ^ c) by
      rw [binaryWeight_three_two_pow a b c hab hbc])
  rw [log_three_two_pow a b c hab hbc] at hlower
  exact Nat.le_antisymm hupper hlower

/-- Every integer of binary weight three has exactly three increasing binary
positions. Positivity explicitly excludes the empty-bit boundary. -/
theorem eq_three_two_pow_of_binaryWeight_eq_three {n : ℕ} (hn : 0 < n)
    (hw : binaryWeight n = 3) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ n = 2 ^ a + 2 ^ b + 2 ^ c := by
  have hsum := Nat.sum_map_two_pow_bitIndices n
  have hsorted := Nat.bitIndices_sorted (n := n)
  change n.bitIndices.length = 3 at hw
  cases hbits : n.bitIndices with
  | nil =>
    simp only [hbits, List.map_nil, List.sum_nil] at hsum
    omega
  | cons a tail =>
    cases tail with
    | nil => simp [hbits] at hw
    | cons b rest =>
      cases rest with
      | nil => simp [hbits] at hw
      | cons c last =>
        have hlast : last = [] := by
          rw [hbits, List.length_cons, List.length_cons, List.length_cons] at hw
          exact List.length_eq_zero_iff.mp (by omega)
        subst last
        have horder : (a < b ∧ a < c) ∧ b < c := by
          simpa [hbits, List.sortedLT_iff_pairwise] using hsorted
        refine ⟨a, b, c, horder.1.1, horder.2, ?_⟩
        simpa [hbits, Nat.add_assoc] using hsum.symm

/-- Every positive integer of binary weight three has shortest addition-chain
length exactly two beyond its binary logarithm. -/
theorem l_eq_log_add_two_of_binaryWeight_eq_three {n : ℕ} (hn : 0 < n)
    (hw : binaryWeight n = 3) : l n = Nat.log 2 n + 2 := by
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := eq_three_two_pow_of_binaryWeight_eq_three hn hw
  rw [l_three_two_pow a b c hab hbc, log_three_two_pow a b c hab hbc]

/-! The exponent domain is inhabited, with jointly realizable strict inequalities
at the minimal triple `(0,1,2)` and at separated positions `(1,3,7)`.
The positive endpoint `7` witnesses all general three-bit hypotheses. -/

example : (0 : ℕ) < 1 ∧ (1 : ℕ) < 2 ∧
    binaryWeight (2 ^ 0 + 2 ^ 1 + 2 ^ 2) = 3 ∧
    l (2 ^ 0 + 2 ^ 1 + 2 ^ 2) = 4 :=
  ⟨by decide, by decide, binaryWeight_three_two_pow 0 1 2 (by decide) (by decide),
    l_three_two_pow 0 1 2 (by decide) (by decide)⟩

example : (1 : ℕ) < 3 ∧ (3 : ℕ) < 7 ∧
    binaryWeight (2 ^ 1 + 2 ^ 3 + 2 ^ 7) = 3 ∧
    l (2 ^ 1 + 2 ^ 3 + 2 ^ 7) = 9 :=
  ⟨by decide, by decide, binaryWeight_three_two_pow 1 3 7 (by decide) (by decide),
    l_three_two_pow 1 3 7 (by decide) (by decide)⟩

example : 0 < 7 ∧ binaryWeight 7 = 3 := by decide
example : l 7 = 4 := by
  have hlog : Nat.log 2 7 = 2 := by decide
  simpa only [hlog] using l_eq_log_add_two_of_binaryWeight_eq_three
    (n := 7) (by decide) (by decide)

end NumberComplexity
