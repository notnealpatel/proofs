import Enumerative.PalindromeRowsBijection

set_option autoImplicit false

/-!
# Palindromic power-of-two subset-count rows

This solution repeats the Challenge definition rather than importing it.  Its
proof transparently unfolds that definition and applies the existing explicit
complement-and-translation bijection for the same shifted finite subsets.
-/

namespace PalindromeRowBijection

/-- The number of `k`-element subsets of `{1, …, n}` whose ordinary sum is
divisible by `n`, using `i ↦ i + 1` to label `Finset.range n`. -/
def subsetCount (n k : ℕ) : ℕ :=
  (((Finset.range n).powersetCard k).filter
    (fun S => n ∣ S.sum (fun i => i + 1))).card

example : subsetCount 4 2 = 1 := by decide

/-- At every strict interior index, the subset-count row whose length is a
power of two is symmetric. -/
theorem subsetCount_two_pow_symm (j k : ℕ) (hk0 : 0 < k) (hk : k < 2 ^ j) :
    subsetCount (2 ^ j) k = subsetCount (2 ^ j) (2 ^ j - k) := by
  unfold subsetCount
  exact A267632.PalindromeBijection.shifted_row_card_symm_two_pow j hk0 hk

example : 0 < (1 : ℕ) ∧ 1 < 2 ^ 2 := by decide

example (k : ℕ) : ¬ (0 < k ∧ k < 2 ^ 0) := by
  intro h
  have hk0 : 0 < k := h.1
  have hk1 : k < 1 := by simpa only [pow_zero] using h.2
  exact (Nat.not_lt_of_ge hk0) hk1

example : subsetCount 4 4 = 0 ∧ subsetCount 4 0 = 1 := by decide

#print axioms subsetCount_two_pow_symm
#check @subsetCount_two_pow_symm

end PalindromeRowBijection
