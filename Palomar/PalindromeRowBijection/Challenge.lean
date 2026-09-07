import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

/-!
# Palindromic power-of-two subset-count rows

For natural numbers `n` and `k`, `subsetCount n k` literally counts the
`k`-element subsets of `{1, …, n}` whose ordinary natural-number sum is
divisible by `n`.  A subset of `Finset.range n` represents those labels by the
shift `i ↦ i + 1`.

The theorem concerns only strict interior indices.  This matters: for a
positive exponent the two endpoint counts are unequal.  When `j = 0`, there is
no `k` satisfying the hypotheses, so the theorem makes no endpoint claim.
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
  sorry

example : 0 < (1 : ℕ) ∧ 1 < 2 ^ 2 := by decide

example (k : ℕ) : ¬ (0 < k ∧ k < 2 ^ 0) := by
  intro h
  have hk0 : 0 < k := h.1
  have hk1 : k < 1 := by simpa only [pow_zero] using h.2
  exact (Nat.not_lt_of_ge hk0) hk1

example : subsetCount 4 4 = 0 ∧ subsetCount 4 0 = 1 := by decide

end PalindromeRowBijection
