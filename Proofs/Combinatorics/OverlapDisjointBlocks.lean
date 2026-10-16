import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Disjoint blocks from overlapping equal-order windows

A repeated comparison-preserving shift gives disjoint equal-order blocks away
from position zero. No injectivity or order laws are needed for this step.
-/

set_option autoImplicit false

namespace OverlapDisjointBlocks

/-- Equal-order prefix and suffix windows yield two equal-order length-`t`
blocks starting at `1` and `1 + r * (n - k)`. The shift separates the blocks,
and their last index is strictly below `n`. -/
theorem exists_disjoint_blocks {α : Type*} [LT α] (f : ℕ → α)
    (n k t : ℕ) (_hk : 2 ≤ k) (hkn : k < n) (ht : 1 ≤ t)
    (htk : 2 * t ≤ k)
    (hshift : ∀ i j : ℕ, i < k → j < k →
      (f i < f j ↔ f (i + (n - k)) < f (j + (n - k)))) :
    ∃ r : ℕ, 1 ≤ r ∧ t ≤ r * (n - k) ∧
      r * (n - k) < t + (n - k) ∧ t + r * (n - k) < n ∧
      ∀ i j : ℕ, i < t → j < t →
        (f (i + 1) < f (j + 1) ↔
          f (i + 1 + r * (n - k)) < f (j + 1 + r * (n - k))) := by
  let d := n - k
  let a := (t - 1) / d
  have hd : 0 < d := by dsimp [d]; omega
  have hdivision : (t - 1) % d + a * d = t - 1 := by
    simpa only [a, Nat.mul_comm] using Nat.mod_add_div (t - 1) d
  have hmod : (t - 1) % d < d := Nat.mod_lt _ hd
  have had : a * d < t := by omega
  have hrLower : t ≤ (a + 1) * d := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hrUpper : (a + 1) * d < t + d := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hlast : t + (a + 1) * d < n := by
    have hnd : k + d = n := by dsimp [d]; omega
    rw [Nat.add_mul, Nat.one_mul]
    omega
  refine ⟨a + 1, Nat.succ_le_succ (Nat.zero_le a), hrLower, hrUpper, hlast, ?_⟩
  intro i j hi hj
  have iterate : ∀ q : ℕ, q ≤ a + 1 →
      (f (i + 1) < f (j + 1) ↔ f (i + 1 + q * d) < f (j + 1 + q * d)) := by
    intro q
    induction q with
    | zero => intro _; simp
    | succ q ih =>
      intro hq
      have hqa : q ≤ a := by omega
      have hqd : q * d ≤ a * d := Nat.mul_le_mul_right d hqa
      have hiWindow : i + 1 + q * d < k := by omega
      have hjWindow : j + 1 + q * d < k := by omega
      have hstep := hshift (i + 1 + q * d) (j + 1 + q * d) hiWindow hjWindow
      have hprevious := ih (by omega)
      simpa only [Nat.succ_mul, Nat.add_assoc] using hprevious.trans hstep
  exact iterate (a + 1) (Nat.le_refl _)

/-- Taking half the window length supplies positive disjoint equal-order blocks
avoiding position zero for every window length `2 ≤ k < n`. -/
theorem exists_disjoint_half_blocks {α : Type*} [LT α] (f : ℕ → α)
    (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hshift : ∀ i j : ℕ, i < k → j < k →
      (f i < f j ↔ f (i + (n - k)) < f (j + (n - k)))) :
    ∃ r : ℕ, 1 ≤ r ∧ k / 2 ≤ r * (n - k) ∧
      r * (n - k) < k / 2 + (n - k) ∧ k / 2 + r * (n - k) < n ∧
      ∀ i j : ℕ, i < k / 2 → j < k / 2 →
        (f (i + 1) < f (j + 1) ↔
          f (i + 1 + r * (n - k)) < f (j + 1 + r * (n - k))) := by
  have ht : 1 ≤ k / 2 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have htk : 2 * (k / 2) ≤ k := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self k 2
  exact exists_disjoint_blocks f n k (k / 2) hk hkn ht htk hshift

example : 2 ≤ (2 : ℕ) ∧ 2 < (3 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 2 * 1 ≤ (2 : ℕ) ∧
    (∀ i j : ℕ, i < 2 → j < 2 →
      (i < j ↔ i + (3 - 2) < j + (3 - 2))) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro i j _ _
  omega

example : 2 ≤ (4 : ℕ) ∧ 4 < (104 : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ 2 * 2 ≤ (4 : ℕ) ∧
    (∀ i j : ℕ, i < 4 → j < 4 →
      (i < j ↔ i + (104 - 4) < j + (104 - 4))) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro i j _ _
  omega

end OverlapDisjointBlocks
