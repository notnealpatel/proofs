/-
# A recurrence identity for A086845 and A087808

Source: Sean A. Irvine's OEIS A086845 comment (Jul 14 2022).
For `n ≥ 1`, the recurrence-defined `h n` equals `Σ_{k<n} g k`, where
`g 0 = 0`, `g(2k) = 2g(k)` and `g(2k+1) = g(k)+1` define A087808.
Pairing even and odd terms gives the A086845 recurrence for the partial sums.
This is a recurrence-level result, not a formal sorting-network interpretation
of the Bose–Nelson comparator count.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086845BoseNelsonComparator

/-- A087808: `g 0 = 0`, `g (2n) = 2 g n`, `g (2n+1) = g n + 1`. -/
def g : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then 2 * g ((n + 1) / 2) else g ((n + 1) / 2) + 1
decreasing_by all_goals omega

/-- A086845: `h 1 = 0` and, for `n ≥ 2`,
`h n = h ⌊n/2⌋ + 2 h ⌈n/2⌉ + ⌊n/2⌋` (with `⌈n/2⌉ = (n+1)/2`).
The value at `0` is outside the entry's domain and set to `0`. -/
def h : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => h ((n + 2) / 2) + 2 * h ((n + 3) / 2) + (n + 2) / 2
decreasing_by all_goals omega

/-! ## Examples -/

example : (List.range 17).map g = [0,1,2,2,4,3,4,3,8,5,6,4,8,5,6,4,16] := by
  decide +kernel

example : (List.range' 1 19).map h =
    [0,1,3,5,9,12,16,19,27,32,38,42,50,55,61,65,81,90,100] := by
  decide +kernel

/-! ## Recursion lemmas -/

/-- `g (2n) = 2 g n`. -/
theorem g_two_mul (n : ℕ) : g (2 * n) = 2 * g n := by
  rcases n with _ | n
  · simp [g]
  · rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, g]
    have hmod : (2 * n + 1 + 1) % 2 = 0 := by omega
    have hdiv : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [if_pos hmod, hdiv]

/-- `g (2n+1) = g n + 1`. -/
theorem g_two_mul_add_one (n : ℕ) : g (2 * n + 1) = g n + 1 := by
  rw [g]
  have hmod : ¬ (2 * n + 1) % 2 = 0 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [if_neg hmod, hdiv]

/-- The defining recursion of `h` for `n ≥ 2`. -/
theorem h_rec (n : ℕ) (hn : 2 ≤ n) :
    h n = h (n / 2) + 2 * h ((n + 1) / 2) + n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [h]

/-- Pairing `g (2j) + g (2j+1) = 3 g j + 1`: `∑_{k<2m} g k = 3 ∑_{k<m} g k + m`. -/
theorem sum_range_two_mul (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), g k = 3 * ∑ k ∈ Finset.range m, g k + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, g_two_mul, g_two_mul_add_one]
    ring

/-- The partial sums satisfy the `h`-recursion at every `n ≥ 1`. -/
theorem sum_range_rec (n : ℕ) :
    ∑ k ∈ Finset.range n, g k = ∑ k ∈ Finset.range (n / 2), g k
      + 2 * ∑ k ∈ Finset.range ((n + 1) / 2), g k + n / 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, h2, sum_range_two_mul]
    ring
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [h1, h2, Finset.sum_range_succ, sum_range_two_mul, Finset.sum_range_succ,
      g_two_mul]
    ring

/-! ## The conjecture -/

/-- Irvine's identity: for `n ≥ 1`, the recurrence-defined A086845 term
is the sum of A087808 terms at indices `0,…,n-1`. -/
theorem h_eq_sum_range (n : ℕ) (hn : 1 ≤ n) :
    h n = ∑ k ∈ Finset.range n, g k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      simp [h, g]
    · have hhalf : 1 ≤ n / 2 := by omega
      have hceil : 1 ≤ (n + 1) / 2 := by omega
      rw [h_rec n hge, sum_range_rec n, ih (n / 2) (by omega) hhalf,
        ih ((n + 1) / 2) (by omega) hceil]

end Candidates.A086845BoseNelsonComparator
