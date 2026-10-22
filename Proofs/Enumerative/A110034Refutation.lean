/-
# A110034: a boundary failure of Bergot's partial-sum identity

OEIS A110034, J. M. Bergot (Jun 10 2013), with A061646.
The recurrence used here is the one matching the entry's generating
function and signature `(3,0,-3,1)`, not its misprinted recurrence line;
`gf_spec` proves the generating-function identity. The Hankel-triangle
counting interpretation is not formalized.
The all-natural partial-sum statement fails at `n = 0`, where the sum is
empty and `|a(0)| = 1`. The identity is proved for every `n ≥ 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A110034Refutation

/-! ## Definitions -/

/-- **A110034**, `a : ℕ → ℤ` with offset `0`: the coefficients of
`(1-3x-x^2+2x^3)/((1-x^2)(1-3x+x^2))`, given by the recurrence of signature
`(3,0,-3,1)` with initial values `1, 0, -1, -4` (certified against the g.f. by
`gf_spec`). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | 3 => -4
  | n + 4 => 3 * a (n + 3) - 3 * a (n + 1) + a n

/-- **A061646**, re-indexed to start at `0`: `A061646Seq j` is the OEIS value
`A061646(j - 1)` (the OEIS offset is `-1`).  So `A061646Seq 0 = A061646(-1) = 1`,
`A061646Seq 1 = A061646(0) = 1`, `A061646Seq 2 = A061646(1) = 1`, and
`A061646(n) = 2 A061646(n-1) + 2 A061646(n-2) - A061646(n-3)`. -/
def A061646Seq : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => 2 * A061646Seq (n + 2) + 2 * A061646Seq (n + 1) - A061646Seq n

/-! ## Examples against the OEIS DATA lines -/

example : (List.range 12).map a =
    [1, 0, -1, -4, -11, -30, -79, -208, -545, -1428, -3739, -9790] := by
  decide

example : (List.range 13).map A061646Seq =
    [1, 1, 1, 3, 7, 19, 49, 129, 337, 883, 2311, 6051, 15841] := by
  decide

/-- The generating function of `a` is `(1-3x-x^2+2x^3)/((1-x^2)(1-3x+x^2))`,
stated without division: `(∑ a(n) xⁿ) · (1-x^2)(1-3x+x^2) = 1-3x-x^2+2x^3`
in `ℤ⟦X⟧`. -/
theorem gf_spec :
    PowerSeries.mk a * ((1 - PowerSeries.X ^ 2) *
      (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2)) =
    (1 - 3 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 : PowerSeries ℤ) := by
  have hden : ((1 - PowerSeries.X ^ 2) * (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) :
      PowerSeries ℤ) = 1 - PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 1 +
        PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 := by
    simp only [map_ofNat, pow_one]; ring
  have hnum : (1 - 3 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 :
      PowerSeries ℤ) = 1 - PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 1 - PowerSeries.X ^ 2 +
        PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat, pow_one]
  rw [hden, hnum]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add,
    mul_left_comm (PowerSeries.mk a) (PowerSeries.C _), PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_C]
  rcases n with _ | _ | _ | _ | n
  · simp [a]
  · simp [a]
  · simp [a]
  · simp [a]
  · simp only [a, le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right,
      Nat.reduceSubDiff, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, sub_self,
      Nat.reduceEqDiff, add_zero]
    ring

/-- The defining recurrence of `a` (signature `(3,0,-3,1)`). -/
theorem a_add_four (n : ℕ) : a (n + 4) = 3 * a (n + 3) - 3 * a (n + 1) + a n := rfl

/-- The defining recurrence of A061646 in the re-indexed form. -/
theorem A061646Seq_add_three (n : ℕ) :
    A061646Seq (n + 3) = 2 * A061646Seq (n + 2) + 2 * A061646Seq (n + 1) - A061646Seq n := rfl

/-- First differences of A110034: `a(n+1) - a(n) = -A061646(n)` for all `n ≥ 0`
(here `A061646(n) = A061646Seq (n + 1)`). -/
theorem a_succ_sub (n : ℕ) : a (n + 1) - a n = -A061646Seq (n + 1) := by
  have key : ∀ m : ℕ, (a (m + 1) - a m = -A061646Seq (m + 1)) ∧
      (a (m + 2) - a (m + 1) = -A061646Seq (m + 2)) ∧
      (a (m + 3) - a (m + 2) = -A061646Seq (m + 3)) := by
    intro m
    induction m with
    | zero => exact ⟨by decide, by decide, by decide⟩
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have ha : a (m + 1 + 3) = 3 * a (m + 3) - 3 * a (m + 1) + a m := a_add_four m
      have hc : A061646Seq (m + 1 + 3) =
          2 * A061646Seq (m + 3) + 2 * A061646Seq (m + 2) - A061646Seq (m + 1) :=
        A061646Seq_add_three (m + 1)
      rw [ha, hc]
      linear_combination 2 * h2 + 2 * h1 - h0
  exact (key n).1

/-- Every term of A061646 is nonnegative. -/
theorem A061646Seq_nonneg (n : ℕ) : 0 ≤ A061646Seq n := by
  have key : ∀ m : ℕ, 0 ≤ A061646Seq m ∧ A061646Seq m ≤ A061646Seq (m + 1) ∧
      A061646Seq (m + 1) ≤ A061646Seq (m + 2) := by
    intro m
    induction m with
    | zero => exact ⟨by decide, by decide, by decide⟩
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨by linarith, h2, ?_⟩
      rw [show m + 1 + 2 = m + 3 from rfl, A061646Seq_add_three m]
      linarith
  exact (key n).1

/-- For `n ≥ 1`, `-a(n) = Sum_{k=1..n-1} A061646(k)`. -/
theorem neg_a_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    -a n = ∑ k ∈ Finset.Ico 1 n, A061646Seq (k + 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]
    linear_combination (-1 : ℤ) * a_succ_sub n

/-! ## The conjecture -/

/-- Bergot's A110034 conjecture `|a(n)| = Σ_{k=1}^{n-1} A061646(k)`,
stated over the full offset-zero domain. The interval `Ico 1 n` avoids
natural subtraction. Because A061646 starts at `-1`, its term at `k`
is `A061646Seq(k+1)`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, |a n| = ∑ k ∈ Finset.Ico 1 n, A061646Seq (k + 1)

/-- The all-natural statement fails at `n = 0`: `|a(0)| = 1`, whereas
the empty sum is `0`. The identity for `n ≥ 1` is
`abs_eq_sum_of_one_le`. -/
theorem bergot_conjecture_false : ¬ Conjecture := by
  intro h
  have h0 : |a 0| = ∑ k ∈ Finset.Ico 1 0, A061646Seq (k + 1) := h 0
  have hlhs : |a 0| = 1 := by decide
  have hrhs : ∑ k ∈ Finset.Ico 1 0, A061646Seq (k + 1) = 0 := by decide
  rw [hlhs, hrhs] at h0
  exact one_ne_zero h0

/-- **Corrected form (proved).** Bergot's identity holds for every `n ≥ 1`:
`|a(n)| = Sum_{k=1..n-1} A061646(k)`.  Indeed `a(n+1) - a(n) = -A061646(n)`, so
`-a(n) = Sum_{k=1..n-1} A061646(k) ≥ 0` for `n ≥ 1`. -/
theorem abs_eq_sum_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    |a n| = ∑ k ∈ Finset.Ico 1 n, A061646Seq (k + 1) := by
  have hsum : 0 ≤ ∑ k ∈ Finset.Ico 1 n, A061646Seq (k + 1) :=
    Finset.sum_nonneg fun k _ => A061646Seq_nonneg (k + 1)
  have hneg : -a n = ∑ k ∈ Finset.Ico 1 n, A061646Seq (k + 1) := neg_a_eq_sum n hn
  rw [← hneg, ← abs_neg, abs_of_nonneg (hneg ▸ hsum)]

-- Non-vacuity of the corrected form: at `n = 4`, `|a(4)| = 11 = 1 + 3 + 7`.
example : |a 4| = ∑ k ∈ Finset.Ico 1 4, A061646Seq (k + 1) ∧ |a 4| = 11 := by decide

end Candidates.A110034Refutation
