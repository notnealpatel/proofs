import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# A051293: arbitrary-order integer-mean subset asymptotics

This is the independent statement surface for the Palomar draft. For `n ≥ 1`,
`integerMeanSubsetCount n` literally counts nonempty subsets of `{1, …, n}`
whose cardinality divides their sum. The coefficient recurrence defines the
ordered Bell (Fubini) numbers `1, 1, 3, 13, 75, 541, …`.

The general theorem uses the error scale
`o(2^n / n^(M+1))`. Equivalently, after division by the prefactor
`2^(n+1)/n`, its parenthesized error is `o(1/n^M)`. This convention follows
the unambiguous fixed order-five statement; it does not assert the potentially
stronger reading of the ambiguously punctuated general OEIS sentence.

The `if 0 < n` branches keep all real divisions away from their totalized value
at zero. They alter only one term and therefore do not change an asymptotic at
`Filter.atTop`.
-/

set_option autoImplicit false

open Finset BigOperators Filter Asymptotics

namespace PalomarA051293

/-- The number of nonempty subsets of `{1, …, n}` with integer arithmetic mean. -/
def integerMeanSubsetCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S : Finset ℕ =>
    S.Nonempty ∧ S.card ∣ S.sum id)).card

example : integerMeanSubsetCount 0 = 0 := by decide
example : integerMeanSubsetCount 1 = 1 := by decide
example : integerMeanSubsetCount 5 = 15 := by decide

/-- The ordered Bell (Fubini) coefficient, transparently defined by its recurrence. -/
def fubiniCoefficient : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), (n + 1).choose k.val * fubiniCoefficient k.val
termination_by n => n
decreasing_by exact k.isLt

/-- The first six transparent coefficients agree with `1, 1, 3, 13, 75, 541`. -/
theorem fubiniCoefficient_first_six :
    List.ofFn (fun i : Fin 6 => fubiniCoefficient i) = [1, 1, 3, 13, 75, 541] := by
  sorry

/-- For every truncation order `M`, the literal integer-mean subset count has
Fubini coefficients through order `M`, with error `o(2^n / n^(M+1))`. -/
theorem arbitrary_order_asymptotic (M : ℕ) :
    (fun n : ℕ => if 0 < n then
      (integerMeanSubsetCount n : ℝ) -
        (2 : ℝ) ^ (n + 1) / (n : ℝ) *
          ∑ i ∈ Finset.range (M + 1),
            (fubiniCoefficient i : ℝ) / (n : ℝ) ^ i
      else 0)
    =o[Filter.atTop]
      (fun n : ℕ => if 0 < n then
        (2 : ℝ) ^ n / (n : ℝ) ^ (M + 1)
        else 1) := by
  sorry

/-- The order-five corollary: after normalization by `2^(n+1)/n^6`, the error
from the first six coefficients tends to zero. -/
theorem fixed_order_five :
    Tendsto (fun n : ℕ => if 0 < n then
      ((integerMeanSubsetCount n : ℝ) -
          (2 : ℝ) ^ (n + 1) / (n : ℝ) *
            (1 + 1 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3
              + 75 / (n : ℝ) ^ 4 + 541 / (n : ℝ) ^ 5)) /
        ((2 : ℝ) ^ (n + 1) / (n : ℝ) ^ 6)
      else 0) Filter.atTop (nhds 0) := by
  sorry

#check @PalomarA051293.arbitrary_order_asymptotic
#check @PalomarA051293.fixed_order_five

end PalomarA051293
