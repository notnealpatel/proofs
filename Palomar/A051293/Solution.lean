import Enumerative.A051293.Cloitre

/-!
# A051293: proved Palomar solution surface

This module gives the same declarations as `Palomar.A051293.Challenge` while
bridging them to the substantive development in
`Proofs/Enumerative/A051293/Counting.lean` and
`Proofs/Enumerative/A051293/Cloitre.lean`. It intentionally does not import the
Challenge module: Comparator compiles the two same-named declaration surfaces
separately.
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

private theorem fubiniCoefficient_succ_eq_sum_range (i : ℕ) :
    fubiniCoefficient (i + 1) =
      ∑ m ∈ Finset.range (i + 1), (i + 1).choose m * fubiniCoefficient m := by
  conv_lhs => unfold fubiniCoefficient
  exact Fin.sum_univ_eq_sum_range
    (fun k => (i + 1).choose k * fubiniCoefficient k) (i + 1)

private theorem fubiniCoefficient_eq_fubini (n : ℕ) :
    fubiniCoefficient n = A051293.fubini n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp only [fubiniCoefficient, A051293.fubini_zero]
      | succ n =>
          rw [fubiniCoefficient_succ_eq_sum_range,
            A051293.fubini_succ_eq_sum_range]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [ih m (Finset.mem_range.mp hm)]

/-- The first six transparent coefficients agree with `1, 1, 3, 13, 75, 541`. -/
theorem fubiniCoefficient_first_six :
    List.ofFn (fun i : Fin 6 => fubiniCoefficient i) = [1, 1, 3, 13, 75, 541] := by
  change [fubiniCoefficient 0, fubiniCoefficient 1, fubiniCoefficient 2,
    fubiniCoefficient 3, fubiniCoefficient 4, fubiniCoefficient 5] =
      [1, 1, 3, 13, 75, 541]
  simp only [fubiniCoefficient_eq_fubini, A051293.fubini_zero, A051293.fubini_one,
    A051293.fubini_two, A051293.fubini_three, A051293.fubini_four, A051293.fubini_five]

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
  refine (A051293.cloitre_conjecture M).congr' ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simp only [if_pos hn]
    rw [A051293.a_comb_eq_a_oeis]
    simp only [integerMeanSubsetCount, A051293.a_oeis]
    simp_rw [fubiniCoefficient_eq_fubini]
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simp only [if_pos hn]

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
  apply Filter.Tendsto.congr' _ A051293.cloitre_explicit_tendsto
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [if_pos hn, integerMeanSubsetCount, A051293.a_oeis]

#check @PalomarA051293.arbitrary_order_asymptotic
#check @PalomarA051293.fixed_order_five

#print axioms PalomarA051293.fubiniCoefficient_first_six
#print axioms PalomarA051293.arbitrary_order_asymptotic
#print axioms PalomarA051293.fixed_order_five

end PalomarA051293
