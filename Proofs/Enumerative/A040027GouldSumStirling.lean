/-
# A Stirling transform for the Gould numbers (A040027)

Source: Velin Yanev's OEIS A040027 formula (Aug 31 2021).
The Gould numbers are defined by Jon Perry's recurrence (Apr 26 2005).
For every `n`, `a(n) = Σ_{k≤n} A058006(k) S(n+1,k+1)`, where
`A058006(k) = Σ_{i≤k} (-1)^i i!` and `S` is A048993, the Stirling numbers
of the second kind. The sum is stated in `ℤ` since A058006 has negative terms.
-/
import Mathlib
import Enumerative.StirlingBellCombinatorial

set_option autoImplicit false

namespace Candidates.A040027GouldSumStirling

open Finset

/-! ## Definitions -/

/-- The Gould numbers A040027, via Perry's recurrence from the entry:
`a(0) = a(1) = 1` and `a(n) = n + Σ_{j=1}^{n-1} C(n, j+1) a(j)` for `n ≥ 2`
(here `n = m + 2` and `j = i + 1` with `i : Fin (m + 1)`). -/
def gould : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) + ∑ j : Fin (n + 1), (n + 2).choose (j + 2) * gould (j + 1)
decreasing_by omega

/-- The alternating factorial sum A058006: `Σ_{i=0}^{k} (-1)^i i!`. -/
def altFactSum (k : ℕ) : ℤ := ∑ i ∈ range (k + 1), (-1) ^ i * (i.factorial : ℤ)

/-- The first terms of `gould` agree with A040027. -/
example : (List.range 10).map gould = [1, 1, 3, 9, 31, 121, 523, 2469, 12611, 69161] := by
  decide +kernel

/-- The first terms of `altFactSum` agree with A058006. -/
example : (List.range 8).map altFactSum = [1, 0, 2, -4, 20, -100, 620, -4420] := by
  decide +kernel

/-- Mathlib's `Nat.stirlingSecond` agrees with the rows `n = 0..4` of A048993. -/
example : ((List.range 5).map fun n => (List.range (n + 1)).map (Nat.stirlingSecond n)) =
    [[1], [0, 1], [0, 1, 1], [0, 1, 3, 1], [0, 1, 7, 6, 1]] := by
  decide

/-! ## Helper lemmas -/

/-- `Σ_{m=0}^{N} (-1)^m m! S(N, m) = (-1)^N`. -/
theorem sum_neg_one_pow_factorial_mul_stirlingSecond (N : ℕ) :
    ∑ m ∈ range (N + 1), (-1 : ℤ) ^ m * (m.factorial : ℤ) * (N.stirlingSecond m : ℤ) =
      (-1) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hshift : ∑ m ∈ range (N + 1), (-1 : ℤ) ^ (m + 1) * ((m + 1).factorial : ℤ) *
        ((m + 1 : ℕ) : ℤ) * (N.stirlingSecond (m + 1) : ℤ) =
        ∑ m ∈ range (N + 1), (-1 : ℤ) ^ m * (m.factorial : ℤ) * (m : ℤ) *
          (N.stirlingSecond m : ℤ) := by
      have h := sum_range_succ' (fun m => (-1 : ℤ) ^ m * (m.factorial : ℤ) * (m : ℤ) *
        (N.stirlingSecond m : ℤ)) (N + 1)
      rw [sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self N)] at h
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h
      exact h.symm
    rw [sum_range_succ', Nat.stirlingSecond_succ_zero]
    simp only [Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul, mul_add,
      sum_add_distrib, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero]
    have hfirst : ∑ m ∈ range (N + 1), (-1 : ℤ) ^ (m + 1) * ((m + 1).factorial : ℤ) *
        (((m : ℤ) + 1) * (N.stirlingSecond (m + 1) : ℤ)) =
        ∑ m ∈ range (N + 1), (-1 : ℤ) ^ m * (m.factorial : ℤ) * (m : ℤ) *
          (N.stirlingSecond m : ℤ) := by
      rw [← hshift]
      refine sum_congr rfl fun m _ => ?_
      push_cast
      ring
    rw [hfirst, ← sum_add_distrib]
    calc ∑ m ∈ range (N + 1), ((-1 : ℤ) ^ m * (m.factorial : ℤ) * (m : ℤ) *
            (N.stirlingSecond m : ℤ) + (-1 : ℤ) ^ (m + 1) * ((m + 1).factorial : ℤ) *
              (N.stirlingSecond m : ℤ))
        = ∑ m ∈ range (N + 1), -((-1 : ℤ) ^ m * (m.factorial : ℤ) *
            (N.stirlingSecond m : ℤ)) := by
          refine sum_congr rfl fun m _ => ?_
          push_cast [Nat.factorial_succ]
          ring
      _ = (-1) ^ (N + 1) := by
          rw [sum_neg_distrib, ih]
          ring

/-- `U(j) = Σ_{k=0}^{j} A058006(k) S(j, k)`, an auxiliary Stirling transform. -/
def stirlingAltSum (j : ℕ) : ℤ := ∑ k ∈ range (j + 1), altFactSum k * (j.stirlingSecond k : ℤ)

/-- `T(n) = Σ_{k=0}^{n} A058006(k) S(n+1, k+1)`, the right side of Yanev's conjecture. -/
def gouldStirlingSum (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), altFactSum k * ((n + 1).stirlingSecond (k + 1) : ℤ)

/-- `A058006(k+1) = A058006(k) + (-1)^(k+1) (k+1)!`. -/
theorem altFactSum_succ (k : ℕ) :
    altFactSum (k + 1) = altFactSum k + (-1) ^ (k + 1) * ((k + 1).factorial : ℤ) := by
  rw [altFactSum, sum_range_succ, ← altFactSum]

/-- Extending the range of `U(i)` beyond `i` adds only zero terms. -/
theorem sum_range_altFactSum_mul_stirlingSecond {i M : ℕ} (hiM : i < M) :
    ∑ k ∈ range M, altFactSum k * (i.stirlingSecond k : ℤ) = stirlingAltSum i := by
  symm
  refine sum_subset (range_subset_range.2 (by omega)) fun k _ hk => ?_
  rw [mem_range, not_lt] at hk
  rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- `T(n) = Σ_{i=0}^{n} C(n, i) U(i)`, from `S(n+1,k+1) = Σ_i C(n,i) S(i,k)`. -/
theorem gouldStirlingSum_eq_sum_choose (n : ℕ) :
    gouldStirlingSum n = ∑ i ∈ range (n + 1), (n.choose i : ℤ) * stirlingAltSum i := by
  simp_rw [gouldStirlingSum, StirlingBellCombinatorial.stirlingSecond_succ_succ_eq_sum,
    Nat.cast_sum, Nat.cast_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_range_altFactSum_mul_stirlingSecond (mem_range.1 hi), mul_sum]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- `U(n+1) + (-1)^n = T(n)`. -/
theorem stirlingAltSum_succ_add (n : ℕ) :
    stirlingAltSum (n + 1) + (-1) ^ n = gouldStirlingSum n := by
  have hW := sum_neg_one_pow_factorial_mul_stirlingSecond (n + 1)
  rw [sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero] at hW
  have hU : stirlingAltSum (n + 1) = gouldStirlingSum n + (-1) ^ (n + 1) := by
    rw [stirlingAltSum, sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero,
      add_zero, ← hW, gouldStirlingSum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [altFactSum_succ]
    ring
  rw [hU, pow_succ]
  ring

/-- `U(0) = 1`. -/
theorem stirlingAltSum_zero : stirlingAltSum 0 = 1 := by
  simp [stirlingAltSum, altFactSum]

/-- `T(0) = 1`. -/
theorem gouldStirlingSum_zero : gouldStirlingSum 0 = 1 := by
  simp [gouldStirlingSum, altFactSum, Nat.stirlingSecond_self]

/-- `T(1) = 1`. -/
theorem gouldStirlingSum_one : gouldStirlingSum 1 = 1 := by
  decide +kernel

/-- `Σ_{i=0}^{n+1} (-1)^i C(n+2, i+1) = 1`. -/
theorem sum_range_neg_one_pow_mul_choose_succ (n : ℕ) :
    ∑ i ∈ range (n + 2), (-1 : ℤ) ^ i * ((n + 2).choose (i + 1) : ℤ) = 1 := by
  have h := Int.alternating_sum_range_choose (n := n + 2)
  rw [sum_range_succ'] at h
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, if_false, pow_zero,
    Nat.choose_zero_right, Nat.cast_one, mul_one, pow_succ, mul_neg_one, neg_mul,
    sum_neg_distrib] at h
  linarith

/-- Perry's recurrence for `gould (n + 2)` with the sum over `Finset.range`. -/
theorem gould_add_two (n : ℕ) :
    gould (n + 2) = (n + 2) + ∑ j ∈ range (n + 1), (n + 2).choose (j + 2) * gould (j + 1) := by
  rw [gould, Fin.sum_univ_eq_sum_range (fun j => (n + 2).choose (j + 2) * gould (j + 1))]

/-- `a(n) = T(n)` for every `n`, by strong induction. -/
theorem gould_eq_gouldStirlingSum (n : ℕ) : (gould n : ℤ) = gouldStirlingSum n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [gouldStirlingSum_zero, gould, Nat.cast_one]
    | 1, _ => rw [gouldStirlingSum_one, gould, Nat.cast_one]
    | n + 2, ih =>
      rw [gould_add_two, gouldStirlingSum_eq_sum_choose,
        sum_range_succ' (fun i => ((n + 2).choose i : ℤ) * stirlingAltSum i), stirlingAltSum_zero]
      have hU : ∀ i, stirlingAltSum (i + 1) = gouldStirlingSum i - (-1) ^ i := fun i => by
        rw [← stirlingAltSum_succ_add i]
        ring
      simp_rw [hU, mul_sub]
      rw [sum_sub_distrib,
        sum_range_succ' (fun i => ((n + 2).choose (i + 1) : ℤ) * gouldStirlingSum i),
        gouldStirlingSum_zero]
      have halt : ∑ i ∈ range (n + 2), ((n + 2).choose (i + 1) : ℤ) * (-1) ^ i = 1 := by
        exact (sum_congr rfl fun i _ => mul_comm _ _).trans
          (sum_range_neg_one_pow_mul_choose_succ n)
      rw [halt]
      have hIH : ∀ j ∈ range (n + 1), ((n + 2).choose (j + 1 + 1) : ℤ) * gouldStirlingSum (j + 1) =
          (((n + 2).choose (j + 2) * gould (j + 1) : ℕ) : ℤ) := fun j hj => by
        rw [mem_range] at hj
        rw [← ih (j + 1) (by omega)]
        push_cast
        ring_nf
      rw [sum_congr rfl hIH]
      push_cast
      simp only [Nat.choose_zero_right, Nat.choose_one_right]
      push_cast
      ring

/-! ## The conjecture -/

/-- Yanev's formula: the Gould number equals the A058006-weighted shifted
Stirling sum. The equality is in `ℤ` because A058006 takes negative values. -/
theorem gould_eq_sum_altFactSum_mul_stirlingSecond (n : ℕ) :
    (gould n : ℤ) =
      ∑ k ∈ range (n + 1), altFactSum k * ((n + 1).stirlingSecond (k + 1) : ℤ) :=
  gould_eq_gouldStirlingSum n

end Candidates.A040027GouldSumStirling
