/-
# A100056 — Adamson's maximality conjecture for golden-ratio permutations is false

## OEIS source (retrieved 2026-10-21; `oeis show A100056` and the live entry)

```
A100056   Sum of absolute differences of p(n) defined in A054065.
OFFSET:   2
DATA:     1,3,7,10,16,22,27,37,47,57,67,75,91,107,123,139,155,171,187,200,226,
          ...
COMMENT:  Conjecture: a(n) provides the maximum sum of difference terms of any
          permutation of 1 through n. A054065 (or reversals) give the optimal
          permutations and a(n) gives the sum.
FORMULA:  a(n) = sum, (abs. values) of difference row of p(n), A054065.
EXAMPLE:  a(4) = 7 since p(4) of A054065 = 2 4 1 3. Finite difference row
          (abs. values) of p(4) = 2 3 2; sum = 7.
AUTHOR:   Gary W. Adamson, Oct 31 2004
EXTENSIONS: Edited and extended by Ray Chandler, Apr 18 2009
```

A054065: "Fractal sequence induced by tau: for k >= 1, let p(k) be the
permutation of 1,2,...,k obtained by ordering the fractional parts {h*tau}
for h=1,2,...,k; then juxtapose p(1),p(2),p(3),..." (`tau` is the golden
ratio; the Mathematica program sorts `FractionalPart[k*r]` increasingly with
`r = (1+Sqrt[5])/2`).  Its rows begin `1 | 2 1 | 2 1 3 | 2 4 1 3 | 5 2 4 1 3`.

The conjecture line carries no separate author or date; it belongs to the
entry by Gary W. Adamson, Oct 31 2004.  No later comment on A100056 retracts
it.

## Status

This module **refutes** the conjecture.  At `n = 5`, `p(5) = (5,2,4,1,3)` has
absolute differences `3,2,3,2`, so `a(5) = 10`, while the permutation
`(3,1,5,2,4)` of `1..5` has absolute differences `2,4,3,2`, total `11`.
(Brute force for `n ≤ 9`: the true maximum is `⌊n²/2⌋ - 1` =
`1,3,7,11,17,23,31,39` for `n = 2..9`, while `a(n) = 1,3,7,10,16,22,27,37`;
the conjecture holds for `n = 2,3,4` only.)
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A100056Refutation

open Real

/-! ## Definition layer -/

/-- The fractional part `{h * τ}` of `h` times the golden ratio `τ = (1+√5)/2`. -/
noncomputable def fracPhi (h : ℕ) : ℝ := Int.fract ((h : ℝ) * goldenRatio)

/-- The permutation `p(k)` of A054065: the numbers `1, 2, …, k` listed in
increasing order of the fractional parts `{h * τ}`.  (These fractional parts
are pairwise distinct because `τ` is irrational, so the order is strict and the
sort is unambiguous; see `p_eq_of_perm_of_pairwise`.) -/
noncomputable def p (k : ℕ) : List ℕ :=
  (List.range' 1 k).mergeSort (fun a b => decide (fracPhi a ≤ fracPhi b))

/-- The sum of the absolute values of the consecutive differences of a list of
natural numbers: `|x₂ - x₁| + |x₃ - x₂| + ⋯` (computed in `ℤ`). -/
def sumAbsDiff : List ℕ → ℕ
  | a :: b :: t => ((b : ℤ) - (a : ℤ)).natAbs + sumAbsDiff (b :: t)
  | _ => 0

/-- `a(n)` of A100056: the sum of absolute differences of `p(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sumAbsDiff (p n)

/-! ## The conjecture -/

/-- **Adamson's conjecture (A100056).**  Verbatim: "Conjecture: a(n) provides
the maximum sum of difference terms of any permutation of 1 through n."

For every `n` in the entry's range (`OFFSET 2`), `a(n)` is the greatest value of
`∑ |π(i+1) - π(i)|` over all permutations `π` of `1, …, n` (lists that are
permutations of `[1, …, n]`). -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    IsGreatest {s : ℕ | ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ s = sumAbsDiff l} (a n)

/-! ## The golden ratio and the fractional parts `{h τ}`, `h ≤ 5` -/

/-- Crude bounds `8/5 < τ < 5/3`, enough to fix `⌊h τ⌋` and the order of
`{h τ}` for `h ≤ 5`. -/
lemma goldenRatio_bounds : (8 / 5 : ℝ) < goldenRatio ∧ goldenRatio < 5 / 3 := by
  have h1 : (11 / 5 : ℝ) < √5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : √5 < (7 / 3 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  rw [goldenRatio]
  constructor <;> linarith

/-- Distinct naturals have distinct fractional parts `{h τ}` (irrationality). -/
lemma fracPhi_injective : Function.Injective fracPhi := by
  intro x y hxy
  by_contra hne
  have hsub : ((x : ℝ) - y) * goldenRatio = ⌊(x : ℝ) * goldenRatio⌋ - ⌊(y : ℝ) * goldenRatio⌋ := by
    have hx := Int.floor_add_fract ((x : ℝ) * goldenRatio)
    have hy := Int.floor_add_fract ((y : ℝ) * goldenRatio)
    unfold fracPhi at hxy
    linarith
  have hirr : Irrational (((x : ℤ) - (y : ℤ) : ℤ) * goldenRatio) :=
    Real.goldenRatio_irrational.intCast_mul (by omega)
  apply hirr
  refine ⟨(⌊(x : ℝ) * goldenRatio⌋ - ⌊(y : ℝ) * goldenRatio⌋ : ℤ), ?_⟩
  push_cast
  rw [hsub]

/-- Uniqueness of the sorted order: any arrangement of `1, …, k` that is
increasing in `{h τ}` is `p(k)`. -/
lemma p_eq_of_perm_of_pairwise {k : ℕ} {l : List ℕ} (hperm : l.Perm (List.range' 1 k))
    (hsort : l.Pairwise (fun a b => fracPhi a ≤ fracPhi b)) : p k = l := by
  have hms : (p k).Pairwise (fun a b => fracPhi a ≤ fracPhi b) := by
    have := List.pairwise_mergeSort (le := fun a b => decide (fracPhi a ≤ fracPhi b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
      (fun a b => by simpa using le_total (fracPhi a) (fracPhi b)) (List.range' 1 k)
    simpa [p] using this
  refine List.Perm.eq_of_pairwise (fun x y _ _ hxy hyx => fracPhi_injective (le_antisymm hxy hyx))
    hms hsort ?_
  exact (List.mergeSort_perm _ _).trans hperm.symm

/-- `{h τ} = h τ - m` once `m ≤ h τ < m + 1`. -/
lemma fracPhi_eq {h : ℕ} {m : ℤ} (hlo : (m : ℝ) ≤ h * goldenRatio)
    (hhi : (h : ℝ) * goldenRatio < m + 1) : fracPhi h = h * goldenRatio - m := by
  rw [fracPhi, Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, m, by ring⟩

/-- `{1 τ} = τ - 1`. -/
lemma fracPhi_one : fracPhi 1 = goldenRatio - 1 := by
  obtain ⟨hl, hu⟩ := goldenRatio_bounds
  rw [fracPhi_eq (m := 1) (by push_cast; linarith) (by push_cast; linarith)]
  push_cast; ring

/-- `{2 τ} = 2 * τ - 3`. -/
lemma fracPhi_two : fracPhi 2 = 2 * goldenRatio - 3 := by
  obtain ⟨hl, hu⟩ := goldenRatio_bounds
  rw [fracPhi_eq (m := 3) (by push_cast; linarith) (by push_cast; linarith)]
  push_cast; ring

/-- `{3 τ} = 3 * τ - 4`. -/
lemma fracPhi_three : fracPhi 3 = 3 * goldenRatio - 4 := by
  obtain ⟨hl, hu⟩ := goldenRatio_bounds
  rw [fracPhi_eq (m := 4) (by push_cast; linarith) (by push_cast; linarith)]
  push_cast; ring

/-- `{4 τ} = 4 * τ - 6`. -/
lemma fracPhi_four : fracPhi 4 = 4 * goldenRatio - 6 := by
  obtain ⟨hl, hu⟩ := goldenRatio_bounds
  rw [fracPhi_eq (m := 6) (by push_cast; linarith) (by push_cast; linarith)]
  push_cast; ring

/-- `{5 τ} = 5 * τ - 8`. -/
lemma fracPhi_five : fracPhi 5 = 5 * goldenRatio - 8 := by
  obtain ⟨hl, hu⟩ := goldenRatio_bounds
  rw [fracPhi_eq (m := 8) (by push_cast; linarith) (by push_cast; linarith)]
  push_cast; ring

/-- The order of the fractional parts: `{5τ} < {2τ} < {4τ} < {τ} < {3τ}`. -/
lemma fracPhi_chain :
    fracPhi 5 < fracPhi 2 ∧ fracPhi 2 < fracPhi 4 ∧ fracPhi 4 < fracPhi 1 ∧
      fracPhi 1 < fracPhi 3 := by
  obtain ⟨hl, hu⟩ := goldenRatio_bounds
  rw [fracPhi_one, fracPhi_two, fracPhi_three, fracPhi_four, fracPhi_five]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The rows `p(2), …, p(5)` (ground truth against A054065) -/

/-- `p(2) = (2, 1)`, row 2 of A054065. -/
theorem p_two : p 2 = [2, 1] := by
  obtain ⟨h52, h24, h41, h13⟩ := fracPhi_chain
  refine p_eq_of_perm_of_pairwise (by decide) ?_
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq, List.Pairwise.nil, or_false, IsEmpty.forall_iff, implies_true, and_true]
  linarith

/-- `p(3) = (2, 1, 3)`, row 3 of A054065. -/
theorem p_three : p 3 = [2, 1, 3] := by
  obtain ⟨h52, h24, h41, h13⟩ := fracPhi_chain
  refine p_eq_of_perm_of_pairwise (by decide) ?_
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, or_false, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith

/-- `p(4) = (2, 4, 1, 3)`, row 4 of A054065 (the entry's EXAMPLE). -/
theorem p_four : p 4 = [2, 4, 1, 3] := by
  obtain ⟨h52, h24, h41, h13⟩ := fracPhi_chain
  refine p_eq_of_perm_of_pairwise (by decide) ?_
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, or_false, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith

/-- `p(5) = (5, 2, 4, 1, 3)`, row 5 of A054065. -/
theorem p_five : p 5 = [5, 2, 4, 1, 3] := by
  obtain ⟨h52, h24, h41, h13⟩ := fracPhi_chain
  refine p_eq_of_perm_of_pairwise (by decide) ?_
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, or_false, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith

/-- Ground truth: the first four listed terms `a(2..5) = 1, 3, 7, 10`. -/
theorem a_two_to_five : a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 7 ∧ a 5 = 10 := by
  simp only [a, p_two, p_three, p_four, p_five]
  decide

/-- Ground truth for `sumAbsDiff`: the entry's EXAMPLE row `2 4 1 3` has sum `7`,
and the witness `(3,1,5,2,4)` has sum `2 + 4 + 3 + 2 = 11`. -/
example : sumAbsDiff [2, 4, 1, 3] = 7 ∧ sumAbsDiff [3, 1, 5, 2, 4] = 11 := by decide

/-! ## The refutation -/

/-- **A100056's conjecture is false.**  Counterexample `n = 5`: `p(5) = (5,2,4,1,3)`
gives `a(5) = 3 + 2 + 3 + 2 = 10`, but the permutation `(3,1,5,2,4)` of `1..5` has
`2 + 4 + 3 + 2 = 11 > 10`.  The true maximum is `⌊n²/2⌋ - 1` (for `n ≥ 2`), which
`a(n)` attains only for `n = 2, 3, 4`; the intended claim was presumably that the
golden-ratio permutations are optimal, which already fails at `n = 5`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hmax := (hconj 5 (by norm_num)).2
  have hmem : (11 : ℕ) ∈ {s : ℕ | ∃ l : List ℕ, l.Perm (List.range' 1 5) ∧ s = sumAbsDiff l} :=
    ⟨[3, 1, 5, 2, 4], by decide, by decide⟩
  have hle : 11 ≤ a 5 := hmax hmem
  rw [a_two_to_five.2.2.2] at hle
  omega

end Candidates.A100056Refutation
