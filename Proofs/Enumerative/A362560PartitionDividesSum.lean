/-
# A362560 — Wiseman: weighted-sum divisibility is reversal invariant

## OEIS source (`oeis show A362560`, live entry https://oeis.org/A362560,
## retrieved 2026-10-21)

```
NAME:     Number of integer partitions of n whose weighted sum is not
          divisible by n.
OFFSET:   1,4
TERMS:    0,1,1,4,5,8,12,19,25,38,51,70,93,124,162,217,279,360,462,601,...
COMMENT:  The (one-based) weighted sum of a sequence (y_1,...,y_k) is
          Sum_{i=1..k} i*y_i. This is also the sum of partial sums of the
          reverse.
COMMENT (the conjecture):
          Conjecture: A partition of n has weighted sum divisible by n iff its
          reverse has weighted sum divisible by n.
EXAMPLE:  The weighted sum of y = (3,3,1) is 1*3+2*3+3*1 = 12, which is not a
          multiple of 7, so y is counted under a(7).
AUTHOR:   Gus Wiseman, Apr 28 2023
MATHEMATICA: Table[Length[Select[IntegerPartitions[n],
          !Divisible[Total[Accumulate[Reverse[#]]],n]&]],{n,30}]
```

The conjecture comment carries no separate signature; the entry (and hence the
comment) is by Gus Wiseman, Apr 28 2023.  `IntegerPartitions` lists parts in
weakly decreasing order, so `y = (y_1 ≥ ... ≥ y_k)`.

## Status

Triage: "open" in the sense that the entry still labels it a conjecture and no
proof was found in the entry or the literature.  It is in fact immediate: the
weighted sum of the reverse is `Sum_i (k+1-i)*y_i = (k+1)*n - W`, which is
`≡ -W (mod n)`.  This module proves it.

Computation (2026-10-21, python, all partitions of `n ≤ 30`): no partition
violates the equivalence, and the count of partitions with `n ∤ W` reproduces
the 30 listed terms exactly.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A362560PartitionDividesSum

/-! ## Definition layer -/

/-- The one-based weighted sum `Sum_{i=1..k} i * y_i` of a list `y = (y_1,...,y_k)`,
written zero-based as `∑_{i < k} (i + 1) * y[i]`. -/
def weightedSum (y : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range y.length, (i + 1) * y.getD i 0

/-- The parts of a partition of `n` listed in weakly decreasing order
`y_1 ≥ y_2 ≥ ... ≥ y_k`, as in Mathematica's `IntegerPartitions`. -/
def decreasingParts {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (fun a b => b ≤ a)

/-- The partition `(3,3,1)` of `7` from the entry's EXAMPLE. -/
def partition331 : Nat.Partition 7 :=
  ⟨(([1, 3, 3] : List ℕ) : Multiset ℕ), by decide, by decide⟩

/-- Ground truth: the decreasing listing of the multiset `{1,3,3}` is `(3,3,1)`. -/
example : decreasingParts partition331 = [3, 3, 1] := by
  rw [decreasingParts, partition331, Multiset.coe_sort, List.mergeSort_eq_insertionSort]
  decide

/-- Ground truth from the EXAMPLE: the weighted sum of `(3,3,1)` is
`1*3 + 2*3 + 3*1 = 12`. -/
example : weightedSum [3, 3, 1] = 12 := by decide

/-- Ground truth: `7 ∤ 12`, so `(3,3,1)` is counted under `a(7)`. -/
example : ¬ 7 ∣ weightedSum (decreasingParts partition331) := by
  rw [decreasingParts, partition331, Multiset.coe_sort, List.mergeSort_eq_insertionSort]
  decide

/-- Ground truth for the reverse: `weightedSum (1,3,3) = 1 + 6 + 9 = 16`, and
`12 + 16 = (3 + 1) * 7`. -/
example : weightedSum [1, 3, 3] = 16 := by decide

/-! ## Helper lemmas -/

/-- A list sum written as a `Finset.range` sum of `getD`. -/
theorem sum_eq_sum_range_getD (l : List ℕ) :
    l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', List.getD_cons_zero, ih]
    simp only [List.getD_cons_succ]
    rw [add_comm]

/-- Prepending `a` adds the full sum once: `W(a :: l) = sum (a :: l) + W(l)`. -/
theorem weightedSum_cons (a : ℕ) (l : List ℕ) :
    weightedSum (a :: l) = (a :: l).sum + weightedSum l := by
  rw [weightedSum, weightedSum, List.length_cons, Finset.sum_range_succ', List.sum_cons]
  simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add, one_mul]
  have hsplit : ∑ i ∈ Finset.range l.length, (i + 1 + 1) * l.getD i 0 =
      ∑ i ∈ Finset.range l.length, l.getD i 0 +
        ∑ i ∈ Finset.range l.length, (i + 1) * l.getD i 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, ← sum_eq_sum_range_getD]
  ring

/-- Appending `a` at position `k + 1` adds `(k + 1) * a`. -/
theorem weightedSum_append_singleton (l : List ℕ) (a : ℕ) :
    weightedSum (l ++ [a]) = weightedSum l + (l.length + 1) * a := by
  rw [weightedSum, weightedSum, List.length_append, List.length_singleton,
    Finset.sum_range_succ, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
    List.getD_cons_zero]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]

/-- The key identity: `W(y) + W(reverse y) = (k + 1) * (y_1 + ... + y_k)`. -/
theorem weightedSum_add_weightedSum_reverse (l : List ℕ) :
    weightedSum l + weightedSum l.reverse = (l.length + 1) * l.sum := by
  induction l with
  | nil => simp [weightedSum]
  | cons a l ih =>
    rw [List.reverse_cons, weightedSum_append_singleton, weightedSum_cons,
      List.length_reverse, List.length_cons, List.sum_cons]
    linear_combination ih

/-- The weighted sum of the reverse is the entry's `Sum_{i=1..k} (k+1-i) * y_i`,
written zero-based as `∑_{i < k} (k - i) * y[i]` (here `i < k`, so the natural
subtraction is exact). -/
theorem weightedSum_reverse_eq (l : List ℕ) :
    weightedSum l.reverse = ∑ i ∈ Finset.range l.length, (l.length - i) * l.getD i 0 := by
  have hS : weightedSum l + ∑ i ∈ Finset.range l.length, (l.length - i) * l.getD i 0 =
      (l.length + 1) * l.sum := by
    rw [weightedSum, ← Finset.sum_add_distrib, sum_eq_sum_range_getD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < l.length := Finset.mem_range.mp hi
    rw [← add_mul]
    congr 1
    omega
  have hR := weightedSum_add_weightedSum_reverse l
  omega

/-- Divisibility by the total is reversal invariant for any list of naturals
with sum `n`: `n ∣ W(y) ↔ n ∣ W(reverse y)`. -/
theorem dvd_weightedSum_iff_dvd_weightedSum_reverse (l : List ℕ) (n : ℕ) (hl : l.sum = n) :
    n ∣ weightedSum l ↔ n ∣ weightedSum l.reverse := by
  have hsum : weightedSum l + weightedSum l.reverse = (l.length + 1) * n := by
    rw [weightedSum_add_weightedSum_reverse, hl]
  have htot : n ∣ weightedSum l + weightedSum l.reverse := hsum ▸ dvd_mul_left n _
  constructor
  · intro hW
    exact (Nat.dvd_add_right hW).mp htot
  · intro hR
    exact (Nat.dvd_add_left hR).mp htot

/-! ## The conjecture -/

/-- **Wiseman's conjecture (A362560, Gus Wiseman, Apr 28 2023), proved.**

Verbatim: "Conjecture: A partition of n has weighted sum divisible by n iff its
reverse has weighted sum divisible by n."

For every `n` and every partition `p` of `n`, listed in weakly decreasing order
as `y = (y_1 ≥ ... ≥ y_k)`, `n` divides the one-based weighted sum
`Sum_i i * y_i` iff `n` divides the weighted sum of the reversed list. -/
theorem a362560_conjecture (n : ℕ) (p : Nat.Partition n) :
    n ∣ weightedSum (decreasingParts p) ↔ n ∣ weightedSum (decreasingParts p).reverse := by
  have hsum : (decreasingParts p).sum = n := by
    rw [decreasingParts, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]
  exact dvd_weightedSum_iff_dvd_weightedSum_reverse _ n hsum

/-- The conjecture in the triage's literal form: with `y = (y_1 ≥ ... ≥ y_k)`
the decreasing parts of a partition of `n`, `n ∣ Sum_{i=1..k} i * y_i` iff
`n ∣ Sum_{i=1..k} (k+1-i) * y_i` (both sums written zero-based). -/
theorem a362560_conjecture_explicit (n : ℕ) (p : Nat.Partition n) :
    let y := decreasingParts p
    n ∣ ∑ i ∈ Finset.range y.length, (i + 1) * y.getD i 0 ↔
      n ∣ ∑ i ∈ Finset.range y.length, (y.length - i) * y.getD i 0 := by
  intro y
  rw [← weightedSum_reverse_eq]
  exact a362560_conjecture n p

end Candidates.A362560PartitionDividesSum
