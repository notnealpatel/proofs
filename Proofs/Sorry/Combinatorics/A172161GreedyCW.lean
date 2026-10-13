/-
# A172161 — growth of the greedy Coppersmith–Winograd sequence

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A172161` plus `curl "https://oeis.org/search?q=id:A172161&fmt=text"`
(the conjecture is in the **FORMULA** section, which `goof oeis show` does not
expose — that is why it took the raw pull to verify):

```
%N A172161 Greedy Coppersmith-Winograd sequence.
%O A172161 1,3
%A A172161 _Warren D. Smith_, Jan 27 2010
%K A172161 nonn,easy
%F A172161 Conjecture: a(n) ~ k*(3 / 2)^n for some k. - _Bill McEachen_, Dec 02 2022
%F A172161 a(n) = floor((Sum_{i<n} a(i))/2) + 1 for n > 4.
           - _Charles R Greathouse IV_, Dec 02 2022
COMMENTS:
  Coppersmith & Winograd asked for dense sets S of integers such that if A,B,C
  are three disjoint subsets of S, their sums are cannot all be equal. Such sets
  yield new matrix multiplication algorithms. This is the "greedy sequence"
  obeying this property, that is, we start with S = {0, 1} and adjoin new
  integers one at a time, always adjoining the least new integer such that the
  Coppersmith-Winograd property remains valid. It looks as though each term is
  approximately 1.5 times the preceding term. The sequence is clearly infinite
  because each term is no greater than the sum of all previous terms.
  Amazingly, this sequence appears to agree with McRae's sequence A120134 after
  the "3". (This probably can be proved, but I haven't yet.)
  - _Warren D. Smith_, Jan 29 2010
  Considering the A120134 tie-in comment, via the Maiga link, its alternate
  algorithm generates both a(n) and A120134(m) for n >= 1 and m >= 1.
  That algorithm applies b(0)=2, b(1)=2, b(2)=3, b(3)=5, b(4)=8 then
  b(n) = floor(3*b(n-1)/2). Then a(n) = first differences of b(n), while
  A120134(m) begins from b(5) - b(4). - _Bill McEachen_, Dec 02 2022
  This sequence is complete: every positive integer is the sum of a subset of
  its terms. - _Charles R Greathouse IV_, Dec 02 2022
XREFS:
  Cf. A120134.
TERMS: 0,1,2,3,4,6,9,13,20,30,45,67,101,151,227,340,510,765,1148,1722,2583,3874,
       5811,8717,13075,19613,29419,44129,66193,99290,148935,223402,335103,502655,
       753982,1130973,1696460,2544690,3817035,5725552
```

Offset `1`: `a(1) = 0`, `a(2) = 1`, `a(3) = 2`, `a(4) = 3`, `a(5) = 4`,
`a(6) = 6`, `a(7) = 9`, …

Greathouse's recurrence check (for `n > 4`, verified by hand):
`a(5) = ⌊(0+1+2+3)/2⌋ + 1 = 4` ✓; `a(6) = ⌊6/2⌋ + 1 = 4`… **no**:
`⌊(0+1+2+3+4)/2⌋ + 1 = ⌊10/2⌋ + 1 = 6` ✓;
`a(7) = ⌊(0+1+2+3+4+6)/2⌋ + 1 = ⌊16/2⌋ + 1 = 9` ✓;
`a(8) = ⌊25/2⌋ + 1 = 13` ✓; `a(9) = ⌊38/2⌋ + 1 = 20` ✓;
`a(10) = ⌊58/2⌋ + 1 = 30` ✓.

## Current formal status

The OEIS formula line attributes the recurrence to Charles R Greathouse IV,
but supplies neither a proof nor a proof reference. It is not evidence that
Greathouse supplied a proof. The historical quotation above is provenance,
not a novelty or literature-completeness claim.

`Combinatorics.GreedyCWAsymptotic` proves the recurrence from the actual
least-admissible greedy construction and proves the positive quotient limit.
`Combinatorics.A172161Recurrence` defines the recurrence sequence and identifies
it with that construction by strong induction, including all five base indices.
This archive imports those results; all five former admissions are discharged.
The retained name `cwGreedy_eq_recurrence` only unfolds the recurrence definition.
The real semantic bridge is `a172161_eq_greedyA`, not that unfolding theorem.
-/
import Combinatorics.A172161Recurrence

set_option autoImplicit false

namespace Candidates.A172161

/-- No three pairwise disjoint nonempty subsets of a finite set have equal sums.
This is exactly the production greedy construction's convention. -/
def CWProperty (S : Finset ℕ) : Prop :=
  ∀ A ⊆ S, ∀ B ⊆ S, ∀ C ⊆ S, A.Nonempty → B.Nonempty → C.Nonempty →
    Disjoint A B → Disjoint A C → Disjoint B C →
    ¬ (A.sum id = B.sum id ∧ B.sum id = C.sum id)

instance (S : Finset ℕ) : Decidable (CWProperty S) := by unfold CWProperty; infer_instance

/-- The archive and production use the same nonempty-subset CW property. -/
theorem cwProperty_iff (S : Finset ℕ) : CWProperty S ↔ GreedyCW.CWProperty S := Iff.rfl

/-- Adjoin the least new integer preserving the CW property, with candidate
existence explicit so that `Nat.find` does not use a default value. -/
noncomputable def cwGreedyStep (S : Finset ℕ) (h : ∃ m, m ∉ S ∧ CWProperty (insert m S)) :
    Finset ℕ := insert (Nat.find h) S

/-- The archive's `Nat.find` step is the production least-admissible step
whenever the candidate existence premise holds. -/
theorem cwGreedyStep_eq (S : Finset ℕ)
    (h : ∃ m, m ∉ S ∧ CWProperty (insert m S)) :
    cwGreedyStep S h = insert (GreedyCW.greedyNext S) S := by
  unfold cwGreedyStep GreedyCW.greedyNext
  congr 1
  apply (Nat.find_eq_iff h).mpr
  refine ⟨Nat.sInf_mem h, ?_⟩
  intro m hm hmem
  exact (not_lt_of_ge (Nat.sInf_le hmem)) hm

/-! ## Sanity and non-vacuity checks
The offset-0 value is unused but included in both definitions and contributes
zero to range sums. Positive natural denominators and the positive base 3/2
avoid totalized-division artifacts. The guarded recurrence applies at n = 5.
-/

example : List.map a172161 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    = [0, 1, 2, 3, 4, 6, 9, 13, 20, 30] := by
  norm_num [List.map, a172161, Finset.sum_range_succ]

example : List.map a172161 [11, 12, 13, 14, 15, 16]
    = [45, 67, 101, 151, 227, 340] := by
  norm_num [List.map, a172161, Finset.sum_range_succ]

example : (0 + 1 + 2) / 2 + 1 ≠ 3 := by decide
example : 4 < (5 : ℕ) := by decide
example (n : ℕ) : 0 < (3 / 2 : ℝ) ^ n := pow_pos (by norm_num) n

example : CWProperty {0, 1} := by decide
example : CWProperty {0, 1, 2, 3, 4} := by
  exact GreedyCW.greedySet_three ▸ GreedyCW.cwProperty_greedySet 3

example : ¬ CWProperty {0, 1, 2, 3, 4, 5} := by
  intro h
  exact h {1, 4} (by decide) {2, 3} (by decide) {5} (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : CWProperty {0, 1, 2, 3, 4, 6} := by
  have hstep := GreedyCW.greedyNext_spec (GreedyCW.cwProperty_greedySet 3)
  have hnext : GreedyCW.greedyNext (GreedyCW.greedySet 3) = 6 :=
    GreedyCW.greedyA_six
  rw [hnext, GreedyCW.greedySet_three] at hstep
  have hset : insert 6 ({0, 1, 2, 3, 4} : Finset ℕ) = {0, 1, 2, 3, 4, 6} := by decide
  rw [hset] at hstep
  exact hstep.2

example : ∃ m, m ∉ ({0, 1} : Finset ℕ) ∧ CWProperty (insert m {0, 1}) :=
  ⟨2, by decide, by decide⟩

example : ({1, 4} : Finset ℕ).sum id = 5 ∧ ({2, 3} : Finset ℕ).sum id = 5 ∧
    ({5} : Finset ℕ).sum id = 5 := by decide
example : (∅ : Finset ℕ).sum id = 0 ∧ ({0} : Finset ℕ).sum id = 0 := by decide

end Candidates.A172161
