/-
# A364906 — refutation of Wiseman's positions-of-ones conjecture

## OEIS source (retrieved with `oeis show A364906` and checked against
## https://oeis.org/A364906, 2026-10-21)

```
NAME:     Number of ways to write A056239(n) as a nonnegative linear
          combination of the multiset of prime indices of n.
TERMS:    1,1,1,3,1,2,1,10,3,2,1,9,1,2,1,35,1,6,1,9,2,2,1,34,3,2,10,10,1,7,
          1,126,1,2,1,30,1,2,2,39,1,6,1,11,3,2,1,130,3,6,1,12,1,20,1,46,...
AUTHOR:   Gus Wiseman, Aug 22 2023
COMMENT (the conjecture; the line carries no separate attribution, so it
         is the author's, Gus Wiseman, Aug 22 2023):
  Conjecture: Positions of 1's are numbers whose distinct divisors all have
  different GCDs of prime indices, listed by A319319, counted by A319318.
XREF:     Positions of 1's appear to be A319319.
MATHEMATICA:
  prix[n_]:=If[n==1,{},Flatten[Cases[FactorInteger[n],{p_,k_}:>Table[PrimePi[p],{k}]]]];
  combs[n_,y_]:=With[{s=Table[{k,i},{k,y},{i,0,Floor[n/k]}]},
    Select[Tuples[s],Total[Times@@@#]==n&]];
  Table[Length[combs[Total[prix[n]],prix[n]]],{n,100}]
```

A319319: "Heinz numbers of integer partitions such that every distinct
submultiset has a different GCD." (Mathematica:
`UnsameQ@@GCD@@@Union[Subsets[primeMS[#]]]`.)

No later comment or extension of A364906 retracts the conjecture.

## Status

This module **refutes** the conjecture.  The counterexample is
`n = 1547 = 7 * 13 * 17`, with prime indices `{4, 6, 7}` and sum `17`.
The equation `4a + 6b + 7c = 17` has the unique solution `(1, 1, 1)`, so
`A364906(1547) = 1`, but `gcd(4, 7) = gcd(6, 7) = 1`, so `1547` is not in
A319319.  A bounded Python search finds `1547` as the least disagreement;
there are 79 disagreements below `20000`, all with exactly three prime
indices, and all of them have `A364906(n) = 1` with `n ∉ A319319`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A364906Refutation

/-! ## Definition layer -/

/-- The prime indices of `n`, listed in weakly increasing order with
multiplicity (row `n` of A112798; Mathematica `prix`).  The index of a prime
`p` is `π(p) = Nat.primeCounting p`, so `prime(m)` has index `m`. -/
def primeIndices (n : ℕ) : List ℕ :=
  n.primeFactorsList.map Nat.primeCounting

/-- The number of ways to write `∑ y_i` as a nonnegative linear combination
`∑ c_i y_i` of the list `y` (Mathematica `Length[combs[Total[y], y]]`):
coefficient `c_i` ranges over `0, …, ⌊(∑ y) / y_i⌋`, exactly as in the
entry's program.  For positive entries `y_i` this bound loses no solution. -/
def countCombs (y : List ℕ) : ℕ :=
  ((Fintype.piFinset fun i : Fin y.length => Finset.range (y.sum / y.get i + 1)).filter
    fun c => ∑ i, c i * y.get i = y.sum).card

/-- `A364906(n)`: the number of ways to write `A056239(n)`, the sum of the
prime indices of `n`, as a nonnegative linear combination of the prime
indices of `n`. -/
def a (n : ℕ) : ℕ :=
  countCombs (primeIndices n)

/-- Membership in A319319: distinct submultisets of the prime indices of `n`
have distinct GCDs (the GCD of the empty submultiset is `0`, as in
Mathematica's `GCD[]`). -/
def InA319319 (n : ℕ) : Prop :=
  ∀ s t : Multiset ℕ, s ≤ (primeIndices n : Multiset ℕ) → t ≤ (primeIndices n : Multiset ℕ) →
    s.gcd = t.gcd → s = t

/-- `InA319319` restated over the (finite) powerset, which makes it decidable. -/
theorem inA319319_iff_powerset (n : ℕ) :
    InA319319 n ↔ ∀ s ∈ (primeIndices n : Multiset ℕ).powerset,
      ∀ t ∈ (primeIndices n : Multiset ℕ).powerset, s.gcd = t.gcd → s = t := by
  simp only [InA319319, Multiset.mem_powerset]
  exact ⟨fun h s hs t ht => h s t hs ht, fun h s t hs ht => h s hs t ht⟩

/-- Decidability of `InA319319` through the powerset form. -/
instance (n : ℕ) : Decidable (InA319319 n) :=
  decidable_of_iff _ (inA319319_iff_powerset n).symm

/-! ## Ground truth -/

example : primeIndices 1 = [] := by
  simp [primeIndices]

example : primeIndices 12 = [1, 1, 2] := by
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide

/-- The prime indices of the counterexample `1547 = 7 * 13 * 17`. -/
theorem primeIndices_1547 : primeIndices 1547 = [4, 6, 7] := by
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide

/-- Shorthand tactic for evaluating `a n` at a numeral: factor `n` with the
`Nat.primeFactorsList` simproc, then decide the bounded count. -/
macro "a_eval" : tactic =>
  `(tactic| (simp only [a, primeIndices, Nat.primeFactorsList_ofNat, List.map_cons,
      List.map_nil]; decide))

-- The first 24 terms of the DATA line.
example : a 1 = 1 := by
  simp only [a, primeIndices, Nat.primeFactorsList_one, List.map_nil]
  decide
example : a 2 = 1 := by a_eval
example : a 3 = 1 := by a_eval
example : a 4 = 3 := by a_eval
example : a 5 = 1 := by a_eval
example : a 6 = 2 := by a_eval
example : a 7 = 1 := by a_eval
example : a 8 = 10 := by a_eval
example : a 9 = 3 := by a_eval
example : a 10 = 2 := by a_eval
example : a 11 = 1 := by a_eval
example : a 12 = 9 := by a_eval
example : a 13 = 1 := by a_eval
example : a 14 = 2 := by a_eval
example : a 15 = 1 := by a_eval
example : a 16 = 35 := by a_eval
example : a 17 = 1 := by a_eval
example : a 18 = 6 := by a_eval
example : a 19 = 1 := by a_eval
example : a 20 = 9 := by a_eval
example : a 21 = 2 := by a_eval
example : a 22 = 2 := by a_eval
example : a 23 = 1 := by a_eval
example : a 24 = 34 := by a_eval

-- A319319 membership against its DATA line `1, 2, 3, 5, 7, 11, 13, 15, 17, …`
-- (`4, 6, 8, 9, 10, 12, 14, 16` are absent).
example : InA319319 2 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 3 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 5 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 7 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 11 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 13 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 15 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : InA319319 17 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 4 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 6 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 8 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 9 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 10 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 12 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 14 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide
example : ¬ InA319319 16 := by
  rw [inA319319_iff_powerset]
  simp only [primeIndices, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil]
  decide

/-! ## The conjecture -/

/-- **Wiseman's conjecture (A364906, Gus Wiseman, Aug 22 2023).**

Verbatim: "Conjecture: Positions of 1's are numbers whose distinct divisors
all have different GCDs of prime indices, listed by A319319, counted by
A319318."

Formally: for every positive `n`, `A364906(n) = 1` iff `n ∈ A319319`.  The
divisors of `n` correspond bijectively to the submultisets of the prime
indices of `n`, so "distinct divisors have different GCDs of prime indices"
is exactly `InA319319 n`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → (a n = 1 ↔ InA319319 n)

/-! ## The refutation -/

/-- `A364906(1547) = 1`: `4a + 6b + 7c = 17` has only the solution
`(1, 1, 1)`. -/
theorem a_1547 : a 1547 = 1 := by
  rw [a, primeIndices_1547]
  decide

/-- `1547 ∉ A319319`: the distinct submultisets `{4, 7}` and `{6, 7}` of the
prime indices `{4, 6, 7}` both have GCD `1`. -/
theorem not_inA319319_1547 : ¬ InA319319 1547 := by
  intro hmem
  have hsub₁ : ({4, 7} : Multiset ℕ) ≤ (primeIndices 1547 : Multiset ℕ) := by
    rw [primeIndices_1547]
    decide
  have hsub₂ : ({6, 7} : Multiset ℕ) ≤ (primeIndices 1547 : Multiset ℕ) := by
    rw [primeIndices_1547]
    decide
  have hgcd : ({4, 7} : Multiset ℕ).gcd = ({6, 7} : Multiset ℕ).gcd := by
    decide
  have hne : ({4, 7} : Multiset ℕ) ≠ {6, 7} := by
    decide
  exact hne (hmem _ _ hsub₁ hsub₂ hgcd)

/-- **Wiseman's A364906 conjecture is false.**  Counterexample:
`n = 1547 = 7 * 13 * 17`, prime indices `{4, 6, 7}`.  Then `A364906(1547) = 1`
(`a_1547`) but `1547 ∉ A319319` because `gcd(4, 7) = gcd(6, 7) = 1`
(`not_inA319319_1547`).

Only the direction `A364906(n) = 1 → n ∈ A319319` fails: a bounded search
(evidence, not proof) finds no `n < 20000` in A319319 with `A364906(n) ≠ 1`,
and every disagreement below `20000` has exactly three prime indices.  The
intended statement was probably the inclusion `A319319 ⊆ {n : A364906(n) = 1}`;
that inclusion is not proved here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  exact not_inA319319_1547 ((hconj 1547 (by norm_num)).mp a_1547)

end Candidates.A364906Refutation
