/-
# A029795 — refutation of Greathouse's "eventually a(n) = m + n" conjecture

## OEIS source (retrieved 2026-10-21 with `oeis show A029795`; offset from
the live entry `%O 1,3`)

```
A029795   Numbers k such that k and k^3 have the same set of digits.
OFFSET:   1
TERMS:    0,1,10,100,1000,10000,100000,107624,109573,132485,138624,159406,
          165640,192574,205738,215806,251894,281536,318725,419375,427863,
          568314,642510,713960,953867,954086,963218,965760,1000000,1008529,
          1023479
COMMENT:  Conjecture: there exists some m and N for which a(n) = m + n for
          all n >= N. - _Charles R Greathouse IV_, Jun 28 2011
```

This is the only comment in the entry; no later comment retracts the
conjecture.  The sibling entry A029797 (`k^2` and `k^3`) carries the identical
conjecture together with David A. Corneth's refutation (Nov 13 2023).

## Status

This module refutes the conjecture.  If `a(n) = m + n` for all `n ≥ N`, then
consecutive terms of the sequence are consecutive integers from `a(N)` on, so
every integer `k ≥ a(N)` belongs to the sequence.  But for every `e`, the
number `k = 2 * 10^e` has digit set `{0, 2}` (or `{2}`) while
`k^3 = 8 * 10^(3e)` has digit set `{0, 8}` (or `{8}`), so `k` is never a term.
A Python recheck (2026-10-21) confirms the 31 listed terms and the exclusion
of `2 * 10^e` for `1 ≤ e ≤ 39`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A029795Refutation

/-! ## Definition layer -/

/-- `k` and `k^3` have the same set of decimal digits.  (`Nat.digits 10 0 = []`,
so `0` qualifies, matching the first listed term.) -/
def SameDigitsCube (k : ℕ) : Prop :=
  (Nat.digits 10 k).toFinset = (Nat.digits 10 (k ^ 3)).toFinset

/-- `SameDigitsCube` is decided by comparing finite digit sets. -/
instance : DecidablePred SameDigitsCube := fun k =>
  inferInstanceAs
    (Decidable ((Nat.digits 10 k).toFinset = (Nat.digits 10 (k ^ 3)).toFinset))

/-- A029795(n), with the OEIS offset `1`: the `n`-th number `k` (counting
from `n = 1`) such that `k` and `k^3` have the same set of digits.
Meaningful for `1 ≤ n`; the conjecture below only uses such `n`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth SameDigitsCube (n - 1)

/-- The value of `a` at an index, from a count of smaller members. -/
theorem a_eq {n k : ℕ} (hk : SameDigitsCube k) (hc : Nat.count SameDigitsCube k + 1 = n) :
    a n = k := by
  subst hc
  simp only [a, Nat.add_sub_cancel]
  exact Nat.nth_count hk

/-! ## Ground truth: the first listed terms `0, 1, 10, 100, 1000` -/

example : a 1 = 0 := a_eq (by decide) (by decide +kernel)
example : a 2 = 1 := a_eq (by decide) (by decide +kernel)
example : a 3 = 10 := a_eq (by decide) (by decide +kernel)
example : a 4 = 100 := a_eq (by decide) (by decide +kernel)
example : a 5 = 1000 := a_eq (by decide +kernel) (by decide +kernel)

/-! ## The two digit families -/

/-- Every power of ten `10^e` is a term: `10^e` and `10^(3e)` both have digit
set `{0, 1}` (or `{1}` when `e = 0`). -/
theorem sameDigitsCube_ten_pow (e : ℕ) : SameDigitsCube (10 ^ e) := by
  have h1 : Nat.digits 10 (10 ^ e) = List.replicate e 0 ++ [1] := by
    simpa using Nat.digits_base_pow_mul (b := 10) (k := e) (m := 1) (by norm_num) (by norm_num)
  have h3 : Nat.digits 10 ((10 ^ e) ^ 3) = List.replicate (3 * e) 0 ++ [1] := by
    rw [← pow_mul, mul_comm e 3]
    simpa using
      Nat.digits_base_pow_mul (b := 10) (k := 3 * e) (m := 1) (by norm_num) (by norm_num)
  unfold SameDigitsCube
  rw [h1, h3]
  ext x
  simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, List.mem_replicate,
    List.mem_singleton]
  omega

/-- No number `2 * 10^e` is a term: its digit set contains `2`, while its cube
`8 * 10^(3e)` has digit set `{0, 8}` (or `{8}`). -/
theorem not_sameDigitsCube_two_mul_ten_pow (e : ℕ) : ¬ SameDigitsCube (10 ^ e * 2) := by
  have h1 : Nat.digits 10 (10 ^ e * 2) = List.replicate e 0 ++ [2] :=
    Nat.digits_base_pow_mul (by norm_num) (by norm_num)
  have h3 : Nat.digits 10 ((10 ^ e * 2) ^ 3) = List.replicate (3 * e) 0 ++ [8] := by
    have hcube : (10 ^ e * 2) ^ 3 = 10 ^ (3 * e) * 8 := by ring
    rw [hcube]
    exact Nat.digits_base_pow_mul (by norm_num) (by norm_num)
  intro h
  unfold SameDigitsCube at h
  rw [h1, h3] at h
  have h2mem : (2 : ℕ) ∈ (List.replicate e 0 ++ [2]).toFinset := by simp
  rw [h] at h2mem
  simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, List.mem_replicate,
    List.mem_singleton] at h2mem
  omega

/-- The set of terms is infinite (it contains every power of ten). -/
theorem infinite_ofPred_sameDigitsCube : (Set.ofPred SameDigitsCube).Infinite :=
  Set.infinite_of_injective_forall_mem (Nat.pow_right_injective (by norm_num : 2 ≤ 10))
    sameDigitsCube_ten_pow

/-- Not every sufficiently large integer `k` has the same digit set as `k^3`:
for every bound `K`, the number `2 * 10^K ≥ K` fails. -/
theorem not_eventually_sameDigitsCube :
    ¬ ∃ K : ℕ, ∀ k, K ≤ k → SameDigitsCube k := by
  rintro ⟨K, hK⟩
  have hle : K ≤ 10 ^ K * 2 := by
    have hlt : K < 10 ^ K := Nat.lt_pow_self (by norm_num)
    omega
  exact not_sameDigitsCube_two_mul_ten_pow K (hK _ hle)

/-! ## The conjecture -/

/-- **Greathouse's conjecture in A029795 (Jun 28 2011).** Verbatim:
"Conjecture: there exists some m and N for which a(n) = m + n for all
n >= N."  The shift `m` is taken in `ℤ` (the most permissive reading), and
`n` ranges over the valid indices `1 ≤ n` of the offset-`1` sequence. -/
def Conjecture : Prop :=
  ∃ m : ℤ, ∃ N : ℕ, ∀ n, 1 ≤ n → N ≤ n → (a n : ℤ) = m + n

/-- The conjecture implies that every integer from some point on is a term:
from index `N + 1` on, consecutive terms are consecutive integers. -/
theorem eventually_sameDigitsCube_of_conjecture (h : Conjecture) :
    ∃ K : ℕ, ∀ k, K ≤ k → SameDigitsCube k := by
  obtain ⟨m, N, hN⟩ := h
  refine ⟨a (N + 1), fun k hk => ?_⟩
  have hbase : (a (N + 1) : ℤ) = m + (N + 1 : ℕ) := hN (N + 1) (by omega) (by omega)
  have hstep : (a (N + 1 + (k - a (N + 1))) : ℤ) = m + (N + 1 + (k - a (N + 1)) : ℕ) :=
    hN _ (by omega) (by omega)
  have hval : a (N + 1 + (k - a (N + 1))) = k := by
    push_cast at hbase hstep
    omega
  rw [← hval]
  exact Nat.nth_mem_of_infinite infinite_ofPred_sameDigitsCube _

/-- **The A029795 conjecture is false.**  Counterexample family: for every
`e`, `2 * 10^e` has digit set `{0, 2}` while its cube `8 * 10^(3e)` has digit
set `{0, 8}`, so `2 * 10^e` is never a term, whereas the conjecture forces
every integer `≥ a(N + 1)` to be a term.  Greathouse probably intended the
density statement that almost all integers are terms (`a(n) ~ n`, since
almost all `k` and `k^3` contain all ten digits); that form is not proved
here. -/
theorem conjecture_false : ¬ Conjecture := fun h =>
  not_eventually_sameDigitsCube (eventually_sameDigitsCube_of_conjecture h)

end Candidates.A029795Refutation
