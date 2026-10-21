/-
# A063534 — Mathar's conjecture `A063534 = A001748` (index 2 excepted) is false

## OEIS source (retrieved with `oeis show A063534`, 2026-10-21)

```
NAME:     Numbers k such that C(k) = H(k) + d(k), where C(k) is Chowla's
          function A048050, H(k) is the half-totient function A023022 and
          d(k) is the number of divisors function A000005.
TERMS:    6,8,15,21,33,39,51,57,69,87,93,111,123,129,141,159,177,183,201,213,
          219,237,249,267,291,303,309,321,327,339,381,393,411,417,447,453,...
FORMULA (the conjecture):
  Conjecture: a(n) = A001748(n), n <> 2. - _R. J. Mathar_, Dec 15 2008
FORMULA (later, already recording the failure):
  The conjecture is false. The least counterexample is a(11546) = 368335 =
  5 * 11 * 37 * 181. The next counterexample is 4922335, and there are no
  more below 10^10. - _Amiram Eldar_, Apr 15 2024
```

`A001748(n) = 3 * prime(n)`, so the conjecture says that, apart from the
second term `a(2) = 8`, the members of A063534 are exactly the numbers
`3 * p` with `p` prime (`p ≠ 3`, since `A001748(2) = 9` is the excluded index).

Auxiliary entries (retrieved 2026-10-21):
* A048050 "Chowla's function: sum of divisors of n except for 1 and n",
  terms `0,0,0,2,0,5,0,6,3,7,0,15,...`.
* A023022 "Number of partitions of n into two relatively prime parts. After
  initial term, this is the "half-totient" function phi(n)/2", terms
  `1,1,1,2,1,3,2,3,2,5,2,6,...`, formula `a(n) = phi(n)/2 for n >= 3`.
* A000005 the number of divisors.

## This module

Refutes the conjecture (kernel-checked) at Eldar's least counterexample
`k = 368335 = 5 * 11 * 37 * 181`, which is not divisible by `3` yet satisfies
`C(k) = 129616 = 129600 + 16 = H(k) + d(k)`.  Re-validated in Sage on
2026-10-21: the set statement below fails on `1 ≤ k < 400000` only at
`k = 368335`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A063534Refutation

open scoped Pointwise

/-- Chowla's function (A048050): the sum of the divisors of `k` other than
`1` and `k`.  In particular `chowla 1 = 0` and `chowla p = 0` for `p` prime. -/
def chowla (k : ℕ) : ℕ := ∑ d ∈ k.divisors with d ≠ 1 ∧ d ≠ k, d

/-- The half-totient function as tabulated in A023022 (offset `2`): `a(2) = 1`
(the partition `2 = 1 + 1`) and `φ(k) / 2` for `k ≥ 3`, where `φ(k)` is even so
the division is exact.  The value `1` at `k ≤ 1` lies outside the entry's
domain and is immaterial for A063534: at `k = 1` one has `C(1) = 0 < d(1)`. -/
def halfTotient (k : ℕ) : ℕ := if k ≤ 2 then 1 else k.totient / 2

/-- Membership predicate of A063534: `C(k) = H(k) + d(k)` with `C` Chowla's
function, `H` the half-totient and `d(k)` the number of divisors. -/
def IsA063534 (k : ℕ) : Prop := chowla k = halfTotient k + k.divisors.card

instance : DecidablePred IsA063534 := fun k => by
  unfold IsA063534; infer_instance

/-! ## Ground truth -/

/-- A048050, first twelve terms. -/
example : (List.range 12).map (fun n => chowla (n + 1)) =
    [0, 0, 0, 2, 0, 5, 0, 6, 3, 7, 0, 15] := by decide

/-- A023022, first twelve terms (offset `2`). -/
example : (List.range 12).map (fun n => halfTotient (n + 2)) =
    [1, 1, 1, 2, 1, 3, 2, 3, 2, 5, 2, 6] := by decide

/-- A063534, the terms up to `60`. -/
example : (List.range 61).filter IsA063534 = [6, 8, 15, 21, 33, 39, 51, 57] := by
  decide

/-! ## The conjecture -/

/-- **Mathar's conjecture (A063534, R. J. Mathar, Dec 15 2008).**

Verbatim: "Conjecture: a(n) = A001748(n), n <> 2."

Since `A001748(n) = 3 * prime(n)` and the entry lists `a(2) = 8` (whereas
`A001748(2) = 9`), the indexwise statement is equivalent to the set
statement used here: a positive integer `k` lies in A063534 iff `k = 8` or
`k = 3 * p` for a prime `p ≠ 3`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → (IsA063534 k ↔ k = 8 ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ k = 3 * p)

/-! ## The refutation -/

/-- Divisors of `368335 = 5 * 11 * 37 * 181`, as a pointwise product. -/
lemma divisors_368335 :
    Nat.divisors 368335 = ({1, 5} : Finset ℕ) * ({1, 11} : Finset ℕ) *
      ({1, 37} : Finset ℕ) * ({1, 181} : Finset ℕ) := by
  rw [show (368335 : ℕ) = 5 * 11 * 37 * 181 by norm_num, Nat.divisors_mul,
    Nat.divisors_mul, Nat.divisors_mul, Nat.Prime.divisors (by norm_num),
    Nat.Prime.divisors (by norm_num), Nat.Prime.divisors (by norm_num),
    Nat.Prime.divisors (by norm_num)]

/-- `φ(368335) = 4 * 10 * 36 * 180 = 259200`. -/
lemma totient_368335 : Nat.totient 368335 = 259200 := by
  rw [show (368335 : ℕ) = 5 * 11 * 37 * 181 by norm_num,
    Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_prime (by norm_num)]

/-- `368335` belongs to A063534: `C = 129616`, `H = 129600`, `d = 16`. -/
theorem isA063534_368335 : IsA063534 368335 := by
  have hC : chowla 368335 = 129616 := by
    unfold chowla
    rw [divisors_368335]
    decide
  have hH : halfTotient 368335 = 129600 := by
    unfold halfTotient
    rw [if_neg (by norm_num), totient_368335]
  have hd : (Nat.divisors 368335).card = 16 := by
    rw [divisors_368335]
    decide
  unfold IsA063534
  rw [hC, hH, hd]

/-- **Mathar's conjecture on A063534 is false.**  Counterexample (Eldar,
Apr 15 2024): `k = 368335 = 5 * 11 * 37 * 181` satisfies
`C(k) = H(k) + d(k)` but is neither `8` nor `3 * p` (it is not divisible by
`3`).  The heuristic behind the conjecture — `k = 3p` gives
`C = p + 3`, `H = p - 1`, `d = 4` — is exact for those `k`, so only the
"only if" direction fails; no evident corrected form is recorded. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hmem := (hconj 368335 (by norm_num)).mp isA063534_368335
  rcases hmem with h8 | ⟨p, -, -, hp⟩
  · norm_num at h8
  · omega

end Candidates.A063534Refutation
