/-
Refutation of Mathar's A063534 conjecture (R. J. Mathar, Dec 15 2008).

The sequence consists of k with C(k)=H(k)+d(k): Chowla's function A048050,
half-totient A023022 and divisor count A000005. The proposed equality with
A001748 (three times primes), except at the second index, is refuted by
k=368335=5*11*37*181: C(k)=129616=129600+16=H(k)+d(k), but 3 does not divide k.
This counterexample is recorded by Amiram Eldar (Apr 15 2024).
The formal refutation is of the value-set statement; it does not establish
the counterexample's position in an increasing enumeration.
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

/-! ## Examples -/

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

/-- The value-set reading of Mathar's indexed conjecture: a positive member
is `8` or `3p` for prime `p≠3`. The source proposes equality with A001748
except at index `2`; no formal enumeration bridge is supplied here. -/
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

/-- Mathar's A063534 value-set conjecture is false: Eldar's counterexample
`368335 = 5*11*37*181` satisfies `C(k)=H(k)+d(k)` but is neither `8` nor
three times a prime. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hmem := (hconj 368335 (by norm_num)).mp isA063534_368335
  rcases hmem with h8 | ⟨p, -, -, hp⟩
  · norm_num at h8
  · omega

end Candidates.A063534Refutation
