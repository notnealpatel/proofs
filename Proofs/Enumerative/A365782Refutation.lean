/-
# A365782 — Bala: `a(n) mod k` has eventual period dividing `phi(k)` (refuted at `k = 4`)

## OEIS source (retrieved with `oeis show A365782`, 2026-10-21)

```
NAME:     Expansion of e.g.f. 1 / (3 - 2 * exp(2*x))^(1/4).
TERMS:    1,1,7,79,1273,26761,694207,21426679,766897873,31228168561,
          1425551226007,72103869999679,4002503339419273,...
FORMULA:  a(n) = Sum_{k=0..n} 2^(n-k) * (Product_{j=0..k-1} (4*j+1))
          * Stirling2(n,k).
FORMULA:  a(0) = 1; a(n) = a(n-1) - 3*Sum_{k=1..n-1} (-2)^k
          * binomial(n-1,k) * a(n-k).
COMMENT (the conjecture):
  Conjecture: the sequence a(n) taken modulo a positive integer k is
  eventually periodic with the period dividing phi(k). For example, the
  sequence taken modulo 21 begins [1, 1, 7, 16, 13, 7, 10, 1, 7, 16, 13, 7,
  10, 1, 7, 16, 13, 7, 10, ...] with an apparent period of 6 (= phi(21)/2)
  starting at n = 1. - _Peter Bala_, Oct 23 2025
```

No later comment in the entry retracts or amends the conjecture.

## Status

This module **refutes** the conjecture.  Modulo `k = 4` the residues of
`a(n)` are `1, 1, 3, 3, 1, 1, 3, 3, ...`, with exact period `4`, while
`phi(4) = 2`.  The proof: in the Stirling closed form every term with
`n - k ≥ 2` carries `2^(n-k) ≡ 0 (mod 4)`, every product
`Product_{j<k} (4j+1)` is `≡ 1 (mod 4)`, and `Stirling2(n, n-1) =
binomial(n, 2)`, so `a(n) ≡ 1 + 2 binomial(n, 2) (mod 4)`.  Since
`binomial(n+2, 2) - binomial(n, 2) = 2n + 1` is odd, `a(n+2) ≡ a(n) + 2
(mod 4)` for every `n`.  A Python check (`n < 400`, moduli `2..129`) found
`k = 4` to be the only failing modulus in that range.

## Definitional fidelity

The sequence is defined by the entry's Stirling-number closed form, a
finite sum of natural numbers (the subtraction `n - k` is guarded by
`k ∈ range (n + 1)`).  It is checked against the first eight listed terms,
and against the entry's independent recurrence
`a(n) = a(n-1) - 3 Sum_{k=1..n-1} (-2)^k binomial(n-1,k) a(n-k)` for the
first eight terms.  The e.g.f. identity itself is not formalized (it is the
entry's own formula, not part of the claim being refuted).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A365782Refutation

/-- A365782 via the entry's closed form
`a(n) = Sum_{k=0..n} 2^(n-k) (Product_{j=0..k-1} (4j+1)) Stirling2(n,k)`.
The natural subtraction `n - k` is guarded by `k ∈ range (n + 1)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    2 ^ (n - k) * (∏ j ∈ Finset.range k, (4 * j + 1)) * n.stirlingSecond k

/-- The entry's recurrence `a(0) = 1`,
`a(n) = a(n-1) - 3 Sum_{k=1..n-1} (-2)^k binomial(n-1,k) a(n-k)`, written for
`n + 1` with the summation index shifted by one; used only as an independent
cross-check of `a`. -/
def aRec : ℕ → ℤ
  | 0 => 1
  | n + 1 => aRec n - 3 * ∑ k : Fin n,
      (-2 : ℤ) ^ (k.val + 1) * (n.choose (k.val + 1) : ℤ) * aRec (n - k.val)
decreasing_by all_goals omega

/-! ## Ground truth against the listed terms -/

example : a 0 = 1 := by decide
example : a 1 = 1 := by decide
example : a 2 = 7 := by decide
example : a 3 = 79 := by decide
example : a 4 = 1273 := by decide
example : a 5 = 26761 := by decide
example : a 6 = 694207 := by decide
example : a 7 = 21426679 := by decide

example : aRec 0 = 1 := by norm_num [aRec]
example : aRec 1 = 1 := by norm_num [aRec]
example : aRec 2 = 7 := by norm_num [aRec, Fin.sum_univ_succ, Nat.choose]
example : aRec 3 = 79 := by norm_num [aRec, Fin.sum_univ_succ, Nat.choose]
example : aRec 7 = 21426679 := by norm_num [aRec, Fin.sum_univ_succ, Nat.choose]


/-! ## The conjecture -/

/-- **Bala's conjecture (A365782, Peter Bala, Oct 23 2025).**

Verbatim: "Conjecture: the sequence a(n) taken modulo a positive integer k is
eventually periodic with the period dividing phi(k)."

Formalized: for every `k > 0` there is a positive period `p ∣ φ(k)` and a
threshold `N` with `a(n + p) ≡ a(n) (mod k)` for all `n ≥ N`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + p) ≡ a n [MOD k]

/-! ## Residues modulo 4 -/

/-- Every product `Product_{j<k} (4j+1)` is `1` modulo 4. -/
theorem prod_four_mul_add_one_cast (k : ℕ) :
    (∏ j ∈ Finset.range k, (4 * (j : ZMod 4) + 1)) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  have h4 : (4 : ZMod 4) = 0 := rfl
  rw [h4, zero_mul, zero_add]

/-- Modulo 4 only the top two Stirling terms survive:
`a(n) ≡ 1 + 2 binomial(n, 2) (mod 4)`. -/
theorem a_cast_zmod_four (n : ℕ) :
    (a n : ZMod 4) = 1 + 2 * (n.choose 2 : ZMod 4) := by
  cases n with
  | zero => decide
  | succ m =>
    have hlow : ∀ k ∈ Finset.range m,
        (((2 ^ (m + 1 - k) * (∏ j ∈ Finset.range k, (4 * j + 1)) *
          (m + 1).stirlingSecond k : ℕ)) : ZMod 4) = 0 := by
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      have hexp : m + 1 - k = (m - 1 - k) + 2 := by omega
      have h22 : (2 : ZMod 4) ^ 2 = 0 := rfl
      push_cast
      rw [hexp, pow_add, h22, mul_zero, zero_mul, zero_mul]
    rw [a, Nat.cast_sum, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero hlow, Nat.stirlingSecond_self,
      Nat.stirlingSecond_succ_self_left, Nat.sub_self,
      show m + 1 - m = 1 by omega]
    push_cast
    rw [prod_four_mul_add_one_cast, prod_four_mul_add_one_cast]
    ring

/-- Two steps add `2` modulo 4: `a(n+2) ≡ a(n) + 2 (mod 4)`. -/
theorem a_add_two_cast (n : ℕ) : (a (n + 2) : ZMod 4) = a n + 2 := by
  have hchoose : (n + 2).choose 2 = n.choose 2 + 2 * n + 1 := by
    rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_succ_succ n 1,
      Nat.choose_one_right, Nat.choose_one_right]
    ring
  have h4 : (4 : ZMod 4) = 0 := rfl
  rw [a_cast_zmod_four, a_cast_zmod_four, hchoose]
  push_cast
  linear_combination (n : ZMod 4) * h4

/-- For every `n`, `a(n+2) ≢ a(n) (mod 4)`: no period dividing `phi(4) = 2`
holds anywhere in the sequence. -/
theorem a_add_two_not_modEq (n : ℕ) : ¬ a (n + 2) ≡ a n [MOD 4] := by
  intro h
  have hcast : (a (n + 2) : ZMod 4) = a n :=
    (ZMod.natCast_eq_natCast_iff _ _ 4).mpr h
  rw [a_add_two_cast] at hcast
  have h2 : (2 : ZMod 4) = 0 := by
    linear_combination hcast
  exact absurd h2 (by decide)

/-- The sequence is purely periodic modulo 4 with period 4:
`a(n+4) ≡ a(n) (mod 4)` (residues `1, 1, 3, 3, ...`). -/
theorem a_add_four_modEq (n : ℕ) : a (n + 4) ≡ a n [MOD 4] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have h4 : (4 : ZMod 4) = 0 := rfl
  rw [show n + 4 = n + 2 + 2 by omega, a_add_two_cast, a_add_two_cast]
  linear_combination h4

/-! ## The refutation -/

/-- **Bala's A365782 conjecture is false**, with counterexample modulus
`k = 4`.  Here `phi(4) = 2`, so the only admissible periods are `1` and `2`,
and either would give `a(n+2) ≡ a(n) (mod 4)` for large `n`; but
`a(n+2) ≡ a(n) + 2 (mod 4)` for every `n`.  The true period modulo 4 is `4`
(`a_add_four_modEq`).  Computation over moduli `2..129` finds `4` as the only
exception, so the author probably intended the claim for moduli `k ≠ 4` (or
with period dividing `2 phi(k)` at `k = 4`). -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨p, hp, hpd, N, hN⟩ := h 4 (by norm_num)
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hpd
  have hp2 : p = 1 ∨ p = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hpd
    interval_cases p <;> simp_all
  have hper2 : a (N + 2) ≡ a N [MOD 4] := by
    rcases hp2 with rfl | rfl
    · exact (hN (N + 1) (by omega)).trans (hN N le_rfl)
    · exact hN N le_rfl
  exact a_add_two_not_modEq N hper2

end Candidates.A365782Refutation
