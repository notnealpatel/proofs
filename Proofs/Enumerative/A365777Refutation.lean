/-
# A365777 — Bala: `a(n) mod k` has eventual period dividing `phi(k)` (refuted at `k = 4`)

## OEIS source (retrieved with `oeis show A365777`, 2026-10-21)

```
NAME:     Expansion of e.g.f. (exp(2*x) / (2 - exp(2*x)))^(3/4).
TERMS:    1,3,15,117,1257,17163,284055,5522877,123344817,3111071283,
          87454712895,2710961144037,91862770847577,3378032307195003,...
FORMULA:  a(n) = Sum_{k=0..n} (-2)^(n-k) * (Product_{j=0..k-1} (4*j+3))
          * Stirling2(n,k).
FORMULA:  a(0) = 1; a(n) = 3*a(n-1) + Sum_{k=1..n-1} 2^k * binomial(n-1,k)
          * a(n-k).
COMMENT (the conjecture):
  Conjecture: the sequence a(n) taken modulo a positive integer k is
  eventually periodic with the period dividing phi(k). For example, the
  sequence taken modulo 21 begins [1, 3, 15, 12, 18, 6, 9, 3, 15, 12, 18, 6,
  9, 3, 15, 12, 18, 6, 9, ...] with an apparent period of 6 (= phi(21)/2)
  starting at n = 1. - _Peter Bala_, Oct 23 2025
```

No later comment in the entry retracts or amends the conjecture.

## Status

This module **refutes** the conjecture.  Modulo `k = 4` the residues of
`a(n)` are `1, 3, 3, 1, 1, 3, 3, 1, ...`, with exact period `4`, while
`phi(4) = 2`.  The proof: every term of the recurrence with `k ≥ 2` carries
a factor `2^k ≡ 0 (mod 4)`, so `a(n+1) ≡ (2n+3) a(n) (mod 4)`, hence
`a(n+2) ≡ 3 a(n) (mod 4)`; since every `a(n)` is odd, `a(n+2) ≢ a(n)
(mod 4)` for all `n`.  A Python check (`n < 200`, moduli `1..129`) found
`k = 4` to be the only failing modulus in that range; mod `8` the period is
`4 = phi(8)`.

## Definitional fidelity

The sequence is defined by the entry's recurrence
`a(n) = 3 a(n-1) + Sum_{k=1..n-1} 2^k binomial(n-1,k) a(n-k)`, reindexed as
`a(n+1) = 3 a(n) + Sum_{k<n} 2^(k+1) binomial(n,k+1) a(n-k)`.  It is checked
against the first eleven listed terms, and against the entry's independent
Stirling-number closed form for `n ≤ 10`.  The e.g.f. identity itself is
not formalized (it is the entry's own formula, not part of the claim being
refuted).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A365777Refutation

/-- A365777 via the entry's recurrence: `a(0) = 1` and
`a(n) = 3 a(n-1) + Sum_{k=1..n-1} 2^k binomial(n-1,k) a(n-k)`, written for
`n + 1` with the summation index shifted by one. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * a n + ∑ k : Fin n, 2 ^ (k.val + 1) * n.choose (k.val + 1) * a (n - k.val)
decreasing_by all_goals omega

/-- The entry's closed form
`a(n) = Sum_{k=0..n} (-2)^(n-k) (Product_{j=0..k-1} (4j+3)) Stirling2(n,k)`,
used only as an independent cross-check of `a`.  The natural subtraction
`n - k` is guarded by `k ∈ range (n + 1)`. -/
def aStirling (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-2 : ℤ) ^ (n - k) * (∏ j ∈ Finset.range k, (4 * (j : ℤ) + 3)) * n.stirlingSecond k

/-! ## Ground truth against the listed terms -/

example : a 0 = 1 := by norm_num [a]
example : a 1 = 3 := by norm_num [a]
example : a 2 = 15 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 3 = 117 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 4 = 1257 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 5 = 17163 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 6 = 284055 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 7 = 5522877 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 8 = 123344817 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 9 = 3111071283 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 10 = 87454712895 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]

example : aStirling 3 = 117 := by decide
example : aStirling 10 = 87454712895 := by decide

/-! ## The conjecture -/

/-- **Bala's conjecture (A365777, Peter Bala, Oct 23 2025).**

Verbatim: "Conjecture: the sequence a(n) taken modulo a positive integer k is
eventually periodic with the period dividing phi(k)."

Formalized: for every `k > 0` there is a positive period `p ∣ φ(k)` and a
threshold `N` with `a(n + p) ≡ a(n) (mod k)` for all `n ≥ N`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + p) ≡ a n [MOD k]

/-! ## Residues modulo 4 -/

/-- Modulo 4 only the `k = 1` term of the recurrence survives:
`a(n+1) ≡ (2n+3) a(n) (mod 4)`. -/
theorem a_succ_modEq (n : ℕ) : a (n + 1) ≡ (2 * n + 3) * a n [MOD 4] := by
  cases n with
  | zero => simp [a, Nat.ModEq]
  | succ m =>
    rw [a, Fin.sum_univ_succ]
    have hrest : 4 ∣ ∑ k : Fin m, 2 ^ ((k.succ : Fin (m + 1)).val + 1) *
        (m + 1).choose ((k.succ : Fin (m + 1)).val + 1) *
        a (m + 1 - (k.succ : Fin (m + 1)).val) := by
      apply Finset.dvd_sum
      intro k _
      have h4 : 4 ∣ 2 ^ ((k.succ : Fin (m + 1)).val + 1) := by
        rw [Fin.val_succ]
        exact pow_dvd_pow 2 (by omega : 2 ≤ k.val + 1 + 1)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h4 _) _
    obtain ⟨c, hc⟩ := hrest
    rw [hc]
    simp only [Fin.val_zero, zero_add, pow_one, Nat.choose_one_right, Nat.sub_zero]
    have hring : 3 * a (m + 1) + (2 * (m + 1) * a (m + 1) + 4 * c)
        = (2 * (m + 1) + 3) * a (m + 1) + 4 * c := by ring
    rw [hring]
    exact Nat.add_mul_mod_self_left _ _ _

/-- Every term `a(n)` is odd. -/
theorem a_mod_two (n : ℕ) : a n % 2 = 1 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have h2 : a (n + 1) ≡ (2 * n + 3) * a n [MOD 2] :=
      (a_succ_modEq n).of_dvd (by norm_num)
    have hring : (2 * n + 3) * a n = a n + 2 * ((n + 1) * a n) := by ring
    rw [hring] at h2
    unfold Nat.ModEq at h2
    rw [h2, Nat.add_mul_mod_self_left, ih]

/-- Two steps of the recurrence multiply the residue by `3` modulo 4:
`a(n+2) ≡ 3 a(n) (mod 4)`. -/
theorem a_add_two_modEq (n : ℕ) : a (n + 2) ≡ 3 * a n [MOD 4] := by
  have h1 := a_succ_modEq (n + 1)
  have h0 := (a_succ_modEq n).mul_left (2 * (n + 1) + 3)
  have hring : (2 * (n + 1) + 3) * ((2 * n + 3) * a n)
      = 3 * a n + 4 * ((n ^ 2 + 4 * n + 3) * a n) := by ring
  rw [hring] at h0
  calc a (n + 2) ≡ (2 * (n + 1) + 3) * a (n + 1) [MOD 4] := h1
    _ ≡ 3 * a n + 4 * ((n ^ 2 + 4 * n + 3) * a n) [MOD 4] := h0
    _ ≡ 3 * a n [MOD 4] := Nat.add_mul_mod_self_left _ _ _

/-- For every `n`, `a(n+2) ≢ a(n) (mod 4)`: no period dividing `phi(4) = 2`
holds anywhere in the sequence. -/
theorem a_add_two_not_modEq (n : ℕ) : ¬ a (n + 2) ≡ a n [MOD 4] := by
  intro h
  have h3 : 3 * a n ≡ a n [MOD 4] := (a_add_two_modEq n).symm.trans h
  have hodd := a_mod_two n
  unfold Nat.ModEq at h3
  omega

/-- The sequence is purely periodic modulo 4 with period 4:
`a(n+4) ≡ a(n) (mod 4)` (residues `1, 3, 3, 1, ...`). -/
theorem a_add_four_modEq (n : ℕ) : a (n + 4) ≡ a n [MOD 4] := by
  have h2 : a (n + 2 + 2) ≡ 3 * a (n + 2) [MOD 4] := a_add_two_modEq (n + 2)
  calc a (n + 4) ≡ 3 * a (n + 2) [MOD 4] := h2
    _ ≡ 3 * (3 * a n) [MOD 4] := (a_add_two_modEq n).mul_left 3
    _ = a n + 4 * (2 * a n) := by ring
    _ ≡ a n [MOD 4] := Nat.add_mul_mod_self_left _ _ _

/-! ## The refutation -/

/-- **Bala's A365777 conjecture is false**, with counterexample modulus
`k = 4`.  Here `phi(4) = 2`, so the only admissible periods are `1` and `2`,
and either would give `a(n+2) ≡ a(n) (mod 4)` for large `n`; but
`a(n+2) ≡ 3 a(n) (mod 4)` with `a(n)` odd for every `n`.  The true period
modulo 4 is `4` (`a_add_four_modEq`).  Computation over moduli `1..129`
finds `4` as the only exception, so the author probably intended the claim
for moduli `k ≠ 4` (or with period dividing `2 phi(k)` at `k = 4`). -/
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

end Candidates.A365777Refutation
