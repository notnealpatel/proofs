/-
# A052895 — Bala: `C(e^x - 1)` coefficients are eventually periodic mod every modulus

## OEIS source (pulled with `oeis show A052895`, retrieved 2026-10-21)

```
NAME:     Expansion of e.g.f. (1/2)/(exp(x) - 1) * (1 - (5 - 4*exp(x))^(1/2)).
TERMS:    1,1,5,43,545,9211,195305,4990483,149371745,5128125451,198696086105,
          8578228640323,...
FORMULA (the definition used here):
  a(n) = Sum_{k=0..n} k!*Stirling2(n,k)*Catalan(k). - _Vladimir Kruchinin_,
  Sep 15 2010
FORMULA (the conjecture):
  From _Peter Bala_, Jan 15 2018: (Start)
  E.g.f.: C(exp(x) - 1), where C(x) = (1 - sqrt(1 - 4*x))/(2*x) is the o.g.f.
  for A000108. Cf. A006531.
  Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is eventually
  periodic with the exact period dividing phi(k), where phi(k) is the Euler
  totient function A000010. For example, modulo 10 the sequence becomes
  (1, 1, 5, 3, 5, 1, 5, 3, 5, ...), with an apparent period 1, 5, 3, 5 of
  length 4 = phi(10) beginning at a(1). (End)
```

## Status

Triage status: open (no proof in the entry; none found in the literature by
the triage, although the result is plausibly folklore).  This module proves
it: `a (n + φ m) ≡ a n [ZMOD m]` for every `m > 0` and every `n ≥ m`, which is
exactly "eventually periodic mod `m` with a period `φ m`", hence the exact
(minimal) eventual period divides `φ m`.

## Proof

Same argument as the sibling `Enumerative.A006531SemiorderMod` (the same sum
with the sign `(-1)^(n+k)`), whose lemmas are reused:

1. `k! S(n,k) = Σ_{i ≤ k} (-1)^(k+i) C(k,i) i^n`
   (`A006531SemiorderMod.factorial_mul_stirlingSecond`).
2. For `m ≤ n`, `x^(n + φ m) ≡ x^n [ZMOD m]` for every integer `x`
   (`A006531SemiorderMod.dvd_pow_add_totient_sub_pow`).
3. Summands with `k ≥ m` vanish mod `m` because `m ∣ k!`.

## Definitional fidelity

The entry's NAME is an e.g.f.; this module uses Kruchinin's formula
`Σ_k k! S(n,k) Catalan(k)` from the entry, which is the form named in the
conjecture's statement (`C(exp(x) - 1)`).  Ground-truth examples check it
against the listed terms `a(0..9)` (the kernel check of
`a(10)` exhausts memory and is omitted); the e.g.f. identity is not formalized.
-/
import Mathlib
import Enumerative.A006531SemiorderMod

set_option autoImplicit false

namespace Candidates.A052895SumStirlingCatalan

open Finset Nat

/-! ## Definition layer -/

/-- Kruchinin's formula for A052895:
`a(n) = Σ_{k=0..n} k! * Stirling2(n,k) * Catalan(k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (k ! : ℤ) * (stirlingSecond n k : ℤ) * (catalan k : ℤ)

example : a 0 = 1 := by decide +kernel
example : a 1 = 1 := by decide +kernel
example : a 2 = 5 := by decide +kernel
example : a 3 = 43 := by decide +kernel
example : a 4 = 545 := by decide +kernel
example : a 5 = 9211 := by decide +kernel
example : a 6 = 195305 := by decide +kernel
example : a 7 = 4990483 := by decide +kernel
example : a 8 = 149371745 := by decide +kernel
example : a 9 = 5128125451 := by decide +kernel

/-! ## Periodicity of the summands -/

/-- Each summand of `a n` is an `n`-independent integer combination of the
powers `i^n`, `i ≤ k`. -/
theorem summand_eq_sum_pow (n k : ℕ) :
    (k ! : ℤ) * (stirlingSecond n k : ℤ) * (catalan k : ℤ) =
      ∑ i ∈ range (k + 1),
        ((catalan k : ℤ) * (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ)) * (i : ℤ) ^ n := by
  have hfs : (k ! : ℤ) * (stirlingSecond n k : ℤ) = A006531SemiorderMod.altPowSum n k := by
    rw [← A006531SemiorderMod.factorial_mul_stirlingSecond]
    push_cast
    ring
  rw [hfs, A006531SemiorderMod.altPowSum, sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- For `0 < m ≤ n`, the `k`-th summand of `a` is unchanged mod `m` when
`n` is shifted by `φ m`. -/
theorem summand_periodic (m : ℕ) (hm : 0 < m) (k : ℕ) {n : ℕ} (hn : m ≤ n) :
    (m : ℤ) ∣ (k ! : ℤ) * (stirlingSecond (n + φ m) k : ℤ) * (catalan k : ℤ) -
      (k ! : ℤ) * (stirlingSecond n k : ℤ) * (catalan k : ℤ) := by
  rw [summand_eq_sum_pow, summand_eq_sum_pow, ← sum_sub_distrib]
  apply dvd_sum
  intro i _
  rw [← mul_sub]
  exact (A006531SemiorderMod.dvd_pow_add_totient_sub_pow m hm _ hn).mul_left _

/-- Summands with `k ≥ m > 0` vanish mod `m`, since `m ∣ k!`. -/
theorem summand_dvd_of_le (m : ℕ) (hm : 0 < m) {k : ℕ} (hk : m ≤ k) (n : ℕ) :
    (m : ℤ) ∣ (k ! : ℤ) * (stirlingSecond n k : ℤ) * (catalan k : ℤ) := by
  apply Dvd.dvd.mul_right
  apply Dvd.dvd.mul_right
  exact_mod_cast Nat.dvd_factorial hm hk

/-! ## The conjecture -/

/-- Explicit form of Bala's conjecture: for `0 < m ≤ n`,
`a(n + φ(m)) ≡ a(n) (mod m)`, where `a` is A052895. -/
theorem a_add_totient_modEq (m : ℕ) (hm : 0 < m) {n : ℕ} (hn : m ≤ n) :
    a (n + φ m) ≡ a n [ZMOD m] := by
  set s : ℕ → ℕ → ℤ := fun n k =>
    (k ! : ℤ) * (stirlingSecond n k : ℤ) * (catalan k : ℤ) with hs
  have hsplit : ∀ n' : ℕ, m ≤ n' → a n' =
      ∑ k ∈ range m, s n' k + ∑ k ∈ Ico m (n' + 1), s n' k := fun n' hn' =>
    (sum_range_add_sum_Ico _ (by omega)).symm
  have htail : ∀ n' : ℕ, (m : ℤ) ∣ ∑ k ∈ Ico m (n' + 1), s n' k := fun n' =>
    dvd_sum fun k hk => summand_dvd_of_le m hm (mem_Ico.mp hk).1 n'
  have hhead : (m : ℤ) ∣ ∑ k ∈ range m, s (n + φ m) k - ∑ k ∈ range m, s n k := by
    rw [← sum_sub_distrib]
    exact dvd_sum fun k _ => summand_periodic m hm k hn
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd, hsplit n hn, hsplit (n + φ m) (by omega)]
  have hcomb : ∑ k ∈ range m, s (n + φ m) k + ∑ k ∈ Ico m (n + φ m + 1), s (n + φ m) k -
      (∑ k ∈ range m, s n k + ∑ k ∈ Ico m (n + 1), s n k) =
      (∑ k ∈ range m, s (n + φ m) k - ∑ k ∈ range m, s n k) +
      ∑ k ∈ Ico m (n + φ m + 1), s (n + φ m) k - ∑ k ∈ Ico m (n + 1), s n k := by ring
  rw [hcomb]
  exact (hhead.add (htail _)).sub (htail _)

/-- **Bala's conjecture (A052895, Peter Bala, Jan 15 2018).**

Verbatim: "Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is
eventually periodic with the exact period dividing phi(k), where phi(k) is the
Euler totient function A000010."

Formalized as: for every modulus `m > 0` there is `N` with
`a(n + φ(m)) ≡ a(n) (mod m)` for all `n ≥ N`; an eventual period `φ(m)` is the
same as the minimal eventual period dividing `φ(m)`.  Proved with `N = m`. -/
theorem a_eventually_periodic (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + φ m) ≡ a n [ZMOD m] :=
  ⟨m, fun _ hn => a_add_totient_modEq m hm hn⟩

/-- The entry's worked example: modulo `10` the period `1, 5, 3, 5` of length
`φ(10) = 4` starting at `a(1)`, checked at `n = 1`. -/
example : φ 10 = 4 ∧ a (1 + 4) ≡ a 1 [ZMOD 10] := by decide +kernel

end Candidates.A052895SumStirlingCatalan
