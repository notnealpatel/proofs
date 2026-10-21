/-
# A006531 — Bala: labeled semiorder counts are eventually periodic mod every modulus

## OEIS source (pulled with `oeis show A006531`, retrieved 2026-10-21)

```
NAME:     Number of semiorders on n labeled elements.
TERMS:    1,1,3,19,183,2371,38703,763099,17648823,468603091,14050842303,
          469643495179,17315795469063,698171064855811,...
KEYWORDS: nonn,nice,easy,changed
FORMULA (the definition used here):
  From _Peter Bala_, Jan 15 2018: (Start)
  a(n) = Sum_{k = 0..n} (-1)^(n+k)*Catalan(k)*k!*Stirling2(n,k). Cf. A052895.
FORMULA (the conjecture, same block):
  Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is eventually
  periodic with the exact period dividing phi(k), where phi(k) is Euler's
  totient function A000010. For example, modulo 10 the sequence becomes
  (1, 1, 3, 9, 3, 1, 3, 9, 3, ...) with an apparent period 1, 3, 9, 3 of
  length 4 = phi(10) beginning at a(1). (End)
```

## Status

Triage status: open (no proof in the entry; none found in the literature by
the triage, although the result may be folklore).  This module proves it:
`a (n + φ m) ≡ a n [ZMOD m]` for every `m > 0` and every `n ≥ m`, which is
exactly "eventually periodic mod `m` with a period `φ m`", hence the exact
(minimal) eventual period divides `φ m`.

## Proof

1. `k! S(n,k) = Σ_{i ≤ k} (-1)^(k+i) C(k,i) i^n` (inclusion–exclusion count
   of surjections), proved by induction on `n` from `stirlingSecond_succ_succ`.
2. Hence each summand of `a n` is `Σ_i c_{k,i} (-i)^n` with `c_{k,i}`
   independent of `n`.
3. For `m ≤ n`, `x^(n + φ m) ≡ x^n [ZMOD m]` for every integer `x`, checked
   prime power by prime power (`p ∣ x`: both sides vanish since `k < p^k ≤ n`;
   `p ∤ x`: Euler's theorem with `φ(p^k) ∣ φ(m)`).
4. Summands with `k ≥ m` vanish mod `m` because `m ∣ k!`, so the varying upper
   limit of the sum does not matter.

## Definitional fidelity

The entry's NAME counts labeled semiorders; this module uses Bala's formula
from the same comment block as the definition, which is the form in which the
conjecture is stated.  The ground-truth examples check it against the listed
terms `a(0..10)`; the general identity with the semiorder count (via the
e.g.f. `C(1 - exp(-x))`) is not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A006531SemiorderMod

open Finset Nat

/-! ## Definition layer -/

/-- Bala's formula for A006531 (labeled semiorders):
`a(n) = Σ_{k=0..n} (-1)^(n+k) * Catalan(k) * k! * Stirling2(n,k)`. -/
def semiorder (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1),
    (-1 : ℤ) ^ (n + k) * (catalan k : ℤ) * (k ! : ℤ) * (stirlingSecond n k : ℤ)

example : semiorder 0 = 1 := by decide +kernel
example : semiorder 1 = 1 := by decide +kernel
example : semiorder 2 = 3 := by decide +kernel
example : semiorder 3 = 19 := by decide +kernel
example : semiorder 4 = 183 := by decide +kernel
example : semiorder 5 = 2371 := by decide +kernel
example : semiorder 6 = 38703 := by decide +kernel
example : semiorder 7 = 763099 := by decide +kernel
example : semiorder 8 = 17648823 := by decide +kernel
example : semiorder 9 = 468603091 := by decide +kernel
example : semiorder 10 = 14050842303 := by decide +kernel

/-- The inclusion–exclusion sum `Σ_{i ≤ k} (-1)^(k+i) C(k,i) i^n`, which equals
`k! * S(n,k)` (`factorial_mul_stirlingSecond`). -/
def altPowSum (n k : ℕ) : ℤ :=
  ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * (i : ℤ) ^ n

example : altPowSum 3 2 = 6 := by decide +kernel
example : altPowSum 4 2 = 14 := by decide +kernel

/-! ## Euler's theorem in the form needed -/

/-- Euler's theorem over `ℤ`: if `x` is coprime to `M` then `M ∣ x^φ(M) - 1`. -/
theorem dvd_pow_totient_sub_one (x : ℤ) (M : ℕ) (h : IsCoprime x (M : ℤ)) :
    (M : ℤ) ∣ x ^ φ M - 1 := by
  obtain ⟨u, v, huv⟩ := h
  have hunit : IsUnit (x : ZMod M) := by
    refine IsUnit.of_mul_eq_one (u : ZMod M) ?_
    have hc := congrArg (fun z : ℤ => (z : ZMod M)) huv
    simpa [mul_comm] using hc
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [← hunit.unit_spec, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, sub_self]

/-- For `0 < m ≤ n` and every integer `x`, `m ∣ x^(n + φ m) - x^n`; i.e. powers of
any integer are periodic mod `m` with period `φ m` from exponent `m` on. -/
theorem dvd_pow_add_totient_sub_pow (m : ℕ) (hm : 0 < m) (x : ℤ) {n : ℕ} (hn : m ≤ n) :
    (m : ℤ) ∣ x ^ (n + φ m) - x ^ n := by
  have hfac : x ^ (n + φ m) - x ^ n = x ^ n * (x ^ φ m - 1) := by ring
  rw [hfac, Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rw [← Int.natCast_dvd]
  have hkm : p ^ k ≤ m := Nat.le_of_dvd hm hpk
  have hkn : k ≤ n := ((Nat.lt_pow_self hp.one_lt).trans_le (hkm.trans hn)).le
  by_cases hpx : (p : ℤ) ∣ x
  · apply Dvd.dvd.mul_right
    push_cast
    exact (pow_dvd_pow_of_dvd hpx k).trans (pow_dvd_pow x hkn)
  · apply Dvd.dvd.mul_left
    have hcop : IsCoprime x ((p ^ k : ℕ) : ℤ) := by
      push_cast
      apply IsCoprime.pow_right
      apply IsCoprime.symm
      exact (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hpx
    obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hpk
    rw [hc, pow_mul]
    exact (dvd_pow_totient_sub_one x _ hcop).trans (sub_one_dvd_pow_sub_one _ c)

/-! ## The explicit formula for `k! S(n,k)` -/

/-- Shifted form of `altPowSum (n+1) (k+1)`, using `i * C(k+1,i) = (k+1) * C(k,i-1)`. -/
theorem altPowSum_succ_succ (n k : ℕ) :
    altPowSum (n + 1) (k + 1) =
      (k + 1 : ℤ) *
        ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * ((i : ℤ) + 1) ^ n := by
  unfold altPowSum
  rw [sum_range_succ', mul_sum]
  simp only [CharP.cast_eq_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, add_zero]
  apply sum_congr rfl
  intro i _
  have hc : ((k + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = (k + 1 : ℤ) * (k.choose i : ℤ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq k i).symm
  push_cast
  rw [pow_succ]
  linear_combination ((-1 : ℤ) ^ (k + i) * ((i : ℤ) + 1) ^ n) * hc

/-- Pascal's rule for `altPowSum`: `T(n,k+1) + T(n,k) = Σ_{i ≤ k} (-1)^(k+i) C(k,i) (i+1)^n`. -/
theorem altPowSum_succ_add (n k : ℕ) :
    altPowSum n (k + 1) + altPowSum n k =
      ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * ((i : ℤ) + 1) ^ n := by
  have e1 : altPowSum n (k + 1) =
      ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * ((i : ℤ) + 1) ^ n +
      ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose (i + 1) : ℤ) * ((i : ℤ) + 1) ^ n +
      (-1 : ℤ) ^ (k + 1) * (0 : ℤ) ^ n := by
    unfold altPowSum
    rw [sum_range_succ', ← sum_add_distrib]
    congr 1
    · apply sum_congr rfl
      intro i _
      push_cast [Nat.choose_succ_succ]
      ring
    · simp
  have e2 : altPowSum n k =
      -∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose (i + 1) : ℤ) * ((i : ℤ) + 1) ^ n +
      (-1 : ℤ) ^ k * (0 : ℤ) ^ n := by
    unfold altPowSum
    have hext : ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * (i : ℤ) ^ n =
        ∑ i ∈ range (k + 1 + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * (i : ℤ) ^ n := by
      rw [sum_range_succ (n := k + 1), Nat.choose_succ_self]
      simp
    rw [hext, sum_range_succ', ← sum_neg_distrib]
    congr 1
    · apply sum_congr rfl
      intro i _
      push_cast
      ring
    · simp
  rw [e1, e2]
  ring

/-- Base case: `T(0,k) = [k = 0]`, by the alternating binomial sum. -/
theorem altPowSum_zero_left (k : ℕ) : altPowSum 0 k = if k = 0 then 1 else 0 := by
  unfold altPowSum
  have h : ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k + i) * (k.choose i : ℤ) * (i : ℤ) ^ 0 =
      (-1 : ℤ) ^ k * ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i * (k.choose i : ℤ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  rw [h, Int.alternating_sum_range_choose]
  split_ifs with hk
  · subst hk
    simp
  · simp

/-- `k! * S(n,k) = Σ_{i=0..k} (-1)^(k+i) C(k,i) i^n` (number of surjections
`[n] → [k]` by inclusion–exclusion). -/
theorem factorial_mul_stirlingSecond (n k : ℕ) :
    ((k ! * stirlingSecond n k : ℕ) : ℤ) = altPowSum n k := by
  induction n generalizing k with
  | zero =>
    rw [altPowSum_zero_left]
    cases k with
    | zero => simp [stirlingSecond_zero]
    | succ k => simp [stirlingSecond_zero_succ]
  | succ n ih =>
    cases k with
    | zero => simp [stirlingSecond_succ_zero, altPowSum]
    | succ k =>
      rw [altPowSum_succ_succ, ← altPowSum_succ_add, ← ih, ← ih, stirlingSecond_succ_succ,
        Nat.factorial_succ]
      push_cast
      ring

/-! ## Periodicity of the summands -/

/-- Each summand of `semiorder n` is an `n`-independent integer combination of the
powers `(-i)^n`, `i ≤ k`. -/
theorem summand_eq_sum_pow (n k : ℕ) :
    (-1 : ℤ) ^ (n + k) * (catalan k : ℤ) * (k ! : ℤ) * (stirlingSecond n k : ℤ) =
      ∑ i ∈ range (k + 1),
        ((catalan k : ℤ) * (-1 : ℤ) ^ i * (k.choose i : ℤ)) * (-(i : ℤ)) ^ n := by
  have hfs : (k ! : ℤ) * (stirlingSecond n k : ℤ) = altPowSum n k := by
    rw [← factorial_mul_stirlingSecond]
    push_cast
    ring
  have hsq : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [mul_assoc, hfs, altPowSum, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [neg_pow, pow_add, pow_add]
  linear_combination ((-1 : ℤ) ^ n * (catalan k : ℤ) * (-1 : ℤ) ^ i * (k.choose i : ℤ) *
    (i : ℤ) ^ n) * hsq

/-- For `0 < m ≤ n`, the `k`-th summand of `semiorder` is unchanged mod `m` when
`n` is shifted by `φ m`. -/
theorem summand_periodic (m : ℕ) (hm : 0 < m) (k : ℕ) {n : ℕ} (hn : m ≤ n) :
    (m : ℤ) ∣ (-1 : ℤ) ^ (n + φ m + k) * (catalan k : ℤ) * (k ! : ℤ) *
        (stirlingSecond (n + φ m) k : ℤ) -
      (-1 : ℤ) ^ (n + k) * (catalan k : ℤ) * (k ! : ℤ) * (stirlingSecond n k : ℤ) := by
  rw [summand_eq_sum_pow, summand_eq_sum_pow, ← sum_sub_distrib]
  apply dvd_sum
  intro i _
  rw [← mul_sub]
  exact (dvd_pow_add_totient_sub_pow m hm _ hn).mul_left _

/-- Summands with `k ≥ m > 0` vanish mod `m`, since `m ∣ k!`. -/
theorem summand_dvd_of_le (m : ℕ) (hm : 0 < m) {k : ℕ} (hk : m ≤ k) (n : ℕ) :
    (m : ℤ) ∣ (-1 : ℤ) ^ (n + k) * (catalan k : ℤ) * (k ! : ℤ) * (stirlingSecond n k : ℤ) := by
  apply Dvd.dvd.mul_right
  apply Dvd.dvd.mul_left
  exact_mod_cast Nat.dvd_factorial hm hk

/-! ## The conjecture -/

/-- Explicit form of Bala's conjecture: for `0 < m ≤ n`,
`a(n + φ(m)) ≡ a(n) (mod m)`, where `a` is A006531 (labeled semiorders, via
Bala's formula). -/
theorem semiorder_add_totient_modEq (m : ℕ) (hm : 0 < m) {n : ℕ} (hn : m ≤ n) :
    semiorder (n + φ m) ≡ semiorder n [ZMOD m] := by
  set s : ℕ → ℕ → ℤ := fun n k =>
    (-1 : ℤ) ^ (n + k) * (catalan k : ℤ) * (k ! : ℤ) * (stirlingSecond n k : ℤ) with hs
  have hsplit : ∀ n' : ℕ, m ≤ n' → semiorder n' =
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

/-- **Bala's conjecture (A006531, Peter Bala, Jan 15 2018).**

Verbatim: "Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is
eventually periodic with the exact period dividing phi(k), where phi(k) is
Euler's totient function A000010."

Formalized as: for every modulus `m > 0` there is `N` with
`a(n + φ(m)) ≡ a(n) (mod m)` for all `n ≥ N`; an eventual period `φ(m)` is the
same as the minimal eventual period dividing `φ(m)`.  Proved with `N = m`. -/
theorem semiorder_eventually_periodic (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → semiorder (n + φ m) ≡ semiorder n [ZMOD m] :=
  ⟨m, fun _ hn => semiorder_add_totient_modEq m hm hn⟩

/-- The entry's worked example: modulo `10` the period `1, 3, 9, 3` of length
`φ(10) = 4` starting at `a(1)`, checked at `n = 1`. -/
example : φ 10 = 4 ∧ semiorder (1 + 4) ≡ semiorder 1 [ZMOD 10] := by decide +kernel

end Candidates.A006531SemiorderMod
