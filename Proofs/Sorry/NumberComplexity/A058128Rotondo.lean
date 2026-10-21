/-
# A058128 — Rotondo: for even n, a(n) is prime or a weak Fermat pseudoprime to base n

## OEIS source (retrieved with `oeis show A058128`, 2026-10-21)

```
NAME:     a(1) = 1, a(n) = (n^n-n)/(n-1)^2 for n >= 2.
TERMS:    1,2,6,28,195,1866,22876,342392,6053445,123456790,2853116706,
          73686780564,2103299351335,65751519677858,2234152501943160,...
KEYWORDS: nice,nonn,easy
FORMULA:  a(n) = Sum_{k=1..n} k*n^(n-k-1). - _Benoit Cloitre_, Sep 28 2002
COMMENT (the conjecture):
  Conjecture: For even n, a(n) is prime or a weak Fermat pseudoprime to
  base n. - _Davide Rotondo_, Nov 06 2024
```

## Status

Triage status: open (no proof in the entry or in the literature found by the
triage).  Computation: `n ^ a(n) ≡ n [MOD a(n)]` holds for every even
`n ≤ 800` (and for odd `n ≤ 300` only at `n = 3`, so the parity hypothesis is
load-bearing).  This module proves the conjecture (`rotondo_conjecture`), sorry-free.

## Reading of the conjecture

A *weak Fermat pseudoprime to base `b`* is a composite `m` with
`b ^ m ≡ b [MOD m]`.  Since every prime `p` satisfies `b ^ p ≡ b [MOD p]`, the
conjecture says exactly that `n ^ a(n) ≡ n [MOD a(n)]` for every even `n ≥ 2`
(`n = 0` lies outside the entry's offset `1`).

## Proof (elementary, Cipolla-style)

Put `m = n - 1` (odd), `R = ∑_{i<m} n^i`, so `R * m + 1 = n ^ m`.  Modulo
`m^2`, `n^i = (1 + m)^i ≡ 1 + i m`, so `R ≡ m + m^2 (m-1)/2 ≡ m`; hence
`R = m S` with `S ≡ 1 [MOD m]`, and `a(n) = n S ≡ 1 [MOD m]`.  Then
`n ^ m ≡ 1 [MOD S]` gives `n ^ a(n) ≡ n [MOD S]`; modulo `n` both sides vanish;
`gcd(n, S) = 1` because `S ∣ R` and `R ∣ n ^ m - 1`.  CRT finishes.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A058128Rotondo

open Finset

/-! ## Definition layer -/

/-- OEIS A058128: `a(1) = 1` and `a(n) = (n^n - n)/(n-1)^2` for `n ≥ 2`.
The entry has offset `1`; the value at `n = 0` is junk and never used.
For even `n ≥ 2` the division is exact (see `a_structure`). -/
def a (n : ℕ) : ℕ := if n = 1 then 1 else (n ^ n - n) / (n - 1) ^ 2

example : a 1 = 1 := by decide
example : a 2 = 2 := by decide
example : a 3 = 6 := by decide
example : a 4 = 28 := by decide
example : a 5 = 195 := by decide
example : a 6 = 1866 := by decide
example : a 7 = 22876 := by decide
example : a 8 = 342392 := by decide
example : a 9 = 6053445 := by decide
example : a 10 = 123456790 := by decide
example : a 11 = 2853116706 := by decide
example : a 12 = 73686780564 := by decide

/-! ## Helper lemmas -/

/-- `(m + 1)^i ≡ 1 + i m [MOD m^2]` (binomial expansion truncated at order 1). -/
theorem pow_succ_modEq (m i : ℕ) : (m + 1) ^ i ≡ 1 + i * m [MOD m ^ 2] := by
  induction i with
  | zero => simp [Nat.ModEq.refl]
  | succ i ih =>
    have hstep : (m + 1) ^ (i + 1) ≡ (1 + i * m) * (m + 1) [MOD m ^ 2] := by
      rw [pow_succ]; exact ih.mul_right _
    have hexp : (1 + i * m) * (m + 1) = 1 + (i + 1) * m + m ^ 2 * i := by ring
    have hdrop : 1 + (i + 1) * m + m ^ 2 * i ≡ 1 + (i + 1) * m [MOD m ^ 2] :=
      Nat.add_mul_mod_self_left _ _ _
    rw [hexp] at hstep
    exact hstep.trans hdrop

/-- For odd `m = 2k+1`, the geometric sum `∑_{i<m} (m+1)^i ≡ m [MOD m^2]`. -/
theorem geom_sum_modEq (k : ℕ) :
    ∑ i ∈ range (2 * k + 1), (2 * k + 1 + 1) ^ i ≡ 2 * k + 1 [MOD (2 * k + 1) ^ 2] := by
  set m := 2 * k + 1 with hm
  have hsum : ∑ i ∈ range m, (m + 1) ^ i ≡ ∑ i ∈ range m, (1 + i * m) [MOD m ^ 2] :=
    Nat.ModEq.sum fun i _ => pow_succ_modEq m i
  have hid : (∑ i ∈ range m, i) = m * k := by
    have h2 := Finset.sum_range_id_mul_two m
    have hm1 : m - 1 = 2 * k := by omega
    rw [hm1] at h2
    have : (∑ i ∈ range m, i) * 2 = m * k * 2 := by rw [h2]; ring
    omega
  have hval : ∑ i ∈ range m, (1 + i * m) = m + m ^ 2 * k := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hid]
    simp only [sum_const, card_range, smul_eq_mul, mul_one]
    ring
  rw [hval] at hsum
  exact hsum.trans (Nat.add_mul_mod_self_left _ _ _)

/-- Structure of `a(n)` for even `n = m + 1`, `m = 2k+1`: there is `S` with
`a(n) = n S`, `S ≡ 1 [MOD m]`, `n ^ m ≡ 1 [MOD S]`, and `S` coprime to `n`. -/
theorem a_structure (k : ℕ) :
    ∃ S : ℕ, a (2 * k + 1 + 1) = (2 * k + 1 + 1) * S ∧ S ≡ 1 [MOD 2 * k + 1] ∧
      (2 * k + 1 + 1) ^ (2 * k + 1) ≡ 1 [MOD S] ∧ Nat.Coprime S (2 * k + 1 + 1) := by
  set m := 2 * k + 1 with hm
  set R := ∑ i ∈ range m, (m + 1) ^ i
  have hR : R * m + 1 = (m + 1) ^ m := geom_sum_mul_add m m
  have hRmod : R ≡ m [MOD m ^ 2] := geom_sum_modEq k
  -- `m ∣ R`
  have hmR : m ∣ R := by
    have h1 : R % m = m % m := Nat.ModEq.of_dvd (Dvd.intro_left m (sq m).symm) hRmod
    exact Nat.dvd_of_mod_eq_zero (by rw [h1, Nat.mod_self])
  obtain ⟨S, hS⟩ := hmR
  have hm0 : m ≠ 0 := by omega
  have hS1 : S ≡ 1 [MOD m] := by
    apply Nat.ModEq.mul_left_cancel' hm0
    rw [mul_one, ← hS, ← sq]
    exact hRmod
  refine ⟨S, ?_, hS1, ?_, ?_⟩
  · -- `a(n) = n S`
    have hn1 : m + 1 ≠ 1 := by omega
    have hpow : (m + 1) ^ (m + 1) = (m + 1) * S * m ^ 2 + (m + 1) := by
      rw [pow_succ, ← hR, hS]; ring
    simp only [a, hn1, if_false, Nat.add_sub_cancel, hpow]
    exact Nat.mul_div_cancel _ (by positivity)
  · -- `n ^ m ≡ 1 [MOD S]`
    rw [← hR, hS]
    have : m * S * m + 1 = 1 + S * (m * m) := by ring
    rw [this]
    exact Nat.add_mul_mod_self_left _ _ _
  · -- `gcd(S, n) = 1`
    have hcopR : Nat.Coprime R ((m + 1) ^ m) := by
      rw [← hR, Nat.coprime_comm, Nat.coprime_mul_left_add_left]
      exact Nat.coprime_one_left _
    have hcopRn : Nat.Coprime R (m + 1) :=
      Nat.Coprime.coprime_dvd_right (dvd_pow_self _ hm0) hcopR
    exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left m hS.symm) hcopRn

/-- **Weak Fermat congruence for A058128 at even `n`.** For every even `n ≥ 2`,
`n ^ a(n) ≡ n [MOD a(n)]`. -/
theorem pow_a_modEq (n : ℕ) (hn : 2 ≤ n) (he : Even n) : n ^ a n ≡ n [MOD a n] := by
  obtain ⟨j, hj⟩ := he
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 + 1 := ⟨j - 1, by omega⟩
  set m := 2 * k + 1 with hm
  obtain ⟨S, haS, hS1, hpowS, hcop⟩ := a_structure k
  rw [haS]
  -- `S = 1 + m u`
  have hSpos : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · rw [h0] at hcop; simp at hcop
    · exact h0
  obtain ⟨u, hu⟩ : m ∣ S - 1 := (Nat.modEq_iff_dvd' hSpos).mp hS1.symm
  have hSu : S = 1 + m * u := by omega
  have hexp : (m + 1) * S = 1 + m * (1 + u + m * u) := by rw [hSu]; ring
  have hmodS : (m + 1) ^ ((m + 1) * S) ≡ m + 1 [MOD S] := by
    rw [hexp, pow_add, pow_one, pow_mul]
    have h := (hpowS.pow (1 + u + m * u)).mul_left (m + 1)
    rw [one_pow, mul_one] at h
    exact h
  have hmodn : (m + 1) ^ ((m + 1) * S) ≡ m + 1 [MOD m + 1] := by
    have hpos : (m + 1) * S ≠ 0 := by positivity
    have hd : m + 1 ∣ (m + 1) ^ ((m + 1) * S) := dvd_pow_self _ hpos
    exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨hmodn, hmodS⟩

/-- **Rotondo's conjecture (A058128, Davide Rotondo, Nov 06 2024).**

Verbatim: "Conjecture: For even n, a(n) is prime or a weak Fermat pseudoprime to
base n."  Here a weak Fermat pseudoprime to base `n` is a composite `q` (so
`¬ q.Prime` and `1 < q`) with `n ^ q ≡ n [MOD q]`.  The guard `2 ≤ n` keeps `n`
inside the entry's offset (`n = 0` is not a term of the sequence). -/
theorem rotondo_conjecture (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    (a n).Prime ∨ (¬ (a n).Prime ∧ 1 < a n ∧ n ^ a n ≡ n [MOD a n]) := by
  by_cases hp : (a n).Prime
  · exact Or.inl hp
  · refine Or.inr ⟨hp, ?_, pow_a_modEq n hn he⟩
    obtain ⟨j, hj⟩ := he
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 + 1 := ⟨j - 1, by omega⟩
    obtain ⟨S, haS, -, -, hcop⟩ := a_structure k
    have hSpos : 0 < S := by
      rcases Nat.eq_zero_or_pos S with h0 | h0
      · rw [h0] at hcop; simp at hcop
      · exact h0
    rw [haS]
    nlinarith

/- Non-vacuity: the hypotheses `2 ≤ n`, `Even n` are jointly satisfied at `n = 4`,
where `a 4 = 28` is composite and `4 ^ 28 ≡ 4 [MOD 28]`. -/
example : 4 ^ a 4 ≡ 4 [MOD a 4] := pow_a_modEq 4 (by norm_num) ⟨2, rfl⟩

end Candidates.A058128Rotondo
