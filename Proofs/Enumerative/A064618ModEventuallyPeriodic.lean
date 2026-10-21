/-
# A064618 — Bala: the Stirling transform of `(n!)^2` is eventually periodic mod `k`

## OEIS source (retrieved with `oeis show A064618`, 2026-10-21)

```
NAME:     Stirling transform of (n!)^2.
TERMS:    1,1,5,49,821,21121,775205,38516689,2490976661,203419086241,...
FORMULA:  a(n) = Sum_{k=0..n} Stirling2(n, k)*(k!)^2.
COMMENT (the conjecture):
  Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is eventually
  periodic with the exact period dividing phi(k), where phi(k) is the Euler
  totient function A000010. For example, modulo 10 the sequence becomes
  (1, 1, 5, 9, 1, 1, 5, 9, ...), with an apparent period 1, 1, 5, 9 of length
  4 = phi(10) beginning at a(0). - _Peter Bala_, Jan 15 2018
```

## Status

Triage: "proved-elsewhere".  The entry itself carries no proof.  The
statement is an instance of the folklore argument for Stirling transforms
`∑ S(n,j) b(j)` with `k ∣ b(j)` for all large `j`: modulo `k` only finitely
many `j` contribute, `j! S(n,j) = ∑ (-1)^(j-i) C(j,i) i^n`, and
`i^(n + φ(k)) ≡ i^n (mod k)` once `n` is at least the largest exponent in
`k`.  This file formalizes exactly that argument.

## Reading of "exact period dividing φ(k)"

The minimal eventual period of a sequence divides every eventual period, so
"the exact (minimal) period divides `φ(k)`" is equivalent to "`φ(k)` is an
eventual period", which is what `conjecture` states.  The threshold proved
here is `n ≥ k` (the entry's mod-10 example starts at `a(0)`, which is a
stronger, `k`-specific observation not claimed in general).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A064618ModEventuallyPeriodic

open Finset

/-! ## Definition layer -/

/-- OEIS A064618: `a(n) = ∑_{j=0}^{n} S(n,j) (j!)^2`, with `S = Nat.stirlingSecond`
the Stirling numbers of the second kind. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), Nat.stirlingSecond n j * (j.factorial) ^ 2

example : a 0 = 1 := by decide
example : a 1 = 1 := by decide
example : a 2 = 5 := by decide
example : a 3 = 49 := by decide
example : a 4 = 821 := by decide
example : a 5 = 21121 := by decide
example : a 6 = 775205 := by decide

/-- The surjection-count sum `∑_{i=0}^{j} (-1)^(j+i) C(j,i) i^n` (an integer). -/
def surjSum (n j : ℕ) : ℤ :=
  ∑ i ∈ range (j + 1), (-1) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n

/-! ## The surjection-sum formula -/

/-- Recurrence of the surjection sums:
`F(n+1, j+1) = (j+1) (F(n, j+1) + F(n, j))`, where `F = surjSum`. -/
theorem surjSum_succ_succ (n j : ℕ) :
    surjSum (n + 1) (j + 1) = ((j : ℤ) + 1) * (surjSum n (j + 1) + surjSum n j) := by
  -- the common shifted sum `G = ∑_{i ≤ j} (-1)^(j+i) C(j,i) (i+1)^n`
  set G : ℤ := ∑ i ∈ range (j + 1), (-1) ^ (j + i) * (j.choose i : ℤ) * ((i : ℤ) + 1) ^ n
    with hG
  have hsign (i : ℕ) : ((-1 : ℤ)) ^ (j + 1 + (i + 1)) = (-1) ^ (j + i) := by
    rw [show j + 1 + (i + 1) = (j + i) + 2 by omega, pow_add]; norm_num
  have hleft : surjSum (n + 1) (j + 1) = ((j : ℤ) + 1) * G := by
    rw [surjSum, sum_range_succ', hG, mul_sum]
    simp only [pow_succ, Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    have hc : ((j + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((j : ℤ) + 1) * (j.choose i : ℤ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq j i).symm
    rw [hsign i]; push_cast
    linear_combination ((-1 : ℤ) ^ (j + i) * ((i : ℤ) + 1) ^ n) * hc
  have hright : surjSum n (j + 1) + surjSum n j = G := by
    have hext : surjSum n j = ∑ i ∈ range (j + 1 + 1),
        (-1) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
        surjSum]
    rw [hext, surjSum, sum_range_succ' _ (j + 1), sum_range_succ' _ (j + 1), hG]
    have hzero : ((-1 : ℤ)) ^ (j + 1 + 0) * ((j + 1).choose 0 : ℕ) * ((0 : ℕ) : ℤ) ^ n
        + (-1) ^ (j + 0) * (j.choose 0 : ℕ) * ((0 : ℕ) : ℤ) ^ n = 0 := by
      simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_succ]
      ring
    rw [add_add_add_comm, hzero, add_zero, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    have hsign' : ((-1 : ℤ)) ^ (j + (i + 1)) = -(-1) ^ (j + i) := by
      rw [← add_assoc, pow_succ]; ring
    rw [hsign i, hsign', Nat.choose_succ_succ]
    push_cast
    ring
  rw [hleft, hright]

/-- Explicit formula (number of surjections onto a `j`-set):
`j! S(n,j) = ∑_{i=0}^{j} (-1)^(j+i) C(j,i) i^n` in `ℤ`. -/
theorem factorial_mul_stirlingSecond (n j : ℕ) :
    ((j.factorial * Nat.stirlingSecond n j : ℕ) : ℤ) = surjSum n j := by
  induction n generalizing j with
  | zero =>
    rcases j with _ | j
    · simp [surjSum]
    · have halt : surjSum 0 (j + 1) = 0 := by
        have h := Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero j)
        have hfac : surjSum 0 (j + 1) = (-1) ^ (j + 1) *
            ∑ m ∈ range (j + 1 + 1), (-1) ^ m * ((j + 1).choose m : ℤ) := by
          rw [surjSum, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [pow_add]; ring
        rw [hfac, h, mul_zero]
      rw [halt, Nat.stirlingSecond_zero_succ, mul_zero, Nat.cast_zero]
  | succ n ih =>
    rcases j with _ | j
    · simp [surjSum]
    · rw [surjSum_succ_succ, ← ih (j + 1), ← ih j, Nat.stirlingSecond_succ_succ,
        Nat.factorial_succ]
      push_cast
      ring

/-! ## Eventual periodicity of powers -/

/-- For `1 ≤ k ≤ n` and every `x`, `x^(n + φ(k)) ≡ x^n (mod k)`: on each prime power
`p^e ∥ k`, either `p ∣ x` and `p^e ∣ x^n` (as `e < p^e ≤ k ≤ n`), or `x` is a unit
mod `p^e` and `φ(p^e) ∣ φ(k)`. -/
theorem pow_add_totient_modEq (k x n : ℕ) (hk : 0 < k) (hn : k ≤ n) :
    x ^ (n + Nat.totient k) ≡ x ^ n [MOD k] := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [zero_pow (by omega), zero_pow (by omega)]
  have hle : x ^ n ≤ x ^ (n + Nat.totient k) := Nat.pow_le_pow_right hx (Nat.le_add_right _ _)
  refine (Nat.modEq_iff_dvd' hle).mpr ?_ |>.symm
  rw [pow_add, ← Nat.mul_sub_one]
  rcases Nat.eq_zero_or_pos (x ^ n * (x ^ Nat.totient k - 1)) with h0 | hpos
  · rw [h0]; exact dvd_zero k
  refine (Nat.factorization_prime_le_iff_dvd hk.ne' hpos.ne').mp fun p hp => ?_
  set e := k.factorization p with he
  have hek : p ^ e ∣ k := Nat.ordProj_dvd k p
  rw [← hp.pow_dvd_iff_le_factorization hpos.ne']
  by_cases hpx : p ∣ x
  · have hen : e ≤ n :=
      ((Nat.lt_pow_self hp.one_lt).le.trans (Nat.le_of_dvd hk hek)).trans hn
    exact ((pow_dvd_pow p hen).trans (pow_dvd_pow_of_dvd hpx n)).mul_right _
  · have hcop : Nat.Coprime x (p ^ e) :=
      Nat.Coprime.pow_right e ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx)))
    have h1 : x ^ Nat.totient (p ^ e) ≡ 1 [MOD p ^ e] := Nat.ModEq.pow_totient hcop
    obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hek
    have h2 : x ^ Nat.totient k ≡ 1 [MOD p ^ e] := by
      rw [hc, pow_mul]
      simpa using h1.pow c
    have h3 : p ^ e ∣ x ^ Nat.totient k - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hx)).mp h2.symm
    exact h3.mul_left _

/-! ## Reduction of `a` modulo `k` -/

/-- The defining sum of `a n` may be extended to any range `M ≥ n + 1`, since
`S(n,j) = 0` for `j > n`. -/
theorem a_eq_sum_range (n M : ℕ) (hM : n + 1 ≤ M) :
    a n = ∑ j ∈ range M, Nat.stirlingSecond n j * (j.factorial) ^ 2 := by
  refine sum_subset (range_subset_range.mpr hM) fun j _ hj => ?_
  rw [mem_range, not_lt] at hj
  rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), zero_mul]

/-- Modulo `k ≥ 1`, only the terms `j < k` of `a n` survive (`k ∣ j!` for `j ≥ k`), and
each is written as `(j! S(n,j)) · j!`. -/
theorem natCast_a_eq_sum_range (k n : ℕ) (hk : 0 < k) :
    (a n : ZMod k) =
      ∑ j ∈ range k,
        ((j.factorial * Nat.stirlingSecond n j : ℕ) : ZMod k) * (j.factorial : ZMod k) := by
  calc (a n : ZMod k)
      = ∑ j ∈ range (n + 1 + k),
          ((j.factorial * Nat.stirlingSecond n j : ℕ) : ZMod k) * (j.factorial : ZMod k) := by
        rw [a_eq_sum_range n (n + 1 + k) (by omega), Nat.cast_sum]
        refine sum_congr rfl fun j _ => ?_
        push_cast
        ring
    _ = _ := by
        refine (sum_subset (range_subset_range.mpr (Nat.le_add_left k (n + 1)))
          fun j _ hj => ?_).symm
        rw [mem_range, not_lt] at hj
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hk hj), mul_zero]

/-! ## Main results -/

/-- Explicit form of the conjecture: for `1 ≤ k ≤ n`, `a(n + φ(k)) ≡ a(n) (mod k)`. -/
theorem a_add_totient_modEq_of_le (k n : ℕ) (hk : 0 < k) (hn : k ≤ n) :
    a (n + Nat.totient k) ≡ a n [MOD k] := by
  rw [← ZMod.natCast_eq_natCast_iff, natCast_a_eq_sum_range k _ hk, natCast_a_eq_sum_range k _ hk]
  refine sum_congr rfl fun j _ => ?_
  have hF (m : ℕ) : ((j.factorial * Nat.stirlingSecond m j : ℕ) : ZMod k) =
      ((surjSum m j : ℤ) : ZMod k) := by
    rw [← factorial_mul_stirlingSecond, Int.cast_natCast]
  rw [hF, hF, surjSum, surjSum]
  push_cast
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have hp : ((i : ZMod k)) ^ (n + Nat.totient k) = (i : ZMod k) ^ n := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ k).mpr (pow_add_totient_modEq k i n hk hn)
  rw [hp]

/-- Iterating an eventual period: if `a(n + P) ≡ a(n) (mod k)` for all `n ≥ N`, then
`a(n + qP) ≡ a(n) (mod k)` for all `n ≥ N` and all `q`. -/
theorem a_add_mul_modEq_of_period (k P N : ℕ)
    (hPer : ∀ n, N ≤ n → a (n + P) ≡ a n [MOD k]) (q n : ℕ) (hn : N ≤ n) :
    a (n + q * P) ≡ a n [MOD k] := by
  induction q with
  | zero => rw [zero_mul, add_zero]
  | succ q ih =>
    rw [Nat.succ_mul, ← add_assoc]
    exact (hPer (n + q * P) (by omega)).trans ih

/-- **Bala's conjecture (A064618, Peter Bala, Jan 15 2018).**

Verbatim: "Conjecture: for fixed k = 1,2,..., the sequence a(n) (mod k) is eventually
periodic with the exact period dividing phi(k), where phi(k) is the Euler totient
function A000010."

Stated as: for every `k ≥ 1` there is `N` such that `a(n + φ(k)) ≡ a(n) (mod k)` for all
`n ≥ N` (one may take `N = k`).  Since the minimal eventual period divides every eventual
period, this is equivalent to the "exact period divides `φ(k)`" reading; that
equivalence direction is `dvd_totient_of_minimal_eventual_period`. -/
theorem conjecture (k : ℕ) (hk : 0 < k) :
    ∃ N, ∀ n, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] :=
  ⟨k, fun n hn => a_add_totient_modEq_of_le k n hk hn⟩

/-- The "exact period" form: if `P ≥ 1` is the least positive eventual period of
`a mod k` (`k ≥ 1`), then `P ∣ φ(k)`. -/
theorem dvd_totient_of_minimal_eventual_period (k : ℕ) (hk : 0 < k) (P : ℕ) (hP : 0 < P)
    (hPer : ∃ N, ∀ n, N ≤ n → a (n + P) ≡ a n [MOD k])
    (hmin : ∀ p, 0 < p → p < P → ¬ ∃ N, ∀ n, N ≤ n → a (n + p) ≡ a n [MOD k]) :
    P ∣ Nat.totient k := by
  obtain ⟨N, hN⟩ := hPer
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hr
  refine hmin (Nat.totient k % P) (Nat.pos_of_ne_zero hr) (Nat.mod_lt _ hP) ⟨N + k, fun n hn => ?_⟩
  have hsplit : n + Nat.totient k % P + Nat.totient k / P * P = n + Nat.totient k := by
    have := Nat.mod_add_div' (Nat.totient k) P
    omega
  have h1 := a_add_mul_modEq_of_period k P N hN (Nat.totient k / P)
    (n + Nat.totient k % P) (by omega)
  rw [hsplit] at h1
  exact h1.symm.trans (a_add_totient_modEq_of_le k n hk (by omega))

/-- Non-vacuity of the hypotheses of `dvd_totient_of_minimal_eventual_period`: at `k = 1`,
`P = 1` they hold jointly (every sequence is constant mod `1`). -/
example : 1 ∣ Nat.totient 1 :=
  dvd_totient_of_minimal_eventual_period 1 one_pos 1 one_pos
    ⟨0, fun n _ => Nat.modEq_one⟩ (fun p hp hp1 => absurd hp1 (by omega))

/-- Ground truth for the entry's mod-10 example `1, 1, 5, 9, 1, 1, 5, 9, ...`. -/
example : (List.range 8).map (fun n => a n % 10) = [1, 1, 5, 9, 1, 1, 5, 9] := by decide

end Candidates.A064618ModEventuallyPeriodic
