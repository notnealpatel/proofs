/-
# A124000 — semiprime binomial coefficients are odd and of the form p(2p ± 1)

## OEIS source (retrieved 2026-10-21 with `oeis show A124000`, author line
## from https://oeis.org/A124000)

```
NAME:     Semiprimes in A006987(n), or semiprime binomial coefficients:
          C(n,k), 2 <= k <= n-2.
TERMS:    6,10,15,21,35,55,91,253,703,1081,1711,1891,2701,3403,5671,12403,
          13861,15931,18721,25651,34453,38503,49141,60031,64261,73153,...
AUTHOR:   Alexander Adamchuk, Oct 31 2006
COMMENT (the conjecture, unattributed in the entry, hence Alexander
         Adamchuk, Oct 31 2006, as entry author):
  Conjecture: all a(n) except a(1) = 6 and a(2) = 10 are odd. Conjecture:
  all a(n) except a(5) = 35 are triangular numbers of the form p*(2p ± 1)
  that belong to A068443(n) = {6, 10, 15, 21, 55, 91, 253, 703, 1081, 1711,
  1891, 2701, ...} Triangular numbers with two distinct prime factors.
(In the entry `±` is spelled plus, slash, minus; a slash followed by a
 minus would open a nested Lean comment.)
PROGRAM (Mathematica, Robert G. Wilson v): ... If[PrimeOmega@ b == 2, ...]
```

## Status

Triage: open (no proof in the entry; no published classification found).
The proof below is the elementary argument recorded by the triage:
every prime power `p ^ v_p(C(n,k))` is at most `n`
(`Nat.pow_factorization_choose_le`), so a semiprime `C(n,k)` is at most
`n ^ 2`; for `3 ≤ k ≤ n - 3` we have `C(n,k) ≥ C(n,3) > n ^ 2` once
`n ≥ 9`, leaving the finite range `n ≤ 8`, where only `C(7,3) = C(7,4) = 35`
is a semiprime.  For `k = 2` (and `k = n - 2`), `C(n,2) = m(2m ∓ 1)` with
both factors at least `2`, so both are prime.

Note that `p(2p+1) = (2p)(2p+1)/2` and `p(2p-1) = (2p-1)(2p)/2` are
triangular with two distinct prime factors automatically, so the
membership in A068443 asserted by the conjecture is the `p(2p ± 1)` form.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A124000BinomialCoefficientSemiprime

/-! ## Definitions -/

/-- A semiprime: a natural number with exactly two prime factors counted with
multiplicity (`PrimeOmega[m] == 2` in the entry's program, OEIS A001358). -/
def IsSemiprime (m : ℕ) : Prop := m.primeFactorsList.length = 2

/-- Membership in A124000: `m` is a semiprime binomial coefficient `C(n,k)` with
`2 ≤ k ≤ n - 2` (stated as `k + 2 ≤ n` to avoid truncated subtraction). -/
def IsTerm (m : ℕ) : Prop :=
  IsSemiprime m ∧ ∃ n k : ℕ, 2 ≤ k ∧ k + 2 ≤ n ∧ n.choose k = m

/-! ## Ground truth -/

example : IsSemiprime 6 := by simp [IsSemiprime, Nat.primeFactorsList_ofNat]
example : IsSemiprime 35 := by simp [IsSemiprime, Nat.primeFactorsList_ofNat]
example : ¬ IsSemiprime 20 := by simp [IsSemiprime, Nat.primeFactorsList_ofNat]
example : ¬ IsSemiprime 7 := by simp [IsSemiprime, Nat.primeFactorsList_ofNat]

example : IsTerm 6 :=
  ⟨by simp [IsSemiprime, Nat.primeFactorsList_ofNat], 4, 2, le_rfl, le_rfl, by decide⟩
example : IsTerm 10 :=
  ⟨by simp [IsSemiprime, Nat.primeFactorsList_ofNat], 5, 2, le_rfl, by norm_num, by decide⟩
example : IsTerm 35 :=
  ⟨by simp [IsSemiprime, Nat.primeFactorsList_ofNat], 7, 3, by norm_num, by norm_num,
    by decide⟩

/-! ## Helper lemmas -/

/-- A semiprime binomial coefficient `C(n,k)` with `0 < n` is at most `n ^ 2`:
each of its two prime factors `p` satisfies `p ≤ p ^ v_p(C(n,k)) ≤ n`. -/
theorem choose_le_sq_of_isSemiprime {n k : ℕ} (hn : 0 < n)
    (h : IsSemiprime (n.choose k)) : n.choose k ≤ n ^ 2 := by
  have hc0 : n.choose k ≠ 0 := by
    intro h0
    simp [IsSemiprime, h0] at h
  have hle : ∀ p ∈ (n.choose k).primeFactorsList, p ≤ n := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd : p ∣ n.choose k := Nat.dvd_of_mem_primeFactorsList hp
    have h1 : 1 ≤ (n.choose k).factorization p :=
      (hpp.dvd_iff_one_le_factorization hc0).1 hdvd
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (n.choose k).factorization p := Nat.pow_le_pow_right hpp.pos h1
      _ ≤ n := Nat.pow_factorization_choose_le hn
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 h
  have hprod : p * q = n.choose k := by
    have hfl := Nat.prod_primeFactorsList hc0
    rw [hpq] at hfl
    simpa using hfl
  rw [← hprod, sq]
  exact Nat.mul_le_mul (hle p (by simp [hpq])) (hle q (by simp [hpq]))

/-- For `3 ≤ k` and `k + 3 ≤ n`, `C(n,3) ≤ C(n,k)`. -/
theorem choose_three_le {n k : ℕ} (hk : 3 ≤ k) (hkn : k + 3 ≤ n) :
    n.choose 3 ≤ n.choose k := by
  have key : ∀ j, 3 ≤ j → j ≤ n / 2 → n.choose 3 ≤ n.choose j := by
    intro j hj hjn
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  rcases le_or_gt k (n / 2) with hle | hgt
  · exact key k hk hle
  · rw [← Nat.choose_symm (by omega : k ≤ n)]
    exact key (n - k) (by omega) (by omega)

/-- `C(n,3) > n ^ 2` for `n ≥ 9`. -/
theorem sq_lt_choose_three {n : ℕ} (hn : 9 ≤ n) : n ^ 2 < n.choose 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have h6 : (m + 9).descFactorial 3 = Nat.factorial 3 * (m + 9).choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose (m + 9) 3
  have hdf : (m + 9).descFactorial 3 = (m + 7) * ((m + 8) * (m + 9)) := by
    simp [Nat.descFactorial]
  rw [hdf, show Nat.factorial 3 = 6 by rfl] at h6
  nlinarith

/-- **Classification for `3 ≤ k ≤ n - 3`.**  If `C(n,k)` is a semiprime with
`3 ≤ k` and `k + 3 ≤ n`, then `n = 7` and `k ∈ {3, 4}`, i.e. `C(n,k) = 35`. -/
theorem eq_seven_of_isSemiprime_choose {n k : ℕ} (hk : 3 ≤ k) (hkn : k + 3 ≤ n)
    (h : IsSemiprime (n.choose k)) : n = 7 ∧ (k = 3 ∨ k = 4) := by
  have hn9 : n ≤ 8 := by
    by_contra hlt
    have h1 := choose_le_sq_of_isSemiprime (by omega) h
    have h2 := choose_three_le hk hkn
    have h3 := sq_lt_choose_three (n := n) (by omega)
    omega
  have hk5 : k ≤ 5 := by omega
  interval_cases n <;> interval_cases k <;>
    simp_all [IsSemiprime, Nat.choose, Nat.primeFactorsList_ofNat]

/-- If `a * b` is a semiprime with `2 ≤ a` and `2 ≤ b`, then `a` and `b` are prime. -/
theorem prime_and_prime_of_isSemiprime_mul {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : IsSemiprime (a * b)) : a.Prime ∧ b.Prime := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hΩ : ArithmeticFunction.cardFactors (a * b) = 2 := by
    rw [ArithmeticFunction.cardFactors_apply]
    exact h
  rw [ArithmeticFunction.cardFactors_mul ha0 hb0] at hΩ
  have hpos : ∀ c : ℕ, 2 ≤ c → 0 < ArithmeticFunction.cardFactors c := by
    intro c hc
    rw [ArithmeticFunction.cardFactors_apply]
    exact List.length_pos_iff.2 (by rw [Ne, Nat.primeFactorsList_eq_nil]; omega)
  have hpa := hpos a ha
  have hpb := hpos b hb
  exact ⟨ArithmeticFunction.cardFactors_eq_one_iff_prime.1 (by omega),
    ArithmeticFunction.cardFactors_eq_one_iff_prime.1 (by omega)⟩

/-- **The case `k = 2`.**  If `C(n,2)` is a semiprime with `4 ≤ n`, then
`C(n,2) = p(2p+1)` or `p(2p-1)` with `p` and `2p ± 1` prime. -/
theorem choose_two_of_isSemiprime {n : ℕ} (hn : 4 ≤ n) (h : IsSemiprime (n.choose 2)) :
    ∃ p : ℕ, p.Prime ∧ (((2 * p + 1).Prime ∧ n.choose 2 = p * (2 * p + 1)) ∨
      ((2 * p - 1).Prime ∧ n.choose 2 = p * (2 * p - 1))) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hc : (2 * m).choose 2 = m * (2 * m - 1) := by
      rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [hc] at h ⊢
    obtain ⟨hp, hq⟩ := prime_and_prime_of_isSemiprime_mul (by omega) (by omega) h
    exact ⟨m, hp, Or.inr ⟨hq, rfl⟩⟩
  · have hc : (2 * m + 1).choose 2 = m * (2 * m + 1) := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel,
        show (2 * m + 1) * (2 * m) = 2 * (m * (2 * m + 1)) by ring,
        Nat.mul_div_cancel_left _ two_pos]
    rw [hc] at h ⊢
    obtain ⟨hp, hq⟩ := prime_and_prime_of_isSemiprime_mul (by omega) (by omega) h
    exact ⟨m, hp, Or.inl ⟨hq, rfl⟩⟩

/-! ## The conjecture -/

/-- **Conjecture (ii) of A124000 (Alexander Adamchuk, Oct 31 2006).**
Verbatim: "Conjecture: all a(n) except a(5) = 35 are triangular numbers of the
form p*(2p ± 1) that belong to A068443".  Every semiprime binomial coefficient
`C(n,k)` with `2 ≤ k ≤ n - 2` is either `35` or `p(2p+1)` or `p(2p-1)` with `p`
and `2p ± 1` both prime (such numbers are triangular, `T(2p)` resp. `T(2p-1)`,
with two distinct prime factors). -/
theorem conjecture_ii {m : ℕ} (hm : IsTerm m) :
    m = 35 ∨ ∃ p : ℕ, p.Prime ∧ (((2 * p + 1).Prime ∧ m = p * (2 * p + 1)) ∨
      ((2 * p - 1).Prime ∧ m = p * (2 * p - 1))) := by
  obtain ⟨hs, n, k, hk, hkn, rfl⟩ := hm
  rcases (show k = 2 ∨ k + 2 = n ∨ (3 ≤ k ∧ k + 3 ≤ n) by omega) with
    rfl | hkn2 | ⟨hk3, hkn3⟩
  · exact Or.inr (choose_two_of_isSemiprime hkn hs)
  · have hsym : n.choose k = n.choose 2 := Nat.choose_symm_of_eq_add hkn2.symm
    rw [hsym] at hs ⊢
    exact Or.inr (choose_two_of_isSemiprime (by omega) hs)
  · obtain ⟨rfl, rfl | rfl⟩ := eq_seven_of_isSemiprime_choose hk3 hkn3 hs
    · left; decide
    · left; decide

/-- **Conjecture (i) of A124000 (Alexander Adamchuk, Oct 31 2006).**
Verbatim: "Conjecture: all a(n) except a(1) = 6 and a(2) = 10 are odd."
Every semiprime binomial coefficient `C(n,k)` with `2 ≤ k ≤ n - 2` is odd,
or equal to `6` or `10`. -/
theorem conjecture_i {m : ℕ} (hm : IsTerm m) : Odd m ∨ m = 6 ∨ m = 10 := by
  rcases conjecture_ii hm with rfl | ⟨p, hp, ⟨hq, rfl⟩ | ⟨hq, rfl⟩⟩
  · exact Or.inl ⟨17, rfl⟩
  · rcases hp.eq_two_or_odd' with rfl | hodd
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (hodd.mul (odd_two_mul_add_one p))
  · rcases hp.eq_two_or_odd' with rfl | hodd
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hodd.mul (hq.eq_two_or_odd'.resolve_left (by omega)))

end Candidates.A124000BinomialCoefficientSemiprime
