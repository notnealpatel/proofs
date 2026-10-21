/-
# A086534 — the sandwiched-prime sequence is infinite

## OEIS source (retrieved 2026-10-21; local `oeis show A086534` and the live
## internal-format entry https://oeis.org/A086534/internal)

```
%N A086534 Smallest prime p sandwiched between two numbers that are
           divisible by n-th powers.
%S A086534 2,17,271,1249,13121,13121,153089,1272833,28146689,193562623,...
%C A086534 Conjecture: sequence is finite.
%e A086534 a(3) = 271, 270 = 3^3*10 and 272 = 2^3*34. 271 is the smallest
           such number.
%e A086534 a(4) = 1249, 1248 =2^4*78, 1250 = 5^4*2. 1250 is the smallest
           such number.
%A A086534 _Amarnath Murthy_, Aug 17 2003
%E A086534 Edited and extended by _Robert G. Wilson v_, Aug 18 2003
%E A086534 a(5) corrected. a(13)-a(22) from _Donovan Johnson_, Sep 02 2008
```

The conjecture comment carries no separate signature; it is part of the
original submission (_Amarnath Murthy_, Aug 17 2003).  No later comment
retracts it.

## This module refutes the conjecture

By the Chinese remainder theorem there is a residue `c` modulo `2^n * 3^n`
with `c ≡ 1 [MOD 2^n]` and `c ≡ -1 [MOD 3^n]`; it is coprime to the modulus,
so Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`) yields
infinitely many primes `p ≡ c`, each with `2^n ∣ p - 1` and `3^n ∣ p + 1`.
Hence `a(n)` exists for every `n` and the sequence is infinite.

## Definitional fidelity

"Divisible by an `n`-th power" is read as divisible by `b^n` with `b ≥ 2`
(otherwise `1^n` divides everything).  This matches the listed terms for
`n ≥ 2` (checked below for `n = 2, 3` in the kernel; Sage confirms
`n = 2, ..., 6`).  The listed `a(1) = 2` uses the degenerate convention that
`p - 1 = 1` counts; under the `b ≥ 2` reading `a(1) = 3`.  The single index
`n = 1` does not affect finiteness.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086534Refutation

/-- `m` is divisible by the `n`-th power `b ^ n` of some integer `b ≥ 2`. -/
def HasNthPowerDivisor (n m : ℕ) : Prop := ∃ b, 2 ≤ b ∧ b ^ n ∣ m

/-- `p` is a prime sandwiched between two numbers, `p - 1` and `p + 1`, each
divisible by an `n`-th power `b ^ n` with `b ≥ 2`.  (`p - 1` is truncated
subtraction, but `p` prime gives `1 ≤ p`.) -/
def IsSandwichedPrime (n p : ℕ) : Prop :=
  p.Prime ∧ HasNthPowerDivisor n (p - 1) ∧ HasNthPowerDivisor n (p + 1)

/-- **A086534 conjecture** (Amarnath Murthy, Aug 17 2003): "Conjecture:
sequence is finite."  That is, only finitely many indices `n` admit a prime
sandwiched between two numbers divisible by `n`-th powers. -/
def Conjecture : Prop := {n : ℕ | ∃ p, IsSandwichedPrime n p}.Finite

/-- Core construction: for every `n` and every bound `N` there is a prime
`p > N` with `2 ^ n ∣ p - 1` and `3 ^ n ∣ p + 1` (CRT plus Dirichlet). -/
theorem exists_prime_gt_two_pow_dvd_sub_three_pow_dvd_add (n N : ℕ) :
    ∃ p, N < p ∧ p.Prime ∧ 2 ^ n ∣ p - 1 ∧ 3 ^ n ∣ p + 1 := by
  have hco : Nat.Coprime (2 ^ n) (3 ^ n) := Nat.Coprime.pow n n (by norm_num)
  let c := Nat.chineseRemainder hco 1 (3 ^ n - 1)
  have hc2 : (c : ℕ) ≡ 1 [MOD 2 ^ n] := c.2.1
  have hc3 : (c : ℕ) ≡ 3 ^ n - 1 [MOD 3 ^ n] := c.2.2
  have h3pos : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hcop2 : Nat.Coprime (c : ℕ) (2 ^ n) := by
    rw [Nat.Coprime, hc2.gcd_eq, Nat.gcd_one_left]
  have hcop3 : Nat.Coprime (c : ℕ) (3 ^ n) := by
    rw [Nat.Coprime, hc3.gcd_eq]
    have hsub : 3 ^ n = (3 ^ n - 1) + 1 := by omega
    rw [hsub, Nat.add_sub_cancel, Nat.gcd_self_add_right, Nat.gcd_one_right]
  have hq : 2 ^ n * 3 ^ n ≠ 0 := by positivity
  obtain ⟨p, hpN, hp, hpc⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N hq (Nat.Coprime.mul_right hcop2 hcop3)
  have hp2 : p ≡ 1 [MOD 2 ^ n] := (hpc.of_mul_right _).trans hc2
  have hp3 : p ≡ 3 ^ n - 1 [MOD 3 ^ n] := (hpc.of_mul_left _).trans hc3
  refine ⟨p, hpN, hp, ?_, ?_⟩
  · exact (Nat.modEq_iff_dvd' hp.one_le).1 hp2.symm
  · have hsucc : p + 1 ≡ 3 ^ n - 1 + 1 [MOD 3 ^ n] := hp3.add_right 1
    rw [Nat.sub_add_cancel h3pos] at hsucc
    exact Nat.modEq_zero_iff_dvd.1 (hsucc.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))

/-- For every `n` there are arbitrarily large primes sandwiched between two
numbers divisible by `n`-th powers (witnesses `2 ^ n ∣ p - 1`, `3 ^ n ∣ p + 1`). -/
theorem exists_isSandwichedPrime_gt (n N : ℕ) : ∃ p, N < p ∧ IsSandwichedPrime n p := by
  obtain ⟨p, hpN, hp, h2, h3⟩ := exists_prime_gt_two_pow_dvd_sub_three_pow_dvd_add n N
  exact ⟨p, hpN, hp, ⟨2, le_rfl, h2⟩, ⟨3, by norm_num, h3⟩⟩

/-- For every `n` a sandwiched prime exists, so `a(n)` is defined for every `n`. -/
theorem exists_isSandwichedPrime (n : ℕ) : ∃ p, IsSandwichedPrime n p := by
  obtain ⟨p, -, hp⟩ := exists_isSandwichedPrime_gt n 0
  exact ⟨p, hp⟩

/-- **Refutation of the A086534 conjecture.**  The sequence is infinite: every
index `n` admits a sandwiched prime (a prime `p ≡ 1 [MOD 2^n]`,
`p ≡ -1 [MOD 3^n]` from Dirichlet's theorem), so the index set is all of `ℕ`.
For instance `n = 3` gives `p = 593`, `n = 10` gives `p = 411099137`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hfin
  have huniv : {n : ℕ | ∃ p, IsSandwichedPrime n p} = Set.univ :=
    Set.eq_univ_of_forall exists_isSandwichedPrime
  rw [Conjecture, huniv] at hfin
  exact Set.infinite_univ hfin

/-- The phrasing "for some `n` there is no such prime" is refuted as well. -/
theorem not_exists_index_without_isSandwichedPrime :
    ¬ ∃ n, ¬ ∃ p, IsSandwichedPrime n p := by
  rintro ⟨n, hn⟩
  exact hn (exists_isSandwichedPrime n)

/-- A086534: the smallest prime sandwiched between two numbers divisible by
`n`-th powers `b ^ n`, `b ≥ 2` (well defined by `exists_isSandwichedPrime`). -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in Nat.find (exists_isSandwichedPrime n)

/-- For `1 ≤ n` and `0 < m`, a witness `b` for `HasNthPowerDivisor n m` lies in
`[2, m]`, giving a decidable bounded form. -/
theorem hasNthPowerDivisor_iff_bounded {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m) :
    HasNthPowerDivisor n m ↔ ∃ b ∈ Finset.Icc 2 m, b ^ n ∣ m := by
  constructor
  · rintro ⟨b, hb, hdvd⟩
    have hle : b ^ n ≤ m := Nat.le_of_dvd hm hdvd
    have hself : b ≤ b ^ n := Nat.le_self_pow (by omega) b
    exact ⟨b, Finset.mem_Icc.2 ⟨hb, hself.trans hle⟩, hdvd⟩
  · rintro ⟨b, hb, hdvd⟩
    exact ⟨b, (Finset.mem_Icc.1 hb).1, hdvd⟩

/-- Bounded, decidable form of `IsSandwichedPrime` for `1 ≤ n` and `2 ≤ p`. -/
theorem isSandwichedPrime_iff_bounded {n p : ℕ} (hn : 1 ≤ n) (hp : 2 ≤ p) :
    IsSandwichedPrime n p ↔ p.Prime ∧ (∃ b ∈ Finset.Icc 2 (p - 1), b ^ n ∣ p - 1) ∧
      ∃ b ∈ Finset.Icc 2 (p + 1), b ^ n ∣ p + 1 := by
  rw [IsSandwichedPrime, hasNthPowerDivisor_iff_bounded hn (by omega),
    hasNthPowerDivisor_iff_bounded hn (by omega)]

/-- Ground truth: `a(2) = 17` (`16 = 2^4`, `18 = 3^2 * 2`). -/
example : a 2 = 17 := by
  classical
  rw [a, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ⟨2, le_rfl, by norm_num⟩, ⟨3, by norm_num, by norm_num⟩⟩, ?_⟩
  intro k hk hkS
  have hk2 : 2 ≤ k := hkS.1.two_le
  rw [isSandwichedPrime_iff_bounded (by norm_num) hk2] at hkS
  revert hkS
  revert k
  decide

set_option maxRecDepth 100000 in
/-- Ground truth: `a(3) = 271` (`270 = 3^3 * 10`, `272 = 2^3 * 34`). -/
example : a 3 = 271 := by
  classical
  rw [a, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ⟨3, by norm_num, by norm_num⟩, ⟨2, le_rfl, by norm_num⟩⟩, ?_⟩
  intro k hk hkS
  have hk2 : 2 ≤ k := hkS.1.two_le
  rw [isSandwichedPrime_iff_bounded (by norm_num) hk2] at hkS
  revert hkS
  revert k
  decide

end Candidates.A086534Refutation
