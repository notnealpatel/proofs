/-
# A088212 — Seidov: every integer `k ≥ 2` is a value of `a(n) = min{k > 1 : n + k^2 prime}`

## OEIS source (pulled with `oeis show A088212`, retrieved 2026-10-21)

```
NAME:     Smallest k>1 such that n+k^2 is prime.
TERMS:    2,3,2,3,6,5,2,3,2,3,6,5,2,3,2,5,6,5,2,3,4,3,6,7,2,9,2,3,12,7,4,3,2,
          3,6,5,2,3,2,7,24,5,2,3,4,5,6,5,2,3,4,3,6,5,2,9,2,3,18,7,6,3,2,3,6,
          25,2,9,2,3,6,5,4,3,2,5,6,5,2,3,4,5,12,5,2,9,4,3,12,7,4,3,2,3,6,19,
          2,3,2,3,6,5,2
OFFSET:   n starts at 1 (a(1) = 2 since 1 + 2^2 = 5 is prime).
COMMENT (the conjecture):
  Conjecture: all integers >1  eventually appear. Among first 300000 terms,
  first absent integers are 113, 119, 122, 124, 127, 130, 134, 136, 137, 139,
  140, ... - _Zak Seidov_, Jun 06 2013
```

## Status

Triage status: open (no proof in the entry or in the literature found by the
triage).  Computation (2026-10-21) extends Seidov's table: the first `n` with
`a(n) = 113, 124, 122, 119` are `314760, 369171, 373635, 418116`, all just past
Seidov's bound of 300000.

This file proves the conjecture.  The argument is Chinese remaindering plus
Dirichlet's theorem on primes in arithmetic progressions
(`Nat.forall_exists_prime_gt_and_eq_mod`): for `2 ≤ j < k` pick distinct primes
`q_j > 2k`, a residue `n₀ ≡ -j^2 (mod q_j)`, and a prime
`P ≡ n₀ + k^2 (mod ∏ q_j)` that is large; then `n = P - k^2` works.

## Definitional-fidelity note

Whether `n + k^2` is prime for some `k > 1` is not known for every `n`
(it is a Bunyakovsky-type question), so `a` is defined as an `sInf` over
`{k | 1 < k ∧ (n + k^2).Prime}`, whose junk value on the empty set is `0`.
The conjecture concerns values `k ≥ 2`, which the junk value never attains, and
`a_eq_iff` characterises `a n = k` for `k ≥ 2` exactly as the entry's
"smallest `k > 1`" (in particular, it forces the set to be nonempty).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A088212MinPrimeEquals

/-- OEIS A088212: `a n` is the smallest `k > 1` such that `n + k^2` is prime
(junk value `0` if no such `k` exists). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 < k ∧ (n + k ^ 2).Prime}

/-- For `k ≥ 2`, `a n = k` iff `n + k^2` is prime and `n + j^2` is not prime for
every `2 ≤ j < k`. -/
theorem a_eq_iff {n k : ℕ} (hk : 2 ≤ k) :
    a n = k ↔ (n + k ^ 2).Prime ∧ ∀ j, 2 ≤ j → j < k → ¬ (n + j ^ 2).Prime := by
  constructor
  · intro h
    have hne : {k : ℕ | 1 < k ∧ (n + k ^ 2).Prime}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : a n = 0 := by rw [a, hemp, Nat.sInf_empty]
      omega
    have hmem := Nat.sInf_mem hne
    rw [← a, h] at hmem
    refine ⟨hmem.2, fun j hj hjk hjp => ?_⟩
    have hlt : j < sInf {k : ℕ | 1 < k ∧ (n + k ^ 2).Prime} := by rw [← a, h]; exact hjk
    exact Nat.notMem_of_lt_sInf hlt ⟨by omega, hjp⟩
  · rintro ⟨hp, hmin⟩
    have hmem : k ∈ {k : ℕ | 1 < k ∧ (n + k ^ 2).Prime} := ⟨by omega, hp⟩
    apply le_antisymm (Nat.sInf_le hmem)
    apply le_csInf ⟨k, hmem⟩
    rintro m ⟨hm1, hmp⟩
    by_contra hlt
    exact hmin m (by omega) (by omega) hmp

/-! ## Ground truth against the listed terms: `a(1) = 2`, `a(5) = 6`, `a(41) = 24`. -/

example : a 1 = 2 := by
  rw [a_eq_iff le_rfl]; refine ⟨by norm_num, fun j hj hjk => by omega⟩

example : a 5 = 6 := by
  rw [a_eq_iff (by norm_num)]
  refine ⟨by norm_num, fun j hj hjk => ?_⟩
  interval_cases j <;> norm_num

example : a 41 = 24 := by
  rw [a_eq_iff (by norm_num)]
  refine ⟨by norm_num, fun j hj hjk => ?_⟩
  interval_cases j <;> norm_num

/-- Core construction: for every `k ≥ 2` there is `n ≥ 1` with `n + k^2` prime
and `n + j^2` composite for all `2 ≤ j < k` (CRT + Dirichlet). -/
theorem exists_n_minimal (k : ℕ) (hk : 2 ≤ k) :
    ∃ n, 1 ≤ n ∧ (n + k ^ 2).Prime ∧ ∀ j, 2 ≤ j → j < k → ¬ (n + j ^ 2).Prime := by
  let t : Finset ℕ := Finset.Ico 2 k
  let q : ℕ → ℕ := fun j => Nat.nth Nat.Prime (2 * k + j)
  have hqprime : ∀ j, (q j).Prime := fun j => Nat.prime_nth_prime _
  have hqbig : ∀ j, 2 * k < q j := fun j => by
    have hle := Nat.add_two_le_nth_prime (2 * k + j)
    simp only [q]; omega
  have hqinj : Function.Injective q := fun i j hij => by
    have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hidx : 2 * k + i = 2 * k + j := hmono.injective hij
    omega
  let r : ℕ → ℕ := fun j => (q j - 1) * j ^ 2
  obtain ⟨n0, hn0⟩ := Nat.chineseRemainderOfFinset r q t
    (fun j _ => (hqprime j).ne_zero)
    (fun i _ j _ hij => (Nat.coprime_primes (hqprime i) (hqprime j)).2 (hqinj.ne hij))
  have hdiv0 : ∀ j ∈ t, q j ∣ n0 + j ^ 2 := by
    intro j hj
    have hrj : r j + j ^ 2 = q j * j ^ 2 := by
      simp only [r]
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (hqprime j).one_lt.le]
    have hmod : n0 + j ^ 2 ≡ r j + j ^ 2 [MOD q j] := (hn0 j hj).add_right _
    rw [hrj] at hmod
    exact (Nat.modEq_zero_iff_dvd).1
      (hmod.trans ((Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)))
  have hcop : ∀ j ∈ t, Nat.Coprime (n0 + k ^ 2) (q j) := by
    intro j hj
    have hjt := Finset.mem_Ico.1 hj
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hqprime j)]
    intro hd
    have hsub : q j ∣ (k + j) * (k - j) := by
      rw [← Nat.sq_sub_sq, ← Nat.add_sub_add_left n0 (k ^ 2) (j ^ 2)]
      exact Nat.dvd_sub hd (hdiv0 j hj)
    have hbig := hqbig j
    rcases (hqprime j).dvd_mul.1 hsub with h1 | h2
    · have hle := Nat.le_of_dvd (by omega) h1; omega
    · have hle := Nat.le_of_dvd (by omega) h2; omega
  let Q : ℕ := ∏ j ∈ t, q j
  have hQpos : 0 < Q := Finset.prod_pos fun j _ => (hqprime j).pos
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  have hunit : IsUnit ((n0 + k ^ 2 : ℕ) : ZMod Q) :=
    (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.prod_right hcop)
  obtain ⟨P, hPgt, hPprime, hPeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (k ^ 2 + Q)
  have hPmod : P ≡ n0 + k ^ 2 [MOD Q] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hPeq
  have hPk : P - k ^ 2 + k ^ 2 = P := Nat.sub_add_cancel (by omega)
  refine ⟨P - k ^ 2, by omega, by rwa [hPk], ?_⟩
  intro j hj2 hjk hprime
  have hjt : j ∈ t := Finset.mem_Ico.2 ⟨hj2, hjk⟩
  have hqQ : q j ∣ Q := Finset.dvd_prod_of_mem q hjt
  have hmodq : P - k ^ 2 + k ^ 2 ≡ n0 + k ^ 2 [MOD q j] := by
    rw [hPk]; exact Nat.ModEq.of_dvd hqQ hPmod
  have hn : P - k ^ 2 ≡ n0 [MOD q j] := Nat.ModEq.add_right_cancel' _ hmodq
  have hd : q j ∣ P - k ^ 2 + j ^ 2 := (Nat.modEq_zero_iff_dvd).1
    ((hn.add_right _).trans ((Nat.modEq_zero_iff_dvd).2 (hdiv0 j hjt)))
  have hqleQ : q j ≤ Q := Nat.le_of_dvd hQpos hqQ
  have hj4 : 4 ≤ j ^ 2 := by nlinarith
  rcases hprime.eq_one_or_self_of_dvd _ hd with h1 | h2
  · exact (hqprime j).one_lt.ne' h1
  · omega

/-- **Seidov's conjecture (A088212, Zak Seidov, Jun 06 2013), proved.**
Verbatim: "Conjecture: all integers >1 eventually appear."  That is, every
integer `k ≥ 2` equals `a(n)` for some `n ≥ 1`, where `a(n)` is the smallest
`k > 1` with `n + k^2` prime. -/
theorem seidov_conjecture (k : ℕ) (hk : 2 ≤ k) : ∃ n, 1 ≤ n ∧ a n = k := by
  obtain ⟨n, hn1, hp, hmin⟩ := exists_n_minimal k hk
  exact ⟨n, hn1, (a_eq_iff hk).2 ⟨hp, hmin⟩⟩

end Candidates.A088212MinPrimeEquals
