/-
# A229989 — Kimberling: the drops of a(n) occur exactly at n = 2*prime(m+1) - 1

Clark Kimberling's conjectures in OEIS A229989 (2013), where `a(n)` counts
primes in `[floor(n/2),floor(3n/2)]` (offset 1).

Part (3), hence the conjunction of the three conjectures, is false.  At `n = 23` we have `a(23) = 7` (primes 11..31 in `[11, 34]`) and
`a(24) = 6` (primes 13..31 in `[12, 36]`), so `a(24) - a(23) = -1`, yet
`23 = 2*q - 1` forces `q = 12`, which is not prime.  This holds whatever the
range of the index `m`.  The converse direction also fails: `9 = 2*prime(3) - 1`
but `a(10) - a(9) = 0`.

Parts (1) and (2) are true and proved below (`a229989_rises_infinite`,
`a229989_drops_infinite`), together with the corrected form of (3):
`a(n+1) - a(n) = -1` iff `n = 2p + 1` with `p` prime and `3p + 2` composite
(`a229989_drop_iff`).  The proof is elementary: writing `c = Nat.count Nat.Prime`,
`a(n) = c(⌊3n/2⌋ + 1) - c(⌊n/2⌋)`; the step at `n = 2k` is `[3k+1 prime]` and
the step at `n = 2k+1` is `[3k+2 prime] + [3k+3 prime] - [k prime]`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A229989Refutation

open Finset

/-! ## Definitions -/

/-- OEIS A229989: `a(n)` is the number of primes in the closed interval
`[⌊n/2⌋, ⌊3n/2⌋]` (OEIS offset 1; `a 0 = 0` is a harmless extension). -/
def a229989 (n : ℕ) : ℕ := #{p ∈ Icc (n / 2) (3 * n / 2) | p.Prime}

/-- Examples: `a(1), …, a(40)` match the OEIS data. -/
example : (List.range 40).map (fun i => a229989 (i + 1)) =
    [0, 2, 2, 3, 4, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 6, 7, 7, 7, 6, 7, 7, 7, 7, 8, 8,
      8, 9, 9, 9, 9, 9, 9, 9, 9, 9] := by
  decide

/-- Examples: `a(41), …, a(47)` match the OEIS data. -/
example : (List.range 7).map (fun i => a229989 (i + 41)) = [10, 10, 10, 10, 11, 11, 11] := by
  decide

/-- Examples: `a(48), …, a(54)` match the OEIS data. -/
example : (List.range 7).map (fun i => a229989 (i + 48)) = [11, 12, 12, 12, 12, 13, 13] := by
  decide

/-- Examples: `a(55), …, a(61)` match the OEIS data. -/
example : (List.range 7).map (fun i => a229989 (i + 55)) = [13, 14, 14, 14, 14, 14, 14] := by
  decide

/-- Examples: `a(62), …, a(68)` match the OEIS data. -/
example : (List.range 7).map (fun i => a229989 (i + 62)) = [14, 14, 13, 14, 14, 14, 15] := by
  decide

/-- Examples: `a(69), …, a(75)` match the OEIS data. -/
example : (List.range 7).map (fun i => a229989 (i + 69)) = [16, 16, 16, 17, 18, 18, 18] := by
  decide

/-- Kimberling's conjectures (1)–(3) on A229989, stated over the OEIS domain
`n ≥ 1`, with `prime(m+1)` (1-indexed) rendered as `Nat.nth Nat.Prime m`
(0-indexed):

1. `a(n+1) - a(n) = 1` for infinitely many `n`;
2. `a(n+1) - a(n) = -1` for infinitely many `n`;
3. for `n ≥ 1`, `a(n+1) - a(n) = -1` iff `n = 2 * prime(m+1) - 1` for some `m`.

Differences are taken in `ℤ`; the `ℕ` subtraction `2 * q - 1` is exact since
every prime `q` is at least `2`. -/
def Conjecture : Prop :=
  {n : ℕ | 1 ≤ n ∧ (a229989 (n + 1) : ℤ) - a229989 n = 1}.Infinite ∧
  {n : ℕ | 1 ≤ n ∧ (a229989 (n + 1) : ℤ) - a229989 n = -1}.Infinite ∧
  ∀ n : ℕ, 1 ≤ n →
    ((a229989 (n + 1) : ℤ) - a229989 n = -1 ↔ ∃ m : ℕ, n = 2 * Nat.nth Nat.Prime m - 1)

/-! ## The refutation -/

/-- `a(23) = 7`: the primes in `[11, 34]` are `11, 13, 17, 19, 23, 29, 31`. -/
theorem a229989_twentythree : a229989 23 = 7 := by decide

/-- `a(24) = 6`: the primes in `[12, 36]` are `13, 17, 19, 23, 29, 31`. -/
theorem a229989_twentyfour : a229989 24 = 6 := by decide

/-- Kimberling's conjecture on A229989 is false: part (3) fails at `n = 23`,
where `a(24) - a(23) = 6 - 7 = -1` although `23 = 2q - 1` would need `q = 12`,
which is not prime.  The corrected characterization is
`a(n+1) - a(n) = -1 ↔ n = 2p + 1` with `p` prime and `3p + 2` composite
(`a229989_drop_iff`). -/
theorem a229989_conjecture_false : ¬ Conjecture := by
  rintro ⟨-, -, hiff⟩
  have hdrop : (a229989 (23 + 1) : ℤ) - a229989 23 = -1 := by
    rw [a229989_twentythree, a229989_twentyfour]
    norm_num
  obtain ⟨m, hm⟩ := (hiff 23 (by norm_num)).mp hdrop
  have hprime : (Nat.nth Nat.Prime m).Prime := Nat.prime_nth_prime m
  have h12 : Nat.nth Nat.Prime m = 12 := by omega
  rw [h12] at hprime
  norm_num at hprime

/-- The "if" direction of conjecture (3) also fails: `9 = 2 * prime(3) - 1`
(`prime(3) = 5`), but `a(10) - a(9) = 4 - 4 = 0`. -/
theorem a229989_conjecture3_if_fails :
    (∃ m : ℕ, 9 = 2 * Nat.nth Nat.Prime m - 1) ∧
      (a229989 (9 + 1) : ℤ) - a229989 9 ≠ -1 := by
  refine ⟨⟨2, by rw [Nat.nth_prime_two_eq_five]⟩, ?_⟩
  have h9 : a229989 9 = 4 := by decide
  have h10 : a229989 10 = 4 := by decide
  rw [h9, h10]
  norm_num

/-! ## The corrected statement and parts (1), (2) -/

/-- Counting the elements of `[lo, hi)` satisfying `p` via `Nat.count`. -/
theorem card_filter_Ico_eq_count_sub (p : ℕ → Prop) [DecidablePred p] {lo hi : ℕ}
    (h : lo ≤ hi) : #{x ∈ Ico lo hi | p x} = Nat.count p hi - Nat.count p lo := by
  induction hi, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hmono : Nat.count p lo ≤ Nat.count p m := Nat.count_monotone p hm
    rw [Nat.Ico_succ_right_eq_insert_Ico hm, filter_insert, Nat.count_succ]
    split_ifs with hpm
    · rw [card_insert_of_notMem (by simp)]
      omega
    · omega

/-- `a(n) = π(⌊3n/2⌋) - π(⌊n/2⌋ - 1)`, written with `Nat.count Nat.Prime`
(the number of primes below its argument) and cast to `ℤ`. -/
theorem a229989_cast_eq (n : ℕ) :
    (a229989 n : ℤ) = Nat.count Nat.Prime (3 * n / 2 + 1) - Nat.count Nat.Prime (n / 2) := by
  have hle : n / 2 ≤ 3 * n / 2 + 1 := by omega
  have hcard :
      a229989 n = Nat.count Nat.Prime (3 * n / 2 + 1) - Nat.count Nat.Prime (n / 2) := by
    rw [a229989, ← Finset.Ico_add_one_right_eq_Icc, card_filter_Ico_eq_count_sub Nat.Prime hle]
  rw [hcard, Nat.cast_sub (Nat.count_monotone _ hle)]

/-- The step of A229989 at an even index `2k` is `[3k + 1 is prime]`. -/
theorem a229989_diff_even (k : ℕ) :
    (a229989 (2 * k + 1) : ℤ) - a229989 (2 * k) = if (3 * k + 1).Prime then 1 else 0 := by
  rw [a229989_cast_eq, a229989_cast_eq]
  have h1 : 3 * (2 * k + 1) / 2 + 1 = (3 * k + 1) + 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  have h3 : 3 * (2 * k) / 2 + 1 = 3 * k + 1 := by omega
  have h4 : 2 * k / 2 = k := by omega
  rw [h1, h2, h3, h4, Nat.count_succ]
  split_ifs <;> push_cast <;> ring

/-- The step of A229989 at an odd index `2k + 1` is
`[3k + 2 is prime] + [3k + 3 is prime] - [k is prime]`. -/
theorem a229989_diff_odd (k : ℕ) :
    (a229989 (2 * k + 1 + 1) : ℤ) - a229989 (2 * k + 1) =
      (if (3 * k + 2).Prime then 1 else 0) + (if (3 * k + 3).Prime then 1 else 0) -
        (if k.Prime then 1 else 0) := by
  rw [a229989_cast_eq, a229989_cast_eq]
  have h1 : 3 * (2 * k + 1 + 1) / 2 + 1 = (3 * k + 2) + 1 + 1 := by omega
  have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h3 : 3 * (2 * k + 1) / 2 + 1 = 3 * k + 2 := by omega
  have h4 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, h3, h4, Nat.count_succ, Nat.count_succ, Nat.count_succ Nat.Prime k]
  have h5 : 3 * k + 2 + 1 = 3 * k + 3 := by omega
  rw [h5]
  split_ifs <;> push_cast <;> ring

/-- Corrected conjecture (3): `a(n+1) - a(n) = -1` iff `n = 2p + 1` for a prime
`p` with `3p + 2` composite (valid for every `n`, in particular `n ≥ 1`). -/
theorem a229989_drop_iff (n : ℕ) :
    (a229989 (n + 1) : ℤ) - a229989 n = -1 ↔
      ∃ p : ℕ, p.Prime ∧ n = 2 * p + 1 ∧ ¬ (3 * p + 2).Prime := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [a229989_diff_even]
    constructor
    · intro h
      split_ifs at h
    · rintro ⟨p, -, hp, -⟩
      omega
  · rw [a229989_diff_odd]
    have h3 : (3 * k + 3).Prime ↔ k = 0 := by
      constructor
      · intro hpr
        have hdvd : 3 ∣ 3 * k + 3 := ⟨k + 1, by ring⟩
        rcases Nat.Prime.eq_one_or_self_of_dvd hpr 3 hdvd with h | h <;> omega
      · rintro rfl
        norm_num
    constructor
    · intro h
      refine ⟨k, ?_, rfl, ?_⟩
      · by_contra hk
        simp only [hk, if_false] at h
        split_ifs at h <;> omega
      · intro hk2
        simp only [hk2, if_true] at h
        split_ifs at h <;> omega
    · rintro ⟨p, hp, hpk, hp2⟩
      have hkp : k = p := by omega
      subst hkp
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact Nat.not_prime_zero hp
      simp only [hp, hp2, h3, hk0, if_true, if_false]
      norm_num

/-- Conjecture (1) holds: `a(n+1) - a(n) = 1` for infinitely many `n ≥ 1`
(take `n = 2k` with `3k + 1` a prime, of which there are infinitely many). -/
theorem a229989_rises_infinite :
    {n : ℕ | 1 ≤ n ∧ (a229989 (n + 1) : ℤ) - a229989 n = 1}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hNp, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 3) (3 * N) (by norm_num)
  have hmod' : p % 3 = 1 := hmod
  have hp2 : 2 ≤ p := hp.two_le
  refine ⟨2 * (p / 3), ⟨by omega, ?_⟩, by omega⟩
  rw [a229989_diff_even]
  have hq : 3 * (p / 3) + 1 = p := by omega
  simp [hq, hp]

/-- Conjecture (2) holds: `a(n+1) - a(n) = -1` for infinitely many `n ≥ 1`
(take `n = 2p + 1` with `p ≡ 1 (mod 5)` prime, so that `5 ∣ 3p + 2`). -/
theorem a229989_drops_infinite :
    {n : ℕ | 1 ≤ n ∧ (a229989 (n + 1) : ℤ) - a229989 n = -1}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hNp, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 5) (N + 5) (by norm_num)
  have hmod' : p % 5 = 1 := hmod
  refine ⟨2 * p + 1, ⟨by omega, ?_⟩, by omega⟩
  rw [a229989_drop_iff]
  refine ⟨p, hp, rfl, ?_⟩
  intro hpr
  have hdvd : 5 ∣ 3 * p + 2 := by omega
  rcases Nat.Prime.eq_one_or_self_of_dvd hpr 5 hdvd with h | h <;> omega

end Candidates.A229989Refutation
