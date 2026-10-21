/-
# A067076 — Mathar: four descriptions of `(prime(n+1) - 3)/2`

## OEIS source (retrieved with `oeis show`, 2026-10-21)

```
A067076  NAME:  Numbers k such that 2*k + 3 is a prime.
         TERMS: 0,1,2,4,5,7,8,10,13,14,17,19,20,22,25,28,29,32,34,35,...
         FORMULA (the conjecture):
           Conjecture: a(n) = A008507(n) + n - 1 = A005097(n) - 1
           = A102781(n+1) - 1. - _R. J. Mathar_, Jul 07 2009
A008507  NAME:  Number of odd composite numbers less than n-th odd prime.
         TERMS: 0,0,0,1,1,2,2,3,5,5,7,8,8,9,11,...
A005097  NAME:  (Odd primes - 1)/2.
         TERMS: 1,2,3,5,6,8,9,11,14,15,...
A102781  NAME:  Number of positive even numbers less than the n-th prime.
         TERMS: 0,1,2,3,5,6,8,9,11,14,15,...
```

All four entries have offset 1.  The task statement adds the closed form
`a(n) = (prime(n+1) - 3)/2`, which is immediate from the A067076 name.

## Status

Triage: proved-elsewhere.  The identities are elementary consequences of the
definitions (A008507 records `a(n) = A067076(n) - n + 1`, Librandi 2013, and
`a(n) = (A000040(n+1) - 1)/2 - n`, van Tol 2026; A102781 is recorded as A005097
with a leading zero).  Numerically re-checked for `n ≤ 3000` (2026-10-21).
This module gives a kernel-checked proof of the whole chain.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A067076PrimeMathar


/-! ## Definition layer (all sequences 1-indexed, as in the OEIS) -/

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`); OEIS A000040.
`Nat.nth` is 0-indexed, hence the shift.  At `n = 0` the value is junk. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `oddPrime n` is the `n`-th odd prime, 1-indexed (`oddPrime 1 = 3`); A065091. -/
noncomputable def oddPrime (n : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ Odd p) (n - 1)

/-- A067076: the `n`-th (1-indexed) number `k` such that `2*k + 3` is prime. -/
noncomputable def a067076 (n : ℕ) : ℕ := Nat.nth (fun k => (2 * k + 3).Prime) (n - 1)

/-- A008507: number of odd composite numbers less than the `n`-th odd prime.
A composite number is one that is `> 1` and not prime. -/
noncomputable def a008507 (n : ℕ) : ℕ :=
  ((Finset.range (oddPrime n)).filter (fun m => Odd m ∧ 1 < m ∧ ¬ m.Prime)).card

/-- A005097: `(p - 1)/2` for the `n`-th odd prime `p` (the division is exact). -/
noncomputable def a005097 (n : ℕ) : ℕ := (oddPrime n - 1) / 2

/-- A102781: number of positive even numbers less than the `n`-th prime. -/
noncomputable def a102781 (n : ℕ) : ℕ :=
  ((Finset.range (prime n)).filter (fun e => 0 < e ∧ Even e)).card

/-! ## Ground truth against the OEIS DATA lines

Each value is certified independently of the conjecture: `Nat.nth p i = m`
follows from `p m` and `Nat.count p m = i` (`Nat.nth_count`), both decided. -/

/-- `Nat.nth p i = m` whenever `p m` holds and exactly `i` elements below `m`
satisfy `p`. -/
theorem nth_eq_of_count {p : ℕ → Prop} [DecidablePred p] {m i : ℕ} (hpm : p m)
    (hc : Nat.count p m = i) : Nat.nth p i = m := by
  rw [← hc]
  exact Nat.nth_count hpm

-- A000040: 2, 3, 5, 7, 11.
example : prime 1 = 2 ∧ prime 2 = 3 ∧ prime 3 = 5 ∧ prime 4 = 7 ∧ prime 5 = 11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact nth_eq_of_count (by norm_num) (by decide)

/-- Ground truth for `oddPrime` against A065091: the first five odd primes are
`3, 5, 7, 11, 13`. -/
theorem oddPrime_one_to_five : oddPrime 1 = 3 ∧ oddPrime 2 = 5 ∧ oddPrime 3 = 7 ∧
    oddPrime 4 = 11 ∧ oddPrime 5 = 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact nth_eq_of_count ⟨by norm_num, by decide⟩ (by decide)

-- A067076: 0, 1, 2, 4, 5, 7.
example : a067076 1 = 0 ∧ a067076 2 = 1 ∧ a067076 3 = 2 ∧ a067076 4 = 4 ∧
    a067076 5 = 5 ∧ a067076 6 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact nth_eq_of_count (by norm_num) (by decide)

-- A008507: 0, 0, 0, 1, 1.
example : a008507 1 = 0 ∧ a008507 2 = 0 ∧ a008507 3 = 0 ∧ a008507 4 = 1 ∧
    a008507 5 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := oddPrime_one_to_five
  simp only [a008507, h1, h2, h3, h4, h5]
  decide

-- A005097: 1, 2, 3, 5, 6.
example : a005097 1 = 1 ∧ a005097 2 = 2 ∧ a005097 3 = 3 ∧ a005097 4 = 5 ∧
    a005097 5 = 6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := oddPrime_one_to_five
  simp only [a005097, h1, h2, h3, h4, h5]
  decide

-- A102781: 0, 1, 2, 3, 5.
example : a102781 1 = 0 ∧ a102781 2 = 1 ∧ a102781 3 = 2 ∧ a102781 4 = 3 ∧
    a102781 5 = 5 := by
  have hp1 : prime 1 = 2 := nth_eq_of_count (by norm_num) (by decide)
  have hp2 : prime 2 = 3 := nth_eq_of_count (by norm_num) (by decide)
  have hp3 : prime 3 = 5 := nth_eq_of_count (by norm_num) (by decide)
  have hp4 : prime 4 = 7 := nth_eq_of_count (by norm_num) (by decide)
  have hp5 : prime 5 = 11 := nth_eq_of_count (by norm_num) (by decide)
  simp only [a102781, hp1, hp2, hp3, hp4, hp5]
  decide

/-! ## Counting lemmas, by induction on `k` with `x = 2*k + 3` -/

/-- Shifted primes `k ↦ 2k+3` below `k` count the primes below `2k+3` except `2`. -/
theorem count_shift_add_one (k : ℕ) :
    Nat.count (fun j => (2 * j + 3).Prime) k + 1 = Nat.count Nat.Prime (2 * k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h4 : ¬ (2 * k + 4).Prime := by
      intro hp
      have h2 : 2 ∣ 2 * k + 4 := ⟨k + 2, by ring⟩
      rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
    have e : 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 := by ring
    rw [Nat.count_succ, e, Nat.count_succ, Nat.count_succ, ← ih]
    simp only [h4, if_false]
    ring


/-- `2*k + 4` is never prime. -/
theorem not_prime_two_mul_add_four (k : ℕ) : ¬ (2 * k + 4).Prime := by
  intro hp
  have h2 : 2 ∣ 2 * k + 4 := ⟨k + 2, by ring⟩
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

/-- The odd primes below `2k+3` are exactly the `2j+3` with `j < k` prime. -/
theorem count_oddPrime (k : ℕ) :
    Nat.count (fun p => p.Prime ∧ Odd p) (2 * k + 3) =
      Nat.count (fun j => (2 * j + 3).Prime) k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hodd : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
    have hev : ¬ Odd (2 * k + 3 + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 2, by ring⟩
    have e : 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 := by ring
    rw [e, Nat.count_succ _ (2 * k + 3 + 1), Nat.count_succ _ (2 * k + 3),
      Nat.count_succ _ k, ih]
    simp only [hodd, hev, and_true, and_false, if_false, add_zero]

/-- There are `k + 1` positive even numbers below `2k+3`. -/
theorem count_posEven (k : ℕ) :
    Nat.count (fun e => 0 < e ∧ Even e) (2 * k + 3) = k + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hodd : ¬ Even (2 * k + 3) := by
      rw [Nat.not_even_iff_odd]; exact ⟨k + 1, by ring⟩
    have hev : Even (2 * k + 3 + 1) := ⟨k + 2, by ring⟩
    have e : 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 := by ring
    rw [e, Nat.count_succ _ (2 * k + 3 + 1), Nat.count_succ _ (2 * k + 3), ih]
    have hpos : 0 < 2 * k + 3 + 1 := by omega
    simp only [hodd, hev, hpos, and_true, and_false, if_false, if_true]

/-- Below `2k+3` the `k` odd numbers `3, 5, …, 2k+1` split into odd composites
and odd primes `2j+3` (`j < k`). -/
theorem count_oddComposite_add (k : ℕ) :
    Nat.count (fun m => Odd m ∧ 1 < m ∧ ¬ m.Prime) (2 * k + 3) +
      Nat.count (fun j => (2 * j + 3).Prime) k = k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hodd : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
    have hev : ¬ Odd (2 * k + 3 + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 2, by ring⟩
    have hgt : 1 < 2 * k + 3 := by omega
    have e : 2 * (k + 1) + 3 = 2 * k + 3 + 1 + 1 := by ring
    rw [e, Nat.count_succ _ (2 * k + 3 + 1), Nat.count_succ _ (2 * k + 3),
      Nat.count_succ _ k]
    simp only [hodd, hev, hgt, true_and, false_and, if_false, add_zero]
    by_cases hp : (2 * k + 3).Prime <;> simp only [hp, not_true, not_false_eq_true,
      if_true, if_false] <;> omega


/-! ## The `n`-th prime for `n ≥ 2` is `2k + 3` -/

/-- For `1 ≤ n`, the 0-indexed `n`-th prime (that is, `prime (n+1)`) has the
form `2k + 3`, and exactly `n` primes lie below it. -/
theorem exists_nth_prime_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, Nat.nth Nat.Prime n = 2 * k + 3 ∧ Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hgt : 2 < Nat.nth Nat.Prime n := by
    rw [← Nat.nth_prime_zero_eq_two]
    exact Nat.nth_strictMono hinf (by omega)
  have hodd : Odd (Nat.nth Nat.Prime n) :=
    (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ := hodd
  exact ⟨m - 1, by omega, Nat.count_nth_of_infinite hinf n⟩

/-! ## Values of the four sequences at `2k + 3 = prime (n+1)` -/

/-- `prime (n+1)` is the 0-indexed `Nat.nth Nat.Prime n`. -/
theorem prime_succ (n : ℕ) : prime (n + 1) = Nat.nth Nat.Prime n := by
  simp [prime]

/-- If `prime (n+1) = 2k+3` with `1 ≤ n`, then `A067076(n) = k`. -/
theorem a067076_eq (n k : ℕ) (hn : 1 ≤ n) (hk : Nat.nth Nat.Prime n = 2 * k + 3)
    (hc : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n) : a067076 n = k := by
  have hcount : Nat.count (fun j => (2 * j + 3).Prime) k = n - 1 := by
    have h := count_shift_add_one k
    rw [← hk, hc] at h
    omega
  have hP : (2 * k + 3).Prime := hk ▸ Nat.prime_nth_prime n
  rw [a067076, ← hcount]
  exact Nat.nth_count hP

/-- If `prime (n+1) = 2k+3` with `1 ≤ n`, then the `n`-th odd prime is `2k+3`. -/
theorem oddPrime_eq (n k : ℕ) (hn : 1 ≤ n) (hk : Nat.nth Nat.Prime n = 2 * k + 3)
    (hc : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n) : oddPrime n = 2 * k + 3 := by
  have hcount : Nat.count (fun p => p.Prime ∧ Odd p) (2 * k + 3) = n - 1 := by
    have h := count_shift_add_one k
    rw [← hk, hc] at h
    rw [count_oddPrime]
    omega
  have hP : (2 * k + 3).Prime ∧ Odd (2 * k + 3) :=
    ⟨hk ▸ Nat.prime_nth_prime n, ⟨k + 1, by ring⟩⟩
  rw [oddPrime, ← hcount]
  exact Nat.nth_count hP


/-! ## The conjecture -/

/-- **Closed form.** For `1 ≤ n`, `2 * A067076(n) + 3 = prime(n+1)`, i.e.
`A067076(n) = (prime(n+1) - 3)/2` with exact division. -/
theorem two_mul_a067076_add_three (n : ℕ) (hn : 1 ≤ n) :
    2 * a067076 n + 3 = prime (n + 1) := by
  obtain ⟨k, hk, hc⟩ := exists_nth_prime_eq n hn
  rw [a067076_eq n k hn hk hc, prime_succ, hk]

/-- **Mathar's conjecture (A067076, R. J. Mathar, Jul 07 2009), with the closed form.**

Verbatim: "Conjecture: a(n) = A008507(n) + n - 1 = A005097(n) - 1 = A102781(n+1) - 1."
The task statement adds `a(n) = (prime(n+1) - 3)/2`.

All sequences are 1-indexed as in the OEIS; the guard `1 ≤ n` is the OEIS
offset.  Subtractions are taken in `ℤ` after casting, and the division by `2`
is exact because `prime (n+1)` is odd (see `two_mul_a067076_add_three`). -/
theorem mathar_conjecture (n : ℕ) (hn : 1 ≤ n) :
    (a067076 n : ℤ) = ((prime (n + 1) : ℤ) - 3) / 2 ∧
    (a067076 n : ℤ) = (a008507 n : ℤ) + n - 1 ∧
    (a067076 n : ℤ) = (a005097 n : ℤ) - 1 ∧
    (a067076 n : ℤ) = (a102781 (n + 1) : ℤ) - 1 := by
  obtain ⟨k, hk, hc⟩ := exists_nth_prime_eq n hn
  have ha : a067076 n = k := a067076_eq n k hn hk hc
  have hq : oddPrime n = 2 * k + 3 := oddPrime_eq n k hn hk hc
  have hshift : Nat.count (fun j => (2 * j + 3).Prime) k = n - 1 := by
    have h := count_shift_add_one k
    rw [← hk, hc] at h
    omega
  have h8507 : a008507 n + (n - 1) = k := by
    rw [a008507, hq, ← Nat.count_eq_card_filter_range, ← hshift]
    exact count_oddComposite_add k
  have h5097 : a005097 n = k + 1 := by
    rw [a005097, hq]
    omega
  have h2781 : a102781 (n + 1) = k + 1 := by
    rw [a102781, prime_succ, hk, ← Nat.count_eq_card_filter_range]
    exact count_posEven k
  have hp : prime (n + 1) = 2 * k + 3 := by rw [prime_succ, hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha, hp]; push_cast; omega
  · rw [ha]; omega
  · rw [ha, h5097]; push_cast; ring
  · rw [ha, h2781]; push_cast; ring

-- Non-vacuity: the hypothesis `1 ≤ n` is met at the first OEIS index.
example : (a067076 1 : ℤ) = (a005097 1 : ℤ) - 1 := (mathar_conjecture 1 le_rfl).2.2.1

end Candidates.A067076PrimeMathar
