/-
# A048868 — if primes outnumber nonprimes in the reduced residue system of `n`, then `n` is even

## OEIS source (retrieved with `oeis show A048868`, 2026-10-21)

```
NAME:     Numbers whose reduced residue system contains more primes than
          nonprimes.
TERMS:    8,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,
          56,60,62,64,66,68,70,72,74,76,78,80,84,88,90,96,98,100,102,104,108,
          110,112,114,120,126,130,132,138,140,144,150,154,156,160,162,168,170
COMMENT (the conjecture, inside the block "From _Michael De Vlieger_,
  May 21 2017: (Start) ... (End)"):
  Conjecture: all terms are even.
PROGRAM (Mathematica, the definition this file mirrors):
  Select[Range@ 170, Function[n, Count[Range@ n, _?(PrimeQ@ # &&
    CoprimeQ[n, #] &)] > EulerPhi[n]/2]] (* _Michael De Vlieger_, May 21 2017 *)
```

## Status

Open according to the triage: the entry contains no proof, and the b-file and
David A. Corneth's search (PARI programs of Jun 09 2024) report no odd term
below `10^8`.  Recomputed here (Python, 2026-10-21): no odd term `n ≤ 20000`,
and the first 61 terms agree with the DATA line.

This file proves the conjecture.  The argument is elementary: for odd `n` the
reflection `k ↦ n - k` sends odd reduced residues to even ones, and even
residues other than `2` are nonprime.  An explicit injection from the primes of
the reduced residue system into its nonprimes is
`2 ↦ 1`, `n - 2 ↦ n - 1` (when `n - 2` is prime), `p ↦ n - p` otherwise.

## Definition layer

* `reducedResidues n = {k : 1 ≤ k ≤ n, gcd(k, n) = 1}`, the entry's `Range@ n`
  filtered by `CoprimeQ[n, #]`.  Its cardinality is `φ(n)` (checked below for
  `n < 60`), so `nonprimeCount n < primeCount n` is De Vlieger's
  `#primes > EulerPhi[n]/2`.
* `IsA048868 n := nonprimeCount n < primeCount n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A048868GcdPrimeNonprime

/-- The reduced residue system of `n` as in the entry: the `k` with `1 ≤ k ≤ n`
and `gcd(k, n) = 1`. -/
def reducedResidues (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)

/-- The number of primes in the reduced residue system of `n`. -/
def primeCount (n : ℕ) : ℕ :=
  ((reducedResidues n).filter Nat.Prime).card

/-- The number of nonprimes in the reduced residue system of `n`. -/
def nonprimeCount (n : ℕ) : ℕ :=
  ((reducedResidues n).filter (fun k => ¬ k.Prime)).card

/-- Membership in A048868: the reduced residue system of `n` contains more
primes than nonprimes. -/
def IsA048868 (n : ℕ) : Prop :=
  nonprimeCount n < primeCount n

/-- `IsA048868` is decidable, so the DATA line can be checked by evaluation. -/
instance : DecidablePred IsA048868 :=
  fun n => inferInstanceAs (Decidable (nonprimeCount n < primeCount n))

/-! ## Ground truth -/

-- The reduced residue system has `φ(n)` elements (here for `n < 60`).
example : ∀ n ∈ Finset.range 60, (reducedResidues n).card = Nat.totient n := by
  decide +kernel

-- `n = 8`: residues `1, 3, 5, 7`, three primes and one nonprime.
example : primeCount 8 = 3 ∧ nonprimeCount 8 = 1 := by decide

-- The 61 listed terms of the DATA line are exactly the members below `171`.
example : (List.range 171).filter (fun n => decide (IsA048868 n)) =
    [8, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46,
      48, 50, 52, 54, 56, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 84, 88, 90,
      96, 98, 100, 102, 104, 108, 110, 112, 114, 120, 126, 130, 132, 138, 140,
      144, 150, 154, 156, 160, 162, 168, 170] := by
  decide +kernel

-- Non-vacuity of the hypothesis of the main theorem: `8` is a term.
example : IsA048868 8 := by decide

/-! ## Helper lemmas -/

/-- A prime `k` in the reduced residue system of `n` satisfies `2 ≤ k < n`,
is coprime to `n`, and is `2` or odd. -/
theorem facts_of_mem_prime (n k : ℕ) (hk : k ∈ (reducedResidues n).filter Nat.Prime) :
    2 ≤ k ∧ k < n ∧ k.Coprime n ∧ (k = 2 ∨ k % 2 = 1) := by
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨⟨-, hkn⟩, hcop⟩, hp⟩ := hk
  have hne : k ≠ n := by
    rintro rfl
    exact hp.one_lt.ne' ((Nat.coprime_self k).mp hcop)
  exact ⟨hp.two_le, lt_of_le_of_ne hkn hne, hcop, hp.eq_two_or_odd⟩

/-- An even natural number other than `2` is not prime. -/
theorem not_prime_of_mod_two_eq_zero (m : ℕ) (h2 : m % 2 = 0) (hne : m ≠ 2) :
    ¬ m.Prime := by
  intro hp
  rcases hp.eq_two_or_odd with h | h <;> omega

/-- **Key inequality.** For odd `n`, the reduced residue system of `n` contains
at most as many primes as nonprimes.  Proof: the map
`2 ↦ 1`, `n - 2 ↦ n - 1`, `p ↦ n - p` (otherwise) injects the primes of the
reduced residue system into its nonprimes. -/
theorem primeCount_le_nonprimeCount_of_odd (n : ℕ) (hn : Odd n) :
    primeCount n ≤ nonprimeCount n := by
  unfold primeCount nonprimeCount
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  let f : ℕ → ℕ := fun k => if k = 2 then 1 else if k + 2 = n then n - 1 else n - k
  apply Finset.card_le_card_of_injOn f
  · -- `f` maps primes of the reduced residue system to nonprimes in it.
    intro k hk
    obtain ⟨h2k, hkn, hcop, hpar⟩ := facts_of_mem_prime n k hk
    simp only [Finset.mem_coe, reducedResidues, Finset.mem_filter, Finset.mem_Icc]
    by_cases hk2 : k = 2
    · simp only [f, if_pos hk2]
      exact ⟨⟨⟨le_refl 1, by omega⟩, Nat.coprime_one_left n⟩, Nat.not_prime_one⟩
    · by_cases hkn2 : k + 2 = n
      · simp only [f, if_neg hk2, if_pos hkn2]
        refine ⟨⟨⟨by omega, by omega⟩, ?_⟩,
          not_prime_of_mod_two_eq_zero _ (by omega) (by omega)⟩
        exact (Nat.coprime_self_sub_left (by omega)).mpr (Nat.coprime_one_left n)
      · simp only [f, if_neg hk2, if_neg hkn2]
        refine ⟨⟨⟨by omega, by omega⟩, ?_⟩,
          not_prime_of_mod_two_eq_zero _ (by omega) (by omega)⟩
        exact (Nat.coprime_self_sub_left hkn.le).mpr hcop
  · -- `f` is injective on the primes of the reduced residue system.
    intro a ha b hb hab
    obtain ⟨ha2, han, -, hapar⟩ := facts_of_mem_prime n a ha
    obtain ⟨hb2, hbn, -, hbpar⟩ := facts_of_mem_prime n b hb
    simp only [f] at hab
    split_ifs at hab <;> omega

/-! ## The conjecture -/

/-- **De Vlieger's conjecture (A048868, Michael De Vlieger, May 21 2017).**

Verbatim: "Conjecture: all terms are even."  That is, if the reduced residue
system `{k : 1 ≤ k ≤ n, gcd(k, n) = 1}` of `n` contains more primes than
nonprimes, then `n` is even.  Proved via
`primeCount_le_nonprimeCount_of_odd`. -/
theorem even_of_nonprimeCount_lt_primeCount (n : ℕ)
    (h : nonprimeCount n < primeCount n) : Even n := by
  by_contra hne
  have hodd : Odd n := Nat.not_even_iff_odd.mp hne
  exact absurd (primeCount_le_nonprimeCount_of_odd n hodd) (not_le.mpr h)

/-- The conjecture in the sequence's own vocabulary: every term of A048868 is
even. -/
theorem even_of_isA048868 (n : ℕ) (h : IsA048868 n) : Even n :=
  even_of_nonprimeCount_lt_primeCount n h

end Candidates.A048868GcdPrimeNonprime
