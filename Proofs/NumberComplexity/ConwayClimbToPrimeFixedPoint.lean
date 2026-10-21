/-
# Conway's "climb to a prime" is false: the composite fixed point 13532385396179

## Source (recorded 2026-10-21)

* MathOverflow answer https://mathoverflow.net/a/66101 (thread "Open problems
  with monetary rewards", answer listing J. H. Conway's $1000 problems).  The
  thread page itself could not be fetched from this environment on 2026-10-21;
  the claim below is taken from the triage spec and cross-checked against
  OEIS A080670 and the public reports listed here.
* OEIS A080670, "Literal reading of the prime factorization of n" (comment by
  M. F. Hasler, Jun 2017, recording the nontrivial fixed point).
* The Aperiodical, "13532385396179 doesn't climb to a prime" (June 2017),
  https://aperiodical.com/2017/06/13532385396179-doesnt-climb-to-a-prime/
* Prime Curios, https://t5k.org/curios/page.php/13532385396179.html
* No arXiv paper is involved.

## Claim (stated by J. H. Conway, as one of his $1000 problems)

  "Climb to a prime: start from n >= 2, write its prime factorization with
  primes in increasing order and exponents equal to 1 omitted, read the
  concatenated digits as a new number, and repeat.  Conway asked whether this
  always reaches a prime."

## Status

Refuted (proved in the literature): James Davis (June 2017) found
`n = 13532385396179 = 13 * 53^2 * 3853 * 96179`.  Its factorization reads
`13 53 2 3853 96179`, which is `n` again, so `n` is a composite fixed point and
its orbit never reaches a prime.  This module kernel-checks that refutation.

## Conventions

`climb` follows A080670 for every `n ≥ 2` (checked below against the OEIS terms
for `2 ≤ n ≤ 60`).  For `n = 0, 1` the factorization is empty and `climb`
returns `0`, whereas A080670 sets `a(1) = 1`; Conway's process only starts at
`n ≥ 2`, and this boundary value plays no role in the statements.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ConwayClimbToPrimeFixedPoint

/-! ## Definitions -/

/-- Decimal concatenation: `concatDec a b` writes the decimal digits of `b` after
those of `a`, i.e. `a * 10 ^ (number of decimal digits of b) + b`. -/
def concatDec (a b : ℕ) : ℕ := a * 10 ^ (Nat.digits 10 b).length + b

/-- The blocks read off the prime factorization of `n`: the prime factors in
increasing order, each followed by its exponent when that exponent is not `1`.
For `n = 12 = 2^2 * 3` this is `[2, 2, 3]`. -/
def climbBlocks (n : ℕ) : List ℕ :=
  ((n.primeFactors.sort (· ≤ ·)).map fun p =>
    if n.factorization p = 1 then [p] else [p, n.factorization p]).flatten

/-- Conway's climb map (OEIS A080670 for `n ≥ 2`): the number whose decimal
expansion is the concatenation of the blocks of `climbBlocks n`. -/
def climb (n : ℕ) : ℕ := (climbBlocks n).foldl concatDec 0

/-- The fixed point found by James Davis (2017). -/
def davisNumber : ℕ := 13532385396179

/-! ## A computable normal form for the definitions -/

/-- The increasingly sorted prime factors of `n` are the deduplicated list of
prime factors with multiplicity. -/
theorem primeFactorsList_dedup_eq_sort (n : ℕ) :
    n.primeFactorsList.dedup = n.primeFactors.sort (· ≤ ·) := by
  apply List.Perm.eq_of_sortedLE
  · exact ((Nat.primeFactorsList_sorted n).pairwise.sublist (List.dedup_sublist _)).sortedLE
  · exact (Finset.pairwise_sort _ _).sortedLE
  · rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) (Finset.sort_nodup _ _)]
    intro p
    rw [List.mem_dedup, Finset.mem_sort, Nat.mem_primeFactors_iff_mem_primeFactorsList]

/-- `climbBlocks` computed from `Nat.primeFactorsList`: exponents are counts. -/
theorem climbBlocks_eq (n : ℕ) : climbBlocks n =
    (n.primeFactorsList.dedup.map fun p =>
      if n.primeFactorsList.count p = 1 then [p]
      else [p, n.primeFactorsList.count p]).flatten := by
  simp only [climbBlocks, primeFactorsList_dedup_eq_sort, Nat.primeFactorsList_count_eq]

/-- `climb` computed from `Nat.primeFactorsList`, used for kernel evaluation. -/
theorem climb_eq_fun : climb = fun n =>
    ((n.primeFactorsList.dedup.map fun p =>
      if n.primeFactorsList.count p = 1 then [p]
      else [p, n.primeFactorsList.count p]).flatten).foldl concatDec 0 := by
  funext n
  rw [climb, climbBlocks_eq]

/-! ## Ground truth -/

example : concatDec 13 53 = 1353 := by decide +kernel
example : climbBlocks 12 = [2, 2, 3] := by rw [climbBlocks_eq]; decide +kernel
example : climb 8 = 23 := by rw [climb_eq_fun]; decide +kernel
example : climb 12 = 223 := by rw [climb_eq_fun]; decide +kernel
example : climb 90 = 2325 := by rw [climb_eq_fun]; decide +kernel
example : climb 7 = 7 := by rw [climb_eq_fun]; decide +kernel

/-- `climb n` agrees with OEIS A080670 for `2 ≤ n ≤ 60`. -/
example : (List.range' 2 59).map climb =
    [2, 3, 22, 5, 23, 7, 23, 32, 25, 11, 223, 13, 27, 35, 24, 17, 232, 19, 225, 37,
      211, 23, 233, 52, 213, 33, 227, 29, 235, 31, 25, 311, 217, 57, 2232, 37, 219,
      313, 235, 41, 237, 43, 2211, 325, 223, 47, 243, 72, 252, 317, 2213, 53, 233,
      511, 237, 319, 229, 59, 2235] := by
  rw [climb_eq_fun]
  decide +kernel

/-! ## The fixed point -/

/-- The prime factorization of Davis's number, with multiplicity and in
increasing order: `13532385396179 = 13 * 53^2 * 3853 * 96179`. -/
theorem primeFactorsList_davisNumber :
    davisNumber.primeFactorsList = [13, 53, 53, 3853, 96179] := by
  have h13 : Nat.Prime 13 := by norm_num
  have h53 : Nat.Prime 53 := by norm_num
  have h3853 : Nat.Prime 3853 := by norm_num
  have h96179 : Nat.Prime 96179 := by norm_num
  apply List.Perm.eq_of_sortedLE (Nat.primeFactorsList_sorted _)
  · decide
  · apply List.Perm.symm
    apply Nat.primeFactorsList_unique
    · norm_num [davisNumber]
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact h13
      · exact h53
      · exact h53
      · exact h3853
      · exact h96179

/-- The factorization of `13532385396179` reads `13 53 2 3853 96179`. -/
theorem climbBlocks_davisNumber : climbBlocks davisNumber = [13, 53, 2, 3853, 96179] := by
  rw [climbBlocks_eq, primeFactorsList_davisNumber]
  decide +kernel

/-- Davis's number is a fixed point of Conway's climb map:
`climb 13532385396179 = 13532385396179`. -/
theorem climb_davisNumber : climb davisNumber = davisNumber := by
  rw [climb, climbBlocks_davisNumber]
  decide +kernel

/-- Davis's number is composite: it is divisible by `13`. -/
theorem not_prime_davisNumber : ¬ davisNumber.Prime :=
  Nat.not_prime_of_dvd_of_lt (m := 13) (by norm_num [davisNumber]) (by norm_num)
    (by norm_num [davisNumber])

/-- Every iterate of the climb map fixes Davis's number. -/
theorem iterate_climb_davisNumber (k : ℕ) : climb^[k] davisNumber = davisNumber :=
  Function.iterate_fixed climb_davisNumber k

/-- **Conway's "climb to a prime" is false** (James Davis, 2017).  It is not the
case that for every `n ≥ 2` some iterate `climb^[k] n` of Conway's climb map is
prime: the orbit of the composite fixed point `13532385396179` is constant. -/
theorem conway_climb_false : ¬ ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, (climb^[k] n).Prime := by
  intro h
  obtain ⟨k, hk⟩ := h davisNumber (by norm_num [davisNumber])
  rw [iterate_climb_davisNumber k] at hk
  exact not_prime_davisNumber hk

end Candidates.ConwayClimbToPrimeFixedPoint
