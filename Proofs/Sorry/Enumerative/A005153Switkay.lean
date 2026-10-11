/-
# A005153 — Switkay: every odd number ≥ 3 is prime + practical

## OEIS source (re-pulled verbatim with `goof oeis show A005153`, 2026-08-05)

```
NAME:     Practical numbers: positive integers m such that every k <= sigma(m)
          is a sum of distinct divisors of m. Also called panarithmic numbers.
TERMS:    1,2,4,6,8,12,16,18,20,24,28,30,32,36,40,42,48,54,56,60,64,66,72,78,80,
          84,88,90,96,100,104,108,112,120,126,128,132,140,144,150,156,160,162,
          168,176,180,192,196,198,200,204,208,210,216,220,224,228,234,240,252
KEYWORDS: nonn,nice,easy
COMMENT (first comment — the equivalent definition the repo uses):
  Equivalently, positive integers m such that every number k <= m is a sum of
  distinct divisors of m.
COMMENT (the conjecture):
  Conjecture: every odd number, beginning with 3, is the sum of a prime number
  and a practical number. Note that this conjecture occupies the space between
  the unproven Goldbach conjecture and the theorem that every even number,
  beginning with 2, is the sum of two practical numbers (Melfi's 1996 proof of
  Margenstern's conjecture). - _Hal M. Switkay_, Jan 28 2023
```

## Status

Open (Jan 2023).  Switkay's own framing places it strictly between two known
landmarks: Melfi's theorem (proved) below it, Goldbach (open) above it.

## Repo adjacency

`Nat.Practical` and Stewart's criterion already live in
`Proofs/Enumerative/Practical.lean` and `Proofs/Enumerative/StewartCriterion.lean`,
with a `DecidablePred` instance.  Statement cost is essentially zero.
-/
import Mathlib
import Enumerative.Practical
import Enumerative.StewartCriterion

set_option autoImplicit false

namespace Candidates.A005153Switkay

/-! ## Definition layer

Existing repo definition reused verbatim (nothing re-defined):

* `Nat.Practical (n : ℕ) : Prop := 0 < n ∧ ∀ m ≤ n, ∃ S ∈ n.divisors.powerset, ∑ d ∈ S, d = m`
  — `Proofs/Enumerative/Practical.lean`, with `instance decidablePredPractical`.

  **Definitional-fidelity note.**  The repo definition is the OEIS *first
  comment* form ("every number `k ≤ m` is a sum of distinct divisors of `m`"),
  not the OEIS NAME form ("every `k ≤ sigma(m)`").  The two are equivalent, and
  the repo already carries the bridge as
  `practical_iff_forall_le_sum_divisors {n : ℕ} : ...`.  This card is stated over
  the repo's `Nat.Practical` and cites the bridge lemma so a reviewer can check
  the equivalence rather than take it on faith.

Mathlib definitions found by `leandoc` (`mode:"exact"`):

* `Nat.Prime (p : ℕ) : Prop` (`mathlib/Mathlib/Data/Nat/Prime/Defs.lean`).
* `Odd (n : α) : Prop` — Mathlib normal form.
* `leandoc "Nat.Practical"` returns `mode:"miss"`: practical numbers are *not*
  in Mathlib.  The repo definition is the only one available and is used. -/

/-! ## The conjecture -/

/-- **Switkay's conjecture (A005153, Hal M. Switkay, Jan 28 2023).**

Verbatim: "Conjecture: every odd number, beginning with 3, is the sum of a prime
number and a practical number."

The `3 ≤ n` guard is from the source ("beginning with 3") and is load-bearing:
`n = 1` is odd and is *not* prime + practical (the smallest prime is `2`, the
smallest practical is `1`, so the smallest such sum is `3`).  Without the guard
the statement is false, not merely vacuous.

**Mathlib primitives available.** `Nat.Prime`, `Nat.exists_prime_and_dvd`,
`Nat.exists_infinite_primes`, `Nat.Prime.two_le`; Bertrand's postulate
`Nat.bertrand` / `Nat.exists_prime_lt_and_le_two_mul`; the prime counting
function `Nat.primeCounting` and `Nat.primesBelow`.  Nothing about practical
numbers — that side is all repo API.

**Sketch of an attack.**  The honest answer is that this is Goldbach-adjacent
and out of reach, but the shape of a real attack is:
1. Practical numbers have density `≍ x / log x` (Saias 1997; Weingartner
   2015/2020 pins the constant `c = 1.33607…`, per the entry's own comment).
   So both summands come from sets of the same density order as the primes.
2. A Chen/Vinogradov-style circle-method argument on `primes + practicals` would
   need a bilinear/major-arc estimate for the practical-number indicator.
   Weingartner's asymptotics give the major arcs; the minor arcs are the gap.
3. **The cheap partial result within reach**: `2` is prime and `n - 2` is
   practical for many odd `n`, so a sufficient condition is "every odd `n ≥ 3`
   has `n - 2` practical **or** `n - p` practical for some small prime `p`".
   Since every practical number `> 1` is even (`Practical.two_dvd`, already in
   the repo) and `n` is odd, `n - p` is even for odd prime `p` — so the *real*
   statement is: for odd `n ≥ 5`, `n - p` must be an even practical number for
   some odd prime `p < n`, and for `n = 3` the decomposition is `2 + 1`.
   This parity observation is provable today and materially narrows the search;
   see `switkay_parity_reduction`.

**Tactic families.** `decide` for tiny cases via `decidablePredPractical`;
`native_decide` for the sweep (note the enlarged trust surface);
`Nat.Prime` norm_num extension (`norm_num [Nat.prime_def_lt]`) for primality
side conditions; `interval_cases` for bounded searches;
`omega` for the parity bookkeeping.

**Related work in this repo.** `Enumerative.Practical` (definition, decidability,
`practical_two_pow`, `Practical.mul_prime_pow`), `Enumerative.StewartCriterion`
(`practical_iff_stewart` — the workhorse for certifying practicality of a
specific number without a subset-sum search),
`Enumerative.ZumkellerSigmaHalf` (`Practical.isZumkeller`).
Adjacent cards in this directory: `A373686SomuTran.lean`,
`A209312SymmetricPractical.lean`, `A222603PracticalTree.lean`,
`A005153SunRootDecreasing.lean`. -/
theorem switkay_odd_eq_prime_add_practical (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = n := by
  sorry

/-- The parity refinement of Switkay: for odd `n ≥ 5` the prime summand must be
odd and the practical summand even.  This is provable today (every practical
number `> 1` is even by `Practical.two_dvd`, and `q = 1` would force `p = n - 1`
even, hence `p = 2`, hence `n = 3`), and it is the form a search should use. -/
theorem switkay_parity_reduction (n : ℕ) (hodd : Odd n) (hn : 5 ≤ n)
    (h : ∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = n) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Practical ∧ Even q ∧ p + q = n := by
  sorry

/-- **Melfi's theorem (1996), the proved statement Switkay's comment sits above.**

Verbatim from the same comment: "the theorem that every even number, beginning
with 2, is the sum of two practical numbers (Melfi's 1996 proof of Margenstern's
conjecture)".

Recorded here because (a) it is a *theorem*, not a conjecture, so it is a
legitimate full-proof target rather than an archive card, and (b) it is the
natural lower bound against which Switkay's statement should be calibrated.
Melfi, *On two conjectures about practical numbers*, J. Number Theory 56 (1996)
205–210. -/
theorem melfi_even_eq_practical_add_practical (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: satisfiability at the boundary — `3 = 2 + 1` with `2` prime and
-- `1` practical (`Nat.practical_one` is already proved in the repo).
example : ∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = 3 :=
  ⟨2, 1, Nat.prime_two, Nat.practical_one, by norm_num⟩

-- PROVABLE: the guard `3 ≤ n` is load-bearing — `n = 1` is a counterexample.
-- Smallest prime is `2`, smallest practical is `1`, so `p + q ≥ 3 > 1`.
example : ¬ ∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = 1 := by
  rintro ⟨p, q, hp, hq, hpq⟩
  have h2 : 2 ≤ p := hp.two_le
  omega

-- PROVABLE: the next few decompositions, to show the conclusion is not
-- accidentally provable by a single fixed prime.
--   5 = 3 + 2,  7 = 3 + 4,  9 = 7 + 2,  11 = 7 + 4,  13 = 7 + 6
example : ∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = 5 :=
  ⟨3, 2, Nat.prime_three, Nat.practical_two, by norm_num⟩

-- PROVABLE (window check): the conjecture holds for every odd `n ≤ 5000`, with
-- the prime summand bounded by `n`.  The bound is not a hypothesis smuggled in:
-- `p + q = n` with `q ≥ 1` already forces `p < n`.
example : ∀ n ∈ Finset.range 5001, Odd n → 3 ≤ n →
    ∃ p ∈ Finset.range (n + 1), ∃ q ∈ Finset.range (n + 1),
      p.Prime ∧ q.Practical ∧ p + q = n := by
  native_decide

-- PROVABLE: the practical numbers used above really are practical, checked
-- against the OEIS DATA line `1, 2, 4, 6, 8, 12, …`.
example : (Nat.Practical 1) ∧ (Nat.Practical 2) ∧ (Nat.Practical 4) ∧
    (Nat.Practical 6) ∧ ¬ (Nat.Practical 3) ∧ ¬ (Nat.Practical 5) := by decide

/-!
## Adversarial review verdict — **PASS** (zero defects)

Independent re-pull of A005153 by a source-fidelity reviewer, 2026-08-05.

Confirmed:
* Switkay's quote is verbatim; attribution `Hal M. Switkay, Jan 28 2023` correct.
* The `3 ≤ n` guard is load-bearing and the `n = 1` refutation proof is sound.
* The repo's `Nat.Practical` really is the "every `k ≤ m`" form, not the
  "every `k ≤ σ(m)`" form, and `practical_iff_forall_le_sum_divisors` exists at
  `Practical.lean:248` as the bridge.
* `Nat.practical_one` (`:98`), `Nat.practical_two` (`:103`),
  `Nat.Practical.two_dvd` (`:271`) all exist with those exact names.
* Mathlib has no practical-number definition (`leandoc` miss).
* `Nat.prime_two`, `Nat.prime_three`, `Nat.bertrand`,
  `Nat.exists_prime_lt_and_le_two_mul` all exist.
* `switkay_parity_reduction` is TRUE: `q = 1` forces `p = n − 1` even, hence
  `p = 2` and `n = 3`, contradicting `5 ≤ n`.
* `1, 2, 4, 6` practical and `3, 5` not, matching the DATA line.
-/

end Candidates.A005153Switkay
