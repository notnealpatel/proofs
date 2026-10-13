/-
# A003135 — factorials that are nontrivial products of smaller factorials

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A003135` plus `curl "https://oeis.org/search?q=id:A003135&fmt=text"`:

```
%N A003135 n! is a nontrivial product of factorials. It is conjectured that the
           list is complete.
%O A003135 1,1
%A A003135 _N. J. A. Sloane_
%K A003135 nonn,bref,more,hard
COMMENTS:
  A "nontrivial" solution is one in which the largest x! in the product of a(n)!
  is such that x < a(n)-1. There are no other terms < 10^5.
  - _Jud McCranie_, Jun 15 2005
XREFS:
  Cf. A034878, A001013, A058295, A075082, A109095, A109096, A109097, A109098.
TERMS: 9,10,16
```

## The nontriviality condition is the whole subtlety

Without it the sequence is everything: `n! = (n−1)! · n`, and whenever `n` is
itself a factorial (`n = m!`) that is a product of factorials — e.g.
`6! = 5! · 3!` (since `3! = 6`), `24! = 23! · 4!`, `120! = 119! · 5!`.  Those
are the *trivial* solutions, and McCranie's condition
"the largest `x!` in the product has `x < n − 1`" excludes exactly them.

The three known terms, with witnesses (all verified arithmetically):

| `n`  | factorization                | largest `x` | `n − 1` | ok? |
|------|------------------------------|-------------|---------|-----|
| `9`  | `9! = 7! · 3! · 3! · 2!`     | `7`         | `8`     | ✓   |
| `10` | `10! = 7! · 6!`              | `7`         | `9`     | ✓   |
| `16` | `16! = 14! · 5! · 2!`        | `14`        | `15`    | ✓   |

Arithmetic checks: `9! = 362880 = 5040 · 6 · 6 · 2`;
`10! = 3628800 = 5040 · 720`;
`16! = 20922789888000 = 87178291200 · 120 · 2`.

## Status

Open.  Classical (Guy, *UPINT* B23 territory); the entry's own attribution is
thin — the `%A` is Sloane and the only dated comment is McCranie's 2005
computation to `10^5`.
-/
import Enumerative.FactorialProductWindow

set_option autoImplicit false

namespace Candidates.A003135

open Nat

/-! ## Definition layer

`leandoc` findings:

* `Nat.factorial : ℕ → ℕ` with notation `n !` under `open Nat`.
* `Multiset` and `Multiset.prod`, `Multiset.map` — the right home for "a product
  of factorials", since the factors repeat (`9! = 7!·3!·3!·2!` has `3!` twice)
  and are unordered.  A `Finset` would be wrong (it forbids repeats) and a
  `List` would impose an irrelevant order.  This is the definitional choice the
  candidates document called "awkward to state cleanly"; `Multiset` makes it
  clean.
* `Nat.factorial_le`, `Nat.factorial_lt`, `Nat.factorial_dvd_factorial`,
  `Nat.factorial_pos`, `Nat.factorial_inj` — the API for the bounded search.

**Why factors are required `≥ 2`.**  `0! = 1! = 1`, so allowing `x ∈ {0, 1}`
lets any multiset be padded with `1`s without changing the product, which would
make the "largest `x`" condition satisfiable trivially by a multiset of `1`s
(product `1 ≠ n!`, so not actually a problem for the product, but it does make
the multiset non-unique and the search unbounded).  Requiring `2 ≤ x` is the
standard convention and matches A001013 ("Jordan–Polya numbers: products of
factorials"). -/

/-- `n !` is a **nontrivial product of factorials**: there is a multiset `L` of
integers `≥ 2`, each **strictly below `n − 1`** (McCranie's condition, written
`x + 1 < n` to avoid `ℕ` subtraction), whose factorials multiply to `n !`.

The multiset must be nonempty; `L = 0` would give the empty product `1 ≠ n !`
for `n ≥ 2`, so that is automatic, but it is asserted for clarity. -/
abbrev IsNontrivialFactorialProduct := FactorialProducts.IsNontrivialFactorialProduct

/-- The three known terms. -/
abbrev knownTerms := FactorialProducts.knownTerms

/-! ## The conjecture -/

/-- **A003135 completeness (the NAME line).**

Verbatim: "n! is a nontrivial product of factorials. It is conjectured that the
list is complete." with DATA `9, 10, 16`, plus McCranie's
"A 'nontrivial' solution is one in which the largest x! in the product of a(n)!
is such that x < a(n)-1. There are no other terms < 10^5."

**Mathlib primitives available.**  `Nat.factorial` and its full API;
`Nat.factorization` and `Nat.Prime.factorization_factorial` (Legendre's formula
`v_p(n!) = Σ_{i≥1} ⌊n/p^i⌋`) — **this is the key tool**;
`Nat.Prime.factorial_dvd`, `Nat.primeFactors`; `Multiset.prod`, `Multiset.map`,
`Multiset.sum`.

**Sketch of an attack.**  The standard argument is prime-valuation counting with
Bertrand:
1. Let `p` be a prime with `n/2 < p ≤ n` (Bertrand, `Nat.exists_prime_lt_and_le_two_mul`,
   in Mathlib).  Then `v_p(n!) = 1`.
2. So exactly one factor `x!` in the product has `p ≤ x`, and that `x` satisfies
   `x < n − 1`; hence `p ≤ x ≤ n − 2`.
3. Iterating over the primes in `(n/2, n]` and comparing valuations pins the
   largest factor `x` to be very close to `n`, and then the *ratio* `n!/x!` is a
   product of `⌊n/x⌋`-ish consecutive integers that must itself be a product of
   factorials — a Jordan–Pólya condition (A001013).
4. The conjecture is that this cascade has no solutions past `16`.  Making step
   3 effective is where it stalls; the known partial results bound the number of
   factors, not `n`.

**Formalizable subset.**  The *bounded* claim is real content and is provable:
for a fixed `n`, the largest factor `x` satisfies `x ≥ n − O(log n)` by
valuation counting, so the search is finite and small.  Turning that into
`decide` for `n ≤ 100` is a genuine certificate.

**Tactic families.**  `decide`/`native_decide` for bounded searches (note `n!`
overflows fast — `20!` already exceeds `2^61`, so this is bignum territory);
`Nat.factorization` simp set and `Nat.Prime.factorization_factorial` for the
valuation argument; `interval_cases` for the factor enumeration;
`Multiset.induction_on` for the product manipulations; `omega` for the
inequalities.

**Related work in this repo.** `A146968Brocard.lean` in this directory (also a
`Nat.factorial` Diophantine archive card), `A000166SunPerfectPower.lean`
(factorial-scale values avoiding a multiplicative shape). -/
theorem a003135_complete (n : ℕ) (h : IsNontrivialFactorialProduct n) :
    n ∈ knownTerms := by
  sorry

/-- Finiteness — strictly weaker, and the natural target for a valuation
argument that bounds `n` without identifying the exceptions. -/
theorem a003135_finite : {n : ℕ | IsNontrivialFactorialProduct n}.Finite := by
  sorry

/-- The **provable** search bound: in any nontrivial factorization, the largest
factor `x` satisfies `n ≤ 2 * x + 2`.

Reason: apply Bertrand to `n / 2`, obtaining `n / 2 < p ≤ 2 * (n / 2) ≤ n`.
Then `p ∣ n!`, so `p` divides some `x!` in the product, and `p ≤ x`.
Natural division and these inequalities give `n ≤ 2 * x + 1`, hence the stated
bound. This necessary condition alone is not a decidable search certificate. -/
theorem largest_factor_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (L : Multiset ℕ) (hL : L ≠ 0) (h2 : ∀ x ∈ L, 2 ≤ x)
    (hprod : (L.map Nat.factorial).prod = n !) :
    ∃ x ∈ L, n ≤ 2 * x + 2 := by
  exact FactorialProducts.largest_factor_lower_bound hn L hL h2 hprod

/-! ## Sanity layer -/

-- PROVABLE: the three witnesses, arithmetically.
example : (9 : ℕ)! = 7! * 3! * 3! * 2! := by decide
example : (10 : ℕ)! = 7! * 6! := by decide
example : (16 : ℕ)! = 14! * 5! * 2! := by norm_num [Nat.factorial]

-- PROVABLE: satisfiability — each known term really is a nontrivial factorial
-- product, so `a003135_complete`'s hypothesis is instantiable and the theorem
-- is not vacuous.
example : IsNontrivialFactorialProduct 9 :=
  FactorialProducts.isNontrivialFactorialProduct_nine

example : IsNontrivialFactorialProduct 10 :=
  FactorialProducts.isNontrivialFactorialProduct_ten

example : IsNontrivialFactorialProduct 16 :=
  FactorialProducts.isNontrivialFactorialProduct_sixteen

-- PROVABLE: the nontriviality condition is load-bearing.  `6! = 5! · 3!` is a
-- factorial product, but `5 = 6 − 1` violates `x + 1 < n`, so `6` is correctly
-- excluded.  Without McCranie's condition the sequence would contain `6`, `24`,
-- `120`, … and the "list is complete" claim would be nonsense.
example : (6 : ℕ)! = 5! * 3! := by decide
example : ¬ (5 + 1 < 6) := by decide

-- PROVABLE: likewise `24! = 23! · 4!` is trivial (`4! = 24`), and `23 = 24 − 1`.
example : (4 : ℕ)! = 24 := by decide

-- PROVABLE: `6` is genuinely not a term under the correct definition.
example : ¬ IsNontrivialFactorialProduct 6 :=
  FactorialProducts.not_isNontrivialFactorialProduct_six

-- PROVABLE: the factor multiset really may repeat — `9!` needs `3!` twice — so
-- `Multiset` (not `Finset`) is the right type.  This example pins that.
example : ({7, 3, 3, 2} : Multiset ℕ).card = 4 := by decide

-- PROVABLE (window check): no `n ∈ Finset.Icc 2 60` outside `{9, 10, 16}` is a
-- nontrivial factorial product. The complete search equivalence and its
-- kernel-checked certificate are proved in `FactorialProductWindow`.
example : ∀ n ∈ Finset.Icc 2 60, IsNontrivialFactorialProduct n → n ∈ knownTerms := by
  exact FactorialProducts.isNontrivialFactorialProduct_mem_knownTerms_window

/-! ## Notes for a follow-up card

The bounded sanity sweep is now proved through the exact positive-target
multiset equivalence in `FactorialProductWindow`. Its search preserves repeated
factors, permits the empty product only for target one, and rejects zero.
The guarded bridge at `(n - 2, n!)` recovers the original predicate for `2 ≤ n`.
Prime-divisor rejection shortens the certificates without changing search
semantics. The global finiteness and completeness conjectures remain open;
the inclusive window through sixty supplies neither global implication.

Reference: Guy, *Unsolved Problems in Number Theory*, §B23. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A003135 plus exact-integer verification, 2026-08-05.

Confirmed:
* NAME, TERMS `9, 10, 16`, McCranie's comment, `%O 1,1`,
  `%A _N. J. A. Sloane_`, keywords `nonn,bref,more,hard`, XREFS — all verbatim.
* All four products exact: `9! = 362880 = 5040·6·6·2`,
  `10! = 3628800 = 5040·720`,
  `16! = 20922789888000 = 87178291200·120·2`, `6! = 720 = 120·6`.
* **The nontriviality rendering is right**: `x < n − 1 ⟺ x + 1 < n` for
  naturals, and `9, 10, 16` satisfy it (`max x = 7, 7, 14` vs `n − 1 = 8, 9, 15`)
  while `6` does not (`max x = 5 = n − 1`).
* **The Bertrand lower-bound mechanism is sound**: `p ∣ x!` for prime `p` gives
  `p ≤ x`. Applying Bertrand to the natural floor `n / 2` yields
  `n ≤ 2 * x + 1`, not an unconditional strict `n < 2 * x`.

The archived signature `n ≤ 2 * x + 2` is retained exactly. The lower bound
alone does not bound factor multiplicities or certify a finite search.
-/

end Candidates.A003135
