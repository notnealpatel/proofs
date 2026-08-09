import Mathlib
import Enumerative.Practical

/-!
# A276086, A003961, and Karttunen's multiperfect-congruence conjectures (A323653)

This file builds the two "arbitrary companion function" layers that OEIS A351458 and
A349745 are stated over — the **primorial base exp-function** A276086 and the **prime
shift** A003961 — and archives Antti Karttunen's conjecture that intersecting the
A276086 congruence family with the multiply-perfect numbers reproduces A323653.

## Primary sources (pulled live 2026-08-05 via `goof oeis show`)

**A276086** — name, verbatim:

> Primorial base exp-function: digits in primorial base representation of n become the
> exponents of successive prime factors whose product a(n) is.

terms (offset 0), verbatim:

> 1, 2, 3, 6, 9, 18, 5, 10, 15, 30, 45, 90, 25, 50, 75, 150, 225, 450, 125, 250, 375,
> 750, 1125, 2250, 625, 1250, 1875, 3750, 5625, 11250, 7, 14, 21, 42, 63, 126, 35, 70,
> 105, 210, 315, 630, 175, 350, 525, 1050, 1575, 3150, 875, 1750, 2625, 5250, 7875,
> 15750, 4375, 8750, 13125, 26250, 39375, 78750, 49, 98, 147, 294, 441, 882, 245, 490,
> 735, 1470, 2205, 4410, 1225, 2450

normative PARI program (Antti Karttunen, Oct 14 2019), verbatim:

> `A276086(n) = { my(m=1, p=2); while(n, m *= (p^(n%p)); n = n\p; p = nextprime(1+p)); (m); };`

(PARI's `nextprime(x)` is the least prime `≥ x`, so `nextprime(1+p)` is the least prime
`> p`; the loop therefore walks `p = 2, 3, 5, 7, …` and multiplies in `p_i ^ d_i` where
`d_i` is the `i`-th primorial-base digit of `n`.)

**A003961** — name, verbatim:

> Completely multiplicative with a(prime(k)) = prime(k+1).

formula, verbatim:

> If n = Product p(k)^e(k) then a(n) = Product p(k+1)^e(k).

terms (offset 1), verbatim:

> 1, 3, 5, 9, 7, 15, 11, 27, 25, 21, 13, 45, 17, 33, 35, 81, 19, 75, 23, 63, 55, 39, 29,
> 135, 49, 51, 125, 99, 31, 105, 37, 243, 65, 57, 77, 225, 41, 69, 85, 189, 43, 165, 47,
> 117, 175, 87, 53, 405, 121, 147, 95, 153, 59, 375, 91, 297, 115, 93, 61, 315, 67, 111,
> 275, 729, 119

normative PARI program (Michel Marcus, May 17 2014), verbatim:

> `a(n) = my(f = factor(n)); for (i=1, #f~, f[i, 1] = nextprime(f[i, 1]+1)); factorback(f);`

**A351458** — name, verbatim:

> Numbers k for which k * gcd(sigma(k), A276086(k)) is equal to sigma(k) * gcd(k,
> A276086(k)), where A276086 is the primorial base exp-function, and sigma gives the sum
> of divisors of its argument.

terms (offset 1), verbatim:

> 1, 10, 56, 9196, 9504, 56160, 121176, 239096, 354892, 411264, 555520, 716040, 804384,
> 904704, 1063348, 1387386, 1444352, 1454112, 1884800, 2708640, 3317248, 3548920,
> 4009824, 4634784, 6179712, 6795360, 7285248, 14511744, 16328466, 28377216, 29855232,
> 31940280, 37444736, 42711552, 49762944, 52815744

normative PARI program, verbatim:

> `isA351458(n) = { my(s=sigma(n), z=A276086(n)); (n*gcd(s,z))==(s*gcd(n,z)); };`

**A349745** — name, verbatim:

> Numbers k for which k * gcd(sigma(k), A003961(k)) is equal to sigma(k) * gcd(k,
> A003961(k)), where A003961 shifts the prime factorization one step towards larger
> primes, and sigma is the sum of divisors function.

terms (offset 1), verbatim:

> 1, 120, 216, 672, 2464, 22176, 228480, 523776, 640640, 837760, 5581440, 5765760,
> 7539840, 12999168, 19603584, 33860736, 38342304, 71344000, 95472000, 102136320,
> 197308800, 220093440, 345080736, 459818240, 807009280, 975576960, 1476304896,
> 1510831360, 1773584640

**A323653** — name, verbatim:

> Multiperfect numbers m such that sigma(m) is also multiperfect.

terms (offset 1), verbatim:

> 1, 459818240, 51001180160, 13188979363639752997731839211623940096,
> 5157152737616023231698245840143799191339008,
> 54530444405217553992377326508106948362108928,
> 133821156044600922812153118065015159487725568,
> 4989680372093758991515359988337845750507257510078971904

comment of **Antti Karttunen, Mar 20 2021, Feb 18 2022**, verbatim:

> Conjecture 1 (a): This sequence consists of those m for which sigma(m)/m is an integer
> (thus a term of A007691), and coprime with m. Or expressed in a slightly weaker form (b):
> {1} followed by those m for which sigma(m)/m is an integer, but not a divisor of m. In a
> slightly stronger form (c): For m > 1, sigma(m)/m is always the least prime not dividing
> m. This would imply both (a) and (b) forms.

> Conjecture 3: This sequence is the intersection of A007691 and A351458.

> Conjecture 4: This is a subsequence of A349745, thus also of A351551 and of A351554.

comment of **Antti Karttunen, May 16 2022** on A323653, verbatim:

> They are also the only 23 cases among that data such that gcd(n, sigma(n)/n) = 1, or in
> other words, for which the n and its abundancy are relatively prime, with abundancy in all
> cases being the least prime that does not divide n, A053669(n), which is a sufficient
> condition for inclusion in A351458.

and the matching comment on A351458, verbatim:

> It is conjectured that the intersection of this sequence with the multiperfect numbers
> (A007691) gives A323653, see comments in the latter.

**A007691** — name, verbatim: "Multiply-perfect numbers: n divides sigma(n)."  The
predicate `Nat.IsMultiperfect` is reused from `Enumerative.Practical`.

## Provenance of the computed values

Every A276086 value asserted for `n ≤ 56` and every A003961 value asserted for `n ≤ 12` is
one of the terms displayed above, and is checked against it.  Four asserted values lie past
the displayed prefixes and are *derived from the entries' normative PARI programs*, not
pinned to published terms: `A276086(120) = 2401`, `A003961(120) = 945`,
`A003961(459818240) = 37635660909`, and the divisor sums `σ(459818240) = 1379454720`,
`σ(1379454720) = 5517818880`.  All five were cross-checked outside Lean against independent
transcriptions of the same PARI programs (python3 + sympy 1.14.0; `sage` is not installed on
this machine).  The A323653, A349745 and A351458 *memberships* they certify are all pinned:
`459818240` is the second term of A323653, `120` is the second term of A349745.

## What is in this file

* `Nat.primorialRest` / `Nat.primorialDigit` — the primorial-base digit machinery, with
  `Nat.primorialRest_eq_div_prod` identifying `primorialRest i n` as `n / (p_0 ⋯ p_{i-1})`
  (so `primorialDigit i n` really is the `i`-th primorial-base digit of `n`);
* `Nat.primorialBaseExp` (**A276086**) as a finite product, with
  `Nat.primorialBaseExp_eq_prod_range` showing the truncation bound is immaterial, and
  ground-truth checks against the live term list for every `n ≤ 31` in the entry;
* `Nat.nextPrime` and `Nat.primeShift` (**A003961**), with complete multiplicativity
  (`Nat.primeShift_mul`), the prime-power value (`Nat.primeShift_prime_pow`), the
  `a(prime(k)) = prime(k+1)` clause of the OEIS name
  (`Nat.primeShift_nth_prime`), and ground truths against the live term list;
* `Nat.prime_dvd_primorialBaseExp` — the least prime not dividing `n` divides A276086(n)
  (the divisibility half of the entry's identity `A020639(a(n)) = A053669(n)`);
* `Nat.IsA351458`, `Nat.IsA349745`, `Nat.IsA323653` — the three predicates, each with the
  `0 < k` guard that the OEIS offsets demand (both congruences are *satisfied* at `k = 0`
  for junk reasons: `σ(0) = 0` makes both sides `0` —
  `Nat.congruence_holds_vacuously_at_zero`), plus positive and negative ground-truth
  witnesses at `1, 6, 10, 56, 120`;
* `Nat.isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul` — the **sufficient condition
  for membership in A351458** that A323653's May 16 2022 comment asserts, proved: if the
  abundancy of `k` is the least prime not dividing `k`, then `k` is a term of A351458;
* the second term of A323653, `459818240 = 2^8 * 5 * 7 * 19 * 37 * 73`, certified in full:
  `Nat.sum_divisors_459818240`, `Nat.isA323653_459818240`, `Nat.isA351458_459818240` (via
  the sufficient condition — A276086(459818240) has 52 decimal digits and is never
  evaluated), `Nat.primeShift_459818240`, `Nat.isA349745_459818240`;
* `Nat.KarttunenConjecture3`, `Nat.KarttunenConjecture4`, `Nat.KarttunenConjecture1c` — the
  archived open statements, with `Nat.karttunen3_nondegenerate` and
  `Nat.karttunen4_nondegenerate` recording that neither is vacuous (`1` and `459818240`
  satisfy every side; `6` and `120` are multiperfect yet fail every side);
* `Nat.karttunen3_forward_of_karttunen1c` — a **reduction**: Conjecture 1(c) implies the
  inclusion `A323653 ⊆ A007691 ∩ A351458`, i.e. one of the two halves of Conjecture 3.  The
  converse inclusion is untouched and remains open.

## Axiom audit

There is no `sorry`, no `admit` and no `native_decide` in this file; every declaration
reports exactly `{propext, Classical.choice, Quot.sound}`.  The conjectures are archived as
`Prop`-valued definitions, never as `sorry`-carrying theorems; the single theorem that
assumes one, `Nat.karttunen3_forward_of_karttunen1c`, takes it as an explicit hypothesis.
Kernel `decide` on divisor sums past `128` carries a per-declaration `maxRecDepth` bump.
-/

set_option autoImplicit false

namespace Nat

/-! ## The prime enumeration

Mathlib's `Nat.nth Nat.Prime` is the `0`-indexed enumeration of the primes, and
`Nat.nth_prime_zero_eq_two` … `Nat.nth_prime_four_eq_eleven` are already `@[simp]`.  Two
more table entries are needed to certify A276086 out to `n = 120`, whose primorial-base
expansion reaches digit index `6`. -/

/-- `Nat.nth Nat.Prime 5 = 13`. -/
@[simp] theorem nth_prime_five_eq_thirteen : nth Prime 5 = 13 := by
  have hcount : count Prime 13 = 5 := by decide
  simpa [hcount] using nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 13)

/-- `Nat.nth Nat.Prime 6 = 17`. -/
@[simp] theorem nth_prime_six_eq_seventeen : nth Prime 6 = 17 := by
  have hcount : count Prime 17 = 6 := by decide
  simpa [hcount] using nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 17)

/-- Every prime in the enumeration is at least `2`. -/
theorem two_le_nth_prime (i : ℕ) : 2 ≤ nth Prime i := (prime_nth_prime i).two_le

/-- The set of primes, as a `Set.ofPred`, is infinite; this is the side condition on the
`Nat.nth` API. -/
theorem ofPred_prime_infinite : (Set.ofPred Nat.Prime).Infinite := infinite_setOfPred_prime

/-! ## A276086: the primorial base exp-function

The PARI loop `while(n, m *= (p^(n%p)); n = n\p; p = nextprime(1+p))` maintains a running
remainder that is successively divided by `2, 3, 5, 7, …`.  `primorialRest i n` is that
remainder after `i` rounds, `primorialDigit i n` is the digit read off in round `i`, and
`primorialBaseExp n` is the product the loop accumulates. -/

/-- `primorialRest i n` is `n` with its first `i` primorial-base digits stripped: the value
of the PARI loop variable `n` after `i` iterations.  Equivalently
`n / (p_0 * p_1 * ⋯ * p_{i-1})` — see `Nat.primorialRest_eq_div_prod`. -/
noncomputable def primorialRest : ℕ → ℕ → ℕ
  | 0, n => n
  | (i + 1), n => primorialRest i n / nth Prime i

/-- `primorialDigit i n` is the `i`-th digit of `n` in the primorial base, i.e. the
exponent `n % p` read off in round `i` of the PARI loop. -/
noncomputable def primorialDigit (i n : ℕ) : ℕ := primorialRest i n % nth Prime i

/-- **A276086**, the primorial base exp-function: the digits of `n` in the primorial base
become the exponents of the successive primes.  The bound `Finset.range n` is a safe
over-estimate of the digit count — `Nat.primorialBaseExp_eq_prod_range` shows every bound
`m` with `n < 2 ^ m` computes the same value, and `n < 2 ^ n` always holds.  At `n = 0`
the product is empty, giving `a(0) = 1` as the entry's offset-0 term requires. -/
noncomputable def primorialBaseExp (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, nth Prime i ^ primorialDigit i n

/-- Base case: the primorial rest at stage 0 is `n` itself. -/
@[simp] theorem primorialRest_zero (n : ℕ) : primorialRest 0 n = n := rfl

/-- Recurrence for the primorial rest. -/
@[simp] theorem primorialRest_succ (i n : ℕ) :
    primorialRest (i + 1) n = primorialRest i n / nth Prime i := rfl

/-- The stripped remainder is a genuine primorial quotient: `primorialRest i n` is
`n` divided by the product of the first `i` primes.  Together with
`Nat.primorialDigit` this is the "primorial base representation of `n`" of the A276086
name. -/
theorem primorialRest_eq_div_prod (i n : ℕ) :
    primorialRest i n = n / ∏ j ∈ Finset.range i, nth Prime j := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [primorialRest_succ, ih, Nat.div_div_eq_div_mul, Finset.prod_range_succ]

/-- Quantitative decay of the stripped remainder: dividing by primes `≥ 2` shrinks `n` at
least as fast as halving does. -/
theorem primorialRest_lt : ∀ (i : ℕ) {n c : ℕ}, n < 2 ^ i * c → primorialRest i n < c
  | 0, n, c, h => by simpa using h
  | (i + 1), n, c, h => by
      have hstep : n < 2 ^ i * (2 * c) := by
        calc n < 2 ^ (i + 1) * c := h
          _ = 2 ^ i * (2 * c) := by ring
      have hrest : primorialRest i n < 2 * c := primorialRest_lt i hstep
      have hdiv : primorialRest i n / nth Prime i ≤ primorialRest i n / 2 :=
        Nat.div_le_div_left (two_le_nth_prime i) (by norm_num)
      have hhalf : primorialRest i n / 2 < c := by omega
      rw [primorialRest_succ]
      omega

/-- Once `n` is below `2 ^ i`, all its primorial-base digits from index `i` on vanish. -/
theorem primorialRest_eq_zero_of_lt {i n : ℕ} (h : n < 2 ^ i) : primorialRest i n = 0 := by
  have := primorialRest_lt i (c := 1) (by simpa using h)
  omega

/-- The digits from index `i` on vanish once `n < 2 ^ i`. -/
theorem primorialDigit_eq_zero_of_lt {i n : ℕ} (h : n < 2 ^ i) : primorialDigit i n = 0 := by
  simp [primorialDigit, primorialRest_eq_zero_of_lt h]

/-- The truncation bound in `Nat.primorialBaseExp` is immaterial: any `m` with `n < 2 ^ m`
computes the same product.  This is what makes the `Finset.range n` in the definition a
harmless over-estimate rather than a hidden parameter. -/
theorem primorialBaseExp_eq_prod_range {n m : ℕ} (h : n < 2 ^ m) :
    primorialBaseExp n = ∏ i ∈ Finset.range m, nth Prime i ^ primorialDigit i n := by
  -- Extending the truncation bound past `2 ^ k > n` only multiplies in `p_i ^ 0 = 1`.
  have key : ∀ k l : ℕ, n < 2 ^ k → k ≤ l →
      (∏ i ∈ Finset.range k, nth Prime i ^ primorialDigit i n)
        = ∏ i ∈ Finset.range l, nth Prime i ^ primorialDigit i n := by
    intro k l hk hkl
    refine Finset.prod_subset (Finset.range_subset_range.mpr hkl) ?_
    intro i _ hi
    have hik : k ≤ i := by simpa using hi
    have hlt : n < 2 ^ i := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hik)
    simp [primorialDigit_eq_zero_of_lt hlt]
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  rw [primorialBaseExp, key n (max n m) hn (le_max_left n m),
    key m (max n m) h (le_max_right n m)]

/-- A276086 takes positive values. -/
theorem primorialBaseExp_pos (n : ℕ) : 0 < primorialBaseExp n :=
  Finset.prod_pos fun i _ => Nat.pow_pos (by have := two_le_nth_prime i; omega)

/-! ### Ground truth for A276086

Every `n ≤ 31` is certified against the live term list of the entry.  Each check truncates
the product at `m = 5` via `Nat.primorialBaseExp_eq_prod_range` (`31 < 32 = 2 ^ 5`); the
five primes involved, `2, 3, 5, 7, 11`, are Mathlib `@[simp]` table entries. -/

private theorem primorialBaseExp_eq_of_lt_32 {n : ℕ} (h : n < 32) :
    primorialBaseExp n = ∏ i ∈ Finset.range 5, nth Prime i ^ primorialDigit i n :=
  primorialBaseExp_eq_prod_range (by omega)

example : primorialBaseExp 0 = 1 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

/-- A276086 at `n = 1`; `1` is the first term of A351458. -/
theorem primorialBaseExp_one : primorialBaseExp 1 = 2 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

example : primorialBaseExp 2 = 3 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 3 = 6 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 4 = 9 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 5 = 18 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 6 = 5 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 7 = 10 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 8 = 15 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 9 = 30 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

/-- A276086 at `n = 10`; `10` is the second term of A351458. -/
theorem primorialBaseExp_ten : primorialBaseExp 10 = 45 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

example : primorialBaseExp 11 = 90 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 12 = 25 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 13 = 50 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 14 = 75 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 15 = 150 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 16 = 225 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 17 = 450 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 18 = 125 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 19 = 250 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 20 = 375 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 21 = 750 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 22 = 1125 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 23 = 2250 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 24 = 625 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 25 = 1250 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 26 = 1875 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 27 = 3750 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 28 = 5625 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 29 = 11250 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 30 = 7 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]
example : primorialBaseExp 31 = 14 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

/-- A276086 at `n = 56`; `56` is the third term of A351458.  Here the product is truncated
at `m = 6` (`56 < 64`), which brings in `nth Prime 5 = 13`. -/
theorem primorialBaseExp_fiftySix : primorialBaseExp 56 = 13125 := by
  rw [primorialBaseExp_eq_prod_range (m := 6) (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

/-- A276086 at `n = 6`; `6` is a multiperfect number that Karttunen's Conjecture 3 must
exclude. -/
theorem primorialBaseExp_six : primorialBaseExp 6 = 5 := by
  rw [primorialBaseExp_eq_of_lt_32 (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

/-- A276086 at `n = 120`; the value is `7 ^ 4 = 2401`, and `7` is the least prime not
dividing `120 = 2^3 * 3 * 5`, as A276086's identity `A020639(a(n)) = A053669(n)` predicts.
`120` is a multiperfect number that Karttunen's Conjecture 3 must exclude.  The product is
truncated at `m = 7` (`120 < 128`), which brings in `nth Prime 6 = 17`. -/
theorem primorialBaseExp_onetwenty : primorialBaseExp 120 = 2401 := by
  rw [primorialBaseExp_eq_prod_range (m := 7) (by norm_num)]
  simp [Finset.prod_range_succ, primorialDigit]

/-! ### The least prime not dividing `n` divides A276086(n)

A276086 records the identity `A020639(a(n)) = A053669(n)` — "It maps the smallest prime not
dividing n to the smallest prime dividing n" (entry comment, verbatim).  Only the
divisibility half is needed below, and it is what makes the sufficient condition for
membership in A351458 work. -/

/-- The product of the first `j` primes divides any `n` that all of them divide. -/
theorem prod_nth_prime_dvd {n : ℕ} : ∀ {j : ℕ}, (∀ i < j, nth Prime i ∣ n) →
    (∏ i ∈ Finset.range j, nth Prime i) ∣ n := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hdvd
      rw [Finset.prod_range_succ]
      have hcop : Nat.Coprime (∏ i ∈ Finset.range j, nth Prime i) (nth Prime j) :=
        Nat.Coprime.prod_left fun i hi =>
          (coprime_primes (prime_nth_prime i) (prime_nth_prime j)).mpr
            ((nth_injective ofPred_prime_infinite).ne (by simpa using (Finset.mem_range.mp hi).ne))
      exact hcop.mul_dvd_of_dvd_of_dvd (ih fun i hi => hdvd i (by omega)) (hdvd j (by omega))

/-- If every prime below `q` divides `n` while `q` does not — i.e. `q` is the least prime
not dividing `n`, A053669(n) — then `q` divides A276086(n).

The mechanism: `p_0 ⋯ p_{j-1}` divides `n`, so the `j`-th primorial-base digit of `n` is
`(n / p_0 ⋯ p_{j-1}) mod q`, which is nonzero precisely because `q ∤ n`; hence `q ^ d` with
`d ≥ 1` is one of the factors of the A276086 product. -/
theorem prime_dvd_primorialBaseExp {n q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hmin : ∀ p < q, p.Prime → p ∣ n) : q ∣ primorialBaseExp n := by
  set j := count Prime q with hjdef
  have hnthj : nth Prime j = q := nth_count hq
  -- Every earlier prime in the enumeration is smaller than `q`, hence divides `n`.
  have hearlier : ∀ i < j, nth Prime i ∣ n := by
    intro i hi
    have hlt : nth Prime i < q := hnthj ▸ (nth_lt_nth ofPred_prime_infinite).mpr hi
    exact hmin _ hlt (prime_nth_prime i)
  have hP : (∏ i ∈ Finset.range j, nth Prime i) ∣ n := prod_nth_prime_dvd hearlier
  -- The `j`-th digit is nonzero: otherwise `q` would divide `n / (p_0 ⋯ p_{j-1})`, hence `n`.
  have hdigit : primorialDigit j n ≠ 0 := by
    intro hzero
    rw [primorialDigit, hnthj] at hzero
    have hqrest : q ∣ primorialRest j n := Nat.dvd_of_mod_eq_zero hzero
    have hfactor : n = (∏ i ∈ Finset.range j, nth Prime i) * primorialRest j n := by
      rw [primorialRest_eq_div_prod, Nat.mul_div_cancel' hP]
    exact hqn (hfactor ▸ hqrest.mul_left _)
  -- A nonzero digit at index `j` forces `2 ^ j ≤ n`, so `j` is inside the product's range.
  have hjn : j < n := by
    by_contra hcon
    exact hdigit (primorialDigit_eq_zero_of_lt (lt_of_le_of_lt (not_lt.mp hcon)
      Nat.lt_two_pow_self))
  calc q = nth Prime j := hnthj.symm
    _ ∣ nth Prime j ^ primorialDigit j n := dvd_pow_self _ hdigit
    _ ∣ primorialBaseExp n :=
        Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hjn)

-- Satisfiability of `Nat.prime_dvd_primorialBaseExp` at `n = 6`, `q = 5`: `5` is the least
-- prime not dividing `6`, and A276086(6) = 5.
example : (5 : ℕ) ∣ primorialBaseExp 6 :=
  prime_dvd_primorialBaseExp (by norm_num) (by decide) (by decide)

/-! ## A003961: the prime shift

"Completely multiplicative with a(prime(k)) = prime(k+1)"; the PARI program replaces each
prime in the factorisation of `n` by `nextprime(p+1)`, the least prime exceeding `p`. -/

/-- `nextPrime p` is the least prime strictly greater than `p`.  This is total and
junk-free — it is the intended value at *every* natural number, not just at primes
(`nextPrime 4 = 5`), matching PARI's `nextprime(p+1)`. -/
def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- `nextPrime p` is prime. -/
theorem prime_nextPrime (p : ℕ) : (nextPrime p).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (p + 1))).2

/-- `p < nextPrime p`. -/
theorem lt_nextPrime (p : ℕ) : p < nextPrime p :=
  (Nat.find_spec (Nat.exists_infinite_primes (p + 1))).1

/-- Minimality of `Nat.nextPrime`: no prime lies strictly between `p` and `nextPrime p`. -/
theorem nextPrime_le {p q : ℕ} (hq : q.Prime) (hpq : p < q) : nextPrime p ≤ q :=
  Nat.find_le ⟨hpq, hq⟩

/-- `Nat.nextPrime` steps the Mathlib prime enumeration by one index — this is the
`a(prime(k)) = prime(k+1)` clause of the A003961 name. -/
theorem nextPrime_nth_prime (k : ℕ) : nextPrime (nth Prime k) = nth Prime (k + 1) := by
  refine le_antisymm (nextPrime_le (prime_nth_prime (k + 1))
    ((nth_lt_nth ofPred_prime_infinite).mpr (Nat.lt_succ_self k))) ?_
  set q := nextPrime (nth Prime k) with hq
  have hqprime : q.Prime := prime_nextPrime _
  have hlt : nth Prime k < q := lt_nextPrime _
  have hcount : k < count Prime q :=
    (lt_nth_iff_count_lt ofPred_prime_infinite).mpr hlt
  calc nth Prime (k + 1) ≤ nth Prime (count Prime q) :=
        (nth_le_nth ofPred_prime_infinite).mpr hcount
    _ = q := nth_count hqprime

/-- **A003961**, the prime shift: replace every prime in the factorisation of `n` by the
next prime, keeping exponents.  `Nat.factorization 0 = 0`, so `primeShift 0 = 1`; A003961
has offset `1`, so that value is off-sequence and carries no claim. -/
def primeShift (n : ℕ) : ℕ := n.factorization.prod fun p e => nextPrime p ^ e

/-- `primeShift 1 = 1`. -/
@[simp] theorem primeShift_one : primeShift 1 = 1 := by simp [primeShift]

/-- A003961 on prime powers: `a(p ^ k) = nextPrime p ^ k`. -/
theorem primeShift_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeShift (p ^ k) = nextPrime p ^ k := by
  rw [primeShift, hp.factorization_pow]
  exact Finsupp.prod_single_index (pow_zero (nextPrime p))

/-- A003961 is completely multiplicative (the OEIS name's defining property). -/
theorem primeShift_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeShift (m * n) = primeShift m * primeShift n := by
  unfold primeShift
  rw [Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun p => pow_zero (nextPrime p))
      (fun p b₁ b₂ => pow_add (nextPrime p) b₁ b₂)]

/-- A003961 maps the `k`-th prime to the `(k+1)`-st: "a(prime(k)) = prime(k+1)". -/
theorem primeShift_nth_prime (k : ℕ) : primeShift (nth Prime k) = nth Prime (k + 1) := by
  have hpow := primeShift_prime_pow (prime_nth_prime k) 1
  rw [pow_one] at hpow
  rw [hpow, pow_one, nextPrime_nth_prime]

/-- A003961 takes positive values. -/
theorem primeShift_pos (n : ℕ) : 0 < primeShift n := by
  rw [primeShift, Finsupp.prod]
  exact Finset.prod_pos fun p _ => Nat.pow_pos (prime_nextPrime p).pos

/-! ### Ground truth for A003961

Values are certified against the live term list (offset `1`) by the two structural
lemmas — complete multiplicativity and the prime-power value — never by unfolding the
`Finsupp.prod`. -/

private theorem nextPrime_eq_of {p q : ℕ} (hq : q.Prime) (hpq : p < q)
    (hmin : ∀ r < q, ¬(p + 1 ≤ r ∧ r.Prime)) : nextPrime p = q := by
  rw [nextPrime, Nat.find_eq_iff]
  exact ⟨⟨hpq, hq⟩, hmin⟩

/-- `nextPrime 2 = 3`. -/
theorem nextPrime_two : nextPrime 2 = 3 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- `nextPrime 3 = 5`. -/
theorem nextPrime_three : nextPrime 3 = 5 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- `nextPrime 5 = 7`. -/
theorem nextPrime_five : nextPrime 5 = 7 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- `nextPrime 7 = 11`. -/
theorem nextPrime_seven : nextPrime 7 = 11 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- `nextPrime 19 = 23`. -/
theorem nextPrime_nineteen : nextPrime 19 = 23 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- `nextPrime 37 = 41`. -/
theorem nextPrime_thirtySeven : nextPrime 37 = 41 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- `nextPrime 73 = 79`. -/
theorem nextPrime_seventyThree : nextPrime 73 = 79 :=
  nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

-- `Nat.nextPrime` is junk-free off the primes as well.
example : nextPrime 4 = 5 := nextPrime_eq_of (by norm_num) (by norm_num) (by decide)

/-- Evaluation helper: A003961 at a prime is the next prime. -/
private theorem primeShift_of_prime {p q : ℕ} (hp : p.Prime) (h : nextPrime p = q) :
    primeShift p = q := by
  have hpow := primeShift_prime_pow hp 1
  rw [pow_one, pow_one, h] at hpow
  exact hpow

/-- Evaluation helper: A003961 at a prime power. -/
private theorem primeShift_of_prime_pow {p q k v : ℕ} (hp : p.Prime) (h : nextPrime p = q)
    (hv : q ^ k = v) : primeShift (p ^ k) = v := by
  rw [primeShift_prime_pow hp k, h, hv]

/-- Evaluation helper: A003961 across a product. -/
private theorem primeShift_mul_eq {m n a b c : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (ha : primeShift m = a) (hb : primeShift n = b) (hc : a * b = c) :
    primeShift (m * n) = c := by
  rw [primeShift_mul hm hn, ha, hb, hc]

/-- A003961 at `2`: the second term of the entry. -/
theorem primeShift_two : primeShift 2 = 3 := primeShift_of_prime Nat.prime_two nextPrime_two

/-- A003961 at `3`: the third term of the entry. -/
theorem primeShift_three : primeShift 3 = 5 :=
  primeShift_of_prime Nat.prime_three nextPrime_three

/-- A003961 at `5`: the fifth term of the entry. -/
theorem primeShift_five : primeShift 5 = 7 :=
  primeShift_of_prime Nat.prime_five nextPrime_five

/-- `primeShift 7 = 11`. -/
theorem primeShift_seven : primeShift 7 = 11 :=
  primeShift_of_prime (by norm_num) nextPrime_seven

/-- `primeShift 19 = 23`. -/
theorem primeShift_nineteen : primeShift 19 = 23 :=
  primeShift_of_prime (by norm_num) nextPrime_nineteen

/-- `primeShift 37 = 41`. -/
theorem primeShift_thirtySeven : primeShift 37 = 41 :=
  primeShift_of_prime (by norm_num) nextPrime_thirtySeven

/-- `primeShift 73 = 79`. -/
theorem primeShift_seventyThree : primeShift 73 = 79 :=
  primeShift_of_prime (by norm_num) nextPrime_seventyThree

/-- A003961 at `4`: the fourth term of the entry. -/
theorem primeShift_four : primeShift 4 = 9 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h]
  exact primeShift_of_prime_pow Nat.prime_two nextPrime_two (by norm_num)

/-- A003961 at `6`: the sixth term of the entry. -/
theorem primeShift_six : primeShift 6 = 15 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h]
  exact primeShift_mul_eq (by norm_num) (by norm_num) primeShift_two primeShift_three
    (by norm_num)

/-- A003961 at `12`: the twelfth term of the entry. -/
example : primeShift 12 = 45 := by
  have h : (12 : ℕ) = 4 * 3 := by norm_num
  rw [h]
  exact primeShift_mul_eq (by norm_num) (by norm_num) primeShift_four primeShift_three
    (by norm_num)

/-- A003961 at `120`: `120 = 2^3 * 3 * 5` shifts to `3^3 * 5 * 7 = 945`.  `120` is the
second term of A349745. -/
theorem primeShift_onetwenty : primeShift 120 = 945 := by
  have h8 : primeShift 8 = 27 := by
    have h : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h]
    exact primeShift_of_prime_pow Nat.prime_two nextPrime_two (by norm_num)
  have h15 : primeShift 15 = 35 := by
    have h : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h]
    exact primeShift_mul_eq (by norm_num) (by norm_num) primeShift_three primeShift_five
      (by norm_num)
  have h : (120 : ℕ) = 8 * 15 := by norm_num
  rw [h]
  exact primeShift_mul_eq (by norm_num) (by norm_num) h8 h15 (by norm_num)

/-! ## The two congruence families A351458 and A349745

Both entries impose the same shape, `k * gcd(σ(k), f(k)) = σ(k) * gcd(k, f(k))`, with the
companion function `f` taken to be A276086 and A003961 respectively.  Each carries an
explicit `0 < k` guard: `Nat.divisors 0 = ∅` gives `σ(0) = 0`, so at `k = 0` both sides of
either identity are `0` and the unguarded predicate would hold vacuously, contradicting the
offset `1` of both entries (`Nat.congruence_holds_vacuously_at_zero`). -/

/-- **A351458** (OEIS): `0 < k` and `k * gcd(σ(k), A276086(k)) = σ(k) * gcd(k, A276086(k))`. -/
def IsA351458 (k : ℕ) : Prop :=
  0 < k ∧ k * Nat.gcd (∑ d ∈ k.divisors, d) (primorialBaseExp k)
    = (∑ d ∈ k.divisors, d) * Nat.gcd k (primorialBaseExp k)

/-- **A349745** (OEIS): `0 < k` and `k * gcd(σ(k), A003961(k)) = σ(k) * gcd(k, A003961(k))`. -/
def IsA349745 (k : ℕ) : Prop :=
  0 < k ∧ k * Nat.gcd (∑ d ∈ k.divisors, d) (primeShift k)
    = (∑ d ∈ k.divisors, d) * Nat.gcd k (primeShift k)

/-- **A323653** (OEIS): "Multiperfect numbers `m` such that `sigma(m)` is also
multiperfect."  `Nat.IsMultiperfect` already carries its own `0 < ·` guard. -/
def IsA323653 (m : ℕ) : Prop := IsMultiperfect m ∧ IsMultiperfect (∑ d ∈ m.divisors, d)

/-- Both congruence identities hold at `k = 0` for the junk reason that `σ(0) = 0` zeroes
both sides.  This is the degeneracy the `0 < k` guards in `Nat.IsA351458` and
`Nat.IsA349745` exclude. -/
theorem congruence_holds_vacuously_at_zero :
    (0 : ℕ) * Nat.gcd (∑ d ∈ (0 : ℕ).divisors, d) (primorialBaseExp 0)
        = (∑ d ∈ (0 : ℕ).divisors, d) * Nat.gcd 0 (primorialBaseExp 0)
      ∧ (0 : ℕ) * Nat.gcd (∑ d ∈ (0 : ℕ).divisors, d) (primeShift 0)
        = (∑ d ∈ (0 : ℕ).divisors, d) * Nat.gcd 0 (primeShift 0) := by
  constructor <;> simp

/-- `0` is excluded from A351458 by the positivity guard. -/
theorem not_isA351458_zero : ¬ IsA351458 0 := fun h => absurd h.1 (lt_irrefl 0)

/-- `0` is excluded from A349745 by the positivity guard. -/
theorem not_isA349745_zero : ¬ IsA349745 0 := fun h => absurd h.1 (lt_irrefl 0)

/-! ### Ground truth for A351458, A349745 and A323653 -/

/-- `1` is the first term of A351458. -/
theorem isA351458_one : IsA351458 1 := by
  have hs : ∑ d ∈ (1 : ℕ).divisors, d = 1 := by decide
  refine ⟨by norm_num, ?_⟩
  rw [hs, primorialBaseExp_one]

/-- `10` is the second term of A351458: `σ(10) = 18`, `A276086(10) = 45`, and
`10 * gcd(18, 45) = 90 = 18 * gcd(10, 45)`. -/
theorem isA351458_ten : IsA351458 10 := by
  have hs : ∑ d ∈ (10 : ℕ).divisors, d = 18 := by decide
  refine ⟨by norm_num, ?_⟩
  rw [hs, primorialBaseExp_ten]
  norm_num

/-- `56` is the third term of A351458: `σ(56) = 120`, `A276086(56) = 13125`, and
`56 * gcd(120, 13125) = 840 = 120 * gcd(56, 13125)`. -/
theorem isA351458_fiftySix : IsA351458 56 := by
  have hs : ∑ d ∈ (56 : ℕ).divisors, d = 120 := by decide
  refine ⟨by norm_num, ?_⟩
  rw [hs, primorialBaseExp_fiftySix]
  norm_num

/-- `6` is multiperfect but is *not* a term of A351458: `6 * gcd(12, 5) = 6` while
`12 * gcd(6, 5) = 12`. -/
theorem not_isA351458_six : ¬ IsA351458 6 := by
  have hs : ∑ d ∈ (6 : ℕ).divisors, d = 12 := by decide
  rintro ⟨-, heq⟩
  rw [hs, primorialBaseExp_six] at heq
  norm_num at heq

set_option maxRecDepth 20000 in
/-- `120` is multiperfect but is *not* a term of A351458: `120 * gcd(360, 2401) = 120`
while `360 * gcd(120, 2401) = 360`. -/
theorem not_isA351458_onetwenty : ¬ IsA351458 120 := by
  have hs : ∑ d ∈ (120 : ℕ).divisors, d = 360 := by decide
  rintro ⟨-, heq⟩
  rw [hs, primorialBaseExp_onetwenty] at heq
  norm_num at heq

/-- `1` is the first term of A349745. -/
theorem isA349745_one : IsA349745 1 := by
  have hs : ∑ d ∈ (1 : ℕ).divisors, d = 1 := by decide
  refine ⟨by norm_num, ?_⟩
  rw [hs, primeShift_one]

/-- `120` is the second term of A349745: `σ(120) = 360`, `A003961(120) = 945`, and
`120 * gcd(360, 945) = 5400 = 360 * gcd(120, 945)`. -/
theorem isA349745_onetwenty : IsA349745 120 := by
  have hs : ∑ d ∈ (120 : ℕ).divisors, d = 360 := by decide
  refine ⟨by norm_num, ?_⟩
  rw [hs, primeShift_onetwenty]
  norm_num

/-- `6` is not a term of A349745: `6 * gcd(12, 15) = 18` while `12 * gcd(6, 15) = 36`. -/
theorem not_isA349745_six : ¬ IsA349745 6 := by
  have hs : ∑ d ∈ (6 : ℕ).divisors, d = 12 := by decide
  rintro ⟨-, heq⟩
  rw [hs, primeShift_six] at heq
  norm_num at heq

/-- `1` is the first term of A323653. -/
theorem isA323653_one : IsA323653 1 := by
  have hs : ∑ d ∈ (1 : ℕ).divisors, d = 1 := by decide
  exact ⟨by decide, by rw [hs]; decide⟩

/-- `6` is multiperfect but `σ(6) = 12` is not, so `6` is not a term of A323653. -/
theorem not_isA323653_six : ¬ IsA323653 6 := by
  have hs : ∑ d ∈ (6 : ℕ).divisors, d = 12 := by decide
  rintro ⟨-, hmul⟩
  rw [hs] at hmul
  exact absurd hmul (by decide)

/-- `120` is multiperfect but `σ(120) = 360` is not, so `120` is not a term of A323653. -/
theorem not_isA323653_onetwenty : ¬ IsA323653 120 := by
  have hs : ∑ d ∈ (120 : ℕ).divisors, d = 360 := by decide
  rintro ⟨-, hmul⟩
  rw [hs] at hmul
  exact absurd hmul (by decide)

/-! ## The OEIS sufficient condition for membership in A351458

A323653's comment of **Antti Karttunen, May 16 2022** records, verbatim:

> They are also the only 23 cases among that data such that gcd(n, sigma(n)/n) = 1, or in
> other words, for which the n and its abundancy are relatively prime, with abundancy in all
> cases being the least prime that does not divide n, A053669(n), which is a sufficient
> condition for inclusion in A351458.

`Nat.isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul` is that sufficient condition,
proved.  It is the only route by which this file can certify membership in A351458 at
arguments where A276086 is astronomically large: A276086(459818240) has 52 decimal digits,
but the theorem never evaluates it. -/

/-- Splitting a prime off a gcd: if the prime `q` misses `k` but divides `z`, then
`gcd(q * k, z) = q * gcd(k, z)`. -/
theorem gcd_mul_of_prime_not_dvd {q k z : ℕ} (hq : q.Prime) (hqk : ¬ q ∣ k) (hqz : q ∣ z) :
    Nat.gcd (q * k) z = q * Nat.gcd k z := by
  obtain ⟨w, rfl⟩ := hqz
  have hcop : Nat.Coprime q k := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqk
  rw [Nat.gcd_mul_left, hcop.gcd_mul_left_cancel_right w]

-- Satisfiability of `Nat.gcd_mul_of_prime_not_dvd` at `q = 5`, `k = 6`, `z = 5`.
example : Nat.gcd (5 * 6) 5 = 5 * Nat.gcd 6 5 :=
  gcd_mul_of_prime_not_dvd (by norm_num) (by decide) dvd_rfl

/-- **The OEIS sufficient condition for A351458.**  If the abundancy of `k` is exactly the
least prime `q` not dividing `k` — i.e. `σ(k) = q * k`, `q` prime, `q ∤ k`, and every prime
below `q` divides `k` — then `k` is a term of A351458.

The proof is a one-prime gcd split: `q ∣ A276086(k)` by
`Nat.prime_dvd_primorialBaseExp`, so `gcd(σ(k), A276086(k)) = gcd(q * k, A276086(k))` equals
`q * gcd(k, A276086(k))`, and multiplying by `k` gives `σ(k) * gcd(k, A276086(k))`. -/
theorem isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul {k q : ℕ} (hq : q.Prime)
    (hqk : ¬ q ∣ k) (hmin : ∀ p < q, p.Prime → p ∣ k)
    (hsum : ∑ d ∈ k.divisors, d = q * k) : IsA351458 k := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun hzero => hqk (hzero ▸ dvd_zero q)
  refine ⟨hk, ?_⟩
  rw [hsum, gcd_mul_of_prime_not_dvd hq hqk (prime_dvd_primorialBaseExp hq hqk hmin)]
  ring

/-! ## The second term of A323653: `459818240`

`459818240 = 2^8 * 5 * 7 * 19 * 37 * 73` has `σ = 3 * 459818240 = 1379454720`, which in turn
has `σ = 4 * 1379454720`; `3` is the least prime not dividing `459818240`.  This is the only
A323653 term above `1` small enough to certify here, and it exercises every layer of the
file: the sufficient condition (A351458 membership without evaluating the 52-digit
A276086 value) and the direct A003961 computation (A349745 membership). -/

/-- Evaluation helper: `σ` is multiplicative on coprime factors. -/
private theorem sum_divisors_mul_eq {m n s t u : ℕ} (hco : Nat.Coprime m n)
    (hm : ∑ d ∈ m.divisors, d = s) (hn : ∑ d ∈ n.divisors, d = t) (hu : s * t = u) :
    ∑ d ∈ (m * n).divisors, d = u := by
  rw [hco.sum_divisors_mul, hm, hn, hu]

private theorem sum_divisors_3 : ∑ d ∈ (3 : ℕ).divisors, d = 4 := by decide
private theorem sum_divisors_5 : ∑ d ∈ (5 : ℕ).divisors, d = 6 := by decide
private theorem sum_divisors_7 : ∑ d ∈ (7 : ℕ).divisors, d = 8 := by decide
private theorem sum_divisors_19 : ∑ d ∈ (19 : ℕ).divisors, d = 20 := by decide
private theorem sum_divisors_37 : ∑ d ∈ (37 : ℕ).divisors, d = 38 := by decide
private theorem sum_divisors_73 : ∑ d ∈ (73 : ℕ).divisors, d = 74 := by decide
private theorem sum_divisors_256 : ∑ d ∈ (256 : ℕ).divisors, d = 511 := by decide

private theorem sum_divisors_35 : ∑ d ∈ (35 : ℕ).divisors, d = 48 := by
  have h : (35 : ℕ) = 5 * 7 := by norm_num
  rw [h]
  exact sum_divisors_mul_eq (by norm_num) sum_divisors_5 sum_divisors_7 (by norm_num)

private theorem sum_divisors_665 : ∑ d ∈ (665 : ℕ).divisors, d = 960 := by
  have h : (665 : ℕ) = 35 * 19 := by norm_num
  rw [h]
  exact sum_divisors_mul_eq (by norm_num) sum_divisors_35 sum_divisors_19 (by norm_num)

private theorem sum_divisors_24605 : ∑ d ∈ (24605 : ℕ).divisors, d = 36480 := by
  have h : (24605 : ℕ) = 665 * 37 := by norm_num
  rw [h]
  exact sum_divisors_mul_eq (by norm_num) sum_divisors_665 sum_divisors_37 (by norm_num)

private theorem sum_divisors_1796165 : ∑ d ∈ (1796165 : ℕ).divisors, d = 2699520 := by
  have h : (1796165 : ℕ) = 24605 * 73 := by norm_num
  rw [h]
  exact sum_divisors_mul_eq (by norm_num) sum_divisors_24605 sum_divisors_73 (by norm_num)

/-- `σ(459818240) = 1379454720 = 3 * 459818240`, via `459818240 = 2^8 * 1796165`. -/
theorem sum_divisors_459818240 : ∑ d ∈ (459818240 : ℕ).divisors, d = 1379454720 := by
  have h : (459818240 : ℕ) = 256 * 1796165 := by norm_num
  rw [h]
  exact sum_divisors_mul_eq (by norm_num) sum_divisors_256 sum_divisors_1796165 (by norm_num)

/-- `σ(1379454720) = 5517818880 = 4 * 1379454720`, via `1379454720 = 3 * 459818240`. -/
theorem sum_divisors_1379454720 : ∑ d ∈ (1379454720 : ℕ).divisors, d = 5517818880 := by
  have h : (1379454720 : ℕ) = 3 * 459818240 := by norm_num
  rw [h]
  exact sum_divisors_mul_eq (by norm_num) sum_divisors_3 sum_divisors_459818240 (by norm_num)

/-- `459818240` is multiply-perfect, of abundancy `3`. -/
theorem isMultiperfect_459818240 : IsMultiperfect 459818240 := by
  refine ⟨by norm_num, ?_⟩
  rw [sum_divisors_459818240]
  exact ⟨3, by norm_num⟩

/-- `1379454720 = σ(459818240)` is multiply-perfect, of abundancy `4`. -/
theorem isMultiperfect_1379454720 : IsMultiperfect 1379454720 := by
  refine ⟨by norm_num, ?_⟩
  rw [sum_divisors_1379454720]
  exact ⟨4, by norm_num⟩

/-- `459818240` is the second term of A323653. -/
theorem isA323653_459818240 : IsA323653 459818240 := by
  refine ⟨isMultiperfect_459818240, ?_⟩
  rw [sum_divisors_459818240]
  exact isMultiperfect_1379454720

/-- `459818240` is a term of A351458 — the second term of A323653 satisfies the A276086
congruence, as Karttunen's Conjecture 3 requires.  A276086(459818240) is a 52-digit number
and is never evaluated: the sufficient condition supplies the divisibility that the gcd
split needs. -/
theorem isA351458_459818240 : IsA351458 459818240 :=
  isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul (q := 3) (by norm_num) (by norm_num)
    (by decide) (by rw [sum_divisors_459818240])

/-- A003961 at `459818240`: `2^8 * 5 * 7 * 19 * 37 * 73` shifts to
`3^8 * 7 * 11 * 23 * 41 * 79 = 37635660909`. -/
theorem primeShift_459818240 : primeShift 459818240 = 37635660909 := by
  have h256 : primeShift 256 = 6561 := by
    have h : (256 : ℕ) = 2 ^ 8 := by norm_num
    rw [h]
    exact primeShift_of_prime_pow Nat.prime_two nextPrime_two (by norm_num)
  have h35 : primeShift 35 = 77 := by
    have h : (35 : ℕ) = 5 * 7 := by norm_num
    rw [h]
    exact primeShift_mul_eq (by norm_num) (by norm_num) primeShift_five primeShift_seven
      (by norm_num)
  have h665 : primeShift 665 = 1771 := by
    have h : (665 : ℕ) = 35 * 19 := by norm_num
    rw [h]
    exact primeShift_mul_eq (by norm_num) (by norm_num) h35 primeShift_nineteen (by norm_num)
  have h24605 : primeShift 24605 = 72611 := by
    have h : (24605 : ℕ) = 665 * 37 := by norm_num
    rw [h]
    exact primeShift_mul_eq (by norm_num) (by norm_num) h665 primeShift_thirtySeven
      (by norm_num)
  have h1796165 : primeShift 1796165 = 5736269 := by
    have h : (1796165 : ℕ) = 24605 * 73 := by norm_num
    rw [h]
    exact primeShift_mul_eq (by norm_num) (by norm_num) h24605 primeShift_seventyThree
      (by norm_num)
  have h : (459818240 : ℕ) = 256 * 1796165 := by norm_num
  rw [h]
  exact primeShift_mul_eq (by norm_num) (by norm_num) h256 h1796165 (by norm_num)

/-- `459818240` is a term of A349745 — the second term of A323653 satisfies the A003961
congruence, as Karttunen's Conjecture 4 requires: `gcd(σ, A003961) = 21`,
`gcd(k, A003961) = 7`, and `459818240 * 21 = 9656183040 = 1379454720 * 7`. -/
theorem isA349745_459818240 : IsA349745 459818240 := by
  refine ⟨by norm_num, ?_⟩
  rw [sum_divisors_459818240, primeShift_459818240]
  norm_num

/-! ## Karttunen's conjectures

Archived as `Prop`-valued definitions; all are **OPEN**.  No declaration in this file assumes
any of them except the explicitly conditional
`Nat.karttunen3_forward_of_karttunen1c`. -/

/-- **Karttunen's Conjecture 3** (OEIS A323653, comment of Antti Karttunen, Mar 20 2021 /
Feb 18 2022), verbatim: "Conjecture 3: This sequence is the intersection of A007691 and
A351458."  The same claim appears on A351458, verbatim: "It is conjectured that the
intersection of this sequence with the multiperfect numbers (A007691) gives A323653, see
comments in the latter."

**OPEN.**  Unfolding the two sides: for every `m`, `m` and `σ(m)` are both multiperfect if
and only if `m` is multiperfect and `m * gcd(σ(m), A276086(m)) = σ(m) * gcd(m, A276086(m))`.
Neither implication is known; see `Nat.karttunen3_nondegenerate` for the ground data. -/
def KarttunenConjecture3 : Prop :=
  ∀ m : ℕ, IsA323653 m ↔ (IsMultiperfect m ∧ IsA351458 m)

/-- **Karttunen's Conjecture 4** (OEIS A323653, comment of Antti Karttunen, Mar 20 2021 /
Feb 18 2022), verbatim: "Conjecture 4: This is a subsequence of A349745, thus also of
A351551 and of A351554."

**OPEN.**  Only the A349745 clause is archived here; A351551 and A351554 are not defined in
this file. -/
def KarttunenConjecture4 : Prop := ∀ m : ℕ, IsA323653 m → IsA349745 m

/-- **Karttunen's Conjecture 1(c)** (OEIS A323653, same comment block), verbatim: "In a
slightly stronger form (c): For m > 1, sigma(m)/m is always the least prime not dividing m.
This would imply both (a) and (b) forms."

Rendered without `ℕ`-division: for every term `m > 1` of A323653 there is a prime `q` such
that every prime below `q` divides `m`, `q` does not, and `σ(m) = q * m`.  **OPEN.** -/
def KarttunenConjecture1c : Prop :=
  ∀ m : ℕ, 1 < m → IsA323653 m →
    ∃ q : ℕ, q.Prime ∧ ¬ q ∣ m ∧ (∀ p < q, p.Prime → p ∣ m) ∧ ∑ d ∈ m.divisors, d = q * m

/-- Conjecture 1(c) holds at `m = 459818240`, with `q = 3`: the second term of A323653 has
abundancy `3`, and `3` is the least prime not dividing it.  This is the satisfiability
witness for the existential inside `Nat.KarttunenConjecture1c`. -/
theorem karttunen1c_at_459818240 :
    ∃ q : ℕ, q.Prime ∧ ¬ q ∣ 459818240 ∧ (∀ p < q, p.Prime → p ∣ 459818240)
      ∧ ∑ d ∈ (459818240 : ℕ).divisors, d = q * 459818240 :=
  ⟨3, by norm_num, by norm_num, by decide, by rw [sum_divisors_459818240]⟩

/-- **Reduction: Conjecture 1(c) implies the forward half of Conjecture 3.**  Assuming
1(c), every term of A323653 is multiply-perfect *and* satisfies the A276086 congruence —
i.e. `A323653 ⊆ A007691 ∩ A351458`, one of the two inclusions Conjecture 3 asserts.

The proof splits at `m = 1` (handled by `Nat.isA351458_one`) and applies the OEIS
sufficient condition `Nat.isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul` above.  The
converse inclusion `A007691 ∩ A351458 ⊆ A323653` is *not* reduced by this argument and
remains open.

This is a conditional theorem: its hypothesis is an open conjecture, so it has no
unconditional satisfiability witness.  Its *conclusion* is witnessed unconditionally at
`m = 1` and `m = 459818240` (`Nat.isA351458_one`, `Nat.isA351458_459818240`). -/
theorem karttunen3_forward_of_karttunen1c (h : KarttunenConjecture1c) (m : ℕ)
    (hm : IsA323653 m) : IsMultiperfect m ∧ IsA351458 m := by
  refine ⟨hm.1, ?_⟩
  have hpos : 0 < m := hm.1.1
  rcases Nat.lt_or_ge 1 m with hlt | hle
  · obtain ⟨q, hq, hqm, hmin, hsum⟩ := h m hlt hm
    exact isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul hq hqm hmin hsum
  · have hone : m = 1 := by omega
    rw [hone]
    exact isA351458_one

/-- Conjecture 3 is a genuine biconditional over a domain that is neither empty nor
exhausted, and the multiperfect conjunct on the right is not doing the work by itself:

* `1` and `459818240` — the two smallest terms of A323653 — satisfy both sides;
* `6` is multiperfect yet fails both sides, so the right-hand side is not implied by its
  own `IsMultiperfect` conjunct;
* `120` is multiperfect, and even lies in the A003961 analogue A349745, yet still fails
  both sides.

This is the non-vacuity certificate for `Nat.KarttunenConjecture3`. -/
theorem karttunen3_nondegenerate :
    (IsA323653 1 ∧ IsMultiperfect 1 ∧ IsA351458 1)
      ∧ (IsA323653 459818240 ∧ IsMultiperfect 459818240 ∧ IsA351458 459818240)
      ∧ (¬ IsA323653 6 ∧ IsMultiperfect 6 ∧ ¬ IsA351458 6)
      ∧ (¬ IsA323653 120 ∧ IsMultiperfect 120 ∧ ¬ IsA351458 120) :=
  ⟨⟨isA323653_one, by decide, isA351458_one⟩,
   ⟨isA323653_459818240, isMultiperfect_459818240, isA351458_459818240⟩,
   ⟨not_isA323653_six, by decide, not_isA351458_six⟩,
   ⟨not_isA323653_onetwenty, by decide, not_isA351458_onetwenty⟩⟩

/-- Conjecture 4 asserts a containment that is strict on the recorded data — `120` lies in
A349745 but not in A323653 — so it is not an equality of sequences in disguise, and its
conclusion is not vacuously satisfiable by an empty hypothesis: `1` and `459818240` witness
both sides.

This is the non-vacuity certificate for `Nat.KarttunenConjecture4`. -/
theorem karttunen4_nondegenerate :
    (IsA323653 1 ∧ IsA349745 1)
      ∧ (IsA323653 459818240 ∧ IsA349745 459818240)
      ∧ (IsA349745 120 ∧ ¬ IsA323653 120) :=
  ⟨⟨isA323653_one, isA349745_one⟩,
   ⟨isA323653_459818240, isA349745_459818240⟩,
   ⟨isA349745_onetwenty, not_isA323653_onetwenty⟩⟩

end Nat

/-! ## Axiom audit -/

-- A276086 layer.
#print axioms Nat.primorialRest
#print axioms Nat.primorialDigit
#print axioms Nat.primorialBaseExp
#print axioms Nat.primorialRest_eq_div_prod
#print axioms Nat.primorialRest_lt
#print axioms Nat.primorialRest_eq_zero_of_lt
#print axioms Nat.primorialDigit_eq_zero_of_lt
#print axioms Nat.primorialBaseExp_eq_prod_range
#print axioms Nat.primorialBaseExp_pos
#print axioms Nat.prod_nth_prime_dvd
#print axioms Nat.prime_dvd_primorialBaseExp

-- A003961 layer.
#print axioms Nat.nextPrime
#print axioms Nat.prime_nextPrime
#print axioms Nat.lt_nextPrime
#print axioms Nat.nextPrime_le
#print axioms Nat.nextPrime_nth_prime
#print axioms Nat.primeShift
#print axioms Nat.primeShift_prime_pow
#print axioms Nat.primeShift_mul
#print axioms Nat.primeShift_nth_prime
#print axioms Nat.primeShift_pos

-- Predicates and the sufficient condition.
#print axioms Nat.IsA351458
#print axioms Nat.IsA349745
#print axioms Nat.IsA323653
#print axioms Nat.congruence_holds_vacuously_at_zero
#print axioms Nat.gcd_mul_of_prime_not_dvd
#print axioms Nat.isA351458_of_sum_divisors_eq_least_prime_not_dvd_mul

-- The second term of A323653.
#print axioms Nat.sum_divisors_459818240
#print axioms Nat.sum_divisors_1379454720
#print axioms Nat.isMultiperfect_459818240
#print axioms Nat.isA323653_459818240
#print axioms Nat.isA351458_459818240
#print axioms Nat.primeShift_459818240
#print axioms Nat.isA349745_459818240

-- Archived conjectures and the reduction.
#print axioms Nat.KarttunenConjecture3
#print axioms Nat.KarttunenConjecture4
#print axioms Nat.KarttunenConjecture1c
#print axioms Nat.karttunen1c_at_459818240
#print axioms Nat.karttunen3_forward_of_karttunen1c
#print axioms Nat.karttunen3_nondegenerate
#print axioms Nat.karttunen4_nondegenerate
