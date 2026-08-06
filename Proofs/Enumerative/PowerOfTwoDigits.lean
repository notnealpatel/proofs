import Erdos.Erdos175.KummerDigits
import Enumerative.StanleyDigits
import Mathlib.Order.Filter.Cofinite

/-!
# Erdős #406: powers of `2` with only the digits `0` and `1` in base `3`

## Source, pinned verbatim

Pulled with `goof erdos fetch 406` on **2026-08-05**.

`number` (verbatim): `406`

`statement` (verbatim, the whole field):

> Is it true that there are only finitely many powers of $2$ which have only the digits
> $0$ and $1$ when written in base $3$?

`sections[0]` (verbatim, the whole field; the blank lines are the field's own):

> The only examples seem to be $1$, $4=1+3$, and $256=1+3+3^2+3^5$. If we only allow the
> digits $1$ and $2$ then $2^{15}$ seems to be the largest such power of $2$.
>
> This would imply via Kummer's theorem that\[3\mid \binom{2^{k+1}}{2^k}\]for all large $k$.
>
> Saye \cite{Sa22} has computed that $2^n$ contains every possible ternary digit for
> $16\leq n \leq 5.9\times 10^{21}$.
>
> Let $N(x)$ count the number of $n\leq x$ such that $2^n$ has only the digits $0$ and $1$
> in base $3$. Narkiewicz \cite{Na80} proved\[N(x)\leq 1.62 x^{\log_32}\]This is mentioned
> in problem B33 of Guy's collection \cite{Gu04}. There are many generalisations possible -
> see, for example, \cite{AbLa14} and \cite{La09}.

`sections[1]`, the four references, verbatim:

> [AbLa14] Abram, William C. and Lagarias, Jeffrey C., *Intersections of multiplicative
> translates of 3-adic {C}antor sets*. J. Fractal Geom. (2014), 349--390.
>
> [Gu04] Guy, Richard K., *Unsolved problems in number theory*.  (2004), xviii+437.
>
> [La09] Lagarias, Jeffrey C., *Ternary expansions of powers of 2*. J. Lond. Math. Soc. (2)
> (2009), 562--588.
>
> [Na80] Narkiewicz, W., *A note on a paper of {H}. {G}upta concerning powers of two and
> three: ``{P}owers of {$2$}\ and sums of distinct powers of {$3$}''\ [{U}niv. {B}eograd.
> {P}ubl. {E}lektrotehn. {F}ak. Ser. {M}at. {F}iz. {N}o. 602-633 (1978), 151--158 (1979);\
> {MR} 81g:10016]*. Univ. Beograd. Publ. Elektrotehn. Fak. Ser. Mat. Fiz. (1980), 173--174.
>
> [Sa22] Saye, Robert I., *On two conjectures concerning the ternary digits of powers of
> two*. J. Integer Seq. (2022), Art. 22.3.4, 9.

### OEIS cross-references, pinned verbatim

`goof oeis show A351928` (pulled 2026-08-05) — the sequence named in the DB comment
thread — its `name` and both `comments`:

> Smallest positive integer k such that 2^k has no '2' in the last n digits of its ternary
> expansion.

> The powers of two are required to have at least n ternary digits, i.e., 2^k >= 3^(n-1).

> Erdős (~1978) conjectured that 1, 4, and 256 are the only powers of two whose ternary
> expansion consists solely of 0's and 1's.

`goof oeis show A005836`, its `name` and `comments[0]` — this is the ambient set, and the
comment is exactly the Kummer bridge formalised in §4 below:

> Numbers whose base-3 representation contains no 2.

> 3 does not divide binomial(2s, s) if and only if s is a member of this sequence, where
> binomial(2s, s) = A000984(s) are the central binomial coefficients.

## ⚠ Discrepancy with the dispatching brief — READ THIS FIRST

The brief said:

> Three known witnesses (n = 0, 1, 2 give 1, 2, 11 in base 3 — all digits ≤ 1).

**That is wrong, and this file follows the primary source instead.** The three witnesses
are the *values* `1`, `4`, `256`, i.e. the exponents `n = 0, 2, 8` — not `n = 0, 1, 2`.
The brief appears to have read the base-3 *string* `11` (which is `4 = 2 ^ 2`) as an
exponent, and to have listed `2 ^ 1 = 2` as a witness. It is not: `2` in base `3` is the
single digit `2`, which is `> 1`. Four independent checks:

* the pinned `sections[0]`: "The only examples seem to be $1$, $4=1+3$, and
  $256=1+3+3^2+3^5$" — values, and `1 = 2 ^ 0`, `4 = 2 ^ 2`, `256 = 2 ^ 8`;
* the pinned A351928 comment: "1, 4, and 256 are the only powers of two whose ternary
  expansion consists solely of 0's and 1's";
* `Proofs/Scratch/ErdosCandidates/E406.lean`, the previously audited sketch for this
  target, which already records `n = 0, 2, 8` and explicitly lists `2 ^ 1 = 2 = (2)₃` as a
  *non*-example;
* the kernel, here: `witness_two_pow_two`/`witness_two_pow_eight` and
  `not_base3ZeroOne_two_pow_one` below.

Had the brief been followed literally, `witness` at `n = 1` would have been a false
statement and would not have compiled.

## What is archived and what is proved

There is **no `sorry` in this file**. The open problem is carried as a `Prop`-valued
definition, `Conjecture`, not as a `sorry`-ed theorem, so that nothing downstream can
accidentally consume it as proved.

Archived, unproved, and unprovable-by-any-known-method:

* `Conjecture` — "only finitely many `n` have `2 ^ n` with all base-`3` digits in `{0, 1}`",
  i.e. the pinned `statement`. **Status: open.**

Proved here, `sorry`-free and kernel-checked:

* `base3ZeroOne_iff_not_dvd_centralBinom` — the Kummer bridge, i.e. A005836's
  `comments[0]`: all base-`3` digits of `m` are `≤ 1` iff `3 ∤ C(2m, m)`. Obtained from
  `Erdos175.prime_not_dvd_centralBinom_iff_digits` (the #376 layer) at `p = 3`.
* `erdos406_iff_eventually_three_dvd` — **the DB's "would imply", upgraded to an
  equivalence.** The source says the conjecture "would imply via Kummer's theorem that
  `3 ∣ C(2^{k+1}, 2^k)` for all large `k`"; in fact the two statements are *equivalent*,
  because the exceptional set of the divisibility is literally the set the conjecture is
  about. `erdos406_imp_eventually_three_dvd` records the source's implication direction on
  its own.
* `erdos406_iff_finite_gupta` — the same conjecture in the shape named by the [Na80] title
  ("powers of `2` and sums of distinct powers of `3`"), via `binToTernary` from
  `Enumerative.StanleyDigits`.
* `erdos406_iff_exists_bound` — the conjecture as "there is a last one".
* **The unconditional residue sieve** (§6), which is the mathematical content of this file:
  `base3ZeroOne_mod_pow` (all digits `≤ 1` passes to the low `j` digits) plus
  `two_pow_mod_eq_of_pow_mod_one` (periodicity of `2 ^ n` mod `M`) reduce membership at
  depth `j` to a *decidable* check on `n % ord`, giving
  `mod_six_of_base3ZeroOne_two_pow` (`n ≡ 0, 2 mod 6`),
  `mod_eighteen_of_base3ZeroOne_two_pow` (`n ≡ 0, 2, 6, 8 mod 18`), and
  `mod_fiftyFour_of_base3ZeroOne_two_pow` (`8` classes mod `54`). Consequences:
  `even_of_base3ZeroOne_two_pow`, `not_base3ZeroOne_two_pow_of_odd`, and — through the
  Kummer bridge — `three_dvd_centralBinom_two_pow_of_odd`, i.e. **`3 ∣ C(2^{k+1}, 2^k)`
  for every odd `k`, unconditionally**: an infinite explicit family on which the source's
  conjectured consequence provably holds.
* `infinite_setOf_not_base3ZeroOne_two_pow` — the complement is infinite. This is the
  non-degeneracy check that matters: `Conjecture` is not "some obviously cofinite set is
  finite".
* `mem_erdos406Set_iff_of_le` — ground truth to `n ≤ 1000`: `2 ^ n` has all base-`3`
  digits `≤ 1` **iff** `n ∈ {0, 2, 8}`. Kernel-checked by `decide`, no `native_decide`.
* `three_dvd_centralBinom_two_pow_of_le` — the unconditional divisibility on that same
  window, `9 ≤ k ≤ 1000`.
* `mem_oneTwoSet_iff_of_le` — the source's second sentence ("If we only allow the digits
  $1$ and $2$ then $2^{15}$ seems to be the largest such power of $2$"), checked to
  `n ≤ 1000`: all base-`3` digits of `2 ^ n` are `≥ 1` iff `n ≤ 4` or `n = 15`. In
  particular `2 ^ 15` is the largest one in that window, as the source says.

## Why the sieve cannot close the problem (honest claim boundary)

Nothing here is progress on Erdős #406. The sieve of §6 is elementary and provably
non-terminating: at depth `j` the modulus is `3 ^ j`, the period of `2` mod `3 ^ j` is
`2 · 3 ^ (j-1)`, and the number of surviving residues is exactly `2 ^ j`, so the surviving
density is `(2/3) ^ (j-1) > 0` for every `j`. (Computed for `j ≤ 8` in the orientation run
below; `j ≤ 4` is the part re-verified in the kernel here.) That positive-density-at-every-
depth behaviour is precisely why the best known bound is a *counting* bound,
Narkiewicz's `N(x) ≤ 1.62 x^{log_3 2}` — note `log_3 2 = 0.6309…` is the exponent that the
`2 ^ j`-out-of-`2 · 3 ^ (j-1)` count produces. Narkiewicz's bound itself is **not**
formalised here; nor is Saye's `16 ≤ n ≤ 5.9 × 10^21` verification, of which this file
re-verifies `n ≤ 1000` from scratch.

## Mathlib gaps

* Mathlib has no carry function for Kummer's theorem; that gap is closed by
  `Proofs/Erdos/Erdos175/KummerDigits.lean` (see its own scope note), which this file
  imports rather than restates.
* Mathlib has no natural-density notion suitable for stating Narkiewicz's bound
  faithfully, which is the other reason it is only pinned and not stated.

## Computational orientation (not proofs)

`command -v sage` is empty on this machine, so no `sage` was used and none is claimed. A
plain `python3` script (no external libraries) computed the ternary digits of `2 ^ n` for
`n ≤ 2000` and found the `{0,1}`-digit exponents to be exactly `{0, 2, 8}` and the
`{1,2}`-digit exponents to be exactly `{0, 1, 2, 3, 4, 15}`, and computed the sieve
survivor counts `1, 2, 4, 8, 16, 32, 64, 128` at depths `j = 1 … 8` against periods
`2, 6, 18, 54, 162, 486, 1458, 4374`. All of that is orientation; every claim below is
re-verified in the kernel.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2000

namespace Erdos406

/-! ## §1 The digit predicate -/

/-- `Base3ZeroOne m`: every base-`3` digit of `m` is `0` or `1`.

This is the membership condition of OEIS A005836 ("Numbers whose base-3 representation
contains no 2"), spelled `d ≤ 1` rather than `d ≠ 2`; `base3ZeroOne_iff_eq` and
`digits_lt_three` below confirm the two readings agree. -/
def Base3ZeroOne (m : ℕ) : Prop := ∀ d ∈ Nat.digits 3 m, d ≤ 1

instance (m : ℕ) : Decidable (Base3ZeroOne m) := by
  unfold Base3ZeroOne; infer_instance

/-- Base-`3` digits are `< 3`. -/
theorem digits_lt_three {m d : ℕ} (hd : d ∈ Nat.digits 3 m) : d < 3 :=
  Nat.digits_lt_base (by norm_num) hd

/-- `Base3ZeroOne` really is "digits in `{0, 1}`", and equivalently "no digit `2`". -/
theorem base3ZeroOne_iff_eq (m : ℕ) :
    Base3ZeroOne m ↔ ∀ d ∈ Nat.digits 3 m, d = 0 ∨ d = 1 := by
  refine ⟨fun h d hd => by have := h d hd; omega, fun h d hd => by have := h d hd; omega⟩

/-- `Base3ZeroOne` is equivalently "`2` is not a base-`3` digit". -/
theorem base3ZeroOne_iff_two_not_mem (m : ℕ) :
    Base3ZeroOne m ↔ 2 ∉ Nat.digits 3 m := by
  constructor
  · intro h hmem
    have := h 2 hmem
    omega
  · intro h d hd
    have hlt := digits_lt_three hd
    by_contra hcon
    have hd2 : d = 2 := by omega
    exact h (hd2 ▸ hd)

/-- **Non-vacuity of the `∀ d ∈ …`.** For `0 < m` the base-`3` digit list is nonempty, so
`Base3ZeroOne m` is a constraint and not an empty quantification. (At `m = 0` it *is*
vacuous — `Nat.digits 3 0 = []` — which is harmless here because every value this file
applies it to is a power of `2`, hence positive; see `digits_two_pow_ne_nil`.) -/
theorem digits_ne_nil_of_pos {m : ℕ} (hm : 0 < m) : Nat.digits 3 m ≠ [] :=
  Nat.digits_ne_nil_iff_ne_zero.mpr hm.ne'

/-- The values this file constrains have nonempty digit lists. -/
theorem digits_two_pow_ne_nil (n : ℕ) : Nat.digits 3 (2 ^ n) ≠ [] :=
  digits_ne_nil_of_pos (Nat.two_pow_pos n)

/-- The degenerate case, recorded explicitly so it cannot be mistaken for content. -/
theorem base3ZeroOne_zero : Base3ZeroOne 0 := by decide

/-- **The indexed form**, via the `#376` bridge
`Erdos175.forall_div_pow_mod_iff_forall_mem_digits`: instead of list membership, quantify
over digit positions. Index `i` beyond the length of the digit list contributes the digit
`0`, which satisfies `0 ≤ 1`, so the two forms agree with no side condition. This is the
form the sieve of §6 runs on. -/
theorem base3ZeroOne_iff_forall_index (m : ℕ) :
    Base3ZeroOne m ↔ ∀ i, m / 3 ^ i % 3 ≤ 1 :=
  (Erdos175.forall_div_pow_mod_iff_forall_mem_digits (b := 3) (by norm_num) m
    (fun d => d ≤ 1) (by norm_num)).symm

/-! ## §2 The three witnesses of the source

The source's `sections[0]` names the *values* `1`, `4 = 1+3`, `256 = 1+3+3²+3⁵`. Their
exponents are `0`, `2`, `8`. Both the values and the source's own decompositions are
checked below. -/

/-- The source's arithmetic, verbatim: `4 = 1 + 3` and `256 = 1 + 3 + 3^2 + 3^5`. -/
theorem source_decompositions :
    (2 : ℕ) ^ 2 = 1 + 3 ∧ (2 : ℕ) ^ 8 = 1 + 3 + 3 ^ 2 + 3 ^ 5 := by decide

/-- Ground truth for `Nat.digits` at the three witnesses (little-endian):
`1 = (1)₃`, `4 = (11)₃`, `256 = (100111)₃`. -/
theorem digits_witnesses :
    Nat.digits 3 (2 ^ 0) = [1] ∧ Nat.digits 3 (2 ^ 2) = [1, 1] ∧
      Nat.digits 3 (2 ^ 8) = [1, 1, 1, 0, 0, 1] := by decide

/-- Witness `2 ^ 0 = 1`. -/
theorem witness_two_pow_zero : Base3ZeroOne (2 ^ 0) := by decide

/-- Witness `2 ^ 2 = 4 = (11)₃`. -/
theorem witness_two_pow_two : Base3ZeroOne (2 ^ 2) := by decide

/-- Witness `2 ^ 8 = 256 = (100111)₃`. -/
theorem witness_two_pow_eight : Base3ZeroOne (2 ^ 8) := by decide

/-- **Non-witness, and the refutation of the dispatching brief's claim**: `2 ^ 1 = 2` is
the single base-`3` digit `2`, so it is *not* a witness. -/
theorem not_base3ZeroOne_two_pow_one : ¬ Base3ZeroOne (2 ^ 1) := by decide

/-- Non-witness: `2 ^ 4 = 16 = (121)₃`. -/
theorem not_base3ZeroOne_two_pow_four : ¬ Base3ZeroOne (2 ^ 4) := by decide

/-! ## §3 The archived conjecture -/

/-- The set of exponents in question: `{n : 2 ^ n has all base-3 digits in {0, 1}}`. -/
def erdos406Set : Set ℕ := {n : ℕ | Base3ZeroOne (2 ^ n)}

/-- Membership in `erdos406Set` unfolds to the digit condition. -/
theorem mem_erdos406Set_iff (n : ℕ) : n ∈ erdos406Set ↔ Base3ZeroOne (2 ^ n) := Iff.rfl

/-- **Erdős #406 (OPEN).** Verbatim `statement`: "Is it true that there are only finitely
many powers of $2$ which have only the digits $0$ and $1$ when written in base $3$?"

Carried as a `Prop`, not as a `sorry`-ed theorem. Conjecturally `erdos406Set = {0, 2, 8}`;
`mem_erdos406Set_iff_of_le` verifies that for `n ≤ 1000` and Saye [Sa22] verifies the
disjointness from `[16, 5.9 × 10^21]`. No proof method is known. -/
def Conjecture : Prop := erdos406Set.Finite

/-- **Non-degeneracy, positive side.** `erdos406Set` is not empty — so `Conjecture` is not
the triviality "`∅` is finite", and if it holds the set it bounds has content. -/
theorem erdos406Set_nonempty : erdos406Set.Nonempty :=
  ⟨0, witness_two_pow_zero⟩

/-- `0`, `2` and `8` all lie in `erdos406Set`. -/
theorem witnesses_mem_erdos406Set :
    0 ∈ erdos406Set ∧ 2 ∈ erdos406Set ∧ 8 ∈ erdos406Set :=
  ⟨witness_two_pow_zero, witness_two_pow_two, witness_two_pow_eight⟩

/-- **The conjecture as "there is a last one".** For a set of naturals, finiteness is
boundedness; this is the form in which the conjecture is usually stated informally. -/
theorem erdos406_iff_exists_bound :
    Conjecture ↔ ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ Base3ZeroOne (2 ^ n) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := h.bddAbove
    refine ⟨N, fun n hn hb => ?_⟩
    have hle : n ≤ N := hN hb
    omega
  · rintro ⟨N, hN⟩
    refine Set.Finite.subset (Set.finite_Icc 0 N) fun n hn => ?_
    refine Set.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
    by_contra hc
    exact hN n (by omega) hn

/-! ## §4 The Kummer bridge, and the source's stated consequence

A005836's `comments[0]`, verbatim: "3 does not divide binomial(2s, s) if and only if s is
a member of this sequence". That is `Erdos175.prime_not_dvd_centralBinom_iff_digits` at
`p = 3`, where the digit bound `2 * d < p` becomes `d ≤ 1`. -/

/-- **The Kummer bridge at `p = 3`.** All base-`3` digits of `m` are `≤ 1` iff `3` does not
divide the central binomial coefficient `C(2m, m)`.

This is A005836's `comments[0]`, specialised from the `#376` layer
`Erdos175.prime_not_dvd_centralBinom_iff_digits` (proved there from Kummer's theorem, not
from Lucas's). -/
theorem base3ZeroOne_iff_not_dvd_centralBinom (m : ℕ) :
    Base3ZeroOne m ↔ ¬ (3 ∣ Nat.centralBinom m) := by
  rw [Erdos175.prime_not_dvd_centralBinom_iff_digits Nat.prime_three]
  refine ⟨fun h d hd => by have := h d hd; omega, fun h d hd => by have := h d hd; omega⟩

/-- The source writes the central binomial coefficient at a power of `2` as
`\binom{2^{k+1}}{2^k}`; that is `Nat.centralBinom (2 ^ k)`. -/
theorem centralBinom_two_pow (k : ℕ) :
    Nat.centralBinom (2 ^ k) = (2 ^ (k + 1)).choose (2 ^ k) := by
  rw [Nat.centralBinom_eq_two_mul_choose, pow_succ']

/-- Pointwise form: `3 ∣ C(2^{k+1}, 2^k)` exactly when `k` is *not* in `erdos406Set`. -/
theorem three_dvd_centralBinom_two_pow_iff (k : ℕ) :
    3 ∣ (2 ^ (k + 1)).choose (2 ^ k) ↔ k ∉ erdos406Set := by
  rw [mem_erdos406Set_iff, base3ZeroOne_iff_not_dvd_centralBinom, centralBinom_two_pow,
    not_not]

/-- **The source's consequence, upgraded to an equivalence.**

`sections[0]` says: "This would imply via Kummer's theorem that
`\[3\mid \binom{2^{k+1}}{2^k}\]` for all large $k$." In fact the implication is reversible:
the set of `k` at which the divisibility *fails* is, by the Kummer bridge, exactly
`erdos406Set`, so "finitely many exceptions" and "cofinitely many successes" are the same
statement. -/
theorem erdos406_iff_eventually_three_dvd :
    Conjecture ↔ ∀ᶠ k in Filter.atTop, 3 ∣ (2 ^ (k + 1)).choose (2 ^ k) := by
  have hset : {k : ℕ | ¬ (3 ∣ (2 ^ (k + 1)).choose (2 ^ k))} = erdos406Set := by
    ext k
    show ¬ (3 ∣ (2 ^ (k + 1)).choose (2 ^ k)) ↔ k ∈ erdos406Set
    rw [three_dvd_centralBinom_two_pow_iff, not_not]
  rw [Conjecture, ← Nat.cofinite_eq_atTop, Filter.eventually_cofinite, hset]

/-- The source's implication direction on its own, in the source's own words: the
conjecture implies `3 ∣ C(2^{k+1}, 2^k)` for all large `k`. -/
theorem erdos406_imp_eventually_three_dvd (h : Conjecture) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 3 ∣ (2 ^ (k + 1)).choose (2 ^ k) := by
  obtain ⟨N, hN⟩ := erdos406_iff_exists_bound.mp h
  exact ⟨N + 1, fun k hk => (three_dvd_centralBinom_two_pow_iff k).mpr (hN k (by omega))⟩

/-! ## §5 The Gupta form: sums of distinct powers of `3`

The [Na80] reference title is "*Powers of $2$ and sums of distinct powers of $3$*". A
natural has all base-`3` digits in `{0, 1}` exactly when it is a sum of distinct powers of
`3`, i.e. exactly when it is a value of `binToTernary` (read a binary expansion in base
`3`), which is `Enumerative.StanleyDigits`'s enumeration of A005836. -/

/-- All base-`3` digits of `m` are `≤ 1` iff `m` is a sum of distinct powers of `3`, in the
form "`m` is a binary expansion read in base `3`". This is
`Enumerative.StanleyDigits.mem_range_binToTernary`, restated for `Base3ZeroOne`. -/
theorem base3ZeroOne_iff_mem_range_binToTernary (m : ℕ) :
    Base3ZeroOne m ↔ m ∈ Set.range binToTernary :=
  mem_range_binToTernary.symm

/-- **Gupta's formulation of the conjecture**, matching the [Na80] title: only finitely
many powers of `2` are sums of distinct powers of `3`. -/
theorem erdos406_iff_finite_gupta :
    Conjecture ↔ {n : ℕ | ∃ j : ℕ, binToTernary j = 2 ^ n}.Finite := by
  have hset : erdos406Set = {n : ℕ | ∃ j : ℕ, binToTernary j = 2 ^ n} := by
    ext n
    show Base3ZeroOne (2 ^ n) ↔ ∃ j : ℕ, binToTernary j = 2 ^ n
    exact (base3ZeroOne_iff_mem_range_binToTernary (2 ^ n)).trans Set.mem_range
  rw [Conjecture, hset]

/-! ## §6 The unconditional residue sieve

If all base-`3` digits of `m` are `≤ 1` then so are those of `m % 3 ^ j` (the low `j`
digits). And `2 ^ n % M` depends only on `n % d` whenever `2 ^ d ≡ 1 (mod M)`. Together
these turn "`n ∈ erdos406Set`" at depth `j` into a *finite decidable* constraint on
`n % d`. -/

/-- `2 ^ n % M` is periodic in `n` with period `d`, whenever `2 ^ d ≡ 1 (mod M)`. -/
theorem two_pow_mod_eq_of_pow_mod_one {M d : ℕ} (hd : 2 ^ d % M = 1 % M) (n : ℕ) :
    2 ^ n % M = 2 ^ (n % d) % M := by
  conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hd, ← Nat.pow_mod, one_pow, ← Nat.mul_mod, one_mul]

/-- The `i`-th base-`3` digit of `m` reads off `m % 3 ^ (i+1)`. -/
theorem div_pow_mod_eq_mod_pow_div (m i : ℕ) :
    m / 3 ^ i % 3 = m % 3 ^ (i + 1) / 3 ^ i := by
  rw [pow_succ, Nat.mod_mul_right_div_self]

/-- **Truncation.** If every base-`3` digit of `m` is `≤ 1`, the same holds of the number
formed by its low `j` digits. -/
theorem base3ZeroOne_mod_pow {m : ℕ} (h : Base3ZeroOne m) (j : ℕ) :
    Base3ZeroOne (m % 3 ^ j) := by
  rw [base3ZeroOne_iff_forall_index] at h ⊢
  intro i
  rcases lt_or_ge i j with hij | hij
  · have hdvd : (3 : ℕ) ^ (i + 1) ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
    rw [div_pow_mod_eq_mod_pow_div, Nat.mod_mod_of_dvd _ hdvd, ← div_pow_mod_eq_mod_pow_div]
    exact h i
  · have hlt : m % 3 ^ j < 3 ^ i :=
      lt_of_lt_of_le (Nat.mod_lt _ (pow_pos (by norm_num) j))
        (Nat.pow_le_pow_right (by norm_num) hij)
    rw [Nat.div_eq_of_lt hlt]
    norm_num

/-- **The sieve step.** With `2 ^ d ≡ 1 (mod 3 ^ j)`, membership of `n` in `erdos406Set`
forces a condition on `n % d` alone — a finite, decidable constraint. -/
theorem base3ZeroOne_two_pow_mod_pow {n j d : ℕ} (hd : 2 ^ d % 3 ^ j = 1 % 3 ^ j)
    (h : Base3ZeroOne (2 ^ n)) : Base3ZeroOne (2 ^ (n % d) % 3 ^ j) := by
  rw [← two_pow_mod_eq_of_pow_mod_one hd]
  exact base3ZeroOne_mod_pow h j

/-- **Sieve at depth 2** (`3 ^ 2 = 9`, period `6`): `n ≡ 0` or `2 (mod 6)`.

`2 ^ n mod 9` cycles `1, 2, 4, 8, 7, 5`; of these only `1 = (01)₃` and `4 = (11)₃` have
both low digits `≤ 1`. -/
theorem mod_six_of_base3ZeroOne_two_pow {n : ℕ} (h : Base3ZeroOne (2 ^ n)) :
    n % 6 = 0 ∨ n % 6 = 2 := by
  have key : Base3ZeroOne (2 ^ (n % 6) % 3 ^ 2) :=
    base3ZeroOne_two_pow_mod_pow (by norm_num) h
  have hcheck : ∀ r < 6, Base3ZeroOne (2 ^ r % 3 ^ 2) → r = 0 ∨ r = 2 := by decide
  exact hcheck _ (Nat.mod_lt _ (by norm_num)) key

/-- **Sieve at depth 3** (`3 ^ 3 = 27`, period `18`): `n ≡ 0, 2, 6` or `8 (mod 18)`. -/
theorem mod_eighteen_of_base3ZeroOne_two_pow {n : ℕ} (h : Base3ZeroOne (2 ^ n)) :
    n % 18 = 0 ∨ n % 18 = 2 ∨ n % 18 = 6 ∨ n % 18 = 8 := by
  have key : Base3ZeroOne (2 ^ (n % 18) % 3 ^ 3) :=
    base3ZeroOne_two_pow_mod_pow (by norm_num) h
  have hcheck : ∀ r < 18, Base3ZeroOne (2 ^ r % 3 ^ 3) →
      r = 0 ∨ r = 2 ∨ r = 6 ∨ r = 8 := by decide
  exact hcheck _ (Nat.mod_lt _ (by norm_num)) key

/-- **Sieve at depth 4** (`3 ^ 4 = 81`, period `54`): `8` surviving classes mod `54`.

The survivor count doubles (`1, 2, 4, 8` at depths `1, 2, 3, 4`) while the period triples
(`2, 6, 18, 54`), so the surviving density is `(2/3) ^ (j-1)` — positive at every depth.
This is why the sieve cannot settle the problem; see the module docstring. -/
theorem mod_fiftyFour_of_base3ZeroOne_two_pow {n : ℕ} (h : Base3ZeroOne (2 ^ n)) :
    n % 54 = 0 ∨ n % 54 = 2 ∨ n % 54 = 8 ∨ n % 54 = 18 ∨ n % 54 = 20 ∨
      n % 54 = 24 ∨ n % 54 = 26 ∨ n % 54 = 42 := by
  have key : Base3ZeroOne (2 ^ (n % 54) % 3 ^ 4) :=
    base3ZeroOne_two_pow_mod_pow (by norm_num) h
  have hcheck : ∀ r < 54, Base3ZeroOne (2 ^ r % 3 ^ 4) →
      r = 0 ∨ r = 2 ∨ r = 8 ∨ r = 18 ∨ r = 20 ∨ r = 24 ∨ r = 26 ∨ r = 42 := by decide
  exact hcheck _ (Nat.mod_lt _ (by norm_num)) key

/-- Every element of `erdos406Set` is even. (Depth-1 sieve: for odd `n`, `2 ^ n ≡ 2
(mod 3)`, so the units base-`3` digit of `2 ^ n` is `2`.) -/
theorem even_of_base3ZeroOne_two_pow {n : ℕ} (h : Base3ZeroOne (2 ^ n)) : Even n := by
  rcases mod_six_of_base3ZeroOne_two_pow h with h6 | h6 <;>
    exact ⟨n / 2, by omega⟩

/-- **Unconditional: no odd exponent works.** -/
theorem not_base3ZeroOne_two_pow_of_odd {n : ℕ} (hn : Odd n) : ¬ Base3ZeroOne (2 ^ n) :=
  fun h => (Nat.not_odd_iff_even.mpr (even_of_base3ZeroOne_two_pow h)) hn

/-- **Non-degeneracy, negative side.** The complement of `erdos406Set` is infinite — it
contains every odd number. So `Conjecture` is not a statement about a set already known to be
cofinite, and the pointwise failure it asserts is realised infinitely often. -/
theorem infinite_setOf_not_base3ZeroOne_two_pow :
    {n : ℕ | ¬ Base3ZeroOne (2 ^ n)}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * k + 1)
    (fun a b hab => by dsimp only at hab; omega)
    (fun k => not_base3ZeroOne_two_pow_of_odd ⟨k, by ring⟩)

/-- **The source's consequence, proved unconditionally on an infinite explicit family.**

The source conjectures `3 ∣ C(2^{k+1}, 2^k)` for all large `k`. For *odd* `k` this is a
theorem, with no conjecture assumed: `k` odd puts a `2` in the units base-`3` digit of
`2 ^ k`, and Kummer converts that into the divisibility. -/
theorem three_dvd_centralBinom_two_pow_of_odd {k : ℕ} (hk : Odd k) :
    3 ∣ (2 ^ (k + 1)).choose (2 ^ k) :=
  (three_dvd_centralBinom_two_pow_iff k).mpr (not_base3ZeroOne_two_pow_of_odd hk)

/-- The same, for every `k` outside the four classes mod `18` that survive depth 3. -/
theorem three_dvd_centralBinom_two_pow_of_mod_eighteen {k : ℕ}
    (hk : k % 18 ≠ 0 ∧ k % 18 ≠ 2 ∧ k % 18 ≠ 6 ∧ k % 18 ≠ 8) :
    3 ∣ (2 ^ (k + 1)).choose (2 ^ k) := by
  refine (three_dvd_centralBinom_two_pow_iff k).mpr fun hmem => ?_
  rcases mod_eighteen_of_base3ZeroOne_two_pow hmem with h | h | h | h <;> omega

/-! ## §7 The verified window

Saye [Sa22] reports `16 ≤ n ≤ 5.9 × 10^21`. That range is far outside kernel reach; this
section re-verifies `n ≤ 1000` from scratch by `decide` (no `native_decide`, so the
computation is checked by the kernel and adds nothing to the trusted base). -/

set_option maxRecDepth 400000 in
/-- **Ground truth to `n ≤ 1000`:** `2 ^ n` has all base-`3` digits `≤ 1` **iff**
`n ∈ {0, 2, 8}`. This simultaneously re-derives the three witnesses of the source and
verifies there are no others below `1001`. -/
theorem mem_erdos406Set_iff_of_le :
    ∀ n ∈ Finset.range 1001, (Base3ZeroOne (2 ^ n) ↔ n = 0 ∨ n = 2 ∨ n = 8) := by decide

set_option maxRecDepth 400000 in
/-- The window in the form the source's "only examples" sentence takes. -/
theorem not_base3ZeroOne_two_pow_of_mem_Icc :
    ∀ n ∈ Finset.Icc 9 1000, ¬ Base3ZeroOne (2 ^ n) := by decide

/-- **Unconditional divisibility on the window**, via the Kummer bridge: the source's
conjectured `3 ∣ C(2^{k+1}, 2^k)` holds for every `9 ≤ k ≤ 1000`. -/
theorem three_dvd_centralBinom_two_pow_of_le {k : ℕ} (hk1 : 9 ≤ k) (hk2 : k ≤ 1000) :
    3 ∣ (2 ^ (k + 1)).choose (2 ^ k) :=
  (three_dvd_centralBinom_two_pow_iff k).mpr
    (not_base3ZeroOne_two_pow_of_mem_Icc k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩))

/-! ## §8 The `{1, 2}` variant of the source

`sections[0]`, second sentence: "If we only allow the digits $1$ and $2$ then $2^{15}$
seems to be the largest such power of $2$." -/

/-- `Base3OneTwo m`: every base-`3` digit of `m` is `1` or `2`, spelled `1 ≤ d` (the upper
bound `d < 3` is automatic — `digits_lt_three`). -/
def Base3OneTwo (m : ℕ) : Prop := ∀ d ∈ Nat.digits 3 m, 1 ≤ d

instance (m : ℕ) : Decidable (Base3OneTwo m) := by
  unfold Base3OneTwo; infer_instance

/-- `Base3OneTwo` really is "digits in `{1, 2}`". -/
theorem base3OneTwo_iff_eq (m : ℕ) :
    Base3OneTwo m ↔ ∀ d ∈ Nat.digits 3 m, d = 1 ∨ d = 2 := by
  refine ⟨fun h d hd => ?_, fun h d hd => by have := h d hd; omega⟩
  have h1 := h d hd
  have h2 := digits_lt_three hd
  omega

/-- Ground truth: `2 ^ 15 = 32768 = (1122221122)₃` little-endian
`[2, 2, 1, 1, 2, 2, 2, 2, 1, 1]`, all digits in `{1, 2}`. -/
theorem digits_two_pow_fifteen :
    Nat.digits 3 (2 ^ 15) = [2, 2, 1, 1, 2, 2, 2, 2, 1, 1] := by decide

/-- The source's `{1,2}` witness: `2 ^ 15`. -/
theorem base3OneTwo_two_pow_fifteen : Base3OneTwo (2 ^ 15) := by decide

set_option maxRecDepth 400000 in
/-- **Ground truth to `n ≤ 1000` for the `{1,2}` variant:** all base-`3` digits of `2 ^ n`
are `≥ 1` iff `n ≤ 4` or `n = 15`. In particular `2 ^ 15` is the largest such power of `2`
in this window, which is the source's second sentence. -/
theorem mem_oneTwoSet_iff_of_le :
    ∀ n ∈ Finset.range 1001, (Base3OneTwo (2 ^ n) ↔ n ≤ 4 ∨ n = 15) := by decide

set_option maxRecDepth 400000 in
/-- The source's sentence in the form it is written: nothing above `15` and below `1001`
works. -/
theorem not_base3OneTwo_two_pow_of_mem_Icc :
    ∀ n ∈ Finset.Icc 16 1000, ¬ Base3OneTwo (2 ^ n) := by decide

set_option maxRecDepth 400000 in
/-- The two digit conditions overlap exactly on the powers of `2` all of whose base-`3`
digits are `1`: below `1001` that is `n = 0` and `n = 2` only. -/
theorem base3ZeroOne_and_base3OneTwo_iff_of_le :
    ∀ n ∈ Finset.range 1001,
      (Base3ZeroOne (2 ^ n) ∧ Base3OneTwo (2 ^ n) ↔ n = 0 ∨ n = 2) := by decide

/-! ## §9 Joint satisfiability of every hypothesis

Every hypothesis-bearing declaration above is instantiated here at one concrete model, so
that none of them is vacuously true through contradictory hypotheses. The one exception is
`erdos406_imp_eventually_three_dvd`, whose hypothesis is the open conjecture itself; it is
discussed at the end of this section. -/

/-- `digits_lt_three`: satisfied at `d = 1`, `m = 4 = (11)₃`. -/
example : (1 : ℕ) < 3 := digits_lt_three (m := 4) (by decide)

/-- `digits_ne_nil_of_pos`: satisfied at `m = 4`. -/
example : Nat.digits 3 4 ≠ [] := digits_ne_nil_of_pos (by norm_num)

/-- `two_pow_mod_eq_of_pow_mod_one`: `M = 9`, `d = 6` satisfies `2 ^ 6 % 9 = 1 % 9`
(`64 = 7·9 + 1`), and at `n = 8` the conclusion says `256 % 9 = 4 = 2 ^ 2 % 9`. -/
example : 2 ^ 8 % 9 = 2 ^ (8 % 6) % 9 :=
  two_pow_mod_eq_of_pow_mod_one (by norm_num) 8

/-- `base3ZeroOne_mod_pow`: satisfied at `m = 256 = (100111)₃`, `j = 3`; the low three
digits are `(111)₃ = 13`. -/
example : Base3ZeroOne (256 % 3 ^ 3) := base3ZeroOne_mod_pow (by decide) 3

/-- `base3ZeroOne_two_pow_mod_pow`: **both** hypotheses hold jointly at `j = 2`, `d = 6`,
`n = 2` — `2 ^ 6 % 3 ^ 2 = 1 % 3 ^ 2` and `Base3ZeroOne (2 ^ 2)`. -/
example : Base3ZeroOne (2 ^ (2 % 6) % 3 ^ 2) :=
  base3ZeroOne_two_pow_mod_pow (j := 2) (d := 6) (by norm_num) witness_two_pow_two

/-- `mod_six_of_base3ZeroOne_two_pow`: satisfied at `n = 8`, where `8 % 6 = 2`. -/
example : 8 % 6 = 0 ∨ 8 % 6 = 2 := mod_six_of_base3ZeroOne_two_pow witness_two_pow_eight

/-- `mod_eighteen_of_base3ZeroOne_two_pow`: satisfied at `n = 8`. -/
example : 8 % 18 = 0 ∨ 8 % 18 = 2 ∨ 8 % 18 = 6 ∨ 8 % 18 = 8 :=
  mod_eighteen_of_base3ZeroOne_two_pow witness_two_pow_eight

/-- `mod_fiftyFour_of_base3ZeroOne_two_pow`: satisfied at `n = 8`. -/
example : 8 % 54 = 0 ∨ 8 % 54 = 2 ∨ 8 % 54 = 8 ∨ 8 % 54 = 18 ∨ 8 % 54 = 20 ∨
    8 % 54 = 24 ∨ 8 % 54 = 26 ∨ 8 % 54 = 42 :=
  mod_fiftyFour_of_base3ZeroOne_two_pow witness_two_pow_eight

/-- `even_of_base3ZeroOne_two_pow`: satisfied at `n = 8`. -/
example : Even 8 := even_of_base3ZeroOne_two_pow witness_two_pow_eight

/-- `not_base3ZeroOne_two_pow_of_odd`: satisfied at `n = 1`, and the conclusion agrees with
the independent `decide` in `not_base3ZeroOne_two_pow_one`. -/
example : ¬ Base3ZeroOne (2 ^ 1) := not_base3ZeroOne_two_pow_of_odd ⟨0, by norm_num⟩

/-- `three_dvd_centralBinom_two_pow_of_odd`: satisfied at `k = 1`, where the conclusion
`3 ∣ C(4, 2) = 6` is independently checkable. -/
example : 3 ∣ (2 ^ (1 + 1)).choose (2 ^ 1) ∧ (2 ^ (1 + 1)).choose (2 ^ 1) = 6 :=
  ⟨three_dvd_centralBinom_two_pow_of_odd ⟨0, by norm_num⟩, by decide⟩

/-- `three_dvd_centralBinom_two_pow_of_mod_eighteen`: the four-fold hypothesis holds
jointly at `k = 1` (`1 % 18 = 1`), and again the conclusion is `3 ∣ 6`. -/
example : 3 ∣ (2 ^ (1 + 1)).choose (2 ^ 1) :=
  three_dvd_centralBinom_two_pow_of_mod_eighteen ⟨by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- `three_dvd_centralBinom_two_pow_of_le`: both bounds hold jointly at `k = 9`. -/
example : 3 ∣ (2 ^ (9 + 1)).choose (2 ^ 9) :=
  three_dvd_centralBinom_two_pow_of_le (by norm_num) (by norm_num)

/-- `base3ZeroOne_iff_not_dvd_centralBinom`, both directions at concrete values: `4` has
digits `(11)₃` and `C(8,4) = 70 = 2·5·7` is prime to `3`; `2` has digit `(2)₃` and
`C(4,2) = 6` is not. -/
example : (¬ (3 ∣ Nat.centralBinom 4) ∧ Nat.centralBinom 4 = 70) ∧
    (3 ∣ Nat.centralBinom 2 ∧ Nat.centralBinom 2 = 6) :=
  ⟨⟨(base3ZeroOne_iff_not_dvd_centralBinom 4).mp (by decide), by decide⟩,
    ⟨by decide, by decide⟩⟩

/-- `base3ZeroOne_iff_mem_range_binToTernary` at `256 = 2 ^ 8`: the source's third witness
really is a sum of distinct powers of `3`, namely `1 + 3 + 3² + 3⁵`, which is the source's
own decomposition. -/
example : ∃ j : ℕ, binToTernary j = 2 ^ 8 :=
  Set.mem_range.mp ((base3ZeroOne_iff_mem_range_binToTernary _).mp witness_two_pow_eight)

/-! ### The one hypothesis that cannot be instantiated

`erdos406_imp_eventually_three_dvd` assumes `Conjecture`, which is open: no concrete model
can be exhibited, and none is claimed. What *can* be checked is that the hypothesis is not
known-absurd, and that the file does not secretly prove it either way:

* `erdos406Set` provably **contains** `0`, `2`, `8` (`witnesses_mem_erdos406Set`), so it is
  not the empty set;
* `erdos406Set` is provably **disjoint from the odd numbers**
  (`not_base3ZeroOne_two_pow_of_odd`), so its complement is infinite
  (`infinite_setOf_not_base3ZeroOne_two_pow`);
* neither fact decides finiteness, and `erdos406_iff_eventually_three_dvd` shows the
  hypothesis is *equivalent* to an equally open divisibility statement rather than to
  anything settled.

So the conditional theorem is a genuine conditional, not a vacuous one — but it remains
conditional, and nothing in this file discharges it. -/
example : (0 ∈ erdos406Set ∧ 2 ∈ erdos406Set ∧ 8 ∈ erdos406Set) ∧
    {n : ℕ | ¬ Base3ZeroOne (2 ^ n)}.Infinite :=
  ⟨witnesses_mem_erdos406Set, infinite_setOf_not_base3ZeroOne_two_pow⟩

end Erdos406

#print axioms Erdos406.digits_lt_three
#print axioms Erdos406.base3ZeroOne_iff_eq
#print axioms Erdos406.base3ZeroOne_iff_two_not_mem
#print axioms Erdos406.digits_ne_nil_of_pos
#print axioms Erdos406.digits_two_pow_ne_nil
#print axioms Erdos406.base3ZeroOne_zero
#print axioms Erdos406.base3ZeroOne_iff_forall_index
#print axioms Erdos406.source_decompositions
#print axioms Erdos406.digits_witnesses
#print axioms Erdos406.witness_two_pow_zero
#print axioms Erdos406.witness_two_pow_two
#print axioms Erdos406.witness_two_pow_eight
#print axioms Erdos406.not_base3ZeroOne_two_pow_one
#print axioms Erdos406.not_base3ZeroOne_two_pow_four
#print axioms Erdos406.mem_erdos406Set_iff
#print axioms Erdos406.erdos406Set_nonempty
#print axioms Erdos406.witnesses_mem_erdos406Set
#print axioms Erdos406.erdos406_iff_exists_bound
#print axioms Erdos406.base3ZeroOne_iff_not_dvd_centralBinom
#print axioms Erdos406.centralBinom_two_pow
#print axioms Erdos406.three_dvd_centralBinom_two_pow_iff
#print axioms Erdos406.erdos406_iff_eventually_three_dvd
#print axioms Erdos406.erdos406_imp_eventually_three_dvd
#print axioms Erdos406.base3ZeroOne_iff_mem_range_binToTernary
#print axioms Erdos406.erdos406_iff_finite_gupta
#print axioms Erdos406.two_pow_mod_eq_of_pow_mod_one
#print axioms Erdos406.div_pow_mod_eq_mod_pow_div
#print axioms Erdos406.base3ZeroOne_mod_pow
#print axioms Erdos406.base3ZeroOne_two_pow_mod_pow
#print axioms Erdos406.mod_six_of_base3ZeroOne_two_pow
#print axioms Erdos406.mod_eighteen_of_base3ZeroOne_two_pow
#print axioms Erdos406.mod_fiftyFour_of_base3ZeroOne_two_pow
#print axioms Erdos406.even_of_base3ZeroOne_two_pow
#print axioms Erdos406.not_base3ZeroOne_two_pow_of_odd
#print axioms Erdos406.infinite_setOf_not_base3ZeroOne_two_pow
#print axioms Erdos406.three_dvd_centralBinom_two_pow_of_odd
#print axioms Erdos406.three_dvd_centralBinom_two_pow_of_mod_eighteen
#print axioms Erdos406.mem_erdos406Set_iff_of_le
#print axioms Erdos406.not_base3ZeroOne_two_pow_of_mem_Icc
#print axioms Erdos406.three_dvd_centralBinom_two_pow_of_le
#print axioms Erdos406.base3OneTwo_iff_eq
#print axioms Erdos406.digits_two_pow_fifteen
#print axioms Erdos406.base3OneTwo_two_pow_fifteen
#print axioms Erdos406.mem_oneTwoSet_iff_of_le
#print axioms Erdos406.not_base3OneTwo_two_pow_of_mem_Icc
#print axioms Erdos406.base3ZeroOne_and_base3OneTwo_iff_of_le
