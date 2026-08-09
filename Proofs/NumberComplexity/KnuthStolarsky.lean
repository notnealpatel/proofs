import Mathlib
import NumberComplexity.AdditionChain

/-!
# OEIS A003313: the Knuth–Stolarsky lower bound for shortest addition chains

`l n` (OEIS A003313, built in `NumberComplexity/AdditionChain.lean`) is the
number of additions in a shortest addition chain for `n`; `v n` (OEIS A000120)
is the binary weight of `n`.  This file archives the **Knuth–Stolarsky
conjecture**

`⌊log₂ n⌋ + ⌈log₂ (v n)⌉ ≤ l n`

as a single intended `sorry`, together with a sorry-free layer that pins the
statement down: two infinite families on which it is proved outright and sharp,
an equivalent multiplicative reformulation, and an exhaustive certificate for
`1 ≤ n ≤ 16`.

## Ground truth, quoted verbatim

From `goof oeis show A003313`, re-pulled live 2026-08-05:

> Length of shortest addition chain for n.

> 0,1,2,2,3,3,4,3,4,4,5,4,5,5,5,4,5,5,6,5,6,6,6,5,6,6,6,6,7,6,7,5,6,6,7,6,
> 7,7,7,6,7,7,7,7,7,7,8,6,7,7,7,7,8,7,8,7,8,8,8,7,8,8,8,6,7,7,8,7,8,8,9,7,
> 8,8,8,8,8,8,9,7,8,8,8,8,8,8,9,8,9,8,9,8,9,9,9,7,8,8,8,8

and, from the `formulas` field of the same entry:

> From _Achim Flammenkamp_, Oct 26 2016: (Start)

> a(n) <= 9/log_2(71) log_2(n), for all n.

> It is conjectured by D. E. Knuth, K. Stolarsky et al. that for all n:
> floor(log_2(n)) + ceiling(log_2(v(n))) <= a(n), where v(n) = A000120(n). (End)

From `goof oeis show A000120`, pulled live 2026-08-05:

> Ones-counting sequence: number of 1's in binary expansion of n (or the binary
> weight of n).

> 0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,1,2,2,3,
> 2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,1,2,2,3,2,3,3,4,
> 2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3

`goof oeis show` does not carry the entries' *offset* field, so the index
alignment of the two term lists is not quoted but *established* by the ground
checks below: the `100` A003313 terms are `a(1), …, a(100)` (the alignment
already certified in `AdditionChain.lean`), and the `105` A000120 terms are
`A000120(0), …, A000120(104)`, of which `A000120(0..16)` and `A000120(63)` are
checked against `binaryWeight` by kernel `decide`.

## Status of the conjecture (secondary source, fetched live 2026-08-05)

`http://wwwhomes.uni-bielefeld.de/achim/addition_chain.html` — Achim
Flammenkamp's "Shortest Addition Chains", the page behind the OEIS comment
above.  Its `Conjectures` section lists, as its own item,
`ℓ(n) >= λ(n)+log₂(v(n))`, quoted verbatim:

> This famous lower bound was formulated first a bit differently by Stolarsky
> 1969 (p. 680, Lemma 10) [5] and nearly proved 1974 by Schönhage who showed
> that ℓ(n) >= log_2(n)+log_2(v(n))-2.123164629... holds for each n [7].
> Thurber showed 1973 that it holds for all n with v(n) <= 16.  In October 2008
> Clift confirmed the conjecture for all n <= 2^64 and in September 2019 he
> confirmed it for all n with ℓ(n) - λ(n) <= 5.  Finally until November 2023
> Neill Clift extended the validity of the conjecture for all n with
> v(n) <= 128.  This famous inequality may be rewriten equivalently as
> v(n) <= 2^s(n).

with the notation fixed earlier on the same page:

> Write n in its binary representation and denote by v(n) the number of ones in
> this representation and by λ(n) the binary logarithm of n rounded to the next
> integer down in the case it is not already integer (floor-function).

> ℓ(n)-λ(n) is called the number of small steps of n and is denoted by s(n).

So the conjecture is **open**: confirmed for `n ≤ 2^64`, for `s(n) ≤ 5`, and for
`v(n) ≤ 128`, but unproved in general.  Since `l n` and `⌊log₂ n⌋` are integers,
Flammenkamp's ceiling-free `ℓ(n) >= λ(n)+log₂(v(n))` and the OEIS entry's
`floor(log_2(n)) + ceiling(log_2(v(n))) <= a(n)` are the same claim; his
`v(n) <= 2^s(n)` is the reformulation proved here as
`knuth_stolarsky_iff_mul_two_pow_le`.

**Do not confuse this with the adjacent item on that page.**  The `Conjectures`
section's *previous* entry is `ℓ(2^n-1) = n + ℓ(n) - 1`, the exact form of
Scholz–Brauer, and it is that entry — not this one — which carries

> On 1th July 2024 Neill Clift disproved that the conjecture holds for all n by
> constructing an addition chain for 2^30978119-1 of length 30978148, but
> ℓ(30978119)=31.

A web search for "Knuth–Stolarsky conjecture" readily merges the two and reports
the lower bound as disproved.  It is not; the disproof concerns the
Scholz–Brauer *equality*.

## What is proved here, and what is not

The doubling lower bound `⌊log₂ n⌋ ≤ l n` is already
`NumberComplexity.log_two_le_l` in `AdditionChain.lean` and is **not** reproved
here.  The Knuth–Stolarsky bound is strictly stronger: at `n = 7` the doubling
bound gives `2 ≤ l 7` while Knuth–Stolarsky gives `4 ≤ l 7`
(`log_lt_knuth_stolarsky_bound_seven`).  Schönhage's proved approximation
`l n ≥ log₂ n + log₂ (v n) − 2.123164629…` is not formalized.

Main declarations:

* `NumberComplexity.binaryWeight` — A000120, as `n.bitIndices.length`
  (a reducible abbreviation of the Mathlib-standard notion, not a new notion),
  checked against the A000120 terms above;
* `NumberComplexity.binaryWeight_two_pow`,
  `NumberComplexity.binaryWeight_ne_zero` — its value at powers of two, and its
  positivity for `n ≠ 0`;
* `NumberComplexity.eq_two_pow_of_l_le_log`,
  `NumberComplexity.log_add_one_le_l_of_binaryWeight_ne_one` — a chain of length
  `⌊log₂ n⌋` forces `n` to be a power of two, so every non-power-of-two needs a
  small step;
* `NumberComplexity.knuth_stolarsky_iff_mul_two_pow_le` — **proved**:
  Flammenkamp's reformulation `v(n) ≤ 2^{s(n)}`, in the subtraction-free form
  `v n * 2 ^ ⌊log₂ n⌋ ≤ 2 ^ l n`;
* `NumberComplexity.knuth_stolarsky_of_binaryWeight_le_two` — **proved**: the
  conjecture for every `n` with `v n ≤ 2`, an infinite family (the trivial end
  of Thurber's 1973 `v(n) ≤ 16`);
* `NumberComplexity.l_three_mul_two_pow`,
  `NumberComplexity.knuth_stolarsky_eq_three_mul_two_pow` — **proved**:
  `l (3 * 2 ^ m) = m + 2`, and the conjectured bound is attained with *equality*
  on this infinite family, so it cannot be strengthened;
* `NumberComplexity.knuth_stolarsky_of_le_sixteen` — **proved**: the conjecture
  for all `1 ≤ n ≤ 16`, by kernel-`decide` exhaustion of the chain enumeration
  of `AdditionChain.lean`;
* `NumberComplexity.knuth_stolarsky` — **OPEN**, the intended `sorry`: the
  conjecture itself;
* `NumberComplexity.knuth_stolarsky_iff_lAsc` — **proved**: the claim is the
  same under the entry's own ascending chain convention (`lAsc`), via
  `l_eq_lAsc`.

**Degenerate values.**  `Nat.log 2 0 = 0`, `Nat.clog 2 0 = 0`,
`binaryWeight 0 = 0` and `l 0 = 0` (the empty infimum: no addition chain reaches
`0`) are all junk, and at `n = 0` the conjectured inequality would read `0 ≤ 0`
— true, but about the junk.  Every statement below therefore carries the guard
`0 < n`, matching the A003313 offset `1`.

**Trust.**  Every ground check closes by kernel `decide` or `rfl`; no
`native_decide`, no `@[implemented_by]`/`@[extern]`/`@[csimp]`.  The axiom audit
at the bottom reports at most `propext, Classical.choice, Quot.sound` for every
sorry-free declaration, and `sorryAx` for `knuth_stolarsky` alone.

Card: `Formalize/A003313-knuth-stolarsky.md`.
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## `v n`: the binary weight (OEIS A000120) -/

/-- **OEIS A000120**, the binary weight of `n`: the number of `1`s in the binary
expansion of `n`, written as the length of the Mathlib-standard list
`Nat.bitIndices n` of the positions of those `1`s.  This is a reducible
abbreviation, not a new notion — the elaborated statements below mention
`n.bitIndices.length` directly.  Degenerate value: `binaryWeight 0 = 0`,
matching `A000120(0) = 0`. -/
abbrev binaryWeight (n : ℕ) : ℕ := n.bitIndices.length

-- ground checks against the A000120 terms quoted in the module docstring,
-- `A000120(0), …, A000120(16) = 0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1`:
example : binaryWeight 0 = 0 := by decide
example : binaryWeight 1 = 1 := by decide
example : binaryWeight 2 = 1 := by decide
example : binaryWeight 3 = 2 := by decide
example : binaryWeight 4 = 1 := by decide
example : binaryWeight 5 = 2 := by decide
example : binaryWeight 6 = 2 := by decide
example : binaryWeight 7 = 3 := by decide
example : binaryWeight 8 = 1 := by decide
example : binaryWeight 9 = 2 := by decide
example : binaryWeight 10 = 2 := by decide
example : binaryWeight 11 = 3 := by decide
example : binaryWeight 12 = 2 := by decide
example : binaryWeight 13 = 3 := by decide
example : binaryWeight 14 = 3 := by decide
example : binaryWeight 15 = 4 := by decide
example : binaryWeight 16 = 1 := by decide
-- and a spot check deeper into the quoted terms, `A000120(63) = 6`:
example : binaryWeight 63 = 6 := by decide

/-- A power of two has binary weight `1`. -/
@[simp] theorem binaryWeight_two_pow (k : ℕ) : binaryWeight (2 ^ k) = 1 := by
  rw [show binaryWeight (2 ^ k) = (2 ^ k : ℕ).bitIndices.length from rfl,
    Nat.bitIndices_two_pow, List.length_singleton]

/-- Only `0` has binary weight `0`: a nonzero `n` has a `1` in its binary
expansion. -/
theorem binaryWeight_ne_zero {n : ℕ} (hn : 0 < n) : binaryWeight n ≠ 0 := by
  intro h
  have hnil : n.bitIndices = [] := List.length_eq_zero_iff.mp h
  have hsum : (List.map (fun i => 2 ^ i) n.bitIndices).sum = n :=
    Nat.sum_map_two_pow_bitIndices n
  rw [hnil, List.map_nil, List.sum_nil] at hsum
  omega

/-! ## Small steps: a chain of length `⌊log₂ n⌋` forces a power of two

`s n = l n - ⌊log₂ n⌋` is Flammenkamp's *number of small steps*.  The two lemmas
here compute the `s n = 0` boundary: a chain with no small step doubles at every
step, so it reaches only powers of two.  This is what makes the `v n = 2` case of
the conjecture provable outright. -/

/-- If a shortest chain for `0 < n` performs no more than `⌊log₂ n⌋` additions,
then `n` is exactly `2 ^ ⌊log₂ n⌋`: the doubling bound `n ≤ 2 ^ l n` and
`2 ^ ⌊log₂ n⌋ ≤ n` squeeze `n` between equal powers. -/
theorem eq_two_pow_of_l_le_log {n : ℕ} (hn : 0 < n) (h : l n ≤ Nat.log 2 n) :
    n = 2 ^ Nat.log 2 n := by
  have hup : n ≤ 2 ^ l n := le_two_pow_l n hn
  have hlow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hmono : (2 : ℕ) ^ l n ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- Every `0 < n` that is not a power of two costs at least one *small step*:
`⌊log₂ n⌋ + 1 ≤ l n`.  The hypothesis is phrased through the binary weight,
`binaryWeight n ≠ 1`, which for `0 < n` says exactly that `n` is not a power of
two. -/
theorem log_add_one_le_l_of_binaryWeight_ne_one {n : ℕ} (hn : 0 < n)
    (hv : binaryWeight n ≠ 1) : Nat.log 2 n + 1 ≤ l n := by
  by_contra hcon
  have hle : l n ≤ Nat.log 2 n := by omega
  have heq : n = 2 ^ Nat.log 2 n := eq_two_pow_of_l_le_log hn hle
  exact hv (by rw [heq, binaryWeight_two_pow])

/-! ## Flammenkamp's reformulation `v(n) ≤ 2^{s(n)}`

The page quoted in the module docstring records "This famous inequality may be
rewriten equivalently as `v(n) <= 2^s(n)`".  Written subtraction-free (STYLE:
never truncate in `ℕ`), `v(n) ≤ 2^{l n - λ n}` becomes
`v n * 2 ^ ⌊log₂ n⌋ ≤ 2 ^ l n`, and the equivalence is proved below.  It uses
only the already-proved doubling bound `log_two_le_l`, so it is available
independently of the conjecture. -/

/-- **The conjecture, equivalently** (Flammenkamp's `v(n) ≤ 2^{s(n)}`):
`⌊log₂ n⌋ + ⌈log₂ (v n)⌉ ≤ l n` holds iff `v n * 2 ^ ⌊log₂ n⌋ ≤ 2 ^ l n`.  The
guard `0 < n` is needed for the doubling bound `⌊log₂ n⌋ ≤ l n` that lets the
exponent difference `s n = l n - ⌊log₂ n⌋` be split off without `ℕ`
truncation. -/
theorem knuth_stolarsky_iff_mul_two_pow_le (n : ℕ) (hn : 0 < n) :
    Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n ↔
      binaryWeight n * 2 ^ Nat.log 2 n ≤ 2 ^ l n := by
  have hlog : Nat.log 2 n ≤ l n := log_two_le_l n hn
  constructor
  · intro h
    calc binaryWeight n * 2 ^ Nat.log 2 n
        ≤ 2 ^ Nat.clog 2 (binaryWeight n) * 2 ^ Nat.log 2 n :=
          Nat.mul_le_mul_right _ (Nat.le_pow_clog Nat.one_lt_two _)
      _ = 2 ^ (Nat.clog 2 (binaryWeight n) + Nat.log 2 n) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ l n := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro h
    obtain ⟨s, hs⟩ : ∃ s, l n = Nat.log 2 n + s := ⟨l n - Nat.log 2 n, by omega⟩
    have hpow : (2 : ℕ) ^ s * 2 ^ Nat.log 2 n = 2 ^ l n := by
      rw [← pow_add, hs, Nat.add_comm s (Nat.log 2 n)]
    have hcancel : binaryWeight n ≤ 2 ^ s :=
      Nat.le_of_mul_le_mul_right (by rw [hpow]; exact h) (Nat.two_pow_pos _)
    have hclog : Nat.clog 2 (binaryWeight n) ≤ s :=
      (Nat.clog_le_iff_le_pow (b := 2) Nat.one_lt_two).2 hcancel
    omega

/-! ## Proved case: binary weight at most two

For `v n ≤ 2` the conjecture is unconditional.  `v n = 1` is the doubling bound
`log_two_le_l` (since `⌈log₂ 1⌉ = 0`), and `v n = 2` is the small-step lemma
above (since `⌈log₂ 2⌉ = 1`).  This is the trivial end of Thurber's 1973 result
for `v(n) ≤ 16`, quoted in the module docstring; the `v n = 3` case already needs
the classification of one-small-step numbers and is not attempted. -/

/-- **Knuth–Stolarsky for binary weight at most two**, proved:
`⌊log₂ n⌋ + ⌈log₂ (v n)⌉ ≤ l n` whenever `0 < n` and `v n ≤ 2`.  The family is
infinite — it contains every `2 ^ a` and every `2 ^ a + 2 ^ b`. -/
theorem knuth_stolarsky_of_binaryWeight_le_two (n : ℕ) (hn : 0 < n)
    (hv : binaryWeight n ≤ 2) :
    Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n := by
  have hv0 : binaryWeight n ≠ 0 := binaryWeight_ne_zero hn
  interval_cases hcase : (binaryWeight n)
  · omega
  · simpa using log_two_le_l n hn
  · rw [show Nat.clog 2 2 = 1 by decide]
    exact log_add_one_le_l_of_binaryWeight_ne_one hn (by omega)

/-! ## Proved case, and sharpness: the family `3 * 2 ^ m`

`l (3 * 2 ^ m) = m + 2`, with the lower bound supplied by the `v n ≤ 2` case
above and the upper bound by `m` doublings on top of the chain `[3, 2, 1]`.  On
this infinite family the conjectured bound is attained with **equality**, so no
uniform strengthening of its additive constant is possible. -/

/-- `l 3 = 2` (OEIS `a(3) = 2`): the chain `[3, 2, 1]` is optimal, the lower
bound by kernel exhaustion of all one-addition chains. -/
theorem l_three : l 3 = 2 := by
  have hub : l 3 ≤ 2 := l_le_of_isAddChain [3, 2, 1] (by decide) rfl (by decide)
  have hlb : ¬l 3 ≤ 1 := by decide
  omega

/-- `⌊log₂ (3 * 2 ^ m)⌋ = m + 1`, from `2 ^ (m+1) ≤ 3 * 2 ^ m < 2 ^ (m+2)`. -/
theorem log_three_mul_two_pow (m : ℕ) : Nat.log 2 (3 * 2 ^ m) = m + 1 := by
  have hpos : 0 < (2 : ℕ) ^ m := Nat.two_pow_pos m
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
  · rw [show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by ring]
    omega
  · rw [show (2 : ℕ) ^ (m + 1 + 1) = 4 * 2 ^ m by ring]
    omega

/-- `v (3 * 2 ^ m) = 2`: shifting `3 = 2 ^ 1 + 2 ^ 0` left by `m` places keeps its
two binary ones. -/
theorem binaryWeight_three_mul_two_pow (m : ℕ) : binaryWeight (3 * 2 ^ m) = 2 := by
  show (3 * 2 ^ m : ℕ).bitIndices.length = 2
  rw [show 3 * 2 ^ m = 2 ^ m * 3 by ring, Nat.bitIndices_two_pow_mul,
    show (3 : ℕ).bitIndices = [0, 1] by decide]
  rfl

/-- **`l (3 * 2 ^ m) = m + 2`.**  Upper bound: `m` doubling steps on top of the
optimal chain `[3, 2, 1]` for `3`.  Lower bound: `v (3 * 2 ^ m) = 2`, so the
proved case `knuth_stolarsky_of_binaryWeight_le_two` applies and gives
`(m + 1) + 1 ≤ l (3 * 2 ^ m)`. -/
theorem l_three_mul_two_pow (m : ℕ) : l (3 * 2 ^ m) = m + 2 := by
  have hub : ∀ k : ℕ, l (3 * 2 ^ k) ≤ k + 2 := by
    intro k
    induction k with
    | zero => simpa using le_of_eq l_three
    | succ k ih =>
      have hstep : l (2 * (3 * 2 ^ k)) ≤ l (3 * 2 ^ k) + 1 := l_two_mul_le _
      rw [show 2 * (3 * 2 ^ k) = 3 * 2 ^ (k + 1) by ring] at hstep
      omega
  have hlb : Nat.log 2 (3 * 2 ^ m) + Nat.clog 2 (binaryWeight (3 * 2 ^ m)) ≤ l (3 * 2 ^ m) :=
    knuth_stolarsky_of_binaryWeight_le_two _ (by positivity)
      (le_of_eq (binaryWeight_three_mul_two_pow m))
  rw [log_three_mul_two_pow, binaryWeight_three_mul_two_pow,
    show Nat.clog 2 2 = 1 by decide] at hlb
  have hu := hub m
  omega

/-- **Sharpness**: on the infinite family `n = 3 * 2 ^ m` the Knuth–Stolarsky
bound is attained with equality, `⌊log₂ n⌋ + ⌈log₂ (v n)⌉ = l n`.  So the
conjecture, if true, is best possible: no larger additive constant can be
carried. -/
theorem knuth_stolarsky_eq_three_mul_two_pow (m : ℕ) :
    Nat.log 2 (3 * 2 ^ m) + Nat.clog 2 (binaryWeight (3 * 2 ^ m)) = l (3 * 2 ^ m) := by
  rw [log_three_mul_two_pow, binaryWeight_three_mul_two_pow,
    show Nat.clog 2 2 = 1 by decide, l_three_mul_two_pow]

/-! ## Proved case: exhaustive certificate for `1 ≤ n ≤ 16`

Each case pairs a kernel evaluation of the bound `⌊log₂ n⌋ + ⌈log₂ (v n)⌉` with a
kernel exhaustion `¬ l n ≤ bound - 1` of all shorter addition chains, through the
`Decidable (l n ≤ k)` instance of `AdditionChain.lean`.  The two facts are
independent of everything above, so this is also a genuine cross-check of
`knuth_stolarsky_of_binaryWeight_le_two`.

For `n ≤ 16` the bound is in fact *attained*: comparing with the A003313 terms
`a(1..16) = 0,1,2,2,3,3,4,3,4,4,5,4,5,5,5,4` quoted above, the certified lower
bound equals `l n` in every one of the sixteen cases.  The first `n` at which the
bound is strictly smaller than `l n` is `n = 29`, per Flammenkamp's page — "The
smallest n such that ℓ(n)-λ(n)-ceil(log2(v(n))) equals 0,1,2,3,4,... are 1, 29,
3691, 919627, 2135101487, ..." — and certifying *that* would need the enumeration
of all `(6!)^2 = 518400` six-addition chains, beyond this file's kernel budget.

The four `decide +kernel` calls evaluate the 576-chain enumeration
`chainsOfLength 4` in the kernel only, as in `AdditionChain.lean`; this is NOT
`native_decide` and the trust surface is unchanged. -/

/-- **Knuth–Stolarsky for `1 ≤ n ≤ 16`**, proved:
`⌊log₂ n⌋ + ⌈log₂ (v n)⌉ ≤ l n` for every `n` in that range, by exhaustion of the
addition-chain enumeration. -/
theorem knuth_stolarsky_of_le_sixteen (n : ℕ) (hn : 0 < n) (h16 : n ≤ 16) :
    Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n := by
  interval_cases n
  · have hb : Nat.log 2 1 + Nat.clog 2 (binaryWeight 1) = 0 := by decide
    omega
  · have hb : Nat.log 2 2 + Nat.clog 2 (binaryWeight 2) = 1 := by decide
    have hl : ¬l 2 ≤ 0 := by decide
    omega
  · have hb : Nat.log 2 3 + Nat.clog 2 (binaryWeight 3) = 2 := by decide
    have hl : ¬l 3 ≤ 1 := by decide
    omega
  · have hb : Nat.log 2 4 + Nat.clog 2 (binaryWeight 4) = 2 := by decide
    have hl : ¬l 4 ≤ 1 := by decide
    omega
  · have hb : Nat.log 2 5 + Nat.clog 2 (binaryWeight 5) = 3 := by decide
    have hl : ¬l 5 ≤ 2 := by decide
    omega
  · have hb : Nat.log 2 6 + Nat.clog 2 (binaryWeight 6) = 3 := by decide
    have hl : ¬l 6 ≤ 2 := by decide
    omega
  · have hb : Nat.log 2 7 + Nat.clog 2 (binaryWeight 7) = 4 := by decide
    have hl : ¬l 7 ≤ 3 := by decide
    omega
  · have hb : Nat.log 2 8 + Nat.clog 2 (binaryWeight 8) = 3 := by decide
    have hl : ¬l 8 ≤ 2 := by decide
    omega
  · have hb : Nat.log 2 9 + Nat.clog 2 (binaryWeight 9) = 4 := by decide
    have hl : ¬l 9 ≤ 3 := by decide
    omega
  · have hb : Nat.log 2 10 + Nat.clog 2 (binaryWeight 10) = 4 := by decide
    have hl : ¬l 10 ≤ 3 := by decide
    omega
  · have hb : Nat.log 2 11 + Nat.clog 2 (binaryWeight 11) = 5 := by decide
    have hl : ¬l 11 ≤ 4 := by decide +kernel
    omega
  · have hb : Nat.log 2 12 + Nat.clog 2 (binaryWeight 12) = 4 := by decide
    have hl : ¬l 12 ≤ 3 := by decide
    omega
  · have hb : Nat.log 2 13 + Nat.clog 2 (binaryWeight 13) = 5 := by decide
    have hl : ¬l 13 ≤ 4 := by decide +kernel
    omega
  · have hb : Nat.log 2 14 + Nat.clog 2 (binaryWeight 14) = 5 := by decide
    have hl : ¬l 14 ≤ 4 := by decide +kernel
    omega
  · have hb : Nat.log 2 15 + Nat.clog 2 (binaryWeight 15) = 5 := by decide
    have hl : ¬l 15 ≤ 4 := by decide +kernel
    omega
  · have hb : Nat.log 2 16 + Nat.clog 2 (binaryWeight 16) = 4 := by decide
    have hl : ¬l 16 ≤ 3 := by decide
    omega

/-! ## The conjecture: open, intended `sorry`

Everything above is sorry-free and does not depend on what follows.  The
statement below is the OEIS comment quoted verbatim in the module docstring,
transcribed with `Nat.log 2` for `floor(log_2(·))`, `Nat.clog 2` for
`ceiling(log_2(·))`, `binaryWeight` for `v`, and `l` for `a`.  It is open
mathematics (see the status section above); no proof is attempted. -/

/-- **The Knuth–Stolarsky conjecture** (OEIS A003313, comment of Achim
Flammenkamp, Oct 26 2016, attributing it to D. E. Knuth, K. Stolarsky et al.;
first stated in a different form by Stolarsky 1969, Lemma 10) — OPEN:

`floor(log_2 n) + ceiling(log_2 (v n)) ≤ l n` for every `n ≥ 1`,

where `l` is A003313, the shortest-addition-chain length, and `v` is A000120, the
binary weight.  The guard `0 < n` keeps `Nat.log`, `Nat.clog` and `l` off their
junk values at `0` and matches the A003313 offset `1`.

Known: Schönhage 1975 proved the approximation
`l n ≥ log₂ n + log₂ (v n) − 2.123164629…`; Thurber 1973 proved the conjecture
for `v n ≤ 16` (Clift extended this to `v n ≤ 128` by November 2023); Clift
verified it for all `n ≤ 2 ^ 64` (October 2008) and for all `n` with
`l n − ⌊log₂ n⌋ ≤ 5` (September 2019).  Proved here without hypothesis for
`v n ≤ 2` (`knuth_stolarsky_of_binaryWeight_le_two`) and for `n ≤ 16`
(`knuth_stolarsky_of_le_sixteen`), and shown sharp on `3 * 2 ^ m`
(`knuth_stolarsky_eq_three_mul_two_pow`). -/
theorem knuth_stolarsky (n : ℕ) (hn : 0 < n) :
    Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n := by
  -- intended sorry: open conjecture (card `Formalize/A003313-knuth-stolarsky.md`).
  -- Confirmed open as of the 2026-08-05 pull of Flammenkamp's page quoted in the
  -- module docstring; the July 2024 Clift disproof recorded there refutes the
  -- adjacent Scholz-Brauer equality, not this bound.
  sorry

/-! ## The claim under the entry's own (ascending) chain convention

`AdditionChain.lean` proves `l_eq_lAsc : l n = lAsc n`, where `lAsc` is the
minimum over the strictly increasing chains `1 = s 0 < ⋯ < s r = n` of the
A003313 comment of M. F. Hasler.  So the conjecture is convention-independent;
the bridge below is sorry-free and does not use `knuth_stolarsky`. -/

/-- The Knuth–Stolarsky claim is the same statement under the permissive chain
convention (`l`) and under the OEIS entry's own ascending convention (`lAsc`),
because `l = lAsc` (`l_eq_lAsc`). -/
theorem knuth_stolarsky_iff_lAsc (n : ℕ) :
    Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n ↔
      Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ lAsc n := by
  rw [l_eq_lAsc]

/-! ## Satisfiability, sharpness and non-triviality of the archived statement

The hypothesis `0 < n` of `knuth_stolarsky` and its conclusion are jointly
satisfied — proved outright, without the `sorry` — at concrete models, and the
conclusion is strictly stronger than the bound already in hand. -/

/-- The hypothesis and conclusion of `knuth_stolarsky` are jointly satisfiable:
they hold at `n = 15`, where `⌊log₂ 15⌋ + ⌈log₂ 4⌉ = 3 + 2 = 5 = l 15`, and this
is proved outright by chain exhaustion, not assumed. -/
theorem exists_knuth_stolarsky_witness :
    ∃ n : ℕ, 0 < n ∧ Nat.log 2 n + Nat.clog 2 (binaryWeight n) ≤ l n :=
  ⟨15, by norm_num, knuth_stolarsky_of_le_sixteen 15 (by norm_num) (by norm_num)⟩

/-- The conjectured bound is **strictly stronger** than the doubling bound
`log_two_le_l` already proved in `AdditionChain.lean`: at `n = 7` the doubling
bound gives only `2 ≤ l 7`, while Knuth–Stolarsky gives `4 ≤ l 7`.  Without this
the archived statement could be a restatement of a theorem already in hand. -/
theorem log_lt_knuth_stolarsky_bound_seven :
    Nat.log 2 7 < Nat.log 2 7 + Nat.clog 2 (binaryWeight 7) := by decide

-- the proved-case and reformulation lemmas, instantiated at concrete models:
example : Nat.log 2 12 + Nat.clog 2 (binaryWeight 12) ≤ l 12 :=
  knuth_stolarsky_of_binaryWeight_le_two 12 (by norm_num) (by decide)
example : (Nat.log 2 15 + Nat.clog 2 (binaryWeight 15) ≤ l 15) ↔
    binaryWeight 15 * 2 ^ Nat.log 2 15 ≤ 2 ^ l 15 :=
  knuth_stolarsky_iff_mul_two_pow_le 15 (by norm_num)
example : Nat.log 2 12 + 1 ≤ l 12 :=
  log_add_one_le_l_of_binaryWeight_ne_one (by norm_num) (by decide)
example : (4 : ℕ) = 2 ^ Nat.log 2 4 :=
  eq_two_pow_of_l_le_log (by norm_num)
    (by have h1 : l 4 ≤ 2 := l_le_of_isAddChain [4, 2, 1] (by decide) rfl (by decide)
        have h2 : Nat.log 2 4 = 2 := by decide
        omega)
example : (5 : ℕ) = 2 ^ Nat.log 2 5 → l 5 ≤ Nat.log 2 5 → False := fun h _ => by
  rw [show Nat.log 2 5 = 2 by decide] at h
  omega
example : l 24 = 5 := by
  have h := l_three_mul_two_pow 3
  norm_num at h
  exact h
example : Nat.log 2 24 + Nat.clog 2 (binaryWeight 24) = l 24 :=
  knuth_stolarsky_eq_three_mul_two_pow 3
example : (Nat.log 2 15 + Nat.clog 2 (binaryWeight 15) ≤ l 15) ↔
    Nat.log 2 15 + Nat.clog 2 (binaryWeight 15) ≤ lAsc 15 :=
  knuth_stolarsky_iff_lAsc 15

/-! ## Axiom audit

Every declaration below is sorry-free and must report a subset of
`{propext, Classical.choice, Quot.sound}`.  `knuth_stolarsky` is the file's one
intended `sorry` and reports `sorryAx` by design; it is printed last so that the
audit is explicit rather than silent. -/

#print axioms binaryWeight
#print axioms binaryWeight_two_pow
#print axioms binaryWeight_ne_zero
#print axioms eq_two_pow_of_l_le_log
#print axioms log_add_one_le_l_of_binaryWeight_ne_one
#print axioms knuth_stolarsky_iff_mul_two_pow_le
#print axioms knuth_stolarsky_of_binaryWeight_le_two
#print axioms l_three
#print axioms log_three_mul_two_pow
#print axioms binaryWeight_three_mul_two_pow
#print axioms l_three_mul_two_pow
#print axioms knuth_stolarsky_eq_three_mul_two_pow
#print axioms knuth_stolarsky_of_le_sixteen
#print axioms knuth_stolarsky_iff_lAsc
#print axioms exists_knuth_stolarsky_witness
#print axioms log_lt_knuth_stolarsky_bound_seven

-- the intended `sorry`, audited explicitly:
#print axioms knuth_stolarsky

end NumberComplexity
