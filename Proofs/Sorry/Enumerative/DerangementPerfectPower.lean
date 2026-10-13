import Enumerative.DerangementPerfectPower

/-!
# Quarantined admissions

The original source and disclosure documentation is retained below as historical context.
Descriptions of the original file refer to its pre-quarantine layout: independent proven
infrastructure now lives in the imported production module; the admissions and their
admission-dependent consequences live only here. No proof closure is claimed.
-/


/-!
# A000166: Zhi-Wei Sun's conjecture that `a(4) = 9` is the only perfect-power derangement number

## Source, pinned verbatim

Re-pulled with `goof oeis show A000166` on **2026-08-05**.

`id` (verbatim): `A000166`

`name` (verbatim):

> Subfactorial or rencontres numbers, or derangements: number of permutations of n elements
> with no fixed points.

`keywords` (verbatim): `core,nonn,easy,nice`

`terms` (verbatim, the whole field; line-wrapped here only, the field itself is one line):

> 1,0,1,2,9,44,265,1854,14833,133496,1334961,14684570,176214841,2290792932,32071101049,
> 481066515734,7697064251745,130850092279664,2355301661033953,44750731559645106,
> 895014631192902121,18795307255050944540,413496759611120779881,9510425471055777937262

The archived claim (verbatim, the whole line, from the `comments` field — the last of the 41
comment lines):

> Conjecture: a(n) with n > 2 is a perfect power only for n = 4 with a(4) = 3^2. This has been
> verified for n <= 1000. - _Zhi-Wei Sun_, Jan 09 2025

## ⚠ Discrepancy with the dispatching brief — the brief's claim is FALSE

The brief that opened this lane asked to archive

> no derangement number `D(n)` for `n ≥ 3` is a perfect power.

**That is not what the source says, and it is false.**  The source explicitly names an
exception, `a(4) = 3^2`, and `numDerangements 4 = 9 = 3 ^ 2` really is a perfect power in
exactly Sun's sense (`x = 3 > 1`, `m = 2 > 1`).  Formalizing the brief as written would have
put a refutable statement into the archive behind a `sorry`.

What is archived below is the **source's** statement — "a perfect power only for `n = 4`" —
and the brief's reading is refuted outright and `sorry`-free by
`not_forall_not_isPerfectPower_numDerangements`.  Nothing else in the brief is contradicted:
the coprimality warm-up it suggested is proved (`coprime_numDerangements_succ`), and small
values are certified by `decide` as it asked.

## Indexing

The offset is `0`.  Two entries of the `formulas` field pin it: "a(0) = 1, a(n) = round(n!/e) =
floor(n!/e + 1/2) for n > 0", and the editorial note on Plouffe's formula, "[This uses offset 1,
see below for the version with offset 0. - _Charles R Greathouse IV_, Jan 25 2012]".  A
`comments` line says the same in words: "Each necklace with no beads is assumed to contribute a
factor 1 in the counting, hence a(0)=1."  So the `terms` field above is `a(0), …, a(23)`, and
`numDerangements n = a(n)` needs no offset shim.

Mathlib's `numDerangements` is the OEIS `name` read literally: `derangements α` is the set of
permutations of `α` with no fixed points, and `card_derangements_fin_eq_numDerangements` says
`Fintype.card (derangements (Fin n)) = numDerangements n`.  That identification is recorded
here as `numDerangements_eq_card_derangements`, so this file is about A000166 *by definition*
rather than by numerical coincidence — and, independently, the identification with the pinned
`terms` field is kernel-checked (`map_numDerangements_range_eq_a000166Prefix`).

## What is archived and what is proved

Archived with the single intended `sorry`:

* `sun_eq_four_of_isPerfectPower_numDerangements` — for `2 < n`, if `a(n)` is a perfect power
  then `n = 4`.  This is the "only for n = 4" half of the comment above; the "with a(4) = 3^2"
  half is proved.

Proved here, `sorry`-free and kernel-checked:

* `four_le_of_isPerfectPower` — every perfect power in Sun's sense is at least `4`.
* `not_isPerfectPower_of_isRootBracket` — a certificate scheme: a list `xs` of integer roots
  that *strictly* bracket `N` (`xs[i] ^ (i+2) < N < (xs[i]+1) ^ (i+2)`) rules out every
  exponent at once, given `N < 2 ^ (xs.length + 2)`.
* `a000166RootBrackets_valid` — a kernel sweep over 665 such witnesses covering every term
  `a(5), …, a(23)` of the pinned prefix and every exponent `2 … ⌊log₂ a(n)⌋`.
* `isPerfectPower_iff_of_mem_a000166Prefix` — hence **the only perfect power among the pinned
  terms `a(0), …, a(23)` is `9`**, both directions.
* `map_numDerangements_range_eq_a000166Prefix` — kernel-checked ground truth: Mathlib's
  `numDerangements` reproduces the pinned `terms` field exactly, all 24 entries.  Two `example`s
  beside it corroborate the OEIS `name` independently of any recurrence, by having the kernel
  enumerate all `4!` and all `5!` permutations and count the fixed-point-free ones: `9` and `44`.
* `sun_isPerfectPower_numDerangements_iff_of_lt_24` — the conjecture, end to end in the kernel,
  for every `n < 24`.  This is the whole published prefix; the guard `2 < n` is not even needed
  there.
* `isPerfectPower_numDerangements_four` — the exception is real: `a(4) = 9 = 3 ^ 2`.
* `not_forall_not_isPerfectPower_numDerangements` — the dispatching brief's reading is false.
* `not_isPerfectPower_numDerangements_of_lt_three` — the source's guard `n > 2` is removable
  under Sun's reading: `a(0) = a(2) = 1` and `a(1) = 0` are all below `4`.
* `coprime_numDerangements_succ` — consecutive derangement numbers are coprime, for every `n`.
  This is the warm-up: it is the one-line consequence of the `±1` recurrence that a perfect-power
  argument would have to beat, and it is proved for all `n`, not just the prefix.
* `numDerangements_succ_eq_mul_add_neg_one_pow` — the `formulas` field's "a(n) = n*a(n-1) +
  (-1)^n", derived from Mathlib's `numDerangements_succ`.

## Why the certificate scheme rather than a brute-force sweep

The sibling card for A000041 (`Proofs/Enumerative/PartitionPerfectPower.lean`) enumerates
`Finset.Icc 2 S × Finset.Icc 2 B` in the kernel.  That does not transfer: the largest pinned
A000041 term is `173525`, so `S = 416`; the largest pinned A000166 term is
`9510425471055777937262`, so the same scheme would need `S ≈ 9.75 · 10^10` bases.

The scheme used instead is a witness table.  To show `N` is not an `m`-th power it is enough to
exhibit one `x` with `x ^ m < N < (x + 1) ^ m`: any `y` with `y ^ m = N` satisfies either
`y ≤ x`, forcing `y ^ m ≤ x ^ m < N`, or `x + 1 ≤ y`, forcing `N < (x+1) ^ m ≤ y ^ m`.  So the
kernel does two exponentiations per `(N, m)` pair instead of a search: `1330` exponentiations
total, and the whole sweep elaborates in about three seconds.  Coverage of the exponents is not
an extra hypothesis — it is forced by `N < 2 ^ (xs.length + 2)`, because `2 ^ m ≤ x ^ m = N`.

`native_decide` was not granted for this file and is not used; every sweep below is `decide`,
i.e. kernel reduction.  `Nat.sqrt` is likewise avoided: its auxiliary `Nat.sqrt.iter` is
well-founded and does not reduce in the kernel.

## Why the conjecture is hard

The entry's own handles are the wrong shape for it, and the entry says so more sharply than the
A000041 entry does.

*Congruential.*  Peter Bala's comment (verbatim): "The sequence a(n) taken modulo a positive
integer k is periodic with exact period dividing k when k is even and dividing 2*k when k is
odd. This follows from the congruence a(n+k) = (-1)^k*a(n) (mod k) for all n and k, which in
turn is easily proved by induction making use of the recurrence a(n) = n*a(n-1) + (-1)^n. -
_Peter Bala_, Nov 21 2017".  A fixed modulus therefore sees only a periodic pattern of residues,
and it can exclude perfect powers only if some residue class it pins down contains no `m`-th
power residue.  The strongest published congruences do not do that: Bala's own list (verbatim)
"a(2*n) is odd; in fact, a(2*n) == 1 (mod 8). Other divisibility properties include a(6*n) == 1
(mod 24), a(9*n+4) == a(9*n+7) == 0 (mod 9), a(10*n) == 1 (mod 40), a(11*n+5) == 0 (mod 11) and
a(13*n+8 ) == 0 (mod 13). - _Peter Bala_, Apr 05 2022" leaves `a(2n) ≡ 1 (mod 8)`, and `1` is a
square mod `8` — indeed `a(4) = 9 ≡ 1 (mod 8)` is the exception itself.

*Analytic.*  The `formulas` field gives "a(0) = 1, a(n) = round(n!/e) = floor(n!/e + 1/2) for
n > 0", which locates `a(n)` as the nearest integer to a transcendental quantity.  That pins the
value to the integer exactly, but says nothing about whether that integer is an `m`-th power.

The same obstruction blocks the sibling conjecture on A000041 (partitions,
`Proofs/Enumerative/PartitionPerfectPower.lean`) and Brocard's problem
(`Proofs/Scratch/Candidates/A146968Brocard.lean`).

## Computational orientation (not proofs)

`command -v sage` is empty on this machine, so no `sage` was used and none is claimed.  A plain
`python3` script (no `sympy`, no external library — `sympy` is installed but was not used)
recomputed `a(0), …, a(200)` from Euler's recurrence `a(n) = (n-1)*(a(n-1) + a(n-2))`,
reproduced the pinned 24-term prefix byte for byte, cross-checked the second recurrence
`a(n) = n*a(n-1) + (-1)^n` on that prefix, and found `a(4) = 3^2` to be the only perfect power
among `a(3), …, a(200)` and `gcd(a(n), a(n+1)) = 1` throughout.  That run is orientation only;
`a000166RootBrackets_valid` is what carries proof weight, and it covers exactly the pinned
prefix.  The witness table below was emitted by that script and validated by parsing the emitted
Lean text back and re-checking every inequality against the source values.
-/

set_option autoImplicit false

namespace A000166

/-! ## The conjecture -/

/-- **Sun's perfect-power conjecture for the derangement numbers (OEIS A000166).**

Verbatim from the entry's `comments` field, pulled 2026-08-05:

> Conjecture: a(n) with n > 2 is a perfect power only for n = 4 with a(4) = 3^2. This has been
> verified for n <= 1000. - _Zhi-Wei Sun_, Jan 09 2025

This declaration is the "only for n = 4" half.  The "with a(4) = 3^2" half is
`isPerfectPower_numDerangements_four`, which is proved; the two are combined in
`sun_isPerfectPower_numDerangements_iff`.

**Status: open.**  This is the single intended `sorry` of the file.  The entry claims
verification for `n ≤ 1000`; that claim is *not* reproduced here and is not assumed anywhere.
What is verified here is `sun_isPerfectPower_numDerangements_iff_of_lt_24`, the same statement
for every `n < 24`, kernel-checked end to end — the range covered by the entry's published
`terms` field.

See the module docstring for why the entry's own congruential and analytic handles do not
reach this. -/
theorem sun_eq_four_of_isPerfectPower_numDerangements {n : ℕ} (hn : 2 < n)
    (h : IsPerfectPower (numDerangements n)) : n = 4 := by
  sorry

/-- **Sun's conjecture as an iff**, exactly as the source phrases it: for `n > 2`, `a(n)` is a
perfect power precisely when `n = 4`.

The `←` direction is proved (`isPerfectPower_numDerangements_four`); the `→` direction is the
open half. -/
theorem sun_isPerfectPower_numDerangements_iff {n : ℕ} (hn : 2 < n) :
    IsPerfectPower (numDerangements n) ↔ n = 4 :=
  ⟨fun h => sun_eq_four_of_isPerfectPower_numDerangements hn h,
   fun h => h ▸ isPerfectPower_numDerangements_four⟩

/-- The same, with the source's guard dropped — legitimate because the three excluded indices
are settled by `not_isPerfectPower_numDerangements_of_lt_three`. -/
theorem sun_isPerfectPower_numDerangements_iff_all (n : ℕ) :
    IsPerfectPower (numDerangements n) ↔ n = 4 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · constructor
    · intro h
      exact absurd h (not_isPerfectPower_numDerangements_of_lt_three hn)
    · intro h
      omega
  · exact sun_isPerfectPower_numDerangements_iff (by omega)

/-- The hypothesis of `sun_isPerfectPower_numDerangements_iff` is inhabited at the one index
where its conclusion is affirmative, `n = 4`; so the conjecture is not a statement about an
empty family. -/
example : IsPerfectPower (numDerangements 4) ↔ (4 : ℕ) = 4 :=
  sun_isPerfectPower_numDerangements_iff (by norm_num)
end A000166
