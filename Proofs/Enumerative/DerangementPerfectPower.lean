import Mathlib

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

/-! ## The perfect-power predicate

Mathlib has no perfect-power predicate: `leandoc IsPerfectPower` returns `mode: "miss"`.  The
definition below is character-for-character the one in the A000041 sibling card, deliberately:
Sun's two comments use the same words, and the two cards must not drift apart.  It is repeated
rather than imported so that neither archive card depends on the other's `sorry`. -/

/-- `IsPerfectPower N` says `N = x ^ m` for some `1 < x` and `1 < m`.

This is Sun's reading — his A000041 comment spells it out as "the form x^m with m > 1 and
x > 1", and his A000166 comment's own example `a(4) = 3^2` has `x = 3` and `m = 2`.  Both
strictness conditions are load-bearing: without `1 < m` every `N` is `N ^ 1`, and without
`1 < x` every `N ∈ {0, 1}` is `0 ^ 2` or `1 ^ 2`. -/
def IsPerfectPower (N : ℕ) : Prop := ∃ x m : ℕ, 1 < x ∧ 1 < m ∧ x ^ m = N

/-- Satisfiability of `IsPerfectPower`, at the very value this file is about: `9 = 3 ^ 2`. -/
example : IsPerfectPower 9 := ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

/-- Satisfiability again, at a value that is not a square: `8 = 2 ^ 3`. -/
example : IsPerfectPower 8 := ⟨2, 3, by norm_num, by norm_num, by norm_num⟩

/-- **Every perfect power is at least `4`.**

`2 ^ 2` is the smallest value the predicate admits.  This is what lets the source's guard
`n > 2` be dropped: `a(0) = a(2) = 1` and `a(1) = 0` are excluded for free. -/
theorem four_le_of_isPerfectPower {N : ℕ} (h : IsPerfectPower N) : 4 ≤ N := by
  obtain ⟨x, m, hx, hm, rfl⟩ := h
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
    _ ≤ x ^ m := Nat.pow_le_pow_right (by omega) hm

/-- The predicate is not everything: `0`, `1`, `2`, `3` are not perfect powers. -/
example : ¬ IsPerfectPower 0 ∧ ¬ IsPerfectPower 1 ∧ ¬ IsPerfectPower 2 ∧ ¬ IsPerfectPower 3 :=
  ⟨fun h => by have h4 : 4 ≤ 0 := four_le_of_isPerfectPower h; omega,
   fun h => by have h4 : 4 ≤ 1 := four_le_of_isPerfectPower h; omega,
   fun h => by have h4 : 4 ≤ 2 := four_le_of_isPerfectPower h; omega,
   fun h => by have h4 : 4 ≤ 3 := four_le_of_isPerfectPower h; omega⟩

/-! ## Root brackets: ruling out every exponent with two exponentiations apiece -/

/-- `IsRootBracket N xs` says that `xs` is a table of *strict* integer root brackets for `N`,
one per exponent, starting at exponent `2`: entry `xs[i]` satisfies

  `xs[i] ^ (i + 2) < N < (xs[i] + 1) ^ (i + 2)`.

Each entry is exactly the statement that `N` lies strictly between two consecutive
`(i+2)`-th powers, hence is not an `(i+2)`-th power itself.

`List.getD ... 0` is used rather than dependent indexing so that the predicate is a plain
bounded `∀` over `ℕ` and the decidability instance below is the core one. -/
def IsRootBracket (N : ℕ) (xs : List ℕ) : Prop :=
  ∀ i < xs.length, (xs.getD i 0) ^ (i + 2) < N ∧ N < (xs.getD i 0 + 1) ^ (i + 2)

/-- The decidability instance is `Nat.decidableBallLT` after unfolding `IsRootBracket`.
It is supplied by `inferInstanceAs` rather than by `unfold`+`infer_instance` so that the
resulting term is literally the core instance and reduces in the kernel. -/
instance decidableIsRootBracket (N : ℕ) (xs : List ℕ) : Decidable (IsRootBracket N xs) :=
  inferInstanceAs (Decidable (∀ i < xs.length,
    (xs.getD i 0) ^ (i + 2) < N ∧ N < (xs.getD i 0 + 1) ^ (i + 2)))

/-- Ground truth for `IsRootBracket`: `[6, 3, 2, 2]` brackets `44` at exponents `2, 3, 4, 5`
(`6 ^ 2 = 36 < 44 < 49 = 7 ^ 2`, and so on). -/
example : IsRootBracket 44 [6, 3, 2, 2] := by decide

/-- …and the predicate really constrains: `[3]` is *not* a root bracket for `9`, because
`3 ^ 2 = 9` is not `< 9`.  A perfect power admits no bracket at its own exponent. -/
example : ¬ IsRootBracket 9 [3] := by decide

/-- …nor is a table with a wrong entry accepted: `[5, 3, 2, 2]` fails at exponent `2`,
since `44 < 6 ^ 2 = 36` is false. -/
example : ¬ IsRootBracket 44 [5, 3, 2, 2] := by decide

/-- **A full root-bracket table rules out every exponent at once.**

The size hypothesis `N < 2 ^ (xs.length + 2)` is what makes the table *complete* rather than
partial: if `N = x ^ m` with `1 < x` and `1 < m` then `2 ^ m ≤ x ^ m = N < 2 ^ (xs.length + 2)`,
so `m ≤ xs.length + 1`, and the entry at index `m - 2` is in range and contradicts `x ^ m = N`.

At `xs = []` the hypothesis reads `N < 4`, and the conclusion is still correct — no `N < 4` is a
perfect power — so the degenerate case is sound rather than a hole; see the example below. -/
theorem not_isPerfectPower_of_isRootBracket {N : ℕ} {xs : List ℕ}
    (hsize : N < 2 ^ (xs.length + 2)) (hbr : IsRootBracket N xs) : ¬ IsPerfectPower N := by
  rintro ⟨x, m, hx, hm, rfl⟩
  have hbase : 2 ^ m ≤ x ^ m := Nat.pow_le_pow_left hx m
  have hmlt : m < xs.length + 2 := by
    by_contra hcon
    have hbig : (2 : ℕ) ^ (xs.length + 2) ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hlo, hhi⟩ := hbr (m - 2) (by omega)
  rw [show m - 2 + 2 = m by omega] at hlo hhi
  rcases Nat.lt_or_ge x (xs.getD (m - 2) 0 + 1) with hcase | hcase
  · have hle : x ^ m ≤ (xs.getD (m - 2) 0) ^ m := Nat.pow_le_pow_left (by omega) m
    omega
  · have hle : (xs.getD (m - 2) 0 + 1) ^ m ≤ x ^ m := Nat.pow_le_pow_left hcase m
    omega

/-- Nonvacuity of `not_isPerfectPower_of_isRootBracket` at the degenerate table `xs = []`:
the hypotheses are jointly satisfiable there and the conclusion is the true statement that `3`
is not a perfect power. -/
example : ¬ IsPerfectPower 3 :=
  not_isPerfectPower_of_isRootBracket (xs := []) (by decide) (by decide)

/-- Nonvacuity at a nonempty table: the hypotheses are jointly satisfiable at
`N = 44`, `xs = [6, 3, 2, 2]`. -/
example : ¬ IsPerfectPower 44 :=
  not_isPerfectPower_of_isRootBracket (xs := [6, 3, 2, 2]) (by decide) (by decide)

/-! ## The pinned OEIS prefix -/

/-- The `terms` field of OEIS A000166 as pulled on 2026-08-05, transcribed in order:
`a(0), a(1), …, a(23)`. -/
def a000166Prefix : List ℕ :=
  [1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961, 14684570, 176214841, 2290792932,
   32071101049, 481066515734, 7697064251745, 130850092279664, 2355301661033953,
   44750731559645106, 895014631192902121, 18795307255050944540, 413496759611120779881,
   9510425471055777937262]

/-- The pinned prefix has the 24 entries `a(0), …, a(23)`. -/
theorem a000166Prefix_length : a000166Prefix.length = 24 := by decide

/-- **The root-bracket table for the pinned prefix.**

One entry `(a(n), xs)` for each `n` with `5 ≤ n ≤ 23`; `xs` has one witness per exponent
`2, 3, …, ⌊log₂ a(n)⌋`, namely the integer root `⌊a(n)^(1/m)⌋`.  The terms `a(0), …, a(3)` are
below `4` and need no witness, and `a(4) = 9` is the source's exception and deliberately has no
entry — see `nine_notMem_a000166RootBrackets_keys`.

665 witnesses in total. -/
def a000166RootBrackets : List (ℕ × List ℕ) :=
[
  -- a(5) = 44;  exponents 2 .. 5
  (44, [6, 3, 2, 2]),
  -- a(6) = 265;  exponents 2 .. 8
  (265, [16, 6, 4, 3, 2, 2, 2]),
  -- a(7) = 1854;  exponents 2 .. 10
  (1854, [43, 12, 6, 4, 3, 2, 2, 2, 2]),
  -- a(8) = 14833;  exponents 2 .. 13
  (14833, [121, 24, 11, 6, 4, 3, 3, 2, 2, 2, 2, 2]),
  -- a(9) = 133496;  exponents 2 .. 17
  (133496, [365, 51, 19, 10, 7, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2]),
  -- a(10) = 1334961;  exponents 2 .. 20
  (1334961, [1155, 110, 33, 16, 10, 7, 5, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(11) = 14684570;  exponents 2 .. 23
  (14684570, [3832, 244, 61, 27, 15, 10, 7, 6, 5, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(12) = 176214841;  exponents 2 .. 27
  (176214841,
   [13274, 560, 115, 44, 23, 15, 10, 8, 6, 5, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(13) = 2290792932;  exponents 2 .. 31
  (2290792932,
   [47862, 1318, 218, 74, 36, 21, 14, 10, 8, 7, 6, 5, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2]),
  -- a(14) = 32071101049;  exponents 2 .. 34
  (32071101049,
   [179084, 3177, 423, 126, 56, 31, 20, 14, 11, 9, 7, 6, 5, 5, 4, 4, 3, 3, 3, 3, 3, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(15) = 481066515734;  exponents 2 .. 38
  (481066515734,
   [693589, 7835, 832, 216, 88, 46, 28, 19, 14, 11, 9, 7, 6, 6, 5, 4, 4, 4, 3, 3, 3, 3, 3, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(16) = 7697064251745;  exponents 2 .. 42
  (7697064251745,
   [2774358, 19744, 1665, 377, 140, 69, 40, 27, 19, 14, 11, 9, 8, 7, 6, 5, 5, 4, 4, 4, 3, 3, 3,
    3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(17) = 130850092279664;  exponents 2 .. 46
  (130850092279664,
   [11438972, 50768, 3382, 665, 225, 103, 58, 37, 25, 19, 15, 12, 10, 8, 7, 6, 6, 5, 5, 4, 4, 4,
    3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(18) = 2355301661033953;  exponents 2 .. 51
  (2355301661033953,
   [48531450, 133050, 6966, 1186, 364, 157, 83, 51, 34, 24, 19, 15, 12, 10, 9, 8, 7, 6, 5, 5, 4,
    4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(19) = 44750731559645106;  exponents 2 .. 55
  (44750731559645106,
   [211543687, 355031, 14544, 2138, 595, 239, 120, 70, 46, 32, 24, 19, 15, 12, 10, 9, 8, 7, 6, 6,
    5, 5, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2]),
  -- a(20) = 895014631192902121;  exponents 2 .. 59
  (895014631192902121,
   [946052129, 963703, 30757, 3893, 981, 366, 175, 98, 62, 42, 31, 24, 19, 15, 13, 11, 9, 8, 7,
    7, 6, 6, 5, 5, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(21) = 18795307255050944540;  exponents 2 .. 64
  (18795307255050944540,
   [4335355493, 2658784, 65843, 7158, 1630, 566, 256, 138, 84, 56, 40, 30, 23, 19, 16, 13, 11,
    10, 9, 8, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(22) = 413496759611120779881;  exponents 2 .. 68
  (413496759611120779881,
   [20334619731, 7450018, 142599, 13282, 2729, 881, 377, 195, 115, 74, 52, 38, 29, 23, 19, 16,
    13, 12, 10, 9, 8, 7, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
  -- a(23) = 9510425471055777937262;  exponents 2 .. 73
  (9510425471055777937262,
   [97521410321, 21186862, 312284, 24867, 4602, 1379, 558, 276, 157, 99, 67, 49, 37, 29, 23, 19,
    16, 14, 12, 11, 9, 9, 8, 7, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
]

/-- The table has one entry per term `a(5), …, a(23)`. -/
theorem a000166RootBrackets_length : a000166RootBrackets.length = 19 := by decide

set_option maxRecDepth 100000 in
/-- **Kernel sweep.**  Every entry of the table is a complete root-bracket table for its term:
the size bound `a(n) < 2 ^ (len + 2)` holds, and every one of the 665 witnesses satisfies its
two strict inequalities.

`maxRecDepth` is raised for the `decide`: the elaborator recurses once per witness while
reducing `Nat.decidableBallLT`. -/
theorem a000166RootBrackets_valid :
    ∀ c ∈ a000166RootBrackets, c.1 < 2 ^ (c.2.length + 2) ∧ IsRootBracket c.1 c.2 := by
  decide

/-- **No term carried by the table is a perfect power.** -/
theorem not_isPerfectPower_of_mem_a000166RootBrackets {N : ℕ}
    (hN : N ∈ a000166RootBrackets.map Prod.fst) : ¬ IsPerfectPower N := by
  obtain ⟨c, hc, hEq⟩ := List.mem_map.1 hN
  obtain ⟨hsize, hbr⟩ := a000166RootBrackets_valid c hc
  rw [← hEq]
  exact not_isPerfectPower_of_isRootBracket hsize hbr

/-- Nonvacuity of `not_isPerfectPower_of_mem_a000166RootBrackets`: its hypothesis is inhabited,
e.g. at `a(5) = 44`. -/
example : ¬ IsPerfectPower 44 :=
  not_isPerfectPower_of_mem_a000166RootBrackets (by decide)

/-- Nonvacuity again at the largest pinned term `a(23) = 9510425471055777937262`, the value that
forces the table's 72-witness row. -/
example : ¬ IsPerfectPower 9510425471055777937262 :=
  not_isPerfectPower_of_mem_a000166RootBrackets (by decide)

/-- The table's keys are exactly `a(5), …, a(23)`: the pinned prefix splits as the four terms
below `4`, then the exception `a(4) = 9`, then the table. -/
theorem a000166Prefix_eq_append :
    a000166Prefix = [1, 0, 1, 2, 9] ++ a000166RootBrackets.map Prod.fst := by decide

/-- The exception is deliberately absent from the table — the sweep would be **false** if `9`
were an entry, since `9 = 3 ^ 2` admits no strict bracket at exponent `2`.  This is how the
sweep was checked to be load-bearing rather than trivially true. -/
theorem nine_notMem_a000166RootBrackets_keys :
    (9 : ℕ) ∉ a000166RootBrackets.map Prod.fst := by decide

/-- **The only perfect power among the pinned terms `a(0), …, a(23)` is `9`.**

Both directions, kernel-checked.  This is the arithmetic content of Sun's conjecture over the
prefix that the entry publishes, and it is complete over that prefix. -/
theorem isPerfectPower_iff_of_mem_a000166Prefix {N : ℕ} (hN : N ∈ a000166Prefix) :
    IsPerfectPower N ↔ N = 9 := by
  constructor
  · intro hpp
    have h4 : 4 ≤ N := four_le_of_isPerfectPower hpp
    rw [a000166Prefix_eq_append, List.mem_append] at hN
    rcases hN with hsmall | hbig
    · have hcases : N = 1 ∨ N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 9 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hsmall
      omega
    · exact absurd hpp (not_isPerfectPower_of_mem_a000166RootBrackets hbig)
  · rintro rfl
    exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

/-- Nonvacuity of `isPerfectPower_iff_of_mem_a000166Prefix` on its true side, at `a(4) = 9`. -/
example : IsPerfectPower 9 := (isPerfectPower_iff_of_mem_a000166Prefix (by decide)).2 rfl

/-- …and on its false side, at `a(23)`. -/
example : ¬ IsPerfectPower 9510425471055777937262 := fun h =>
  by have := (isPerfectPower_iff_of_mem_a000166Prefix (by decide)).1 h; omega

/-! ## The derangement numbers -/

/-- Mathlib's `numDerangements n` is the OEIS `name` read literally: the number of permutations
of an `n`-element set with no fixed points. -/
theorem numDerangements_eq_card_derangements (n : ℕ) :
    numDerangements n = Fintype.card (derangements (Fin n)) :=
  card_derangements_fin_eq_numDerangements.symm

set_option maxRecDepth 10000 in
/-- Ground truth for the OEIS `name` itself, by direct kernel enumeration: the kernel runs
through all `4! = 24` permutations of `Fin 4`, keeps the fixed-point-free ones, and counts `9`.

This corroborates the identification *without* using the recurrence at all — it counts the
actual set of permutations with no fixed points, which is what the `name` field says — and it
lands on the exceptional term `a(4) = 9` that the whole conjecture turns on. -/
example : Fintype.card (derangements (Fin 4)) = 9 := by decide

set_option maxRecDepth 40000 in
/-- The same at `Fin 5`, over all `5! = 120` permutations: `a(5) = 44`. -/
example : Fintype.card (derangements (Fin 5)) = 44 := by decide

/-- **Ground truth, kernel-checked.**  Mathlib's `numDerangements` reproduces the pinned `terms`
field exactly, all 24 entries `a(0), …, a(23)`.

Unlike the A000041 sibling — where `Fintype (Nat.Partition n)` enumerates compositions and gets
stuck in the kernel, so the identification had to be left to a compiler-level `#guard` —
`numDerangements` is a two-step structural recursion and reduces here outright. -/
theorem map_numDerangements_range_eq_a000166Prefix :
    (List.range 24).map numDerangements = a000166Prefix := by decide

/-- Every `a(n)` with `n < 24` is a term of the pinned prefix. -/
theorem numDerangements_mem_a000166Prefix {n : ℕ} (hn : n < 24) :
    numDerangements n ∈ a000166Prefix := by
  rw [← map_numDerangements_range_eq_a000166Prefix]
  exact List.mem_map_of_mem (List.mem_range.2 hn)

/-- Among the pinned indices, `9` occurs exactly once, at `n = 4`. -/
theorem numDerangements_eq_nine_iff_of_lt_24 : ∀ n < 24, (numDerangements n = 9 ↔ n = 4) := by
  decide

/-- **The exception is real: `a(4) = 9 = 3 ^ 2`.**  This is the "with a(4) = 3^2" half of Sun's
comment, and it is proved. -/
theorem isPerfectPower_numDerangements_four : IsPerfectPower (numDerangements 4) :=
  ⟨3, 2, by norm_num, by norm_num, by decide⟩

/-- **The dispatching brief's reading is false.**

The brief asked for "no derangement number `D(n)` for `n ≥ 3` is a perfect power".  `a(4) = 9`
refutes it, and the source itself names that exception. -/
theorem not_forall_not_isPerfectPower_numDerangements :
    ¬ ∀ n : ℕ, 3 ≤ n → ¬ IsPerfectPower (numDerangements n) := fun h =>
  h 4 (by norm_num) isPerfectPower_numDerangements_four

/-- `a(0) = 1`, `a(1) = 0`, `a(2) = 1` are all below `4`. -/
theorem numDerangements_lt_four_of_lt_three : ∀ n < 3, numDerangements n < 4 := by decide

/-- **The source's guard `n > 2` is removable.**  Under Sun's reading of "perfect power" the
three excluded indices carry nothing: `a(0) = a(2) = 1` and `a(1) = 0`, all below `4`. -/
theorem not_isPerfectPower_numDerangements_of_lt_three {n : ℕ} (hn : n < 3) :
    ¬ IsPerfectPower (numDerangements n) := by
  intro hpp
  have h4 : 4 ≤ numDerangements n := four_le_of_isPerfectPower hpp
  have hlt : numDerangements n < 4 := numDerangements_lt_four_of_lt_three n hn
  omega

/-- **Sun's conjecture, proved outright for every `n < 24`.**

That is the whole published prefix.  The guard `2 < n` is not needed on this range: the three
indices it excludes are covered by `not_isPerfectPower_numDerangements_of_lt_three`. -/
theorem sun_isPerfectPower_numDerangements_iff_of_lt_24 {n : ℕ} (hn : n < 24) :
    IsPerfectPower (numDerangements n) ↔ n = 4 := by
  rw [isPerfectPower_iff_of_mem_a000166Prefix (numDerangements_mem_a000166Prefix hn)]
  exact numDerangements_eq_nine_iff_of_lt_24 n hn

/-- Nonvacuity of `sun_isPerfectPower_numDerangements_iff_of_lt_24` on its true side. -/
example : IsPerfectPower (numDerangements 4) :=
  (sun_isPerfectPower_numDerangements_iff_of_lt_24 (by norm_num)).2 rfl

/-- …and on its false side, at `n = 23`. -/
example : ¬ IsPerfectPower (numDerangements 23) := fun h =>
  by have h4 : (23 : ℕ) = 4 := (sun_isPerfectPower_numDerangements_iff_of_lt_24 (by norm_num)).1 h
     omega

/-! ## The `±1` recurrence and the coprimality warm-up -/

/-- The `formulas` field's second recurrence, verbatim "a(n) = n*a(n-1) + (-1)^n", shifted to
`n + 1` so that no `ℕ`-subtraction appears.  Mathlib states it as `numDerangements_succ` with
the sign on the other side. -/
theorem numDerangements_succ_eq_mul_add_neg_one_pow (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * (numDerangements n : ℤ) + (-1) ^ (n + 1) := by
  rw [numDerangements_succ]; ring

/-- Ground truth for the recurrence at `n = 3`: `a(4) = 4 * a(3) + (-1)^4 = 8 + 1 = 9`. -/
example : (numDerangements 4 : ℤ) = 4 * (numDerangements 3 : ℤ) + (-1) ^ 4 := by decide

/-- **Consecutive derangement numbers are coprime**, for every `n`.

This is the warm-up the dispatching brief asked for, and it is immediate from the `±1`
recurrence: any common divisor `d` of `a(n)` and `a(n+1)` divides
`a(n+1) - (n+1) * a(n) = (-1)^(n+1)`, a unit.

It is worth stating precisely because it shows how little the recurrence gives: it pins the
*joint* arithmetic of consecutive terms completely, and still says nothing about whether any
single term is a perfect power. -/
theorem coprime_numDerangements_succ (n : ℕ) :
    Nat.Coprime (numDerangements n) (numDerangements (n + 1)) := by
  have key : ∀ d : ℕ, d ∣ numDerangements n → d ∣ numDerangements (n + 1) → d = 1 := by
    intro d hd1 hd2
    have h1 : (d : ℤ) ∣ (numDerangements n : ℤ) := Int.natCast_dvd_natCast.2 hd1
    have h2 : (d : ℤ) ∣ (numDerangements (n + 1) : ℤ) := Int.natCast_dvd_natCast.2 hd2
    have hunit : (d : ℤ) ∣ (-1) ^ n := by
      have hrw : ((-1 : ℤ)) ^ n
          = ((n : ℤ) + 1) * (numDerangements n : ℤ) - (numDerangements (n + 1) : ℤ) := by
        rw [numDerangements_succ]; ring
      rw [hrw]
      exact dvd_sub (h1.mul_left _) h2
    have hsq : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by rw [← mul_pow]; norm_num
    have hone : (d : ℤ) ∣ 1 := dvd_trans hunit ⟨(-1 : ℤ) ^ n, hsq.symm⟩
    have hnat : d ∣ 1 := by exact_mod_cast hone
    exact Nat.dvd_one.1 hnat
  exact key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

/-- Ground truth for the coprimality statement at a point where both terms exceed `1`, so that
it is not the trivial `gcd 1 _ = 1`: `gcd (a(5), a(6)) = gcd (44, 265) = 1`. -/
example : Nat.gcd (numDerangements 5) (numDerangements 6) = 1 := by decide

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

/-- **Joint satisfiability of the archived conjecture's hypotheses**, at `n = 4`: `2 < 4` and
`a(4) = 9 = 3 ^ 2`.  Proved `sorry`-free, so the `sorry` above is not standing over an empty
hypothesis set — there really is an `n` past the guard whose derangement number is a perfect
power, and the conjecture asserts that `4` is the only one. -/
example : 2 < 4 ∧ IsPerfectPower (numDerangements 4) :=
  ⟨by norm_num, isPerfectPower_numDerangements_four⟩

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

/-! ## Signature audit -/

#check @IsPerfectPower
#check @four_le_of_isPerfectPower
#check @IsRootBracket
#check @not_isPerfectPower_of_isRootBracket
#check @a000166Prefix
#check @a000166RootBrackets
#check @a000166RootBrackets_valid
#check @not_isPerfectPower_of_mem_a000166RootBrackets
#check @a000166Prefix_eq_append
#check @nine_notMem_a000166RootBrackets_keys
#check @isPerfectPower_iff_of_mem_a000166Prefix
#check @numDerangements_eq_card_derangements
#check @map_numDerangements_range_eq_a000166Prefix
#check @numDerangements_mem_a000166Prefix
#check @isPerfectPower_numDerangements_four
#check @not_forall_not_isPerfectPower_numDerangements
#check @not_isPerfectPower_numDerangements_of_lt_three
#check @sun_isPerfectPower_numDerangements_iff_of_lt_24
#check @numDerangements_succ_eq_mul_add_neg_one_pow
#check @coprime_numDerangements_succ
#check @sun_eq_four_of_isPerfectPower_numDerangements
#check @sun_isPerfectPower_numDerangements_iff
#check @sun_isPerfectPower_numDerangements_iff_all

/-! ## Axiom audit

Everything below is `{propext, Classical.choice, Quot.sound}` except the three declarations
downstream of the single intended `sorry` — `sun_eq_four_of_isPerfectPower_numDerangements`,
`sun_isPerfectPower_numDerangements_iff`, `sun_isPerfectPower_numDerangements_iff_all` — which
also report `sorryAx`. -/

#print axioms four_le_of_isPerfectPower
#print axioms not_isPerfectPower_of_isRootBracket
#print axioms a000166Prefix_length
#print axioms a000166RootBrackets_length
#print axioms a000166RootBrackets_valid
#print axioms not_isPerfectPower_of_mem_a000166RootBrackets
#print axioms a000166Prefix_eq_append
#print axioms nine_notMem_a000166RootBrackets_keys
#print axioms isPerfectPower_iff_of_mem_a000166Prefix
#print axioms numDerangements_eq_card_derangements
#print axioms map_numDerangements_range_eq_a000166Prefix
#print axioms numDerangements_mem_a000166Prefix
#print axioms numDerangements_eq_nine_iff_of_lt_24
#print axioms isPerfectPower_numDerangements_four
#print axioms not_forall_not_isPerfectPower_numDerangements
#print axioms numDerangements_lt_four_of_lt_three
#print axioms not_isPerfectPower_numDerangements_of_lt_three
#print axioms sun_isPerfectPower_numDerangements_iff_of_lt_24
#print axioms numDerangements_succ_eq_mul_add_neg_one_pow
#print axioms coprime_numDerangements_succ
#print axioms sun_eq_four_of_isPerfectPower_numDerangements
#print axioms sun_isPerfectPower_numDerangements_iff
#print axioms sun_isPerfectPower_numDerangements_iff_all

end A000166
