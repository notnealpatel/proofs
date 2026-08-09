import Mathlib

/-!
# A000041: Zhi-Wei Sun's conjecture that no partition number is a perfect power

## Source, pinned verbatim

Re-pulled with `goof oeis show A000041` on **2026-08-05**.

`id` (verbatim): `A000041`

`name` (verbatim):

> a(n) is the number of partitions of n (the partition numbers).

`keywords` (verbatim): `core,easy,nonn,nice,changed`

`terms` (verbatim, the whole field; line-wrapped here only, the field itself is one line):

> 1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231,297,385,490,627,792,1002,1255,
> 1575,1958,2436,3010,3718,4565,5604,6842,8349,10143,12310,14883,17977,21637,26015,
> 31185,37338,44583,53174,63261,75175,89134,105558,124754,147273,173525

The archived claim (verbatim, the whole line, from the `comments` field — entry 34 of 57):

> Conjecture: No a(n) has the form x^m with m > 1 and x > 1. - _Zhi-Wei Sun_, Dec 02 2013

The entry records **no** verification bound for this comment (contrast Sun's sibling
comment on A000166, which says "This has been verified for n <= 1000"), so no such
bound is claimed anywhere below.

## Indexing

The offset is `0`.  The `formulas` field pins it: "a(n) = Sum_{k=-inf..+inf} (-1)^k
a(n-k(3k-1)/2) with a(0)=1 and a(negative)=0".  So the `terms` field above is
`a(0), …, a(49)`, and `partitionNumber n = a(n)` needs no offset shim.

`Nat.Partition n` is Mathlib's type of multisets of positive naturals summing to `n`,
which is the OEIS `name` read literally, so `partitionNumber n :=
Fintype.card (Nat.Partition n)` is A000041 *by definition* rather than by numerical
coincidence.  `Fintype.card` does not depend on which `Fintype` instance is in scope
(`Fintype` is a `Subsingleton`), so the value is a property of the type alone.

## What is archived and what is proved

Archived with the single intended `sorry`:

* `sun_partitionNumber_not_isPerfectPower` — for every `n`, `partitionNumber n` is not
  of the form `x ^ m` with `1 < x` and `1 < m`.  This is the comment above.

Proved here, `sorry`-free and kernel-checked:

* `four_le_of_isPerfectPower` — every perfect power in this sense is at least `4`; this
  is what makes the source's `x > 1, m > 1` reading exclude `a(0) = a(1) = 1` for free.
* `isPerfectPower_iff_bounded` — the bounded, decidable reformulation: with
  `N < (S+1)^2` and `N < 2^(B+1)`, the search may be confined to
  `x ∈ [2, S]`, `m ∈ [2, B]`.
* `pow_notMem_a000041Prefix` — a kernel sweep: no `x ^ m` with `2 ≤ x ≤ 416`,
  `2 ≤ m ≤ 17`, `x ^ m < 173889 = 417 ^ 2` lies in the pinned 50-term prefix.
* `not_isPerfectPower_of_mem_a000041Prefix` — hence **no term of the pinned prefix
  `a(0), …, a(49)` is a perfect power**.  This is the arithmetic half of the
  conjecture's small-case verification, and it is complete for that prefix.
* `not_isPerfectPower_partitionNumber_of_mem_a000041Prefix` — the conjecture holds at
  every `n` whose partition number is a term of the pinned prefix.  This states the
  remaining gap explicitly: what is missing for `2 ≤ n ≤ 49` is only the *identification*
  `partitionNumber n ∈ a000041Prefix`, not any arithmetic.
* `sun_partitionNumber_zero`, `sun_partitionNumber_one` — the conjecture at `n = 0, 1`,
  end to end in the kernel (`partitionNumber 0 = partitionNumber 1 = 1`).
* `partitionNumber_pos`, `partitionNumber_le_succ`, `monotone_partitionNumber` — the
  monotone shell, via the explicit embedding `p ↦ 1 ::ₘ p.parts`.

## Why the identification step is not kernel-checked

Mathlib's `Fintype (Nat.Partition n)` is `Fintype.ofSurjective (ofComposition n)`, i.e.
enumerate all `2 ^ (n-1)` compositions of `n` and deduplicate.  Kernel reduction of that
instance gets stuck: `decide` on `Fintype.card (Nat.Partition 2) = 2` reports "reduction
got stuck at the `Decidable` instance".  Only `n = 0, 1` reduce, via the `Unique
(Partition 0)` and `Unique (Partition 1)` instances.  `native_decide` was not granted for
this file and is not used.

What is used instead is a `#guard` block: the compiler (not the kernel) evaluates
`(List.range 17).map partitionNumber` and compares it against the first 17 entries of the
pinned OEIS `terms` field.  `#guard` produces **no proof term**, so it contributes nothing
to any `#print axioms` result below and enlarges no trusted base; a false `#guard` is a
build error (checked: `#guard (Fintype.card (Nat.Partition 4) == 6)` fails with
"did not evaluate to `true`").  The range stops at `n = 16` because the composition
enumeration costs `2 ^ (n-1) · a(n)` multiset comparisons: `n ≤ 16` takes about five
seconds, `n ≤ 20` about three minutes.

## Deviations from the dispatching brief

* The brief quotes the claim as "No a(n) has the form x^m with m > 1 and x > 1", dropping
  the source's leading "Conjecture:".  The quoted text is otherwise byte-identical to the
  tail of the source line.  The source labels it a conjecture and so does this file.
* The in-tree card `Formalize/A000041-sun-perfect-power.md` adds a guard `n >= 1`.  The
  source carries no such guard and none is needed — `a(0) = a(1) = 1` and no perfect
  power in the source's sense is below `4` — so `sun_partitionNumber_not_isPerfectPower`
  quantifies over all `n : ℕ`.  That is strictly stronger than the card and faithful to
  the entry.
* `Proofs/Enumerative.lean` is not edited by this lane; the module import line is the
  orchestrator's to add.

## Computational orientation (not proofs)

`command -v sage` is empty on this machine, so no `sage` was used and none is claimed.
A plain `python3` dynamic program (no `sympy`, no external library) recomputed
`p(0), …, p(60)`, reproduced the pinned 50-term prefix byte for byte, and found no
perfect power among `p(0), …, p(60)`.  That run is orientation only; the kernel sweep
`pow_notMem_a000041Prefix` is what carries proof weight, and it covers exactly the
pinned prefix.
-/

set_option autoImplicit false

namespace A000041

/-! ## The perfect-power predicate

Mathlib has no perfect-power predicate: `leandoc IsPerfectPower` returns
`mode: "miss"`, and a search for "perfect power" surfaces only `PerfectField`,
`PerfectRing`, `Topology.Perfect` and the Mersenne/perfect-number archive.  So it is
defined here, minimally, in exactly Sun's phrasing. -/

/-- `IsPerfectPower N` says `N = x ^ m` for some `1 < x` and `1 < m`.

This is Sun's reading verbatim — "the form x^m with m > 1 and x > 1" — and both
strictness conditions are load-bearing: without `1 < m` every `N` is `N ^ 1`, and
without `1 < x` every `N ∈ {0, 1}` is `0 ^ 2` or `1 ^ 2`. -/
def IsPerfectPower (N : ℕ) : Prop := ∃ x m : ℕ, 1 < x ∧ 1 < m ∧ x ^ m = N

/-- Satisfiability of `IsPerfectPower`: `4 = 2 ^ 2`. -/
example : IsPerfectPower 4 := ⟨2, 2, by norm_num, by norm_num, by norm_num⟩

/-- Satisfiability again, at a value that is not a square: `8 = 2 ^ 3`. -/
example : IsPerfectPower 8 := ⟨2, 3, by norm_num, by norm_num, by norm_num⟩

/-- **Every perfect power is at least `4`.**

`2 ^ 2` is the smallest value the predicate admits.  This is what makes Sun's
`x > 1, m > 1` phrasing exclude `a(0) = a(1) = 1` with no side condition: the conjecture
needs no `n ≥ 1` guard. -/
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

/-! ## A bounded, decidable reformulation -/

/-- **Bounded search for a perfect power.**  If `N < (S + 1) ^ 2` and `N < 2 ^ (B + 1)`,
then `N` is a perfect power exactly when some `x ∈ [2, S]` and `m ∈ [2, B]` have
`x ^ m = N`.

Both bounds come from `x ^ m = N` with `2 ≤ x`, `2 ≤ m`: the base satisfies
`x ^ 2 ≤ x ^ m = N`, and the exponent satisfies `2 ^ m ≤ x ^ m = N`.

The natural closed forms are `S = Nat.sqrt N` and `B = Nat.log 2 N`, but they are carried
as hypotheses instead.  `Nat.sqrt` would defeat the purpose outright: its auxiliary
`Nat.sqrt.iter` is well-founded (`termination_by guess`), and `decide` on
`Nat.sqrt 173525 = 416` fails with "reduction got stuck at the `Decidable` instance".
`Nat.log` does reduce — it is structural in a fuel argument, and `decide` on
`Nat.log 2 173525 = 17` succeeds — but keeping both bounds parametric makes the search
box visible at each call site and independent of either implementation. -/
theorem isPerfectPower_iff_bounded {N S B : ℕ} (hS : N < (S + 1) ^ 2) (hB : N < 2 ^ (B + 1)) :
    IsPerfectPower N ↔ ∃ x ∈ Finset.Icc 2 S, ∃ m ∈ Finset.Icc 2 B, x ^ m = N := by
  constructor
  · rintro ⟨x, m, hx, hm, rfl⟩
    have hbase : x ^ 2 ≤ x ^ m := Nat.pow_le_pow_right (by omega) hm
    have hexp : 2 ^ m ≤ x ^ m := Nat.pow_le_pow_left hx m
    refine ⟨x, Finset.mem_Icc.2 ⟨hx, ?_⟩, m, Finset.mem_Icc.2 ⟨hm, ?_⟩, rfl⟩
    · by_contra hcon
      have hbig : (S + 1) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    · by_contra hcon
      have hbig : 2 ^ (B + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · rintro ⟨x, hxmem, m, hmmem, rfl⟩
    obtain ⟨hx, -⟩ := Finset.mem_Icc.1 hxmem
    obtain ⟨hm, -⟩ := Finset.mem_Icc.1 hmmem
    exact ⟨x, m, by omega, by omega, rfl⟩

/-- Joint satisfiability of the two bound hypotheses of `isPerfectPower_iff_bounded`,
at a point where the conclusion is genuinely `True` rather than vacuous:
`N = 4`, `S = 2`, `B = 2` gives `4 < 9` and `4 < 8`, and `2 ^ 2 = 4` is found. -/
example : IsPerfectPower 4 ↔ ∃ x ∈ Finset.Icc 2 2, ∃ m ∈ Finset.Icc 2 2, x ^ m = 4 :=
  isPerfectPower_iff_bounded (S := 2) (B := 2) (by norm_num) (by norm_num)

/-! ## The pinned OEIS prefix carries no perfect power -/

/-- The `terms` field of OEIS A000041 as pulled on 2026-08-05, transcribed in order:
`a(0), a(1), …, a(49)`. -/
def a000041Prefix : List ℕ :=
  [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297, 385, 490,
   627, 792, 1002, 1255, 1575, 1958, 2436, 3010, 3718, 4565, 5604, 6842, 8349, 10143,
   12310, 14883, 17977, 21637, 26015, 31185, 37338, 44583, 53174, 63261, 75175, 89134,
   105558, 124754, 147273, 173525]

/-- The pinned prefix has the 50 entries `a(0), …, a(49)`. -/
theorem a000041Prefix_length : a000041Prefix.length = 50 := by decide

/-- Every entry of the pinned prefix is below `173889 = 417 ^ 2`; the largest is
`a(49) = 173525`. -/
theorem a000041Prefix_lt : ∀ N ∈ a000041Prefix, N < 173889 := by decide

set_option maxRecDepth 10000 in
/-- **Kernel sweep.**  No perfect power below `173889 = 417 ^ 2` is a term of the pinned
prefix: for every base `2 ≤ x ≤ 416` and exponent `2 ≤ m ≤ 17` with `x ^ m < 173889`,
the value `x ^ m` is not in `a000041Prefix`.

The `x ^ m < 173889` guard is not a weakening — `isPerfectPower_iff_bounded` only ever
supplies pairs with `x ^ m` equal to a term, hence below `173889` — but it cuts the
kernel cost by about a factor of eight (measured: `28 s` down to `3 s`), because only
`522` of the `415 · 16 = 6640` pairs `(x, m)` clear the size test and reach a list scan.

`maxRecDepth` is raised for the `decide`: the elaborator recurses once per element of
`Finset.Icc 2 416` while reducing the decidability instance. -/
theorem pow_notMem_a000041Prefix :
    ∀ x ∈ Finset.Icc 2 416, ∀ m ∈ Finset.Icc 2 17, x ^ m < 173889 → x ^ m ∉ a000041Prefix := by
  decide

/-- Nonvacuity of `pow_notMem_a000041Prefix`: the quantifier domain is inhabited and the
size guard is satisfiable, at `x = m = 2` with `2 ^ 2 = 4 < 173889`.  So the sweep really
searches; it is not an empty statement about an empty family. -/
example : ∃ x ∈ Finset.Icc 2 416, ∃ m ∈ Finset.Icc 2 17, x ^ m < 173889 ∧ x ^ m = 4 := by
  decide

/-- …and the sweep is consistent only because `4` is not a partition number: planting `4`
(or `1024 = 2 ^ 10`) into `a000041Prefix` makes `decide` report
`pow_notMem_a000041Prefix` **false**, which is how the sweep was checked to be
load-bearing rather than trivially true. -/
example : (4 : ℕ) ∉ a000041Prefix ∧ (1024 : ℕ) ∉ a000041Prefix := by decide

/-- **No term of the pinned OEIS prefix `a(0), …, a(49)` is a perfect power.**

This is the arithmetic content of Sun's conjecture over the prefix that the entry
publishes, and it is complete over that prefix. -/
theorem not_isPerfectPower_of_mem_a000041Prefix {N : ℕ} (hN : N ∈ a000041Prefix) :
    ¬ IsPerfectPower N := by
  intro hpp
  have hlt : N < 173889 := a000041Prefix_lt N hN
  have hS : N < (416 + 1) ^ 2 := by
    rw [show ((416 : ℕ) + 1) ^ 2 = 173889 by norm_num]; exact hlt
  have hB : N < 2 ^ (17 + 1) := by
    rw [show (2 : ℕ) ^ (17 + 1) = 262144 by norm_num]; omega
  obtain ⟨x, hxmem, m, hmmem, hxm⟩ := (isPerfectPower_iff_bounded hS hB).1 hpp
  refine pow_notMem_a000041Prefix x hxmem m hmmem ?_ ?_
  · rw [hxm]; exact hlt
  · rw [hxm]; exact hN

/-- Nonvacuity of `not_isPerfectPower_of_mem_a000041Prefix`: its hypothesis is
inhabited, e.g. at `a(4) = 5`. -/
example : ¬ IsPerfectPower 5 := not_isPerfectPower_of_mem_a000041Prefix (by decide)

/-- Nonvacuity again at the largest pinned term `a(49) = 173525`, the value that fixes
the sweep bounds `S = 416`, `B = 17`. -/
example : ¬ IsPerfectPower 173525 := not_isPerfectPower_of_mem_a000041Prefix (by decide)

/-! ## The partition numbers -/

/-- `partitionNumber n` is OEIS A000041 `a(n)`: the number of partitions of `n`, i.e.
the number of multisets of positive naturals summing to `n`.

This is Mathlib's `Nat.Partition n` counted by `Fintype.card`; `partitionNumber_eq_card`
records that the alias is definitional. -/
def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The alias is definitional: `partitionNumber n` *is* `Fintype.card (Nat.Partition n)`. -/
theorem partitionNumber_eq_card (n : ℕ) : partitionNumber n = Fintype.card (Nat.Partition n) :=
  rfl

/-! Ground truth against the pinned `terms` field, `a(0), …, a(16)`.

Compiler-evaluated, not kernel-checked: see the "Why the identification step is not
kernel-checked" section of the module docstring.  `#guard` emits no proof term, so it
appears in no `#print axioms` result; a mismatch is a build error. -/

#guard (List.range 17).map partitionNumber == a000041Prefix.take 17

/-- Ground truth, kernel-checked: `a(0) = 1`.  `Nat.Partition 0` is `Unique` (the empty
multiset is its only element), so this reduces where larger `n` do not. -/
theorem partitionNumber_zero : partitionNumber 0 = 1 := by decide

/-- Ground truth, kernel-checked: `a(1) = 1`.  `Nat.Partition 1` is `Unique` (`{1}` is its
only element). -/
theorem partitionNumber_one : partitionNumber 1 = 1 := by decide

/-- Adjoining a part `1` embeds the partitions of `n` into the partitions of `n + 1`. -/
def consOne (n : ℕ) (p : Nat.Partition n) : Nat.Partition (n + 1) where
  parts := 1 ::ₘ p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.1 hi with rfl | hmem
    · exact Nat.one_pos
    · exact p.parts_pos hmem
  parts_sum := by
    rw [Multiset.sum_cons, p.parts_sum, Nat.add_comm]

example : (consOne 0 default).parts = ({1} : Multiset ℕ) := rfl

/-- `consOne` is injective: it is `Multiset.cons 1` on the underlying multisets. -/
theorem consOne_injective (n : ℕ) : Function.Injective (consOne n) := by
  intro p q hpq
  have hparts : (1 : ℕ) ::ₘ p.parts = 1 ::ₘ q.parts := congrArg Nat.Partition.parts hpq
  exact Nat.Partition.ext ((Multiset.cons_inj_right 1).1 hparts)

/-- `a(n)` is positive: `Nat.Partition n` is inhabited by the one-part partition
(`Nat.Partition.indiscrete`, the empty multiset when `n = 0`). -/
theorem partitionNumber_pos (n : ℕ) : 0 < partitionNumber n := Fintype.card_pos

/-- `a(n) ≤ a(n+1)`, via the embedding `consOne`. -/
theorem partitionNumber_le_succ (n : ℕ) : partitionNumber n ≤ partitionNumber (n + 1) :=
  Fintype.card_le_of_injective (consOne n) (consOne_injective n)

/-- The partition numbers are monotone. -/
theorem monotone_partitionNumber : Monotone partitionNumber :=
  monotone_nat_of_le_succ partitionNumber_le_succ

/-! ## The conjecture -/

/-- **Sun's perfect-power conjecture for the partition numbers (OEIS A000041).**

Verbatim from the entry's `comments` field, pulled 2026-08-05:

> Conjecture: No a(n) has the form x^m with m > 1 and x > 1. - _Zhi-Wei Sun_,
> Dec 02 2013

No guard on `n` is needed: `a(0) = a(1) = 1` and no perfect power in Sun's sense is
below `4` (`four_le_of_isPerfectPower`), so the two degenerate indices are covered by
the same statement — see `sun_partitionNumber_zero` and `sun_partitionNumber_one`,
which are proved.

**Status: open.**  This is the single intended `sorry` of the file.  The entry publishes
no verification bound for this comment; what is verified here is
`not_isPerfectPower_of_mem_a000041Prefix`, which rules out every term of the pinned
50-term prefix `a(0), …, a(49)`, together with the compiler-checked identification
`partitionNumber n = a(n)` for `n ≤ 16`.

**Why it is hard.**  A proof must control the arithmetic of `p(n)` uniformly in `n`, and
the two handles the A000041 entry itself supplies are the wrong shape for that.

*Congruential.*  In a bracketed note on Forberg's comment about primes dividing
partition numbers, the entry cites Ono (verbatim): "The existence of such partition
numbers follows from Ono's proof (see his paper "Distribution of the partition function
modulo m"). - _Ralf Stephan_, Jan 28 2026" — "such partition numbers" refers to
partition numbers divisible by a given prime, not to perfect powers.  A congruence rules
out a residue class of *values*, but `m`-th
powers occupy every residue class that contains an `m`-th power residue, so no fixed
modulus can exclude them all.

*Analytic.*  The entry's `formulas` field records (verbatim) "a(n) ~
1/(4*n*sqrt(3)) * e^(Pi * sqrt(2n/3)) as n -> infinity (Hardy and Ramanujan). See
A050811."  Even the exact Rademacher refinement of that expansion only locates `p(n)` as
the nearest integer to a transcendental sum, which says nothing about whether that
integer is an `m`-th power.

The same obstruction blocks the sibling conjecture on A000166 (derangements,
`Proofs/Scratch/Candidates/A000166SunPerfectPower.lean`) and Brocard's problem
(`Proofs/Scratch/Candidates/A146968Brocard.lean`). -/
theorem sun_partitionNumber_not_isPerfectPower (n : ℕ) :
    ¬ IsPerfectPower (partitionNumber n) := by
  sorry

/-! ## What the sweep gives unconditionally -/

/-- **Sun's conjecture at every `n` whose partition number is a pinned term.**

Kernel-checked.  The hypothesis isolates exactly what is missing for `2 ≤ n ≤ 49`: the
*identification* of `partitionNumber n` with an OEIS term, which the `#guard` block above
checks with the compiler for `n ≤ 16` and which the kernel cannot check at all through
Mathlib's composition-enumeration `Fintype` instance.  No arithmetic is missing. -/
theorem not_isPerfectPower_partitionNumber_of_mem_a000041Prefix {n : ℕ}
    (hn : partitionNumber n ∈ a000041Prefix) : ¬ IsPerfectPower (partitionNumber n) :=
  not_isPerfectPower_of_mem_a000041Prefix hn

/-- The conjecture at `n = 0`, end to end in the kernel: `a(0) = 1 < 4`. -/
theorem sun_partitionNumber_zero : ¬ IsPerfectPower (partitionNumber 0) := by
  intro hpp
  have h4 : 4 ≤ partitionNumber 0 := four_le_of_isPerfectPower hpp
  rw [partitionNumber_zero] at h4
  omega

/-- The conjecture at `n = 1`, end to end in the kernel: `a(1) = 1 < 4`. -/
theorem sun_partitionNumber_one : ¬ IsPerfectPower (partitionNumber 1) := by
  intro hpp
  have h4 : 4 ≤ partitionNumber 1 := four_le_of_isPerfectPower hpp
  rw [partitionNumber_one] at h4
  omega

/-- The hypothesis of `not_isPerfectPower_partitionNumber_of_mem_a000041Prefix` is
inhabited in the kernel at `n = 0`, so that theorem is not vacuous. -/
example : ¬ IsPerfectPower (partitionNumber 0) :=
  not_isPerfectPower_partitionNumber_of_mem_a000041Prefix
    (by rw [partitionNumber_zero]; decide)

/-- And at `n = 1`. -/
example : ¬ IsPerfectPower (partitionNumber 1) :=
  not_isPerfectPower_partitionNumber_of_mem_a000041Prefix
    (by rw [partitionNumber_one]; decide)

/-! ## Signature audit -/

#check @IsPerfectPower
#check @four_le_of_isPerfectPower
#check @isPerfectPower_iff_bounded
#check @a000041Prefix
#check @pow_notMem_a000041Prefix
#check @not_isPerfectPower_of_mem_a000041Prefix
#check @partitionNumber
#check @partitionNumber_eq_card
#check @partitionNumber_zero
#check @partitionNumber_one
#check @partitionNumber_pos
#check @partitionNumber_le_succ
#check @monotone_partitionNumber
#check @sun_partitionNumber_not_isPerfectPower
#check @not_isPerfectPower_partitionNumber_of_mem_a000041Prefix
#check @sun_partitionNumber_zero
#check @sun_partitionNumber_one

/-! ## Axiom audit

Everything below is `{propext, Classical.choice, Quot.sound}` except
`sun_partitionNumber_not_isPerfectPower`, the single intended `sorry`, which also
reports `sorryAx`. -/

#print axioms four_le_of_isPerfectPower
#print axioms isPerfectPower_iff_bounded
#print axioms a000041Prefix_length
#print axioms a000041Prefix_lt
#print axioms pow_notMem_a000041Prefix
#print axioms not_isPerfectPower_of_mem_a000041Prefix
#print axioms partitionNumber_eq_card
#print axioms partitionNumber_zero
#print axioms partitionNumber_one
#print axioms consOne_injective
#print axioms partitionNumber_pos
#print axioms partitionNumber_le_succ
#print axioms monotone_partitionNumber
#print axioms not_isPerfectPower_partitionNumber_of_mem_a000041Prefix
#print axioms sun_partitionNumber_zero
#print axioms sun_partitionNumber_one
#print axioms sun_partitionNumber_not_isPerfectPower

end A000041
