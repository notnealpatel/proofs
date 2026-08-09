/-
# A000041 — Sun: additive representation by `p(k) + 2` with a divisibility antichain

## OEIS source (re-pulled verbatim with `goof oeis show A000041`, 2026-08-05)

```
NAME:     a(n) is the number of partitions of n (the partition numbers).
TERMS:    1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231,297,385,490,627,792,
          1002,1255,1575,1958,2436,3010,3718,4565,5604,6842,8349,10143,12310,
          14883,17977,21637,26015,31185,37338,44583,53174,63261,75175,89134
KEYWORDS: core,nonn,nice,easy
COMMENT (the conjecture carded here):
  Conjecture: Each integer n > 2 different from 6 can be written as a sum of
  finitely many numbers of the form a(k) + 2 (k > 0) with no summand dividing
  another. This has been verified for n <= 7140. - _Zhi-Wei Sun_, May 16 2023
COMMENT (the sibling conjecture, carded elsewhere — NOT this one):
  Conjecture: No a(n) has the form x^m with m > 1 and x > 1.
  - _Zhi-Wei Sun_, Dec 02 2013
```

`%O A000041 0,3` — offset `0`, `a(0) = 1`.

## Distinctness from the carded sibling

`Formalize/` already carries the A000041 **perfect-power** conjecture
(Sun, Dec 02 2013).  This card is the **additive-representation** conjecture
(Sun, May 16 2023), which is a different claim about the same sequence.
The two are quoted side by side above so the distinction is auditable.

## The summand set

`k > 0`, so the allowed summands are `p(k) + 2` for `k ≥ 1`:

```
p(1)+2 = 3,  p(2)+2 = 4,  p(3)+2 = 5,  p(4)+2 = 7,  p(5)+2 = 9,
p(6)+2 = 13, p(7)+2 = 17, p(8)+2 = 24, p(9)+2 = 32, p(10)+2 = 44, …
```

Note `p(1) = p(2)`? No: `p(1) = 1`, `p(2) = 2`, so the summands `3` and `4` are
distinct.  The set is `{3, 4, 5, 7, 9, 13, 17, 24, 32, 44, 58, 79, …}`.

"with no summand dividing another" is a **divisibility antichain** condition.
Since `x ∣ x`, a repeated summand violates it, so the summands are automatically
distinct — the representation is by a *set*, not a multiset.  (A single summand
satisfies the condition vacuously.)

DATA-driven checks of the guards:
* `n = 3, 4, 5, 7, 9`: single summands. ✓
* `n = 6`: the only options are `3 + 3` (violates: `3 ∣ 3`) and nothing else
  (`4 + 2`, `5 + 1` use non-summands).  So `6` genuinely fails — **that is why
  the source excludes it**, and it makes the exclusion load-bearing rather than
  cosmetic.
* `n = 8 = 3 + 5` ✓ (`3 ∤ 5`, `5 ∤ 3`).
* `n = 12 = 5 + 7` ✓ (note `3 + 9` fails: `3 ∣ 9`).
* `n = 15 = 3 + 5 + 7` ✓.
* `n = 1, 2`: below the `n > 2` guard; the smallest summand is `3`.

## Status

Open (May 2023).  Verified for `n ≤ 7140`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A000041Antichain

/-! ## Definition layer

`leandoc` findings:

* `Nat.Partition (n : ℕ) : Type` — Mathlib's partition **structure**, and
  `Nat.Partition.partitions` etc.  There is a partition *counting* function:
  `Nat.Partition.instFintype` gives `Fintype (Nat.Partition n)`, so
  `Fintype.card (Nat.Partition n)` **is** `p(n)`.  Mathlib also has
  `Nat.partitionsGF`-adjacent generating-function material in
  `Mathlib/Combinatorics/Enumerative/Partition.lean` and
  `Mathlib/NumberTheory/Partition.lean` (Euler's theorem: partitions into odd
  parts = partitions into distinct parts).
  **STYLE.md warns against mixing cardinality APIs** — this card uses
  `Nat.card (Nat.Partition n)` nowhere and `Fintype.card` consistently.
* `Finset`, `Finset.sum`, `Finset.image`; `Nat.dvd`.
* No antichain-under-divisibility predicate exists; `IsAntichain` does exist
  (`IsAntichain (· ∣ ·) s` for `s : Set ℕ`), which is exactly right and is used.

**Definitional-fidelity note.**  Using `Fintype.card (Nat.Partition k)` for
`p(k)` ties the card to Mathlib's semantic definition of a partition rather than
to a recurrence, which is what a statement audit wants.  The sanity layer checks
it against the DATA line. -/

/-- `p(n)`, the number of partitions of `n`, via Mathlib's `Nat.Partition`. -/
noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The allowed summands: `p(k) + 2` for `k ≥ 1`. -/
def IsSummand (m : ℕ) : Prop := ∃ k : ℕ, 0 < k ∧ m = p k + 2

/-- `n` is representable: a **finite set** `S` of allowed summands, forming a
divisibility antichain, with `Σ S = n`.

`Finset` rather than `Multiset` is correct here: `x ∣ x`, so the antichain
condition already forbids repeats.  `IsAntichain (· ∣ ·) (S : Set ℕ)` is
Mathlib's spelling and is what "no summand dividing another" means. -/
def Representable (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧ (∀ m ∈ S, IsSummand m) ∧
    IsAntichain (· ∣ ·) (S : Set ℕ) ∧ ∑ m ∈ S, m = n

/-! ## The conjecture -/

/-- **Sun's additive-antichain conjecture (A000041, Zhi-Wei Sun, May 16 2023).**

Verbatim: "Conjecture: Each integer n > 2 different from 6 can be written as a
sum of finitely many numbers of the form a(k) + 2 (k > 0) with no summand
dividing another. This has been verified for n <= 7140."

Both guards are load-bearing and both are *refutations*, not degeneracies:
* `n ≤ 2`: the smallest summand is `3`, so `1` and `2` are not representable.
* `n = 6`: the only candidate is `3 + 3`, which the antichain condition forbids.

**Mathlib primitives available.**  `Nat.Partition` and `Fintype.card`;
`IsAntichain` and its API (`IsAntichain.subset`, `IsAntichain.insert`);
`Finset.sum_insert`, `Finset.sum_le_sum`;
`Nat.Partition.card_partitions`-adjacent results are thin — Mathlib has Euler's
odd/distinct theorem and the pentagonal number theorem is **not** there, so any
quantitative input about `p(k)` would have to come from Hardy–Ramanujan, which
Mathlib also lacks.

**Sketch of an attack.**  The summand set `{3, 4, 5, 7, 9, 13, 17, 24, 32, 44, …}`
grows sub-exponentially (`p(k) ~ e^{π√(2k/3)}/(4k√3)`, so the summands are
`e^{Θ(√k)}`), which means the set has *super-logarithmic* density on a log
scale — enough for a greedy representation to plausibly always exist.  The
antichain condition is the obstruction: greedy picks large summands first, and
one must avoid divisibility relations.  Since the summands are mostly not
smooth, divisibility collisions are rare, but "rare" is not "never" and there is
no structure theorem for `p(k) + 2` modulo small primes (that would be a strong
statement about partition-number congruences, and Ramanujan's congruences go the
*other* way — they exhibit divisibility, e.g. `5 ∣ p(5k+4)`).

**Honest assessment.**  This is the weakest candidate in the sweep: the
statement is fiddly, the sanity layer does not reduce to a clean `native_decide`
(the search is over antichains, i.e. subsets), and no partial result is in
reach.  The candidates document already says "marginal", and that is right.

**Tactic families.**  `decide` on tiny cases; `IsAntichain` simp lemmas;
`Finset.sum_insert` + `interval_cases` for a bounded greedy search;
`Nat.Partition` is not computable in a useful way, so the sanity layer uses the
*numeric* summand list instead — see below.

**Related work in this repo.** The carded A000041 perfect-power conjecture
(a *different* Sun conjecture, `Formalize/`).  Adjacent in this directory:
`A000166SunPerfectPower.lean` (the derangement analogue of the sibling). -/
theorem sun_a000041_antichain (n : ℕ) (hn : 2 < n) (h6 : n ≠ 6) : Representable n := by
  sorry

/-- The two exclusions, as **refutations** rather than guards — these are finite
claims and should be proved, since they are what justify the guards. -/
theorem not_representable_one : ¬ Representable 1 := by sorry
theorem not_representable_two : ¬ Representable 2 := by sorry
theorem not_representable_six : ¬ Representable 6 := by sorry

/-! ## Sanity layer

`p` is `noncomputable` (`Fintype.card` of a structure), so no `decide` can see
it.  The sanity layer therefore works with the explicit numeric summand list and
cross-checks it against the DATA line separately. -/

/-- The first summands, `p(k) + 2` for `k = 1..16`, transcribed from the
A000041 DATA line `1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231,…`
(offset `0`, so `p(1) = 1, p(2) = 2, p(3) = 3, p(4) = 5, …`). -/
def summandList : List ℕ :=
  [3, 4, 5, 7, 9, 13, 17, 24, 32, 44, 58, 79, 103, 137, 178, 233]

-- PROVABLE: the summand list really is `p(k) + 2`.  This is the transcription
-- audit; without it the whole sanity layer is about the wrong numbers.
theorem summandList_eq :
    summandList = (List.range' 1 16).map (fun k => p k + 2) := by
  sorry

-- PROVABLE: `p` ground truth against the DATA line.
example : p 0 = 1 := by sorry
example : p 1 = 1 := by sorry
example : p 5 = 7 := by sorry
example : p 10 = 42 := by sorry

-- PROVABLE: satisfiability — small representations, using the numeric list.
--   8 = 3 + 5,  12 = 5 + 7,  15 = 3 + 5 + 7
example : ∑ m ∈ ({3, 5} : Finset ℕ), m = 8 := by decide
example : ∑ m ∈ ({5, 7} : Finset ℕ), m = 12 := by decide
example : ∑ m ∈ ({3, 5, 7} : Finset ℕ), m = 15 := by decide

-- PROVABLE: those really are antichains under divisibility.
example : IsAntichain (· ∣ ·) (({3, 5, 7} : Finset ℕ) : Set ℕ) := by decide

-- PROVABLE: the `n = 6` exclusion, stated as a real refutation.
-- `6` is not a sum of a nonempty divisibility-antichain of summands: the only
-- numeric option is `3 + 3`, which is a *repeat*, and `Finset` cannot hold a
-- repeat, so the only single-element candidate summing to `6` would have to be
-- the summand `6` itself — which is not in `summandList`.
-- (An earlier draft here had a vacuous `¬ P → False` example that proved
-- nothing; caught by the adversarial reviewer.)
example : ¬ ∃ S ∈ (summandList.toFinset).powerset,
    S.Nonempty ∧ IsAntichain (· ∣ ·) (S : Set ℕ) ∧ ∑ m ∈ S, m = 6 := by
  native_decide

-- PROVABLE: and the reason the *multiset* reading would differ — `3 ∣ 3`, so
-- `{3, 3}` is not an antichain under divisibility either way.
example : (3 : ℕ) ∣ 3 := by decide

-- PROVABLE: the `n > 2` guard.  The smallest summand is `3`, so no nonempty sum
-- of summands is `1` or `2`.
example : ∀ m ∈ summandList, 3 ≤ m := by decide

-- PROVABLE: `12 = 3 + 9` is *not* a valid representation, because `3 ∣ 9`.
-- This is the check that the antichain condition actually bites — without it
-- the conjecture would be much weaker and probably easy.
example : ¬ IsAntichain (· ∣ ·) (({3, 9} : Finset ℕ) : Set ℕ) := by decide

-- PROVABLE (window check): every `3 ≤ n ≤ 900` with `n ≠ 6` has a representation
-- from `summandList`.  The search is over antichain subsets of a 16-element
-- list, i.e. `2^16 = 65536` subsets — comfortable.
--
-- **The bound `900` is not arbitrary and must not be raised naively.**  The
-- largest achievable antichain sum from these 16 summands is `939`, and the
-- first `n` with no representation is `911`; twelve values in `[911, 939]` fail
-- and everything above `939` is out of range.  So `910` is the exact cutoff for
-- this summand list.  (An earlier draft used a 12-summand list with a `300`
-- bound, which was **false** — that list tops out at `288` and already fails at
-- `260`.  Caught by the adversarial reviewer.)  To go further, extend
-- `summandList` with `p(17)+2 = 299`, `p(18)+2 = 387`, … first.
example : ∀ n ∈ Finset.Icc 3 900, n ≠ 6 →
    ∃ S ∈ (summandList.toFinset).powerset,
      S.Nonempty ∧ IsAntichain (· ∣ ·) (S : Set ℕ) ∧ ∑ m ∈ S, m = n := by
  native_decide

/-! ## Notes for a follow-up card

The candidates document's "marginal" rating stands.  Concretely:

* The only cheap deliverables are `not_representable_one/two/six` — finite
  refutations that justify the guards, and they are worth having because they
  turn the source's parenthetical exclusions into machine-checked facts.
* `summandList_eq` and the `p` ground truths require `Nat.Partition` evaluation,
  which is `noncomputable`; the practical route is a computable partition
  counter with a proved bridge, mirroring `complexityRec` in
  `NumberComplexity.IntComplexity`.  That is real work for little payoff here.
* The conjecture itself is out of reach and no partial result is in sight.

**Recommendation: card it for the archive, do not schedule proof work.** -/

/-!
## Adversarial review verdict — **FLAG, two defects, both FIXED**

Independent re-pull of A000041 plus exhaustive antichain computation,
2026-08-05.

**Defect 1 (HIGH, FIXED).**  The window check claimed every `3 ≤ n ≤ 300` with
`n ≠ 6` is representable from a **12**-summand list.  That is **false**: those
summands top out at an antichain sum of `288`, and the first failure is at
`n = 260` (twelve values in `[260, 288]` fail, and `289..300` are out of range
entirely).  `native_decide` would have rejected it.  **Fixed** by extending
`summandList` to `k = 1..16` (adding `103, 137, 178, 233`) and setting the
sweep to `[3, 900]` — recomputed exactly: the extended list reaches `939` and
first fails at `911`, so `910` is the true cutoff.  The bound is now annotated
with that reasoning so it cannot be raised naively again.

**Defect 2 (MEDIUM, FIXED).**  The `n = 6` exclusion `example` was
`¬ IsAntichain … {3} → False`, which is vacuously true (`{3}` *is* an antichain,
so the hypothesis is `False`) and proved nothing.  Replaced with a genuine
`native_decide` refutation over all antichain subsets of `summandList`.

Confirmed:
* Sun's May 16 2023 comment is verbatim, and is a **different** conjecture from
  the Dec 02 2013 perfect-power one; `%O A000041 0,3`.
* `summandList = p(k) + 2` for `k = 1..16`, checked term by term.
* `n = 1, 2, 6` are genuinely non-representable — so all three guards are
  refutations, not degeneracies.
* `Nat.Partition` exists with a `Fintype` instance, so
  `Fintype.card (Nat.Partition n) = p(n)`.
* `IsAntichain r s` is `s.Pairwise rᶜ` over **distinct** elements, so `x ∣ x`
  causes no trouble and singletons are vacuously antichains — the card's
  reasoning about `Finset`-vs-`Multiset` is correct.
-/

end Candidates.A000041Antichain
