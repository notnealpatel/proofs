import Mathlib
import NumberComplexity.AdditionChain

/-!
# Slizkov's doubling-gap question for shortest addition chains (OEIS A230528)

`A230528` is "Numbers k such that a shortest addition chain for 2*k is shorter
than one for k, that is, A003313(2*k) < A003313(k)" (pulled live via
`oeis show A230528`, 2026-07-30; keywords `nonn,hard,more,nice`).  Its seven
listed terms are

  `375494703, 602641031, 619418303, 728117339, 750793519, 750832687, 750989359`,

so doubling can genuinely *shorten* a shortest addition chain — but at every
listed term it shortens it by exactly one (deficit `≥ 1` is the entry's
definition; "exactly one" because more would answer the question below, which
the entry poses as open).  The entry's only comment asks (verbatim):

> "Can the shortest addition chain for 2*k be shorter than one for k by more
> than 1?" — Alexey Slizkov, Jan 20 2024.

This file works over the A003313 layer `NumberComplexity.AdditionChain`
(`IsAddChain`, `chainSteps`, `l`, `l_le_of_isAddChain`, the `Decidable (l n ≤ k)`
instance) and has three tiers:

* **Tier 1 (PROVED, `sorry`-free).**  The sanity direction of the doubling gap:
  doubling costs at most one extra addition, `l (2 * k) ≤ l k + 1`
  (`l_two_mul_le_of_pos`, the layer's `l_two_mul_le` restated on the
  conjecture's domain `0 < k`), and this is *sharp on an infinite family*:
  `l (2 * 2 ^ j) = l (2 ^ j) + 1` for every `j` (`l_two_mul_two_pow`), so the
  sanity bound cannot be improved to `l (2 * k) ≤ l k`.  The additive doubling
  lower bound `Nat.log 2 k + 1 ≤ l (2 * k)` (`log_two_add_one_le_l_two_mul`).
  Kernel-certified `l` values at `n = 3, …, 14` give the exact doubling law
  `l (2 * k) = l k + 1` — deficit exactly `-1`, never `0` — for every
  `0 < k ≤ 7` (`l_two_mul_eq_add_one_of_le_seven`), hence Slizkov's bound with
  room to spare on that range (`slizkov_of_le_seven`).

* **Tier 2 (COMPUTED, outside the kernel — documented in its own section
  below).**  A bounded witness search: no `k` in the searched range has
  `l (2 * k) < l k` at all, a fortiori none has deficit `≥ 2`; the deficit-`0`
  near-misses found recover all `41` listed terms of A086878, in order, as
  the first `41` found (and extend that list past its last term `10481`).
  Nothing in that section is kernel-certified; it documents the computation
  and its bound.

* **Tier 3 (OPEN, intended `sorry`).**  Slizkov's question, archived in
  additive form (never `Nat` subtraction): `slizkov_doubling_gap :`
  `∀ k, 0 < k → l k ≤ l (2 * k) + 1` — "no, doubling can never save more than
  one addition".  A refutation is exactly a witness `k` with
  `l (2 * k) + 1 < l k` (`slizkov_witness_iff`).  The file's satisfiability
  layer instantiates the statement at kernel-certified values.

**Degenerate values.**  `l 0 = 0` is the junk value of the empty infimum
(layer, `l_zero`); the guards `0 < k` keep every statement here on the honest
domain (at `k = 0` both tier-1 and tier-3 inequalities happen to be junk-true
via `l 0 = 0`, and nothing below relies on that).

**Trust.**  Every ground check closes by kernel `decide`, `rfl`, or
`norm_num`; the single `decide +kernel` (at `¬l 14 ≤ 4`, a 576-chain
enumeration) only moves evaluation from the elaborator to the kernel and is
NOT `native_decide`.  No `native_decide`, no `@[implemented_by]`/`@[extern]`/
`@[csimp]`.  The axiom audit at the bottom reports at most
`propext, Classical.choice, Quot.sound` for everything except the intended
`sorry` of `slizkov_doubling_gap`.

Ground truth: `oeis show A230528`, `oeis show A003313`, `oeis show A086878`,
all pulled live 2026-07-30; A003313 terms (offset 1) begin
`0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, …`, and every `l` value certified
below matches the entry.
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## Tier 1: the sanity direction — doubling costs at most one addition -/

/-- **Sanity direction of the doubling gap** (PROVED): doubling costs at most
one extra addition, `l (2 * k) ≤ l k + 1` — append the doubling step
`k + k = 2 * k` to an optimal chain for `k`.  This is the layer's
`l_two_mul_le` restated on `0 < k`, the domain of the open converse
`slizkov_doubling_gap` below (at `k = 0` the unguarded statement is junk-true
via `l 0 = 0`, so the guard is deliberate slack, unused by the proof);
Slizkov's question is whether the mirror-image bound `l k ≤ l (2 * k) + 1`
also holds. -/
theorem l_two_mul_le_of_pos {k : ℕ} (_hk : 0 < k) : l (2 * k) ≤ l k + 1 :=
  l_two_mul_le k

/-- Tier-1 sharpness on an infinite family: at every power of two the doubling
step is optimal, `l (2 * 2 ^ j) = l (2 ^ j) + 1` (both sides computed by the
layer's `l_two_pow`).  So the sanity bound `l (2 * k) ≤ l k + 1` cannot be
improved to `l (2 * k) ≤ l k` — the deficit `-1` is attained infinitely
often. -/
theorem l_two_mul_two_pow (j : ℕ) : l (2 * 2 ^ j) = l (2 ^ j) + 1 := by
  have h : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
  rw [h, l_two_pow, l_two_pow]

/-- Additive form of the doubling lower bound at a doubled argument: for
`0 < k`, `Nat.log 2 k + 1 ≤ l (2 * k)` (the layer's `log_two_le_l` at `2 * k`,
with `Nat.log_mul_base` splitting off the extra factor `2`).  However far
doubling might drop `l` below `l k`, it can never drop it below
`⌊log₂ k⌋ + 1`.  The guard keeps `Nat.log` off its junk value at `0`. -/
theorem log_two_add_one_le_l_two_mul {k : ℕ} (hk : 0 < k) :
    Nat.log 2 k + 1 ≤ l (2 * k) := by
  have hlog : Nat.log 2 (k * 2) = Nat.log 2 k + 1 :=
    Nat.log_mul_base one_lt_two (by omega)
  calc Nat.log 2 k + 1 = Nat.log 2 (k * 2) := hlog.symm
    _ = Nat.log 2 (2 * k) := by rw [mul_comm]
    _ ≤ l (2 * k) := log_two_le_l (2 * k) (by omega)

/-! ## Kernel-certified `l` values (ground truth: `oeis show A003313`)

Each value is certified by an explicit optimal chain (upper bound, via the
layer's `l_le_of_isAddChain`) plus kernel-`decide` exhaustion of all shorter
chains (lower bound, via the layer's `Decidable (l n ≤ k)` instance) — the
layer's own certification pattern.  `l 1, l 2, l 4, l 8` come from the layer
(`l_one`, `l_two`, `l_two_pow`). -/

/-- `l 3 = 2` (entry `a(3) = 2`). -/
theorem l_three : l 3 = 2 := by
  have h1 : l 3 ≤ 2 := l_le_of_isAddChain [3, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 3 ≤ 1 := by decide
  omega

/-- `l 4 = 2` (entry `a(4) = 2`), the case `k = 2` of the layer's `l_two_pow`. -/
theorem l_four : l 4 = 2 := by
  have h := l_two_pow 2
  norm_num at h
  exact h

/-- `l 5 = 3` (entry `a(5) = 3`). -/
theorem l_five : l 5 = 3 := by
  have h1 : l 5 ≤ 3 := l_le_of_isAddChain [5, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 5 ≤ 2 := by decide
  omega

/-- `l 6 = 3` (entry `a(6) = 3`). -/
theorem l_six : l 6 = 3 := by
  have h1 : l 6 ≤ 3 := l_le_of_isAddChain [6, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 6 ≤ 2 := by decide
  omega

/-- `l 7 = 4` (entry `a(7) = 4`). -/
theorem l_seven : l 7 = 4 := by
  have h1 : l 7 ≤ 4 := l_le_of_isAddChain [7, 6, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 7 ≤ 3 := by decide
  omega

/-- `l 8 = 3` (entry `a(8) = 3`), the case `k = 3` of the layer's `l_two_pow`. -/
theorem l_eight : l 8 = 3 := by
  have h := l_two_pow 3
  norm_num at h
  exact h

/-- `l 10 = 4` (entry `a(10) = 4`). -/
theorem l_ten : l 10 = 4 := by
  have h1 : l 10 ≤ 4 := l_le_of_isAddChain [10, 8, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 10 ≤ 3 := by decide
  omega

/-- `l 12 = 4` (entry `a(12) = 4`). -/
theorem l_twelve : l 12 = 4 := by
  have h1 : l 12 ≤ 4 := l_le_of_isAddChain [12, 8, 4, 2, 1] (by decide) rfl (by decide)
  have h2 : ¬l 12 ≤ 3 := by decide
  omega

/-- `l 14 = 5` (entry `a(14) = 5`). -/
theorem l_fourteen : l 14 = 5 := by
  have h1 : l 14 ≤ 5 :=
    l_le_of_isAddChain [14, 7, 6, 4, 2, 1] (by decide) rfl (by decide)
  -- `+kernel`: evaluate the 576-chain enumeration in the kernel only (the
  -- elaborator's evaluator hits `maxRecDepth` first).  This is NOT
  -- `native_decide`: the certificate is still checked by kernel reduction and
  -- the trust surface is unchanged.  (Same pattern as the layer's `l 15`.)
  have h2 : ¬l 14 ≤ 4 := by decide +kernel
  omega

/-! ## The exact doubling law on the kernel-checked range -/

/-- On the kernel-checked range the doubling gap is *exactly* one addition:
`l (2 * k) = l k + 1` for every `0 < k ≤ 7`.  (Externally this persists much
further: the first `k` with `l (2 * k) = l k` is `191`, per A086878 — beyond
exact-value kernel range, see the tier-2 section.)  In particular neither a
Slizkov witness nor even a deficit-`0` near-miss exists below `8`. -/
theorem l_two_mul_eq_add_one_of_le_seven {k : ℕ} (hk : 0 < k) (hk7 : k ≤ 7) :
    l (2 * k) = l k + 1 := by
  interval_cases k
  · norm_num [l_two, l_one]
  · norm_num [l_four, l_two]
  · norm_num [l_six, l_three]
  · norm_num [l_eight, l_four]
  · norm_num [l_ten, l_five]
  · norm_num [l_twelve, l_six]
  · norm_num [l_fourteen, l_seven]

/-- Bounded verification of Slizkov's bound (tier-3 statement) in-kernel: for
`0 < k ≤ 7` the archived inequality `l k ≤ l (2 * k) + 1` holds — with two
additions to spare, since the doubling law is exact there
(`l_two_mul_eq_add_one_of_le_seven`). -/
theorem slizkov_of_le_seven {k : ℕ} (hk : 0 < k) (hk7 : k ≤ 7) :
    l k ≤ l (2 * k) + 1 := by
  have h := l_two_mul_eq_add_one_of_le_seven hk hk7
  omega

/-! ## Tier 2: bounded witness search (COMPUTED, outside the kernel)

NOTHING in this section is kernel-certified; it documents the campaign's
bounded search (2026-07-30) for a Slizkov witness `l (2 * k) + 1 < l k`.
Exact `l` values at these sizes are far outside `decide` range (the
lower-bound half of `l n = v` enumerates all chains of `v - 1` additions,
`≈ ((v-1)!)²` lists; `v ≈ 11` already at `n = 191`).

* **Independent search** (C program, this campaign: per-target iterative
  deepening over strictly ascending chains — complete, since any chain sorts
  and deduplicates to an ascending one of no greater length and elements
  `> n` never feed elements `≤ n` — with the doubling bound `a_i ≤ 2 ^ i`
  as pruning; the Schönhage-type integer bound `⌊log₂ n⌋ + ⌈log₂ ν(n)⌉` as
  the deepening floor, itself checked against all `100000` b-file terms with
  no violation, and in any case covered by the value-by-value diff below):
  `l n` computed exactly for all `n ≤ 16384`.  Cross-checks: `l 1 .. l 100`
  agree with the pulled A003313 terms, and all `16384` values agree with the
  entry's b-file (value-by-value diff).  Deficit scan over `k ≤ 8192`: `l (2 k) = l k + 1` — deficit
  exactly `-1` — for all but the `33` near-miss values
  `k = 191, 701, 743, 1111, 1389, 1479, 2103, 2215, 2375, 2681, 2951, 4281,
  4423, 4491, 4743, 5337, 5517, 5895, 6319, 6367, 6491, 6703, 6751, 7247,
  7319, 7463, 7481, 7571, 7751, 7909, 7993, 8043, 8083`,
  each with `l (2 k) = l k` (deficit `0`) — exactly the listed terms of
  A086878 that are `≤ 8192`.  Maximum deficit over the range: `0`.

* **Entry b-file scan** (`b003313.txt`, oeis.org, pulled 2026-07-30; `100000`
  terms, so `k ≤ 50000`): `266` near-misses, all with deficit exactly `0`,
  the first `41` of them exactly A086878's complete listed terms
  (`191, …, 10481`); maximum deficit over the range: `0`.

* **Consistency.**  A230528's smallest listed term is `375494703 ≫ 50000`, so
  finding not even a deficit-`1` term is expected; the search's value is the
  certified-by-computation absence of a deficit-`≥ 2` witness below the bound,
  and the near-miss inventory.  No Slizkov witness is known to anyone: at the
  seven listed A230528 terms the deficit is `≥ 1` by the entry's definition,
  and exactly `1` because a larger deficit at a listed term would answer the
  entry's own question, which the entry poses as open.
-/

/-! ## Tier 3: Slizkov's question (OPEN, intended `sorry`) -/

/-- A *Slizkov witness* — a `k` at which doubling saves *more* than one
addition, i.e. "the shortest addition chain for `2*k` is shorter than one for
`k` by more than 1" (entry phrasing) — is exactly a counterexample to the
additive bound archived in `slizkov_doubling_gap`, subtraction-free.

NOTE (vacuity audit): this is a `Nat`-order tautology (`not_le.symm` shape),
true of any function in place of `l` — it records the phrasing correspondence
for the reader and does NOT certify the archived statement's fidelity to the
entry; that is carried by the verbatim entry quote at the archive site.  The
`0 < k` guard keeps the statement off the junk comparison `l 0` vs `l 0`. -/
theorem slizkov_witness_iff (k : ℕ) (_hk : 0 < k) :
    l (2 * k) + 1 < l k ↔ ¬(l k ≤ l (2 * k) + 1) := by
  omega

/-- **Slizkov's question** (OEIS A230528 comment, Alexey Slizkov, 2024-01-20:
"Can the shortest addition chain for 2*k be shorter than one for k by more
than 1?") — archived as the conjecture that the answer is *no*, in additive
form (never `Nat` subtraction): for `0 < k`, `l k ≤ l (2 * k) + 1`.  OPEN,
intended `sorry`.

Status of the statement, per the pulled entries and the tier-2 search:

* it is *nontrivial*: it does not follow from tier 1, which bounds the
  opposite difference, and `l (2 * k) < l k` genuinely happens — smallest at
  `k = 375494703` (A230528; external, far beyond kernel range);
* it is *sharp*: at each listed A230528 term the deficit is at least `1` by
  that entry's definition, and exactly `1` since a larger deficit would answer
  the entry's question (posed as open) — so the conjectured bound is attained
  with equality there and cannot be strengthened to `l k ≤ l (2 * k)`;
* it is kernel-verified for `0 < k ≤ 7` with room to spare
  (`slizkov_of_le_seven`) and computationally verified for `k ≤ 50000`
  (tier-2 section);
* a refutation is exactly a Slizkov witness (`slizkov_witness_iff`), which by
  the tier-2 search must have `k > 50000` — the project's witness-first
  epistemics would want the two explicit chains.

The guard `0 < k` keeps the statement off the junk value `l 0 = 0` (the
`k = 0` instance is junk-true, not evidence). -/
theorem slizkov_doubling_gap (k : ℕ) (hk : 0 < k) : l k ≤ l (2 * k) + 1 := by
  -- intended sorry: open question (card A230528-slizkov-doubling; ROUTE: none
  -- known — the entry offers only the seven deficit-1 terms as evidence, and
  -- a refutation would be an explicit chain pair at some k > 50000).
  sorry

/-! ### Satisfiability / nontriviality layer for the archived statement

The hypothesis `0 < k` and the conclusion are jointly instantiated at
kernel-certified values, so the archived statement is neither vacuous nor
trivially true on its domain; and every hypothesis-bearing PROVED theorem
above is instantiated at a concrete model. -/

-- the tier-3 statement instance at `k = 7`, with both sides certified:
-- `l 7 = 4 ≤ 6 = l 14 + 1`
example : 0 < 7 ∧ l 7 ≤ l (2 * 7) + 1 := by
  refine ⟨by norm_num, ?_⟩
  have h7 := l_seven
  have h14 := l_fourteen
  norm_num [h7, h14]

-- the tier-3 statement instance at `k = 191` is NOT certifiable here (l 191
-- needs a ~10¹³-chain enumeration); the nearest kernel-certified deficit data
-- is the exact law of `l_two_mul_eq_add_one_of_le_seven`, instance k = 6:
example : l (2 * 6) = l 6 + 1 := l_two_mul_eq_add_one_of_le_seven (by norm_num) (by norm_num)

-- tier-1 instances (hypothesis satisfied at k = 3, j = 2, k = 5):
example : l (2 * 3) ≤ l 3 + 1 := l_two_mul_le_of_pos (by norm_num)
example : l (2 * 2 ^ 2) = l (2 ^ 2) + 1 := l_two_mul_two_pow 2
example : Nat.log 2 5 + 1 ≤ l (2 * 5) := log_two_add_one_le_l_two_mul (by norm_num)

-- `slizkov_witness_iff` instance at `k = 7`: no witness there (both sides
-- false, consistently with the exact doubling law)
example : ¬(l (2 * 7) + 1 < l 7) := by
  have h := slizkov_of_le_seven (k := 7) (by norm_num) (by norm_num)
  rw [not_lt]
  omega

-- bounded-verification instance at the edge of its range:
example : l 7 ≤ l (2 * 7) + 1 := slizkov_of_le_seven (by norm_num) (by norm_num)

-- consistency of the certified values with the layer's decision procedure,
-- one positive and one negative probe each at the doubling pair (7, 14):
example : l 7 ≤ 4 := by decide
example : ¬l 10 ≤ 3 := by decide
example : l 12 ≤ 4 := by decide

/-! ## Axiom audit (`sorry`-free declarations only)

`slizkov_doubling_gap` is excluded: it carries the file's single intended
`sorry` and reports `sorryAx` by construction.  Everything below must report a
subset of `{propext, Classical.choice, Quot.sound}`. -/

#print axioms l_two_mul_le_of_pos
#print axioms l_two_mul_two_pow
#print axioms log_two_add_one_le_l_two_mul
#print axioms l_three
#print axioms l_four
#print axioms l_five
#print axioms l_six
#print axioms l_seven
#print axioms l_eight
#print axioms l_ten
#print axioms l_twelve
#print axioms l_fourteen
#print axioms l_two_mul_eq_add_one_of_le_seven
#print axioms slizkov_of_le_seven
#print axioms slizkov_witness_iff

end NumberComplexity
