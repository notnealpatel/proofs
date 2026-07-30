import GroupCount.Gnu

/-!
# A090052: group-perfect, group-deficient, and group-abundant numbers

With `GroupCount.gnu n` the number of groups of order `n` up to isomorphism (OEIS
A000001, `GroupCount/Gnu.lean`), call `n` *group-deficient* when `gnu n < n`,
*group-perfect* when `gnu n = n`, and *group-abundant* when `n < gnu n`.  OEIS A090052
is the sequence of group-abundant numbers: `32, 48, 64, 96, 128, 144, …` (pulled live
2026-07-30 with `oeis show A090052`).

The entry's comment carries two conjectures.  **They are unattributed**: the entry
says only "It seems fairly certain", with no name attached.  Verbatim quote:

> "It seems fairly certain that 1 is the only group-perfect number and that almost
> all numbers are group-deficient. However, all that is known at present is that all
> squarefree numbers except 1 are group-deficient."

This file archives both conjectures together with their provable strata.

## Status tiers

* **Tier 1 (PROVED, `sorry`-free)** — the satisfiability/content layer:
  - `GroupCount.groupPerfect_one` — `n = 1` *is* group-perfect (`gnu 1 = 1`);
  - `GroupCount.groupPerfect_zero` — the raw equation `gnu n = n` degenerates at
    `n = 0` through the pinned junk value `gnu 0 = 0` (see the junk-value section);
  - `GroupCount.groupDeficient_of_prime` — **every prime is group-deficient**
    (`gnu p = 1 < p`, including the edge prime `p = 2`): an infinite family;
  - `GroupCount.groupDeficient_four` — `4` is group-deficient (`gnu 4 = 2 < 4`);
  - `GroupCount.infinite_setOf_groupDeficient` — the group-deficient set is infinite;
  - `GroupCount.not_groupPerfect_of_groupDeficient`,
    `GroupCount.not_groupAbundant_of_groupDeficient` — the strata are disjoint, so
    every certified deficiency instance also certifies conjecture (i) at that index
    and certifies `n ∉ A090052` (consistent with the entry's first term being `32`);
  - `GroupCount.groupAbundantCount` with its ground checks — the counting function
    of the abundant stratum, the quantity conjecture (ii) is about.
* **Tier 2 (OPEN, intended `sorry`)** — conjecture (i),
  `GroupCount.not_groupPerfect_of_two_le`: for `2 ≤ n`, `gnu n ≠ n`.
* **Tier 3 (OPEN, intended `sorry`)** — conjecture (ii),
  `GroupCount.groupAbundant_density_zero`: the group-abundant numbers have natural
  density `0`.

## Junk values and degeneracies

* `gnu 0 = 0` (`GroupCount.gnu_eq_zero_iff`: no group has order `0`), so `n = 0`
  satisfies the *raw* equation `gnu n = n` — as a junk artifact, not as a statement
  about groups.  `GroupCount.groupPerfect_zero` pins this degeneracy explicitly; it
  is why conjecture (i) carries the guard `2 ≤ n` and why the informal "1 is the
  only group-perfect number" tacitly quantifies over `1 ≤ n`.
* In `GroupCount.groupAbundant_density_zero` the ratio at `N = 0` is the real
  division junk `0 / 0 = 0`.  The statement is a `Filter.atTop` limit, which no
  finite prefix (in particular not the `N = 0` term) can affect, so the claim is
  not about the junk value.
* `GroupDeficient` and `GroupAbundant` are junk-safe at `0` and `1` outright:
  `gnu 0 = 0 < 0` and `0 < gnu 0`, resp. `gnu 1 = 1 < 1` and `1 < gnu 1`, are all
  false.

## What is NOT in this file

* **The squarefree stratum.**  The entry's "all that is known" clause — every
  squarefree `n` except `1` is group-deficient — is *known* in the literature (via
  Hölder's classification of groups of squarefree order), so it is not an open
  conjecture to archive; and proving it needs a classification layer (groups of
  squarefree order are metacyclic) far beyond `GroupCount/Gnu.lean`.  Omitted, not
  `sorry`d.
* **A positive `GroupAbundant` witness.**  The first group-abundant number is `32`,
  with `gnu 32 = 51` (A000001, external), far beyond both the measured kernel
  `decide` wall (exact `gnu` values stop at `n = 2`) and the classification layer
  landed upstream (`gnu 4 = 2` is the largest classified value).  So this file
  certifies many *negative* instances `¬ GroupAbundant n` but no positive one; the
  satisfiability of the abundant stratum rests on external ground truth (GAP /
  A090052), and is disclosed here rather than asserted.

## Trust policy (USER decision, binding, inherited from `GroupCount/Gnu.lean`)

**Zero `native_decide` anywhere in this module.**  Kernel `decide` appears only at
sizes measured feasible upstream (values of `gnu n` for `n ≤ 2`).  Every other
numeric fact routes through the certified upstream values `gnu_zero`, `gnu_one` …
`gnu_five`, `gnu_seven`, `gnu_four`, `gnu_prime`.  The axiom sweep at the end
confirms: `sorryAx` on the two archived conjectures only, everything else within
`{propext, Classical.choice, Quot.sound}` — an *allowlist* check, and the sound
`native_decide` detector on this toolchain: a use would surface as a
per-declaration `<decl>._native.native_decide.ax_*` axiom (`Lean.ofReduceBool` is
never emitted).  The one anonymous disclosed example upstream
(`GroupCount/Structures.lean`, ground-truth section) persists no constant and
taints no theorem here.

## Naming note

The declaration `GroupCount.GroupPerfect : ℕ → Prop` coincides with this module's
name (`GroupCount.GroupPerfect`).  Modules are not declarations, so the collision
is kernel-harmless; both names are the natural ones and are kept.

## References

* OEIS A090052 (`oeis show A090052`), terms `32, 48, 64, 96, …`; the conjectures are
  the entry's unattributed comment quoted above.
* OEIS A000001 (`oeis show A000001`), terms `0, 1, 1, 1, 2, 1, 2, 1, 5, …`;
  `a(32) = 51` is the external witness that `32` is group-abundant.
-/

set_option autoImplicit false

namespace GroupCount

/-! ## The trichotomy vocabulary

Three predicates on `ℕ`, all spelled with `<`/`≤`-normal comparisons against
`gnu`.  Each is definitionally transparent (the `Iff.rfl` pins below) and
decidable — decidable *in principle*: deciding an instance at `n` evaluates
`gnu n`, which is kernel-feasible only for `n ≤ 2` (see `GroupCount/Gnu.lean`). -/

/-- `n` is *group-deficient* when there are fewer groups of order `n` than `n`
itself: `gnu n < n`.  The A090052 comment's conjecture (ii) is that almost all
numbers are group-deficient. -/
def GroupDeficient (n : ℕ) : Prop := gnu n < n

/-- `n` is *group-perfect* when the number of groups of order `n` is exactly `n`:
`gnu n = n`.  The A090052 comment's conjecture (i) is that `n = 1` is the only
group-perfect number past the `n = 0` junk degeneracy
(`GroupCount.groupPerfect_zero`). -/
def GroupPerfect (n : ℕ) : Prop := gnu n = n

/-- `n` is *group-abundant* when there are more groups of order `n` than `n`
itself: `n < gnu n`.  **OEIS A090052 is exactly the increasing enumeration of
this predicate**; its terms start `32, 48, 64, 96, …` — all far beyond the
kernel wall, so this file exhibits no positive instance (disclosed in the
module docstring). -/
def GroupAbundant (n : ℕ) : Prop := n < gnu n

-- Definitional transparency pins: the predicates are exactly the raw comparisons.
example : ∀ n : ℕ, GroupDeficient n ↔ gnu n < n := fun _ => Iff.rfl
example : ∀ n : ℕ, GroupPerfect n ↔ gnu n = n := fun _ => Iff.rfl
example : ∀ n : ℕ, GroupAbundant n ↔ n < gnu n := fun _ => Iff.rfl

/-- Group-deficiency is decidable (by evaluating `gnu` — kernel-feasible only for
tiny `n`; see the measured wall in `GroupCount/Gnu.lean`). -/
instance instDecidablePredGroupDeficient : DecidablePred GroupDeficient :=
  fun n => inferInstanceAs (Decidable (gnu n < n))

/-- Group-perfection is decidable (same caveat as
`GroupCount.instDecidablePredGroupDeficient`). -/
instance instDecidablePredGroupPerfect : DecidablePred GroupPerfect :=
  fun n => inferInstanceAs (Decidable (gnu n = n))

/-- Group-abundance is decidable (same caveat as
`GroupCount.instDecidablePredGroupDeficient`); this is the instance that makes the
counting function `GroupCount.groupAbundantCount` well-formed over the predicate
spelling (`GroupCount.groupAbundantCount_eq_card_filter_groupAbundant`). -/
instance instDecidablePredGroupAbundant : DecidablePred GroupAbundant :=
  fun n => inferInstanceAs (Decidable (n < gnu n))

/-! ## Tier 1: proved strata -/

/-- **`n = 1` is group-perfect**: `gnu 1 = 1` — there is exactly one group of order
one.  This is the member the A090052 comment's conjecture (i) asserts is unique. -/
theorem groupPerfect_one : GroupPerfect 1 := gnu_one

/-- **Degeneracy pin, not a statement about groups**: `n = 0` satisfies the raw
equation `gnu n = n` only through the junk value `gnu 0 = 0` (no group has order
`0`; `GroupCount.gnu_eq_zero_iff`).  This is exactly why conjecture (i)
(`GroupCount.not_groupPerfect_of_two_le`) carries the guard `2 ≤ n` and why the
informal claim "1 is the only group-perfect number" tacitly lives on `1 ≤ n`. -/
theorem groupPerfect_zero : GroupPerfect 0 := gnu_zero

/-- **Every prime is group-deficient** — an infinite family of deficiency instances:
`gnu p = 1 < p` by `GroupCount.gnu_prime`.  The edge prime `p = 2` is covered:
`gnu 2 = 1 < 2`. -/
theorem groupDeficient_of_prime {p : ℕ} (hp : p.Prime) : GroupDeficient p := by
  show gnu p < p
  rw [gnu_prime hp]
  exact hp.one_lt

/-- **`4` is group-deficient**: `gnu 4 = 2 < 4`, from the classification-certified
`GroupCount.gnu_four`.  This is the smallest deficiency instance at a non-prime
(and the largest index at which this file can certify deficiency at all — `gnu 6`
is not certified upstream). -/
theorem groupDeficient_four : GroupDeficient 4 := by
  show gnu 4 < 4
  rw [gnu_four]
  omega

/-- **The group-deficient numbers form an infinite set**: they contain the primes
(`GroupCount.groupDeficient_of_prime`), of which there are infinitely many.  This
is the `sorry`-free infinite shadow of conjecture (ii) ("almost all numbers are
group-deficient"): infinitude is proved, density is open. -/
theorem infinite_setOf_groupDeficient : {n : ℕ | GroupDeficient n}.Infinite :=
  Nat.infinite_setOfPred_prime.mono fun _p hp => groupDeficient_of_prime hp

/-! ### Disjointness of the strata

Trichotomy of `<` on `ℕ` makes the three predicates mutually exclusive; recording
the two directions used below turns every certified deficiency instance into a
certified instance of conjecture (i) and a certified non-member of A090052. -/

/-- A group-deficient number is not group-perfect: the strata are disjoint.  Applied
at the certified values, this proves conjecture (i) at `n = 2, 3, 4, 5, 7` and at
every prime (see the satisfiability layer below). -/
theorem not_groupPerfect_of_groupDeficient {n : ℕ} (h : GroupDeficient n) :
    ¬ GroupPerfect n := by
  intro hp
  have hlt : gnu n < n := h
  have heq : gnu n = n := hp
  omega

/-- A group-deficient number is not group-abundant: certified deficiency instances
are certified non-members of A090052 (consistent with the entry's first term `32`). -/
theorem not_groupAbundant_of_groupDeficient {n : ℕ} (h : GroupDeficient n) :
    ¬ GroupAbundant n := by
  intro ha
  have hlt : gnu n < n := h
  have hgt : n < gnu n := ha
  omega

/-! ## The counting function of the abundant stratum

Conjecture (ii) says the group-abundant numbers have natural density `0`.  Mathlib
has no off-the-shelf natural-density predicate (only Schnirelmann density, which is
the wrong notion here), so the statement is spelled as the limit of the counting
function divided by `N` — the standard counting-function formulation of density. -/

/-- The number of group-abundant numbers below `N`: the counting function of
A090052.  The range is half-open — `groupAbundantCount N` counts abundant `n` in
`[0, N)`, agreeing with A090052 as a set (its 1-based listing cannot affect the
`atTop` limit).  `gnu` is computable, so the filter is decidable; evaluating it at
`N` is kernel-feasible only for `N ≤ 3` (it evaluates `gnu n` for every `n < N`),
and the ground check `GroupCount.groupAbundantCount_six` instead routes through
the certified upstream values. -/
def groupAbundantCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => n < gnu n).card

/-- The raw-comparison filter in `GroupCount.groupAbundantCount` is definitionally
the filter of the `GroupAbundant` predicate. -/
theorem groupAbundantCount_eq_card_filter_groupAbundant (N : ℕ) :
    groupAbundantCount N = ((Finset.range N).filter fun n => GroupAbundant n).card := rfl

/-- Trivially, at most `N` of the numbers below `N` are group-abundant — so the
density ratio in conjecture (ii) is at most `1`. -/
theorem groupAbundantCount_le (N : ℕ) : groupAbundantCount N ≤ N := by
  have hcard : ((Finset.range N).filter fun n => n < gnu n).card ≤ (Finset.range N).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_range] at hcard
  exact hcard

/-- **Ground check of the counting function against A090052**: no number below `6`
is group-abundant (the entry's first term is `32`).  Proved through the certified
values `gnu 0, …, gnu 5` — NOT by kernel evaluation, which is infeasible past
`gnu 2` (see the measured wall in `GroupCount/Gnu.lean`).  The range stops at `6`
because `gnu 6` is not certified upstream. -/
theorem groupAbundantCount_six : groupAbundantCount 6 = 0 := by
  show ((Finset.range 6).filter fun n => n < gnu n).card = 0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_range] at hn
  interval_cases n
  · rw [gnu_zero]; omega
  · rw [gnu_one]; omega
  · rw [gnu_two]; omega
  · rw [gnu_three]; omega
  · rw [gnu_four]; omega
  · rw [gnu_five]; omega

/-! ## Tier 2: conjecture (i) — group-perfect uniqueness (OPEN, intended `sorry`) -/

/-- **Group-perfect uniqueness** (OEIS A090052 comment, **unattributed** — the entry
says only "It seems fairly certain that 1 is the only group-perfect number", with no
name attached) — OPEN, intended `sorry`: for `2 ≤ n`, `gnu n ≠ n` (definitionally,
`¬ GroupPerfect n`), i.e. `n = 1` is the only group-perfect number on `1 ≤ n`
(`GroupCount.groupPerfect_one` gives membership; the `n = 0` junk solution is pinned
by `GroupCount.groupPerfect_zero` and excluded by the guard).

What exactly is open: no `n` with `2 ≤ n` and `gnu n = n` is known (none exists in
the GAP-verified range), but no proof excludes one.  The entry itself claims nothing
stronger than "seems fairly certain".  What *is* known (literature, not formalized
here): all squarefree `n` except `1` satisfy the conjecture, since they are
group-deficient (Hölder).  Proved strata in this file: every prime and `n = 4`, via
`GroupCount.not_groupPerfect_of_groupDeficient` (instances in the satisfiability
layer below). -/
theorem not_groupPerfect_of_two_le {n : ℕ} (hn : 2 ≤ n) : ¬ GroupPerfect n := by
  -- intended sorry: open conjecture (card A090052-group-perfect, claim (i)).
  -- ROUTE: needs upper bounds on gnu away from 2-heavy orders and exact knowledge
  -- at them; the squarefree stratum is classical (Hölder), the rest is open.
  sorry

/-! ## Tier 3: conjecture (ii) — density 0 of group-abundant numbers
(OPEN, intended `sorry`) -/

/-- **The group-abundant numbers have natural density `0`** — conjecture (ii) of
OEIS A090052 (comment, **unattributed**, same "seems fairly certain" sentence) —
OPEN, intended `sorry`, in the counting-function formulation:
`groupAbundantCount N / N → 0` as `N → ∞` in `ℝ`.

This is a strict *consequence* of the literal comment, not the comment itself.
The comment says "almost all numbers are group-deficient", i.e. the *deficient*
set has density `1`; deficient/perfect/abundant partition `ℕ` by trichotomy, so
deficient-density-`1` is abundant-density-`0` PLUS perfect-density-`0`, and the
perfect stratum is nonempty (`{0, 1}` in the certified range —
`GroupCount.groupPerfect_zero`, `GroupCount.groupPerfect_one`).  This file
archives the abundant-density-`0` form — the reading the campaign card itself
fixes with its "i.e." — and derives neither reading from the other.  Under
conjecture (i) the perfect stratum is exactly `{0, 1}`, which is null, so the two
readings agree conjecturally.

Junk-value note: at `N = 0` the ratio is the real-division junk `0 / 0 = 0`; the
`Filter.atTop` limit is unaffected by any finite prefix, so the statement is not
about the junk value.  (STYLE's guarded-`/` rule cannot attach its hypothesis
inside a `Tendsto` over `atTop`; the rule's purpose is met by this disclosure
plus the invariance of the limit under any reassignment of the `N = 0` term.)
Content notes: the ratio is well-grounded — it is `0` at `N = 6`
(`GroupCount.groupAbundantCount_six`) and at most `1` always
(`GroupCount.groupAbundantCount_le`); and the conjecture does NOT follow from
`GroupCount.infinite_setOf_groupDeficient` (an infinite complement does not force
density `0`). -/
theorem groupAbundant_density_zero :
    Filter.Tendsto (fun N : ℕ => (groupAbundantCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  -- intended sorry: open conjecture (card A090052-group-perfect, claim (ii)).
  -- ROUTE: Pyber-type upper bounds on gnu are the known tool, far beyond the
  -- current machinery (no upper bound on gnu of any kind is formalized upstream).
  sorry

/-! ## Ground truth and satisfiability

Every hypothesis of every proved theorem above is jointly instantiated at a
concrete model, and the two archived conjectures are instantiated (hypothesis and
conclusion jointly) at certified indices, so neither is vacuous on its domain.
Checked against `oeis show A090052` (first term `32`) and `oeis show A000001`
(terms `0, 1, 1, 1, 2, 1, …`). -/

section GroundTruth

-- `GroupDeficient` at the certified small indices: primes 2, 3, 5, 7 (the prime
-- family instantiated, `p = 2` edge included) and the non-prime 4.
example : GroupDeficient 2 := groupDeficient_of_prime Nat.prime_two
example : GroupDeficient 3 := groupDeficient_of_prime Nat.prime_three
example : GroupDeficient 5 := groupDeficient_of_prime (by norm_num)
example : GroupDeficient 7 := groupDeficient_of_prime (by norm_num)
example : GroupDeficient 4 := groupDeficient_four

-- Direct route (no prime detour) at 2, pinning the definitional content.
example : GroupDeficient 2 := by show gnu 2 < 2; rw [gnu_two]; omega

-- Conjecture (i), statement instantiated AND proved at certified indices: the
-- hypothesis `2 ≤ n` and the conclusion hold jointly at `n = 2, 3, 4, 5, 7`.
example : 2 ≤ 2 ∧ ¬ GroupPerfect 2 :=
  ⟨le_refl 2, not_groupPerfect_of_groupDeficient (groupDeficient_of_prime Nat.prime_two)⟩
example : 2 ≤ 4 ∧ ¬ GroupPerfect 4 :=
  ⟨by omega, not_groupPerfect_of_groupDeficient groupDeficient_four⟩
example : ¬ GroupPerfect 3 :=
  not_groupPerfect_of_groupDeficient (groupDeficient_of_prime Nat.prime_three)
example : ¬ GroupPerfect 5 :=
  not_groupPerfect_of_groupDeficient (groupDeficient_of_prime (by norm_num))
example : ¬ GroupPerfect 7 :=
  not_groupPerfect_of_groupDeficient (groupDeficient_of_prime (by norm_num))

-- …and conjecture (i)'s conclusion fails at both indices its guard excludes: the
-- `2 ≤ n` hypothesis is not droppable.
example : GroupPerfect 0 := groupPerfect_zero
example : GroupPerfect 1 := groupPerfect_one

-- Non-membership in A090052 (`¬ GroupAbundant`) at every certified index —
-- consistent with the entry's first term being 32.
example : ¬ GroupAbundant 2 :=
  not_groupAbundant_of_groupDeficient (groupDeficient_of_prime Nat.prime_two)
example : ¬ GroupAbundant 3 :=
  not_groupAbundant_of_groupDeficient (groupDeficient_of_prime Nat.prime_three)
example : ¬ GroupAbundant 4 := not_groupAbundant_of_groupDeficient groupDeficient_four
example : ¬ GroupAbundant 5 :=
  not_groupAbundant_of_groupDeficient (groupDeficient_of_prime (by norm_num))
example : ¬ GroupAbundant 7 :=
  not_groupAbundant_of_groupDeficient (groupDeficient_of_prime (by norm_num))

-- The perfect/junk indices are not abundant either (via the certified values, not
-- via deficiency, which fails at 0 and 1).
example : ¬ GroupAbundant 0 := by show ¬ 0 < gnu 0; rw [gnu_zero]; omega
example : ¬ GroupAbundant 1 := by show ¬ 1 < gnu 1; rw [gnu_one]; omega

-- The counting function at kernel-feasible sizes (`gnu` evaluated at `n ≤ 2`
-- only, inside the measured wall): independent `rfl`/`decide` cross-checks of the
-- theorem-route `groupAbundantCount_six`.
example : groupAbundantCount 0 = 0 := rfl
example : groupAbundantCount 2 = 0 := by decide

-- The density ratio of conjecture (ii) at a certified index: genuinely `0` at
-- `N = 6`, and the `N = 0` junk value is `0` as disclosed.
example : (groupAbundantCount 6 : ℝ) / (6 : ℝ) = 0 := by
  rw [groupAbundantCount_six]
  norm_num
example : (groupAbundantCount 0 : ℝ) / ((0 : ℕ) : ℝ) = 0 := by
  norm_num

-- `groupAbundantCount_le` instantiated at a nondegenerate and a degenerate index.
example : groupAbundantCount 6 ≤ 6 := groupAbundantCount_le 6
example : groupAbundantCount 0 ≤ 0 := groupAbundantCount_le 0

-- The infinite deficient set is not merely nonempty-by-junk: two explicit members.
example : (2 : ℕ) ∈ {n : ℕ | GroupDeficient n} := groupDeficient_of_prime Nat.prime_two
example : (4 : ℕ) ∈ {n : ℕ | GroupDeficient n} := groupDeficient_four

end GroundTruth

/-! ## Axiom audit

Sweep of every public declaration.  The two archived conjectures
(`not_groupPerfect_of_two_le`, `groupAbundant_density_zero`) carry the file's only
intended `sorry`s and report `sorryAx` by construction — nothing else may.  Every
other declaration must report a subset of `{propext, Classical.choice, Quot.sound}`.
The subset is the sound `native_decide` detector: a use would appear as a
per-declaration `*._native.native_decide.ax_*` axiom on this toolchain
(`Lean.ofReduceBool` is never emitted, so grepping for it detects nothing). -/

#print axioms GroupDeficient
#print axioms GroupPerfect
#print axioms GroupAbundant
#print axioms instDecidablePredGroupDeficient
#print axioms instDecidablePredGroupPerfect
#print axioms instDecidablePredGroupAbundant
#print axioms groupPerfect_one
#print axioms groupPerfect_zero
#print axioms groupDeficient_of_prime
#print axioms groupDeficient_four
#print axioms infinite_setOf_groupDeficient
#print axioms not_groupPerfect_of_groupDeficient
#print axioms not_groupAbundant_of_groupDeficient
#print axioms groupAbundantCount
#print axioms groupAbundantCount_eq_card_filter_groupAbundant
#print axioms groupAbundantCount_le
#print axioms groupAbundantCount_six
#print axioms not_groupPerfect_of_two_le
#print axioms groupAbundant_density_zero

end GroupCount
