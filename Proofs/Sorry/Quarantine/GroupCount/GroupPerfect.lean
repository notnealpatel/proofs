import Sorry.Quarantine.GroupCount.CdoIteration

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

This file proves strata relevant to both conjectures.  The unproved uniqueness
statement and the weaker abundant-density-zero consequence are archived in
`Sorry.GroupCount.GroupPerfect`, which imports this production module.  The literal
source claims deficient density one: abundant density zero alone does not imply
that without perfect density zero.  Conjoining uniqueness of the positive perfect
number `1` yields the conditional equivalence proved here in
`groupDeficient_density_one_iff_abundant_density_zero`.  The archive derives the
literal deficient-density-one statement using both existing admissions; production
still proves neither conjecture unconditionally.

## Status tiers

* **Tier 1 (PROVED, `sorry`-free)** — the satisfiability/content layer:
  - `GroupCount.groupPerfect_one` — `n = 1` *is* group-perfect (`gnu 1 = 1`);
  - `GroupCount.groupPerfect_zero` — the raw equation `gnu n = n` degenerates at
    `n = 0` through the pinned junk value `gnu 0 = 0` (see the junk-value section);
  - `GroupCount.groupDeficient_of_prime` — **every prime is group-deficient**
    (`gnu p = 1 < p`, including the edge prime `p = 2`): an infinite family;
  - `GroupCount.groupDeficient_prime_sq` — **every prime square is group-deficient**
    (`gnu (p ^ 2) = 2 < p ^ 2`, including `p = 2`);
  - `GroupCount.groupDeficient_four` — `4` is group-deficient (`gnu 4 = 2 < 4`);
  - `GroupCount.infinite_setOf_groupDeficient` — the group-deficient set is infinite;
  - `GroupCount.not_groupPerfect_of_groupDeficient`,
    `GroupCount.not_groupAbundant_of_groupDeficient` — the strata are disjoint, so
    every certified deficiency instance also certifies conjecture (i) at that index
    and certifies `n ∉ A090052` (consistent with the entry's first term being `32`);
  - `GroupCount.not_groupPerfect_prime_sq`,
    `GroupCount.not_groupAbundant_prime_sq` — every prime square is neither
    group-perfect nor group-abundant;
  - `GroupCount.groupAbundantCount` with its ground checks — the counting function
    of the abundant stratum, used in the weaker consequence of conjecture (ii);
  - the finite trichotomy counts and conditional density equivalence, retaining
    perfect uniqueness as an explicit unpaid premise.
* **Tier 2 (OPEN, archived separately)** — conjecture (i),
  `GroupCount.not_groupPerfect_of_two_le`: for `2 ≤ n`, `gnu n ≠ n`.
* **Tier 3 (OPEN, archived separately)** — a weaker consequence of conjecture (ii),
  `GroupCount.groupAbundant_density_zero`: the group-abundant numbers have natural
  density `0`.  Both unproved declarations live in `Sorry.GroupCount.GroupPerfect`.

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
  `decide` wall (exact `gnu` values stop at `n = 2`) and the classification results
  used here (`gnu p = 1` and `gnu (p ^ 2) = 2` for prime `p`).  So this file
  certifies many *negative* instances `¬ GroupAbundant n` but no positive one; the
  satisfiability of the abundant stratum rests on external ground truth (GAP /
  A090052), and is disclosed here rather than asserted.

## Trust policy (USER decision, binding, inherited from `GroupCount/Gnu.lean`)

**Zero `native_decide` anywhere in this module.**  Kernel `decide` appears only at
sizes measured feasible upstream (values of `gnu n` for `n ≤ 2`).  Every other
numeric fact routes through the certified upstream values `gnu_zero`, `gnu_one` …
`gnu_five`, `gnu_seven`, `gnu_four`, `gnu_prime`, `gnu_prime_sq`.  The recorded axiom footprint
for the proved layer is within
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

/-- Every prime square is group-deficient: there are exactly two groups of order
`p ^ 2`, and primality gives `4 ≤ p ^ 2`.  This includes the edge prime `p = 2`. -/
theorem groupDeficient_prime_sq {p : ℕ} (hp : p.Prime) : GroupDeficient (p ^ 2) := by
  show gnu (p ^ 2) < p ^ 2
  rw [gnu_prime_sq hp]
  have hfour : 4 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
  exact lt_of_lt_of_le (by decide : 2 < 4) hfour

/-- **`4` is group-deficient**: `gnu 4 = 2 < 4`, from the classification-certified
`GroupCount.gnu_four`.  This is the smallest deficiency instance at a non-prime. -/
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

/-- Every prime square is not group-perfect, since it is group-deficient. -/
theorem not_groupPerfect_prime_sq {p : ℕ} (hp : p.Prime) : ¬ GroupPerfect (p ^ 2) :=
  not_groupPerfect_of_groupDeficient (groupDeficient_prime_sq hp)

/-- Every prime square is not group-abundant, since it is group-deficient. -/
theorem not_groupAbundant_prime_sq {p : ℕ} (hp : p.Prime) : ¬ GroupAbundant (p ^ 2) :=
  not_groupAbundant_of_groupDeficient (groupDeficient_prime_sq hp)

/-! ## The counting function of the abundant stratum

Abundant density zero is a consequence of conjecture (ii), not its literal statement.  Mathlib
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









/-! ## Conditional bridge to the literal source density statement

The new counts include the raw perfect index `0`; this is why the conditional
perfect-count bound is `2`, not `1`.  Uniqueness remains an explicit unpaid premise:
none of the production results below proves either global conjecture.  The ratio
identity requires `0 < N`, and all asymptotic arguments use that guard eventually.
The ratio at zero is totalized division and has no effect on the limit. -/

/-- Number of group-deficient indices in the half-open interval `[0,N)`. -/
def groupDeficientCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => gnu n < n).card
/-- Number of raw group-perfect indices in `[0,N)`, including the junk index zero. -/
def groupPerfectCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => gnu n = n).card
example : groupDeficientCount 0 = 0 := rfl
example : groupPerfectCount 0 = 0 := rfl
example : groupDeficientCount 3 = 1 := by decide
example : groupPerfectCount 3 = 2 := by decide
/-- Trichotomy partitions each finite initial interval into the three strata. -/
theorem groupCount_partition (N : ℕ) :
    groupDeficientCount N + groupAbundantCount N + groupPerfectCount N = N := by
  have hD := Finset.card_filter_add_card_filter_not (s := Finset.range N)
    (fun n => gnu n < n)
  have hAP := Finset.card_filter_add_card_filter_not
    (s := (Finset.range N).filter fun n => ¬ gnu n < n) (fun n => n < gnu n)
  simp only [Finset.filter_filter] at hAP
  have hA : ((Finset.range N).filter fun n => (¬ gnu n < n) ∧ n < gnu n) =
      ((Finset.range N).filter fun n => n < gnu n) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter]
    constructor
    · intro hn
      exact ⟨hn.1, hn.2.2⟩
    · intro hn
      exact ⟨hn.1, ⟨Nat.not_lt.mpr (Nat.le_of_lt hn.2), hn.2⟩⟩
  have hP : ((Finset.range N).filter fun n => (¬ gnu n < n) ∧ (¬ n < gnu n)) =
      ((Finset.range N).filter fun n => gnu n = n) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter]
    constructor
    · intro hn
      exact ⟨hn.1, Nat.le_antisymm (Nat.le_of_not_gt hn.2.2) (Nat.le_of_not_gt hn.2.1)⟩
    · intro hn
      refine ⟨hn.1, ?_⟩
      rw [hn.2]
      exact ⟨lt_irrefl n, lt_irrefl n⟩
  rw [hA, hP] at hAP
  rw [Finset.card_range] at hD
  unfold groupDeficientCount groupAbundantCount groupPerfectCount
  omega
/-- Under the unproved uniqueness premise, only indices zero and one can be perfect. -/
theorem groupPerfectCount_le_two (huniq : ∀ n : ℕ, 2 ≤ n → gnu n ≠ n) (N : ℕ) :
    groupPerfectCount N ≤ 2 := by
  have hsub : ((Finset.range N).filter fun n => gnu n = n) ⊆ Finset.range 2 := by
    intro n hn
    have heq := (Finset.mem_filter.mp hn).2
    have hlt : n < 2 := by
      by_contra hnot
      exact huniq n (by omega) heq
    exact Finset.mem_range.mpr hlt
  simpa only [groupPerfectCount, Finset.card_range] using Finset.card_le_card hsub
/-- Uniqueness makes the perfect stratum null; division is bounded eventually away from zero. -/
theorem groupPerfect_density_zero_of_unique
    (huniq : ∀ n : ℕ, 2 ≤ n → gnu n ≠ n) :
    Filter.Tendsto (fun N : ℕ => (groupPerfectCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (g := fun N : ℕ => (2 : ℝ) / (N : ℝ))
    (Filter.Eventually.of_forall fun N => by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact div_le_div_of_nonneg_right (by exact_mod_cast groupPerfectCount_le_two huniq N)
      hpos.le
  · exact tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
/-- At positive denominators the finite partition gives the exact complementary ratios. -/
theorem groupDeficient_ratio (N : ℕ) (hN : 0 < N) :
    (groupDeficientCount N : ℝ) / (N : ℝ) =
      1 - (groupAbundantCount N : ℝ) / (N : ℝ) -
        (groupPerfectCount N : ℝ) / (N : ℝ) := by
  have hp : (groupDeficientCount N : ℝ) + (groupAbundantCount N : ℝ) +
      (groupPerfectCount N : ℝ) = (N : ℝ) := by exact_mod_cast groupCount_partition N
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  linarith
/-- Under uniqueness, literal deficient density one is equivalent to abundant density zero. -/
theorem groupDeficient_density_one_iff_abundant_density_zero
    (huniq : ∀ n : ℕ, 2 ≤ n → gnu n ≠ n) :
    Filter.Tendsto (fun N : ℕ => (groupDeficientCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) ↔
    Filter.Tendsto (fun N : ℕ => (groupAbundantCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  have hp := groupPerfect_density_zero_of_unique huniq
  constructor
  · intro hd
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hd |>.sub hp
    have heq : (fun N : ℕ => 1 - (groupDeficientCount N : ℝ) / (N : ℝ) -
        (groupPerfectCount N : ℝ) / (N : ℝ)) =ᶠ[Filter.atTop]
        (fun N : ℕ => (groupAbundantCount N : ℝ) / (N : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hr := groupDeficient_ratio N (by omega)
      linarith
    simpa only [sub_self, sub_zero] using ht.congr' heq
  · intro ha
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub ha |>.sub hp
    have heq : (fun N : ℕ => 1 - (groupAbundantCount N : ℝ) / (N : ℝ) -
        (groupPerfectCount N : ℝ) / (N : ℝ)) =ᶠ[Filter.atTop]
        (fun N : ℕ => (groupDeficientCount N : ℝ) / (N : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      exact (groupDeficient_ratio N (by omega)).symm
    simpa only [sub_zero] using ht.congr' heq

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

-- Prime-square hypotheses and conclusions hold jointly, including the edge prime.
example : Nat.Prime 2 ∧ GroupDeficient (2 ^ 2) :=
  ⟨Nat.prime_two, groupDeficient_prime_sq Nat.prime_two⟩
example : Nat.Prime 3 ∧ GroupDeficient (3 ^ 2) :=
  ⟨Nat.prime_three, groupDeficient_prime_sq Nat.prime_three⟩
example : Nat.Prime 2 ∧ ¬ GroupPerfect (2 ^ 2) :=
  ⟨Nat.prime_two, not_groupPerfect_prime_sq Nat.prime_two⟩
example : Nat.Prime 2 ∧ ¬ GroupAbundant (2 ^ 2) :=
  ⟨Nat.prime_two, not_groupAbundant_prime_sq Nat.prime_two⟩

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

The two unproved declarations are admitted only in `Sorry.GroupCount.GroupPerfect`.
Every declaration here must report a subset of `{propext, Classical.choice, Quot.sound}`.
There is no `native_decide` in this file.  The anonymous disclosed example upstream
(`GroupCount/Structures.lean`) persists no constant and taints no theorem here.
The inherited `CdoIteration` admission is outside this module's proof dependencies. -/



end GroupCount
