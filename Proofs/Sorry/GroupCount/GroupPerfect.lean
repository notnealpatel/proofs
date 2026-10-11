import GroupCount.GroupPerfect

/-!
# Unproved obligations associated with `GroupCount.GroupPerfect`

This archive imports the proved production layer; production does not import this archive.
The declarations below preserve the original names, types, and source provenance.
## Archived implementation-card crosswalk

Former card `A090052-group-perfect.md`: A090052, claim `group-perfect-uniqueness`,
statement size M, proof difficulty hard. Both source claims remain open; the OEIS
“seems fairly certain” comment is unattributed. A090052 counts group-abundant
orders (`gnu n > n`), not group-perfect ones. The production counting model is the
same all-group isomorphism count as A000001, with counts over `Finset.range N`.
Production `Proofs/GroupCount/GroupPerfect.lean` proves
`GroupCount.groupDeficient_of_prime` and `GroupCount.groupDeficient_prime_sq`,
including the edge case prime 2. General squarefree and cube-free deficiency
remain classification obligations, not consequences of these two strata.
The reported absence of other group-perfect numbers in GAP ranges and sparsity
of abundant, 2-group-heavy orders are finite external evidence only.

The card's “i.e.” between deficient density one and abundant density zero needs
perfect density zero. Production now proves that missing bridge conditionally
on the uniqueness assertion (at most the two exceptional indices 0 and 1).
This archive derives the literal deficient-density-one source statement from
its two existing admissions, without admitting a third proposition. Estimates
for arbitrary orders and the source's asymptotic density claim remain unpaid.
-/

set_option autoImplicit false

namespace GroupCount

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
group-deficient (Hölder).  Proved strata in the imported production module: every prime and `n = 4`, via
`GroupCount.not_groupPerfect_of_groupDeficient` (instances in the satisfiability
layer of that module). -/
theorem not_groupPerfect_of_two_le {n : ℕ} (hn : 2 ≤ n) : ¬ GroupPerfect n := by
  -- intended sorry: open conjecture (card A090052-group-perfect, claim (i)).
  -- ROUTE: needs upper bounds on gnu away from 2-heavy orders and exact knowledge
  -- at them; the squarefree stratum is classical (Hölder), the rest is open.
  sorry

/-- **The group-abundant numbers have natural density `0`** — a weaker consequence of
conjecture (ii) in OEIS A090052 (comment, **unattributed**, same "seems fairly certain"
sentence) — OPEN, intended `sorry`, in the counting-function formulation:
`groupAbundantCount N / N → 0` as `N → ∞` in `ℝ`.

This is a strict *consequence* of the literal comment, not the comment itself.
The comment says "almost all numbers are group-deficient", i.e. the *deficient*
set has density `1`; deficient/perfect/abundant partition `ℕ` by trichotomy, so
deficient-density-`1` is abundant-density-`0` PLUS perfect-density-`0`, and the
perfect stratum is nonempty (`{0, 1}` in the certified range —
`GroupCount.groupPerfect_zero`, `GroupCount.groupPerfect_one`).  This archive
records the abundant-density-`0` form — the reading the campaign card itself
fixes with its "i.e.".  Production proves the equivalence conditional on
conjecture (i), via `groupDeficient_density_one_iff_abundant_density_zero`.
The derived theorem `groupDeficient_density_one` below combines these two
existing admissions to recover the literal source reading, without a new admission.

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

/-- The literal OEIS A090052 source statement: almost all indices are group-deficient.
This derives from the two existing admitted conjectures through the proved conditional
finite-count bridge; it is not an unconditional production proof or a new admission.
The ratio at zero is totalized division; eventual positive denominators control the limit. -/
theorem groupDeficient_density_one :
    Filter.Tendsto (fun N : ℕ => (groupDeficientCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  have huniq : ∀ n : ℕ, 2 ≤ n → gnu n ≠ n := by
    intro n hn
    exact not_groupPerfect_of_two_le hn
  exact (groupDeficient_density_one_iff_abundant_density_zero huniq).mpr
    groupAbundant_density_zero

end GroupCount
