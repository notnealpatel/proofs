import Sorry.Quarantine.GroupCount.CdoIteration

/-!
# The admitted Conway–Dietrich–O'Brien iteration conjecture (OEIS A000001)

This module houses the single open proposition `GroupCount.cdo_gnu_iteration`.
`GroupCount.gnu` counts all groups of order `n` up to isomorphism, not only abelian
ones. The proved absorption, reformulations, and strata remain in the production
module `GroupCount.CdoIteration`, which does not import this admission.

Source: J. H. Conway, H. Dietrich, E. A. O'Brien, *Counting groups: gnus, moas and
other exotica*, Math. Intelligencer 30 (2008); OEIS A000001 comment recorded by
Muniru A Asiru, Nov 19 2017. Task card: `Formalize/A000001-cdo-iteration.md`
(claim `cdo-gnu-iteration`).

Status: OPEN. The theorem below is this module's single intended `sorry`, not a
proof of the conjecture. Its axiom footprint includes `sorryAx`; neither GAP finite
coverage nor asymptotic comments discharge the all-positive-`n` proposition.
No `native_decide` is used here.
## Archived implementation-card crosswalk

Former card `A000001-cdo-iteration.md`: A000001, claim `cdo-gnu-iteration`,
statement size M, proof difficulty hard, mathematical status open. The boundary
is implemented, not proved; the production path is `Proofs/GroupCount/CdoIteration.lean`
and the admission now lives here under `Proofs/Sorry/GroupCount/`.

The classification-free model counts the isomorphism quotient of group structures
on `Fin n` using `Nat.card`. Finite tables and bijections permit a finite-search
computability argument; this is not a claim that a fast evaluator was implemented.
The card's proposed sanity suite was prime orders, prime squares, and order 15.
The first two strata are proved upstream; `gnu 15 = 1` is a remaining suggested
sanity target, not a theorem supplied here. Structural classification is preferable
to the factorial-scale table/isomorphism search; no `native_decide` certificate is
claimed. The card's assertion of Lean novelty was not independently established.

GAP SmallGroups coverage is reported finite external evidence, not a Lean proof
or an exhaustive statement beyond that coverage. Arbitrary prime-power values
remain the obstruction to extending the known iteration strata.
-/

set_option autoImplicit false

namespace GroupCount

/-- **The Conway–Dietrich–O'Brien `gnu`-iteration conjecture** (OEIS A000001 comment,
recorded by Muniru A Asiru, Nov 19 2017; conjectured in J. H. Conway, H. Dietrich,
E. A. O'Brien, *Counting groups: gnus, moas and other exotica*, 2008): from every
`1 ≤ n`, the iteration `n → gnu n → gnu (gnu n) → ⋯` eventually reaches `1`.  OPEN,
the file's single intended `sorry`.

Fidelity of the statement:

* "consists ultimately of 1s" is `∃ k, gnu^[k] n = 1` *together with* the proved
  absorption `GroupCount.gnu_iterate_eq_one_of_le`; the two phrasings are exchanged by
  `GroupCount.exists_gnu_iterate_eq_one_iff_forall_le`.
* The guard `1 ≤ n` is necessary, not decorative: `gnu 0 = 0` is a fixed point, so the
  `n = 0` instance is *false* (`GroupCount.not_exists_gnu_iterate_zero_eq_one`).
  A000001 itself starts its group-theoretic content at `n = 1`.

Status: open.  The iteration decreases dramatically in known ranges (external
evidence: it terminates for all `n` within GAP SmallGroups coverage), but a proof
would need control of `gnu` at prime powers, where the value explodes
(`gnu (p^e) ~ p^{(2/27)e³ + O(e^{8/3})}`, entry formula section) — no route is known.
Proved strata in `GroupCount.CdoIteration`: `n = 1`, every prime, `n = 4`, and every `p²`
(`GroupCount.cdo_gnu_iteration_one` / `_prime` / `_four` / `_prime_sq`). -/
theorem cdo_gnu_iteration {n : ℕ} (hn : 1 ≤ n) : ∃ k, gnu^[k] n = 1 := by
  -- intended sorry: open conjecture (card Formalize/A000001-cdo-iteration.md,
  -- claim cdo-gnu-iteration; ROUTE: none known — see the docstring).
  sorry

-- The guard and conclusion are jointly satisfied without using the admission.
example : 1 ≤ 4 ∧ ∃ k, gnu^[k] 4 = 1 := ⟨by omega, cdo_gnu_iteration_four⟩

end GroupCount
