import NumberComplexity.HamiltonBallinger

/-!
# Archived open admission: hamiltonBallinger_finiteness

The original admission is relocated unchanged from `NumberComplexity.HamiltonBallinger`.
The proved definitions, engines, special cases, and ground checks remain there.
This module is not imported by production.
## Retired implementation card: A005245-hamilton-ballinger

The former hard-blocked card's `integerComplexity`/`powerComplexity` target is
implemented by production `complexity`/`powComplexity`, whose optimization
characterizations are proved. The first counts ones using addition and
multiplication; the second uses addition and exponentiation. The OEIS A005245
comment is due to Gordon Hamilton and Brad Ballinger, 2022-05-23. This
admission retirement is not mathematical closure: a comparative eventual
bound strong enough to make the displayed exceptional set finite is unpaid.

The older universal prime recurrence `c(p) = c(p-1) + 1` is refuted, with
reported least counterexample `353942783`. It is not the Hamilton–Ballinger
target and must not be reintroduced as an admission or used as a prerequisite.
-/

set_option autoImplicit false

namespace NumberComplexity

/-- **Hamilton–Ballinger finiteness conjecture** (OEIS A005245 comment,
Gordon Hamilton and Brad Ballinger, 2022-05-23) — OPEN: the integer
(Mahler–Popken) complexity A005245 is strictly below the
`{1, +, ^}`-complexity A348262 for only finitely many `n`. The set is
nonempty (`6` is a member, `exists_complexity_lt_powComplexity`), and
membership fails at `8` (`exists_powComplexity_lt_complexity`), so the
statement is nontrivial in both directions. `n = 0` contributes nothing:
both norms take the junk value `0` there and `0 < 0` is false. -/
theorem hamiltonBallinger_finiteness :
    {n : ℕ | complexity n < powComplexity n}.Finite := by
  -- intended sorry: open conjecture (card A005245-hamilton-ballinger,
  -- ROUTE: none known — requires comparative growth theory of the two
  -- complexity measures; the OEIS entry offers only empirical evidence).
  sorry

end NumberComplexity
