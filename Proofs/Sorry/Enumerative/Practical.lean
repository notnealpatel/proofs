import Sorry.Quarantine.Enumerative.Practical

/-!
# Archived open admission

The attributed declaration below is relocated verbatim from `Enumerative.Practical`.
Its intended `sorry` is not a proof; production retains the independent results,
concrete witnesses, and explicitly hypothesis-parameterized conditional statements.
References to results above or below in the original attribution refer to production.

## Retired implementation card: Coleman (A007691)

The positive multiply-perfect predicate and distinct-divisor subset-sum
practicality predicate are the unchanged production objects. Jaycob Coleman's
OEIS conjecture remains open; its implementation card was hard-blocked, not
mathematically discharged. Production `Practical` proves the Stewart step,
standard infrastructure and the even-perfect case; `StewartCriterion` proves
Stewart's criterion in both directions. The missing argument concerns odd
multiply-perfect numbers (and would rule out odd perfect numbers), or even
multiply-perfect numbers beyond abundancy two. Bounded certificates and the
explicit-hypothesis odd-perfect reduction do not supply it. This archive
completes statement implementation only.
-/

set_option autoImplicit false

namespace Nat

/-- **Coleman's conjecture** — OEIS A007691, comment of Jaycob Coleman (Oct 15
2013), pulled live: "Conjecture: Every multiply-perfect number is practical
(A005153)."  **OPEN**; this is the file's single intended `sorry`.

Status, per the live entry and this file:

* Coleman reports verification "for the first 5261 terms with abundancy > 2 using
  Achim Flammenkamp's data";
* the realization layer below certifies the conjecture sorry-free at the first ten
  terms of A007691, `1, 6, 28, 120, 496, 672, 8128, 30240, 32760, 523776`
  (`Nat.coleman_instance_1` … `Nat.coleman_instance_523776`), which also witness
  joint satisfiability of the hypothesis;
* the conjecture is **OPN-hard** on its odd part: with `Nat.Practical.two_dvd` it
  implies no odd multiperfect `> 1`, in particular no odd perfect number — see the
  reduction section below (`Nat.not_perfect_of_odd_of_coleman`);
* of Coleman's weak form (every *even* multiply-perfect number is practical), the
  perfect case is settled below (`Nat.Perfect.practical_of_even`, via a local
  re-proof of Euler's direction of Euclid–Euler); the even multiperfect case of
  abundancy `≠ 2` remains the attackable open fragment.

ROUTE: Stewart's criterion makes the conjecture verifiable per instance (as the
realization layer does); no proof of the full conjecture is known to anyone. -/
theorem coleman_multiperfect_practical {n : ℕ} (hn : n.IsMultiperfect) :
    n.Practical := by
  -- intended sorry: open conjecture (card Formalize/A007691-coleman-practical.md).
  sorry

end Nat
