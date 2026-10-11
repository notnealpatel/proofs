import Enumerative.PrimesNotCubeMinusSquare

/-!
# Open obligation for A161682

This quarantine module retains the existing unproved source statement under its original
namespace and header. The production module supplies the definitions and unconditional
proofs; importing production alone does not admit this conjecture. Source quotations,
limitations, and evidence for the statement are retained below and in the production
module's pinned source documentation. No mathematical proof closure is claimed.
-/

set_option autoImplicit false

namespace A161682

/-- **The A161682 infinitude conjecture.**

Verbatim from the entry's `comments` field, pulled 2026-08-05 — the whole line,
which carries no attribution:

> Conjecture: The sequence is infinite.

**Status: open.**  This is the single intended `sorry` of the file.

**What is and is not established around it.**  The statement is not vacuous in
either direction: `primesNotCubeMinusSquare_nonempty` shows the set is inhabited
(so the claim is not trivially *false*), and
`primesNotCubeMinusSquare_ssubset_setOf_prime` shows it is a *proper* subset of
the primes (so the claim is not a restatement of Euclid, which would make it
trivially *true*).  Neither of those, of course, is evidence for the conjecture.

**Why it is hard.**  Membership of a single prime `p` is the assertion that the
Mordell equation `y ^ 2 = x ^ 3 - p` has no integral point.  Each such assertion
is decidable in principle — Baker's method bounds the integral points effectively,
and Siegel's theorem makes them finite — but the bounds are astronomical and, more
to the point, they are *per `p`*.  An infinitude statement needs a single
obstruction that recurs for infinitely many `p`, and the entry supplies none: its
only evidence is the bounded search recorded in the first comment (`x,y < 10000`)
and Starodubtsev's extension (`x < 2.2*10^9`), which are searches for
representations, not proofs that none exist.  Hall's conjecture on `|x ^ 3 - y ^ 2|`
is the natural quantitative frame and is itself open.

The congruence obstructions that settle the individual cases here — `p = 3` and
`p = 5`, via `x ^ 2 ∓ x + 1 ≡ 3 (mod 4)` dividing `z ^ 2 + 1` — do not generalize:
for `p = 4 * k ^ 2 + 1` with `k > 1` the same factorization produces
`x ^ 2 + x + 1 ∣ z ^ 2 + k ^ 2`, and a prime `≡ 3 (mod 4)` may divide `z ^ 2 + k ^ 2`
whenever it divides both `z` and `k`, which nothing in the descent rules out. -/
theorem primesNotCubeMinusSquare_infinite : primesNotCubeMinusSquare.Infinite := by
  -- intended sorry: the unattributed A161682 comment "Conjecture: The sequence is infinite."
  sorry

end A161682
