# Conditional a=12 seed, e ≥ 3

## Source gate and scope

The source is `Argument.md` at immutable revision
`62dae66fcf92bdc82df1d8b10e161278c4351aa0`, directly inspected at lines
200, 243, and 303–315. Components mean distinct actual prime powers with
positive exponents. The fixed core is `3*5*7*13`; the remaining odd-exponent
component is `p^e`, with `p>13`, `p%24=1`, and positive odd `e`. Equation (5)
and `s=a-7` give five unspecified square components when `a=12`.
No additional congruence is imposed on their bases: contamination by primes
3 modulo 4 is permitted.

The canonical installed `erdos fetch 1052` reports the question “Are there
only finitely many unitary perfect numbers?” and lists the five known examples.
The installed `erdos search 'unitary perfect numbers'` and `erdos list` report
problem 1052 as open. This metadata is not a proof. No consequential sequence
question arose, so no OEIS query was used.

## Selected contract

`Erdos1052.a12_e3_forces_eleven_square` takes natural numbers
`p,e,q1,...,q5,d1,...,d5`, the source conditions, `3 ≤ e`, the positive
`di`, the component conditions for each of the five bases, pairwise
inequality of `[p,q1,q2,q3,q4,q5]`, and the full left-associated canceled
identity. Component conditions are packaged as a universal predicate over
the explicit five-element finset, exactly equivalent to the five individual
conjunctions. Its conclusion is the five-way disjunction
`qi = 11 ∧ di = 1`. The seed is derived, not assumed.

## Proof and finite-to-universal transfer

* The residue and primality conditions imply `73 ≤ p`: the only possible
  smaller residues are 25 and 49, both composite. Therefore `73^3 ≤ p^e`.
* Exhaustive prime-gap exclusion proves that an allowed square base is 11,
  17, 19, or at least 23. Without a seed, a base 11 has `di ≥ 2` and
  denominator at least `11^4`; all other bases have exponent at least two.
* Each square abundance is at most `A=290/289` for bases 17 or 19 and
  at most `B=530/529` otherwise. Reciprocal monotonicity explicitly transfers
  the natural denominator bounds to these rational bounds.
* Exhaustive symbolic splitting of the five exceptional-membership
  propositions, with pairwise distinctness, proves the product is at most
  `A^2*B^3`. Impossible branches require three distinct elements of `{17,19}`.
  This is a universally quantified finite certificate, not a sample search.
* Casting the full identity to rationals and clearing nonzero denominators
  gives abundance `65/64`. Monotonicity bounds it above by
  `(1+1/4096)*(1+1/73^3)*A^2*B^3`. Exact rational normalization proves that
  this upper bound is strictly smaller than `65/64`, a contradiction.

There is no asymptotic extrapolation. The power and reciprocal inequalities
are the transfer to arbitrary admissible exponents and bases.

## Boundaries and remaining obligations

Natural subtraction is not used; all denominator powers are nonzero because
the bases are prime. All five index slots exist explicitly. Concrete examples
check the jointly satisfiable arithmetic/component/distinctness side data,
including the no-seed case `q=11,d=2`. No existence claim is made for a full
unitary-perfect model satisfying the identity.

This proof is conditional on `e ≥ 3`. The `e=1` case, global fixed-core
applicability, the `a=12` reduction, Wall's `a>10` premise, and global finiteness
remain unpaid.

## Compiled downstream consumer

`Erdos1052.a12_e3_forces_sixty_one_not_dvd_eighty_one`, in the separate
`Unitary1052A12E3Force61.lean` module, has exactly the same premises and full
identity. Its conclusion is the five-way disjunction `qi = 61 ∧ ¬ 81 ∣ di`.
It splits the derived 11-square disjunction, substitutes the actual base and
exponent, transports distinctness by explicit `List.Perm` proofs, and reorders
the full identity by commutativity. Each branch directly applies the already
paid `a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one` consumer with the
four remaining slots and their unchanged component/exponent conditions.
Thus the permutation/consumer bridge is compiled, not unpaid. There is no
hidden existential exponent or newly assumed seed.

## Verification receipts

The first narrow build failed at dependency resolution: this checkout lacks
`Mathlib.Data.Rat.Order` and `Mathlib.Tactic.Omega`. After correcting imports,
the prime-gap candidate check required the installed `NormNum.Prime`
extension. The corrected gap lemmas compiled. The main proof's first attempt
hit the default heartbeat limit in repeated `tauto`; explicit disjunction
injections removed that incidental search. Neither failure was a mathematical
counterexample.

The seed module subsequently compiled with exit 0 (reported elaboration
7.0 seconds), and the downstream consumer compiled with exit 0 (6.1 seconds).
A separate disposable leaf audit was then executed with one Lean thread and
a 4000 MB ceiling, under `timeout --kill-after=2s 60s` and task limit 70 seconds.
All seven full signatures were inspected. All seven axiom reports are subsets
of `{propext, Classical.choice, Quot.sound}`; both main theorems report exactly
those three. No `sorry`, declared axiom, or `native_decide` is used. Production
modules retain no signature/axiom-print commands. Compilation and axiom review
do not establish existence of a full model satisfying the canceled identity.

After the two tactic-linter warnings were removed, a narrow build of precisely
both new production modules completed with exit 0 and no warnings. A repeat
of the same disposable signature/axiom audit on the rebuilt modules completed
with exit 0, unchanged signatures, and the same permitted axiom reports.
The audit leaf was removed; only the two production Lean files and this note
are episode artifacts. Coordinator-owned review and adoption remain separate
gates.

