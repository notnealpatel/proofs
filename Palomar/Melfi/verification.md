# Verification record: Melfi practical-number sum

## Current status

This is a preparation receipt for USER review, not a Palomar submission. The
current authoritative manifest `../Wave4ComparatorEvidence.yaml` records
**PASS** for `Palomar.Melfi.even_eq_practical_add_practical` and supersedes the
older local Comparator NOT RUN note. Human review remains **UNCHECKED**.
Mechanical PASS is not human approval, a novelty or priority claim, or a
submission/publication claim.

## Source gate: PASS

The source gate was closed by reading Giuseppe Melfi, “A survey on practical
numbers,” *Rend. Sem. Mat. Univ. Pol. Torino* 53 (1995), 347–359,
[public PDF](https://seminariomatematico.polito.it/rendiconti/cartaceo/53-4/347.pdf),
printed pp. 349–351: Proposition 3, Lemma 4, Lemma 5, and Theorem 6.

The survey's Theorem 6 states that every positive even integer is a sum of two
practical numbers. Lemma 4 gives the multiplier closure condition
`n ≤ σ(m)+1` (and the useful `n ≤ 2m` bound used here for the relevant practical
numbers). The survey's twin-practical route uses seeds
`{16, 30, 54, 88, 160}`, successors `r²/2 + 2r` and `r² + 3r`, and overlapping
windows `[m²/2, 7m²/2]`. The Lean development instead uses practical families
`2^k` and `2·3^j`, windows
`[2^k*(3^j+1), 2^(2*k+1)]` under
`3^(j+1) ≤ 2^k < 3^(j+2)`, and the separate cases `2, 4, 6`.
This is a source-checked route comparison only: it does not establish
proof-theoretic independence, novelty, priority, or first formalization.

The survey attributes the middle-interval and recursion arguments to [8,
Lemma 2] and [8, Theorem 1]. The cited original paper is bibliographically
recorded in `formalization.yaml` (Melfi, *JNT* 56 (1996), 205–210,
DOI 10.1006/jnth.1996.0012), but was not independently read here. Those
subsidiary arguments are therefore not claimed to have been rederived. This
research record is not human review.

## Mechanical checks

- Challenge elaboration: **PASS**; the one warning is the intentional Challenge
  hole.
- Solution build: **PASS**.
- Selected theorem axiom audit: **PASS**; exactly `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
- Comparator evidence: **PASS**, according to the authoritative manifest named
  above. The package source relationship recorded there covers this package.

The selected wrapper transports the repository theorem
`Nat.even_eq_practical_add_practical` across the matching practical predicate.
The imported development contains an unrelated archived Coleman `sorry`; the
selected theorem's declaration-level audit excludes it.

## Fresh imported-module audit

At exact base `2a3cd431d0056a242ac3d001ea6e446a2256379b`, the coordinator ran a
narrow `lake` build of `Palomar.Melfi.Solution`, followed by a scratch import
of `Solution` with expanded `#check` of both wrapper/source declarations,
`#print` of both `Practical` definitions, and `#print axioms` for both
results. Both wrapper and source have exactly `[propext, Classical.choice,
Quot.sound]`. The predicates are literally identical (`0 < n` together with a
finite subset of `n.divisors` covering every `m ≤ n`), and the positivity guard
is preserved. The imported module's Coleman warning is unrelated to these
closures. Full log: `/home/exedev/x/erdos/prize-portfolio/evidence/melfi-issue45-import-audit.log`.

This is an imported-module audit, not a new Comparator run. The scratch audit
source is not adopted. The present change is documentation-only and leaves the
audited Lean code unchanged; USER review will verify the package state. The
inherited authoritative manifest PASS remains the current Comparator evidence.


The following is retained historical evidence from the preparation work; it is
not a current blocker and does not override the manifest PASS.

Challenge command:

```sh
ulimit -v 8388608
timeout 180s lake env lean -M 5000 -j 1 Palomar/Melfi/Challenge.lean
```

Solution command:

```sh
ulimit -v 22544384
timeout 720s taskset -c 0 lake --no-ansi build Palomar.Melfi.Solution
```

The successful logs were retained at the preparation paths recorded in the
prior receipt (`challenge-final.log`, `solution-build-affinity1.log`, and
`axiom-audit.log`). Earlier resource failures and the old Comparator NOT RUN
attempt are historical attempts only; no obsolete tooling blocker is asserted
as current, and `comparator.json` was not changed to bypass them.

## Review and unpaid contract items

USER review, human mathematical/source-fidelity review, authoritative human
authors, and a responsible human maintainer remain pending. The metadata keeps
those identity and reviewer fields empty rather than inventing people. The
package is prepared as evidence for USER review and has not been submitted.
No event/receipt date is asserted here. No mathematical, novelty, priority, or
Palomar acceptance claim is made.
