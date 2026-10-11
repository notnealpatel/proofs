# Palomar/Melfi — prepared candidate

**Status:** PREPARED candidate package for USER review for issue [#45](https://github.com/thatnealpatel/proofs/issues/45). This is a review package, not a Palomar submission. The Challenge, Solution, `comparator.json`, metadata, and verification evidence are present; no submission, acceptance, or publication is claimed.

## Candidate and exact claim

The single selected headline is:

```lean
theorem Nat.even_eq_practical_add_practical {n : ℕ} (heven : Even n) (hn : 0 < n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n
```

Thus every **positive even natural number** is a sum of two practical numbers. The
`0 < n` hypothesis is essential: zero is even, whereas a sum of two practical
numbers is positive. The package also contains the equivalent `2 ≤ n` alias,
but does not present it as a second result. Practicality is the ordinary
positive-number/divisor-sum predicate defined in the Challenge and Solution.

The substantive development is `Proofs/Enumerative/MelfiPracticalSum.lean`; the
package wrapper is `Palomar/Melfi/Solution.lean`. Its proof uses an alternative
covering architecture based on powers of two and twice powers of three, rather
than claiming to reproduce Melfi's published route. The result is known
mathematics, not a new theorem or a priority claim.

## Source gate and comparison

The source-reading gate is **PASS** for the survey source:

- Giuseppe Melfi, “A survey on practical numbers,” *Rendiconti del Seminario
  Matematico della Università di Torino* **53** (1995), 347–359,
  [public PDF](https://seminariomatematico.polito.it/rendiconti/cartaceo/53-4/347.pdf).
- The reading covered printed pp. 349–351, including Proposition 3, Lemma 4,
  Lemma 5, and Theorem 6.

The survey states Theorem 6 (every positive even integer is a sum of two
practical numbers), records multiplier closure in Lemma 4 (in particular the
useful bound `n ≤ 2m`), and gives the twin-practical construction with seed
`{16, 30, 54, 88, 160}`, successors `r²/2 + 2r` and `r² + 3r`, and overlapping
windows `[m²/2, 7m²/2]`. The formal development instead uses practical families
`2^k` and `2·3^j`, windows
`[2^k(3^j+1), 2^(2k+1)]` under
`3^(j+1) ≤ 2^k < 3^(j+2)`, and the separate cases `2, 4, 6` to tile `n ≥ 8`.
This supports a source-checked route comparison, not a claim of proof-theoretic
independence, novelty, priority, or first formalization.

The survey notes that the detailed middle-interval and recursion arguments use
[8, Lemma 2] and [8, Theorem 1], respectively. The cited original paper is
recorded for attribution (Giuseppe Melfi, *Journal of Number Theory* 56 (1996),
205–210, DOI [10.1006/jnth.1996.0012](https://doi.org/10.1006/jnth.1996.0012)),
but that paper was not independently read here. No claim is made that all of
those subsidiary arguments were rederived.

## Mechanical evidence and limitations

The selected wrapper mechanically passed the Challenge/Solution checks and the
Comparator evidence records PASS; the selected declaration has exactly the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx` dependency. The archived Coleman theorem is unrelated and outside
the selected theorem's dependency closure. The current authoritative evidence
is `Palomar/Wave4ComparatorEvidence.yaml`; an older Comparator NOT RUN record in
`verification.md` is historical only.

This preparation is AI-assisted and is not human mathematical, attribution, or
source-fidelity review. Human identities and human review remain pending and
are intentionally not invented. In particular, `authors`,
`responsible_maintainers`, and reviewer fields remain empty, and the package is
not submitted. Prior formalization status for this specific Melfi theorem has
not been established; no global novelty or priority claim is made.

## Audience and recommendation

The intended audience is researchers in elementary/additive number theory and
practical numbers, with a secondary formal-methods audience interested in a
machine-checkable alternative proof architecture. The candidate is ready as a
bounded package/evidence receipt for USER review, subject to the explicit human
identity and review blockers above.
