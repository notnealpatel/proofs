# Palomar/Melfi — scouting candidate

**Status:** bounded scouting note for issue [#45](https://github.com/thatnealpatel/proofs/issues/45), not a submission package. No Challenge, Solution, Comparator configuration, metadata, registration, or publication is included here.

## Candidate and exact claim

The recommended headline is the source-based formalization

```lean
theorem Nat.even_eq_practical_add_practical {n : ℕ} (heven : Even n) (hn : 0 < n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n
```

This says that every **positive even natural number** is a sum of two practical
numbers. The `0 < n` hypothesis is load-bearing: `0` is even, while the
positivity conjunct in `Nat.Practical` makes a sum of two practical numbers
positive. The file also provides the equivalent `2 ≤ n` presentation:

```lean
theorem Nat.melfi_thm_6 (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n
```

The alias should not be advertised as a second mathematical result. Possible
supporting declarations, if a future package genuinely needs them, are:

- `Nat.Practical.mul_of_le_one_add_sum_divisors`;
- `Nat.Practical.mul_of_le_two_mul`;
- `Nat.practical_two_mul_three_pow`;
- `Nat.two_mul_one_add_sum_divisors_two_mul_three_pow`;
- `Nat.exists_practical_add_practical_of_window`;
- `Nat.exists_three_pow_bracket`;
- `Nat.exists_pow_window`.

The preferred package headline remains the first theorem, with only the
multiplier lemma or window lemma added as a companion if it improves auditability
rather than merely exposing proof infrastructure.

## Actual formal development and dependencies

- The substantive file is `Proofs/Enumerative/MelfiPracticalSum.lean`.
- Its direct import is exactly `Enumerative.Practical`.
- `Proofs/Enumerative/Practical.lean` directly imports `Mathlib` and defines the
  project predicate `Nat.Practical` as `0 < n` together with the requirement
  that every `m ≤ n` is a sum of distinct divisors of `n`.
- The Melfi file proves the stronger divisor-sum characterization, a multiplier
  closure lemma, practical families based on `2^k` and `2 · 3^j`, a modular
  covering window, a tiling of all `n ≥ 8`, and the small cases `2, 4, 6`.
- The covering route is the development's alternative route: it uses the two
  practical modulus families and does not formalize Melfi's twin-practical
  sequence construction. The source comments describe it as an elementary
  replacement, not as new mathematics.
- `Practical.lean` also contains the deliberately archived, unrelated
  `sorry` declaration `Nat.coleman_multiperfect_practical`. The source file
  claims the Melfi declarations avoid it, but that claim has not been freshly
  checked for this scouting snapshot.

For a future Palomar package, the Challenge cannot import this project module:
its transitive imports would include project-specific source. The Challenge
should state the ordinary practical-number definition and theorem using only
Palomar-allowlisted imports (normally Mathlib); a separate Solution may bridge
to this existing development. The Challenge/Solution declaration names and
types must then match exactly.

## Attribution, significance, and audience

The mathematical theorem belongs to Giuseppe Melfi. It is the practical-number
analogue of a Goldbach statement: Margenstern posed the conjecture and Melfi
proved that every positive even integer is a sum of two practical numbers. The
candidate is therefore a **formalization of known mathematics**, not a claim of
a new theorem. Its plausible audience is researchers in elementary/additive
number theory and practical numbers, with a secondary formal-methods audience
interested in an independently checkable proof architecture.

The formalization's defensible contribution is a machine-checked statement and
proof, including a direct proof of the multiplier lemma and the documented
two-family covering argument. It must not be described as Melfi's original
proof route or as a first formalization without a new, properly bounded
literature search.

## Mathematical sources and prior formalization

Primary mathematical source:

- Giuseppe Melfi, “On Two Conjectures about Practical Numbers,” *Journal of
  Number Theory* **56** (1996), 205–210, DOI
  [10.1006/jnth.1996.0012](https://doi.org/10.1006/jnth.1996.0012). Melfi's
  own publication page and author-hosted PDF were retrieved at
  `http://members.unine.ch/giuseppe.melfi/articoli/jnt.pdf`.

The PDF is an authoritative author-hosted copy, but its custom Type-3 font
encoding did not yield reliable text extraction. The paper's bibliographic
identity and theorem-level abstract were corroborated by the publisher search
record. The detailed proof was **not independently read** in this scouting
pass. Consequently, any comparison between this development's `2^k`/
`2·3^j` covering and Melfi's twin-practical proof remains qualified and should
not be presented as a fully source-verified proof comparison.

The Lean module also cites Melfi's “A survey on practical numbers,” *Rend.
Sem. Mat. Univ. Pol. Torino* **53** (1995), 347–359, and earlier work of
Margenstern, Srinivasan, Stewart, and Sierpiński. Those citations are useful
background and attribution leads; they are not evidence that the corresponding
proof details were freshly verified here.

Prior formalization leads recorded in the ignored draft include Google's
`formal-conjectures` repository, which had `Nat.IsPractical` and a proved
`factorial_isPractical` at the dated revisions cited there. The draft also
records a dated search sweep across Mathlib, Isabelle AFP, Coq/Rocq, Mizar,
GitHub, Lean Zulip, and an AlphaProof nexus. These are **old audit/search
records, not fresh checks**, and do not support any global novelty or priority
claim. The README should say that prior formalization status for Melfi's
specific theorem is not established here.

## Production and review limitations

The repository's root README says that proofs in `Proofs/` were at least partly
or wholly AI-assisted and may be incorrect or not rigorously human-vetted. This
scouting note does not constitute human mathematical review, and no claim of
human review should be made in future metadata without actual review evidence.

Known limitations and blockers before a package could be proposed:

1. Fresh compilation of `Proofs/Enumerative/MelfiPracticalSum.lean` was **not
   run** in this scouting turn.
2. A fresh targeted axiom audit was **not run**. In particular, the in-file
   `#print axioms` commands and prose are not themselves audit evidence. The
   selected declarations must be checked against exactly
   `propext`, `Classical.choice`, and `Quot.sound`.
3. Independence from `Nat.coleman_multiperfect_practical` (the unrelated
   `sorry`) remains **unverified** here and must be mechanically established
   for every declaration selected for comparison.
4. The primary-source PDF was retrieved, but its detailed proof was not
   independently read; the alternative-route comparison remains qualified.
5. A future package still needs a small ordinary Challenge, a separate Solution
   bridge, Comparator configuration, current `formalization.yaml`, a compatible
   pinned snapshot, and recorded verification inputs. None is prepared here.
6. The result is source-based and established; no global claim of novelty,
   priority, or first Lean formalization is made.

## Recommendation

Keep Melfi as a candidate for USER review, with
`Nat.even_eq_practical_add_practical` as the sole headline. It is a recognizable
and nontrivial practical-number theorem with a credible specialist audience,
but the candidate should be presented honestly as a formalization of Melfi's
known result and as a checked alternative proof architecture only after the
fresh compilation, declaration-level axiom/dependency audit, and source review
blockers above are addressed.
