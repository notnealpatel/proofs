# Odd-gap reflection targets: formalized bounds and status

## Statement and status

The finalized source at `9e0c2540e38169a177571b2c30f2a5f30d9fb562`,
`Proofs/Erdos/Erdos142/ReflectionOddGapTargets.lean`, proves the following
for every finite `A ⊂ ℤ`, integer `d,h`, and scalar 3-AP-free `A`, assuming
`h % 2 = 1`. Put

\[
 S=\nu(d-h)+\nu(d)+\nu(d+h),\quad
 q=\#\{a\in A:(a-d)\bmod2=0\},\quad
 r=\#\{a\in A:(a-d)\bmod2=1\}.
\]

Then
\[
 2S\le 3|A|+\min(q,r),\qquad 4S\le7|A|.
\]
The public declarations are `two_mul_reflectionMultiplicity_oddGap_le` and
`four_mul_reflectionMultiplicity_oddGap_le`. These are kernel-checked
unconditional integer statements: there are no interval, minimum-size,
positive-gap, or positive-mass assumptions. Negative odd gaps are included,
and parity is relative to `d`, not absolute parity. The accepted adoption
checkpoint is `01d6a6fa7c69737b1512877389d408ca395965df`; its finite-2(m−1)
bound and strict-rich-target AP-freeness are already semantic and foundations
CLEAN for the original graph, `2S`, and `7/4` material. The focused build and standard axiom audit confirmed precisely `propext`, `Classical.choice`, and `Quot.sound`. An independent vacuity review of the exact original source was CLEAN. A reviewer whole-umbrella attempt timed out after 120 seconds in unrelated modules; this is superseded as a verification obstacle by the successful final independent audit below, but remains part of the chronology. The parent independently copied a byte-identical module and umbrella from prover output `c5266c8f0d5a02d4d1bfd14a01b0e81e10663b96`, verified them with `cmp`, built the focused target and full `Erdos` umbrella successfully, and checked all three exact public statements and axioms. The new module emitted no diagnostics; the umbrella replayed only old unrelated warnings, including sorry warnings. The rebased mechanical output `dd742b8f9b68f4ec3869246fdcbf22564a750429` still has unavailable build completion and is superseded by this final check. The incremental semantic review of the five-thirds result is CLEAN with no findings. Foundations/provenance review and new-result adoption remain pending. Issue [#80](https://github.com/thatnealpatel/proofs/issues/80)
was requested for primary novelty evaluation. No novelty claim is made.

## Proof in prose

Translate conceptually by `d`, writing `B=A-d`; the Lean proof works directly
at arbitrary `d` and does not require a translation lemma. For each normalized
target `s∈{-h,0,h}`, draw an arc `a → 2a-s` whenever both vertices are in
`B` and `a≠s`. Across the three labels there are exactly `S` arcs: the
reflection map is injective on admissible centers, so each label contributes
its reflection multiplicity. There are no loops, and the three labels are
pairwise distinct because `h` is odd.

A vertex has outdegree at most two. Three outgoing labels would put three
endpoints in a nonconstant 3-term progression, contrary to scalar
3-AP-freeness. Endpoint parity equals target parity. Thus a relative-even
vertex can receive only the middle label and has indegree at most one, while a
relative-odd vertex can receive only the two outer labels and has indegree at
most two. Consequently every total degree is at most four.

Let `H` be the degree-four vertices. Every member of `H` is relative odd and
has both outer-label predecessors. Those predecessors differ by `h`, hence
exactly one is relative even. Select that even predecessor. This selection is
injective: if one source fed two distinct saturated successors, the labels
would be opposite outer labels. The other predecessors would then be `a-h`
and `a+h`; together with `a` they form a forbidden nonconstant progression.
Therefore `|H|≤q` and `|H|≤r`.

Handshake counting now gives the first inequality. All vertices outside `H`
have degree at most three, while members of `H` have one extra unit, so
`2S≤3|A|+|H|≤3|A|+min(q,r)`. Relative parity partitions `A`, hence
`q+r=|A|`; using `2 min(q,r)≤q+r` yields `4S≤7|A|`.

## Strengthened formal theorem

**Kernel checked.** Prover output `c5266c8f0d5a02d4d1bfd14a01b0e81e10663b96` now implements `Erdos142.three_mul_reflectionMultiplicity_oddGap_le`, with the same arbitrary `A,d,h`, `ThreeAPFree`, and `h % 2 = 1` hypotheses, concluding `3S≤5*A.card`. The generic private endpoint-parity bound needs no AP-freeness. Focused build, signature checks, and axiom checks passed with exactly `propext`, `Classical.choice`, and `Quot.sound`; extra odd-middle and negative-odd-gap examples compile. The parent final independent audit copied the byte-identical module and umbrella, verified `cmp`, built the focused target and full `Erdos` umbrella successfully, and checked all three exact public statements and axioms. The new module emitted no diagnostics; the umbrella replayed only old unrelated warnings, including sorry warnings. The incremental semantic review is CLEAN with no findings; foundations/provenance review and adoption remain pending.

Endpoint parity gives `ν(d)≤q` and `ν(d-h),ν(d+h)≤r`, hence `S≤q+2r`; combining this with the existing kernel-checked `2S≤3m+min(q,r)≤3m+q` yields `3S≤3m+2q+2r=5m`, or `S≤5m/3`. The older `4S≤7m` theorem remains unchanged.

## Pruned routes and regression boundaries

Two tempting graph arguments are explicitly pruned. The set
`{-17,-6,-5,-3,1,2,4}` with `h=7,d=0` is scalar 3-AP-free and has
`(ν(-7),ν(0),ν(7))=(3,3,4)`, hence `S=10`. The displayed outer-label arcs
`-5→-3→1→-5` form a cycle, so a degree-four argument cannot assume that
saturated components are acyclic or that a charge must terminate. The set
`{1,2,4,5,10,11,13}` with `h=3,d=0` is another scalar-free regression:
vertex `5` has degree four, while even predecessor `4` has two outgoing
neighbors `11,5` although `8` is absent. Thus saturation does not force an
iterated doubling continuation. The source explicitly checks these finite
facts by `decide` (including the scalar-freeness, multiplicity, cycle-edge,
and missing-doubling conjunctions); they are regression models, not separate
general theorems. Neither example refutes the universal conjectural bound
`S≤floor(3|A|/2)`.

## Informal dyadic extension (not Lean)

The earlier `α_0=7/4` formulation is superseded by the stronger prose lead.
For `h=2^k t` with `t` odd and `k∈ℕ`, the current intended extension is
\[
 (k+6)S\le2(k+5)|A|.
\]
Its parity split, scaling identity, and induction remain not Lean formalized.
The recurrence is `α_{k+1}=4/(4-α_k)`, starting at `α_0=5/3`, hence
`α_k=2-2/(k+6)`. For even `h`, normalized endpoints are even; even-source
arcs scale to a smaller odd-valuation problem, while odd-source arcs contribute
at most `2r`. If `m≥1`, this may be combined informally with the finite
`2(m−1)` bound, but it makes no asymptotic claim.

The odd-gap result is a local reflection estimate only. It gives no global
energy improvement (`S` is not the global `E=Σν²`, whose ordered collision
diagonals remain distinct), no O/C result, and no closure of Erdős 142. In
particular, the current five-thirds prose threshold cannot by itself make
every gap AP-free: even gaps remain uncovered. The universal `3|A|/2` bound
remains OPEN. Parent reran its exact Sage audit with assertions for
`S≤q+2r`, `3S≤5|A|`, and the improved dyadic inequality: it passed 705
scalar-free caps in `[0,12)`, 84,302 integer target APs with at least two
supported targets, and the same maximum `S/|A|=3/2` witness `A={0,1,3,4}`,
targets `(-1,2,5)`, `S=6`, in 0.76 seconds. This is computation only, from
the intentionally unintegrated parent file `Proofs/Scratch/Erdos142DyadicAudit.sage`
and task `parent-improved-dyadic-small-audit`. The old N14 launched audit
remains unavailable and is not presented as passed.
