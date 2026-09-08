# Erdős–Lovász: the elementary pair-cover lower bound

## Status

This candidate selects exactly

```lean
Palomar.ErdosLovaszPairCover.two_mul_sub_one_le_erdosLovaszNum
    {r : ℕ} (hr : 0 < r) :
    2 * r - 1 ≤ Palomar.ErdosLovaszPairCover.erdosLovaszNum r
```

The Challenge and Solution freshly elaborate in the pinned Lean environment,
and the selected Solution theorem has axiom closure exactly `propext`,
`Classical.choice`, and `Quot.sound`. Comparator, export, Landrun, and NanoDa
are **NOT RUN** because their executables are unavailable. The compilation and
metadata checks below are a packaging self-audit. An independent AI vacuity
review of the frozen Lean bytes is recorded separately; it is not human review.

This is **not yet mechanically admissible for Palomar submission**. The current
policy requires nonempty human `project.authors` and
`project.responsible_maintainers`, but those identities and submission
authorization were not supplied. The metadata leaves both lists empty and names
the blocker rather than inventing people. The independent AI vacuity review
passed on the frozen Lean bytes at the recorded old revision. The PC-1-corrected
metadata still awaits final foundations recheck, and human review remains
pending. Nothing here claims registration, acceptance, endorsement, or
readiness to submit.

## Independent statement model

For a finite family `F : Finset (Finset α)`, the package predicate says:

1. every edge has cardinality `r`;
2. every two edges are non-disjoint, including an edge paired with itself;
3. every finite set of cardinality less than `r` is disjoint from some edge.

The diagonal case in (2) excludes the empty edge. Clause (3) says that no set
of fewer than `r` vertices is a transversal. Conversely, when `0 < r`, every
edge is nonempty and, by intersection, is itself an `r`-vertex transversal.
Thus the three clauses describe an `r`-uniform intersecting finite hypergraph
with transversal number exactly `r`.

The attainable edge-count set is

```lean
{k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))),
  IsErdosLovaszFamily r F ∧ F.card = k}
```

where `N` ranges over **all** natural numbers. There is no bounded-ground
substitution. The invariant `erdosLovaszNum r` is the natural infimum of that
set.

The positive guard is material. `Nat.sInf` is totalized, so an empty index
would return zero. Both Challenge and Solution prove nonemptiness for every
`0 < r` using all `(m+1)`-subsets of a `(2m+1)`-vertex set, and then prove that
the infimum is attained by an actual family. The Solution separately checks the
repository's `erdosLovaszNum_mem` after establishing definitional equality of
the predicate, attainable-count set, and invariant. The selected source proof
uses that attained family.

Ground checks include:

- the empty family on `Fin 0` is an honest family at `r = 0`, and `g(0) = 0`;
- the empty family on `Fin 0` fails at `r = 1`;
- the one-edge singleton family satisfies the predicate at `r = 1`;
- the three edges of a triangle satisfy it at `r = 2` and attain count three;
- in the Solution, the selected inequality is sharp at `r = 1` and `r = 2`.

These jointly instantiate the definitions and distinguish the honest `r = 0`
value from the positive-parameter nonempty-infimum regime.

## Proof mechanism and scope

The reusable source theorem

```lean
exists_isTransversal_two_mul_card_le
```

works for a finite family of nonempty, pairwise-intersecting edges over an
arbitrary ground type. It gives a transversal `T` satisfying
`2 * T.card ≤ F.card + 1`. Informally, pair distinct edges and choose a common
vertex for each pair; if one edge remains, choose one vertex from it. The Lean
proof implements this by strong induction, avoiding an ordered pairing or a
finite-ground assumption.

For an Erdős–Lovász family, the no-small-cover clause forces `r ≤ T.card`, so
`2*r ≤ F.card+1` and hence `2*r-1 ≤ F.card`. The source then obtains an actual
minimum family from `erdosLovaszNum_mem hr` and transports the family-level
bound to `g(r)`. The package selects only the all-positive-`r` invariant bound;
the structural lemma is explained as proof mechanism, not added as another
Comparator target.

This is an elementary known lower bound, not a state-of-the-art estimate. The
exact structural inequality and proof appear as Fact 17 in §3.1 of Neal
Bushaw, James Danielsson, and Glenn Hurlbert, *Erdős-Ko-Rado Theorems for
Paths in Graphs*, arXiv:2504.05406v1 (7 April 2025): for an intersecting
family `F`, `τ(F) ≤ ⌈|F|/2⌉`, proved by pairing its sets, selecting a shared
element from each pair, and selecting one element from a possible unpaired
set. Applying `τ(F)=r` gives `2*r-1 ≤ |F|`, exactly the source proof mechanism.

This source was located after the recorded Lean proof had been constructed;
the Lean proof does not import or assume Fact 17. That chronology is not a
claim of retrieval-blind discovery, novelty, or priority. Erdős and Lovász's
published `8r/3 - 3` bound and later results are stronger in the relevant
large-parameter regime. Sivashankar's arXiv:2606.24878 proves `3r - 4` for all
positive `r` and a stronger asymptotic coefficient. The candidate makes no
novelty, priority, significance, or source-author-endorsement claim.

## Package boundary and production disclosure

- `Challenge.lean` imports only `Mathlib`, fully states the model, and contains
  exactly one deliberate theorem hole: the selected theorem.
- `Solution.lean` does not import Challenge. It repeats the independent model,
  proves definitional bridges to the source, verifies positive-`r` attainment,
  and applies the accepted source theorem. It has no holes.
- `comparator.json` names one theorem and only the three permitted axioms.
- `formalization.yaml` records provenance, scope, AI production, review status,
  and blockers.
- `verification.md` records exact commands, outputs, hashes, comparisons, and
  tooling limitations.

The source proof was materially AI-assisted by **gpt-6-astra, xhigh**, through
Yah. This separate packaging was performed by **gpt-5.6-sol, high**, through
Yah. No subagent participated in packaging. An independent AI foundations
review of the exact combined candidate revision
`dcf241b5a1f33b86325e82d575fa588d9a3575e6` found the formal statement and
model faithful but required the prior-art correction now recorded here. That
review is not human approval and did not review or approve this corrected
revision. A separate independent AI vacuity review passed at that same exact
revision on the frozen Lean sources: Challenge SHA-256
`80d50b25af6a8266a7c2402149a1a74afdd5dd9f44e58cb20cbe41ec07a004ae` and
Solution SHA-256
`b825d9ba1a28136cad53a1a44fe7085e0949136b37dea80b9925e28d434aecde`.
It reported no semantic, trust, or material-style findings after checking all
three package/source proofs, separately compiling the six reviewed package
Lean modules, checking raw types and the model, and confirming standard-three
selected closures. This was an independent AI review of those exact Lean
bytes, not human approval or approval of the corrected metadata. Final
foundations recheck of the PC-1 correction and human review remain pending.
Human formalization authors and responsible maintainers are unknown; they must
be identified truthfully, and authorization confirmed, before submission can
be considered.
