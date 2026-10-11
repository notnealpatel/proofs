/-!
# Maximal complex irreducible degree of SL(n,2) — A062733

## Current archive status

Documentation-only archive of a refuted proposed formula and an unpaid formal
counterexample target. The basename `SL2MaxDegree` refers to the field of two
elements, not a replacement problem for the fixed group SL(2). No imports,
definitions, theorem statements, or admissions are introduced here. In
particular, **the known-false proposed maximum equality is not admitted**.
The historical `stmt: M` and proof-route metadata are not formal declarations.

## Remaining target and hypotheses/representation

Formalize an irreducible complex character of `SL(8,2) = GL(8,2)` of degree
`359810304`, establish that this degree occurs in the group's actual irreducible
character-degree multiset, and derive the strict lower bound contradicting the
proposed degree `353730560`. Alternatively, formalize the source's family of
witnesses for every integer `n` with `8 ≤ n`. This is not a target to identify
the true maximum, and it is not the separate historical degree-8 example at
`n = 3`. The finite matrix group over `𝔽₂`, its canonical group structure, the
complex irreducible representations, and the bridge to the existing multiset
must be specified; no abstract substitute group is sufficient.

The historical formula only purported to hold for `3 < n`. The family witness
uses `8 ≤ n`, so the expressions involving `n-4`, `n-5`, `n-3` and products have
nondegenerate ranges. A future formal arithmetic representation must justify
exponent integrality and division by 3 and 45 rather than relying on truncated
natural subtraction/division. There is no such new representation here.

## Known prerequisites, corrected witness, and named blocker

The inspected headers of `GroupTPP/CharDegrees.lean` and
`GroupTPP/Wedderburn.lean` supply canonical character-degree multisets and the
Wedderburn block-size bridge. They do not supply Jordan/Green parametrization,
the relevant semisimple centralizer `GL(n-4,2) × GL(2,4)`, Steinberg degrees,
or their identification in the actual group's character-degree multiset.

Named blocker: **Jordan character-degree witness-to-charDegrees bridge**.
The corrected comparison `359810304 > 353730560` at `n = 8`, with ratio
`651/640`, is sourced mathematical prose preserved from the card, **not a
Lean-checked character witness or formal counterexample**. The card attributes
the argument to standard Jordan character-degree correspondence and cites
arXiv:1808.07116 §4; this documentation task performs no new source verification
or character construction. Agreement of OEIS terms or a related column does
not certify a maximum. No theorem closure, true-maximum formula, or novelty
claim is made.

## Historical/source-card subsection (verbatim)

Source: `Formalize/A062733-zabolotskii-sl-n-2.md`. The complete current card text follows;
historical metadata is not promoted to a formal declaration.

```text
seq:     A062733
claim:   zabolotskii-closed-form
status:  refuted mathematically; formal counterexample pending
stmt:    M
proof:   L (representation-theory bridge)
module:  Proofs/GroupTPP/CharDegrees.lean,
         Proofs/GroupTPP/Wedderburn.lean (machinery)
source:  OEIS A062733 formula, Andrei Zabolotskii, 2025-05-27;
         Jordan decomposition background: arXiv:1808.07116, section 4

HISTORICAL CLAIM (NOT AN ASSUMPTION)
  a(n) is the maximal degree of a complex irreducible representation
  of SL(n,2) = GL(n,2). The source proposes, for n > 3,
    D_n = 2^((n-2)(n-3)/2) * (2^n - 1) * (2^(n-1) - 1) / 3,
  from apparent agreement with |column k=2 of A135950|.
  The listed OEIS terms and that agreement do not certify a maximum.

REFUTATION
  For n >= 8, a semisimple parameter with centralizer
    GL(n-4,2) x GL(2,4)
  and the Steinberg characters of both factors yields, by the standard
  Jordan character-degree correspondence, an irreducible degree
    E_n = 2^((n-4)(n-5)/2 + 2)
          * product_{j=n-3}^n (2^j - 1) / 45.
  In particular E_8 = 359810304 > D_8 = 353730560, with ratio 651/640.
  Thus the proposed universal maximum equality is false. This is a
  source-based mathematical argument, independently reviewed, NOT a
  Lean-checked counterexample or identification of the true maximum.
  No theorem asserting the refuted equality may be admitted.

REMAINING TARGET
  Formalize the n=8 character-degree witness and resulting strict lower
  bound, or the family a(n) >= E_n for n >= 8. Existing CharDegrees and
  Wedderburn infrastructure does not supply Jordan/Green parametrization,
  semisimple centralizers, Steinberg degrees, or their charDegrees bridge.
  The historical n=3 degree-8 example is distinct from this refutation;
  neither its formalization nor a novelty claim is established here.
```
-/
