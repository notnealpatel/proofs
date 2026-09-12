# Erdős #142 — supersaturation checkpoint

## Bottom line

The current Lean development proves finite supersaturation infrastructure, not the
open Erdős #142 conclusion.  The accepted modules are `ThreeAPCount`,
`WeightedCapacity`, `RobustCapacity`, `Sampling`, and `SamplingBounds`.  The
affine work is implemented in `AffineWindows` and `AffineSupersaturation`,
independently ACCEPT reviewed (all parameters valid, standard axioms),
integrated, and adopted at revision
`f13fa8aba30ecda3c2a0275738d219c5fd88d15d`; the aggregate `lake build Erdos`
passed.  No claim is made here of a new upper bound, a general `k`-theory, or
an asymptotic theorem.

The decisive negative result is that the most natural exhaustive affine-cover
route cannot improve the published finite bounds.  This is a mathematical
obstruction, not a failed optimizer run.

## What is proved (formal Lean)

- `ThreeAPCount` defines the canonical three-element AP edges and proves the
  finite deletion inequality: a set is bounded by the ambient additive Roth
  number plus its canonical 3-AP count.
- `WeightedCapacity` proves weighted local-capacity certificates, including the
  covered case with no point-defect term.
- `RobustCapacity` allows AP-containing sets by charging each AP edge through a
  bounded weighted edge load.
- `Sampling` proves the exact fixed-cardinality subset double count and the
  resulting binomial supersaturation inequality.
- `SamplingBounds` derives the finite falling-factorial and cubic consequences,
  including the BLS-style cubic sparsening bound in its stated finite range.

These are formal Lean results about finite sets.  They do not formalize the
asymptotic assertion of #142, and they do not establish a general `k`-term
analogue.

## Source and exact evidence

1. **Dybizbanski, EJC 19(2) (2012), P15** — [article and
   PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v19i2p15).
   The paper gives exact `r_3(m)` for `m <= 123`.  The exact jump data imply
   `r_3(120)=30`, `r_3(123)=32`, and
   `min_{1 <= m <= 123} r_3(m)/m = 30/120 = 1/4`.
   This is source/exact evidence, not an asymptotic estimate.
2. **Gasarch--Glenn--Kruskal, Survey II, arXiv:2501.01634v1** —
   [arXiv](https://arxiv.org/abs/2501.01634v1).  Table 3 gives published
   finite upper bounds for `187 <= N <= 250`.  In canonical v1, the high
   `H` is called an upper bound; conservatively record only `r_3(N) <= H`.
   Source reading plus the read-only comparison experiment confirms
   `H < N/4` throughout this range; only the conservative `r_3(N) <= H`
   statement is used here.
3. **Balogh--Liu--Sharifzadeh, Lemma 2.3 (source label `lem-supsat2`)** —
   [arXiv:1605.03172](https://arxiv.org/abs/1605.03172).  The citation in the
   Lean sampling files is corrected to this lemma/source label.  The Lean
   development formalizes a finite exact reparameterization of the relevant
   sampling argument; it does not claim the paper's asymptotic theorem.

## Closed affine-cover route

Take every affine interval copy
`C = {a, a+d, ..., a+(m-1)d}` in `[0,N)`, with `m <= 123`, and use the exact
Dybizbanski local cap `r_3(m)`.  For any nonnegative weighted cover, its LP
objective satisfies the exact informal inequality

```text
sum_C r_3(|C|) w_C
  >= (1/4) sum_C |C| w_C
  >= N/4.
```

The second inequality is just the point-cover constraints summed over the
points.  Consequently this entire local-capacity family cannot certify an
upper bound below `N/4`; since the published `H` is already below `N/4`,
there is no possible improvement from this family.  This conclusion holds for
all choices of affine copies and weights, not merely for the optimizer's
returned solution.

A computation solved all 64 cases `N=187,...,250` with SciPy HiGHS, in eight
Sage `timeout 60` chunks, all successful.  Those optima are floating-point
outputs, not rational certificates, and yield no novelty.  They are retained
only as corroboration of the exact obstruction; no large LP table is copied
here.  The affine implementation is independently ACCEPT reviewed, integrated,
and adopted; rerunning this same LP family is not a route forward.

## Two-window diagnostic

For `C=[0,m)` and `D=[s,s+m)` with `2 <= m <= 12` and `1 <= s < m`, define

```text
beta_m(s) = max {|A ∩ C| + |A ∩ D| : A ⊆ C ∪ D, A is 3-AP-free}.
```

Exhaustive bit-mask enumeration covers all 66 cases (union size at most 23).
There are 32 positive gaps `2*r_3(m)-beta_m(s)` and 34 zero gaps; all seven
cases with `m=8` have zero gap.  Thus a universal positive overlap gap is
false.  This does **not** rule out a gap for selected scales or a multiscale
construction.

Session artifacts used for this checkpoint (not copied into the repository)
are `/tmp/r3-affine-cover-ledger.md`, `/tmp/affine_lp_187_250.py`,
`/tmp/beta-contiguous-m12.json`, `.csv`, and
`/tmp/exact_beta_contiguous.py`.

## Status and route closure

**Established:** the five accepted finite Lean modules above; the exact
local-capacity ratio obstruction; the finite LP and two-window computations;
and the implemented modules `AffineWindows` and `AffineSupersaturation`.

The implemented affine argument has the sharp displayed form

$$
  L D\,|A| \le F\,r_3(L) + M_L T(A).
$$

It is independently ACCEPT reviewed, integrated, and adopted at revision
`f13fa8aba30ecda3c2a0275738d219c5fd88d15d`; all parameters are valid under the
standard axioms, and the aggregate `lake build Erdos` passed.  The asymptotic
#142 goal remains open; no formal or informal argument here closes it, and no
new upper bound has been obtained.

**Route status:** the all-affine `m <= 123` improvement route is stopped.  The
`1/4` obstruction is decisive for that family; the floating-point LP outputs
are not rational certificates and are not a new result.  Do not promote the
finite infrastructure or this implementation status to a general or
asymptotic claim.
