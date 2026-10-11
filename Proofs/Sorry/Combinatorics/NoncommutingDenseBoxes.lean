import Combinatorics.NoncommutingDenseWindow
import Combinatorics.NoncommutingDenseRectangle
import Combinatorics.NoncommutingDenseMaximal

set_option autoImplicit false

/-!
# Dense translated boxes: consolidated argument and formalization boundary

This is a DOCUMENTATION ARCHIVE, not a declaration of the dense-box theorem.
It introduces no definitions, theorem placeholders, axioms, or unfinished proofs.
Its three imports supply checked geometric and one-dimensional consumers only.
Production must not import this `Sorry` archive.

## Provenance and scope

The substantive sources absorbed here, both full-read during consolidation, are:

* `Plans/NoncommutingDenseBoxLinear.md` (199 lines), SHA-256
  `24f1f2aac46656b009071f8892e50a9675527b641f901cf156cbf912d94cf752`;
* `Plans/NoncommutingDenseCubeLinear.md` (155 lines), SHA-256
  `c956f31948f57def43cae97f086c26ebc59c362d23c5464c0f8303ab6eeaaa03`.

The box source identifies the adopted cube artifact as
`873072cd65205aec2b2dd318e5a2c18c2d6633aa`, with the cube source path above.
It also points to the older comparable-box plan
`00c77ea87467bed7c5c168d0bd45745431787e93`,
`Plans/NoncommutingDenseBox.md`, as historical provenance, not as an additional
premise or a substitute for the argument recorded here.
The completed imports are supplied by checked output
`c7bbb12c6d542c67c850b34b4a225f75d62a4af0`.

The sources' status sentences are historical: they describe prose proofs, not
Lean-checked full deficit theorems. The box source records adversarial boundary
checks finding no counterexample to its plateau conventions; this is not a
kernel proof. The cube source's phrase "verified dense equal-side cube class"
is a prose assessment, not a formal verification of the final bound. Producer
compilation and producer axiom checks of the imported units are not independent
source review or a full proof. Fresh imported axiom audit and independent
source review remain coordinator-owned. Neither Markdown source is retired by
this archive; all mathematics needed for their later retirement is stated below.

This route concerns translated comparable boxes, with an equal-side refinement.
It makes no arbitrary-set inverse theorem, Erdos #711 bridge, optimality, or
novelty claim. The numerical constants are deliberately crude/nonoptimal.

## Exact objects, conventions, and targets (not yet Lean theorems)

For ALL translations `r1,r2,r3 : ℤ`, ALL positive integer cardinalities
`N1,N2,N3 : ℕ` with `1 ≤ Ni`, and ALL finite `A ⊆ B`, let

```
Ii = {ri, ri+1, ..., ri+Ni-1},
B = I1 × (I2 × I3),   V = N1*N2*N3 = |B|,
h = |B \ A|,   m = min(N1,min(N2,N3)),   M = max(N1,max(N2,N3)).
```

Products of three integers are right-associated, matching `ℤ × (ℤ × ℤ)`.
Lengths mean cardinalities, not endpoint differences; a singleton has length
one. Endpoints `ri + Ni - 1` are integer arithmetic after casting `Ni`.
Assume a real `κ` with `1 ≤ κ` and `(M : ℝ) ≤ κ*(m : ℝ)`.
All cardinalities in the real inequalities below are cast to `ℝ`; subtraction
in those inequalities is real subtraction, never truncated natural subtraction.

```
L0(x,y,z) = (y,-x,0),
L1(x,y,z) = (z,0,-x),
L2(x,y,z) = (0,z,-y),
M(A) = L0(A) + L1(A) + L2(A),
D = |M(B) \ M(A)|.
```

Here images are distinct-support finite images, and `+` is coordinatewise
pointwise finite-set addition, not a multiset sum. This agrees with the existing
`NoncommutingFiber.L0`, `L1`, `L2`, and `mixedSum` definitions in
`Proofs/Combinatorics/NoncommutingFiber.lean`; those definitions are source
pointers, not imported bridges in this archive. We use `M(A)` only as prose
notation and do not redefine `mixedSum`.

The main comparable-box target is

```
D ≤ 7776*κ^5*h.
```

The refined two-dimensional halo argument would give the stronger target

```
D ≤ (7776*κ^5 - 1296*κ^3)*h.
```

For ALL translations with `N1=N2=N3=N ≥ 1`, the equal-cube deficit target is
`D ≤ 6480*h`. The cube source also targets

```
|M(A)| ≥ 8*|A| - 6480*(h + N^2).
```

No density lower bound on `A` is assumed: `h` measures its missing mass.

## Projection holes and the absent-fiber bound

Use the actual two-coordinate projection grids

```
G0 = I2 × (-I1),   G1 = I3 × (-I1),   G2 = I3 × (-I2),
```

where `-I` is the image under negation. Define `Hi` as the pairs in `Gi`
not attained by the corresponding two nonzero coordinates of `Li(A)`.
Equivalently, a pair is a hole exactly when its entire remaining-coordinate
fiber in `B` is absent from `A`. For `H0` this fiber has `N3` points; for
`H1` it has `N2`; for `H2` it has `N1`. Fibers for distinct pairs within
one projection are disjoint. The intended weighted conclusions are

```
N3*|H0| ≤ h,   N2*|H1| ≤ h,   N1*|H2| ≤ h,
|H0| ≤ h/N3,  |H1| ≤ h/N2,  |H2| ≤ h/N1,
|Hi| ≤ h/m.
```

All divisors are positive. In a cube, `|Hi| ≤ h/N`.
A proof must identify these exact projection complements and count disjoint
absent fibers inside `B \ A`; it cannot treat hole sizes as supplied premises.

## Missing-output covering and rectangle density

For each `s=(s1,s2,s3) ∈ M(B) \ M(A)`, write a summand choice as

```
(a,b,0) + (c,0,d) + (0,e,f),
c=s1-a,   e=s2-b,   f=s3-d.
```

The free variables `(a,b,d)` range independently over the nonempty common fiber

```
J1 = I2 ∩ (s1-I3),
J2 = (-I1) ∩ (s2-I3),
J3 = (-I1) ∩ (s3+I2).
```

For example, `s-I` means `{s-t : t∈I}`, and `s+I` means `{s+t : t∈I}`.
Nonemptiness here follows from `s∈M(B)`; averages are taken only on nonempty
fibers and rectangles. The projected pairs associated with a triple are

```
P0=(a,b),   P1=(c,d)=(s1-a,d),   P2=(e,f)=(s2-b,s3-d).
```

Every triple in `J1 × J2 × J3` has at least one of `P0∈H0`, `P1∈H1`,
`P2∈H2`. Otherwise the three non-hole pairs have independent completions in
`A`, yielding three summands whose sum is `s`, contradicting `s∉M(A)`.
This uses independent choices of summands, NOT independence of hole sets.

Averaging the three covering indicators makes their density sum at least one,
so one of the following actual projection-coordinate rectangles has hole
density at least `1/3`:

```
R0 = J1 × J2                                  in G0,
R1 = [I3 ∩ (s1-I2)] × [(-I1) ∩ (s3+I2)]       in G1,
R2 = [I3 ∩ (s2+I1)] × [(-I2) ∩ (s3+I1)]       in G2.
```

The maps `(a,d) ↦ (s1-a,d)` and `(b,d) ↦ (s2-b,s3-d)` are bijections
onto `R1` and `R2`, respectively. Thus these are precisely the densities of
`H1` and `H2`, not densities obtained by incorrectly reusing common-variable
coordinates. Translations/reflections preserve counts and reverse endpoint
orientation when appropriate. Formalizing these affine identifications and
the covering-to-density averaging remains necessary.

## Unequal-side marked windows and the zero-extension convention

Normalize a fixed interval pair to `[0,u-1]` and `[0,v-1]`, with integer
cardinalities `1 ≤ u`, `1 ≤ v`. For `0 ≤ t ≤ u+v-2`, put

```
Jt = [0,u-1] ∩ [t-v+1,t],   l=max(0,t-v+1).
```

The source construction retains or enlarges `Jt` and chooses a mark `q`:

* If `t ≤ u-1`, retain `Jt` and mark its right endpoint `q=t`.
* If `u-1 < t` and `0 < l`, retain `Jt` and mark its left endpoint `q=l`.
* If `u-1 < t` and `l=0`, then `u ≤ t ≤ v-1` and `v>u`.
  Replace `Jt=[0,u-1]` by `[0,t]` and mark `q=t`.

Every window lies in the FIXED expanded grid `[0,max(u,v)-1]` and contains
both its original overlap and its mark. Only the plateau enlarges the interval:

```
|[0,t]|/|Jt| = (t+1)/u ≤ v/u ≤ κ;
```

the other branches have ratio one. Side comparability supplies `v ≤ κ*u`.
The side pair `(u,v)` must stay fixed while source preimages are counted.
A mark has at most two source values: `t=q` or `t=q+v-1`. The prefix and
plateau both use `q=t` but are disjoint source branches, so there is no third
preimage. The multiplicity is at most two per coordinate and four per pair.
Translations/reflections preserve this assertion; no extra reflection factor
is charged. When `u=1` enlargement costs at most `v≤κ`; when `v=1` there
is no enlargement; when `u=v` there is no plateau enlargement.

Applying the construction to each coordinate of a dense `Ri` enlarges its
area by at most `κ^2`, giving hole density at least

```
α = 1/(3*κ^2),   0 < α ≤ 1.
```

ONLY WINDOWS are enlarged. The hole set stays exactly the same finite set:
its indicator is extended by zero off the original projection grid. No new
holes are created, no hole neighborhood is substituted, and the expanded grid
is fixed for each interval pair. This convention is needed both for the mass
bound and for applying the halo lemma.

In a cube, overlaps have lengths `1,2,...,N-1,N,N-1,...,2,1`: proper prefixes,
the full interval once, then proper suffixes. Mark the right endpoint on
prefixes and the full interval, and the left endpoint on suffixes. The mark
lies in the original rectangle; no enlargement is needed. The same statement
holds for sums or differences and reflected intervals.

## Checked interfaces actually available from the three imports

All following names are in namespace `NoncommutingDense`.

* `overlap u v t`, `overlapMark u v t`, and `overlapWindow u v t` implement
  the normalized construction. In particular the suffix test is
  `u ≤ t ∧ v ≤ t`; the enlargement test is `u ≤ t ∧ t < v`.
* `overlap_nonempty` takes `1≤u`, `1≤v`, `0≤t`, `t≤u+v-2`.
  `overlapWindow_geometry` takes the same guards and proves original-overlap
  containment, mark membership, and fixed-expanded-grid containment.
  `overlap_card_of_plateau` gives `card(overlap)=u.toNat` under
  `1≤u`, `u≤t`, `t<v`.
* `overlapWindow_card_le` adds real `1≤κ` and `(v:ℝ)≤κ*(u:ℝ)` and gives
  `card(window)≤κ*card(overlap)` in real arithmetic.
  `overlapMark_sources` gives the two source alternatives;
  `card_overlapMark_fiber_le_two` bounds the fiber in ANY finite source set.
  `overlapWindow_eq_overlap_of_eq_sides` proves no equal-side enlargement.
* `rectangle_density_transport E I J U V κ` takes `1≤κ`, `I⊆U`, `J⊆V`,
  `card(U)≤κ*card(I)`, `card(V)≤κ*card(J)`, and
  `card(I×J)≤3*card(E∩(I×J))`, and concludes
  `card(U×V)≤3*κ^2*card(E∩(U×V))`, with real casts. The SAME `E` occurs
  on both sides. Its denominator-free statement allows empty rectangles;
  nonemptiness must not be inferred from this theorem alone.
* `overlapRectangle_certificate` combines the preceding result with both
  guarded normalized overlaps and their side-ratio hypotheses. It certifies
  window-product nonemptiness, mark-pair membership, fixed-grid containment,
  and the transported density. `card_overlapMark_pair_fiber_le_four` bounds
  two-coordinate mark fibers for fixed side pairs in any finite source set.
* `endpointInterval (a,b)=Icc a b` and
  `tripleInterval (a,b)=Icc (2*a-b) (2*b-a)` implement greedy enlargement.
  `endpointInterval_subset_tripleInterval` takes ordered endpoints for both
  intervals, a cardinality comparison, and nondisjointness.
  `card_tripleInterval_le` takes ordered endpoints and gives the factor three.
  `exists_disjoint_interval_cover` takes a finite endpoint family `S` with
  `∀p∈S, p.1≤p.2`, and PRODUCES `T⊆S`, pairwise disjoint original intervals,
  and `∀p∈S, ∃q∈T, endpointInterval p⊆tripleInterval q`. Selection is proved
  by finite strong induction, not accepted as an assumption.
* `intervalMaximalHalo X f τ` is
  `{x∈X : ∃a∈X, ∃b∈X, a≤b ∧ x∈Icc a b ∧
  τ*card(Icc a b)≤∑y∈Icc a b,f y}`.
  The checked consumer `intervalMaximalHalo_weak_bound` has precisely
  integer endpoints `a0≤b0`, `f:ℤ→ℝ` nonnegative on `Icc a0 b0`, and
  real `0<τ`, and concludes
  `τ*card(intervalMaximalHalo (Icc a0 b0) f τ)≤3*∑x∈Icc a0 b0,f x`.
  It proves the division-free form of `|{Mf≥τ}|≤(3/τ)∑f`.

The geometric imports have concrete singleton and unequal-plateau checks;
the maximal import checks singleton mass, zero-function mass, and empty halos.
Reported producer axiom dependencies lie in `{propext, Classical.choice,
Quot.sound}`. This archive does not run or independently certify that audit.
None of these interfaces yet identifies translated projection rectangles or
attributes missing `mixedSum` outputs. Those are semantic bridges, not extra
assumptions secretly discharged by the imported normalized geometry.

## Fixed-threshold two-dimensional halo (prose, not yet formalized)

For finite nonempty integer intervals `X,Y`, `E⊆X×Y`, and `0<α≤1`, define
`Halo_α(E)` to be the grid points contained in a nonempty integer rectangle
`I×J⊆X×Y` with `|E∩(I×J)|≥α*|I×J|`.
The coarse box-source estimate is

```
|Halo_α(E)| ≤ 36*α^(-2)*|E|.
```

The refined two-stage argument gives

```
|Halo_α(E)| ≤ [18*(2-α)/α^2]*|E|.
```

The one-dimensional argument in both sources is now paid by the imported
consumer: choose a witnessing interval for each level-set point and greedily
retain intervals in nonincreasing order of cardinality. The retained intervals
are disjoint. Every discarded interval intersects a retained one at least as
long and lies in its threefold enlargement, so coverage has cardinality at
most three times the sum of retained lengths. Each retained witness has mass
at least its length times the positive threshold; disjointness and nonnegative
mass bound the sum of these masses by the total mass on the ambient interval.
This gives the factor `3/τ`. The checked implementation instead selects a
maximum-cardinality interval recursively on a finite endpoint family, which
establishes exactly this certificate without assuming a greedy ordering.

Here is the complete intended two-dimensional argument. For each fixed `x`,
let `g(x,y)`
be the finite uncentered maximal average in the y-coordinate of `1_E`.
Singleton witnessing intervals exist, maxima are over finite nonempty families,
and `0≤g≤1`. Put `F={g>α/2}`. On a dense rectangle through `(x,y)`,
the x-average of `g(·,y)` is at least `α`: each point of its x-interval
may use the same y-interval as witness. If `p` is the fraction of that
x-interval in the row-section of `F`, then

```
α ≤ avg_x g ≤ p + (1-p)*α/2,
p ≥ α/(2-α) ≥ α/2.
```

Apply the checked 1D estimate columnwise at threshold `α/2` to bound the
STRICT level set `F` (a subset of the non-strict level set):
`|F|≤6*|E|/α`. Apply it rowwise to `1_F` at threshold `α/(2-α)`:

```
|Halo_α(E)| ≤ [3*(2-α)/α]*|F|
            ≤ [18*(2-α)/α^2]*|E|
            ≤ 36*|E|/α^2.
```

The cube source specializes `α=1/3`, using `F={g>1/6}` and `p≥1/5`:
`|F|≤18*|E|`, `|Halo_(1/3)(E)|≤15*|F|≤270*|E|`.
The coarse specialization instead gives 324, so 270 is essential to the
cube's 6480 constant. For the comparable-box threshold `α=1/(3κ^2)`,
the coarse constant is `324κ^4` and the refined constant is
`324κ^4-54κ^2`. This latter specialization records the finer derivation;
it is conditional on the same still-unformalized halo argument.

Witnessing rectangles are contained in the finite grid. Greedy enlargements
used to upper-bound one-dimensional coverage may extend beyond it; this causes
no added mass. The 2D argument uses zero-supported holes on the fixed expanded
grids. It does NOT assert a threshold-uniform strong weak-(1,1) estimate: the
fixed-threshold/indicator argument and its `α^(-2)` loss are indispensable.

## Output attribution, unused coordinates, and final constants (prose)

Attribute each missing output to one of the dense `R0,R1,R2` alternatives;
a union bound suffices, so no disjointness of alternatives is assumed.
The relevant output pairs are `(s1,s2)`, `(s1,s3)`, `(s2,s3)`, respectively.
Their normalized marked pairs lie in the corresponding halos and have at
most FOUR source pairs each. The unused output coordinate ranges have sizes

```
for H0: s3 in (-I1)+(-I2), length N1+N2-1;
for H1: s2 in (-I1)+I3,    length N1+N3-1;
for H2: s1 in I2+I3,       length N2+N3-1.
```

Each is at most `2M-1≤2M`. There is no additional reflection multiplicity.
If `Cκ` is a valid halo constant after enlargement, the weighted intended
count is

```
D ≤ 4*Cκ*((N1+N2-1)*|H0| + (N1+N3-1)*|H1| + (N2+N3-1)*|H2|)
  ≤ 4*Cκ*h*((N1+N2-1)/N3 + (N1+N3-1)/N2 + (N2+N3-1)/N1).
```

In particular the coarse box route gives

```
D ≤ 3*4*(2M)*(324κ^4)*(h/m) ≤ 7776κ^5*h.
```

Keeping the refined halo term instead gives

```
D ≤ 3*4*(2M)*(324κ^4-54κ^2)*(h/m)
  ≤ (7776κ^5-1296κ^3)*h.
```

For `κ≥1` the halo coefficient is nonnegative, so comparability is used
with the correct inequality direction. At `κ=1` the refined coefficient is
6480. Independently, the cube argument keeps its unused-coordinate length:

```
number of output pairs attributed to Hi ≤ 4*270*|Hi| = 1080*|Hi|,
D ≤ 1080*(2N-1)*(|H0|+|H1|+|H2|)
  ≤ 3240*(2N-1)*h/N ≤ 6480*h.
```

Establishing these actual output-pair maps and counting their fibers is still
required: a normalized four-preimage bound alone is not mixed-sum attribution.

## Exact ambient box and optional cardinality consequences (prose)

Independent coordinates of the three independently chosen summands give

```
M(B) = (I2+I3) × ((-I1+I3) × (-I1-I2)),
|M(B)| = (N2+N3-1)*(N1+N3-1)*(N1+N2-1).
```

Here `-I1-I2` denotes `(-I1)+(-I2)`.
For positive sides this is at least `8V-12M^2`. One expands the three
sum-minus-one factors, uses
`(N2+N3)*(N1+N3)*(N1+N2)≥8V`, bounds the sum of the three products
of two pairwise sums by `12M^2`, and drops the nonnegative remaining
linear-minus-one term. Under the SAME positive-side comparability hypotheses,
`Ni≤M≤κ*V^(1/3)`, so

```
|M(B)| ≥ 8V-12M^2 ≥ 8V-12κ^2*V^(2/3).
```

Fractional powers here mean real powers of the positive real volume `V`, not
natural-number exponentiation. The ambient formula needs positive intervals;
the `κ`-bound additionally needs comparability. With `A⊆B`, monotonicity
`M(A)⊆M(B)`, `|A|=V-h`, and the COARSE deficit target, one obtains

```
|M(A)| ≥ 8V-12κ^2*V^(2/3)-7776κ^5*h
       ≥ 8*|A|-(7776κ^5+12κ^2)*(h+V^(2/3)).
```

The first line is the sharper quantitative version recorded in the box source.
This optional ambient consequence is not a prerequisite for the deficit route.
In a cube the exact formula and the deficit estimate give

```
|M(B)| = (2N-1)^3 = 8N^3-12N^2+6N-1,
|M(A)| ≥ 8N^3-12N^2+6N-1-6480*h.
```

Compare with `8*|A|=8*(N^3-h)`. For `N≥1`, the term `6N-1` is favorable;
dropping it and relaxing the error yields the cube source's
`|M(A)|≥8*|A|-6480*(h+N^2)`.

## Boundaries and exact unpaid implications

* If `h=0`, `A=B`, all hole sets and the deficit vanish. The cube's exact
  full-box value remains `(2N-1)^3`.
* If `A=∅`, then `h=V`; the deficit bounds are harmless and the optional
  lower bounds are vacuous. No unmentioned density assumption is needed.
* Singleton sides have cardinality one, not zero. For `N=1` the cube overlap
  is the unique full interval, with mark multiplicity one. All denominators
  above remain positive. The unequal plateau repair covers `u=1`, `v=1`,
  and `u=v` as described, including translated/reflected zero-supported holes.
* Translations and sign reflections preserve cardinalities and only change
  the orientation of endpoint marks; their actual projection identification
  must still be formalized.

The exact remaining mathematical implications, not stale coordination tasks,
are:

1. **2D maximal halo:** construct the finite maxima/indicator sections and
   derive the coarse and refined bounds from the checked 1D consumer, including
   strict-to-nonstrict threshold handling and summation over rows/columns.
2. **Translated/reflected projection identification:** connect the actual
   `R0,R1,R2`, grids, and affine pair maps to the normalized overlap/window
   interfaces, preserving support, density, and mark multiplicity.
3. **Absent-fiber counts:** define the actual projection holes from `A⊆B`
   and prove the three weighted bounds using disjoint fibers of positive size.
4. **Covering density:** turn a missing mixed-sum output into the nonempty
   common fiber, prove the three indicators cover it, and obtain one actual
   projection rectangle of density at least one third via the bijections.
5. **Mixed-sum attribution/counting and final constants:** combine the halo
   marks with actual output-pair fibers, the correct unused coordinate ranges,
   and the union over the three alternatives to establish the weighted count
   and the 7776 / refined / 6480 deficit conclusions. The optional ambient
   formula, monotonicity, and cardinality lower bounds also need their own
   bridges if that corollary is requested.

No genuinely ambiguous mathematical claim was found in the two full-read notes
under these conventions. Their historical status language is not treated as
proof evidence; the refined general constant is explicitly a conditional
extension of their stated two-stage argument, not a checked new theorem.
The current checked imports pay the normalized window/density and 1D greedy
obligations only. This archive preserves the rest without claiming completion.
-/
