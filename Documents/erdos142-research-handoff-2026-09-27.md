# Erdős 142 research handoff — 2026-09-27

## Status, scope, and evidence

This handoff records the frontier at accepted revision
`596825af4c347bbb311da8a340bec333c45b2f9a`. Scope is **only the three-term
case, k=3**. Use
$$
r(N)=\max\{|A|:A\subseteq[1,N]\text{ has no nontrivial 3-AP}\},\qquad
\lambda(N)=\log\frac{N}{r(N)},\qquad
D(N)=\frac{\lambda(N)}{\sqrt{\log N}},
$$
with natural logarithms, and fix
$$
X(N)=\lambda(N^2)-2\lambda(N)
    =\log\frac{r(N)^2}{r(N^2)}.
$$
The canonical Erdős problem 142 still asks for an asymptotic formula for the
progression-free extremal function. It remains unsolved here; none of the
results below is a proof or disproof of the problem.

**Evidence labels.** “Kernel checked” means a sorry-free Lean result with the
stated axiom audit. “Accepted prose” means a reviewed mathematical deduction,
not a Lean theorem. Raghavan's result is an external theorem/preprint input.
Exploratory computations and conjectures are not proofs. In particular,
reviewed prose and external inputs must not be described as Lean theorems.
At this accepted revision the formal modules named below are sorry-free; their
stated public endpoints use only `[propext, Classical.choice, Quot.sound]`.

## Accepted kernel-checked frontier

- **Square-scale negative-defect density.**
  `Proofs/Erdos/Erdos142/SquareScaleNegativeDensity.lean` proves, for fixed
  `M ≥ 3`, `N_j=M^(2^j)`, and each `0<β<2−√2`, the lower-density curve
  $$
  \delta_\beta=1-\frac{\log\sqrt2}{\log(2-\beta)}
  $$
  for indices with `X(N_j) ≤ −β λ(N_j)`. Its strict-negative corollary gives
  tower-index lower density at least `1/2`: for every `δ<1/2`, eventually at
  least `δK` indices `j<K` have `X(N_j)<0`. This is not an exact density or
  bounded-gap result; no overlap with positive-density P-shaped good scales is
  established. It gives neither `D(N)→0` nor a full asymptotic formula. The
  endpoint does not assert the cardinality bound at
  `δ=1/2`.
- **Finite carry-cardinality obstruction.**
  `Proofs/Erdos/Erdos142/CarryCardinalityCapObstruction.lean` proves that the
  relaxation imposing ordinary 3-AP-freeness on row and column fibers and a
  common in-range fiber cap `2b≤N` permits a bounded relation of size at least
  `N r(N)/2`. Its scalar base-`N` image contains a nontrivial 3-AP. This closes
  only that relaxation as a way to prove a universal `o(Nr(N))` upper bound;
  it is deliberately **not scalar-free** and is not an obstruction theorem
  for the scalar-free problem itself.
- **Reflection shadow.** `Proofs/Erdos/Erdos142/ReflectionShadow.lean` proves
  that an ordinary 3-AP-free finite `A⊂ℤ` is disjoint from its nontrivial
  reflection shadow, and, for every `d≠0`,
  `2*|differenceSources(A,d)|≤|A|`. This is a finite-set lemma, not an
  asymptotic estimate for `r(N)`. Carry-union, median-shadow, and
  representation-mass/energy statements used below are reviewed informal
  mathematics, not formal results of this module.

## External and accepted-prose context

**External theorem.** Raghavan, *Improved Bounds for 3-Progressions*,
[arXiv:2603.27045v3](https://arxiv.org/abs/2603.27045v3), Theorem 1.4, gives
for all sufficiently large `N`
$$
\lambda(N)\ge c_R\left(\frac{\log N}{\log\log N}\right)^{1/6}
$$
for an absolute `c_R>0`, as recorded in the accepted note. This is an external
preprint input, not formalized here. The negative-defect density theorem does
not use Raghavan; combining it with this bound for an explicit growing
negative-defect magnitude is accepted prose, not a Lean theorem.

## Live conjectural route: positional collisions

Let `A⊂[0,N²)` be scalar 3-AP-free, let `m=|A|>N`, and let
$$
S=\{2a-b:a,b\in A,\ a\ne b\}\cap[0,N^2)
$$
be its in-range nontrivial reflection shadow. The exact live candidate is
$$
\boxed{|S|^3 r(N)^8\ \ge\ N^2(m-N)^6.}\tag{C}
$$
It is **unproved**. Together with the informal shadow/mass bookkeeping, it
would imply
$$
r(N^2)\le N+N^{2/3}r(N)^{4/3}
       \le 2N^{2/3}r(N)^{4/3}
$$
eventually, using the usual eventual Behrend lower bound to absorb `N`.
This is a P-shaped intermediate gain with `η=1/3`, not a full asymptotic
formula and not a solution of Erdős 142.

A sufficient but also **unproved and undisproved** second-moment estimate is
$$
\boxed{E\le\frac{M^2 r(N)^{8/3}}{N^{2/3}(m-N)^2}.}\tag{O}
$$
Here the ordered in-range target multiplicity, total mass, energy, and
integer-difference count are
$$
\nu(c)=\#\{(a,b)\in A^2:a\ne b,\ 2a-b=c\}\quad(0\le c<N^2),
\qquad
M=\sum_{0\le c<N^2}\nu(c),\qquad
E=\sum_{0\le c<N^2}\nu(c)^2,
$$
$$
r_A(d)=\#\{x\in A:x+d\in A\}\quad(d\in\mathbb Z).
$$
Cauchy would turn (O) into (C) using the informal carry/shadow mass
bookkeeping. Neither estimate nor that overall derivation is Lean-checked.

## Obstructions and adversarial checks

Fixed-difference edges form matchings, but fixed-target multiplicities do
not: `{1,2,4,8}⊂[9]` is scalar-3-AP-free and has `ν(0)=3`. Any attempt at
positional collision control must stress-test graph unions, unequal and
translated fibers, all three base-`N` carries `−1,0,1`, short-digit Cartesian
products, sparse sizes `m` just above `N`, and the boundary case `N=3`.
These are required adversarial checks, not assertions that (C) has been
refuted. Scalar proxy sequences do not settle claims about actual Roth
numbers or scalar-3-AP-free sets.

## Closed routes and limits of the closures

- The proposed `η=1/2` coverage inequality
  `r(N²)≤N+√N r(N)^(3/2)` is rigorously impossible asymptotically: after the
  additive term is absorbed it implies an eventual `η=1/2` square gain,
  contradicted by the accepted negative square-defect theorem. This closes
  that inequality, not broader coverage approaches.
- Row/column ordinary freeness plus fiber-cardinality caps alone cannot prove
  a universal `o(Nr(N))` bound, by the finite carry-cardinality example
  above. This does not rule out stronger positional information.
- The previously proposed high-mass entropy inequality is refuted by its
  accepted counterexample. Size/energy summaries and the one-scale LP are
  insufficient in their recorded forms. These closures are scoped to those
  arguments; they imply no broader impossibility.

## Novelty-evaluation filings

These repository issues request **external evaluation**; they are not
novelty certifications:

- [#57](https://github.com/thatnealpatel/proofs/issues/57): negative
  square-defect density, including the half-density follow-up.
- [#58](https://github.com/thatnealpatel/proofs/issues/58): carry-cardinality
  obstruction.
- [#59](https://github.com/thatnealpatel/proofs/issues/59): reflection-shadow
  route and cubic candidate.

Neighboring evaluation issues #50–#56 exist for related work; consult them
collectively rather than relying on stale formulations. Make no global
novelty claim from any filing.

## Recommended next action and verification

Either prove (C)/(O) with genuinely positional collision control, or find an
actual scalar-3-AP-free counterexample family. Do not revive the ruled-out
`η=1/2` inequality or discard carries. Before advertising any new potential
novelty claim, open its own repository issue or make an explicit scoped update
to the matching existing issue.

Focused build commands for the three modules, followed by the umbrella build,
are:

```sh
lake build Erdos.Erdos142.SquareScaleNegativeDensity
lake build Erdos.Erdos142.CarryCardinalityCapObstruction
lake build Erdos.Erdos142.ReflectionShadow
lake build Erdos
```

Accepted build records (not new build claims in this handoff): the focused and
full ReflectionShadow build succeeded, with full build count 8814; the carry
full build succeeded with count 8813; density focused and full builds are
recorded as successful.
