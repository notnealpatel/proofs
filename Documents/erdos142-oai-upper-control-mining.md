# Erdős 142: three-Luna source-mining synthesis

## Status and scope

This note records the completed three-Luna, read-only source inspection. It is
synthesis rather than new research, and makes no novelty or closure claim. The
three `litreader` scopes were **Estimates/reflection/energy**,
**Fourier/Linear/Lattices**, and **Results/FixedDensity/Geometry/Sampling**. The
canonical source prefix for all records is
`/home/exedev/x/math/lean/OAI/Combinatorics/Progressions/`. All external results
below were SOURCE-INSPECTED, not newly compiled or axiom-audited. The inspected
external toolchain is Lean 4.34.1, whereas the local toolchain is 4.33.0-rc1; no
compatibility failure is claimed. No inspected result supplies the new upper
gain; porting these adapters alone would not advance (O).

The accepted bridge at revision `4cbaa76aef42e1bb2e462495155b4c7048ac977f`
already proves, for arbitrary finite $A$ and $N>0$, $E=\sum_{z,k}K_{zk}$ and
$E\le 3N\max K$. The existing scalar-free upper bound is $2E\le (m+\lfloor
m/2\rfloor)M$. The open target remains

$$E N^{2/3}(m-N)^2\le M^2 r_3(N)^{8/3}$$

for scalar-free $A\subset[0,N^2)$ with $m>N$. The route “O → shadow C → square
gain” is a mathematical route, not a theorem discovered by mining. The square
gain $P$ is intermediate and is not an asymptotic closure of Erdős 142.

## Source findings

`Estimates/FiniteGraphEnergy.lean:86ff`
(`graph_energy_of_few_quadruple_differences`) directly imports Mathlib. Its
exact setup is finite additive commutative `G,K` with decidable equality,
$H\subset G$, $S\subset G^3$, $b:G\to K$, and $D\subset K$. For graph points
$t=(h,x,y)\in S$, it assumes $x,x-h,y,y-h\in H$ and $b(x-h)+b(y)-b(x)-b(y-h)\in
D$, concluding $|S|\le
|D|\,\operatorname{addEnergy}(\operatorname{graph}(b|_H),\operatorname{graph}(b|_H))$.
This is generic bookkeeping, with no AP hypothesis; $G=\mathbb Z$ is not
permitted by the finite-group hypotheses. The actual identity $2(a-a')=b-b'$
does not furnish the required AP-sensitive energy bound. No faithful better map
was established.

`Fourier/NativeMixedFourierProfiles.lean:85ff` directly imports
`Estimates.NativeMixedCubeResiduals`; `exists_fourier_of_twisted_unit_shift`
assumes nonzero $N$, $q,f:\mathbb Z/N\mathbb Z\to\mathbb C$ unit-bounded,
$|\zeta|=1$, average twisted shift error, explicitly $\mathbb E_n|q(n+1)-\zeta
q(n)|\le2/N$, **and $0<\rho\le1$**, plus correlation $|\mathbb E_n
f(n)\overline{q(n)}|\ge\rho$, concluding an additive-character coefficient of
$f$ at least $\rho^2/16$. A real linear phase has the shift bound except at one
wrap point, but scalar AP-freeness supplies neither the required positive
correlation nor new mixed-fiber phase structure. There is no fixed-denominator
consequence, so RAI(K) remains refuted. Fiber indicators are unit-bounded;
dividing by fiber density generally breaks that hypothesis. This is a generic
inverse adapter, not a collision upper bound.

`Fourier/FiniteFourierSmoothing.lean:32ff,77ff` supplies inversion and Parseval
bookkeeping only; it does not give cubic unequal-fiber control.

`FixedDensity/OrderedRemoval.lean:32ff` directly imports
`Mathlib.Data.Finset.Max`, `Mathlib.Order.Hom.PowersetCard`,
`FixedDensity.BooleanCutReduction`, and `FixedDensity.OrderedPattern`. Its
`weightedAPCount_of_denseAPCount` assumes nonzero $Q$, $\delta\ge0$,
`HasDenseAPCount k Q (δ/2) c`, $0\le g\le1$, and mean $g\ge\delta$, concluding
$\operatorname{cyclicAPCount}(k,Q,g)\ge(\delta/2)^k c$. Here `HasDenseAPCount`
means every $B$ of density at least $\delta/2$ has cyclic count at least $c$.
The definition of `cyclicAPCount` is in `FixedDensity/Energy.lean:105ff`; it is
the all-pairs mean. The theorem propagates an assumed dense AP count $c$; it
does not produce a quantitative $c(\delta,Q)$. Its count averages all $(a,d)$,
including diagonal degeneracies: for $k=3$, $d=0$ contributes $Q^{-2}\sum_a
g(a)^3$, and for even $Q$, $d=Q/2$ contributes $Q^{-2}\sum_a g(a)^2g(a+Q/2)$.
Any scalar contradiction must exceed these terms and adapter exceptions and
prove transport back to $A$. Positive $c$ alone is insufficient; the naive
reflection-target transport is false.

The conditional structural lead is
`FixedDensity/CoarseOrderedRemoval.lean:267ff`, directly importing
`Mathlib.Algebra.Order.Chebyshev`, `FixedDensity.BundleCountingRecurrence`, and
`FixedDensity.CoarseAtomBridge`. For finite nonempty $G$ with decidable
equality, unit-interval edge weights $H$, and a fine refinement of a coarse
model, `regularizedOrderedPattern_count_sub_sq_le_totalEnergyGap` gives
$|\operatorname{count}_{fine}-\operatorname{count}_{coarse}|^2\le
\operatorname{card}(\operatorname{OrderedFace}\ k\
r)\,(\operatorname{energy}_{fine}-\operatorname{energy}_{coarse})$. It offers
stability only if a faithful scalar/carry model of bounded enough complexity is
first constructed. No such carry refinement, AP-sensitive coarse upper estimate,
or useful quantitative rate was found; there is no rank-one inference. Exact
count identification, diagonal separation, error budgeting, and complexity
losses would all precede any port.

Lower-priority negative findings likewise do not prove O: generic local
correlation smoothing, uncontrolled weighted-overlap derivatives,
translation-sensitive reciprocal results, and weighted Fourier counting that
assumes unavailable niltest comparison or odd modulus.

## Finite check and disposition

A completed Sage computation (domain `A={1,2,4,8}`, `N=3`) gives a scalar
AP-free set whose shadow has `S={0,3,6,7}`, with shadow AP `(0,3,6)`, `M=6`, and
`E=12`. The in-range nontrivial representations by center are
`c0:(1,2),(2,4),(4,8)`, `c3:(2,1)`, `c6:(4,2)`, and `c7:(4,1)`. This is finite
verified computation plus elementary enumeration, not a Lean theorem: shadow APs
do not imply APs in `A`, though this does not refute O or C. Ordered collision
diagonals are included.

Conclusion: no ready-made theorem closes O or improves the existing bound. Do
not present generic adapters as mathematical progress. The best gated next
investigation is whether mixed scalar/carry exclusion controls a faithful coarse
collision model at affordable quantitative complexity. Tests must retain uneven
fibers, in-range targets, Cartesian subproducts, affine-flat thinning
counterfamilies, and all carries.
