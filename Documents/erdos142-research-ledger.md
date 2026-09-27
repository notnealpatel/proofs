# Erdős 142 research ledger

This is the long-lived ledger for the automated research campaign begun on
2026-09-26.  It records the current posture, evidence level, live leads, and
closed routes.  It is not a proof of an asymptotic formula.

## Evidence levels

Entries use the following labels.

- **Kernel checked:** a sorry-free Lean artifact compiled in the stated
  revision, with an explicit axiom audit.
- **Accepted prose deduction:** a reviewed mathematical argument in the
  accepted repository, but not a kernel-checked theorem.
- **External theorem:** a claim read from a pinned primary source; it is not
  thereby formalized in Lean.
- **Exploratory or conditional:** a computation, conjecture, model, or
  implication with an unproved premise.

Finite computation is evidence only.  A scalar comparison function is not a
model realized by progression-free sets.  A failed route does not disprove the
square-scale target.

## Problem and fixed conventions

For three-term progressions,

$$
r(N)=\max\{|A|:A\subseteq[1,N]\text{ has no nontrivial 3-AP}\},
\qquad
\lambda(N)=\log\frac{N}{r(N)},
$$

$$
D(N)=\frac{\lambda(N)}{\sqrt{\log N}},
\qquad
X(N)=\lambda(N^2)-2\lambda(N)
    =\log\frac{r(N)^2}{r(N^2)}.
$$

The signs in these definitions are fixed.  The principal repository-specific
route target is an eventual inequality

$$
r(N^2)\le C r(N)^{1+\eta}N^{1-\eta},
\qquad 0<\eta\le\sqrt2-1.
$$

The cleaner asymptotic target is

$$
X(N)=o(\sqrt{\log N}),
$$

which is equivalent in the accepted development to $D(N)\to0$.  Neither is
known.  The canonical Erdős problem asks for an asymptotic formula, so even
this limit would be only progress toward the problem.

## Accepted starting frontier

The campaign started from accepted revision
`d923d18ffb4f0bbd066adcbbbedf39d14cfccd2d`, an adopted descendant of the
handoff revision `71ea6ec436ecff75aa10d431635086a8f7ca3195`.

- **Kernel checked:** the repository proves an explicit finite Roth theorem,
  the torus lower construction and its $\lambda(N)=O(\sqrt{\log N})$
  consequence, scale regularity below the critical dilation, the square-scale
  criterion, and the finite critical-contraction transfer.
- **Accepted prose deduction:** critical-contraction regularity transfers the
  best current square gains to a positive log-log weighted density of scales,
  but not to all sufficiently large scales.
- **External theorem:** Raghavan, arXiv:2603.27045v3, Theorem 1.4, gives
  $\lambda(N)\gg(\log N/\log\log N)^{1/6}$ for all sufficiently large $N$.
- **Accepted obstruction:** the lacunary scalar comparison function satisfies
  the currently used scalar constraints while defeating every fixed positive
  gain.  Additive structure is indispensable.

The canonical problem statement was also checked with the local `erdos`
corpus: problem 142 asks for an asymptotic formula for $r_k(N)$ and remains far
out of reach even for $k=3$.

## Recovery lane

### Square-scale negative theorem

**Kernel checked.**  The reviewed theorem was adopted in revision
`4a7e259353bfbbefa05531207582c88609bafd5c`.  The integration candidate
compiled both the exact module and `Proofs/Erdos.lean`; the principal endpoints
use exactly the permitted axioms `propext`, `Classical.choice`, and
`Quot.sound`.  A vacuity review required and then certified an explicit
`1 ≤ M` guard on the square-root logarithm helper, excluding the totalized
`Real.log 0` boundary case.

The main claimed endpoint is that for every fixed $M\ge3$ and
$0<\varepsilon<2-\sqrt2$, frequently in $k$,

$$
X(M^{2^k})\le
 -(2-\sqrt2-\varepsilon)\lambda(M^{2^k}).
$$

It consequently makes $r(N^2)/r(N)^2$ unbounded.  This is one-sided negative
excursion information; it does not prove $D(N)\to0$, positive excursions,
two-sided oscillation, or an asymptotic formula.  Independent mathematical
and vacuity reviews certified the theorem and its advertised scope.

### Tower-index negative-defect density and quantitative rate

**Kernel checked.** At revision `6a6bb75bfbaa7301070a3ab5a5c24a3fde9b626b`, `Proofs/Erdos/Erdos142/SquareScaleNegativeDensity.lean`, imported by `Proofs/Erdos.lean`, proves the density results recorded in `Documents/erdos142-negative-defect-density.md`. The public endpoints are `Erdos142.eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit`, `Erdos142.eventually_card_squareScaleDefect_le_neg_const`, `Erdos142.eventually_card_squareScaleDefect_neg`, and `Erdos142.eventually_card_squareScaleDefect_nonpos`. The first pair give the existing $\delta_\beta=1-\log\sqrt2/\log(2-\beta)$ lower-density curve and its fixed-$H$ consequence. The new endpoint corollaries say that for every fixed tower $N_k=M^{2^k}$ with $M\ge3$ and every real $\delta<1/2$, eventually at least $\delta K$ indices $k<K$ have, respectively, $X(N_k)<0$ and $X(N_k)\le0$. Equivalently, the strict-negative set has tower-index lower density at least $1/2$.

The half-density proof chooses $\beta>0$ in the existing curve with $\delta<\delta_\beta$; it does not apply the source theorem at $\beta=0$. Positivity of $\lambda(N_k)$ at every tower scale makes the source bound imply strict negativity. The focused module and full `Erdos` umbrella builds succeeded; the exact axiom audit is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. This uses accepted Roth and EHPS/Behrend inputs, not Raghavan. It is tower-index density, not integer density or exact density, and does not assert the eventual-cardinality bound at $\delta=1/2$ or any endpoint magnitude. No overlap with P-shaped good scales, bounded gaps, $D\to0$, or asymptotic formula follows. The parameter endpoint $\beta=2-\sqrt2$ in the original density curve remains excluded, and no common set as $\beta$ varies is asserted.

Issue [#57](https://github.com/thatnealpatel/proofs/issues/57) tracks independent evaluation of soundness and global novelty. A scoped literature review found the growth-budget lemma standard and no explicit published Roth-number application. The live status remains **repository-level consequence / no global novelty claim**; issue #57 is not external certification of novelty.

**Accepted prose deduction plus external theorem.**  The separately accepted `Documents/erdos142-raghavan-square-defect-rate.md` combines the density theorem with Raghavan, arXiv:2603.27045v3, Theorem 1.4. On the same lower-density set (up to deleting finitely many indices), it yields the explicit growing bound

$$
X(N_k)\le-\beta c_R\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}.
$$

The density theorem itself is kernel checked and unconditional from accepted inputs; this quantitative magnitude is not Lean formalized and its Raghavan input remains external. This is a repository-level consequence, not an Erdős 142 solution or a global novelty claim.

This complements the existing positive-density P-shaped good-scale result in `Documents/erdos142-positive-density-square-scales.md`: on its positive-density tower-index set the good ratio gives a lower bound $X(N_k)\ge-(2-q)\lambda(N_k)$, whereas the new theorem gives an upper bound $X(N_k)\le-\beta\lambda(N_k)$ on a positive-lower-density set. No overlap, bounded-gap conclusion, or two-sided oscillation follows. Neither result proves eventual P, $D(N)\to0$, or an asymptotic formula.

### EHPS Chebyshev refinement

**Accepted prose deduction.**  The reviewed artifact was adopted in revision
`f6b62ff20a59cf775dae717430b0a217feb5a3f9`.  It ports the final archived
argument with one corrected primary-source locator.  Conditional on the cited
EHPS building-block proposition, it derives

$$
r(N)\ge
 \kappa N e^{-2\sqrt{\log(24/7)\log N}}(\log N)^{-5/4}
$$

and excludes only the specified critical-leading-coefficient comparison
profiles with logarithmic exponent $\beta>5/4$.  Independent mathematical and
provenance reviews found the deduction sound and its status accurate.  It is
not an EHPS theorem as stated, a Lean formalization, or an asymptotic formula.

## Campaign outputs and closed lanes

### Normalized square-tower excursions

**Kernel checked.**  The reviewed theorem was adopted in revision
`d2dd236dc67994865746894441a2e3213d0253aa`.  The integration candidate
compiled both the exact module and `Proofs/Erdos.lean`; the three new theorems
use exactly `propext`, `Classical.choice`, and `Quot.sound`.  For fixed
$M\ge3$ and $c>0$, if frequently
$D(M^{2^k})\ge c$, then frequently

$$
\frac{X(M^{2^k})}{\sqrt{\log(M^{2^k})}}
\le -(2-\sqrt2)c.
$$

The sequence kernel uses
$Z_k=\sqrt2D_{k+1}-2D_k$: if the displayed negative excursion failed
eventually, the excess $D_k-c$ would grow geometrically by a factor exceeding
one, contradicting the accepted eventual upper envelope for $D$.  This does
not prove that the premise holds, and therefore does not prove nonconvergence
or two-sided oscillation.

### High-mass entropy conjecture

**Accepted prose deduction.**  The reviewed counterexample was adopted in
revision `0dc08fc9cf05124ac1e93ddea3e8af41aac615f4` as
`Documents/erdos142-high-mass-entropy-counterexample.md`; it closes the
conjecture as stated.  Let $B\subseteq[0,N-1]$ be a maximum 3-AP-free set,
$|B|=r(N)$, and take a suitably regular $m$-element subset
$A\subseteq B\times B$ with $m=\lceil N\sqrt{r(N)}\rceil$.  Every subset of
$B\times B$ is a vector cap, so this meets the proposed threshold.  A random
$m$-subset has all row and column degrees asymptotic to $m/r(N)$ with positive
probability, giving

$$
H(X)=H(Y)=\log r(N)-o(1),\qquad H(X,Y)=\log m.
$$

Writing $\lambda=\log(N/r(N))$, it follows that

$$
I(X;Y)=\tfrac12\log N-\tfrac32\lambda+o(1),
\qquad d_X+d_Y=2\lambda+o(1).
$$

The accepted lower bound $\lambda=O(\sqrt{\log N})$ makes
$I/(d_X+d_Y+1)$ unbounded.  This defeats the entropy inequality but not the
desired P-shaped cardinality bound, which this family still satisfies.
Independent mathematical review certified the ceiling, concentration,
entropy calculation, asymptotic bookkeeping, and exact non-consequence.

### Carry-cardinality obstruction

**Kernel checked.** At revision
`37a2ec6468a5a33ee7e3dd966ecc816d0971f46c`,
`Proofs/Erdos/Erdos142/CarryCardinalityCapObstruction.lean`, imported by
`Proofs/Erdos.lean`, proves the finite endpoint
`Erdos142.exists_carryCardinalityCap`. Focused and full `Erdos` builds
succeeded (8813 jobs); independent vacuity and foundations reviews were clean.
The public endpoints use exactly `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

For each $N\ge3$, it constructs a bounded $G\subseteq[0,N)^2$ with every
ordinary natural-number row and column fiber 3-AP-free; all in-range fibers
have common size $b$, $2b\le N$, and
$N\,r(N)\le2|G|$. It also contains $(0,0),(1,1),(2,2)$, so its base-$N$
scalar image contains the nontrivial progression $0,N+1,2(N+1)$. The scalar
encoding is injective on the bounded square, but the witness is deliberately
not scalar-3-AP-free.

The finite construction half-slices a maximum ordinary 3-AP-free subset of
$[0,N)$, translates and (if needed) shrinks the dense piece into a short
interval, embeds it as a modular cap $B\subseteq\mathbb Z/N\mathbb Z$, and
translates $B$ to contain zero. The graph $x-y\in B$ has fibers that are
translates/reflections of $B$, and has $N|B|$ edges. Thus this relaxation,
using only ordinary row/column freeness and the pair-size cap, cannot imply a
universal $o(Nr(N))$ cardinality upper bound, and alone cannot prove the
P-shaped saving. This closes a proof method, not Erdős 142; it is not an
asymptotic theorem about $r(N)$.

See [`erdos142-carry-cardinality-obstruction.md`](erdos142-carry-cardinality-obstruction.md)
for the proof sketch and the closed computational lead. Evidence labels and
scope are preserved there as well. Issue [#58](https://github.com/thatnealpatel/proofs/issues/58)
requests external evaluation of this obstruction; it is not a novelty
certification.

### Reflection-shadow route

**Kernel checked.** At accepted revision `66eca70dc75c548dcf27862d0f8c8bcc5e436f67`, `Proofs/Erdos/Erdos142/ReflectionShadow.lean`, imported by `Proofs/Erdos.lean`, defines the integer `reflectionShadow` and `differenceSources`. It proves that a finite ordinary 3AP-free `A⊂ℤ` is disjoint from its nontrivial reflection shadow, and that `2·|{x∈A:x+d∈A}|≤|A|` for every nonzero `d`. Focused and full builds succeeded (8814 jobs); the public endpoints use only `[propext, Classical.choice, Quot.sound]`. Independent mathematical review was clean. A vacuity audit found no semantic/trust issue; additional scratch cardinality probes did not complete and are not integrated.

**Informal finite mathematics, independently audited but not Lean formalized.** For scalar-free `A⊂[0,N²)` with `m=|A|`, the target-wise union of valid carry cases is exactly the in-range nontrivial reflection shadow `S(A)`, so `|S(A)|≤N²−m`; median reflection gives `|S(A)|≥floor((m−1)/2)`. With in-range representation multiplicities `ν(c)=#{(a,b)∈A²:a≠b:2a−b=c}`, `M=Σν`, `E=Σν²`, and `r_A(d)=|{x∈A:x+d∈A}|`, the informal collision count gives `E≤M+Σ_{d≠0}r_A(d)r_A(2d)≤Σ_d r_A(d)r_A(2d)`. The formal fixed-difference theorem is exactly `r_A(d)≤floor(m/2)` for `d≠0`, but using it naively is far too weak. The formal module does **not** contain the carry-union identity, median bound, mass/energy identities, or candidate below.

**Exploratory/conjectural.** The candidate `|S(A)|³ r(N)^8 ≥ N²(m−N)^6` for `m>N` is unproved and would imply `r(N²)≤N+N^(2/3)r(N)^(4/3)≤2N^(2/3)r(N)^(4/3)` eventually, a P-shaped gain with `η=1/3`; this would be an intermediate estimate, not an asymptotic formula. It is checked informally for `N=3`, eventual fixed-linear `m≤KN` regimes, and short ternary Cartesian products; exhaustive `N≤6` and structured searches are computation only. A sufficient second-moment overlap bound `E≤M²r(N)^(8/3)/(N^(2/3)(m−N)²)` remains unproved and undisproved. The fixed-difference matching argument does not bound fixed-target multiplicity: `{1,2,4,8}⊂[9]` has `ν(0)=3`. A capped-at-2 moment variant is also unproved and at most within factor `9/8` of the desired support bound, not an independent breakthrough. See [`erdos142-reflection-shadow-route.md`](erdos142-reflection-shadow-route.md) for definitions, exact status, and derivations.

**Conditional significance only:** if an eventual P bound with `η=1/3` and fixed constant held, its iteration would give `λ(M^{2^k})≳_M(4/3)^k` on a sufficiently large fixed square tower, equivalently a tower lower bound of logarithmic exponent `log₂(4/3)≈0.415`. This is not an all-scale interpolation or a solution of Erdős 142. The carry-sensitive route complements, but does not remove, the relaxation obstruction in [`erdos142-carry-cardinality-obstruction.md`](erdos142-carry-cardinality-obstruction.md); the comparison with the square-defect threshold is recorded in [`erdos142-negative-defect-density.md`](erdos142-negative-defect-density.md). No global novelty claim is made. Issue [#59](https://github.com/thatnealpatel/proofs/issues/59)
requests external evaluation of the reflection-shadow route and cubic
candidate; it is not a novelty certification.

## Dead ends and guardrails

- Exhaustive and sampled tests suggested a target-wise union-reflection
  coverage inequality implying
  $r(N^2)\le N+\sqrt N\,r(N)^{3/2}$. This is a dead exploratory lead, not a
  live conjecture or accepted computation theorem. The accepted Behrend lower
  bound absorbs $N$ eventually, yielding a P-shaped estimate with
  $\eta=1/2>\sqrt2-1$. That eventual estimate would imply
  $X(N)\ge-\tfrac12\lambda(N)-O(1)$, contradicted on fixed square towers by
  the accepted negative square-defect theorem (choose
  $\varepsilon<2-\sqrt2-\tfrac12$). Finite tests therefore cannot support
  this inequality asymptotically. A viable positional/collision route must
  retain reflected-digit locations and target $\eta\le\sqrt2-1$.
- The universal mutual-information bound without a high-mass hypothesis is
  false for graph caps.
- Pairwise fiber sizes or energies cannot force a local mixed midpoint count;
  translated-fiber examples kill that inference.
- The one-scale edge/window LP has a uniform feasible point of order
  $Nr(N)$, so its dual cannot produce the required power saving.
- **Kernel checked:** row/column ordinary freeness and the pair-size cap
  alone permit cardinality at least $Nr(N)/2$; see the carry-cardinality
  obstruction above. They cannot force a universal $o(Nr(N))$ bound.
- Rank, radius, and measure of a generic Bohr set do not guarantee an
  interval-scale affine copy; one copy would not provide density averaging
  anyway.
- The carry modes in base $N$ are all of $-1,0,1$.  Any scalar fiber theorem
  must either retain all three or explicitly pass to a valid stronger vector
  relaxation.
- $r(N)$ is monotone, but arbitrary monotonicity of $\lambda(N)$ is not
  available.  The accepted reverse comparison loses $\log2$.

## Next decisions

1. Sharpen the negative-defect distribution: the strict-negative set now has
   lower tower-index density at least $1/2$ (every fixed $\delta<1/2$ is
   eventually attained). Investigate exact density or endpoint magnitude,
   overlap with the positive-density P-shaped good scales, and gap control.
   The original $\beta$-curve endpoint remains excluded; no cardinal bound at
   $\delta=1/2$, no bounded gaps, and no common set across $\beta$ is known.
2. Develop carry-sensitive global aggregation retaining reflected-digit
   locations. The reflection-shadow candidate and its open second-moment overlap
   estimate are recorded in
   [`erdos142-reflection-shadow-route.md`](erdos142-reflection-shadow-route.md);
   keep unequal-fiber aggregation and Cartesian sub-products as stress tests.
   Any P-shaped exponent target must satisfy $\eta\le\sqrt2-1$.
3. Keep the entropy route closed unless a replacement inequality either
   excludes sub-products or applies only within an $\exp(O(\lambda))$ factor
   of the row-cap maximum.

## Current handoff

See [`erdos142-research-handoff-2026-09-27.md`](erdos142-research-handoff-2026-09-27.md)
for the self-contained frontier at accepted revision
`596825af4c347bbb311da8a340bec333c45b2f9a`. Any new potential novelty claim
must receive its own repository issue or an explicit scoped update to the
matching existing issue before it is advertised; filed requests are external
evaluation, not novelty certification.
