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

## Dead ends and guardrails

- The tentative inequality
  $|A|\le N^{1/2}r(N)^{3/2}$ was rejected before dispatch.  It corresponds to
  exponent $\eta=1/2>\sqrt2-1$ and conflicts with the square-tower negative
  excursion mechanism.  Rephrasing the desired conclusion as a
  carry-compatible fiber inequality supplies no new mechanism.
- The universal mutual-information bound without a high-mass hypothesis is
  false for graph caps.
- Pairwise fiber sizes or energies cannot force a local mixed midpoint count;
  translated-fiber examples kill that inference.
- The one-scale edge/window LP has a uniform feasible point of order
  $Nr(N)$, so its dual cannot produce the required power saving.
- Row and column degree constraints alone permit order $Nr(N)$.
- Rank, radius, and measure of a generic Bohr set do not guarantee an
  interval-scale affine copy; one copy would not provide density averaging
  anyway.
- The carry modes in base $N$ are all of $-1,0,1$.  Any scalar fiber theorem
  must either retain all three or explicitly pass to a valid stronger vector
  relaxation.
- $r(N)$ is monotone, but arbitrary monotonicity of $\lambda(N)$ is not
  available.  The accepted reverse comparison loses $\log2$.

## Next decisions

1. Seek an unconditional input that establishes persistent positive $D$-mass
   on a fixed square tower, or bypasses that premise; none is currently known.
2. Treat the entropy route as closed.  Any replacement inequality must either
   exclude sub-products or apply only within an $\exp(O(\lambda))$ factor of
   the row-cap maximum.
3. Return to a carry-sensitive unequal-fiber inequality or Bohr-to-interval
   density averaging, with Cartesian sub-products as a mandatory stress test.
