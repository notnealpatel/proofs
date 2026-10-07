# Popular reflection targets: a new triple bound

## The theorem

This checkpoint records a repository-new, kernel-checked theorem about reflection
multiplicities. Let $A\subset\mathbb Z$ be finite and 3-AP-free, and write
\[
\nu_c=\#\{a\in A:2a-c\in A,\ a\ne c\}.
\]
(The count is ordered: the reflected endpoint $2a-c$ is determined by $a$.)
For an arithmetic progression of targets $c,d,e$ with
$c+e=2d$ and $c\ne e$, the finalized Lean source proves
\[
  \nu_c+\nu_d+\nu_e\le 2(\lvert A\rvert-1).
\]
In the public spelling, for `A : Finset ℤ`, `c d e : ℤ`, and
`hfree : ThreeAPFree (A : Set ℤ)`, the endpoint is
`reflectionMultiplicity_triple_le A c d e hfree hap hne`.  The right side is
natural-number subtraction and multiplication, so the displayed formula has
exactly the finite-cardinality meaning formalized by Lean.

The result is genuinely positional: it concerns three targets themselves being
in a 3-AP, rather than merely three large values of $\nu$.  It also makes no
interval, positivity, or positive-mass assumption.  Reflection collisions with
$a=a'$ remain counted in the associated energy; the theorem is not obtained by
silently deleting those diagonals.

## Proof idea

Order the targets as $c<d<e$ (the other orders are handled by the symmetry in
the formal statement).  A center has reflection degree at most two.  Indeed,
three distinct reflected endpoints from one center would produce a nontrivial
3-AP in $A$; the 3-AP-free hypothesis rules this out.  The estimate for zero or one elements of $A$ follows from the universal cap
$\nu_x\le |A|-1$; the theorem always has three target variables.

Assume therefore that there are three targets and put $m=|A|$.  Let
$u=\min A$ and $v=\max A$.  If $u<c$, the minimum endpoint cannot be reflected through $c$ to another member of $A$; more precisely, if $D(x)$ denotes the incidence count for center $x$ against the three fixed targets, then $D(u)=0$.  Similarly, $v>e$ gives $D(v)=0$.  These two zero-degree contributions subtract two units from the naive total cap $2m$.  Thus in this exterior case the sum is at most
$2m-2=2(m-1)$.

It remains to consider the non-exterior case.  If $m\ge2$, then either the
extreme points lie at or between the targets, and every remaining target has
degree at most two.  The endpoint degrees are at most one: at the lower
endpoint, a second reflected endpoint would lie below the minimum, and the
same argument applies at the upper endpoint.  The only possible overlap of
these endpoint exceptions would require the middle target to be simultaneously
below the minimum and above it (equivalently, the minimum-endpoint and
maximum-endpoint reflection constraints force incompatible inequalities).
Consequently the two endpoint losses are distinct, and again the total is at
most $2m-2$.  The cases $m=0,1$ are vacuous or immediate.  This is the finite
incidence argument implemented by the finalized source, not an asymptotic
estimate disguised as one.

A useful corollary packages the theorem as a target-set obstruction.  Define
\[
 \operatorname{richReflectionTargets}(A,T)=
 \{c\in T:2(|A|-1)<3\nu_c\}
\]
for finite target set $T$.  The companion theorem
`threeAPFree_richReflectionTargets` says this rich set is 3-AP-free for every
finite $T$.  Otherwise three rich targets would have sum of multiplicities
strictly greater than $2(m-1)$, contradicting the triple bound.  This is a
clean way to prune popular-target searches, while preserving arbitrary finite
and non-interval target sets.

## Equality, status, and limits

The additive constant is sharp at the stated scale: $A=\{0,1,3,4\}$ and
targets $(-1,2,5)$ give multiplicity two at each target and attain equality.
As an informal translation check (not a compiled Lean example), the shifted set
$A=\{1,2,4,5\}$ with targets $(0,3,6)$ has the same behavior, with all targets
in $[0,7)$.  Only the original example and the failure of the analogous
non-strict rich cutoff are kernel-checked in the new module.  Do not infer that the multiplicative constant two is optimal for
large numbers of targets: this result claims only the additive correction
$2(m-1)$ for a target triple.

The result is repository-new, not certified literature novelty. Bounded searches
found no direct match for “popular reflection targets” or a sum
$\nu_c+\nu_d+\nu_e$; broader web results concerned generic sumset growth and
progression-free-set structure. Those checks are provenance context, not a
novelty certification. The stronger statement
$\sum_c\nu_c\le\lfloor3m/2\rfloor$ remains a conjecture: exhaustive data over
scalar caps with target APs in the tested window gave maxima
$0,2,4,6,7,9,9,10$ for $m=1,\ldots,8$, but finite evidence is not a proof.
Optional parity and window-tail ideas remain informal. No automatic improvement
of the existing global $E$, $O$, or $C$ routes follows, and Erdős 142 remains
open. This checkpoint should be updated if the conjecture is proved or
refuted.

## Verification record

The finalized source is `Proofs/Erdos/Erdos142/ReflectionPopularTargets.lean`.
The primary focused prover output is `d231ee8c590cd0344e7cf16de8257c4d38fea81d`.
The registered Lean-only integration candidate is
`fc00ae3d7812dfc7e21737a5dee723ad1b10fb10` (integration `snuQXux`), not an
isolated parent-workspace revision. A later combined Lean-plus-documents
candidate, reviewed as `ecd269ab4bbe3db90e5d970ab171c26cb2ca7238`, records the
documentation combination; it is not presented here as a future finalized hash.
The parent copied the byte-identical module from `fc00...` into isolated audit
workspace `dispatch-gxmCEPK`, verified the comparison, and built the module plus
scratch signature/axiom probes there. That workspace was intentionally not
integrated or adopted. Public declarations independently use only `propext`,
`Classical.choice`, and `Quot.sound`. Primary semantic review was CLEAN. The
parent then ran bounded `timeout 600s lake -q build Erdos` (tool task 660s) to
exit 0: the umbrella passed with inherited unrelated warnings, including sorry
warnings outside this module, and no new-module warnings. A historical reviewer
umbrella attempt timed out after 180s on unrelated modules; this is preserved
separately and is not a sorry-free umbrella claim. The foundations review of
`ecd269...` is not CLEAN solely because of the earlier provenance wording error.
Documentation fidelity recheck and adoption remain pending.
