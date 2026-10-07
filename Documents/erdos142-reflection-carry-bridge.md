# Erdős 142: finite reflected-collision carry bridge

## Scope and receiving theorem

This is a finite localization of the **existing in-range reflection energy**,
not an estimate proving (O), (C), or Erdős 142. It specializes the three-carry
idea in L18 to nonnegative, zero-extended digit indicators. L19 and L20 are
not needed. Verification status and exact Lean names are recorded below.

The receiving expression is precisely

$$
E=\sum_{c\in[0,N^2)}\mathrm{reflectionMultiplicity}(A,c)^2
$$

in `ReflectionEnergyCriterion.sum_sq_mul_le_mass_sq_mul_of_card_condition`
and `ReflectionFiberOverlap.two_mul_sum_sq_multiplicity_le`. The former
assumes the exact natural-number cardinality condition

$$
(m-1)(m-N)^2\le\lfloor(m-1)^2/4\rfloor F
$$

and concludes $E(m-N)^2\le M^2F$; it uses no AP-freeness. The latter assumes
$A\subset[0,L)$, scalar `ThreeAPFree`, and $m\ge9$, and proves
$2E\le(m+\lfloor m/2\rfloor)M$. Neither supplies general (O).
The new bridge uses their actual multiplicity, not a cyclic proxy.

## Exact finite mathematics

For $N>0$ and $A\subset[0,N^2)$, let

$$
C_c=\{a\in A:2a-c\in A,\ a\ne c\},\qquad
\ell_N(a)=a\bmod N\in[0,N).
$$

`ReflectionMassEnergy.reflectionMultiplicity_eq_card_filter` identifies
$|C_c|$ with the number of ordered **nontrivial** representations $c=2a-b$.
The condition $a\ne c$ is equivalent to $a\ne b$ at $b=2a-c$.
The energy counts ordered collision tuples $(c,a,a')$ with
$c\in[0,N^2)$ and $a,a'\in C_c$. Collision diagonals $a=a'$ remain included;
this is distinct from including trivial reflection representations.

Define

$$
K_{z,k}=\#\{(c,a,a'):c\in[0,N^2),\ a,a'\in C_c,
\ \ell_N(a)+\ell_N(a')+\ell_N(c)=z+kN\},
$$

where $0\le z<N$ and $k\in\{0,1,2\}$. Each low-digit sum is in
$[0,3N)$, so Euclidean division supplies one and only one $(z,k)$.
Consequently

$$
E=\sum_{z=0}^{N-1}\sum_{k=0}^2K_{z,k},\qquad
\exists z,k:\quad E\le 3N K_{z,k}.
\tag{B}
$$

No AP-freeness, equal fiber sizes, positive mass, or $m>N$ is needed for this
bookkeeping. $A=\varnothing$ and $E=0$ are allowed; $N=0$ is excluded.

For the digit interpretation write
$a=x+Ni$, $a'=y+Nj$, and $c=n+Nv$, with all six digits in $[0,N)$.
Define the zero-extended center indicator

$$
f_{i,v}(x,n)=\mathbf1_{0\le x,n,i,v<N}
 \mathbf1_A(x+Ni)\mathbf1_A(2(x+Ni)-(n+Nv))
 \mathbf1_{x+Ni\ne n+Nv}.
$$

Its endpoint membership is a **scalar** test. In particular it retains any
borrow/carry in $2x-n$ and the actual high-digit boundary of the endpoint;
it is not a coordinatewise AP-free relaxation. Then, as finite mathematics,

$$
K_{z,k}=\sum_{i,j,v,x,y\in[0,N)}
 f_{i,v}(x,z+kN-x-y)f_{j,v}(y,z+kN-x-y).
\tag{D}
$$

The condition $0\le z+kN-x-y<N$ is hard zero extension, not a cyclic
identification. Unequal rows are retained through the independent indices
$i,j$. Formula (D) explains the reflected argument in L18; the Lean digit
endpoint below states it as an exact membership equivalence rather than a
complex normalized-average identity.

## L18 correspondence and direction check

Canonical source:
`/home/exedev/x/math/lean/OAI/Combinatorics/Progressions/Estimates/CyclicMixedReflection.lean`,
`OAI.Erdos3.tripleCarry_representative` and
`OAI.Erdos3.exists_unwrapped_family_reflected_correlation` (the family
statement starts at line 247 in the inspected source). This is attribution
of the adapted three-carry localization idea, not a claim of copying,
direction of influence, or external kernel certification.

The source-inspected family theorem requires nonempty finite $T$, nonzero
$N$, $p\ge0$, unit-bounded complex $R,S,b$, and a wrapped norm lower bound
$\exp(-p)$. It produces unit-bounded complex weights on integer arguments and an unwrapped norm
lower bound $\exp(-(2p+10))$. Its interval-removal proof first retains a
carry with loss $3$, then smoothing gives $(\exp(-p)/3)^2/48$
$=\exp(-2p)/432$, weakened to the displayed exponential bound.

Here the concrete proposed interpretation is
$T=[0,N)^3$ with $t=(i,j,v)$,
$R_t(x,n)=f_{i,v}(x,n)$, $S_t(y,n)=f_{j,v}(y,n)$, and $b=1$.
Indicators supply unit boundedness, and $N>0$ supplies a nonempty family.
Complex conjugation has no effect on these real $0/1$ factors.
Let $W_z$ be the same unnormalized digit sum with
$n=(z-x-y)\bmod N$. Finite mathematics gives

$$
W_z=\sum_{k=0}^2K_{z,k},\qquad E=\sum_zW_z.
$$

Thus some wrapped normalized correlation is at least $E/N^6$:
the average over $t,x,y$ has denominator $N^5$, and choosing $z$ loses
another factor $N$. If $E>0$, one can choose
$p=\log(N^6/E)\ge0$ (there are at most $N^6$ digit tuples).
L18 would then certify only

$$
K_{z,k}\ge \exp(-10)\,E^2/N^7,
$$

since the unwrapped weighted sum has norm at most its nonnegative support
count $K_{z,k}$. The elementary positive extraction (B) instead gives the
stronger $K_{z,k}\ge E/(3N)$, with no smoothing, characters, or exponential
loss. This is why the full complex theorem was not ported.

**Genuinely missing obligation:** a positional **upper** bound on these
mixed reflected collision slices, or on their sum, sharp enough to give

$$
E N^{2/3}(m-N)^2\le M^2r_3(N)^{8/3}.
$$

Neither extraction nor the supplied unit-norm bounds control that upper
bound. A correlation norm is not automatically a positive count. For
example in the source model with $N=2$, $R=S=1$, and
$b(0)=1,b(1)=-1$, the wrapped norm is $|\mathbb E b|^2=0$ although the
unweighted normalized count is $1$. The triangle inequality converts a
weighted **lower** norm bound to a support **lower** bound only after a
specific indicator interpretation; it does not reverse the inequality.
This obstruction does not refute (O) or (C).

The carry $k=0,1,2$ here is the quotient of a sum of three nonnegative low
digits. It is not the local Fourier note's AP residual $t=-1,0,1$; there is
no automatic universal reindexing $t=k-1$. The $Q=4N$ AP Fourier identity,
its diagonal ordered triples, and its hard high-digit indicators are
unchanged. No theorem equating it to this collision count is asserted.

## Dependency choice and unused candidates

The external source imports `AnchoredReflectedFamily` and
`Fourier.QuadraticFrequencyCoordinates`. A source-only recursive traversal
of their OAI imports reached 1,825 modules (377,425 source lines); this is
not a trust audit. The external toolchain is Lean `v4.34.1`, whereas this
project uses `v4.33.0-rc1`. No external build, axiom audit, or compatibility
experiment was undertaken. The selected proof is a small local finite
adaptation using local Mathlib; no external dependency is imported or copied.
The differing toolchains were a reason to avoid a bulk port, not a proven
incompatibility of the finite mathematics.

L19's `FiniteFiberVolumeBound.product_measureReal_le_of_fiber_bound` is a
pointwise-fiber integration principle. The local multiplicity/mass identities
and Mathlib finite fiber-cardinality sums already supply the required
finite bookkeeping. L19's reflected restriction tools additionally need
symmetry and translation total-variation hypotheses absent here. L20's
weighted Hölder and inner-progression families do not supply an identified
missing input to (B) or (D). Neither L19 nor L20 was used.
The external AP upper-bound headline remains opposite-direction input for
an upper bound on $\lambda(N)=\log(N/r_3(N))$; it is not a Roth-number lower
bound and plays no role.

## Verification and boundary evidence

The reproducible computation is
`Programs/Erdos142/verify_reflection_carry_energy.sage`:

```
timeout 60 sage Programs/Erdos142/verify_reflection_carry_energy.sage
```

It checks all 530 subsets for $N=1,2,3$, including 184 scalar-3AP-free
subsets, against an independently organized six-digit count. It checks
(B), (D), and the per-residue three-carry identity. Additional stress cases
include empty/zero-energy cases in the exhaustive domain, unequal fibers,
interval endpoints, non-free full intervals, and:

- $N=3$, $A=\{1,2,4,8\}$: $M=6$, $E=12$; nonzero slices
  $K_{0,1}=5$, $K_{1,1}=2$, $K_{2,0}=5$.
- $N=3$, $A=\{2,5\}$: the unique representation is center $5$, endpoint $2$,
  target $8$; $E=K_{0,2}=1$. This scalar-free example requires the third
  carry and the upper target boundary.
- $N=3$, $A=\{0,3\}$: $E=K_{0,0}=1$.

These tests are computation, not a universal proof. The initial computation
reached its assertions but failed JSON serialization of Sage integers;
after explicit integer conversion it completed successfully.

## Lean declarations

`Proofs/Erdos/Erdos142/ReflectionCarryEnergy.lean` defines
`reflectionCollisions`, `reflectionLowSum`, `reflectionCarrySlice`,
`reflectionDigitCenter`, and `reflectionWrappedSlice`, in namespace
`Erdos142`. The module is imported by `Proofs/Erdos.lean`.
The collision and slice sets are exactly the tuples defined above;
`reflectionWrappedSlice` filters collisions by `reflectionLowSum N tuple % N = z`.
`reflectionDigitCenter A N i v x n` is the proposition whose $0/1$ indicator
is $f_{i,v}(x,n)$ above.

The principal public statements are:

```lean
reflection_energy_eq_sum_carry (A : Finset ℤ) (N : ℕ) (hN : 0 < N) :
  (∑ c ∈ Finset.Ico 0 ((N : ℤ) ^ 2), (reflectionMultiplicity A c) ^ 2) =
    ∑ z ∈ Finset.Ico 0 (N : ℤ), ∑ k : Fin 3,
      (reflectionCarrySlice A N z k).card

exists_reflectionCarrySlice_large (A : Finset ℤ) (N : ℕ) (hN : 0 < N) :
  ∃ z ∈ Finset.Ico 0 (N : ℤ), ∃ k : Fin 3,
    (∑ c ∈ Finset.Ico 0 ((N : ℤ) ^ 2), (reflectionMultiplicity A c) ^ 2) ≤
      3 * N * (reflectionCarrySlice A N z k).card

card_reflectionWrappedSlice_eq_sum_carry
    (A : Finset ℤ) (N : ℕ) (hN : 0 < N)
    (z : ℤ) (hz : z ∈ Finset.Ico 0 (N : ℤ)) :
  (reflectionWrappedSlice A N z).card =
    ∑ k : Fin 3, (reflectionCarrySlice A N z k).card

reflection_energy_eq_sum_wrapped (A : Finset ℤ) (N : ℕ) (hN : 0 < N) :
  (∑ c ∈ Finset.Ico 0 ((N : ℤ) ^ 2), (reflectionMultiplicity A c) ^ 2) =
    ∑ z ∈ Finset.Ico 0 (N : ℤ), (reflectionWrappedSlice A N z).card
```

These four theorems are **stronger in domain** than the intended local
application: they require only $N>0$, with arbitrary finite integer $A$.
No bound on $A$, AP-freeness, or positive energy is assumed.

For arbitrary $A,N,z,k,i,j,v,x,y,n$, the public
`mem_reflectionCarrySlice_digits` assumes that all six digits
$i,j,v,x,y,n$ belong to `Finset.Ico 0 (N : ℤ)` and concludes

$$
(n+Nv,x+Ni,y+Nj)\in\mathrm{reflectionCarrySlice}(A,N,z,k)
\iff
\mathrm{reflectionDigitCenter}(A,N,i,v,x,n)\ \land
\mathrm{reflectionDigitCenter}(A,N,j,v,y,n)\ \land
n=z+kN-x-y.
$$

The public `reflectionCarrySlice_digit_cell_iff` assumes only the five
digits $i,j,v,x,y$ are in range and concludes

$$
\begin{aligned}
&\exists n\in[0,N): (n+Nv,x+Ni,y+Nj)\in
 \mathrm{reflectionCarrySlice}(A,N,z,k)\\
&\quad\iff \mathrm{reflectionDigitCenter}(A,N,i,v,x,z+kN-x-y)\ \land
 \mathrm{reflectionDigitCenter}(A,N,j,v,y,z+kN-x-y).
\end{aligned}
$$

These equivalences neither assume $z$ is in range nor require $N>0$;
the extraction and partition endpoints above do require $N>0$.
The other public helpers are `mem_reflectionCollisions`,
`mem_reflectionCarrySlice`, `card_reflectionCollisions`,
`reflectionLowSum_bounds`, and `sum_carry_indicator`.
Concrete compiled examples include the essential third carry for
$A=\{2,5\},N=3$, and empty collisions at $N=1$.

The focused `lake -q build Erdos.Erdos142.ReflectionCarryEnergy` passed. The reviewer’s own 120s umbrella attempt timed out, while the author’s `timeout 600s lake -q build Erdos` passed (8871 jobs; unrelated inherited `sorry` warnings). A parent's fresh isolated workspace exact-source rebuild passed (3007 jobs), and `lake env lean Proofs/Scratch/Erdos142CarryAudit.lean` printed all ELEVEN endpoints exactly `[propext, Classical.choice, Quot.sound]`; that scratch workspace was never integrated or adopted. An initial 300s umbrella attempt also timed out during unrelated cold builds before the bounded resumed build passed. Semantic/vacuity review of exact code candidate `964f753dc24b19e46b56bc61dbaa38525e0c6eaf` completed CLEAN. Foundations review requested only the repaired weights wording. Independent review outcomes are reported with campaign acceptance; no novelty claim is made.

## Remaining frontier

This bridge supplies a local, boundary-exact interpretation of L18's
wrapped/unwrapped collision correlations and a finite extraction from the
actual local energy. It does not improve the accepted universal or
AP-free averaged energy bounds. No sharp collision-slice upper estimate,
cross-row cancellation, general (O), support target (C), eventual square
gain, or Erdős 142 asymptotic conclusion is proved. No novelty claim is made:
finite partition and pigeonhole extraction are standard bookkeeping.
