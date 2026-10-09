# Polynomial bad-prime sieve without a unit-leading hypothesis

## Verdict and scope

**Valid arithmetic gate (prose-verified; not Lean-checked).** This note removes the condition `gcd(k*leading(P),M)=1` from the fixed-degree polynomial full-neighborhood model. It retains the exact full-neighborhood, squarefree-modulus, canonical-residue, band, and realized-congruence hypotheses. The replacement is a finite bad-prime sieve: discard indices `j` for which a large prime at which `P` becomes affine also divides `j+a₁`.

The conclusion is a necessary sparsity condition for a deficient *full-neighborhood union* in this explicit model. It is not a reduction of arbitrary Hall subsets, an arbitrary-phase theorem, or an exponent improvement for Problem 711. No novelty claim is made. The local progression-union and quadratic CRT provenance is Chen--Korsky, Section 5 of `/home/exedev/p/erdos711-restart-20261009/sources/ChenKorsky-2607.26450.tex` (compression lemma at lines 330--350, prime-rich block and construction at lines 354--429). The historical quadratic CRT note at revision `672d5ebf503e293036ea21732e6f1c584cadab9a` remains unchanged.

## Formalization contract

Fix an integer `k >= 2`. Let

* `v,W,L` be positive integers, with `L >= 3`;
* `D` be a nonempty set of distinct integer steps in `[v,v+W)`, and `Q=|D|`;
* `M >= 2` be squarefree;
* `P in Z[T]` have degree at most `k` (including degree zero and one), and let `a₁` be its coefficient of `T`;
* `b_d in {1,...,M}` be the canonical positive representative of `P(d) mod M`;
* `M+(L-1)W < v`;
* an actual integer `m >= 0` realize all congruences `m = -b_d (mod d)` for `d in D`.

Set `I={m+1,...,m+Lv}` and

`N_d={m+b_d+j d : 0 <= j < L}`.

The congruence and band hypotheses imply that these are exactly the multiples of `d` in `I`. Put `T_j={b_d+j d:d in D}`. The sets `T_j` lie in pairwise disjoint bands, since

`jv+1 <= b_d+jd <= M+j(v+W-1) < (j+1)v+1`.

Consequently translation by `m` identifies the full-neighborhood union with the disjoint union of the `T_j`.

Define the bad-prime product

`R = product {q : q prime, q | M, q > k, and deg(P mod q) <= 1}`.

For `1 <= j < L`, call `j` good when `gcd(j+a₁,R)=1`, and let `G` be the number of good indices. If `R=1`, every index is good and `G=L-1` exactly.

Define

`S_M = product_{q|M}(2-1/q) = sum_{e|M} phi(e)/e`,

and `H_r=sum_{t=1}^r 1/t`. Then the gate is

`|union_d N_d| >= Q G - (W+M) k^(omega(M)) S_M H_(L-1)`.

In particular, if the full-neighborhood family is deficient, `|union_d N_d|<Q`, and `G>1`, then

`Q(G-1) < (W+M) k^(omega(M)) S_M H_(L-1)`.

The strict sign follows from strict deficiency; a non-strict version is safe if the consumer uses `<=`.

## Collision proof

For `j>=1`, let `C_j` count unordered pairs of distinct steps whose values in `T_j` coincide. Orient one as `d` and `d+Delta`, with `Delta>0`. Equality gives

`j Delta = b_d-b_(d+Delta)`.

Because both canonical residues lie in `[1,M]`, a collision has

`1 <= Delta < M/j`.

Write `g=gcd(Delta,M)`. Since `b_x` is the residue of `P(x)`, reducing the equality modulo `M` gives

`Delta (F_Delta(d)+j) = 0 (mod M)`,

where the integer polynomial

`F_Delta(T)=(P(T+Delta)-P(T))/Delta`

is integral by the binomial theorem. Cancelling the integer gcd gives

`F_Delta(d)+j = 0 (mod M/g)`.

This cancellation does not assume that `Delta` is a unit modulo `M`.

Consider a prime `q | M/g`; then `q` does not divide `Delta`.

1. If `q<=k`, the congruence has at most `q<=k` residue roots, even if the polynomial is identically zero.
2. If `q>k` and the reduced polynomial `P mod q` has degree `r>=2`, then `r<=k` and the reduced `F_Delta` has degree `r-1`, with leading coefficient `r` times the leading coefficient of `P mod q`. This is nonzero because `q>k>=r`. Thus it has at most `r-1<=k-1<k` roots.
3. If `q>k` and `P mod q` has degree at most one, then `F_Delta=a₁ mod q`. Goodness says `q` does not divide `j+a₁`, so `F_Delta+j` is a nonzero constant and has no roots.

Thus, for good `j`, there are at most `k` root classes modulo each prime factor of `M/g`. Squarefreeness and the Chinese remainder theorem give at most `k^(omega(M/g)) <= k^(omega(M))` root classes modulo `M/g`. For each root class, an interval of `W` candidate integers contains at most `Wg/M+1` representatives. Hence the total number of candidate `d` for this `Delta` is at most

`k^(omega(M/g)) (Wg/M+1)
 <= k^(omega(M)) (W+M)g/M`.


For squarefree `M`, for every real `A>=0` the number of positive multiples `e*t` satisfying `e*t<A` is at most `A/e`. Therefore, using `gcd(Delta,M)=sum_{e|gcd(Delta,M)}phi(e)`,

`sum_(1<=Delta<A) gcd(Delta,M)
 <= A sum_(e|M) phi(e)/e = A S_M`.

There is no floor formula needed, and this handles nonintegral `A` correctly. With `A=M/j`, the preceding total-per-`Delta` bound gives

`C_j <= (W+M) k^(omega(M)) S_M / j`.


A fiber of multiplicity `r` loses `r-1` distinct values and contributes `choose(r,2)` collision pairs, so `|T_j| >= Q-C_j`.

## Good-index count and Hall consumer

Inclusion--exclusion over the prime divisors of `R`, applied to the shifted interval `j=1,...,L-1`, gives

`G >= (L-1) phi(R)/R - 2^(omega(R))`.

Each divisor contributes at most one endpoint-rounding error; the displayed bound is uniform in the shift `a₁`. For `R=1`, use the exact value `G=L-1` rather than the weaker error form.

The bands are disjoint, so summing only the good bands (and discarding `j=0` and bad bands) yields

`|union_d N_d| = sum_(j=0)^(L-1)|T_j|
 >= sum_(j good)|T_j|
 >= QG - (W+M)k^(omega(M))S_M H_(L-1)`.

This is why an ordinary untagged union is legitimate here: the supplied band inequality makes distinct `j` occupy disjoint integer intervals. No all-subsets Hall reduction is being asserted.

## Uniform polynomial-length consequence

Assume additionally the ambient bounds `M<=W<=n`, all steps are at most `n`, fixed `k`, and `L>=n^epsilon` for fixed `epsilon>0`. The band condition in the intended `n`-bounded setting supplies `L<=n` (the finite inequality itself does not need this upper bound). Standard elementary uniform estimates give, uniformly for integers `R<=M<=n`,

`2^(omega(R))=n^(o(1))`, `R/phi(R)=n^(o(1))`,
`k^(omega(M))S_M=n^(o(1))`, and `H_(L-1)=O(log n)`.

Hence the inclusion--exclusion bound gives

`G >= n^(epsilon-o(1))`.

If deficiency holds, then for large `n`, `G-1` has the same order, and `M<=W` gives

`Q/W <= 2 k^(omega(M)) S_M H_(L-1)/(G-1)
     = n^(-epsilon+o(1))`.

Thus a rich prime block (for example `Q >= W/(2 log n)`) cannot be deficient at polynomial `L`, without any unit-leading-coefficient assumption. This does not exclude lengths `L=n^(o(1))`.

## What squarefreeness still blocks

Squarefreeness is load-bearing in three places: it makes the residual modulus `M/g` a product of fields for the CRT root count; it ensures that removing the primes dividing `Delta` is captured by the single gcd `g`; and it gives the clean identity/product for the gcd sum `S_M`. For non-squarefree moduli, cancellation modulo `M/g` and prime-by-prime root counts do not control repeated-prime-power congruences; a separate p-adic multiplicity analysis is required. The argument also relies essentially on canonical representatives in `[1,M]` for the strict bound `Delta<M/j`.

The condition that `m` actually exists remains separate: for non-coprime steps it is equivalent to the pairwise compatibility of the residue congruences. Polynomial residues alone do not produce `m`.

## Non-vacuity and compatibility with the sourced CRT family

The gate has a genuine sourced instantiation, rather than being compatible only because several quantities are all `n^(o(1))`. Take the quadratic source family (`k=2`) with

`M = product_{q first odd primes} q`,

`delta = 2^(-omega(M)) product_{q|M}(1+1/q)`,

`K=floor(1/(4 sqrt(delta log n)))`, `W=floor(n/(4K))`, and `L=K`. The source supplies a prime block of size `Q>=W/(2 log n)`, a location `v` with `M+KW<v`, and `b_p` the canonical positive residue of `p^2 mod M`. The prime steps are pairwise coprime, so the required `m` exists by CRT, and the source's full-neighborhood construction gives

`|U| <= 3K^2 W delta <= 3W/(16 log n) < Q`.

Every prime divisor of `M` is odd and therefore exceeds `k=2`, while `P mod q` remains quadratic. Hence `R=1` and `G=L-1`. This is an actual deficient full-neighborhood example covered by the present contract, with `L=K=n^(o(1))`; it is not ruled out by the polynomial-length consequence.

For this instantiation, `B=k^(omega(M))=2^(omega(M))` and

`S_M=product_{q|M}(2-1/q) >= product_{q|M}(1+1/q)`.

Together with the displayed source relations for `delta`, `K`, and `Q`, the gate's error term is more than large enough to coexist with the source deficiency. Thus compatibility is checked through the finite inequality and the actual sourced construction, not merely by observing that both `L` and auxiliary factors are subpolynomial.


Two independent prose audits were requested. Both accepted the local bad-prime sieve and checked the affine, constant, small-prime, `q|Delta`, CRT-lifting, endpoint, inclusion--exclusion, and asymptotic cases. One audit initially noted that the polynomial link must be explicit; here it is part of the definition of `b_d`, namely `b_d=P(d) mod M`. The other proposed a counterexample to the cross-`j` union bound, but its parameters violate the retained band condition (`M+(L-1)W<v`); with the band condition, the `T_j` are disjoint. These objections therefore do not invalidate the stated gate, but they identify two representation risks that must remain explicit in any formal consumer.

No bounded Sage experiment was needed: the decisive checks are exact finite-difference and divisor identities, and the only plausible numerical counterexamples above fail a stated hypothesis. The claim is prose-reviewed and interface-inspected only; it is not Lean-checked.

## Evidence and non-claims

* **Sourced:** Chen--Korsky's local progression-union framework and Section 5 quadratic compression/prime-rich-block/full-neighborhood construction; the historical subpolynomial quadratic CRT family.
* **Proved in this note:** the bad-prime root sieve, collision bound, good-index estimate, disjoint-band union bound, and polynomial-length sparsity consequence under deficiency.
* **Assumed:** canonical polynomial residues, squarefree `M`, realized `m`, the exact band inequality, and the ambient `n`-bounds.
* **Not established:** arbitrary phase patterns, nonsquarefree moduli, arbitrary Hall subsets, arbitrary neighborhoods, or any improvement to the Erdos 711 exponent. Polynomial coefficient heights are unrestricted in the stated model; the unresolved extension is to non-polynomial or otherwise arbitrary phase patterns.

The prior quadratic CRT examples remain compatible: for their odd squarefree modulus, the quadratic reduction is degree two at every modulus prime, so `R=1`; their `L=n^(o(1))` does not enter the polynomial-length exclusion.
