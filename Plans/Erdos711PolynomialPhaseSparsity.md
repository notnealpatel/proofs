# Polynomial-phase sparsity for the Hall obstruction

## Status and question

This note tests one precise proposal for the Erdos 711 Hall obstruction: replace the quadratic CRT phase by a fixed-degree integer polynomial phase and ask whether a deficient full-neighborhood family can have polynomial length. The result below is a proved arithmetic consumer for one explicit model. It does **not** prove a theorem for arbitrary phase patterns or arbitrary Hall subsets, and it makes no full-solution claim.

The conclusion is negative for rich step families in this model. If the phase has fixed degree `k`, the modulus is squarefree, and its leading coefficient remains a unit at every prime of the modulus, then a deficient family of polynomial length must be arithmetically sparse. In particular a rich prime block cannot be deficient when `L >= n^epsilon`. The unit and squarefreeness hypotheses are load-bearing; without them the root-count argument can degenerate.

The primary source was inspected in Section 2 (the local progression-union method) and Section 5 (quadratic CRT compression, prime-rich blocks, CRT neighborhoods, and Hall deficiency):
`/home/exedev/p/erdos711-restart-20261009/sources/ChenKorsky-2607.26450.tex`.
The existing CRT entropy artifact was read from revision `672d5ebf503e293036ea21732e6f1c584cadab9a` with `jj file show`; it remains unchanged. Its square-phase family has subpolynomial length and is not refuted here.

## Exact model and formalization contract

Let

* `v,W,L >= 1`, with `L >= 3` for the Hall consequence;
* `D` be a nonempty set of distinct positive integer steps contained in
  `{v, v+1, ..., v+W-1}`, and `Q = |D|`;
* `M >= 2` be squarefree;
* `P in Z[T]` have degree `k >= 2`, leading coefficient `c_k`, and
  `gcd(k*c_k,M)=1`;
* `b_d in {1,...,M}` be the canonical positive residue of `P(d) mod M`;
* `M + (L-1)W < v`.

Assume only **conditionally** that an actually existing integer `m >= 0` satisfies

`m = -b_d (mod d)` for every `d in D`.

No pairwise-coprimality or composite-modulus CRT existence is assumed. For pairwise coprime steps, existence follows from the ordinary CRT; for general integer steps this is an additional compatibility condition and must be realized before applying the result.

Set

`I = {m+1,...,m+Lv}`,
`N_d = {m+b_d+j*d : 0 <= j < L}`,
`U = union_{d in D} N_d`,
`T_j = {b_d+j*d : d in D}`.

Then the intended consumer is

`|U| >= Q(L-1) - (W+M) B S_M H_(L-1)`,

where

`B = (k-1)^(omega(M))`,
`S_M = sum_{e|M} phi(e)/e = product_{q|M}(2-1/q)`,

and `H_r = sum_{j=1}^r 1/j`. Thus genuine full-neighborhood deficiency `|U| < Q` implies

`Q(L-2) < (W+M) B S_M H_(L-1)`.

Using `<=` instead of `<` is a safe formalization variant.

## Boundary and band verification

For each `d`, the congruence for `m` makes every displayed point of `N_d` a multiple of `d`. Conversely, the multiples of `d` in `I` are exactly these points. Indeed, `1 <= b_d <= M`, while

`b_d + (L-1)d <= M + (L-1)(v+W-1) < Lv`,

by the stronger supplied assumption `M+(L-1)W<v`. The preceding translate with `j=-1` is at most `m+b_d-d <= m+M-v < m`, and the next translate with `j=L` is above `m+Lv`. Hence no endpoint contributes an extra multiple.

After subtracting `m`, `T_j` lies in the band

`[jv+1, jv+M+j(W-1)]`.

The bands for `0 <= j < L` are disjoint: the upper endpoint for `j` is strictly below `(j+1)v+1`, since `M+j(W-1)<v`. Therefore

`U-m` is the disjoint union of the `T_j`.

The existence assumption on `m` is not automatic for composite steps. Equivalently, the congruences require the usual pairwise compatibility
`b_d = b_e (mod gcd(d,e))` for every `d,e`; the proof below does not use more than actual existence.

## Collision lemma

For `j >= 1`, let `C_j` be the number of unordered pairs of distinct steps whose values in `T_j` collide. Orient each collision by writing `d' = d + Delta > d`. Equality gives

`j*Delta = b_d - b_(d+Delta)`.

Since both residues are in `{1,...,M}`, this implies

`0 < Delta < M/j`.

In particular, the endpoint `Delta=M/j` cannot be a collision; enlarging to a non-strict range in an upper bound is harmless.

Define the finite-difference polynomial

`F_Delta(T) = (P(T+Delta)-P(T))/Delta`.

Binomial expansion shows `F_Delta in Z[T]`; its degree is exactly `k-1` and its leading coefficient is `k*c_k`. Reducing the collision equality modulo `M` gives

`Delta (F_Delta(d)+j) = 0 (mod M)`.

Let `g = gcd(Delta,M)`. Integer divisibility cancellation, not division by a unit modulo `M`, gives

`F_Delta(d)+j = 0 (mod M/g)`.

Because `M` is squarefree, `M/g` is squarefree. At every prime `q | M/g`, the leading coefficient `k*c_k` is nonzero modulo `q` by the unit hypothesis. A degree `k-1` polynomial over the field `F_q` has at most `k-1` roots. CRT therefore gives at most

`(k-1)^(omega(M/g)) <= B`

root classes modulo `M/g`. Each such class has exactly `g` lifts modulo `M` (with the empty-modulus case interpreted as one class). Consequently, for fixed `Delta`, the number of possible integer `d` in the interval of `W` candidate steps is at most

`(W/M + 1) g B`.

This deliberately ignores whether `d` and `d+Delta` belong to `D`, and so is an upper bound.

The squarefree divisor identity gives, for any `A >= 0`,

`sum_{1 <= Delta <= A} gcd(Delta,M)
 = sum_{e|M} phi(e) floor(A/e)
 <= A S_M`.

Summing the preceding count over `1 <= Delta < M/j` yields

`C_j <= (W+M) B S_M / j`.

This is the central new derivation. It is independent of the CRT compatibility and of `m`.

## From collisions to the Hall consumer

Let `f_j(x)` be the multiplicity of `x` in the multiset `(b_d+j*d)_(d in D)`. Its ordered energy is

`E_j = sum_x f_j(x)^2 = Q + 2 C_j`.

A fiber of size `r` loses only `r-1` distinct values but contributes `choose(r,2)` collisions, so

`|T_j| >= Q-C_j
 >= Q - (W+M)B S_M/j`

for every `j >= 1`. Summing over `j=1,...,L-1` and using the disjoint bands gives

`|U| >= sum_{j=1}^{L-1}|T_j|
 >= Q(L-1) - (W+M)B S_M H_(L-1)`.

The `j=0` band is simply discarded, so no assertion about its collisions is needed. If `|U|<Q`, rearrangement gives the strict necessary condition

`Q(L-2) < (W+M)B S_M H_(L-1)`.

No exponent improvement follows from this note; it is exactly a sparsity constraint on deficient families.

## Polynomial-length consequence

Suppose now `M <= W <= n`, the fixed degree `k` is independent of `n`, every step is at most `n`, and `L >= n^epsilon`. In the intended `n`-bounded Hall setting, the band hypothesis supplies `L <= n` (as stipulated in the model). Since

`omega(M) = O(log n / log log n)`,

we have

`B S_M = (k-1)^(omega(M)) * product_{q|M}(2-1/q) = n^(o(1))`.

Because `M<=W`, the exact necessary condition sharpens to

`Q/W <= 2 B S_M H_(L-1)/(L-2) = n^(-epsilon+o(1))`.

Thus no rich prime block with `Q >= W/(2 log n)` can be deficient at polynomial `L`: its left side is only `n^{-o(1)}`, while the right side is `n^{-epsilon+o(1)}`. More generally, every deficient family in this model has the displayed precise sparsity bound. This is the requested arithmetic/Hall-dependent gate. The conclusion uses the stipulated `L<=n` only to place the polynomial-length regime in the ambient range; the inequality itself is valid without that upper bound.

The assertion is deliberately not extended to arbitrary `m`, arbitrary phase patterns, or all Hall subsets. It applies only when the full neighborhoods are represented by one fixed polynomial phase modulo one squarefree modulus, with the unit leading-difference condition and an actually realized congruence system.

## Adversarial checks and failure modes

1. **All quantifiers.** The collision lemma quantifies over every `j>=1`, every `Delta`, and every integer candidate `d`; restricting to `D` only decreases the count. The Hall conclusion quantifies over every realized `m`, not over nonexistent CRT systems.

2. **Phase compatibility.** Polynomial residues need not satisfy the congruences required by composite steps. This is why existence of `m` is a hypothesis, not a claimed consequence. Pairwise-coprime prime steps are the clean CRT case.

3. **Leading-coefficient degeneration.** The unit condition cannot be dropped from this proof. For `P(T)=T^2`, `M=2`, `Delta=j=1`, one has `F_1(T)+1=2T+2`, which vanishes on both residue classes modulo `2`, whereas `k-1=1`. A compatible concrete configuration is `v=8,W=2,L=3,D={8,9},m=62`; this illustrates failure of the root bound, not failure of the theorem, since `gcd(2,2) != 1`.

4. **Modulus division.** The argument cancels the integer gcd and works modulo `M/g`; it never assumes that `Delta` is invertible modulo `M`. The squarefree hypothesis is used both for the prime-factor root count and for the clean divisor sum/product formula.

5. **Strictness and endpoints.** Collision gives `Delta<M/j`, while replacing this by `Delta<=M/j` only enlarges the count. The strict Hall deficiency gives a strict final inequality. All `N_d` endpoints were checked above.

6. **Known quadratic CRT family.** The existing construction uses `P(T)=T^2` and an odd squarefree product `M`, so the unit condition holds. Its length is `L=n^{o(1)}`, not polynomial. The present necessary condition does not exclude it: `B=1`, `S_M=n^{o(1)}`, and the harmonic factor can absorb the subpolynomial length. Therefore this result is compatible with, rather than a refutation of, the known CRT obstruction.

## Exact remaining structural gap

The fixed-degree polynomial assumption by itself is not enough for a general theorem. The proof needs a uniform bound on roots of every finite-difference polynomial after cancellation at every prime dividing the residual modulus. A phase family may have coefficient heights depending on `n`, non-squarefree moduli, or leading coefficients vanishing modulo many primes; these cases require a separate bad-prime analysis and are not covered here. Nor does the argument show that an arbitrary deficient Hall subset admits a single polynomial-phase representation.

Accordingly, the validated statement is: **within the explicit squarefree, unit-leading-coefficient polynomial CRT model, polynomial-length deficiency forces `Q/W <= n^{-epsilon+o(1)}` and rules out rich blocks.** The unresolved question is whether every relevant fixed-degree phase or every Hall subset can be reduced to this model. No such reduction is claimed.

## Evidence classification

* **Sourced:** the local progression-union framework and the quadratic CRT compression/prime-block/CRT-neighborhood construction in Chen--Korsky, Sections 2 and 5; the previously recorded subpolynomial quadratic family.
* **Prose-proved here:** boundary verification, band disjointness, finite-difference root count, gcd cancellation, divisor sum, collision energy, Hall deficiency inequality, and the polynomial-length sparsity consequence.
* **Not Lean-checked:** this is a mathematical handoff, not a formal proof artifact.
* **Not established:** extension to arbitrary phases, arbitrary composite CRT systems without realized compatibility, all Hall subsets, or any full solution to Problem 711.
