# Prime-power phase sparsity: repeated-prime extension of the polynomial sieve

## Verdict and scope

**AUTHOR-validated, pending independent review (prose-checked; not Lean-checked).** The squarefree hypothesis in `Plans/Erdos711PolynomialBadPrimeSieve.md` can be removed for the fixed-degree, canonical polynomial full-neighborhood model, at the cost of two explicit repeated-prime factors:

* `E(M)=M/rad(M)` in the interval-class count; and
* `S_M=sum_{e|M} phi(e)/e = prod_{q^a||M}(1+a(1-1/q))` in the gcd summation.

The resulting Hall consumer is quantitative, but it is **not** an all-moduli density theorem and gives no all-integer Hall reduction or #711 exponent gain. It is a restricted-model finite extension. The source comparison below is a derived adaptation of Chen--Korsky Section 5, not a theorem literally stated there.

## Contract

Fix `k>=2`, `M>=2`, and positive integers `v,W,L` with `L>=3`, and a polynomial `P in Z[T]` of degree at most `k`, with unrestricted coefficient height (including constant, affine, and zero polynomials). Let `D` be a nonempty set of distinct integers in `[v,v+W)`, `Q=|D|`, and let `b_d` be the canonical representative in `{1,...,M}` of `P(d) mod M`. Assume `M+(L-1)W<v` and assume an actual `m>=0` realizing `m=-b_d mod d` for every `d in D`.

Put `N_d={m+b_d+j*d:0<=j<L}`. Let

`E(M)=M/rad(M)`,

`R=prod {q : q|M, q>k, deg(P mod q)<=1}`,

and let `a1` be the integer coefficient of `T` in `P`. Call `j` in `{1,...,L-1}` good when `gcd(j+a1,R)=1`, and write `G` for the number of good indices. Define

`S_M=sum_{e|M} phi(e)/e = prod_{q^a||M} (1+a(1-1/q))`.

Then

`|union_{d in D} N_d| >= Q*G - (W+M)*k^(omega(M))*E(M)*S_M*H_(L-1)`,

where `H_r=sum_{j=1}^r 1/j`. Also

`G >= (L-1)*phi(R)/R - 2^(omega(R))`,

and `R=1` gives the exact value `G=L-1`. Consequently, strict deficiency `|union N_d|<Q` implies

`Q*(G-1) < (W+M)*k^(omega(M))*E(M)*S_M*H_(L-1)`.

This is the required quantitative Hall consumer.

## Proof of the repeated-prime cost

The band argument is unchanged. The sets `T_j={b_d+j*d:d in D}` lie in pairwise disjoint bands because `M+(L-1)W<v`; the displayed `N_d` are exactly the multiples of `d` in the relevant interval, using the assumed realization of `m`. Thus it suffices to bound collisions inside each positive band.

If `d'=d+Delta` and `T_j` collides, then `j*Delta=b_d-b_{d'}`, hence `0<Delta<M/j`. Since `b_x=P(x) mod M`, with the integer polynomial

`F_Delta(T)=(P(T+Delta)-P(T))/Delta`,

one has `F_Delta(d)+j=0 mod M/g`, where `g=gcd(Delta,M)`. This is integer gcd cancellation, not division by a unit. A prime `q` dividing `Delta` **can remain** in `M/g` (for example, `M=q^3, Delta=q` gives `M/g=q^2`); the argument must therefore work at the retained prime power, and it does.

For each `q|M/g`: if `q<=k`, there are at most `q<=k` roots, even in the identically-zero case. If `q>k` and `deg(P mod q)=r>=2`, exact integral division first gives `F_Delta mod q` degree `r-1` with leading coefficient `r*c_r`, which is nonzero because `q>k>=r`; this remains true even when `q` divides `Delta`, because `F_Delta` was formed by exact integral division before reduction. If `deg(P mod q)<=1`, then `F_Delta=a1 mod q`, and goodness makes `a1+j` nonzero. Hence there are at most `k` roots modulo every retained prime.

For a retained prime power `q^a||M/g`, each root modulo `q` has at most `q^(a-1)` lifts, with no Hensel nonsingularity assumption. CRT therefore gives at most

`k^(omega(M/g))*prod_{q^a||M/g}q^(a-1) <= k^(omega(M))*E(M)`

root classes modulo `M/g`. A root class modulo `M/g` contains at most `W/(M/g)+1 = W*g/M+1` candidate integers in the interval for `d`. Thus the collision candidates for fixed `Delta` are at most

`k^(omega(M))*E(M)*(W+M)*g/M`.

Finally, for every real `A>=0`,

`sum_{1<=Delta<A} gcd(Delta,M) <= A*sum_{e|M}phi(e)/e = A*S_M`,

by `gcd(Delta,M)=sum_{e|gcd(Delta,M)}phi(e)` and counting positive multiples of `e`. Taking `A=M/j` gives the per-band collision bound

`C_j <= (W+M)*k^(omega(M))*E(M)*S_M/j`.

Since a fiber of multiplicity `r` loses only `r-1` values but contributes `choose(r,2)` collisions, `|T_j|>=Q-C_j`. Summing good bands and using disjointness proves the displayed union bound. Inclusion--exclusion on the divisors of `R` proves the estimate for `G`, including the shifted-endpoint error `2^(omega(R))`.

## Uniform consumer and its limitation

If additionally `M<=W<=n`, all steps are at most `n`, `k` is fixed, and `L>=n^epsilon`, then `L<=n` follows directly from the hypotheses: `W>=1`, `D` is nonempty, so `v<=n`, while `M+(L-1)W<v` implies `L-1<v<=n`. Therefore `H_(L-1)=O(log n)` without an informal 'intended regime' qualification. The elementary uniform estimates give

`k^(omega(M))*E(M)*S_M*H_(L-1) <= n^(rho+o(1))`

whenever `E(M)<=n^rho`, while inclusion--exclusion gives

`G >= n^(epsilon-o(1))`.

Deficiency therefore forces

`Q/W <= n^(rho-epsilon+o(1))`.

This is useful only when `rho<epsilon`; if `E(M)=n^{o(1)}`, it recovers decay. It is not uniform density decay over all moduli, and is not an all-moduli #711 gain.

## Nonsquarefree sourced check (derived adaptation)

Use the Chen--Korsky quadratic family from `/home/exedev/p/erdos711-restart-20261009/sources/ChenKorsky-2607.26450.tex`, Section 5, with `P(T)=T^2`. If `Q0` is the source product of the first `s` odd primes (including `3`), replace its phase modulus by

`M=3*Q0=9*prod_{q|Q0,q>3}q`.

Modulo `9`, `d^2+j*d` has exactly four possible values (complete the square since `2` is invertible), versus two modulo `3`; CRT therefore changes the source compression density from `delta` to `delta_new=(2/3)*delta=2*A/(3*2^s)`. Keep the source prime block, `K`, and `W` (renaming the source interval length to `W`). Since `M=3Q0=o(W)` and the prime block is at scale `n`, the source band inequalities still hold for large `n`, and all source primes are coprime to `M`. CRT still supplies the actual `m`. The source estimate becomes

`|T| <= 3*K^2*W*delta_new < Q`,

because it is `2/3` of the already strict source upper bound; hence this is an actual nonsquarefree deficient family, not merely an old witness with a changed label. Here `E(M)=3`, while the factor at `3` in `S_M` is `1+2(1-1/3)=7/3` (the squarefree factor was `5/3`). Also `R=1`, so `G=K-1` exactly.

For finite-sieve compatibility, the source relation `K^2<=2^s/(16*A*log n)`, with `A=prod_{q|Q0}(1+1/q)`, remains available and `delta_new=2*A/(3*2^s)`. The new error is explicitly

`Err=(W+M)*2^s*3*S_M*H_(K-1)`,

where `S_M=(7/3)*prod_{q|Q0,q>3}(2-1/q)`. Since the source block has `Q<=W` and `M=o(W)`, using `W+M>=W` and the displayed source relation gives

`Err/Q >= 48*A*S_M*K^2*log n*H_(K-1)`.

This is eventually larger than `G-1=K-2`, so the finite sieve error is quantitatively compatible with the source deficiency. The source actual-union count and CRT realization remain required; this comparison does not replace them. It does **not** show that the consumer rules out the construction.

## Remaining gaps and representation risks

The result remains **AUTHOR-validated pending independent review**. It assumes one fixed polynomial phase, canonical representatives, the band inequality, and an actually realized congruence system. It does not cover arbitrary Hall subsets, arbitrary phase patterns, all moduli with a decay conclusion, or the central arbitrary-integer #711 problem. The source adaptation is checked from its explicit compression and CRT inequalities, but it is not a literal source theorem and should not be cited as one. Root counts are intentionally non-sharp. The argument is not Lean-checked.

**Strongest author-validated claim pending independent review:** repeated prime powers cost at most `E(M)` in the root-lift/class count and replace the squarefree sieve factor by `S_M`; under `E(M)<=n^rho`, a deficient polynomial full-neighborhood family with `L>=n^epsilon` has `Q/W<=n^(rho-epsilon+o(1))`, with the explicit nonsquarefree quadratic source family above showing compatibility and non-vacuity.
