# Erdős #142: an actual stretched-exponential comparison window

Write
\[
 r_3(N)=\max\{|A|:A\subseteq\{1,\ldots,N\},\ A\text{ has no non-trivial 3-term AP}\},
 \qquad \lambda(N)=\log\frac{N}{r_3(N)},
\]
and put \(L=\log N\) (natural logarithms). The following is an unconditional comparison-class exclusion, not an asymptotic formula.

## The external input

Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v3 (15 May 2026)](https://arxiv.org/abs/2603.27045v3), Theorem 1.4, is a preprint and external/non-Lean input. It proves for all \(N\), with some \(c>0\),
\[
 r_3(N)\leq N\exp\!\left(-c\,(\log N)^{1/6}(\log\log N)^{-1/6}\right).
\]
Thus, eventually for every \(N\),
\[
 \lambda(N)\geq c\,\frac{L^{1/6}}{(\log L)^{1/6}},
 \qquad
 \log\lambda(N)\geq \tfrac16\log\log N-\tfrac16\log\log\log N+O(1). \tag{R}
\]
This is not the stronger pure bound \(\lambda(N)\geq c(\log N)^{1/6}\). The cited theorem/source statement is used here rather than the stale abstract, which retains the older loglog exponent.

The repository-accepted Behrend/EHPS-shaped construction is
`Proofs/Erdos/Erdos142/TorusAsymptoticLowerBound.lean`, theorem
`Erdos142.eventually_rothNumberNat_lower_bound`: for every fixed slack \(\delta>0\), eventually
\[
 N\exp\!\bigl(-(C_\delta)\sqrt L\bigr)\leq r_3(N).
\]
Thus \(\lambda(N)=O(\sqrt L)\). Its construction provenance is Elsholtz--Hunter--Proske--Sauermann, *Improving Behrend's construction*, arXiv:2406.12290v1, Proposition 2.2 and §5, Definition 5.1.

## Consequences, with the ratio signs made explicit

1. First take the natural stretched-exponential range \(\gamma<1/6\). From (R), for every fixed real \(\gamma<1/6\),
\[
 \frac{\lambda(N)}{L^\gamma}
 \geq c\,\frac{L^{1/6-\gamma}}{(\log L)^{1/6}}
 \longrightarrow+\infty.
\]
For large \(N\), \(L>0\), so this also covers \(\gamma\leq0\).

2. Let \(a>0\) and \(\gamma<1/6\), and set
\[
 f_{a,\gamma}(N)=N\exp(-aL^\gamma).
\]
Since \(r_3(N)/N=\exp(-\lambda(N))\),
\[
 \frac{r_3(N)}{f_{a,\gamma}(N)}
 =\exp\!\left(aL^\gamma-\lambda(N)\right)
 =\exp\!\left[L^\gamma\left(a-\frac{\lambda(N)}{L^\gamma}\right)\right]
 \longrightarrow0.
\]
Hence no member of this natural fixed-coefficient family can be an asymptotic formula for \(r_3\) (its ratio is not merely non-unit; it tends to zero).

3. For every fixed \(A>0\),
\[
 \frac{r_3(N)}{N/L^A}=\exp\!\left(A\log L-\lambda(N)\right)\longrightarrow0,
\]
because \(A\log L=o(L^{1/6}/\log L)\), while (R) gives the displayed lower bound for \(\lambda(N)\). This also excludes every fixed logarithmic-power comparison.

4. Conversely, the construction bound gives, for every \(\gamma>1/2\),
\[
 0\leq\frac{\lambda(N)}{L^\gamma}\leq C_\delta L^{1/2-\gamma}\longrightarrow0.
\]
Therefore, for \(a>0\),
\[
 \frac{r_3(N)}{f_{a,\gamma}(N)}
 =\exp\!\left[L^\gamma\left(a-\frac{\lambda(N)}{L^\gamma}\right)\right]
 \longrightarrow+\infty,
\]
not zero: the bracket tends to \(a>0\), and \(L^\gamma\to\infty\).

Thus present bounds exclude only the pure fixed-coefficient natural stretched-exponential candidates with exponent outside \([1/6,1/2]\). The endpoint \(\gamma=1/6\) remains unresolved, as do candidates inside the window and endpoint coefficients. These statements do not prove P, give an asymptotic formula, or solve canonical Erdős #142. The Raghavan estimate is a preprint external input, not Lean-formalized; existing `Proofs/Erdos/Erdos142/StretchedExponentialObstruction.lean` formalizes only the \(\gamma>1/2\) half (in particular, `tendsto_rothLogDeficit_div_rpow_zero`).
