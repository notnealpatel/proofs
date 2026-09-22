# Erdős #142: an actual stretched-exponential comparison window

Write
\[
 r_3(N)=\max\{|A|:A\subseteq\{1,\ldots,N\},\ A\text{ has no non-trivial 3-term AP}\},
 \qquad \lambda(N)=\log\frac{N}{r_3(N)},
\]
and put \(L=\log N\) (natural logarithms). The following is an unconditional comparison-class exclusion, not an asymptotic formula.

## The two inputs

Bloom--Sisask, *An improvement to the Kelley--Meka bounds on three-term arithmetic progressions*, [arXiv:2309.02353](https://arxiv.org/abs/2309.02353), Theorem 1, proves that for some \(c>0\), eventually
\[
 r_3(N)\leq N\exp(-cL^{1/9}).
\]
Taking logarithms gives the lower deficit bound
\[
 \lambda(N)\geq cL^{1/9}\qquad(N\text{ sufficiently large}). \tag{B--S}
\]

The repository-accepted Behrend/EHPS-shaped construction is
`Proofs/Erdos/Erdos142/TorusAsymptoticLowerBound.lean`, theorem
`Erdos142.eventually_rothNumberNat_lower_bound`: for every fixed slack \(\delta>0\), eventually
\[
 N\exp\!\bigl(-(C_\delta)\sqrt L\bigr)\leq r_3(N).
\]
Thus \(\lambda(N)=O(\sqrt L)\). Its construction provenance is Elsholtz--Hunter--Proske--Sauermann, *Improving Behrend's construction*, arXiv:2406.12290v1, Proposition 2.2 and §5, Definition 5.1.

## Consequences, with the ratio signs made explicit

1. First take the natural stretched-exponential range \(0<\gamma<1/9\). From (B--S),
\[
 \frac{\lambda(N)}{L^\gamma}\geq cL^{1/9-\gamma}\longrightarrow+\infty.
\]
The same inequality proves the stated conclusion for **every real** \(\gamma<1/9\), including \(\gamma\leq0\): for large \(N\), \(L>0\), and \(1/9-\gamma>0\), so the denominator is positive and the right side diverges.

2. Let \(a>0\) and \(0<\gamma<1/9\), and set
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
because \(A\log\log N=A\log L=o(L^{1/9})\), while (B--S) gives \(\lambda(N)\geq cL^{1/9}\). This also excludes every fixed logarithmic-power comparison.

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

Thus present bounds exclude only the pure fixed-coefficient natural stretched-exponential candidates with exponent outside \([1/9,1/2]\). They do **not** validate candidates inside that window, classify endpoint coefficients, or give an asymptotic formula or a solution of canonical Erdős #142. The modality is mathematically unconditional given the published Bloom--Sisask theorem, but this comparison is not Lean-formalized. Existing `Proofs/Erdos/Erdos142/StretchedExponentialObstruction.lean` formalizes the \(\gamma>1/2\) half only (in particular, `tendsto_rothLogDeficit_div_rpow_zero`).
