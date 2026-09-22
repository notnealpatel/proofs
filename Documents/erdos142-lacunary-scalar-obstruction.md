# A lacunary scalar obstruction for Erdős #142

## Status and the target

All logarithms are natural unless a subscript is displayed.

Write the desired assertion exactly as
\[
 P:\quad \exists C>0\ \exists\eta\in(0,\sqrt2-1]\ \exists N_0\ \forall N\geq N_0,
 \qquad r_3(N^2)\leq C r_3(N)^{1+\eta}N^{1-\eta}.
\]
Here this note is a *synthetic derivability obstruction*: it is not a counterexample to actual Roth numbers and is not a solution of Erdős #142. We construct a positive real comparison function on the integers having a broad package of accepted scalar behaviors, but violating every inequality of the shape in \(P\), even with arbitrary \(\eta>0\). Thus those scalar behaviors, even used simultaneously, do not imply \(P\); a finite/synthetic failure does not disprove \(P\). The real-valued \(R\) is not an actual extremal function, and no set construction is claimed to realize it.

## The tangent envelope

Put \(a=1/6\), choose
\[
 1<p<5,\qquad T_0>\max(1,2^{1/(p-1)}),\qquad T_{k+1}=T_k^p,
\]
and define
\[
 \ell_T(s)=(1-a)T^a+aT^{a-1}s,\quad
 f(s)=\inf_{k\geq0}\ell_{T_k}(s),\quad F(s)=f(s)-f(0).
\]
Every \(\ell_T\) is the tangent to \(s^a\) at \(T\), so it majorizes \(s^a\). In particular \(f(0)=(1-a)T_0^a\) and \(F(0)=0\).

The intersection of adjacent tangents is
\[
 S_k=\frac{1-a}{a}\,\frac{T_{k+1}^a-T_k^a}{T_k^{a-1}-T_{k+1}^{a-1}}.
\]
If \(r_k=(T_{k+1}/T_k)^{1/6}\), direct cancellation gives
\[
 S_k=\frac{5T_kr_k^5}{1+r_k+r_k^2+r_k^3+r_k^4},
 \qquad T_kr_k\leq S_k\leq5T_kr_k. \tag{1}
\]
For completeness, let \(g(r)=5r^5/(1+r+\cdots+r^4)\). Its logarithmic derivative is positive (the weighted mean of the exponents \(0,\ldots,4\) is less than \(5\)), so \(g\) is increasing. Since \(r_{k+1}=r_k^p>r_k\),
\[
 \frac{S_{k+1}}{S_k}=T_k^{p-1}\frac{g(r_{k+1})}{g(r_k)}>T_k^{p-1}>2. \tag{2}
\]
The intercepts of the lines are increasing and their slopes are decreasing. Together with the increasing adjacent intersections (2), this ordering rules out a skipped tangent: \(f=\ell_{T_{k+1}}\) on \([S_k,S_{k+1}]\). Consequently \(f\) is increasing and concave (an infimum of affine functions), and \(f\geq s^a\).

Here is the quantitative size check. On \([S_k,S_{k+1}]\), use the line with parameter \(T_{k+1}\). From (1),
\[
 \frac{T_{k+1}^a}{\sqrt{S_k}}\ll T_k^{(p-5)/12},
 \qquad
 aT_{k+1}^{a-1}\sqrt{S_{k+1}}
 \ll T_{k+1}^{(p-5)/12}.
\]
The first controls the intercept and the second controls the slope term, since \(s/\sqrt s=\sqrt s\) is increasing. The condition \(p\leq5\) would make both bounds uniform, while the chosen strict condition \(p<5\) makes them decay. Hence, eventually,
\[
 s^{1/6}-f(0)\leq F(s)\leq C\sqrt{s}. \tag{3}
\]
The upper bound is only an eventual bound; no claim \(C\sqrt s\) at \(s=0\) is intended. It follows that \(F(s)\to\infty\) and \(F(s)=o(s)\). Also, since \(2S_k<S_{k+1}\), both points lie on the same tangent and
\[
 F(2S_k)-F(S_k)=aT_{k+1}^{a-1}S_k.
\]
After division by \(S_k^a\), this is \(a(S_k/T_{k+1})^{1-a}\to0\), because
\[
 S_k/T_{k+1}\ll T_k^{-5(p-1)/6}.
\]
The lower bound in (3) then proves
\[
 0\leq\frac{F(2S_k)-F(S_k)}{F(S_k)}\longrightarrow0. \tag{4}
\]
Thus the pointwise lower power is \(s^{1/6}-f(0)\), and the corresponding Matuszewska discussion has exponent \(1/6\): nevertheless, for every fixed \(\lambda>1\), eventually \(\lambda S_k<S_{k+1}\) and the same tangent calculation gives \(F(\lambda S_k)/F(S_k)\to1\). In the O-regular/Matuszewska language, this construction still has lower scaling index zero despite its pointwise \(1/6\)-power lower bound.

## The integer comparison function

Define, for integer \(N\geq1\),
\[
 R(N)=N\exp\{-F(\log N)\}.
\]
It is positive and \(R(1)=1\). Every tangent slope is at most \(aT_0^{a-1}<1\), so \(s-F(s)\) is increasing; therefore \(R\) is increasing. The global slope bound, for \(s>0\),
\[
 0\leq F(s)\leq aT_0^{a-1}s<s
\]
together with \(F(0)=0\) gives \(1\leq R(N)\leq N\) globally; the limits remain eventual/asymptotic:
\[
 R(N)/N\to0,\qquad \frac{\log R(N)}{\log N}\to1. \tag{5}
\]
The deficit has the stronger model envelope
\[
 c(\log N)^{1/6}\leq F(\log N)\leq C\sqrt{\log N} \tag{6}
\]
eventually. This lower model envelope is stronger than Raghavan's actual external bound, which has the factor \(/\log\log N\); it is therefore a synthetic model choice, not a claim about actual Roth numbers. The names refer to the corresponding sides for actual Roth bounds, not to an assertion that \(R\) is an extremal function.

A nonnegative increasing concave function vanishing at zero is subadditive: its decreasing increments give \(F(x+y)-F(x)\leq F(y)-F(0)\). Thus the following are exact for every indicated integer:
\[
 R(N^2)\leq NR(N),\qquad R(N)^2\leq R(N^2)\quad(\text{hence }R(N)^2\leq2R(N^2)). \tag{7}
\]
For the useful shifted product relation, put \(x=\log N\), \(y=\log M\), and \(h=\log(2M-1)\geq y\). Subadditivity gives \(F(x+h)\leq F(x)+F(h)\), while monotonicity of \(u-F(u)\) gives \(F(h)\leq F(y)+h-y\). Exponentiating yields
\[
 R(N)R(M)\leq R\bigl(N(2M-1)\bigr). \tag{8}
\]

## Failure of every fixed-power inequality

Let \(n_k=\lfloor e^{S_k}\rfloor\). Then
\[
 \log n_k-S_k=O(e^{-S_k}).
\]
The global tangent-slope bound makes \(F\) Lipschitz, so (4) is stable under this perturbation and gives
\[
 \frac{F(2\log n_k)}{F(\log n_k)}\longrightarrow1. \tag{9}
\]
For any \(C_0>0\) and any \(\eta>0\), the proposed comparison inequality
\[
 R(N^2)\leq C_0R(N)^{1+\eta}N^{1-\eta}
\]
is equivalent to
\[
 F(2\log N)\geq(1+\eta)F(\log N)-\log C_0. \tag{10}
\]
Equation (9), together with \(F(\log n_k)\to\infty\), contradicts (10) along \(n_k\). This is an explicit falsifying sequence, not a finite computation.

## Audit and scope

1. **Quantifiers/status.** \(P\) has one fixed \(\eta\), one fixed \(C\), and a discarded finite initial range. The model defeats all such choices; it does not assert anything about actual \(r_3\).
2. **Additive structure represented vs absent.** \(R\) has no sets, 3-term progressions, digit fibers, or carries. The obstruction therefore identifies exactly what scalar information cannot see.
3. **Implication for \(X/\lambda\).** For this model, \(\lambda_R(N)=\log(N/R(N))=F(\log N)\) and \(X_R(N)=\log(R(N)^2/R(N^2))=F(2\log N)-2F(\log N)\). By subadditivity, \(F(2\log N)\leq2F(\log N)\), so \(X_R(N)\leq0\). Scalar control of these quantities, absent an additive lemma, does not force the fixed-power lower bound for \(\lambda_R(N^2)\).
4. **Optimized \(p<5\) and \(\eta\).** The cutoff \(p<5\) is exactly the square-root upper-envelope calculation; failure holds for every \(\eta>0\), so the permitted \(\sqrt2-1\) range is irrelevant to the obstruction.
5. **Model behavior.** The model is increasing, sublinear, has (6), satisfies the exact relations (7)--(8), and still has lacunary near-doubling plateaux.
6. **Falsifier/termination.** The sequence \(n_k\) is the termination certificate: (9) directly falsifies (10), with no search or unverified asymptotic guess.
7. **Exact route exclusion.** Any derivation using only the listed scalar monotonicity, concavity/subadditivity, envelopes, and exact relations (including their simultaneous use) is insufficient for \(P\). A genuinely additive input must enter.
8. **Minimal future Lean artifact.** A minimal formalization would prove the tangent-envelope bounds, subadditivity, the sampled integer perturbation, and the quantified failure of (10); it need not formalize any claim about actual Roth numbers.

For context, Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v2](https://arxiv.org/abs/2603.27045), Theorem 1.4, gives for odd \(N>1\) the external bound used for the actual comparison. Passing to \(N+1\) for even \(N\), using monotonicity and absorbing the factor \((N+1)/N\) and comparable logarithms, gives eventually for all \(N\)
\[
 \lambda(N)\geq c\frac{(\log N)^{1/6}}{\log\log N},\qquad
 \log\lambda(N)\geq\tfrac16\log\log N-\log\log\log N+O(1).
\]
This actual external envelope is weaker than the model envelope (6), whose stronger pure power is synthetic. Matuszewska (1964), [doi:10.4064/sm-24-3-271-279](https://doi.org/10.4064/sm-24-3-271-279), and Bingham--Goldie--Teugels, *Regular Variation*, §2.2, Proposition 2.2.1, provide the O-regular/Matuszewska context. No audited source supplied this exact tangent-envelope Roth-route obstruction; that is not a claim that none exists. Flooring \(R\) is optional intuition only: the exact relations above are not claimed after flooring.
