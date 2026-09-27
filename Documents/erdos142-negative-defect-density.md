# Positive lower density of negative square defects on a tower

Let
\[
r(N)=r_3(N)=\max\{|A|:A\subseteq[1,N]\text{ contains no nontrivial 3-term arithmetic progression}\},
\qquad \lambda(N)=\log\frac{N}{r(N)},
\]
and put
\[
X(N)=\lambda(N^2)-2\lambda(N).
\]
All logarithms are natural. Fix an integer \(M\ge3\), let
\[
N_k=M^{2^k},\qquad a_k=\lambda(N_k)\quad(k\ge0).
\]
This note proves the following unconditional tower-index density statement: for every
\(0<\beta<2-\sqrt2\), with
\[
t=2-\beta>\sqrt2,
\qquad
\delta_\beta=1-\frac{\log\sqrt2}{\log(2-\beta)}>0,
\]
we have
\[
\boxed{\displaystyle
\liminf_{K\to\infty}\frac1K\#\{0\le k<K:X(N_k)\le-\beta\lambda(N_k)\}\ge\delta_\beta.}
\tag{1}
\]
For each fixed \(H>0\), the same lower bound holds with the condition
\(X(N_k)\le-H\).

## Inputs and monotonicity along the tower

First, partition \([1,N^2]\) into the \(N\) consecutive intervals
\[
[1,N], [N+1,2N],\ldots,[(N-1)N+1,N^2].
\]
The intersection of any progression-free set with each interval is progression-free, and translating that interval to \([1,N]\) preserves this property. Each intersection therefore has size at most \(r(N)\). Summing over the partition gives
\[
r(N^2)\le N r(N).
\]
Consequently
\[
\lambda(N^2)=\log\frac{N^2}{r(N^2)}
\ge\log\frac{N^2}{N r(N)}=\lambda(N),
\]
so, because \(N_{k+1}=N_k^2\),
\[
a_{k+1}\ge a_k\quad\text{for every }k.\tag{2}
\]
This is only the needed comparison on successive square scales; no arbitrary monotonicity of \(\lambda(N)\) is being asserted.

Also \(a_0>0\). Indeed, when \(M\ge3\), the full interval \([1,M]\) contains the nontrivial progression \(1,2,3\), so \(r(M)<M\), and hence \(\lambda(M)=\log(M/r(M))>0\).

Use the accepted EHPS/Behrend construction input
\[
\lambda(N)=O(\sqrt{\log N}).\tag{3}
\]
Along the fixed tower, \(\log N_K=2^K\log M\), so (3) gives an eventual bound \(a_K\le C_M2^{K/2}\) for some finite constant. Increase that constant, if necessary, to cover the finitely many earlier values and to be at least \(a_0\). Thus there is \(A_M\ge a_0>0\) such that
\[
a_K\le A_M2^{K/2}\quad\text{for every }K\ge0.\tag{4}
\]
Only this upper envelope from the construction is used below.

## Product-of-ratios density argument

Fix \(0<\beta<2-\sqrt2\), set \(t=2-\beta\), and let
\[
s_K=\#\{0\le k<K:a_{k+1}\le t a_k\}.
\]
All ratios \(a_{k+1}/a_k\) are defined and at least \(1\), by \(a_k\ge a_0>0\) and (2). At each of the \(s_K\) counted indices the ratio is at least \(1\). At every other index it is strictly greater than \(t\), and in particular at least \(t\). Multiplying all \(K\) ratios and weakening the resulting strict inequality if needed gives
\[
t^{K-s_K}\le\prod_{k=0}^{K-1}\frac{a_{k+1}}{a_k}
=\frac{a_K}{a_0}
\le\frac{A_M}{a_0}2^{K/2}.\tag{5}
\]
For \(K\ge1\), taking logarithms (with \(\log t>0\)) and rearranging yields the explicit estimate
\[
\frac{s_K}{K}\ge
1-\frac{\log\sqrt2}{\log t}
-\frac{\log(A_M/a_0)}{K\log t}.
\tag{6}
\]
Since \(t>\sqrt2\), the limiting lower bound in (6) is precisely
\(\delta_\beta>0\).

For every counted index, use \(N_k^2=N_{k+1}\) to compute
\[
X(N_k)=a_{k+1}-2a_k\le(t-2)a_k=-\beta a_k.
\tag{7}
\]
Thus the set counted by \(s_K\) is contained in the set in (1). Combining this inclusion with (6) and taking the lower limit proves (1).

Roth's theorem gives \(r(N)/N\to0\), and hence \(\lambda(N)\to\infty\). Since \(N_k\to\infty\), for each fixed \(H>0\) there is an index \(k_H\) such that \(a_k\ge H/\beta\) for all \(k\ge k_H\). At each counted index beyond \(k_H\), (7) implies \(X(N_k)\le-H\). Removing the at most \(k_H\) earlier indices does not change a lower density in the index variable. This proves the stated fixed-\(H\) version with the same bound \(\delta_\beta\).

## Formal endpoint corollary: half-density of negative defects

The formal development now also proves that for every fixed \(M\ge3\) and every real \(\delta<1/2\), eventually
\[
\delta K\le\#\{0\le k<K:X(N_k)<0\},
\qquad
\delta K\le\#\{0\le k<K:X(N_k)\le0\}.
\]
Thus the strict-negative set has tower-index lower density at least \(1/2\). These are the public Lean endpoints `Erdos142.eventually_card_squareScaleDefect_neg` and `Erdos142.eventually_card_squareScaleDefect_nonpos` in `Proofs/Erdos/Erdos142/SquareScaleNegativeDensity.lean`.

The proof chooses an admissible \(\beta>0\) from the existing density curve so that \(\delta<\delta_\beta\), then applies the earlier theorem. It does not apply that source theorem at \(\beta=0\): since \(\lambda(N_k)>0\) at every tower scale, the resulting bound \(X(N_k)\le-\beta\lambda(N_k)\) implies strict negativity. The nonpositive statement follows by inclusion.

This is a tower-index lower-density result, not integer density or exact density. The eventual-cardinality statements require \(\delta<1/2\); they do not assert the bound at \(\delta=1/2\). They give no endpoint magnitude, no overlap with the P-shaped good scales, no bounded gaps, and no conclusion \(D\to0\) or asymptotic formula.

## Separate corollary using an external quantitative input

The preceding density theorem does not use Raghavan's result. The following strengthening does. By Theorem 1.4 of Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v3](https://arxiv.org/abs/2603.27045v3), there are absolute constants \(c_R>0\) and \(N_0\) such that for every \(N\ge N_0\),
\[
\lambda(N)\ge c_R\left(\frac{\log N}{\log\log N}\right)^{1/6}.
\tag{8}
\]
This is an external preprint input, not part of the unconditional deduction above. The expression is well-defined and positive on this tower: \(N_k\ge M\ge3>e\), so \(\log\log N_k>0\). Since \(N_k\to\infty\), (8) holds for all sufficiently large tower indices.

For each fixed admissible \(\beta\), every counted index sufficiently far along the tower therefore satisfies, by (7) and (8),
\[
X(N_k)\le-\beta c_R\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}.
\]
Deleting the finite initial segment leaves the lower-density bound unchanged. In particular,
\[
\boxed{\displaystyle
\liminf_{K\to\infty}\frac1K\#\left\{0\le k<K:
X(N_k)\le-\beta c_R\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}\right\}
\ge\delta_\beta.}
\tag{9}
\]
The exact identity
\[
-X(N)=\log\frac{r(N^2)}{r(N)^2}
\]
shows that (9) is equivalently the same lower-density assertion with
\[
\frac{r(N_k^2)}{r(N_k)^2}\ge
\exp\!\left(\beta c_R\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}\right).
\]
For each fixed \(\beta\), this upgrades the already accepted
`erdos142-raghavan-square-defect-rate.md` conclusion from mere frequency to positive lower density at its corresponding negative-defect coefficient. This is a repository-level strengthening, not a claim of global novelty.

## Status and scope

The density results are kernel checked in `Proofs/Erdos/Erdos142/SquareScaleNegativeDensity.lean`, imported by `Proofs/Erdos.lean`. The theorem list is `Erdos142.eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit` and `Erdos142.eventually_card_squareScaleDefect_le_neg_const` (the \(\delta_\beta\) curve and fixed-\(H\) bound), together with the endpoint corollaries `Erdos142.eventually_card_squareScaleDefect_neg` and `Erdos142.eventually_card_squareScaleDefect_nonpos`. For every fixed \(M\ge3\) and every real \(\delta<1/2\), these last endpoints give eventually at least \(\delta K\) strict-negative, respectively nonpositive, defects among \(k<K\). The focused module and full `Erdos` umbrella builds succeeded. The exact axiom audit is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The proof chooses \(\beta>0\) with \(\delta<\delta_\beta\), does not apply the source theorem at \(\beta=0\), and uses positivity of \(\lambda\) on every tower scale. The density argument uses accepted Roth and EHPS/Behrend inputs, not Raghavan's preprint.

Issue [#57](https://github.com/thatnealpatel/proofs/issues/57) tracks independent evaluation of soundness and global novelty. A scoped literature review found the growth-budget lemma standard and no explicit published Roth-number application; the status remains a repository-level consequence, with no global novelty claim. The issue is not external certification of novelty.

The stronger quantitative-rate conclusion (8)–(9) remains a prose combination, not a Lean theorem: it combines this density result with Theorem 1.4 of the external v3 preprint cited above. It is also recorded separately in [`erdos142-raghavan-square-defect-rate.md`](erdos142-raghavan-square-defect-rate.md). In particular, for each fixed admissible \(\beta\), the external lower bound on \(\lambda\) holds eventually on the same tower, so deleting a finite initial segment preserves the lower density while yielding the explicit growing magnitude in (9).

The half-density conclusion is in the tower index \(k\), not density among integers \(N\), and is only a lower bound: it asserts neither exact density nor the eventual-cardinality inequality at \(\delta=1/2\). It gives no magnitude for \(X\) at the half-density endpoint. Existing positive-density P-shaped good-scale results bound \(X\) from below on their good indices (for example, a ratio growth condition gives \(X(N_k)\ge-(2-q)\lambda(N_k)\)); no overlap or common set with the negative-defect indices is established, and no bounded gaps follow. The \(\delta_\beta\) theorem is still stated for each fixed \(\beta\), without a common set as \(\beta\) varies; its parameter endpoint \(\beta=2-\sqrt2\) remains excluded. None of these results proves eventual P, \(D(N)\to0\), an asymptotic formula, or two-sided oscillation.
