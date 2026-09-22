# Erdős 142: critical gain on dense and local scales

This note isolates the gain that survives the critical contraction transfer. It is a density and recurrence statement, not **P**, and makes no novelty claim. Write
\[
 r=r_3,\qquad \lambda(N)=\log\frac{N}{r(N)},\qquad m_n=r(n)^2,
\]
and, with all logarithms natural except \(\log_2\), put
\[
 w_n=\log\log(n+1)-\log\log n,
 \qquad C_n=\log_2\frac{\lambda(n^2)}{\lambda(n)}.
\]
Powers of two form arbitrarily large finite nontrivial-3-AP-free sets, so \(r_3(n)\to\infty\) and hence \(m_n=r(n)^2\to\infty\). Also \([M]\) contains a nontrivial 3-AP for every \(M\ge3\), so \(\lambda(M)>0\) there. Thus choose \(n_0\) so that \(\lambda(n),\lambda(n^2),\lambda(m_n)>0\) for \(n\ge n_0\), and define
\[
 K_n=\log_2\frac{\lambda(m_n)}{\lambda(n)}\qquad(n\ge n_0).
\]

The accepted inputs used below are the critical-contraction estimate
\[
 |\lambda(m_n)-\lambda(n^2)|=O\!\left(\sqrt{\lambda(n)}\right),                 \tag{A1}
\]
\(\lambda(n^2)\ge\lambda(n)\), and \(\lambda(n)\to\infty\); the global weighted \(C\)-identity and its density consequence; the square upper bound giving \(C_n\le1+o(1)\); the local weighted recurrence for \(C_n\); and the Raghavan-v3 lower envelope. The latter is the external preprint Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v3 (15 May 2026)](https://arxiv.org/abs/2603.27045v3), Theorem 1.4, whose all-\(N\) bound gives
\[
 \log\lambda(N)\ge \tfrac16\log\log N-\tfrac16\log\log\log N+O(1).       \tag{R}
\]
No claim below promotes this external input to a Lean theorem.

## 1. Transfer from the square scale

Let \(d_n=\lambda(m_n)-\lambda(n^2)\). From (A1), for some fixed \(B\),
\(|d_n|\le B\sqrt{\lambda(n)}\) on a tail. Since \(\lambda(n^2)\ge\lambda(n)\),
\[
 \left|\frac{d_n}{\lambda(n^2)}\right|
 \le \frac{B}{\sqrt{\lambda(n)}}\longrightarrow0.                              \tag{1}
\]
In particular, on a further tail
\(\lambda(m_n)\ge\lambda(n^2)-B\sqrt{\lambda(n)}>0\), so the logarithm defining \(K_n\) is eventually positive in its argument (and hence is defined independently of the initial choice of \(n_0\)). More precisely, using \(\log_2(1+t)=O(t)\) uniformly for \(|t|\le1/2\),
\[
 K_n-C_n
 =\log_2\left(1+\frac{d_n}{\lambda(n^2)}\right)=o(1),                 \tag{2}
\]
with the \(o(1)\) tail-uniform. Notice that this does not assert \(K_n\ge0\): the transferred quantity can be slightly negative before the error disappears.

## 2. The weighted mean

The accepted global identity is, with an immaterial finite change of initial index,
\[
 \sum_{n_0\le n\le M}w_nC_n
   =\log\lambda(M+1)+o(\log\log M).                                  \tag{3}
\]
Equation (2) transfers it to
\[
 \boxed{\displaystyle
 \sum_{n_0\le n\le M}w_nK_n
   =\log\lambda(M+1)+o(\log\log M).}                                  \tag{4}
\]
Here is the needed fixed-tail justification, rather than an unquantified termwise substitution. Given \(\varepsilon>0\), choose a fixed \(J\) so that \(|K_n-C_n|\le\varepsilon\) for \(n\ge J\). The contribution before \(J\) is a constant, while
\[
 \sum_{J\le n\le M}w_n|K_n-C_n|
 \le\varepsilon\sum_{J\le n\le M}w_n
 =\varepsilon\bigl(\log\log(M+1)+O_J(1)\bigr).
\]
First let \(M\to\infty\), then \(\varepsilon\downarrow0\), proving that the difference of the two weighted sums is \(o(\log\log M)\). This is the promised fixed-tail split.

## 3. Global lower density of genuine critical gains

Fix \(1<q<2^{1/6}\), write \(\alpha=\log_2q\), and let
\[
 E_q=\{n\ge n_0: \lambda(m_n)\ge q\lambda(n)\}=\{n\ge n_0:K_n\ge\alpha\}.
\]
By (R) and (4),
\[
 \liminf_{M\to\infty}
 \frac{\sum_{n_0\le n\le M}w_nK_n}{\log\log M}\ge\frac16.                 \tag{5}
\]
Also (2) and the accepted square upper bound give the tail-uniform estimate
\[
 K_n\le1+o(1).                                                           \tag{6}
\]
Let \(p_M\) be the relative \(w\)-weight of \(E_q\) up to \(M\). On the complement, \(K_n<\alpha\), while on \(E_q\), (6) bounds \(K_n\) above; no lower bound on \(K_n\) is needed. For each fixed tail cutoff \(J\), choose \(\varepsilon_J\downarrow0\) with \(K_n\le1+\varepsilon_J\) for \(n\ge J\), and write \(W_M=\sum_{n_0\le n\le M}w_n\). The finite prefix contributes \(O_J(1)\), so for \(M\ge J\) the literally valid split is
\[
 \frac{\sum_{n_0\le n\le M}w_nK_n}{W_M}
 \le \alpha(1-p_M)+(1+\varepsilon_J)p_M+\frac{O_J(1)}{W_M}.
\]
Since \(W_M=\log\log M+O(1)\), the last term tends to zero for fixed \(J\); take \(M\to\infty\) first and then \(J\to\infty\), combining this inequality with (5) to obtain
\[
 \boxed{\displaystyle
 \liminf_{M\to\infty}p_M\ge
 \frac{1/6-\log_2q}{1-\log_2q}.}                                      \tag{7}
\]
As \(q\downarrow1\), the displayed lower bound tends to \(1/6\). This does not claim that \(q=1\) is a good threshold at every critical scale: unlike \(C_n\), \(K_n\) can be slightly negative. At the endpoint \(q=2^{1/6}\), the bound degenerates to zero.

## 4. Local log-log windows

Fix \(\rho>3\). For all sufficiently large real \(T\) for which the endpoint sets are nonempty, define over natural numbers \(n\ge3\),
\[
 u(T)=\min\{n\in\mathbb N:n\ge3,\ \log\log n\ge T\},\qquad
 v(T)=\max\{n\in\mathbb N:n\ge3,\ \log\log n\le\rho T\}.
\]
Then \(u(T)\to\infty\), and endpoint rounding gives
\[
 W_T:=\sum_{u(T)\le n\le v(T)}w_n=(\rho-1)T+o(T),\qquad W_T>0,\quad u(T)\le v(T) \tag{8}
\]
for all sufficiently large such \(T\).
Put
\[
 A=\frac{\rho/6-1/2}{\rho-1}>0.
\]
The accepted local recurrence for \(C_n\) says
\[
 \liminf_{T\to\infty}\frac1{W_T}
 \sum_{u(T)\le n\le v(T)}w_nC_n\ge A.                              \tag{9}
\]
The transfer (2) is tail-uniform on this window, so its weighted average differs from the one in (9) by \(o(1)\). Therefore
\[
 \liminf_{T\to\infty}\frac1{W_T}
 \sum_{u(T)\le n\le v(T)}w_nK_n\ge A.                              \tag{10}
\]
For fixed \(0<c<A\), let \(p_T\) be the relative \(w\)-weight in this window of \(\{n:K_n\ge c\}\). Since \(K_n\le1+o(1)\) uniformly there, the same split as above gives
\[
 \boxed{\displaystyle
 \liminf_{T\to\infty}p_T\ge\frac{A-c}{1-c}>0.}                    \tag{11}
\]
The liminf is over all real \(T\), not merely integer windows. In particular, every sufficiently large all-real-\(T\) window contains an index with \(K_n\ge c\). This is a local positive-density assertion, not eventual validity at all indices.

## 5. Finite transfer and the defect

Suppose \(K_n\ge c\), and write \(q=2^c=1+\eta\), \(\eta=2^c-1\). Then
\[
 \lambda(m_n)\ge q\lambda(n).
\]
The finite contraction inequality
\[
 \lambda(n^2)\ge\lambda(m_n)-\log2
\]
therefore gives, after exponentiating,
\[
 \boxed{r(n^2)\le2\,r(n)^{1+\eta}n^{1-\eta}.}                         \tag{12}
\]
Equivalently, in the \(q\)-notation,
\[
 r(n^2)\le2\,r(n)^q n^{2-q}.                                      \tag{13}
\]
Equations (12)--(13) hold on the positive-density good scales supplied above only; they are not an eventual statement.

For
\[
 X(n)=\lambda(n^2)-2\lambda(n),
\]
the same calculation says on those scales
\[
 \boxed{X(n)\ge-(2-q)\lambda(n)-\log2.}                              \tag{14}
\]
For fixed \(q<2^{1/6}\), this is far weaker than the missing assertion
\(X(n)\ge-o(\sqrt{\log n})\), which would require a near-zero lower defect rather than a fixed fractional loss of \(\lambda(n)\).

## Eight-part compact contract

1. **Quantifiers and modality.** Statements (7) and (11) quantify fixed \(q\in(1,2^{1/6})\), fixed \(\rho>3\), and fixed \(c<A\), with liminf over \(M\to\infty\) or all real \(T\to\infty\); they do not assert eventual \(P\). Raghavan-v3 is an external preprint input, not a Lean-formalized theorem.
2. **Exact additive/error structure.** The only contraction error used in (1)--(2) is the additive \(O(\sqrt{\lambda(n)})\) error in (A1), divided by \(\lambda(n^2)\ge\lambda(n)\); the finite transfer loses exactly \(\log2\), and the weighted transfer uses the fixed-tail split.
3. **\(\lambda\)/\(X\) implications.** The threshold \(K_n\ge c\) gives (12)--(13), and hence exactly the one-sided bound (14); neither this bound nor the density conclusion implies the missing near-zero \(X\)-bound.
4. **Parameter optimization.** The global threshold is \(\alpha=\log_2q<1/6\), giving \((1/6-\alpha)/(1-\alpha)\); locally the endpoint mean is \(A=(\rho/6-1/2)/(\rho-1)\), and the density loss is \((A-c)/(1-c)\). Letting \(\rho\to\infty\) approaches \(1/6\), but no endpoint is silently included.
5. **Models.** In the exact model \(\lambda(N)=C\sqrt{\log N}\), both \(C_n,K_n\to1/2\) (under the stated transfer error). In an exact Raghavan-shaped model \(\lambda(N)=c_0(\log N)^{1/6}(\log\log N)^{-1/6}\), both tend to \(1/6\). The model \(r(N)=N/\log N\), i.e. \(\lambda(N)=\log\log N\), is inconsistent with Raghavan-v3.
6. **Falsifier and termination.** A failure of (2), (7), or (11) at the stated orders would falsify the corresponding accepted weighted identity, contraction estimate, envelope, or local recurrence. The argument terminates at positive-density scales and local recurrence: it claims no eventual **P** and no asymptotic formula.
7. **Formalization boundary.** `CriticalContractionTransfer.lean` already formalizes the finite transfer. The weighted and asymptotic transfer in (1)--(11), including the external Raghavan input, is not Lean-formalized; a minimal Lean artifact would be an abstract weighted-prefix-density lemma with the analytic inputs supplied as hypotheses.
8. **Scope.** This is a self-contained bookkeeping and transfer note only; it makes no novelty claim, adds no vector-grid reduction, and does not strengthen any conclusion from positive-density or local recurrence to an all-scale theorem.
