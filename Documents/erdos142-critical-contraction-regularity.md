# Erdős 142: critical-contraction regularity

This note records a transfer lemma, not **P**, and makes no novelty claim. Write
\(r=r_3\), \(\lambda(M)=\log(M/r(M))\), and \(h=\log 2\). Assume the accepted inputs: Roth \(\lambda(M)\to\infty\); the eventual envelope \(\lambda(M)\le C\sqrt{\log M}\); interval partitioning
\[
 x\ge y\ge1\quad\Longrightarrow\quad \lambda(x)\ge\lambda(y)-h;
\]
and the carry-free product inequality
\[
 r(2uv)\ge r(u)r(v),
\]
formalized as `Erdos142.rothNumberNat_mul_le_rothNumberNat_two_mul_mul` in `Proofs/Erdos/Erdos142/ScaleProduct.lean`.

## Exact finite transfer

For each \(N\), put
\[
 x=N^2,\qquad a=r(N)^2,\qquad t=x/a=e^{2\lambda(N)},\qquad b=\lceil t\rceil.
\]
(Here \(a\ge1\), and \(x\ge a\) because \(r(N)\le N\).) Interval partitioning immediately gives the first, directed inequality
\[
 \boxed{\lambda(a)-\lambda(x)\le h}. \tag{1}
\]
For the other direction, the ceiling bounds are \(t\le b<t+1\), so \(x=at\le ab\), hence \(x\le2ab\). Applying partitioning with \(2ab\ge x\) gives
\(\lambda(x)\le\lambda(2ab)+h\). The product inequality, with its direction preserved on taking logarithms, gives
\[
 \lambda(2ab)=\log\frac{2ab}{r(2ab)}
 \le \log\frac{2ab}{r(a)r(b)}
 =h+\lambda(a)+\lambda(b).
\]
Consequently the second exact finite inequality is
\[
 \boxed{\lambda(x)-\lambda(a)\le\lambda(b)+2h}. \tag{2}
\]
No monotonicity of \(\lambda\) has been used. In particular, one must not claim \(\lambda(x)\ge\lambda(a)\), nor that the difference in (1) has a fixed sign.

Since \(\lambda(N)\to\infty\), \(t=e^{2\lambda(N)}\to\infty\), and therefore \(b\to\infty\). Also, eventually \(t\ge1\), and
\[
 b=\lceil t\rceil\le t+1\le2t,
 \qquad \log b\le2\lambda(N)+h. 
\]
The envelope applies to \(b\) eventually, so (1)--(2), together with \(\lambda(b)\ge0\) (because \(r(b)\le b\)), yield
\[
 |\lambda(r(N)^2)-\lambda(N^2)|
 \le C\sqrt{2\lambda(N)+h}+2h
 =O(\sqrt{\lambda(N)})=o(\lambda(N)). \tag{3}
\]
This is regularity of the critical contraction, not a gain.

## Exact logical classification

Let
\[
 H_{\eta,K}:\quad \lambda(r(N)^2)\ge(1+\eta)\lambda(N)-K
\]
for all sufficiently large \(N\), with fixed \(\eta>0,K\). The square-gain/P statement with the same \(\eta\) follows from (1):
\[
 \lambda(N^2)\ge(1+\eta)\lambda(N)-(K+h),
\]
equivalently
\[
 r(N^2)\le e^{K+h}r(N)^{1+\eta}N^{1-\eta}.
\]
Thus \(H_{\eta,K}\Rightarrow P_{\eta,K+h}\). Conversely, if this square gain holds with \(\eta>0\) and constant \(L\), (3) gives, for every fixed \(0<\eta'<\eta\),
\[
 \lambda(r(N)^2)\ge(1+\eta')\lambda(N)-K'
\]
for some fixed \(K'\) and all sufficiently large \(N\): the \(O(\sqrt\lambda)\) error is eventually absorbed by \((\eta-\eta')\lambda\). Hence existence of some fixed positive eventual gain is equivalent between \(H\) and square gain/P, after loss in \(\eta\). This is not literal equivalence with identical fixed parameters.

For the accepted defect \(X=\lambda(N^2)-2\lambda(N)\), (3) says
\[
 X=\lambda(r(N)^2)-2\lambda(N)+O(\sqrt{\lambda(N)}).
\]
The envelope gives \(\sqrt{\lambda(N)}=O((\log N)^{1/4})=o(\sqrt{\log N})\). Therefore the missing assertion \(X\ge-o(\sqrt{\log N})\) is equivalent to
\[
 \lambda(r(N)^2)\ge2\lambda(N)-o(\sqrt{\log N}).
\]
Neither inequality, nor **P**, is proved here.

## Compact contract and status

The modality is eventual: constants \(C,\eta,K\) are fixed, and conclusions quantify all sufficiently large \(N\). The exact finite inequalities (1)--(2) are now formalized in `Proofs/Erdos/Erdos142/CriticalContractionTransfer.lean`, via `criticalContraction_upper`, `criticalContraction_lower`, and `criticalContractionTransfer`. The ceiling specialization and the asymptotic \(O(\sqrt{\lambda})\), **P** classification, and \(X\) equivalence remain prose/unformalized. The artifact is sorry-free and audited with only standard axioms.

The algebraic model \(r(N)\approx N/\log N\) has bounded discrepancy in the contraction comparison (3) but violates the current lower envelope, so it is only a model. Behrend \(\lambda\sim c\sqrt{\log N}\) likewise predicts bounded discrepancy in (3). The accepted lacunary scalar obstruction may have no fixed positive gain and is compatible with this transfer. A falsifier would contradict one exact input or inequality above; absent that, termination means only transfer regularity, not gain. One foundations audit incorrectly asserted this difference is nonnegative; this note explicitly avoids that assertion.
