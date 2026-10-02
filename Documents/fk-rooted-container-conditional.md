# Conditional rooted FK container: supported cycles through a prescribed outside arm (polylog return boundary)

**Status.** Conditional theorem; this is our informal fixed-arm adaptation $F'$ of Friedman--Krivelevich (arXiv:1912.11011, §2.1 Lemmas 2.1--2.6, §2.2 Lemma 2.7, and §2.3 proof of Theorem 1). No Lean formalization, no EGC claim. The container is a hypothesis here and is **not proved by this file**. The assembled manuscript `Documents/high-girth-expander-cycles.md` constructs that container before applying $F'$.  This exposition is based on repository manuscript snapshot `724c14d8259403ad831c3f0dbcf90aee04326c0d`, not on an arXiv version, with the greedy quantifier clarification below.
$\log=\log_2$.

## 0. Expansion conventions, bridge, and the independent floor-pruning lemma

For a graph $J$ of order $M$, write $N_J(S)$ for the external neighborhood
$N_J(S)\setminus S$.  We distinguish the two half-range conventions:

* **floor-half $\gamma$-expansion** means
  $|N_J(S)|\ge\gamma|S|$ for every $S$ with
  $|S|\le\lfloor M/2\rfloor$;
* **ceil-half $\gamma$-expansion** means the same inequality for every $S$ with
  $|S|\le\lceil M/2\rceil$.

The parameter $\alpha$ in the theorem in §1 is explicitly a **ceil-half**
parameter.  The floor-pruning lemma below is independent of the source's FK
lemmas: it has no degree hypothesis and its loss is not obtained by replacing
$|F|$ with a neighborhood of $F$.

**Floor-pruning lemma.** Let $G$ have order $M>0$ and be floor-half
$\alpha$-expanding, where $0<\alpha\le1$.  Let $F\subseteq V(G)$, write
$f:=|F|$, and assume
$$
 f\le\frac{\alpha^2M}{16}.
$$
Starting with $R=\varnothing$, always keep $R\cap F=\varnothing$.  Put
$H:=G-(F\cup R)$.  While there is a nonempty bad set
$S\subseteq V(H)$ with $|S|\le|H|/2$ and
$$
 |N_H(S)|<\frac\alpha2|S|,
$$
remove $S$ into $R$.  The process terminates with
$$
 |R|\le\frac{2f}{\alpha},\qquad |F\cup R|\le\frac{3f}{\alpha},
$$
and the final $H$ is floor-half $\alpha/2$-expanding.  The conclusion is
non-vacuous: $H$ is nonempty because
$3f/\alpha\le3\alpha M/16<M$.

Here is the bookkeeping.  At every stage a candidate bad $S$ is contained in
an original half-set, and
$$
 |N_G(S)|\le f+|R|+|N_H(S)|,
$$
so original expansion gives
$$
 |S|<\frac{2(f+|R|)}\alpha.                       \tag{0.1}
$$
For the union of all removed bad sets, including a partial union at any stage,
any external neighbor outside $F$ was present when the bad set adjacent to it
was removed.  Consequently
$$
 N_G(R)\subseteq F\cup\bigcup_iN_{H_i}(S_i),\qquad
 |N_G(R)|\le f+\frac\alpha2|R|,                    \tag{0.2}
$$
where $H_i$ is the current graph at the removal of $S_i$.  Applying original
expansion to the **new** set $R$ (not to $F\cup R$) gives
$|R|\le2f/\alpha$, provided $R$ is in the floor range.  Inductively this is
valid: before the next removal, (0.1) and the preceding bound give
$$
 |R|+|S|\le\frac{4f}{\alpha}+\frac{4f}{\alpha^2}
 \le\frac{8f}{\alpha^2}\le\frac M2.               \tag{0.3}
$$
Thus (0.2) applies after each update as well.  If $f=0$, no bad set exists
initially, directly by original floor expansion, and $R$ stays empty.  At
termination there is no bad set, which is precisely floor-half
$\alpha/2$-expansion of the final graph.  This is a degree-free lemma and is
not the source's FK Lemma 2.2.

**Floor-to-ceil bridge.** If $J$ has order $M$ and is floor-half
$\gamma$-expanding, it is ceil-half $\gamma/2$-expanding once the displayed
threshold below is met.  For even $M$ there is no change.  For odd
$M=2m+1$, only a set $S$ of size $m+1$ is new: choose $v\in S$ and apply
floor expansion to $S\setminus\{v\}$ to obtain
$$
 |N_J(S)|\ge\gamma m-1\ge\frac\gamma2(m+1)
$$
whenever $m\ge1+2/\gamma$.  Smaller sets are already in the floor range.
Thus the explicit threshold is $M\ge2\lceil1+2/\gamma\rceil+1$ in the odd
case (and no threshold is needed in the even case).  In particular a large
floor-half $\gamma$ host supplies a ceil-half $\gamma/2$ host.

## 1. Theorem

Let $0<\alpha\le1$, $K>0$, $G$ a graph, $U\subseteq V(G)$, $|U|=n$, $H:=G[U]$ an
**ceil-half $\alpha$-expander**. Assume

* (H1) outside $U$: vertex-disjoint rooted trees $T_1$ (root $a$), $T_2$ (root $b$),
  each of radius $\le K\log n$;
* (H2) an $a$–$b$ path $Q_0$ with $V(Q_0)\cap U=\varnothing$,
  $V(Q_0)\cap(V(T_1)\cup V(T_2))=\{a,b\}$, $|Q_0|\le K\log n$;
* (H3) $X_i:=N_G(V(T_i))\cap U$ satisfy $X_1\ne\varnothing$ and $|X_2|\ge\log^6 n$.

Then there are $A(\alpha)=3C_2=51/\alpha$ (**independent of $K$ and $n$**),
$c=3K+O_\alpha(1)$, $\rho(\alpha)=2^{-O(\log(1/\alpha)/\alpha)}$, $n_0(\alpha,K)$ such
that for every $n\ge n_0$ and every integer $\ell\in[c\log n,\rho n]$ there is a simple
cycle $C_\ell$ with

* (C1) $Q_0\subseteq C_\ell$ and $|C_\ell|\in[\ell,\ell+A]$;
* (C2) **support:** $V(C_\ell)\subseteq U\cup V(T_1)\cup V(T_2)\cup V(Q_0)$;
* (C3) **interface:** $W_\ell:=y\to T_1\to a\to_{Q_0}b\to T_2\to x_0$ (endpoints
  $y,x_0\in U$ included) is a simple path, $C_\ell$ is $W_\ell$ plus a simple $H$-path
  from $x_0$ to $y$, and $C_\ell\setminus U=V(W_\ell)\setminus\{y,x_0\}$.

(C3) is the composition interface: if $Q_j$ ($j=0,\dots,r$, $r$ fixed) is an $a$–$b$ path
with $V(Q_j)\cap U=\varnothing$ and interior avoiding $V(T_1)\cup V(T_2)$, replacing $Q_0$
by $Q_j$ inside $W_\ell$ gives a simple cycle with support
$\subseteq U\cup V(T_1)\cup V(T_2)\cup V(Q_j)$ and length $|C_\ell|+(|Q_j|-|Q_0|)$.

The width $51/\alpha$ and the constants $\rho(\alpha)$ and $(\log n)^6$
are parameters of this internal conditional adaptation $F'$, not verbatim
constants of canonical Friedman--Krivelevich Theorem 1.  That canonical theorem
does not itself prescribe the two trees, the outside path, or the support and
interface in (C2)--(C3); those features are derived here.

## 2. Greedy packing lemma (replaces FK's Menger packing; no linear $|X_2|$)

**Lemma.** Let $H$ be an $\alpha$-expander on $n$ vertices, $A,B\subseteq V(H)$,
$D_0:=\min(|A|,|B|)\ge1$, and let $F\subseteq V(H)$ satisfy $|F|\le\alpha D_0/20$ and
$|A\setminus F|,|B\setminus F|\ge D_0/2$. Then $H-F$ contains an $A\setminus F$–$B\setminus F$
path of length $\le L:=2r+1$, where $r:=\lceil\log(2n/D_0)/\log(1+0.9\alpha)\rceil$, so
$L=O(\alpha^{-1}\log(2n/D_0))$. Consequently, starting from $F=\varnothing$ and repeating
this at most $p:=\lfloor\alpha D_0/(20(L+1))\rfloor$ times (each time adding all vertices
of the found path to $F$) yields $p$ vertex-disjoint paths, each of length $\le L$, and
the invariant $|F|\le\alpha D_0/20$ holds at every step.

*Proof.* For $S\subseteq V(H-F)$ with $D_0/2\le|S|\le\lfloor(n-|F|)/2\rfloor$ we have
$\lfloor(n-|F|)/2\rfloor\le\lceil n/2\rceil$, so
$|N_{H-F}(S)|\ge|N_H(S)|-|F|\ge\alpha|S|-\alpha D_0/20\ge0.9\alpha|S|$ (as $|S|\ge D_0/2$).
So every ball $B$ in $H-F$ of size in $[D_0/2,\lfloor(n-|F|)/2\rfloor]$ grows:
$|B\cup N_{H-F}(B)|\ge(1+0.9\alpha)|B|$. Since $(1+0.9\alpha)^r(D_0/2)\ge n/2\ge(n-|F|)/2$, both
$B_{H-F}(A\setminus F,r)$ and $B_{H-F}(B\setminus F,r)$ have size
$\ge\lfloor(n-|F|)/2\rfloor+1>(n-|F|)/2$; as subsets of the $(n-|F|)$-vertex graph $H-F$
they meet, and the concatenation is a path of length $\le2r+1=L$. For the loop: after
$t\le p$ steps, $|F|\le t(L+1)\le\alpha D_0/20$, so the hypothesis is available at each
step and $|A\setminus F|,|B\setminus F|\ge D_0-\alpha D_0/20\ge D_0/2$. $\square$

If
$$
 x:=\frac{\alpha D_0}{20(L+1)}\ge4,
$$
then the floor has the useful slack estimate
$$
 p=\lfloor x\rfloor\ge\frac{x}{2}
   =\frac{\alpha D_0}{40(L+1)}\ge2.                        \tag{2.1}
$$
This is an additional condition, not a consequence of `n` growing when
`D_0` is arbitrary.  In the application below,
`D_0\ge0.5\log^6 n` and `L=O(\alpha^{-1}\log n)`, so `x\ge4` for all
sufficiently large `n`.  All packed paths are short; `U_2` enters only as a
large target set.

## 3. Proof of the theorem

**(S1)** Pick $y\in X_1$. Lemma 2.7 in $H$ at $v_0=y$ gives $T'$ rooted at $y$, levels
$L_1=\{y\},\dots,L_{k_2}$, with $k_0\le C_0\log n$, $k_1-k_0\le C_1$, $k_2-k_1\le C_2$,
degrees in $T'_{[k_1,k_2]}\le\Delta$, and $U_2\subseteq T'_{[k_1,k_2]}$ an
$(n/10,\alpha/5)$-expander, $|U_2|\ge n/10$; $\Delta=\lceil1600/\alpha^5\rceil$,
$C_0=15/\alpha$, $C_1=201/\alpha^5$, $C_2=17/\alpha$.

**(S2)** §2 with $A:=X_2\setminus\{y\}$ (so $|A|\ge\log^6n-1$) and $B:=U_2$ gives
$D_0=\min(|A|,|U_2|)\ge0.5\log^6n$ for $n\ge n_0(\alpha)$, and
$p=\lfloor\alpha D_0/(20(L+1))\rfloor$ disjoint paths,
$L=O(\alpha^{-1}\log n)$.  Since the condition in (2.1) holds for large
$n$, the slack estimate there gives
$p\ge\alpha D_0/(40(L+1))\ge2$. **Truncate** each at its first $U_2$-vertex, so its $U_2$-end is
$v_x$ and $Q_x\cap U_2=\{v_x\}$; if $x\in U_2$ the truncated path is the single vertex
$x=v_x$.

**(S3)** Drop the $\le1$ path containing $y$; let $S$ be the remaining $x$-ends,
$|S|\ge p-1\ge p/2$ (as $p\ge2$). For $x\in S$ let $b_x\in Q_x\cap T'$ maximise
$|T'_{b_x}|$ (exists: $v_x\in U_2\subseteq T'$); $B_{\rm set}:=\{b_x\}$,
$|B_{\rm set}|=|S|$ (paths disjoint).

**(S4) Elimination.** $B_{\rm set}\subseteq T'=\bigcup_{i\le k_2}L_i$ and
$k_2\le C_0\log n+C_1+C_2$, so some level carries $B'\subseteq B_{\rm set}$ with
$|B'|\ge|B_{\rm set}|/k_2$; subtrees at one level are disjoint, so some $x_0$ has
$|T'_{b_{x_0}}|\le n/|B'|\le2nk_2/p$. By the union bound (no nesting of the $T'_u$)
$$|Y|:=\Bigl|\bigcup_{u\in Q_{x_0}\cap T'}T'_u\Bigr|\le(L+1)|T'_{b_{x_0}}|\le\frac{2(L+1)nk_2}{p}
=O\!\left(\frac{n\log^3n}{\alpha^4D_0}\right)=O\!\left(\frac{n}{\alpha^4\log^3n}\right),$$
since $D_0\ge0.5\log^6n$.

**(S5) Cleaning.** $w\in L_{k_1}$ is *bad* if $T'_w\cap Y\ne\varnothing$; $A_B:=$ union of bad
subtrees satisfies $|A_B|\le C_3|Y|$ with $C_3:=\Delta^{C_2+1}=2^{O(\log(1/\alpha)/\alpha)}$
(distinct level-$k_1$ subtrees are disjoint, each of size $\le C_3$), and
$Y\cap T'_{[k_1,k_2]}\subseteq A_B$. Let $v_0:=v_{x_0}$ and $K$ be its component in
$G_2=H[U_2]$; $G_2[K]$ is an $(n/10,\alpha/5)$-expander and $|K|>n/10$. Lemma 2.2 is
applied to $G_2[K]$ with $V_0:=A_B\cap K$ (not $A_B$, which need not lie in $K$); the
sizes are unchanged, $|A_B\cap K|\le C_3|Y|=O_\alpha(n/\log^3n)\le\alpha^2n/2000$ for
$n\ge n_0(\alpha)$. It gives $U_3\subseteq K\setminus A_B$ with
$|U_3|\ge(1-3\alpha/40)|K|$ such that $G_3=H[U_3]$ is an $(n/10,\alpha/10)$-expander;
hence $|U_3|>n/10$ automatically. Set
$D:=\bigcup\{T'_w:w\in L_{k_1},\,T'_w\cap U_3\ne\varnothing\}$; $D$ is a union of *good*
subtrees, so $D\cap Y=\varnothing$.

**(S6)** Let $Q'$ be a shortest $v_0$–$(D\cap K)$ path in $K$, endpoint $u_0$; then
$Q'\cap D=\{u_0\}$ and $|Q'|\le350\log n/\alpha$ (Lemma 2.1). Contract each cluster
$T'_w\cap U_3$ ($w\in L_{k_1}\cap D$) in $G_3$; by Lemma 2.4 the result $G'$ is an
$(n/(10C_3),\alpha/(10C_3))$-expander on $>n/(10C_3)$ vertices, so every component is
larger than $n/(10C_3)$ and Lemma 2.5 gives a path $P'=v_{w_0},a_1,a_2,\dots$ from the
contracted cluster of $w_0$ ($u_0\in T'_{w_0}$, $w_0\in L_{k_1}\cap D$) of length
$\ell':=\lceil(\alpha/(10C_3))\lfloor n/(10C_3)\rfloor\rceil\ge\alpha n/(100C_3^2)-\alpha/(10C_3)$.
**Unfold every cluster.** For each edge of $P'$ incident with a contracted vertex $v_w$,
take a representative $u\in T'_w\cap U_3$ adjacent in $G_3$ to the other endpoint; $v_w$
occurs once in $P'$, so at most two representatives are needed, joined by the unique tree
path in $T'_w$ (length $\le2C_2$). For the first cluster, add the tree path from $u_0$
(possibly outside $U_3$) to its representative. The
result $P$ is a simple path in $D$ starting at $u_0$, with $|P|\ge\ell'$, $P\cap T'_{w_0}$
an initial segment of $P$, and each cluster contributing one contiguous block of
$\le2C_2+1$ vertices. Simplicity: clusters are disjoint, $P'$ visits each
contracted vertex once, and original vertices of $P'$ lie in no cluster.

**(S7) Cycle.** Choose $x_0'\in V(T_2)$ adjacent to $x_0$ and
$W:=y\to y_1(\in T_1)\to a\to_{Q_0}b\to x_0'(\in T_2)\to x_0$: simple, contains $Q_0$,
$V(W)\cap U=\{y,x_0\}$, $|W|\le3K\log n+2$. With $Q:=W+Q_{x_0}+Q'$ and
$m:=|Q|\le3K\log n+2+L+350\log n/\alpha=(3K+O_\alpha(1))\log n$, take
$c\ge3K+O_\alpha(1)$ (so $d:=\ell-m-k_1\ge0$) and $\rho:=\alpha/(400C_3^2)$; since
$|P|\ge\alpha n/(100C_3^2)-\alpha/(10C_3)\ge\alpha n/(200C_3^2)$ for $n\ge n_0(\alpha)$,
we get $d+2C_2+2\le|P|$. Walk $d$ steps along $P$ from $u_0$ to $z$, continue along $P$ to
the first vertex $z'$ outside $z$'s cluster, then along $T'$ from $z'$ to $y$. This is a
simple cycle $C_\ell$ with $|C_\ell|=(\ell-k_1)+s+\mathrm{dep}(z')$,
$1\le s\le2C_2+1$, $k_1-1\le\mathrm{dep}(z')\le k_1+C_2-1$; hence
$|C_\ell|\in[\ell,\ell+3C_2]$.

**(S8) Support.** $Q_{x_0},Q',P$ and the closing segment lie in $U$;
$V(W)\setminus\{y,x_0\}\subseteq V(T_1)\cup V(T_2)\cup V(Q_0)$. Hence
$V(C_\ell)\subseteq U\cup V(T_1)\cup V(T_2)\cup V(Q_0)$ and
$C_\ell\setminus U=V(W)\setminus\{y,x_0\}$: (C2) and (C3) hold.

**(S9) Disjointness audit (repairs to the source argument).**
(i) Truncating $Q_{x_0}$ at its first $U_2$-vertex gives $Q_{x_0}\cap U_2=\{v_0\}$, hence
$Q_{x_0}\cap Q'=\{v_0\}$ since $Q'\subseteq K\subseteq U_2$ — the source only asserts
$Q\cap P=\{u_0\}$.
(ii) Dropping the path through $y$ gives $W\cap Q_{x_0}=\{x_0\}$ and, since
$Q'\subseteq K\subseteq U_2$ while $W\cap U=\{y,x_0\}$, $W\cap Q'\subseteq\{x_0\}$: the
only possible sharing is $x_0=v_0$ when $x_0\in U_2$ (then $Q_{x_0}=\{x_0\}$ and $x_0$ is
the single concatenation endpoint of $W$ and $Q'$). So $Q$ is a simple path.
(iii) $Q_{x_0}\cap D=\varnothing$ (as $Q_{x_0}\cap T'\subseteq Y$, $D\cap Y=\varnothing$, and
$Q_{x_0}\setminus T'\subseteq U\setminus T'$), so $Q\cap D=\{u_0\}$ and $Q\cap P=\{u_0\}$.
(iv) $y,x_0\notin D$ ($y$ at level $1<k_1$; $x_0\in Y$ whenever $x_0\in T'$, and
$D\cap Y=\varnothing$), so the closing segment misses $W$.
(v) It misses $Y$: if $v\in Y$ lay on the root path $w'\to y$, then
$T'_{w'}\subseteq T'_v\subseteq Y$, contradicting goodness of $w'$; hence it misses
$Q_{x_0}\cap T'\subseteq Y$.
(vi) Only the **prefix** $P_{z'}$ of $P$ through $z'$ lies on the cycle. Since $P$'s block
inside $T'_{w'}$ (the cluster of $z'$) is contiguous and starts at $z'$,
$P_{z'}\cap T'_{w'}=\{z'\}$; the closing path meets $T'_{[k_1,k_2]}$ only inside
$T'_{w'}$, where it is $[z',w']$, so closing $\cap P_{z'}=\{z'\}$. Also
$Q'\cap T'_{w'}=\varnothing$ ($Q'\cap D=\{u_0\}$, $u_0\in T'_{w_0}$, and $w'\ne w_0$ since
$P\cap T'_{w_0}$ is an initial segment). Above level $k_1$ the closing path is only
$[w',y]$, avoiding all other clusters and $Q'$ ($w'\notin Q'$).
(vii) $P$ is simple by the cluster unfolding of (S6); this replaces the source's "path
starting at $u_0$" step, which needs repair because $u_0\in D\cap K$ need not lie in
$U_3$.

## 4. Constants and composition interface

$A=3C_2=51/\alpha$, independent of $K$ and $n$; $C_3=2^{O(\log(1/\alpha)/\alpha)}$;
$\rho=\alpha/(400C_3^2)=2^{-O(\log(1/\alpha)/\alpha)}$, $\alpha$-only;
$c=3K+O_\alpha(1)$; $n_0=n_0(\alpha,K)$ from $C_3|Y|\le\alpha^2n/2000$ and
$c\log n\le\rho n$. Since $A$ is $K$-free, the composition may choose the
ceil-half parameter $\alpha$ after applying the floor-to-ceil bridge, and may
fix $q$ before any packing.

## 5. Provenance and asymptotic weakening

The canonical source uses $\mu=200/\alpha^4$ and a linear return condition
$|X_2|\ge\alpha^4 n/200$ in its source-level container argument.  This
companion does not attribute that linear-return proof to the present
polylogarithmic statement.  Our $F'$ adaptation uses the full-level window in
(S4), the greedy packing of §2, and the count
$$
 |Y|=O\!\left(\frac{n\log^3 n}{\alpha^4D_0}\right),
$$
which is enough when $D_0\ge\tfrac12\log^6 n$.  The $\beta$-dependent sketch
sometimes used to motivate a shorter window is not attributed to
Friedman--Krivelevich.  No claim is made that any canonical source proof has an
error beyond the precisely documented adaptation and its changed return
boundary.

All constants in this adaptation are $\alpha$-only except $c$ and $n_0$,
which carry $K$.

## 6. Bipartite / dyadic corollary

Fix $r$ (independent of $n$) with $r\ge\lceil A/2\rceil$. If $G$ is bipartite (all cycles
even) and there are $a$–$b$ paths $Q_j$, $j=0,\dots,r$, of length $|Q_0|+2j$, each with
vertices outside $U$ and interior avoiding $V(T_1)\cup V(T_2)$, then for every dyadic $2^k$
with $\ell:=2^k-2r\in[c\log n,\rho n]$, §3 gives $C_\ell$ with
$|C_\ell|\in[2^k-2r,2^k-2r+A]$, so $|C_\ell|\le2^k$, $|C_\ell|$ is even and
$2j:=2^k-|C_\ell|\in[2r-A,2r]$, $j\le r$. Replacing $Q_0$ by $Q_j$ in $W_\ell$ (valid by
(C3)) increases the length by exactly $2j$, giving a simple cycle of length exactly $2^k$
with support $\subseteq U\cup V(T_1)\cup V(T_2)\cup V(Q_j)$; this holds for every dyadic
$2^k\in[2c\log n,\rho n]$ once $n\ge n_0(\alpha,K,r)$.

## 7. Status of verification

Proved here: the greedy packing lemma (no source analogue), the elimination count, repairs
(i),(ii),(vi),(vii) of §3. Checked against the source: Lemmas 2.1–2.7 with
$\Delta,C_0,C_1,C_2$, the $(n/10,\alpha/5)$ expander $U_2$, contraction (Lemma 2.4), the
long-path lemma (Lemma 2.5, exact form
$\lceil(\alpha/(10C_3))\lfloor n/(10C_3)\rfloor\rceil$), and deletion (Lemma 2.2:
$|V_0|\le\alpha^2k/8$, output $|U|\ge(1-3\varepsilon/\alpha')|K|$). **Conditional boundary of this companion.** The two-arm container (existence of
$T_1,T_2,Q_0$ with $X_1\ne\varnothing$, $|X_2|\ge\log^6n$) is an input to
this file, not a conclusion of it.  The assembled high-girth manuscript
constructs this container before applying the theorem.  Greedy constants are
deliberately lossy; no finite-$n$ experiment is decisive.
