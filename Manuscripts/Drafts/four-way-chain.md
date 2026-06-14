# Four bounds, two mechanisms, one collapse

A synthesis note on why four distinct lower bounds all saturate at
n^2 on the matrix multiplication tensor <n,n,n>, and what that
saturation tells us about the barrier landscape for omega.

---

## 1. The four bounds

### 1a. Flattening rank (linear algebra)

**Statement.** For any tensor T in C^{m_1} x C^{m_2} x C^{m_3},
the rank R(T) is at least the rank of any unfolding (flattening)
T_{(i)}.  For T = <n,n,n>, each flattening is an n^2 x n^2 matrix
of full rank, giving R(<n,n,n>) >= n^2.

**Primary source.** This is classical linear algebra; it appears
as a basic tool throughout Landsberg, *Geometry and Complexity
Theory* (2017), Sections 2.1--2.3.  The flattening rank equals
the rank of the linear map T_{(i)}: (C^{m_j} tensor C^{m_k})* -> C^{m_i}.

**What it uses.** Rank of a matrix -- a single integer.  No spectral
information (eigenvalues, singular values) beyond the count of
nonzero ones.

### 1b. Catalecticant rank (algebraic geometry / apolarity)

**Statement.** For a symmetric tensor (homogeneous polynomial)
P in S^n V, the Waring rank RS(P) >= rank(P_{k,n-k}) for any
partition n = k + (n-k), where P_{k,n-k}: S^k V* -> S^{n-k} V is
the catalecticant map.

**Primary source.** Landsberg (2017), Section 6.2.2 (line 9546):
"first introduced by Sylvester in 1852 and called catalecticants
by him.  They are also called flattenings and in the computer
science literature the polynomials induced by the method of partial
derivatives."

**What it uses.** Rank of a matrix (the catalecticant map).  For the
specific form h_{n,m} = ||x||^{2s}, Reznick (1992) Theorem 8.15(ii)
gives rank(H_{h_{n,m}}) = N(n,s) = dim F_{n,s} = binom(n+s-1, s),
where H_p is the Hankel/moment matrix of p.

### 1c. Fisher / design-size bound (combinatorics)

**Statement.** Any spherical t-design X in S^{n-1} has |X| >= N(n,s)
where m = 2s = t (even precision) and N(n,s) = binom(n+s-1, s).
This is the "Fisher bound" or "dimension-counting bound."

**Primary source.** Reznick (1992):
- Theorem 7.18 (p.94): quadrature formula of precision m with r
  nodes exists iff G_{K,mu} in Q_{n,m}(K-tilde) and width
  w(G_{K,mu}; K-tilde) <= r.
- Theorem 7.22 (p.95): If K is full, then
  N(n,s) <= w(G_{K,mu}; K-tilde) <= N(n,m).
- Proposition 7.24 (p.96): in every such quadrature formula,
  r >= N(n,s).

**Connection to 1b.** The proof of the lower bound r >= N(n,s) uses
rank(H_p) where H_p is Reznick's moment/Hankel matrix.  This
matrix IS structurally a catalecticant -- it is the bilinear form
(f,g) -> [fg, p] on F_{n,s} x F_{n,s} -- but Reznick never uses
the word "catalecticant" or cites the apolarity literature.

**What it uses.** Rank of the moment matrix = dimension of a
polynomial space.  No spectral information.

### 1d. Quantum functional F_theta (quantum information)

**Statement.** For any complex tensor T in C^{n_1} x ... x C^{n_k}
and any probability distribution theta on {1,...,k}:

  F_theta(T) = 2^{E_theta(T)},

  E_theta(T) = sup_{(lambda) in Delta_T} sum_i theta(i) H(lambda^{(i)})

where Delta_T is the entanglement polytope (moment polytope) of T
and H is Shannon entropy.  F_theta is a universal spectral point:
monotone under restriction, multiplicative under tensor product,
additive under direct sum.

For T = <n,n,n>: F_theta(<n,n,n>) = n^2 for all singleton theta.

**Primary sources.**
- Christandl--Vrana--Zuiddam (CVZ), arXiv:1709.07851, Theorem 1.1 /
  Section 3 (= Theorem 4.14 at line 2655 for free tensors):
  F^theta = F_theta for singleton theta, and this is a universal
  spectral point.
- CVZ, Section 4.3, Example at line 2783: the format (ab,bc,ca) is
  comfortable; the support of <a,b,c> with uniform distribution gives
  marginals uniform on [ab], [bc], [ca].
- Christandl--Lysikov--Zuiddam (CLZ), arXiv:2012.14412, Theorem 4
  (= Corollary 3.8, line 673): T is semistable iff
  G_xi(T) = min_i m_i^{1/xi_i} for every xi.

**What it uses.** The full marginal spectrum (all singular values,
normalized) of each flattening, optimized over the moment polytope.
This is strictly more than rank: Shannon entropy H(p) depends on
all entries of the probability vector p, not just its support size.

---

## 2. The two mechanisms

The four bounds above separate into two fundamentally different
mechanisms for producing the number n^2.

### Mechanism R: rank-of-a-matrix

Bounds 1a, 1b, and 1c all work by computing the rank of a matrix
built from the tensor or form.

- **1a (flattening):** rank(T_{(i)}) for T in C^{m_1} x C^{m_2} x C^{m_3}.
- **1b (catalecticant):** rank(P_{k,n-k}) for P in S^n V.
- **1c (Fisher/design):** rank(H_p) for p in Q_{n,m}.

The matrices differ in construction, but all three bounds extract a
single integer (the rank) and use nothing about the spectrum beyond
the count of nonzero singular values.

**Identification 1b = 1c (IMPLICIT).** Reznick's moment/Hankel
matrix H_p is structurally identical to the catalecticant
P_{s,s}: S^s V* -> S^s V evaluated at p = h_{n,2s}.  Both are the
bilinear form on the space of degree-s polynomials induced by the
degree-2s form p.  But Reznick never identifies H_p as a
catalecticant, and Landsberg never mentions designs.  This
cross-identification is implicit in the literature: it requires
recognizing that the same matrix appears under different names in
two disjoint communities (real algebraic geometry / quadrature
vs. algebraic geometry / apolarity).

**Identification 1a ~ 1b (KNOWN AS ANALOGY).** Landsberg (2017),
Section 8.2.1, presents Young flattenings (including catalecticants)
as generalizations of tensor flattenings.  The catalecticant is a
special case of a flattening for SYMMETRIC tensors; the general
tensor flattening is the analogue for arbitrary tensors.  These are
structurally analogous but apply to different objects (symmetric
Waring rank vs. general tensor rank) and are not literally "the
same inequality."

### Mechanism E: entropy-over-moment-polytope

Bound 1d (the quantum functional) works by optimizing Shannon
entropy over a convex body (the moment polytope / entanglement
polytope).  The optimization considers the full probability
vector of squared singular values of each flattening, not just the
rank.  This is a strictly richer invariant: for non-uniform spectra,
H(p) < log_2(support size), so the entropy bound can be strictly
weaker than a log-rank bound.

**Mechanism E has no analogue of the rank bound's simplicity.**
The Fisher bound is always N(n,s) = dim F_{n,s} regardless of
weights; it never varies with the spectrum shape.  The quantum
functional F_theta varies with the moment polytope and, in
principle, with the spectrum at the optimizing point.

---

## 3. The collapse: why both mechanisms give n^2 on <n,n,n>

### The structural reason

For the matrix multiplication tensor <n,n,n>, the entropy bound
(Mechanism E) degenerates to a log-rank bound (Mechanism R).  The
reason is that the optimal point in the moment polytope has
**uniform marginals**, so Shannon entropy at that point equals
log_2(rank).

The chain of implications:

1. **<n,n,n> is semistable / polystable.**
   CLZ arXiv:2012.14412, Example after Lemma 3.3 (line 643):
   the matrix multiplication tensor <n_1,n_2,n_3> is semistable
   because the matrix spaces V_i* tensor V_j are irreducible
   representations of GL(V_1) x GL(V_2) x GL(V_3) and the tensor
   is invariant under the sandwiching action.  (In fact polystable,
   per the footnote at line 643.)

2. **Semistability implies G_xi = min_i m_i^{1/xi_i}.**
   CLZ Corollary 3.8 (line 673): over C, T is semistable iff
   G_xi(T) = min_i m_i^{1/xi_i} for every xi in Xi.
   Here the m_i = dim(V_i) are the **ambient dimensions** of the
   three tensor legs, NOT the flattening ranks.

   **Cite-check (binding).** The m_i in CLZ are unambiguously
   ambient dimensions: line 420 reads "T in V_1 tensor V_2 tensor V_3
   with dim V_i = m_i".  For the MM tensor <n_1,n_2,n_3>, the
   ambient dimensions of the three legs are n_1 n_2, n_2 n_3,
   n_3 n_1 (since T lives in (V_1* tensor V_2) tensor (V_2* tensor V_3)
   tensor (V_3* tensor V_1) where dim V_i = n_i).  For <n,n,n>,
   each m_i = n^2.  No conciseness hypothesis is required: the
   semistability test (Lemma 3.3, line 636) needs only that T be
   invariant under a group acting irreducibly on each V_i, which the
   sandwiching action provides.

3. **Semistability implies the all-uniform point is in the moment
   polytope.**
   By CLZ Theorem 4 / Corollary 3.8, semistability implies
   G_xi(T) = min_i m_i^{1/xi_i} = n^2 for all xi (when m_i = n^2).
   Via the minimax correspondence (CLZ Theorem 3, line 221 of the
   introduction), this implies F_theta(T) = n^2 for all theta.
   The moment polytope Pi(T) therefore contains the point where
   each marginal spectrum is uniform on [n^2] -- i.e., all singular
   values of each flattening are equal.

4. **At the uniform point, entropy = log(rank).**
   When the marginal probability vector is uniform on d elements,
   H(p) = log_2 d.  For d = n^2: H = 2 log_2 n.  So
   E_theta = sum_i theta(i) * 2 log_2 n = 2 log_2 n (for singleton
   theta), and F_theta = 2^{2 log_2 n} = n^2.

5. **The entropy optimization does not exercise its full power.**
   The optimization sup_{p in Pi(T)} searches over all possible
   spectra in the moment polytope.  But since the uniform spectrum
   is available AND maximizes H over all probability vectors of
   length n^2, the supremum is achieved at the uniform point.  The
   entropy bound reduces to counting the number of nonzero singular
   values, i.e., the rank.

### Why the Fisher bound also gives n^2

On the Fisher/Reznick side, the number N(n,s) arises as
dim F_{n,s} = binom(n+s-1, s).  For the specific parameters that
connect symmetric tensors to the MM setting (via catalecticant =
flattening for symmetric tensors), the dimension N(n,s) can be
identified with the flattening rank.  The proof uses only
rank(H_{h_{n,m}}) = N(n,s) by Reznick Theorem 3.16(ii), invoked
in the proof of Corollary 8.17 (p.106).

### The collapse summarized

Both mechanisms produce n^2 because both ultimately reduce to
counting n^2 nonzero values in a matrix built from the tensor:

- Mechanism R counts the rank directly.
- Mechanism E optimizes entropy over spectra, but the optimal
  spectrum happens to be uniform, so entropy = log(rank).

The structural coincidence is that <n,n,n> is both:
- **oblique/free** (CVZ line 2053: tight implies oblique implies
  free), so F_theta = zeta^theta (CVZ Theorem 4.14, line 2655),
  and
- **semistable/polystable** (CLZ line 643), so the all-uniform
  marginal point lies in the moment polytope, collapsing entropy
  to log-rank.

---

## 4. The saturation: degree-2 information and the n^2 barrier

All four bounds use only **degree-2 information** about the tensor:
they extract data from a single bilinear form (a flattening, a
catalecticant, a moment matrix, or marginal spectra of flattenings).
The number n^2 is the maximum that any such degree-2 method can
produce on <n,n,n>, because:

- Each flattening of <n,n,n> is a full-rank n^2 x n^2 matrix.
- No rank-of-a-matrix argument can exceed the matrix dimension.
- The entropy bound cannot exceed log_2(dimension) = 2 log_2 n,
  giving F_theta <= n^2.

**Breaking n^2 requires leaving this paradigm.** The Koszul
flattening bound R(<n,n,n>) >= 2n^2 - n (Landsberg Theorem 2.5.2.6,
[LO15]) already breaks past n^2 for BORDER rank by using
antisymmetric structure -- the Koszul flattening T^{wedge p}_A is
a map involving exterior powers, not just tensor products.  This is
a degree-(p+1) method, not a degree-2 method.

But for ASYMPTOTIC rank (the quantity controlling omega), all four
bounds and their natural extensions give exactly n^2 on <n,n,n>:
- Every quantum functional F_theta(<n,n,n>) = n^2 (CVZ).
- Every support functional zeta^theta(<n,n,n>) = n^2 (Strassen).
- Every weighted slice rank G_xi(<n,n,n>) = n^2 (CLZ).

This is the barrier landscape: proving omega > 2 would require an
invariant sensitive to something beyond the marginal spectrum --
i.e., beyond degree-2 information.  No such invariant is currently
known for asymptotic rank.

---

## 5. Novelty assessment

### Per-link status

| Link | Status | Evidence |
|------|--------|----------|
| Catalecticant = flattening (symmetric tensors) | KNOWN | Landsberg (2017), Section 6.2.2: explicit identification |
| Waring-rank lower bound from catalecticant rank | KNOWN | Standard; in both Reznick and Landsberg |
| Design-size lower bound from moment matrix rank | KNOWN | Reznick (1992), Theorem 8.15, Proposition 7.24 |
| Reznick's H_p = catalecticant (cross-identification) | IMPLICIT | Structurally identical objects, never identified across the two literatures |
| Tensor flattening analogous to catalecticant | KNOWN AS ANALOGY | Landsberg Section 8.2.1 presents Young flattenings as generalizations |
| F_theta(<n,n,n>) = n^2 via semistability collapse | KNOWN | CLZ Theorem 4 + CVZ Theorem 4.14 |
| "Breaking n^2 = leaving degree-2 paradigm" | UNSTATED | Not framed this way in any examined source |
| Four-way chain identification as a single collapse phenomenon | UNSTATED | No source states or implies this cross-literature synthesis |

### What is genuinely unstated

The cross-literature identification -- that these four bounds from
algebraic geometry, combinatorial design theory, and quantum
information share a common mechanism (degree-2/rank-of-a-matrix)
and saturate together because of a single structural property
(semistability of <n,n,n>) -- is not stated in any of the examined
sources.  Each community knows its own bound and the relevant
adjacent bound, but the four-way picture is assembled here for the
first time.

Specifically:
- Reznick (1992) has the design <-> Waring rank equivalence via
  moment matrices but never connects to tensor rank or quantum
  information.
- Landsberg (2017) has catalecticant = flattening and Koszul
  flattening bounds but never mentions designs or quantum functionals.
- CVZ (arXiv:1709.07851) and CLZ (arXiv:2012.14412) have the quantum
  functional framework and the semistability characterization but
  never connect to designs or Reznick's work.

### What this note is NOT claiming

This note does NOT claim a new theorem.  Qf1 established that the
F_theta mechanism and the Fisher mechanism are **independent**: they
are not the same inequality in any formal sense.  They produce the
same value on <n,n,n> because of the coincidence described in
Section 3 above, not because of a logical equivalence between the
bounds.

The contribution of this synthesis is:
1. Identifying the two-mechanism structure (rank-of-a-matrix vs.
   entropy-over-moment-polytope) and the collapse that connects them
   on semistable tensors.
2. The cross-identification of Reznick's H_p with the catalecticant
   (implicit in the literature, never stated).
3. The framing of all four bounds as instances of the degree-2
   paradigm, with the n^2 barrier as the boundary of that paradigm.

The human judges the final framing (Hu5).

---

## Citation index

- **Reznick 1992:** *Sums of even powers of real linear forms.*
  Memoirs AMS, Vol. 96, No. 463.
  - Theorem 7.18 (p.94): quadrature <-> width equivalence.
  - Theorem 7.22 (p.95): N(n,s) <= w(G_{K,mu}) <= N(n,m).
  - Proposition 7.24 (p.96): every quadrature formula has r >= N(n,s).
  - Theorem 8.15(ii) (p.105): h_{n,m} in int Q_{n,m}, so
    N(n,m) >= w(h_{n,m}) >= N(n,s).
  - Corollary 8.17 (p.106): every tight representation is first-caliber.
  - Proposition 8.38 (p.114): spherical t-design <-> first-caliber
    representation equivalence.

- **Landsberg 2017:** *Geometry and Complexity Theory.*
  Cambridge Studies in Advanced Mathematics, Vol. 169.
  - Section 6.2.2 (line 9546): catalecticant = flattening =
    method of partial derivatives (for symmetric tensors).
  - Section 8.2.1 (line 15207): Young flattenings as generalizations.
  - Theorem 2.5.2.6 (line 2367): R(M<n>) >= 2n^2 - n from Koszul
    flattenings [LO15].

- **Christandl--Vrana--Zuiddam (CVZ), arXiv:1709.07851:**
  *Universal points in the asymptotic spectrum of tensors.*
  STOC 2018 / JAMS 2023.
  - Theorem 4.14 (line 2655): for free tensors,
    rho^theta = E^theta = E_theta.
  - Line 2053: tight implies oblique implies free.
  - Section 4.3, Example (line 2783): format (ab,bc,ca) is
    comfortable; support of <a,b,c> with uniform P gives
    marginals uniform on [ab], [bc], [ca].

- **Christandl--Lysikov--Zuiddam (CLZ), arXiv:2012.14412:**
  *Weighted slice rank and a minimax correspondence to Strassen's
  spectra.* J. Math. Pures Appl.
  - Theorem 4 / Corollary 3.8 (lines 420, 673): T in C^{m_1 x m_2 x m_3}
    is semistable iff G_xi(T) = min_i m_i^{1/xi_i} for every xi,
    where m_i = dim(V_i) (ambient dimensions, not flattening ranks).
  - Lemma 3.3 (line 636): semistability test -- if T is invariant
    under a group acting irreducibly on each V_i, then T is semistable.
  - Example (line 643): <n_1,n_2,n_3> is semistable (in fact
    polystable) via the sandwiching action.
  - Theorem 3 (minimax, line 221): G_xi <-> F_theta correspondence.
