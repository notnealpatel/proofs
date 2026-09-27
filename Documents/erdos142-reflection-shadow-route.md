# Erdős 142 reflection-shadow route: current frontier

> **Status.** This is a bounded route record, not a solution of Erdős problem 142 and not a global novelty claim. It separates kernel-checked finite theorems, independently audited but informal finite mathematics, exploratory computation, and the open conjectural estimate. The canonical problem asks for an asymptotic formula for the progression-free-set extremal function; none of the results below supplies one.

## 1. Kernel-checked core

At accepted revision `66eca70dc75c548dcf27862d0f8c8bcc5e436f67`, `Proofs/Erdos/Erdos142/ReflectionShadow.lean` is imported by `Proofs/Erdos.lean`. For a finite `A : Finset ℤ`, it defines `Erdos142.reflectionShadow A`, consisting of the values `2*a-b` for `a,b ∈ A` with `a ≠ b`, and `Erdos142.differenceSources A d`, consisting of `x ∈ A` with `x+d ∈ A`.

The module proves:

1. If `A` is ordinary 3-AP-free, then `A` is disjoint from `reflectionShadow A`. A shadow point gives `b + (2*a-b) = a+a`, and freeness forces the distinct `a,b` to coincide.
2. For every nonzero integer `d`,
   \[
   2\,|\{x\in A:x+d\in A\}|\le |A|.
   \]
   The source set and its translate by `d` are disjoint equal-cardinality subsets of `A`.

The exact public endpoints are `disjoint_reflectionShadow`, `two_mul_card_differenceSources_le`, and `card_differenceSources_le_half`. Focused and full umbrella builds succeeded (8814 jobs); the public endpoints have only `[propext, Classical.choice, Quot.sound]`. Independent mathematical review was **CLEAN**. The vacuity audit found no semantic or trust issue; some additional scratch cardinality probes did not complete and are not integrated into the formal development.

**Boundary of the formal result:** this module does not formalize any base-`N` carry-union identity, median-shadow bound, representation-mass or energy identity, or the candidate estimate below. It is a finite integer-set kernel, not an asymptotic statement about `r(N)`.

## 2. Informal finite mathematics (independently audited; not Lean formalized)

Use the convention `[0,N²)={0,1,…,N²−1}`. Let `A ⊆ [0,N²)` be scalar 3-AP-free and write `m=|A|`. Let
\[
 S(A)=\{2a-b:a,b\in A,\ a\ne b\}\cap[0,N^2).
\]
The target-wise valid union of the base-`N` carry cases is exactly this in-range, nontrivial reflection shadow. This is a statement about the union of all valid carry modes, not a claim that a single coordinatewise progression test captures scalar progressions. Since `A` is disjoint from its nontrivial shadow,
\[
 |S(A)|\le N^2-m.
\]

A median-reflection argument also gives
\[
 |S(A)|\ge \left\lfloor\frac{m-1}{2}\right\rfloor.
\]
Choose a median element as the reflection center and use the side of it on which reflection stays in the interval; the selected images are distinct and, by scalar freeness, outside `A`. This is an informal finite argument, not part of `ReflectionShadow.lean`.

For each in-range target `c`, let `ν(c)` count the **ordered** nontrivial representations `c=2a-b` with `a,b∈A`, `a≠b`. Put
\[
 M=\sum_{0\le c<N^2}\nu(c),\qquad E=\sum_{0\le c<N^2}\nu(c)^2,
 \qquad r_A(d)=|\{x\in A:x+d\in A\}|.
\]
The route's counting gives useful lower bounds on the in-range mass `M` in the regime `m>N`; these are informal and must retain the stated in-range target convention (boundary losses matter). The collision count gives
\[
 E\le M+\sum_{d\ne0}r_A(d)r_A(2d)
   \le \sum_{d\in\mathbb Z}r_A(d)r_A(2d),
\]
where the difference sums range over all integers and `r_A(0)=m`. For the first inequality, diagonal pairs of representations contribute `M`; an off-diagonal collision with first-center difference `d` requires a pair at difference `d` and another at difference `2d`. The second inequality uses `M\le m^2=r_A(0)^2`.

The formal fixed-difference theorem above is exactly the fact
\[
 r_A(d)\le \lfloor m/2\rfloor\quad(d\ne0)
\]
available to this energy calculation. Applying that cap naively to the sum is much too weak: it does not control the overlap of the `d` and `2d` difference structures tightly enough.

## 3. Exploratory candidate and its conditional consequence

**Conjectural, not proved:** for every scalar-free `A⊆[0,N²)` with `m>N`, the candidate estimate is
\[
 \boxed{\quad |S(A)|^3\,r(N)^8\ \ge\ N^2(m-N)^6.\quad}
 \tag{C}
\]
If true, combining it with `|S(A)|≤N²-m≤N²` yields
\[
 m\le N+N^{2/3}r(N)^{4/3}.
\]
For the usual eventual Behrend lower bound on `r(N)`, this would imply
\[
 r(N^2)\le N+N^{2/3}r(N)^{4/3}
       \le 2N^{2/3}r(N)^{4/3}
\]
eventually. This is a P-shaped square gain with `η=1/3`, within the necessary range `η≤√2−1`. It would be an intermediate estimate only, not a full asymptotic formula for Erdős 142. **Conditional significance:** if an eventual P bound with `η=1/3` held with fixed constant `C`, then `λ(N²)≥(4/3)λ(N)−log C`; using `λ(M)→∞` to choose a sufficiently large fixed `M` and iterating only at `N=M^{2^k}` gives `λ(M^{2^k})≥c_M(4/3)^k` eventually, i.e. a lower bound of order `(log M^{2^k})^{log₂(4/3)}` on that tower (exponent about `0.415`). This makes (C) a potentially major intermediate advance, but asserts neither an all-`N` interpolation nor a solution of Erdős 142.

The candidate is informally checked in the `N=3` case, in eventual fixed-linear regimes `m≤K N` for fixed `K`, and on short ternary Cartesian products. Exhaustive tests through `N≤6` and structured searches are **computation only**. None proves (C), and no search is evidence of a universal theorem.

## 4. Open second-moment step and the exact obstruction

A sufficient route to (C) would be the following overlap estimate, still **unproved and undisproved** for `m>N`:
\[
 E\le \frac{M^2 r(N)^{8/3}}
              {N^{2/3}(m-N)^2}.
 \tag{O}
\]
Indeed, Cauchy gives `E≥M²/|S(A)|` when `M>0`; combining with (O) yields (C). No counterexample to (O) has been found, but the search evidence is only exploratory. A capped-at-2 moment variant is also unproved; at most it is within a factor `9/8` of the desired support bound and must not be advertised as an independent breakthrough.

The precise structural obstacle is that fixed-difference edges form matchings, whereas fixed-target reflections need not. For example, the scalar-free set
\[
 A=\{1,2,4,8\}\subset[9]
\]
has three representations of target zero: `2·1−2=2·2−4=2·4−8=0`, so `ν(0)=3`. Thus the fixed-difference matching/source theorem does not bound fixed-target multiplicities. It supplies an exact local ingredient for the energy sum, but not the missing overlap estimate.

## 5. Relationship to the wider route and stop conditions

This route retains target locations through `S(A)`, unlike a scalar-free relaxation that only retains ordinary row/column freeness and fiber-size caps. The latter has the separate kernel-checked counterexample recorded in [`erdos142-carry-cardinality-obstruction.md`](erdos142-carry-cardinality-obstruction.md): the relaxed conditions permit cardinality at least `N r(N)/2` and cannot alone yield a universal `o(Nr(N))` bound. Carry information therefore cannot simply be discarded.

The `η=1/3` consequence conditional on (C) is inside the current consistency limit; it does not repeat the ruled-out `η=1/2` route. For the comparison with known negative square defects and the endpoint `η≤√2−1`, see the carry obstruction note and [`erdos142-negative-defect-density.md`](erdos142-negative-defect-density.md). The density theorem there is kernel checked, but gives no proof of (C) or (O).

**Current frontier:** the formal reflection and source-counting lemmas are established; the carry union, median bound, and representation-energy bookkeeping are independently audited informal mathematics; (C) and sufficient step (O) remain conjectural. No global novelty claim is made, and there is no claim to have solved or disproved Erdős 142.
