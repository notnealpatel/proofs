# Erdős Problem Candidates — Mining Sweep 2026-08-05

The repo has eight Erdős-numbered results landed or partial
(#20, #21, #175, #440, #542, #715, #857, #880) plus the
covering-system lane (#1142, Sierpiński, Riesel, Erdős 1950).
This sweep mines the `goof erdos` database (1217 problems) for
the next wave: solved-but-unformalized proof targets, disproved
problems with small certificates, and famous open problems
worth archiving with sanity layers.

Method: full status inventory via `goof erdos list`; `show`
sweeps over all 225 solved/proved/disproved problems with
`formalized=no`, all decidable/falsifiable problems, and all
open problems numbered <= 130; topic searches; then a paired
advocate/skeptic evaluation with leandoc-grounded Mathlib gap
checks. All statements below are quoted from `goof erdos show`
digests, not from model memory. Caveat: the search index only
covers tags/comments (11 of 20 natural queries return zero
hits), so status-based sweeps did the heavy lifting.

## Database Statistics

- Total problems: 1217
- Status: open 604, proved 210, proved (Lean) 120, solved 71,
  disproved 69, disproved (Lean) 63, falsifiable 27,
  solved (Lean) 23, decidable 9, verifiable 7, open (Lean) 4,
  not disprovable 4, not provable 3, independent 3
- Formalized flag: yes 581, no 636. The "(Lean)" statuses mark
  problems already formalized elsewhere (formalizederdosproblems
  ecosystem) — excluded as targets.
- Prime hunting ground: 225 problems solved/proved/disproved
  with `formalized=no`; all were individually inspected.

## Candidates

### Tier A — Proof targets (solved problems, formalizable with current Mathlib)

#### Erdős #1213 — equal-sum intervals in bounded-gap sequences
- **Status**: proved
- **Statement**: "Let $a,K\geq 1$. Does there exist $f(a,K)$
  such that if $a=a_1<\cdots<a_s$ with $a_s>f(a,K)$ and
  $a_{i+1}-a_i\leq K$, then two distinct intervals have equal
  sums?"
- **Solved by**: Hegyvári (1986), with $f(a,K) \ll a e^{O(K)}$
- **Repo adjacency**: pure `Finset.Icc`/`Finset.sum`
  vocabulary; same toolkit as `Proofs/Enumerative/` (NederGap,
  StanleyDigits)
- **Lean feasibility**: pigeonhole on interval-sum residues;
  zero new definitions. Best payoff-per-effort in the sweep.
- **Effort**: S

#### Erdős #384 — small prime divisor of binomial coefficients
- **Status**: proved
- **Statement**: "If $1 < k < n-1$ then $\binom{n}{k}$ is
  divisible by a prime $p < n/2$ (except $\binom{7}{3}=35$)."
  ⚠ DB statement is doubly off vs Ecklund's actual theorem
  (per comment thread, JoshuaB Feb 2026): Ecklund has
  $n \ge 2k$ and $p \le n/2$ (non-strict); with strict
  $p < n/2$ the case $(4,2)$ fails, and the range $1<k<n-1$
  also misses the symmetric exception $\binom{7}{4}$.
  The Lean sketch formalizes Ecklund's corrected form.
- **Solved by**: Ecklund (1969)
- **Repo adjacency**: Kummer-theorem machinery in
  `Proofs/Erdos/Erdos175/NotSquarefree.lean`; `Nat.bertrand`
  in Mathlib
- **Lean feasibility**: clean `Nat.choose` statement with one
  finite exception; elementary proof. Skeptic survived with
  low residual risk.
- **Effort**: S

#### Erdős #1058 — prime factors of n!+1
- **Status**: proved
- **Statement**: "Are there only finitely many $n$ with
  $n\in[p_{k-1},p_k)$ such that the only prime divisors of
  $n!+1$ are $p_k$ and $p_{k+1}$? The only known cases are
  $n=1,2,3,4,5$."
  NB: the "$p_k$ and $p_{k+1}$" indexing is the corrected
  form per Tao (Sep 2025 comment); the original statement
  used "$p_{k-1}$ and $p_k$", which is a typo — $n!+1$ is
  never divisible by a prime $\le n$.
- **Solved by**: Luca (2001) — these are the only solutions
- **Repo adjacency**: certificate-then-tail pattern from
  `Proofs/Erdos/Covering/ErdosMinus2k.lean`
- **Lean feasibility**: five `decide` certificates plus a
  4-page elementary tail argument (factorial divisibility +
  Bertrand). Full closure of an Erdős problem is plausible.
- **Effort**: M

#### Erdős #482 — Graham–Pollak recurrence and binary sqrt(2)
- **Status**: solved
- **Statement**: "Define $a_1=1$,
  $a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor$. The difference
  $a_{2n+1}-2a_{2n-1}$ is the $n$th digit in binary expansion
  of $\sqrt 2$."
- **Solved by**: Graham–Pollak (original); Stoll (2005, 2006)
  for generalizations
- **Repo adjacency**: `Nat.floor`, `Real.sqrt` from Mathlib;
  `native_decide` ground checks for initial terms
- **Lean feasibility**: concrete computable recurrence with a
  short inductive proof. Skeptic flags the floor-arithmetic
  to binary-expansion bridge as fiddly but feasible.
- **Effort**: M

#### Erdős #916 — cycles with an attached 3-neighbor vertex
- **Status**: proved
- **Statement**: "Does every graph with $n$ vertices and
  $2n-2$ edges contain a cycle and another vertex adjacent to
  three vertices on the cycle?"
- **Solved by**: Thomassen (1974), ~5 page direct argument
- **Repo adjacency**: `SimpleGraph` experience from Erdos715
- **Lean feasibility**: `Walk.IsCycle` + neighborhood
  intersection compose the statement; no off-the-shelf lemma
  but all primitives exist. Medium risk of Walk-API friction.
- **Effort**: M

#### Erdős #58 — chromatic number vs odd cycle lengths
- **Status**: proved
- **Statement**: "If $G$ is a graph which contains odd cycles
  of $\leq k$ different lengths then $\chi(G)\leq 2k+2$, with
  equality iff $G$ contains $K_{2k+2}$."
- **Solved by**: Gyárfás (1992)
- **Repo adjacency**: `SimpleGraph.chromaticNumber` and
  `Walk.IsCycle` exist in Mathlib
- **Lean feasibility**: prove the $\chi \le 2k+2$ headline
  first and sorry the equality characterization; the
  2-connected structural argument is elementary but the
  odd-cycle-length set needs careful plumbing.
- **Effort**: M (headline), L (with equality case)

### Tier B — Archive targets (open or certificate-style, good sanity layers)

#### Erdős #1140 — n - 2x^2 always prime
- **Status**: disproved
- **Statement**: "Do infinitely many n exist such that
  $n-2x^2$ is prime for all $x$ with $2x^2 < n$?"
- **Partial results**: known members {2,5,7,13,31,61,181,199};
  finiteness by Mollin–Williams (1989), Epure–Gica (2010) via
  class number bounds (at most one further exception)
- **Repo adjacency**: exactly the `ErdosMinus2k.lean` shape:
  predicate, certificates, finite window, archived conjecture
- **Sanity layer**: eight `decide` certificates plus a
  `native_decide` window; completeness sorry'd (class number
  theory out of scope)
- **Effort**: S

#### Erdős #781 — descending waves
- **Status**: disproved
- **Statement**: "Is $f(k)=k^2-k+1$ for descending waves
  (monochromatic in 2-colourings of $\{1,\ldots,n\}$)?"
- **Partial results**: Brown–Erdős–Freedman proved
  $f(k)\ge k^2-k+1$; Alon–Spencer (1989) proved
  $f(k)\gg k^3$, killing equality
- **Sanity layer**: a 2-coloring certificate at the first
  failing k. k=4 means 2^13 colorings, k=5 means 2^21 — both
  `native_decide` range. Risk: the first failing k is not
  documented in the DB entry; probe with sage before
  committing (Alon–Spencer is asymptotic, small k could
  still satisfy equality).
- **Effort**: S (after the probe)

#### Erdős #993 — unimodal independent-set sequences of trees
- **Status**: falsifiable
- **Statement**: "The independent set sequence of any tree or
  forest is unimodal." (False for general graphs by
  Alavi–Malde–Schwenk–Erdős 1987; open for trees.)
- **Partial results**: none for trees; DB status
  "falsifiable" signals an expected finite counterexample
- **Sanity layer**: `native_decide` unimodality sweep over
  all trees on <= 15 vertices. Either outcome is publishable
  progress: a counterexample resolves the problem; a clean
  sweep is a verified partial result.
- **Effort**: S

#### Erdős #405 — (p-1)! + a^(p-1) = p^k
- **Status**: proved
- **Statement**: "Let $p$ be an odd prime.
  $(p-1)!+a^{p-1}=p^k$ has only finitely many solutions."
- **Solved by**: Brindza–Erdős (1991); complete resolution
  Yu–Liu (1996)
- **Sanity layer**: verify the known solution list by
  `decide`; archive finiteness with sorry (Baker's method is
  absent from Mathlib). Fidelity warning from the skeptic
  pass: the DB's example solutions involve p=2, which the
  "odd prime" hypothesis excludes — pin down the exact
  odd-p solution set from Yu–Liu before stating.
- **Effort**: S

#### Erdős #895 — independent {a, b, a+b} in triangle-free graphs
- **Status**: proved
- **Statement**: "For all sufficiently large $n$, if $G$ is a
  triangle-free graph on $\{1,\ldots,n\}$ then must there
  exist three independent points $a,b,a+b$?"
- **Solved by**: Barber (personal communication), SAT-verified
  for all $n\ge 18$
- **Partial results / sanity layer**: explicit small-n
  counterexample graphs (n < 18) are formalizable now; the
  universal n >= 18 direction needs verified SAT certificate
  replay (DRAT checking), which the repo lacks. Archive the
  statement, land the small-n layer, revisit if LRAT
  infrastructure arrives.
- **Effort**: M

#### Erdős #86 — C4-free subgraphs of the hypercube
- **Status**: open
- **Statement**: "Is it true that every subgraph of the
  n-dimensional hypercube $Q_n$ with
  $\geq(1/2+o(1))n2^{n-1}$ edges contains a $C_4$?"
- **Partial results**: Brass–Harborth–Nienborg (1995) lower
  construction; Baber (2012) 0.60318 upper; explicit C4-free
  certificates for Q9–Q15 (rafalwrona 2026)
- **Sanity layer**: define Q_n over `Fin n -> Bool`, verify
  C4-freeness of explicit edge-list certificates for small n
  by `native_decide`; archive the threshold conjecture
- **Effort**: M

#### Erdős #81 — clique partitions of chordal graphs
- **Status**: open
- **Statement**: "Can the edges of any chordal graph on n
  vertices be partitioned into $n^2/6+O(n)$ cliques?"
- **Partial results**: Erdős–Ordman–Zalcstein (1993)
  $(1/4-\varepsilon)n^2$; Chen–Erdős–Ordman (1994) split
  graphs $3n^2/16+O(n)$; a $(1/4-1/133)n^2$ bound already
  formalized in Lean externally (Woett, June 2026)
- **Sanity layer**: archive conjecture; the split-graph
  subcase is the natural provable slice. Check Woett's
  external repo first to avoid duplication.
- **Effort**: M

#### Erdős #5 — limit points of normalized prime gaps
- **Status**: open
- **Statement**: "Is the set S of limit points of
  $(p_{n+1}-p_n)/\log n$ equal to $[0,\infty]$?"
- **Partial results**: $\infty \in S$ (Westzynthius 1931),
  $0 \in S$ (Goldston–Pintz–Yıldırım 2009), positive measure
  (Erdős 1955, Ricci 1956), >= 1/3 density (Merikoski 2020)
- **Sanity layer**: statement archive with `Nat.nth`
  `Nat.Prime` + `Filter.limsup`; computational prime-gap
  ratio checks. The named partial results are deep — archive
  only. OEIS A001223.
- **Effort**: M (statement + sanity only)

### Tier C — Infrastructure-adjacent (new defs, connect to existing work)

#### Erdős #702 — Frankl's forbidden singleton intersection
- **Status**: proved
- **Statement**: "Let $k\geq 4$. If $\mathcal F$ is a family
  of k-element subsets of $\{1,\ldots,n\}$ with
  $|\mathcal F| > \binom{n-2}{k-2}$ then there are
  $A,B\in\mathcal F$ with $|A\cap B|=1$."
- **Solved by**: Frankl (1977); Katona (k=4, unpublished)
- **Repo adjacency**: compression operators in
  `Proofs/Erdos/Erdos20/Sunflower.lean`; the
  forbidden-1-intersection variant needs its own shifting
  lemma, so reuse is partial
- **Lean feasibility**: clean `Finset (Finset (Fin n))`
  statement now; the shifting lemma is the new
  infrastructure, and it would deepen the extremal set
  theory lane beyond sunflowers
- **Effort**: M–L

#### Erdős #77 — growth of diagonal Ramsey numbers
- **Status**: open
- **Statement**: "Does $\lim R(k)^{1/k}$ exist? If so,
  determine its value."
- **Partial results**: $\sqrt 2 \le \liminf \le \limsup \le 4$
  (Erdős, classical); $4 - 1/128$
  (Campos–Griffiths–Morris–Sahasrabudhe 2023); 3.7992
  (Gupta–Ndiaye–Norin–Wei 2024)
- **Lean feasibility**: R(k) is not in Mathlib; the
  definition is ~50 lines and unlocks #781 and #112 too.
  The classical bounds (probabilistic lower, pigeonhole
  upper) are genuine formalizable theorems. OEIS A059442.
- **Effort**: M

#### Erdős #834 — 3-critical 3-uniform hypergraph, min degree 7
- **Status**: solved
- **Statement**: "Does there exist a 3-critical 3-uniform
  hypergraph with every vertex of degree $\geq 7$?"
- **Solved by**: Li (2025) — yes under chromatic criticality
  (explicit 9-vertex construction); no under transversal
  criticality
- **Lean feasibility**: no hypergraph type in Mathlib, but a
  3-uniform hypergraph on 9 vertices is a small `Finset`
  structure; 3^9 colorings makes criticality checking
  `native_decide`-sized. Definitional layer is the cost;
  it would seed a hypergraph lane the repo currently lacks.
- **Effort**: M

#### Erdős #112 — independent sets vs transitive subtournaments
- **Status**: open
- **Statement**: "Determine $k(n,m)$ = min N such that any
  directed graph on N vertices contains either an independent
  set of size n or a transitive tournament of size m."
- **Partial results**: Erdős–Rado (1967) upper bound;
  Larson–Mitchell (1997) $k(n,3)\le n^2$; Hunter–Steiner
  exact $k(n,m)=(n-1)(m-1)$ for the directed-path variant
- **Lean feasibility**: no tournament infrastructure in
  Mathlib (~100 lines to build); the Hunter–Steiner path
  variant is a self-contained exact theorem — the right
  first slice
- **Effort**: M

#### Erdős #130 — integral distances and the Anning–Erdős theorem
- **Status**: open
- **Statement**: "Let A be an infinite set in $R^2$ with no 3
  collinear, no 4 concyclic ... How large can the chromatic
  number [of the integer-distance graph] be? Can it be
  infinite?"
- **Partial results**: Anning–Erdős (1945): an infinite set
  in $R^2$ with all pairwise distances integral must be
  collinear
- **Lean feasibility**: the main question is wide open; the
  Anning–Erdős theorem itself is the target — a classic,
  self-contained Euclidean argument. Requires plane-geometry
  work with `EuclideanSpace`, a lane the repo has not opened.
- **Effort**: M–L

#### Erdős #80 — edges in many triangles
- **Status**: open
- **Statement**: "Let $f_c(n)$ = max m such that every
  n-vertex graph with $\geq cn^2$ edges where every edge is
  in a triangle has an edge in $\geq m$ triangles. Estimate
  $f_c(n)$."
- **Partial results**: Fox–Loh (2012) kill the $n^\epsilon$
  conjecture for c < 1/4; Edwards / Khadzhiivanov–Nikiforov
  (1979): $f_c(n)\ge n/6$ for c > 1/4
- **Lean feasibility**: the c > 1/4 threshold is the clean
  slice but leans on a Turán-type theorem not in Mathlib.
  Archive plus the Turán prerequisite, or defer.
- **Effort**: M–L

#### Erdős #673 — divisor ratio sums
- **Status**: proved
- **Statement**: "Let $d_1<\cdots<d_{\tau(n)}$ be divisors of
  n and $G(n)=\sum_{i<\tau(n)} d_i/d_{i+1}$. Is it true that
  $G(n)\to\infty$ for almost all n?"
- **Solved by**: Tao — trivial from
  $\tau(n)/4 \le G(n) \le \tau(n)$ (for even n)
- **Lean feasibility**: `Nat.divisors` Finset sum; the
  pointwise inequality is a clean one-file target. The
  "almost all" density framing needs `Nat`-density
  primitives Mathlib mostly lacks — prove the inequality,
  archive the density claim.
- **Effort**: S (inequality), L (density)

### Tier D — Interesting but heavy

#### Erdős #577 — vertex-disjoint 4-cycles
- **Status**: proved
- **Statement**: "If $G$ has $4k$ vertices and minimum degree
  $\geq 2k$, then $G$ contains $k$ vertex-disjoint 4-cycles."
- **Solved by**: Wang (2010)
- **Lean feasibility**: statement is clean but the proof is
  ~45 pages of case analysis, and Mathlib has no
  vertex-disjoint cycle packing layer. Statement archive at
  most; the full proof is a campaign, not a lane.
- **Effort**: L

#### Erdős #439 — monochromatic pairs summing to a square
- **Status**: proved
- **Statement**: "In any finite colouring of the integers,
  there exist $x\neq y$ same colour with $x+y$ a square."
- **Solved by**: Khalfalah–Szemerédi (2006)
- **Lean feasibility**: density-Ramsey proof is out of reach;
  finite instances ("any 2-coloring of {1..N} works") are
  `native_decide`-checkable for specific N as a sanity
  layer under an archived statement.
- **Effort**: L (proof), S (archive + instances)

#### Erdős #362 — subset-sum concentration
- **Status**: proved
- **Statement**: "Let $A\subseteq\mathbb N$ be finite of size
  N. For fixed t,
  $|\{S\subseteq A: \sum_{n\in S} n = t\}| \ll 2^N/N^{3/2}$."
- **Solved by**: Sárközy–Szemerédi (1965); Halász (1977) for
  the sharper fixed-size version
- **Lean feasibility**: clean Finset statement; the
  Littlewood–Offord-adjacent proof is real work. Mathlib has
  some Littlewood–Offord material worth checking via leandoc
  before scoping. Archive + small-N checks first.
- **Effort**: L

## Rejected after audit

These were rated STRONG by the first-pass sweep and killed by
the skeptic audit; recorded so the next sweep does not redo
the work.

- **#631** (Thomassen 5-choosability): Mathlib has zero
  planarity infrastructure and no list-chromatic definitions;
  both are multi-month prerequisites. The famous 1-page proof
  is not the bottleneck.
- **#758** (cochromatic z(12)=4): no cochromatic number in
  Mathlib and the underlying computation enumerates ~10^8
  12-vertex graphs — outside `native_decide` territory
  without a verified enumeration engine.
- **#1187** (monochromatic prime-difference APs): the mod-4
  counterexample is already formalized in Lean 4 (KitaKen1);
  the other half is Green–Tao. Citation, not a target.
- **#104** (unit circles through triples): open, with nothing
  proved beyond the trivial n(n-1)/3 double-count; even the
  archive value is marginal without a geometry lane.

## Already covered (skipped)

- Fully proved in repo: #440 (`Erdos440/LcmCount.lean`),
  #542 (`Erdos542/SchinzelSzekeres.lean`),
  #715 (`Erdos715/RegularSubgraph.lean`),
  #880 (`Erdos880/BurrErdos.lean`), #857 bound
  (`Erdos857/NaslundSawin.lean`), Erdős 1950 + Sierpiński +
  Riesel (`Erdos/Covering/`). The DB still lists #440, #542,
  #715, #880 as `formalized=no` — worth reporting upstream.
- Partial in repo: #20 (shifted case + spread lemma),
  #21 (g(1..3) proved, g(4..6) archived), #175 (n <= 2^30;
  remainder needs exponential sums), #1142 (certificates +
  10^9 window; conjecture archived).
- Queued in PLAN.md: #274, #278, #1188, #1189 (covering
  lane C4/C5).
- Upstream `formal-conjectures` owns: #7, #203, #204,
  #273–#277, #279–#281, #1113 — do not duplicate.

## Cross-references

OEIS anchors for candidates: #5 -> A001223 (prime gaps),
#77 -> A059442 (diagonal Ramsey), #86 -> A245762,
#482 -> A004539 (binary digits of sqrt 2). Repo OEIS cards
already bridging Erdős problems: A039669/A089654 (#1142),
A391599 (#21), A046098 (#175), A332077 (#20), A236397
(#857-adjacent). The #993 tree sweep and #781 wave probe are
natural companions to the OEIS mining sweep: both produce
sequence-shaped computational data (independent-set
polynomials; descending-wave extremal colorings) that may
match or extend existing OEIS entries.

## Provenance

Statements quoted verbatim from `goof erdos show` sweep
digests (2026-08-05). Tier and effort calls reconcile a
paired advocate/skeptic evaluation; where they disagreed the
skeptic's leandoc-verified Mathlib gap findings won. Residual
uncertainty is flagged inline (#781 first failing k, #405
odd-p solution set, #81 external duplication).

## Unsolved Problems — Deep Sweep 2026-08-05

Method: full triage of all 661 unsolved-status entries
(status in {open, open (Lean), decidable, falsifiable,
independent, not disprovable, not provable, verifiable})
from `goof erdos list`, 12-way parallel `goof erdos fetch`
sweep scored against repo infrastructure, a second
extraction pass over 34 finalists, and an adversarial
audit of every Tier-UA placement (verdicts folded in
below; disagreements noted inline). Statements are
verbatim from the database. Numbers already covered in
this file or PLAN.md (#7 partially, #1188, #1189) are
handled where noted. Full triage TSVs and fetch cache in
session scratchpad `triage/`, `fetches/`.

### Tier UA — Attack surface exists (partial proof or sub-case realistic with current infra)

#### Erdős #699 — common prime factor of binomials
- **Status**: falsifiable
- **Statement**: "Is it true that for every $1\leq i<j\leq n/2$ there exists some prime $p\geq i$ such that $p\mid \textrm{gcd}\left(\binom{n}{i}, \binom{n}{j}\right)?$"
- **Partial results**: known true if $j\le\tfrac32 i$ or $n=2j$ (recent, AI-assisted, via the identity $\binom{n}{i}\binom{n-i}{j-i}=\binom{n}{j}\binom{j}{i}$). For fixed $i<j$ only finitely many $n$ can fail (easy). Extreme known case: $\gcd(\binom{28}{5},\binom{28}{14})=2^3\cdot3^3\cdot5$.
- **Attack surface**: the finiteness-per-$(i,j)$ observation, the $n=2j$ balanced case, and decidable verification for small $(i,j)$ — all plain binomial arithmetic on top of `Proofs/Erdos/Erdos175`. Audit verdict: keep.
- **Infrastructure needed**: binomial gcd/valuation lemmas; nothing new.
- **OEIS link**: none

#### Erdős #1063 — near-uniform divisibility of C(n,k) by n-i
- **Status**: open
- **Statement**: "Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$ such that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$. Estimate $n_k$."
- **Partial results**: Erdős–Selfridge [ErSe83] (proof in Monier [Mo85]): for $n\ge2k$ some $0\le i<k$ has $(n-i)\nmid\binom{n}{k}$, so "all but one" is optimal. Known $n_2=4$, $n_3=6$, $n_4=9$, $n_5=12$; $n_k\le k!$ (Monier); $n_k\le k\,\mathrm{lcm}(2,\dots,k-1)$ (Cambie, comments).
- **Attack surface**: the Erdős–Selfridge non-divisibility lemma is self-contained; $n_2=4$, $n_3=6$ are `decide`-scale; the lcm upper bound sits on `Proofs/Erdos/Erdos440` LcmCount. (Not in the audit batch; confidence self-assessed high — all fragments are finite or elementary.)
- **Infrastructure needed**: nothing beyond BINOM + LCM layers.
- **OEIS link**: A389360

#### Erdős #1062 — no a|b, a|c triples
- **Status**: open
- **Statement**: "Let $f(n)$ be the size of the largest subset $A\subseteq \{1,\ldots,n\}$ such that there are no three distinct elements $a,b,c\in A$ such that $a\mid b$ and $a\mid c$. How large can $f(n)$ be? Is $\lim f(n)/n$ irrational?"
- **Partial results**: interval $[m+1,3m+2]$ gives $f(n)\ge\lceil 2n/3\rceil$; Lebensold [Le76]: $0.6725n\le f(n)\le0.6736n$ for large $n$.
- **Attack surface**: the $\lceil2n/3\rceil$ lower bound via the explicit interval is elementary divisibility-poset reasoning; small exact $f(n)$ values are decidable. (Not in audit batch; self-assessed high confidence for the lower bound only.)
- **Infrastructure needed**: none new (Finset divisibility combinatorics).
- **OEIS link**: A038372

#### Erdős #856 — equal pairwise lcms and weak sunflowers
- **Status**: open
- **Statement**: "Let $k\geq 3$ and $f_k(N)$ be the maximum value of $\sum_{n\in A}\frac{1}{n}$, where $A$ ranges over all subsets of $\{1,\ldots,N\}$ which contain no subset of size $k$ with the same pairwise least common multiple. Estimate $f_k(N)$."
- **Partial results**: Erdős [Er70]: $f_k(N)\ll(\log N)/(\log\log N)$. Tang–Zhang (2025): $(\log N)^{0.438}\le f_3(N)\le(\log N)^{0.889}$; the upper exponent is $<1$ iff the sunflower conjecture (#857) holds for $k$-sunflowers.
- **Attack surface**: the Er70 upper bound is a short prime-counting inequality; the Tang–Zhang bridge makes this the natural second client of the `Proofs/Erdos/Erdos857` Naslund–Sawin layer. Audit verdict: keep — both directions reduce to SUNFLOWER/SLICE assets already landed.
- **Infrastructure needed**: Chebyshev-type prime counting (Mathlib has it); lcm-pattern-to-set-system encoding defs.
- **OEIS link**: none listed

#### Erdős #535 — same pairwise gcd
- **Status**: open
- **Statement**: "Let $r\geq 3$, and let $f_r(N)$ denote the size of the largest subset of $\{1,\ldots,N\}$ such that no subset of size $r$ has the same pairwise greatest common divisor between all elements. Estimate $f_r(N)$."
- **Partial results**: Erdős [Er64]: $f_r(N)\le N^{3/4+o(1)}$, improved by Abbott–Hanson to $N^{1/2}$-order; ALWZ sunflower bounds give $f_r(N)\le N^{o(1)}$; 2026 block construction gives $\exp((\log(r-1)+o(1))\log N/\log\log N)$ below.
- **Attack surface**: encode $n\mapsto\{(p,j):j\le v_p(n)\}$; $r$ elements with equal pairwise gcds become an $r$-sunflower. Pushing the repo's Erdős–Rado bound through this encoding yields an explicit (weaker than ALWZ, still nontrivial) upper bound on $f_r(N)$ — a genuinely new formal artifact. Audit verdict: promoted to UA on exactly this reduction.
- **Infrastructure needed**: the prime-power encoding and a translation lemma; sunflower side exists.
- **OEIS link**: none listed

#### Erdős #273 — covering system with moduli p-1
- **Status**: open
- **Statement**: "Is there a covering system all of whose moduli are of the form $p-1$ for some primes $p\geq 5$?"
- **Partial results**: Selfridge: allowing $p\ge3$, a covering exists using divisors of 360. Site comment (Jul 2026): any $p\ge5$ covering needs a modulus with $p>877$; $\sum1/(p-1)$ must exceed 1 by an explicit margin (via Filaseta–Kalogirou).
- **Attack surface**: verify the Selfridge $p\ge3$ certificate with the existing `Proofs/Erdos/Covering` layer; state the $p\ge5$ question as the open boundary. The $p>877$ obstruction is a large finite claim — gate on a scaled `decide` probe first (C6 lesson). Audit verdict: keep.
- **Infrastructure needed**: modulus-set-restricted covering def; certificate layer exists.
- **OEIS link**: none

#### Erdős #276 — composite Lucas sequence without covering obstruction
- **Status**: open
- **Statement**: "Is there an infinite Lucas sequence $a_0,a_1,\ldots$ where $a_{n+2}=a_{n+1}+a_n$ for $n\geq 0$ such that all $a_k$ are composite, and yet no integer has a common factor with every term of the sequence?"
- **Partial results**: Graham [Gr64]: all-composite Lucas sequence via covering systems; Vsemirnov's smaller seeds $a_0=106276436867$, $a_1=35256392432$. Ismailescu–Son (2014): candidate answer with even terms composite by covering and odd terms factored algebraically; conjectural because covering non-responsibility is unproved.
- **Attack surface**: verifying the Vsemirnov certificate is the same `IsFibonacciLike` alpha-layer machinery PLAN.md lane C6 (A083216) is staging — this is a direct second instance once C6 lands. It formalizes the covering half; the headline stays open. (Not in audit batch; confidence high conditional on C6.)
- **Infrastructure needed**: C6 lane first; then reuse.
- **OEIS link**: none listed

#### Erdős #376 — central binomial coprime to 105
- **Status**: open, $1000 (Graham)
- **Statement**: "Are there infinitely many $n$ such that $\binom{2n}{n}$ is coprime to $105$?"
- **Partial results**: EGRS75: for any two odd primes $p,q$, infinitely many $n$ with $(pq,\binom{2n}{n})=1$. Bloom–Croot (2025): three large primes up to an $n^\epsilon$ factor. Kummer: equivalent to simultaneous digit conditions ($\{0,1\}$ base 3, $\{0,1,2\}$ base 5, $\{0,1,2,3\}$ base 7).
- **Attack surface**: narrowed after audit. The audit demoted the headline (multi-base digit distribution is deep); kept in UA only for the Kummer-equivalence theorem itself — coprimality iff digit conditions — which is finite carry-counting over `Nat.digits` and yields a reusable Kummer layer for #175/#699/#1093–#1095. The EGRS two-prime case is a stretch goal pending a read of the actual proof.
- **Infrastructure needed**: Kummer's theorem in Lean (the deliverable).
- **OEIS link**: A030979

#### Erdős #836 — intersecting 3-chromatic hypergraphs
- **Status**: open
- **Statement**: "Let $r\geq 2$ and $G$ be a $r$-uniform hypergraph with chromatic number $3$ (that is, there is a $3$-colouring of the vertices of $G$ such that no edge is monochromatic). Suppose any two edges of $G$ have a non-empty intersection. Must $G$ contain $O(r^2)$ many vertices? Must there be two edges which meet in $\gg r$ many vertices?"
- **Partial results**: Alon refuted the $O(r^2)$ vertex bound ($\sim4^r/\sqrt r$ vertices). Erdős–Lovász [ErLo75]: two edges share $\gg r/\log r$ vertices. Fano plane: edges need not meet in $r-1$ points. Audit notes a recent claimed short proof of the second question in the site comments (AI-assisted, reportedly reviewed) — verify against the live entry before treating the question as closed.
- **Attack surface**: same paper and same objects as the repo's `ErdosLovasz` g(k) work; the $r/\log r$ intersection bound is the concrete target, and small-$r$ instances are decidable. Audit verdict: keep.
- **Infrastructure needed**: intersecting-family + proper-2-coloring defs shared with #901.
- **OEIS link**: none

### Tier UB — Clean archive targets (open, statable, good sanity layer)

#### Erdős #7 — odd covering systems
- **Status**: verifiable (site status); no accepted proof. Selfridge $2000 for an explicit odd covering, Erdős $25 for nonexistence
- **Statement**: "Is there a distinct covering system all of whose moduli are odd?"
- **Partial results**: BBMST22: impossible with odd squarefree moduli; Hough–Nielsen: some modulus divisible by 2 or 3; multiple 2026 AI-assisted proofs posted and rejected (false axioms / gaps).
- **Attack surface**: PLAN.md already tracks `erdos_7` upstream (sorry'd, over `StrictCoveringSystem Z`); the contribution is the decidable restatement plus archiving the BBMST squarefree boundary. Given the rejected-proof churn, a trusted formal statement has unusual audit value.
- **Infrastructure needed**: squarefree-moduli predicate on the existing Covering layer.
- **OEIS link**: none

#### Erdős #203 — Sierpinski numbers coprime to 6
- **Status**: open
- **Statement**: "Is there an integer $m\geq 1$ with $(m,6)=1$ such that none of $2^k3^\ell m+1$ are prime, for any $k,\ell\geq 0$?"
- **Partial results**: no such $m$ up to $10^{11}$; 2026 comment: density necessary condition $\sum1/|H_p|\ge1$ for 2D covering sets, small-lcm coverings ruled out.
- **Attack surface**: archive only — audit confirmed demotion: the 2-generator subgroup structure $\langle2,3\rangle\le(\mathbb{Z}/p)^*$ is genuinely different from the 1D covering lane, and no decidable fragment is in reach. Worth stating as the exact 2D generalization of the repo's Sierpinski work.
- **Infrastructure needed**: two-parameter covering def over $(k,\ell)$.
- **OEIS link**: none

#### Erdős #242 — Erdős–Straus
- **Status**: falsifiable
- **Statement**: "For every $n>2$ there exist distinct integers $1\leq x<y<z$ such that $\frac{4}{n} = \frac{1}{x}+\frac{1}{y}+\frac{1}{z}.$"
- **Partial results**: verified to $10^{18}$ [MiDu25]; Mordell: true except possibly $n\equiv\{1,121,169,289,361,529\}\pmod{840}$; Elsholtz–Tao solution counts over primes.
- **Attack surface**: famous, so zero novelty in the statement — the value is the Mordell residue-class reduction (explicit per-class identities, fully elementary) plus a decidable small-$n$ layer.
- **Infrastructure needed**: none new.
- **OEIS link**: A073101, A075245, A075246, A075247, A075248, A287116

#### Erdős #406 — powers of 2 in base 3
- **Status**: open
- **Statement**: "Is it true that there are only finitely many powers of $2$ which have only the digits $0$ and $1$ when written in base $3$?"
- **Partial results**: only known cases $2^0,2^2,2^8$; Saye (2022) verified failure for $16\le n\le5.9\times10^{21}$; Narkiewicz: $N(x)\le1.62x^{\log_32}$.
- **Attack surface**: archive with a decidable `Nat.digits` sanity layer (three witnesses, finite verified ranges). Audit confirmed demotion of anything stronger: ternary digits of $2^n$ is known-hard Diophantine territory. Shares digit language with #376's Kummer layer.
- **Infrastructure needed**: none new.
- **OEIS link**: none listed

#### Erdős #677 — lcm of consecutive blocks
- **Status**: open
- **Statement**: "Let $M(n,k)=[n+1,\ldots,n+k]$ be the least common multiple of $\{n+1,\ldots,n+k\}$. Is it true that for all $m\geq n+k$ $M(n,k) \neq M(m,k)?$"
- **Partial results**: Thue–Siegel gives (ineffective) finiteness for fixed $k$; only known cross-$k$ coincidences $M(4,3)=M(13,2)$, $M(3,4)=M(19,2)$.
- **Attack surface**: statement plus the two coincidences as `decide` witnesses, directly on Erdos440. A proof needs effective Diophantine bounds — out of reach.
- **Infrastructure needed**: none new.
- **OEIS link**: none confirmed

#### Erdős #1020 — Erdős matching conjecture
- **Status**: falsifiable
- **Statement**: "Let $f(n;r,k)$ be the maximal number of edges in an $r$-uniform hypergraph which contains no set of $k$ many independent edges. For all $r\geq 3$, $f(n;r,k)=\max\left(\binom{rk-1}{r}, \binom{n}{r}-\binom{n-k+1}{r}\right)$."
- **Partial results**: $r=2$ is Erdős–Gallai; Łuczak–Mieczkowska proved $r=3$; Frankl: $f(n;r,k)\le(k-1)\binom{n-1}{r-1}$; many large-$n$ thresholds (Huang–Loh–Sudakov etc.).
- **Attack surface**: audit demoted from UA — the shifting/absorption proofs are out of reach. Archive value is high: statement is one line, the two extremal families are exact binomial identities, and if the repo ever ports Erdos20 compression to matchings, Frankl's bound is the re-entry point.
- **Infrastructure needed**: matching defs for Finset set-families.
- **OEIS link**: none

#### Erdős #1093 — deficiency of binomial coefficients
- **Status**: open
- **Statement**: "For $n\geq 2k$ we define the deficiency of $\binom{n}{k}$ as follows. If $\binom{n}{k}$ is divisible by a prime $p\leq k$ then the deficiency is undefined. Otherwise, the deficiency is the number of $0\leq i<k$ such that $n-i$ is $k$-smooth, that is, divisible only by primes $\leq k$. Are there infinitely many binomial coefficients with deficiency $1$? Are there only finitely many with deficiency $>1$?"
- **Partial results**: ELS88/ELS93: 58 deficiency-1 examples below $10^5$; all known deficiency $>1$ cases (8 of def 2, 6 of def 3, $\binom{47}{11}$ def 4, $\binom{284}{28}$ def 9); $n\ll2^k\sqrt k$ when deficiency is defined.
- **Attack surface**: deficiency is computable — the listed examples are decidable certificates; the ELS93 bound is a plausible lemma.
- **Infrastructure needed**: $k$-smoothness predicate (shared with #684, #1094, #1095).
- **OEIS link**: none

#### Erdős #1094 — least prime factor of C(n,k)
- **Status**: open
- **Statement**: "For all $n\geq 2k$ the least prime factor of $\binom{n}{k}$ is $\leq \max(n/k,k)$, with only finitely many exceptions."
- **Partial results**: ELS88: exactly 14 known exceptions; Selfridge: $\le n/k$ once $n\ge k^2-1$ except $\binom{62}{6}$; ELS93 conjecture a $\max(n/k,13)$ bound with 12 exceptions.
- **Attack surface**: archive; the 14 exceptions and $\binom{62}{6}$ are decidable checks. (Extraction-pass hygiene note: one subagent's suggested fragment here was cross-contaminated from #1020; discard the "Frankl bound" mention.)
- **Infrastructure needed**: least-prime-factor lemmas.
- **OEIS link**: none

#### Erdős #1160 — group counts below powers of two
- **Status**: open
- **Statement**: "Let $g(n)$ denote the number of groups of order $n$. If $n\leq 2^m$ then $g(n)\leq g(2^m)$."
- **Partial results**: Pantelidakis: proved for odd $n$ when $m\ge3619$; stronger sum version conjectured ([BNV07] Q22.18).
- **Attack surface**: the only Lean home this could have is `Proofs/GroupCount` gnu machinery. Sanity layer from A000001 for small $m$; honest confidence low for certified counts at $m\ge6$ (gnu(64)=267 is already serious) — check the repo's current certified gnu range before promising anything beyond the statement.
- **Infrastructure needed**: group counting beyond current gnu range is the bottleneck.
- **OEIS link**: A000001

#### Erdős #548 — Erdős–Sós conjecture
- **Status**: falsifiable
- **Statement**: "Let $n\geq k+1$. Every graph on $n$ vertices with at least $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices."
  Parity note: the standard conjecture is "more than
  $(k-1)n/2$" edges; the DB's "$+1$" form is one edge
  weaker as a hypothesis when $(k-1)n$ is odd. The Lean
  sketch uses the standard (stronger) form.
- **Partial results**: proved for hosts of girth $\ge5$ (Brandt–Dobson), C4-free hosts (Saclé–Woźniak), complement variants; announced AKSS proof for large $k$ unpublished. Companion #547 ($R(T)\le2n-2$, site status "decidable") follows from it; Zhao settled #547 for large $n$, so #547 is deliberately not listed separately here.
- **Attack surface**: archive; the path case (Erdős–Gallai) is the provable fragment. Sub-case proofs are serious extremal graph theory beyond current infra.
- **Infrastructure needed**: tree-embedding lemmas; heavy.
- **OEIS link**: none

### Tier UC — Lemma mines (surrounding theory has provable results)

#### Erdős #727 — factorial square divisibility
- **Status**: open
- **Statement**: "Let $k\geq 2$. Does $(n+k)!^2 \mid (2n)!$ for infinitely many $n$?"
- **Partial results**: Balakran (1929): the $k=1$ analogue, $(n+1)!^2\mid(2n)!$ i.e. $(n+1)^2\mid\binom{2n}{n}$, holds infinitely often (Catalan-number argument). EGRS75: $(n+k)!(n+1)!\mid(2n)!$ infinitely often for $k<c\log n$. Open even for $k=2$.
- **Lemma mine**: audit demoted from UA because the verbatim statement starts at $k\ge2$, where smooth-number technology is needed. The mine: Balakran's $k=1$ theorem and factorial-divisibility lemmas ($a!b!\mid n!$ criteria) as BINOM assets.
- **Infrastructure needed**: Catalan numbers (Mathlib) + factorial valuation lemmas.
- **OEIS link**: A002503, A343507, A389396

#### Erdős #901 — Property B / m(n)
- **Status**: open
- **Statement**: "Let $m(n)$ be minimal such that there is an $n$-uniform hypergraph with $m(n)$ edges which is $3$-chromatic. Estimate $m(n)$."
- **Partial results**: $2^n\ll m(n)\ll n^22^n$ (Erdős); $\sqrt{n/\log n}\,2^n$ (Radhakrishnan–Srinivasan); Erdős–Lovász conjecture $m(n)\sim n2^n$; $m(2)=3$, $m(3)=7$, $m(4)=23$.
- **Lemma mine**: audit demoted from UA (the modern bounds use probabilistic resampling beyond the g(k) machinery). Mines: $m(2)=3$ (triangle) is quick; $m(3)=7$ (Fano) is a bounded but nontrivial finite theorem; the union-bound lower bound $m(n)>2^{n-1}$-type statement is the entry point to finite probabilistic arguments next to `ErdosLovasz`.
- **Infrastructure needed**: proper-2-coloring defs shared with #836.
- **OEIS link**: none listed

#### Erdős #1178 — Brown–Erdős–Sós
- **Status**: open
- **Statement**: "For $r\geq 3$ let $d_r(e)$ be the minimal $d$ such that $\mathrm{ex}_r(n,\mathcal{F})=o(n^2)$, where $\mathcal{F}$ is the family of $r$-uniform hypergraphs on $d$ vertices with $e$ edges. Prove that $d_r(e)=(r-2)e+3$ for all $r,e\geq 3$."
- **Partial results**: BES73: $d_r(e)\ge(r-2)e+3$; Ruzsa–Szemerédi: $d_3(3)=6$; EFR86: $d_r(3)$ for all $r$; Sárközy–Selkow: $d_r(e)\le(r-2)e+2+\lfloor\log_2e\rfloor$.
- **Lemma mine**: audit demoted from UA — the equality direction runs through regularity/removal, absent from the repo and Mathlib. The mine is the BES73 lower-bound construction: finite hypergraph combinatorics in the repo's existing vocabulary.
- **Infrastructure needed**: $\mathrm{ex}_r$ Turán-density defs (small).
- **OEIS link**: none

#### Erdős #124 — completeness of power sums (second question)
- **Status**: open (second question only; the first was proved in Lean, Alexeev/Aristotle, Nov 2025)
- **Statement**: "If we further have $\mathrm{gcd}(d_1,\ldots,d_r)=1$ then, for any $k\geq 1$, can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$ where $c_i\in \{0,1\}$ and $a_i\in P(d_i,k)$?"
- **Partial results**: BEGL96: proved for $\{3,4,7\}$; Melfi: completeness with $\sum1/(d_i-1)<\epsilon$.
- **Lemma mine**: the sorted-partial-sum completeness criterion (used in the Aristotle proof of question one) belongs in `Proofs/Enumerative` regardless; $\{3,4,7\}$ is an explicit bounded target.
- **Infrastructure needed**: complete-sequence criterion defs.
- **OEIS link**: none

#### Erdős #18 — practical numbers and h(m)
- **Status**: open, $250
- **Statement**: "We call $m$ practical if every integer $1\leq n<m$ is the sum of distinct divisors of $m$. If $m$ is practical then let $h(m)$ be such that $h(m)$ many divisors always suffice. Are there infinitely many practical $m$ such that $h(m) < (\log\log m)^{O(1)}$? Is it true that $h(n!)<n^{o(1)}$? Or perhaps even $h(n!)<(\log n)^{O(1)}$?"
- **Partial results**: Erdős: $h(n!)<n$; Vose [Vo85]: infinitely many practical $m$ with $h(m)\ll(\log m)^{1/2}$; computed $h(n!)$ for $n=3..11$: 2,3,4,5,5,6,7,7,7.
- **Lemma mine**: `Proofs/Enumerative` already has practical numbers; defining $h$, proving $h(n!)<n$, and certifying the small table are direct extensions.
- **Infrastructure needed**: greedy divisor-representation lemmas.
- **OEIS link**: A005153

#### Erdős #683 — largest prime divisor of C(n,k)
- **Status**: open
- **Statement**: "Is it true that for every $1\leq k\leq n$ the largest prime divisor of $\binom{n}{k}$, say $P(\binom{n}{k})$, satisfies $P\left(\binom{n}{k}\right)\geq \min(n-k+1, k^{1+c})$ for some constant $c>0$?"
- **Partial results**: Sylvester–Schur: $P(\binom{n}{k})>k$ for $k\le n/2$; Erdős 1955: $\gg k\log k$; essentially equivalent to #961.
- **Lemma mine**: Sylvester–Schur itself is the prize — not in Mathlib, elementary (Erdős's proof), and load-bearing for #699, #1094, #1095 above. Hard but classical.
- **Infrastructure needed**: none beyond BINOM.
- **OEIS link**: A006530, A074399, A121359

#### Erdős #1095 — binomials with all prime factors large
- **Status**: open
- **Statement**: "Let $g(k)>k+1$ be the smallest $n$ such that all prime factors of $\binom{n}{k}$ are $>k$. Estimate $g(k)$."
- **Partial results**: EES74: $k^{1+c}<g(k)\le\exp((1+o(1))k)$, conjecture $g(k)<\mathrm{lcm}(1,\dots,k)$; Konyagin: $g(k)\gg\exp(c(\log k)^2)$.
- **Lemma mine**: small values decidable via A003458; the EES74 lower bound is an elementary target; shares the prime-factor toolkit with #683/#1094.
- **Infrastructure needed**: none beyond BINOM.
- **OEIS link**: A003458

#### Erdős #849 — Singmaster-type multiplicity
- **Status**: open
- **Statement**: "Is it true that, for every integer $t\geq 1$, there is some integer $a$ such that $\binom{n}{k}=a$ (with $1\leq k\leq n/2$) has exactly $t$ solutions?"
- **Partial results**: $t=3$ at $a=120$, $t=4$ at $a=3003$; nothing known for $t\ge5$; MRSTT22 restrict solutions for large $k$.
- **Lemma mine**: "$\binom{n}{k}=3003$ has exactly 4 solutions" (and the $a=120$ case) are clean finite theorems once binomial monotonicity gives an a-priori bound on $n$ — elementary.
- **Infrastructure needed**: binomial monotonicity lemmas.
- **OEIS link**: A003016, A003015, A059233, A098565, A090162, A180058, A182237

#### Erdős #1100 — coprime consecutive divisors
- **Status**: open
- **Statement**: "If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then let $\tau_\perp(n)$ count the number of $i$ for which $(d_i,d_{i+1})=1$. Is it true that $\tau_\perp(n)/\omega(n)\to \infty$ for almost all $n$? Is it true that $\tau_\perp(n)< \exp((\log n)^{o(1)})$ for all $n$?" (plus the squarefree $g(k)$ growth question in the entry)
- **Partial results**: Erdős–Hall 1978 max-order bound; Erdős–Simonovits: $(\sqrt2+o(1))^k<g(k)<(2-c)^k$ over squarefree $n$ with $\omega(n)=k$.
- **Lemma mine**: $\tau_\perp$ is decidable on the sorted divisor list — adjacent to the Schinzel–Szekeres divisor-structure work (Erdos542); trivial bounds and small tables are immediate.
- **Infrastructure needed**: sorted-divisor-chain lemmas.
- **OEIS link**: A325864 (⚠ metadata mismatch: A325864 is
  "Number of subsets of {1..n} of which every subset has a
  different sum" — tangentially connected but not a direct
  encoding of $\tau_\perp$ values)

#### Erdős #663 — least prime not dividing a product
- **Status**: open
- **Statement**: "Let $k\geq 2$ and $q(n,k)$ denote the least prime which does not divide $\prod_{1\leq i\leq k}(n+i)$. Is it true that, if $k$ is fixed and $n$ is sufficiently large, we have $q(n,k)<(1+o(1))\log n?$"
- **Partial results**: $q(n,k)<(1+o(1))k\log n$ is easy (Erdős–Pomerance); Tao heuristic supports the conjecture.
- **Lemma mine**: the easy $k\log n$ bound is a primorial-growth argument pairing with the Covering lane's arithmetic; sibling entry #1181 covers the same theme.
- **Infrastructure needed**: primorial/Chebyshev bounds (Mathlib-adjacent).
- **OEIS link**: A391668

#### Erdős #688 — sieving [1,n] by large primes
- **Status**: open
- **Statement**: "Define $\epsilon_n$ to be maximal such that there exists some choice of congruence class $a_p$ for all primes $n^{\epsilon_n}<p\leq n$ such that every integer in $[1,n]$ satisfies at least one of the congruences $\equiv a_p\pmod{p}$. Estimate $\epsilon_n$ - in particular is it true that $\epsilon_n=o(1)?$"
- **Partial results**: Erdős: $\epsilon_n\gg(\log\log\log n)/(\log\log n)$; cluster with #687, #689, #1200.
- **Lemma mine**: concrete $a_p$ choices covering $[1,n]$ for specific $n$ are interval-covering certificates with prime moduli — the same verification shape as the Covering layer, yielding certified lower-bound data points.
- **Infrastructure needed**: interval-covering (vs. full residue covering) def.
- **OEIS link**: none

#### Erdős #117 — covering groups by abelian subgroups
- **Status**: open
- **Statement**: "Let $h(n)$ be minimal such that any group $G$ with the property that any subset of $>n$ elements contains some $x\neq y$ such that $xy=yx$ can be covered by at most $h(n)$ many Abelian subgroups. Estimate $h(n)$ as well as possible."
- **Partial results**: Pyber [Py87]: $c_1^n<h(n)<c_2^n$; lower bound already known to Isaacs.
- **Lemma mine**: small-$n$ instances and the basic covering lemmas fit `Proofs/GroupCount` (commuting-pair structure is literally in scope). Exploratory: no computed $h(n)$ table exists in the entry, so scope a probe first.
- **Infrastructure needed**: abelian-subgroup cover defs.
- **OEIS link**: none confirmed

#### Erdős #684 — smooth part of binomial coefficients
- **Status**: open
- **Statement**: "For $0\leq k\leq n$ write $\binom{n}{k} = uv$ where the only primes dividing $u$ are in $[2,k]$ and the only primes dividing $v$ are in $(k,n]$. Let $f(n)$ be the smallest $k$ such that $u>n^2$. Give bounds for $f(n)$."
- **Partial results**: Mahler: $f(n)\to\infty$ (ineffective); APSSV26: $f(n)\ll(\log n)^2$ and $f(n)\ge(\tfrac12-o(1))\log n$ infinitely often; RH gives $n^{2/3+o(1)}$ via a different route.
- **Lemma mine**: audit kept this out of UA — even the "elementary" $(\log n)^2$ bound leans on prime-distribution input. The mine is the smooth/rough factorization $u\cdot v$ as a reusable def feeding #1093/#1094/#1095, plus Kummer-level valuation lemmas.
- **Infrastructure needed**: smooth-part decomposition on top of BINOM.
- **OEIS link**: A392019

### Sweep provenance and hygiene

Counts: 661 unsolved entries triaged, 34 finalists
extracted, 32 retained here (9 UA, 10 UB, 13 UC).
Dropped at final cut: #547 (site status "decidable",
settled for large $n$ by Zhao — noted under #548) and
#1143 (Erdős–Selfridge exact bound has "no published
reference located"; too thin to card).

Confidence flags: partial-results bullets are paraphrased
from `goof erdos fetch` section text and site comments,
including several 2025-26 AI-assisted claims (#699's
$j\le\frac32i$ case, #836's claimed second-question
proof, #273's $p>877$ threshold) — these are comment-
sourced, not refereed; re-fetch the live entry before
building on any of them. Statements are verbatim except #1100 (third question
summarized after the quoted text) and #124 (only the
still-open second question is quoted); the fetch cache
has complete texts.
