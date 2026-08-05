# Mining Methodology Gaps — Adversarial Meta-Sweep 2026-08-05

## methodology of the original sweeps

Two sweeps ran on 2026-08-05. The OEIS sweep
(`Formalize/CONJECTURE_CANDIDATES.md`, 25 candidates) ran six
topic-cluster keyword searches plus one conjecture-marker
sweep, deduped against repo A-numbers, and produced sorry'd
sketches in `Proofs/Scratch/Candidates/`. The Erdős sweep
(`Formalize/ERDOS_CANDIDATES.md`, 56 candidates; tracked in
issue #5) triaged all 225 solved/proved/disproved problems
with `formalized=no` plus all 661 unsolved-status entries,
with paired advocate/skeptic evaluation.

This meta-sweep probed what those methodologies exclude by
construction, then tried to fill each gap with live tool runs
(six probe agents plus direct verification). Verdict up
front: both sweeps were thorough INSIDE their search frames;
the losses are at the frame boundaries. The largest single
loss is measurable: 63 solved problems excluded by a filter
whose premise is false.

## identified blind spots

### 1. the `formalized=yes` exclusion discards proof targets

- **Gap**: the Erdős sweep's hunting ground was "solved/
  proved/disproved with `formalized=no`" (225 problems). But
  `formalized=yes` mostly means a STATEMENT stub exists in
  google-deepmind/formal-conjectures — not a proof. Measured
  now: 63 problems have `status.state` in {solved, proved,
  disproved} and `formalized.state=yes`; I fetched 8 upstream
  files (#4, #43, #152, #442, #599, #705, #937, #1092) and
  all 8 are `answer(...) := by sorry` stubs. The proofs are
  unclaimed. The sweep's own PRIOR ART notes (#857 stub) show
  the pattern was known and the filter was applied anyway.
- **Candidates found**: from the 63, statements pulled live:
  #387 (a divisor of `C(n,k)` in `(cn, n]` — directly on the
  repo's BINOM lane, sibling of #683/#1094), #937 (four-term
  AP of coprime powerful numbers, solved by Bajpai–Bennett–
  Chan 2024), #851 (density of `2^k + n` with `n` having few
  prime factors — Romanoff-shaped, adjacent to
  `Erdos/Covering/NotTwoPowerPlusPrime.lean`), #1064
  (totient inequality `phi(n) > phi(n - phi(n))` for almost
  all n). Solver identity and proof difficulty for #387/#851
  were NOT audited — verify before carding.
- **Recommendation**: re-run the Tier-A triage over exactly
  these 63 numbers: 4, 6, 13, 22, 43, 48, 67, 69, 92, 109,
  119, 139, 152, 219, 228, 239, 245, 248, 250, 253, 266,
  277, 285, 318, 321, 358, 387, 402, 442, 448, 480, 494,
  516, 533, 587, 590, 591, 594, 599, 615, 633, 697, 705,
  755, 822, 825, 847, 851, 868, 888, 899, 920, 937, 946,
  965, 987, 1064, 1077, 1092, 1096, 1105, 1128, 1214.
  Classify each upstream file as stub vs proof first; a
  repo proof that discharges an upstream stub is a strictly
  stronger artifact than a fresh statement.

### 2. the algebraic-complexity arc has no database to mine

- **Gap**: the repo's deepest infrastructure
  (`BilinearComplexity`, `AlgComplexity`, `GroupTPP`,
  `ShearEC`) got zero candidates because neither source
  database covers the area. Measured, not assumed: OEIS
  queries for Strassen, Cohn–Umans, apolarity return 0 hits;
  "tensor rank" / "border rank" hits are all about unrelated
  notions (Riemann tensors, triangle borders). erdosproblems
  has nothing. formal-conjectures likewise has no matmul,
  cap-set-numeric, addition-chain, or integer-complexity
  files.
- **Candidates found**: thin, honestly. A075099 (minimal
  multiplications to generate all length-n words in a free
  monoid on two generators; verbatim "I believe a(2n) = a(n)
  + 2^(2n). I guess a(7) = 156.", unattributed, open) is
  addition-chain-shaped and statable with a ~30-line
  program-semantics def. A324585/A324586 (BDD size of the
  middle bit of multiplication, conjectured `~2^(6n/5)`)
  is marginal. A250109 is already carded and on HOLD.
- **Recommendation**: this area needs a literature-sourced
  lane, not keyword mining: the Bürgisser–Clausen–
  Shokrollahi problem list and the open problems in the
  Landsberg tensor literature are where these conjectures
  live. Treat "no database indexes the repo's deepest arc"
  as a standing fact in every future sweep writeup.

### 3. the search tool cannot support the claimed marker sweep

- **Gap**: `goof oeis search` semantics are unfit for phrase
  mining, measured live: `"no proof is known"` returns 0
  results; comment-author `"Switkay"` returns 0 (comment
  fields are not indexed for authors); bare `"conjecture"`
  returns only 140; `"remains open"` 209; `"it appears
  that"` 1086. The OEIS sweep's methodology section claims a
  marker sweep over exactly these phrases — whatever those
  queries hit, coverage was far below what the prose
  implies, and phrasings like "empirically", "probably",
  "verified up to" were never claimed at all. (The Erdős
  sweep self-reported the sibling defect: 11 of 20 natural
  queries returned zero; and issue #5 records the
  `show`-vs-`fetch` verb confusion.)
- **Candidates found**: this gap is about recall, not any
  single miss; the finds in (4) below are its concrete
  fruit, since xref-walking bypasses the search index.
- **Recommendation**: stop mining through the search
  endpoint. Mine the OEIS bulk dumps (`stripped.gz` +
  full-entry fetches) with local grep over comment text,
  where phrase and author queries are trivially exact.

### 4. cross-reference depth: one hop yields a 33% hit rate

- **Gap**: neither sweep followed xref chains. Measured: 24
  one-hop xrefs pulled from six carded seeds (A005245,
  A003313, A005153, A083207, A000041, A007691) contained
  conjecture language in 8 entries — 10 open conjecture
  statements the keyword frame never saw.
- **Candidates found**: see the new-candidates list below —
  the multiperfect finiteness cluster (A005820, A027687,
  A046060) sits one hop from the carded A007691 layer;
  A002093 (highly abundant practicality) one hop from
  A005153; A000009 (two fresh Zhi-Wei Sun conjectures) one
  hop from A000041. One xref find (A000700, Plouffe) was
  conjectured Sep 2025 and proved May 2026 — the freshness
  half-life of OEIS conjectures is months, so re-pull every
  entry immediately before carding.
- **Recommendation**: BFS one xref hop from every carded
  A-number as a standing sweep stage. At 33% hit rate it is
  the cheapest candidate source found by this meta-sweep.

### 5. external sources: formal-conjectures beyond ErdosProblems, UPINT

- **Gap**: the Erdős sweep used formal-conjectures only as a
  dedup set for `ErdosProblems/`. The repo tree has 16 other
  directories — `GreensOpenProblems/` (53 files, Ben Green's
  list, sum-free/cap-set adjacent), `Kourovka/` (group
  theory, gnu-adjacent), `Wikipedia/`, `Mathoverflow/`,
  `OEIS/` (23 entries; none touch A005245, A003313, or
  A005153) — plus `FormalConjecturesForMathlib/` defs for
  practical numbers, covering systems, and sunflowers that
  overlap repo infrastructure. Open Problem Garden was
  probed and is an honest null (dormant, low density). Guy's
  UPINT was probed: C6 and F26 both hit (below).
- **Candidates found**: `||2^n|| = 2n` (UPINT F26; open,
  known for n <= 41 per Iraids et al. 2012 — probe-sourced,
  verify) is statable TODAY on the repo's `complexity` and
  appears nowhere in `Formalize/` (grep-verified). Melfi's
  1996 theorem (below) surfaced from the same probe.
  Scholz–Brauer also surfaced — but it is NOT a miss: the
  repo already adjudicated it "hopeless to prove;
  computation-saturated. Skip." in
  `Formalize/ReversibleECShear-T5-addition-chains.md`. The
  only delta worth recording: the probe reports a
  formal-conjectures issue (#2217 there) with no Lean file,
  so a statement-archive card would be cheap if that ruling
  is ever revisited. Not proposing it against the ruling.
- **Recommendation**: mine `GreensOpenProblems/` and
  `Kourovka/` next sweep; align repo defs with the upstream
  `FormalConjecturesForMathlib` practical/covering/sunflower
  defs to keep an upstreaming path open.

### 6. conjecture-only framing misses proved-but-unformalized theorems

- **Gap**: the OEIS sweep mined open conjectures only. The
  repo demonstrably values first-formalizations of proved
  results (PLAN P6 reframed A061256 exactly this way after
  finding Britnell's 2012 proof), but no search axis targets
  "conjecture in comments, later proved" entries.
- **Candidates found**: Melfi 1996 (every even number >= 2
  is a sum of two practical numbers — Margenstern's
  conjecture, quoted as proved in the carded Switkay entry
  itself) is a full-proof target sitting directly on
  `Enumerative/Practical.lean` + `StewartCriterion.lean`.
  Grep-verified uncarded. Effort M; the proof is elementary
  and constructive.
- **Recommendation**: add a "proved by" / "proof in the
  links" marker pass over the bulk dump; every hit adjacent
  to repo infra is a low-risk proof lane.

### 7. famous conjectures without marker phrasing

- **Gap**: keyword mining assumes conjectures announce
  themselves. Higman's PORC conjecture (gnu(p^n) polynomial
  on residue classes of p) is the canonical counterexample:
  central to `GroupCount`'s subject, zero repo mentions
  (grep-verified: no hit for "PORC" anywhere in `Formalize/`,
  `PLAN.md`, or `Proofs/` outside `.lake`), and absent from
  both candidate docs.
- **Candidates found**: PORC itself, archive-only. Statement
  care is real (fixed n, polynomials in p on residue
  classes), and its current status needs a literature check
  first — du Sautoy–Vaughan-Lee (2012) gave evidence usually
  read as against it at order p^10. Confidence: statement
  shape high, openness framing needs the check.
- **Recommendation**: per repo arc, once per campaign, ask
  "what is the famous conjecture of this subfield?" and
  check it by name — a five-minute pass that no keyword
  sweep replaces.

## new candidates (not in either existing document)

Assessments below had no second adversarial pass (see
provenance); confidence flags are inline.

#### Erdős #387 — binomial coefficient divisor in (cn, n]
- From the excluded-63 (blind spot 1). Upstream stub only.
- Statement (verbatim from `goof erdos fetch 387`): "Is
  there an absolute constant $c>0$ such that, for all
  $1\leq k< n$, the binomial coefficient $\binom{n}{k}$ has
  a divisor in $(cn,n]$?"
- DB status solved/proved/disproved; solver unverified —
  fetch the full entry before carding. BINOM-lane adjacent
  (#683, #1094, #1095 toolkit).

#### Erdős #937 — coprime powerful numbers in 4-AP
- From the excluded-63. Upstream stub cites Bajpai–Bennett–
  Chan [BBC24], answer yes. If the BBC24 construction is an
  explicit parametric family, certificates are decidable and
  a full proof may be in reach. Effort unknown until the
  paper is read.

#### Erdős #851 — density of 2^k + n, n with few prime factors
- From the excluded-63. Romanoff-flavored; sits next to the
  covering lane's `NotTwoPowerPlusPrime`. Likely archive
  plus partial fragments; unaudited.

#### A005820 / A027687 / A046060 — multiperfect finiteness cluster
- One xref hop from carded A007691 (blind spot 4).
- A005820: "These six terms are believed to comprise all
  3-perfect numbers." (entry comment via MathWorld link,
  Daniel Forgues, May 11 2010). Completeness implies no odd
  perfect number exists (entry comment) — direct bridge to
  the repo's OPN-reduction manuscript arc.
- A027687: "It is conjectured that there are only finitely
  many terms." (N. J. A. Sloane, Jul 22 2012) — with a
  recorded CONTRARY conjecture (Firoozbakht, Dec 26 2014),
  which the card must state honestly.
- Statement cost near zero on the existing sigma machinery;
  sanity layer = decidable membership of the known terms.

#### A002093 — highly abundant numbers are practical
- Xref hop A005153 -> A002093. Verbatim: "Conjecture: (a)
  Every highly abundant number > 10 is practical (A005153)."
  (Jaycob Coleman, Oct 16 2013; verified to 10^4 terms).
- Highly-abundant def is ~3 lines; `Nat.Practical` exists.
  Clean archive card with a `native_decide` window. Best
  statement-cost-to-adjacency ratio of the new finds.

#### A000009 — Sun conjectures on strict partition numbers
- Xref hop A000041 -> A000009. Two verbatim Zhi-Wei Sun
  conjectures (Apr 14 2023: antichain summand
  representation, verified to 1350; May 20 2023: a(n)
  divides none of p(n), p(n)-1, p(n)+1 for n > 7, verified
  to 2*10^6 per Kotesovec). Siblings of the carded A000041
  Sun statements; shares their machinery.

#### Melfi's theorem — every even number is a sum of two practicals
- Proved 1996 (Margenstern's conjecture); see blind spot 6.
  Full-proof lane on existing practical-number infra, and
  the natural companion to the carded Switkay statement,
  whose card already quotes it.

#### ||2^n|| = 2n — integer complexity of powers of two
- UPINT F26; open; the central open question of the
  `NumberComplexity` arc and absent from all repo docs.
  Statement is one line on `complexity`. Archive card +
  `decide` for small n. (Known-range claim n <= 41 is
  probe-sourced; re-verify against Iraids–Balodis 2012.)

#### A075099 — multiplication complexity of free-monoid words
- Blind spot 2's only direct OEIS find. Verbatim: "I believe
  a(2n) = a(n) + 2^(2n). I guess a(7) = 156." Unattributed;
  open; `hard,more`. Medium def cost; sibling of the chain/
  complexity model family (A293771 card shape).

#### Higman PORC — gnu(p^n) polynomial on residue classes
- Blind spot 7. Archive-only, literature check required
  before carding. `GroupCount` is its only possible home.

## incomplete probes

Three of nine probe agents never returned final reports:
the alternate-marker density sweep, the full 63-problem stub
triage (recovered by hand above at reduced depth: 8 of 63
files checked, 4 statements pulled), and the classical-
conjecture check (recovered by hand: Scholz ruled-skip
found, PORC and ||2^n|| grep-verified absent; the Shitov
counterexample-size question for Strassen-additivity/Comon
is UNRESOLVED — no grounded claim about certificate
feasibility is made here). Marker-density statistics beyond
the five measured queries in blind spot 3 remain unknown.

## recommendations for future sweeps

1. Re-triage the excluded 63 (blind spot 1). Highest
   expected yield per hour of any item here.
2. Add the one-hop xref BFS stage from all carded seeds
   (33% measured hit rate).
3. Move OEIS mining off the search endpoint onto bulk
   dumps; add "proved by" marker mining for proof lanes
   (Melfi first).
4. Mine `GreensOpenProblems/` and `Kourovka/` in
   formal-conjectures; keep def-compatibility with
   `FormalConjecturesForMathlib` in view.
5. Open a literature-sourced candidate lane for the
   algebraic-complexity arc; no database will ever feed it.
6. Re-pull every entry immediately before carding
   (Plouffe-to-Bala resolution took eight months).
7. Once per campaign, name-check each arc's flagship
   conjecture directly instead of trusting markers.

## provenance

Probe agents (2026-08-05): OEIS algebraic-complexity sweep,
xref-chain probe, external-DB probe — full reports received;
alternate-marker, stub-triage, classical checks — partial,
recovered by direct tool runs recorded above. All verbatim
quotes are from live `goof oeis show` / `goof erdos fetch` /
raw.githubusercontent pulls this session, except where
flagged probe-sourced. The candidate assessments here did
NOT receive the paired advocate/skeptic audit the original
sweeps used; treat every effort call above as single-pass.
