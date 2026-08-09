# Compositional coverage certificates, and the first machine verification of a minimum-modulus record

**STATUS: SCOPING SHEET, opened 2026-07-31.** Not a result sheet — nothing
here is built yet. This scopes the one item surfaced during the covering-arc
review that has the properties the rest of that corpus lacks: it is hard, it
is unclaimed, it needs a technique nobody has built, and it produces an
artifact people already care about.

**Provenance discipline.** Seven prior-art claims in the sibling sheet
`first-proofs-and-opn-reduction.md` were believed and turned out false, every
one caught by retrieving an artifact rather than by reasoning. Accordingly
every claim below is tagged:

- **[M]** measured or retrieved by the orchestrator directly in this session;
- **[A]** agent-reported, artifact fetched by the agent but **not**
  independently re-verified — treat as a lead, re-fetch before citing;
- **[O]** open question, nobody has checked.

---

## 1. The target

Erdős problem **#2**, $1000, "perhaps my favourite problem" (Erdős): *can the
smallest modulus of a covering system be arbitrarily large?* **[M]** — from
the live erdosproblems.com entry:

> Hough, building on work of Filaseta, Ford, Konyagin, Pomerance, and Yu, has
> shown (contrary to Erdős' expectations) that the answer is no: the smallest
> modulus must be at most $10^{16}$. An alternative, simpler, proof was given
> by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba, who improved the
> upper bound on the smallest modulus to $616000$. The best known lower bound
> is a covering system whose minimum modulus is $42$, due to Owens.

So the problem has two sides, and they are formalization targets of totally
different character:

| | upper bound | lower bound |
|---|---|---|
| result | no system with min modulus > 616000 | a system with min modulus 42 exists |
| shape | universal non-existence | **one explicit object** |
| method | distortion sieve, probabilistic | construction + verification |
| est. cost **[A]** | 5–9 person-months (BBMST) | this document |
| committed layer helps? | **no** — statement vocabulary only, <3% of effort | **this is exactly what it is for** |

This sheet is about the **lower bound**. The upper bound is scoped, and
deliberately deferred, in `PLAN.md` lanes F/G.

## 2. The gap nobody has closed

**[A]** No machine verification of the record systems exists, in any
language — not a proof assistant, not C, not PARI, not Sage. Nielsen's own
paper says a program *could* be written and describes what it would check:

> clearly a computer program could be written to double check that the set we
> constructed covers all the integers. The most straightforward method seems
> to be: (1) checking that no modulus is repeated, by listing all used moduli
> (treating the upwards arrow as exhausting all higher powers), and
> (2) checking that each empty input is eventually filled by later (or
> earlier) congruence classes.

He did not implement it, and states the system "contains many more than
`10^50` congruence classes … unfortunately too many for humans to grasp
concretely, or list (even in factored form) with modern computing power."

**[A]** Sizes, to be re-verified before any claim:

| author | year | min modulus | congruences | lcm of moduli |
|---|---|---|---|---|
| Churchhouse | 1968 | ≤ 9 | — | ≤ 6.0·10⁵ |
| Krukenberg | 1971 | 18 | ? | 4.75·10¹⁴ |
| Gibson | 2009 | 25 | ? | primes to 2017 |
| Nielsen | 2009 | 40 | > 10⁵⁰ | ~10⁴⁴⁹⁵ |
| Owens | 2014 | 42 | > 10⁵⁰ | ~10⁴⁴⁹⁵ |

**[A]** Gibson's m = 25 system *was* computer-enumerated by its author during
the greedy search that found it, so the unverified gap begins at m = 40.

## 3. Why brute force is structurally dead — measured, not argued

The committed layer discharges coverage through
`Erdos.Covering.covers_iff_forall_range`: coverage of ℤ is equivalent to
coverage of `0 … L−1` for any common multiple `L` of the moduli, checked by
kernel `decide`. Selfridge's certificate runs at `L = 36`.

**[M]** Measured 2026-07-31, Lean 4.33.0-rc1, cold `lake env lean`, import
baseline 5.33 s, on the dyadic test family (lcm `2^a`, `a+1` classes) —
recorded in `Proofs/Scratch/CoverCeiling.lean`:

| L | classes | net `decide` |
|---|---|---|
| 256 | 9 | 0.46 s |
| 1024 | 11 | 1.62 s |
| 4096 | 13 | 9.88 s |
| 16384 | 15 | **92.35 s — largest that completes** |
| 65536 | 17 | **OOM; the kernel killed the session** |

Growth is ≈ `L^1.6`, worse than the `L·|S|` work count predicts, and **the
binding resource is memory, not time**. Three walls arrive in order and all
three precede any notional compute budget: `maxHeartbeats` (default 200000)
blocks from `L = 16384`; `maxRecDepth` blocks from `L = 65536`; then the
process is OOM-killed. Note also that `-DmaxRecDepth=` on the `lean` command
line silently did nothing — only the in-file `set_option` takes effect.

**The conclusion is a structural one.** The frontier is at `L ≈ 10^4495`.
This route tops out just past `10^4`. That is a shortfall of roughly **4490
orders of magnitude**, and no amount of hardware, patience, or
`native_decide` changes the exponent. Enumerating residues is not a slow path
to the target; it is not a path.

### 3.1 The ceiling is hardware-movable — by one rung out of 4490

These numbers came from a **24 GB** box. A **256 GB** machine is available,
so the obvious question is what an order of magnitude of RAM buys. Stating
the answer precisely converts a limitation into the paper's central argument.

**[O] Extrapolation, not measurement.** Peak working set was never profiled —
we know only that `L = 16384` completes within 24 GB and `L = 65536` does
not. *Assuming* memory tracks the measured `L^1.6` time exponent, each 4× in
`L` costs ≈ 9.2× in memory, so 10.7× more RAM is worth **one rung, perhaps
a second**:

| RAM | reachable `L` | what that reaches |
|---|---|---|
| 24 GB **[M]** | ~1.6·10⁴ | Brier (180), Wilf (8640) |
| 256 GB **[O]** | ~6.6·10⁴, optimistically ~2.6·10⁵ | min-modulus ≤ 9 ladder, *marginally* |
| 10⁶ GB | ~10⁶ | nothing new |
| every machine on Earth | — | nothing new |

Churchhouse/Krukenberg at minimum modulus 9 sit at `L ≤ 6.05·10⁵` **[A]**,
just past the optimistic end of that range. So the bigger box plausibly
brings the *smallest* rung of the minimum-modulus literature within reach,
and stops there.

**Going from 24 GB to 256 GB closes one of ~4490 orders of magnitude.**
Buying every machine on Earth closes perhaps three more. That is the sense
in which the obstruction is structural rather than economic: the exponent is
untouched by hardware, by `native_decide` (which trades trust for a constant
factor, not an exponent), and by patience.

**Frame it this way in the paper.** "We ran out of memory" is a lab note.
"We characterized the ceiling, moved it by an order of magnitude, and it
moved by one rung out of 4490" is *evidence* that a different kind of
certificate is required — which is the thesis. The 256 GB run is therefore
worth doing **as an experiment expected to fail**, and reporting as such.

## 4. The proposal

Verify the **compact recursive description**, not the expanded system.

**[A]** Nielsen's construction proceeds prime by prime. Each stage uses one
prime to fill a hole left by an earlier stage, and the "arrow" operator
`q^↑` denotes an infinite recursion on powers of `q` terminated by a single
fill prime (107 in Nielsen's case). Removing the congruences with moduli
below the target minimum opens holes; later primes close them. The residual
set at every stage is a union of arithmetic progressions, each identified by
a residue class modulo a product of prime powers.

**[A]** The compact description is ~O(P²) in the number of primes `P ≈ 28` —
a few hundred nodes describing > 10⁵⁰ congruences. The proposed certificate:

```
CertNode
  | Leaf     (residue, modulus)
  | Branch   prime, inputs : Array (Option CertNode)   -- CRT split by a prime
  | Arrow    prime, fillPrime, depth, children         -- the q^↑ recursion
  | HoleFill targetHole, primeUsed, subCertificates
```

with the obligation at each node that its children cover the parent's scope.

### 4.1 What has to be built

1. **The covering principle** — soundness of arrow-recursion. **[A]**
   Nielsen §3; reportedly a short argument about CRT and density. This is
   the mathematical core and the first thing to attempt, because if it does
   not formalize cleanly the rest is moot.
2. **`CertNode` and its soundness theorem** — `Valid c → Covers (expand c)`,
   where `expand` is never actually run. This replaces
   `covers_iff_forall_range` for large systems; the existing lemma stays as
   the base case for small ones.
3. **The no-repeated-modulus check** on the compact form, reducing to
   disjointness of prime-power signatures across arrows rather than
   enumeration of moduli.
4. **The instantiation** at Nielsen's or Owens's data.

### 4.2 Why this is a result and not a case study

It has the four properties the covering arc currently lacks:

- **Unclaimed** — **[A]** no machine verification of these systems exists
  anywhere. (**[O]** re-verify independently; this is the load-bearing
  novelty claim and it is exactly the kind that has been wrong seven times.)
- **Needs new technique** — §3 shows the obvious method is not merely slow
  but structurally incapable. A compositional certificate for coverage is
  not in Mathlib, not in the committed layer, and not, as far as the sweep
  found, in any proof assistant.
- **Reusable** — the same object verifies every system in the table, and the
  small-`L` cases become its regression tests.
- **Wanted** — it produces the machine-checked record lower bound for a
  $1000 Erdős problem, against an upper bound that is itself a celebrated
  theorem. The two sides meet: `42 ≤ min modulus ≤ 616000`.

## 5. Risks, stated up front

- **The construction may not be recoverable from the papers.** **[A]**
  Nielsen's system is 25 pages of recursive notation; Owens is a BYU MS
  thesis. If the data cannot be transcribed faithfully, the deliverable
  degrades to the certificate machinery plus a smaller worked system
  (Krukenberg m = 18 at `L ≈ 4.75·10¹⁴` is already far past brute force and
  would demonstrate the technique). **That fallback is honest and should be
  planned for, not discovered late.**
- **Transcription is the trust boundary.** A verified certificate for a
  mistranscribed system proves nothing about the literature's system. The
  paper must say precisely what was checked and what was assumed, and the
  transcription should be diffed against the source by a second reader.
- **`Arrow` termination.** The `q^↑` operator is an infinite family; the
  soundness theorem must handle it coinductively or by an explicit
  depth-bound argument. **[O]** unassessed — this is the most likely place
  for the formalization to become hard.
- **Novelty may evaporate.** **[O]** If someone has quietly verified Nielsen
  in an unpublished script, the contribution narrows to "first in a proof
  assistant." Sweep before committing effort.

## 6. Explicit non-goals

- **Not** the upper bound (Hough 2015 / BBMST 2022). Different mathematics,
  different cost, scoped in `PLAN.md`. **[A]** the committed covering layer
  saves ~200 lines of statement preamble there, under 3% of the effort.
- **Not** a claim that covering systems characterize anything. Izotov (1995)
  gives Sierpiński numbers with no covering set at all.
- **Not** an improvement to the record. Formalizing Owens's 42 is
  verification, not mathematics. If the certificate machinery happens to make
  a *search* for min modulus 43+ tractable, that is a separate project and a
  much larger one.

## 7. Relation to the committed layer

`Proofs/Erdos/Covering/Basic.lean` supplies `Covers`, `IsCoveringSystem`
(distinct moduli, all > 1) and `covers_iff_forall_range`. Those definitions
are the right ones and are reused verbatim; **only the decision procedure is
replaced**. `FixedDivisor.lean` and the Sierpiński/Riesel/Erdős-1950
applications are orthogonal to this sheet — they consume coverage, they do
not produce it — and would become the infrastructure chapter of a paper this
sheet headlines. See `first-proofs-and-opn-reduction.md` §8.1.

## 8. First dispatch, if this is scoped

1. Retrieve Nielsen 2009 (*J. Number Theory* 129, 640–666) and Owens 2014
   (BYU ScholarsArchive) in full, and independently confirm the §2 sizes and
   the §4 recursion. Everything **[A]** above becomes **[M]** or dies here.
2. Independently sweep the "nobody has verified this" claim.
3. Formalize the covering principle (§4.1 item 1) alone, against a small
   hand-built arrow system. Abort the lane if that step is not clean —
   it is the cheapest possible falsification of the whole plan.

## 9. Future work

Ordered by whether it produces evidence, machinery, or mathematics.

### 9.1 Evidence — what the 256 GB machine is actually for

The big box does **not** advance the target (§3.1). Its value is producing
the ground truth against which the certificate machinery is validated, and
turning three **[O]** tags into **[M]**.

- **F1. Profile the memory curve under a fence.** Peak working set was never
  measured; the ceiling was *discovered* by an OOM kill, which is not a
  measurement. Re-run the ladder under
  `systemd-run --scope -p MemoryMax=…` (note: `ulimit -v` breaks Lean at
  startup and is not an option) and record peak RSS per rung. This produces
  the real memory exponent instead of the assumed `L^1.6`, and makes the
  §3.1 table citable.
- **F2. Find the true ceiling and report it either way.** Expected outcome:
  `L = 65536` completes, `L = 262144` does not. A negative result here is
  publishable content, not a setback — it is the quantitative core of the
  structural argument.
- **F3. Build the `m ≤ 9` ground-truth corpus.** **[A]** Churchhouse and
  Krukenberg give systems for minimum modulus 3–9 at `L ≤ 6.05·10⁵`. Verify
  as many as the box reaches by brute force through
  `covers_iff_forall_range`. **These become the regression suite for
  `CertNode`** — the only systems for which both methods can be run, hence
  the only place the certificate can be checked against something
  independent. This is the single most valuable use of the hardware.

### 9.2 Machinery — the certificate line

- **F4. Proof by reflection.** A computable `Valid : CertNode → Bool` plus
  soundness `Valid c = true → Covers (expand c)`, where `expand` is never
  evaluated. The check then costs `O(|certificate|)` — a few hundred nodes —
  instead of `O(L)`. This is the whole complexity argument, and it should be
  built and demonstrated on the `m ≤ 9` corpus *before* anyone transcribes
  Nielsen.
- **F5. Arrow termination.** **[O]** The `q^↑` operator denotes an infinite
  family; soundness needs either a coinductive treatment or an explicit
  depth-bound argument with the fill prime discharging the tail. Most likely
  place for the formalization to become genuinely hard, and worth a spike
  before committing.
- **F6. Extraction as a fallback, reluctantly.** If kernel reduction on the
  tree is still too slow, a verified checker with compiled evaluation is the
  escape — but it enlarges the trusted base, which is precisely what
  distinguishes this work from the `native_decide` prior art. Prefer F4;
  document the trust surface loudly if F6 is ever used.

### 9.3 Integrity — the parts that decide whether anyone believes it

- **F7. Differential validation.** Every system verifiable both ways
  (`m ≤ 9`, plus Sierpiński 78557, Riesel 509203, Brier, Wilf) must agree.
  The failure mode that matters is a certificate that *accepts* a system
  brute force rejects; build the disagreement test first, not last.
- **F8. Two-reader transcription.** A verified certificate for a
  mistranscribed system proves nothing about the literature's system
  (§5). Nielsen's and Owens's data should be transcribed independently by
  two readers and diffed, with the diff published as part of the artifact.
- **F9. State the two-sided bound formally.** A single Lean theorem
  `42 ≤ minModulus ∧ minModulus ≤ 616000`, lower bound proved, upper bound
  `sorry`'d with attribution to BBMST 2022. An honest artifact that shows
  exactly where the frontier of formalization sits, and a natural home for
  a later upper-bound effort.

### 9.4 Mathematics — the only route by which this stops being verification

- **F10. Certificate as search oracle.** If checking is `O(|certificate|)`,
  *searching* over compact certificates becomes conceivable, and minimum
  modulus 43+ is a genuinely open target. This would be new mathematics
  rather than verification — and a far larger project than everything above
  combined. Record it; do not scope it until F4 exists and works.
- **F11. Upstream.** `Basic` (and, if it generalizes, `CertNode`) to
  Mathlib, which has **zero** covering-system content. Long review latency,
  durable impact, and the API needs reshaping first.
- **F12. Generalize the certificate format.** Is there a compositional
  coverage certificate for covering-*type* statements beyond congruences —
  exact covers, tilings, Herzog–Schönheim (erdosproblems #274)? If the
  answer is yes, the ITP contribution is the format rather than the
  instance, and that is a substantially stronger paper than the one scoped
  here. **[O]** entirely unexplored.
