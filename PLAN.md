# PLAN — covering-system extension arc

ONE arc: the extension work opened up by the covering-system layer. Not a
revival of the general campaign PLAN retired into `Formalize/INDEX` at
`9ce3a87`; `INDEX` remains the dispatch state of record for everything
else. Fold this back into `INDEX` and delete it when the arc closes.

Correction history is in `git log -p PLAN.md`, not in this file. Several
claims here have been wrong before; when one moves, move it and let the
commit record why.


## STATE

  Basic.lean                f2cd3df  Covers, IsCoveringSystem (distinct
                                     moduli > 1), covers_iff_forall_range
  NotTwoPowerPlusPrime      add6611  Erdos 1950 in full
  ErdosMinus2k / ErdosRows  7520b62  A039669 archive + 10^9 window;
                                     A089654 bridge (1 intended sorry)
  FixedDivisor.lean         9d873d7  THE GENERAL CRITERION
  Sierpinski / Riesel       9d873d7  78557, 509203, both infinitudes
  Erdos1950Instance.lean    9d873d7  Erdos 1950 from the criterion
  RankOfApparition.lean     3c7d4ef  alpha(p) and Fibonacci-like zero
                                     sets — the alpha-layer lane H needs

Sorry-free except the archived A039669 conjecture. Axioms within
{propext, Classical.choice, Quot.sound}. No native_decide.


## AXIOM HYGIENE — how that last line is actually checked

The five hand-listed sweeps under `Proofs/Scratch` (Ad1AxiomSweep,
Aw1AxiomAudit, Le1AxiomAudit, Secp256k1AxiomAudit, ShearReviewAudit)
state their criterion as "no `Lean.ofReduceBool`". That name is never
emitted on this toolchain, so those five detect nothing. Measured on
v4.33.0-rc1: a native_decide proof yields
`<decl>._native.native_decide.ax_1_1`.

This is documented upstream behaviour, not a discovery — RFC #12216 /
PR #12217, shipped in Lean v4.29.0 (2026-03-27), moved native
computation to one axiom per computation. The idiom went stale under us;
`ofReduceBool` was deprecated 2026-02-01.

Only an allowlist-SUBSET test works. `RankOfApparition` section 10 does
it that way and `throwError`s, verified to fire by planting both a
native_decide proof and a `sorry`. It cannot close two limits from
inside: `example`s contribute no constant and escape any such sweep, and
the sweep is positional.

  ACTION: adopt `leanprover-community/axiom-audit` rather than
  retrofitting five hand-rolled sweeps. It already does the
  allowlist-subset check, runs over `.olean` files so it catches
  transitive dependencies, and is community-maintained. Mathlib solves
  the same problem with a syntactic linter plus periodic lean4checker,
  and explicitly notes name-checking is "not airtight".


## PRIOR ART, as enumerated

Recorded here because the canonical grading document
(`.tasks/main/docs/novelty-ErdosCovering.md`) is outside version control.
Each absence names the enumeration it was checked against.

  alpha(p) / Pisano   Absent from Mathlib rev 3edb3c0 (`grep -ric
                      apparition|pisano` over Mathlib/ = zero files).
                      Absent from AFP (63 NT entries enumerated) and
                      from Coq/Rocq sources checked. agda-unimath DOES
                      have `elementary-number-theory.pisano-periods` —
                      closest prior art anywhere; it defines the period
                      but not the entry point, and does not prove the
                      zero-set theorem. The mathematics is routine
                      (Vajda 1989 p. 73); first-formalization at most,
                      never new mathematics.
  Naslund-Sawin       No prior formalization found. formal-conjectures
                      `ErdosProblems/857.lean` exists but is a stub —
                      `answer(sorry)`, body `sorry`, 0 lines proved.
                      Mathlib has zero sunflower/slice-rank content. AFP
                      `Sunflowers` is Erdos-Rado, i.e. #20, a different
                      problem. Lean 3 `lean-forward/cap_set_problem` is
                      Ellenberg-Gijswijt, method-adjacent but not this.
                      `SproutSeeds/sunflower-lean` is structural, not
                      the tensor bound.
  Covering in Lean    NOT clear ground. erdosproblems.com links
                      per-problem Lean artifacts in personal repos: #16
                      is "disproved (Lean)" via D. Chin 2026-02-25,
                      building two covered APs from the SAME
                      {3,5,7,13,17,241}/period-24 system as
                      NotTwoPowerPlusPrime. Sweep each entry's comment
                      thread before any novelty claim, not just the
                      formal-conjectures tree.

  LIMIT on all three: GitHub code search does not index every repo and
  was unauthenticated for the alpha sweep; the Rocq opam index (584
  packages) and the Mizar MML (~1300 articles) were not enumerated
  exhaustively. "None found in the corpora named" is the claim; "does
  not exist" is not.


## LANES

### A'. Base-b parameterisation                          [S]  DO FIRST

  Goal   `2` -> `b` throughout FixedDivisor. Order bridge becomes
         `(b:Z)^d = 1 [ZMOD p]`; per-class step unchanged.
  Why    decidability survives — `b^d % p = 1 % p` stays a ground
         check. Reaches base-b Sierpinski/Riesel (cf. A273987).
  Blocks nothing. Mechanical; highest value per line here.

### A. Sequence-level generalisation                     [L]  PART LANDED

  Goal   replace `A*2^n + B` with `f : N -> Z` carrying, per class
         `(a,d,p)`, the hypothesis `forall n, n % d = a % d -> p | f n`.
  Done   the Fibonacci-like half, at 3c7d4ef.
  Left   the abstract layer both families instantiate. What exists is
         one family's bridge, not the shared statement.
  Cost   ~15 lines, and it buys STATEMENT reuse only — the `decide`
         pipeline lives in the per-family bridges and does not
         abstract. Cheap correct refactor, not high-leverage.
  Note   the shared hypothesis is NOT decidable as stated. Both
         families satisfy it by different mechanisms: ord_p(2) for
         exponential, alpha(p) for Fibonacci-like.

### B. Brier numbers                                     [S]  READY

  Goal   simultaneously Sierpinski and Riesel.
  Needs  nothing. k = 3316923598096294713661 (Clavier), all four
         fields checked both sides, zero uncovered residues, all
         divisors prime:
           Sierpinski (p | k*2^a + 1), L = 48, 7 triples, max 108 bits
             {(1,2,3),(2,4,5),(4,12,13),(0,8,17),(36,48,97),
              (20,24,241),(12,48,673)}
           Riesel (p | k*2^a - 1), L = 180, 13 triples, max 109 bits
             {(0,2,3),(0,3,7),(9,10,11),(11,18,19),(1,5,31),(23,36,37),
              (7,20,41),(10,60,61),(8,9,73),(5,36,109),(13,15,151),
              (25,30,331),(37,60,1321)}
  Shape  TWO INDEPENDENT `IsFixedDivisorSystem` instances, not one
         structure with two residue assignments — the sides share only
         the prime 3 and the modulus 2.
  Blocks load 336 and 2340 vs Selfridge's 252, far inside the measured
         ceiling. Width (109 vs 44 bits) is all that grows, and Nat is
         GMP-backed.
  Warn   the record k is also the smallest; there is no cheaper
         witness to fall back to. Do not source covering sets from
         primepuzzles.net without re-verifying — Wesolowski's entry
         fails Riesel coverage against the primes it lists.
  Open   whether ANY proof assistant has a Brier number. Unswept; the
         prior-art sweep was scoped to the criterion. Sweep first.

### C. More instantiations                               [S]  LOW VALUE

  Goal   A076336 Sierpinski (271129, 271577, ...), A101036 Riesel
         (762701, 777149, ...). One certificate + one `decide` each.
  Value  none is a first — ACL2 covers several. Worth doing only as
         evidence the framework is reusable. Cap at two or three and
         say in-file that the list is illustrative.

### D. Mirsky-Newman theorem                             [M]

  Goal   no disjoint distinct covering system exists. Conjectured
         Erdos 1950; proved Mirsky-Newman, independently
         Davenport-Rado; the original proof was never published.
         Special case of Herzog-Schonheim.
  Why    self-contained, elegant (root-of-unity argument), stated
         directly in terms of the committed `IsCoveringSystem`.
         Strongest classical target in reach.
  Check  `ErdosProblems/274.lean` IS present upstream, content unread.
         An external abelian-case Lean proof was reported in a sweep
         and is UNVERIFIED. Read both before restating.

### E. Statement archives                                [S each]

  Measured against the formal-conjectures tree (recursive, API), not
  inferred. Naming is `ErdosProblems/NNN.lean`, 509 files. The
  covering-systems tag returns 22 entries.

    PRESENT upstream, do NOT duplicate:
      7, 203, 204, 273, 274, 275, 276, 277, 279, 280, 281, 1113
    ABSENT upstream:
      2, 8, 27, 202, 278, 586, 947, 1188, 1189, 1190

  Most of the absent list is dead as archive targets — 202 and 1190 are
  "solved (Lean)", 947 "proved (Lean)", 2/8/27/586 "disproved". What is
  unclaimed AND open:

    #278   density of integers covered by congruences on a fixed
           modulus set. NOT a mere archive: the second question is
           SETTLED (minimum at all a_i equal), attribution corrected on
           the entry 2026-03-03 to Rogers via Halberstam-Roth
           *Sequences* (1983) 5.3, three years before Simpson 1986.
           Tao wrote it up 2026-01-19. A provable target.
    #1188  estimate F(x), the count of minimal distinct covering
           systems. Open.
    #1189  irreducible covering sets. Open; final sub-question settled
           by Sun 2007.

  #7 is upstream as `erdos_7` over `StrictCoveringSystem Z` (sorry'd),
  so the statement is taken. Their moduli are `Ideal`s over a general
  ring, which is not decidable — a decidable restatement is a
  defensible separate contribution, but say so explicitly.

### F. Hough-Nielsen 2019                                [XL]  GATED

  Goal   every distinct covering system has a modulus divisible by 2
         or 3. Sharpest partial constraint on #7 — an odd system would
         need a modulus divisible by 3.
  Gate   an ITP paper on its own. Do NOT start without the USER
         explicitly scoping it.

### G. Hough 2015 — minimum modulus bounded              [XXL]  RECORDED

  Resolves Erdos #2 ($1000, listed disproved). Almost certainly out of
  reach at current leverage. Recorded for completeness, not dispatch.

### H. Wilf primefree sequence A083216                   [M]  READY

  Goal   Fibonacci-like, every term composite, consecutive terms
         coprime. a(0) = 20615674205555510, a(1) = 3794765361567513.
  Needs  the alpha-layer — LANDED at 3c7d4ef. It is alpha(p), not the
         Pisano period, that plays the role ord_p(2) plays for us.
  Blocks `decide` load L*|T| = 8640*18 = 155520, ~600x Selfridge's 252
         — roughly at the measured practical limit, not inside it.
         And the terms cannot be evaluated: a(8640) ~ 10^1805, so the
         bridge MUST be phrased entirely in `ZMod p`. A naive port of
         the existing certificate shape will not terminate.
  Warn   the 18-triple certificate (L = 8640, coverage verified,
         gcd(a0,a1) = 1) was reconstructed computationally from
         A083216, NOT read off a paper. Vsemirnov's published 17
         quadruples are for a DIFFERENT sequence with a partly
         different prime set. Re-derive independently before
         committing.
  Src    Graham, Math. Mag. 37 (1964) 322-324; Wilf, Math. Mag. 63
         (1990) 284; Vsemirnov, JIS 7 (2004) 04.3.7.

### I. A006285 de Polignac note                          [S]  DROP?

  Nothing mathematically to contribute. Infinitude is already in the
  entry twice (Crocker: 2^2^n - 5; and positive lower density, Van der
  Corput / Erdos 1950, > 0.00905 by Habsieger-Roblot 2006). Separately,
  `erdos_1950_not_two_pow_add_prime` carries `1 <= k` while OEIS allows
  k = 0, which is why 3 = 2 + 2^0 is absent from the terms; the gap
  bites only at m = 3, so infinitude survives via a one-line patch the
  committed theorem does not contain. Demote to a formalization link,
  or drop. USER decision.


## NON-GOALS — state these explicitly in any writeup

  * Izotov (1995): certain fourth powers are Sierpinski WITHOUT a
    covering set, via the aurifeuillean factorization
      t^4*2^(4m+2) + 1 = (t^2*2^(2m+1) + t*2^(m+1) + 1)
                       * (t^2*2^(2m+1) - t*2^(m+1) + 1).
    Our framework provably cannot reach these. "Covering systems
    characterize Sierpinski numbers" is FALSE and easy to imply by
    accident. Whether Sierpinski numbers with no finite covering set
    exist is itself Erdos #1113 (open) — cite it as the anchor.
  * The Sierpinski problem (is 78557 least?) is a search question no
    covering argument touches. PrimeGrid is down to k = 21181, 22699,
    24737, 55459, 67607.
  * Pushing the A039669 window past 2^44 to discharge DeepMind's
    sorry'd `mientka_weitzenkamp` needs q = 37 and ~60x the current
    sweep; memory-bound on this box. Not a lane until that changes.


## USER DECISIONS PENDING

  1. Does the covering arc seed a SEPARATE ITP/CPP paper, or join
     `Manuscripts/Drafts/first-proofs-and-opn-reduction.md` as a fourth
     result? My read: separate — it is a formalization-infrastructure
     paper, not an OEIS-first-proof paper.
  2. Scope lane F (Hough-Nielsen) yes/no.
  3. A006285 note (lane I) yes/no.
  4. Whether to upstream `Basic` + `FixedDivisor` to Mathlib. Mathlib
     has ZERO covering-system content; impact is real and durable,
     review latency is long, and the API would need reshaping first.
  5. Whether `Manuscripts/` and `.tasks/` stay outside version control.
     Six drafts, 17 novelty sweeps and the triage sheet are untracked,
     including the file this arc calls canonical for novelty grading.
