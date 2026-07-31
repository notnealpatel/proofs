# PLAN — covering-system extension arc

Scope: the extension work opened up by the covering-system layer, as of
2026-07-31. This file is NOT a revival of the general campaign PLAN.md
retired into `Formalize/INDEX` at `9ce3a87`; `INDEX` remains the dispatch
state of record for everything else. This file covers ONE arc and should
be folded back into `INDEX` and deleted when the arc closes.

Novelty positions for everything below are graded in
`.tasks/main/docs/novelty-ErdosCovering.md`. Do not restate a claim from
memory; that document is canonical and records six claims that were
believed and turned out false.


## STATE — what is landed

  Basic.lean                f2cd3df  Covers, IsCoveringSystem (distinct
                                     moduli > 1), covers_iff_forall_range
  NotTwoPowerPlusPrime.lean add6611  Erdos 1950 in full, sorry-free
  ErdosMinus2k / ErdosRows  7520b62  A039669 archive + 10^9 window;
                                     A089654 bridge (1 intended sorry)
  FixedDivisor.lean         9d873d7  THE GENERAL CRITERION
  Sierpinski / Riesel       9d873d7  78557, 509203, both infinitudes
  Erdos1950Instance.lean    9d873d7  Erdos 1950 re-derived from the
                                     criterion (cone-verified)

All sorry-free except the one archived A039669 conjecture. Axioms within
{propext, Classical.choice, Quot.sound} throughout. No native_decide.


## THE CENTRAL OBSERVATION DRIVING THIS ARC

`FixedDivisor` proves things about `A * 2^n + B`. The ONLY property of
`2^n` it uses is that `2^n mod p` is periodic with period dividing `d`.
Nothing else in the proof cares that the base is 2, or that the family is
affine. Generalising that one hypothesis is the highest-leverage move
available, and it is what lane A is.


## LANES, in dispatch order

### A. Periodic-sequence generalisation of the criterion       [L, do first]

  Replace `A * 2^n + B` with a sequence `f : N -> Z` carrying, per
  covering class `(a, d, p)`, the hypothesis `p | f a` and
  `f (n + d) = f n (mod p)`. Everything downstream should follow.

  Unlocks, in the same file or cheap successors:
    * base-b Sierpinski/Riesel (`k * b^n +- 1`), cf. A273987
    * dual Sierpinski (`2^n + k`)
    * Wilf primefree Fibonacci-like sequences — lane H
  Risk: the abstraction may not pay for itself if the per-application
  glue costs more than the bespoke statement. MEASURE before committing:
  re-derive the existing Sierpinski instance through the general form
  first, and abandon if it is uglier than what is already committed.

### B. Brier numbers                                            [S]

  Simultaneously Sierpinski and Riesel. Certificate = a pair of
  certificates on the same k; the criterion already handles each side.
  Smallest known: 3316923598096294713661 (Wikipedia lists five, notes
  they may not be the five smallest). CHECK first whether kernel `decide`
  survives numbers of that size — this is the whole risk of the lane, and
  if it does not, the honest deliverable is the general Brier criterion
  plus a smaller worked witness, not a forced native_decide.

### C. More instantiations                                      [S, low value]

  A076336 "(Provable) Sierpinski numbers" 78557, 271129, 271577, 322523,
  327739, 482719, 575041, 603713, ...; A101036 Riesel 509203, 762701,
  777149, ... Each is one certificate + one `decide`. Nearly free, adds
  little per item, and none is a first (ACL2 covers several). Worth doing
  ONLY as evidence the framework is reusable — cap at two or three, and
  say in the file that the list is illustrative, not exhaustive.

### D. Mirsky-Newman theorem                                    [M]

  No disjoint distinct covering system exists. Classical (conjectured
  Erdos 1950, proved Mirsky-Newman, independently Davenport-Rado; the
  original proof was never published). Special case of Herzog-Schonheim.
  Self-contained, elegant (generating function / root-of-unity argument),
  and stated directly in terms of the committed `IsCoveringSystem`.
  Strongest classical target in reach. Cross-check erdosproblems #274
  (Herzog-Schonheim) — an external abelian-case Lean proof was reported
  in a sweep and is UNVERIFIED; verify before claiming anything.

### E. Statement archives for the Erdos covering cluster        [S each]

  22 erdosproblems entries carry the `covering systems` tag. Our
  `IsCoveringSystem` is the right object for most. Highest value:
    #7    distinct covering system with all moduli odd?  (verifiable)
    #203  open, covering + primes
    #273, #276, #277, #278, #1189  open
  Already Lean-touched upstream (do NOT duplicate; confirm status first):
    #202, #204, #275, #1190
  Cheap, and they make the layer visibly load-bearing for open problems.

### F. Hough-Nielsen 2019                                        [XL]

  Every distinct covering system has a modulus divisible by 2 or 3.
  A serious result and a serious formalization; would be an ITP paper on
  its own. Also the sharpest partial constraint on #7 (an odd system
  would need a modulus divisible by 3). Do NOT start without the USER
  explicitly scoping it.

### G. Hough 2015 — minimum modulus bounded                      [XXL]

  Resolves Erdos #2 ($1000, listed disproved). Almost certainly out of
  reach at current leverage. Recorded for completeness, not dispatch.

### H. Wilf primefree sequence A083216                           [M, needs A]

  Fibonacci-like, every term composite, consecutive terms coprime;
  a(0) = 20615674205555510, a(1) = 3794765361567513. Proved by a covering
  system on the indices where each prime divides the recurrence — the
  Pisano periods play the role `ord_p(2)` plays for us. This is the
  clearest evidence that lane A's abstraction is the right one, and it is
  the reason to do A before B or C.

### I. A006285 de Polignac — OEIS note                           [S, non-Lean]

  A006285 = odd numbers not of the form p + 2^k: 1, 127, 149, 251, 331,
  337, 373, 509, ... `erdos_1950_not_two_pow_add_prime` is exactly the
  infinitude statement for this sequence, with an explicit arithmetic
  progression of witnesses. Sixth candidate for the OEIS notes queue and
  stronger than the label-retirement items already there. USER decision.


## NON-GOALS — state these explicitly in any writeup

  * Izotov (1995): certain fourth powers are Sierpinski WITHOUT a
    covering set, via the aurifeuillean factorization
    t^4 * 2^(4m+2) + 1 = (t^2*2^(2m+1) + t*2^(m+1) + 1)
                       * (t^2*2^(2m+1) - t*2^(m+1) + 1).
    Our framework provably cannot reach these. "Covering systems
    characterize Sierpinski numbers" is FALSE and easy to imply by
    accident.
  * The Sierpinski problem (is 78557 least?) is a search question no
    covering argument touches. PrimeGrid is down to
    k = 21181, 22699, 24737, 55459, 67607.
  * Pushing the A039669 window past 2^44 to discharge DeepMind's sorry'd
    `mientka_weitzenkamp` needs q = 37 and ~60x the current sweep;
    memory-bound on this box. Not a lane until that changes.


## USER DECISIONS PENDING

  1. Does the covering arc seed a SEPARATE ITP/CPP paper, or join
     `Manuscripts/Drafts/first-proofs-and-opn-reduction.md` as a fourth
     result? (My read: separate — it is a formalization-infrastructure
     paper, not an OEIS-first-proof paper. See manuscript section 4.)
  2. Scope lane F (Hough-Nielsen) yes/no.
  3. A006285 OEIS note yes/no (lane I).
  4. Whether to upstream `Basic` + `FixedDivisor` to Mathlib. Mathlib has
     ZERO covering-system content; impact is real and durable, review
     latency is long, and the API would need reshaping first.
