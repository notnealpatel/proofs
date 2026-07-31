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
affine.

CORRECTED 2026-07-31 — periodicity is the WRONG generalisation axis, and
the correction is measured, not argued. Verified directly against Wilf's
A083216 (a(0) = 20615674205555510, a(1) = 3794765361567513) with an
18-triple certificate, L = 8640, zero uncovered residues: every modulus
equals alpha(p), the RANK OF APPARITION, and for 13 of the 18 primes
alpha(p) is a PROPER divisor of the Pisano period pi(p) --
(p, d, alpha, pi) = (3,4,4,8), (7,8,8,16), (47,16,16,32),
(2521,60,60,120), ... So the sequence is NOT periodic mod p with period
d; only its ZERO SET is. The shared hypothesis is therefore

    for each (a, d, p):  forall n, n % d = a % d  ->  p | s n

("p divides s on the whole class"), which both families satisfy by
DIFFERENT mechanisms -- ord_p(2) for exponential, alpha(p) for
Fibonacci-like -- and which is NOT decidable as stated. Consequences:

  * the abstract layer is ~15 lines and buys STATEMENT reuse only; the
    `decide` pipeline lives in the per-family bridges and does not
    abstract. It is a cheap correct refactor, NOT "the highest-leverage
    move available".
  * the highest-leverage move is instead parameterising the BASE
    (`2 |-> b`): nothing in FixedDivisor.lean uses the numeral 2, every
    proof goes through verbatim, and decidability is PRESERVED. That is
    lane A' below and it should precede everything else.


## LANES, in dispatch order

### A. Periodic-sequence generalisation of the criterion       [L, do first]

  Replace `A * 2^n + B` with a sequence `f : N -> Z` carrying, per
  covering class `(a, d, p)`, the hypothesis `p | f a` and
  `f (n + d) = f n (mod p)`. Everything downstream should follow.

  Unlocks: Wilf primefree Fibonacci-like sequences (lane H) and nothing
  else. Reduced from the original scope, which was wrong on two counts:

    * base-b Sierpinski/Riesel belongs to lane A' (base parameterisation),
      not here — it keeps decidability and this does not.
    * dual Sierpinski (`2^n + k`) is NOT an unlock: it is ALREADY the
      case `(A, B) = (1, k)` of the COMMITTED criterion. Zero new work.
      Witness derived 2026-07-31 by CRT back through the Selfridge
      skeleton: k = 58049738 (mod 70050435), first odd member
      128100173; some p in {3,5,7,13,19,37,73} divides 2^n + k for every
      n, and no member of the family is prime for n <= 40. Whether that
      k is a KNOWN dual-Sierpinski number is unchecked — no novelty
      claim attached.

  The abort condition is now answered: do it, but as the ~15-line
  zero-set layer described above, and expect statement reuse only.

### A'. Base-b parameterisation of the criterion            [S, DO FIRST]

  Replace the numeral `2` with a parameter `b` throughout
  `FixedDivisor.lean`. Nothing there uses `2`: the order bridge becomes
  `(b : Z)^d = 1 [ZMOD p]` and the per-class step is unchanged
  (`mul_left A`, `add_right B`). Decidability survives because
  `b ^ d % p = 1 % p` remains a ground check. Reaches base-b
  Sierpinski/Riesel (cf. A273987). Mechanical; highest value per line
  in this document.

### B. Brier numbers                                            [S]

  Simultaneously Sierpinski and Riesel. RISK RESOLVED 2026-07-31 — the
  stated risk ("whether kernel `decide` survives numbers of that size")
  is answered yes, and both certificates are verified.

  k = 3316923598096294713661 (Clavier). All four fields checked
  independently, both sides, zero uncovered residues, all divisors prime:

    Sierpinski (p | k*2^a + 1), L = 48, 7 triples, max 108 bits
      {(1,2,3), (2,4,5), (4,12,13), (0,8,17), (36,48,97), (20,24,241),
       (12,48,673)}
    Riesel (p | k*2^a - 1), L = 180, 13 triples, max 109 bits
      {(0,2,3), (0,3,7), (9,10,11), (11,18,19), (1,5,31), (23,36,37),
       (7,20,41), (10,60,61), (8,9,73), (5,36,109), (13,15,151),
       (25,30,331), (37,60,1321)}

  Load is L * |T| = 336 and 2340 against Selfridge's 252 — both far
  inside the measured ceiling below. Integer width (109 vs 44 bits) is
  the only thing that grows meaningfully, and Lean's Nat is GMP-backed.

  NO SHARED SKELETON. The two sides share only the prime 3 and the
  modulus 2; moduli are {2,4,8,12,24,48} vs {2,3,5,9,10,15,18,20,30,36,
  60}. A Brier certificate is two INDEPENDENT `IsFixedDivisorSystem`
  instances, not one structure with two residue assignments.

  NO CHEAPER WITNESS EXISTS: the record k is also the smallest. The
  next known (24 digits) is comparable, and the Vantieghem/Cohen-
  Selfridge 26-digit number needs 19 triples at 132 bits. The fallback
  in the old text — "a smaller worked witness" — has nothing to point
  at; if this lane runs, it runs on the record number.

  Do NOT source covering sets from primepuzzles.net without
  re-verifying: at least one entry there (Wesolowski's) fails Riesel
  coverage against the primes it lists.

  UNSWEPT: whether any proof assistant has a Brier number at all. The
  §4.1 prior-art sweep was scoped to the general criterion, not to
  Brier. Sweep before claiming.

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
  MEASURED 2026-07-31: a statement file `ErdosProblems/274.lean` IS
  present upstream in formal-conjectures (content unread — check
  before restating).

### E. Statement archives for the Erdos covering cluster        [S each]

  MEASURED 2026-07-31 against the formal-conjectures repo tree (GitHub
  API, recursive), NOT inferred. Naming is `ErdosProblems/NNN.lean`
  (509 files), not `ErdosNNN.lean`.

  RE-MEASURED 2026-07-31 (later, same enumeration method, still 509
  files): the covering-systems tag now returns 22 entries, not 20 —
  it adds 274, 1113 (and #277's status moved to "proved"). Updated:

    PRESENT upstream (do NOT duplicate):
      7, 203, 204, 273, 274, 275, 276, 277, 279, 280, 281, 1113
    ABSENT upstream (unchanged from the first measurement):
      2, 8, 27, 202, 278, 586, 947, 1188, 1189, 1190

  STATUS DRIFT on the absent list (per erdosproblems statuses,
  enumerated 2026-07-31): 202 and 1190 are "solved (Lean)", 947
  "proved (Lean)", 2/8/27/586 "disproved". (204 and 280 are also
  "disproved (Lean)", but they are PRESENT upstream, not absent.)
  So as ARCHIVE targets the absent list is mostly dead; the
  still-open, still-unclaimed set remains exactly #278, #1188, #1189
  as already scoped below. (A wide sweep attributes the #202/#1190
  solutions to GPT-5.4 Pro / Ho Boon Suan via Park-Pham —
  attribution UNVERIFIED, from the entry comment thread only.)

  CAVEAT (2026-07-31): "absent upstream" no longer implies "no Lean
  artifact anywhere". erdosproblems.com statuses now link per-problem
  Lean artifacts in personal repos — e.g. #16 (the 2^k + p cluster) is
  "disproved (Lean)": Chen 2023 (arXiv:2312.04120), formalized by
  D. Chin 2026-02-25 at github.com/danielchin/proofs
  `Proofs/ErdosProblems/Erdos16.lean`. That file builds two covered
  APs (residues 992077, 3292241 mod 11184810) from the SAME
  {3,5,7,13,17,241} / period-24 system as `NotTwoPowerPlusPrime`,
  coverage checked by `decide` — covering-congruence prior art in Lean
  that the covering-criterion.md §4.1 sweep (scoped to the criterion)
  did not cover. Sweep each entry's comment thread before any novelty
  claim, not just the formal-conjectures tree.

  This kills most of the lane as originally scoped: five of the seven
  entries previously nominated as "highest value" (#7, #203, #273, #276,
  #277) are already upstream. What is actually unclaimed AND open:

    #278   density of integers covered by congruences on a fixed
           modulus set. NOT a mere archive — the second question is
           SETTLED (minimum at all a_i equal). Attribution corrected on
           the entry 2026-03-03: Rogers, via Halberstam-Roth *Sequences*
           (1983) 5.3, THREE YEARS BEFORE Simpson 1986. Tao wrote it up
           2026-01-19. This is a provable target, not a statement.
    #1188  estimate F(x), the count of minimal distinct covering
           systems. Open.
    #1189  irreducible covering sets: count, extremal n_k, max sum 1/n_i.
           Open; the final sub-question is settled by Sun 2007.

  #7 is upstream as `erdos_7` over `StrictCoveringSystem ℤ` (sorry'd),
  so the statement is taken; note their moduli are `Ideal`s over a
  general ring, which is not decidable — a decidable restatement is a
  defensible separate contribution, but say so explicitly.

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
  a(0) = 20615674205555510, a(1) = 3794765361567513.

  CORRECTED: it is the RANK OF APPARITION alpha(p), not the Pisano
  period pi(p), that plays the role `ord_p(2)` plays for us — see THE
  CENTRAL OBSERVATION above, verified directly. The old sentence naming
  Pisano periods was wrong, and with it the claim that this lane is
  "the reason to do A before B or C".

  An 18-triple certificate exists (L = 8640, coverage verified, every
  `p | a(n)` confirmed on its full class over a whole period, and
  gcd(a(0), a(1)) = 1 — the coprimality side condition, which the
  covering argument neither uses nor produces). PROVENANCE WARNING: it
  was reconstructed computationally from A083216, NOT read off a paper —
  Vsemirnov's published 17 quadruples are for a DIFFERENT sequence with
  a partly different prime set. Re-derive independently before
  committing.

  Two costs to price before starting:
    * `decide` load is L * |T| = 8640 * 18 = 155520, about 600x
      Selfridge's 36 * 7 = 252. Against the MEASURED ceiling below this
      is roughly at the practical limit, not comfortably inside it.
    * the terms cannot be evaluated: a(8640) ~ 10^1805. Unlike
      `A * 2^a + B`, the bridge MUST be phrased entirely in `ZMod p`;
      a naive port of the existing certificate shape will not terminate.

  Sources: Graham, Math. Mag. 37 (1964) 322-324; Wilf, Math. Mag. 63
  (1990) 284; Vsemirnov, JIS 7 (2004) Article 04.3.7.

### I. A006285 de Polignac — OEIS note                           [S, non-Lean]

  A006285 = odd numbers not of the form p + 2^k: 1, 127, 149, 251, 331,
  337, 373, 509, ...

  DEMOTED 2026-07-31 after reading the live entry. Two problems:

  1. QUANTIFIER MISMATCH. `erdos_1950_not_two_pow_add_prime` carries
     `1 <= k`. OEIS allows k = 0 — that is precisely why 3 = 2 + 2^0 is
     ABSENT from the terms. The gap bites only at m = 3 (for odd m,
     m - 1 is even), so infinitude survives, but via a one-line patch
     the committed theorem does NOT contain. "Exactly the infinitude
     statement" is false as written.

  2. INFINITUDE IS ALREADY IN THE ENTRY, TWICE. Verbatim comments:
     "Crocker shows that this sequence is infinite; in particular,
     2^2^n - 5 is in this sequence for each n > 2." And: "The lower
     asymptotic density of this sequence is positive (Van Der Corput,
     1950; Erdos, 1950), and larger than 0.00905 (Habsieger and Roblot,
     2006)."

  So there is nothing mathematically to contribute. "Stronger than the
  label-retirement items already there" was backwards: label retirement
  changes an entry's epistemic status, this does not. Demote to a
  formalization link at most, or drop. USER decision.


## NON-GOALS — state these explicitly in any writeup

  * Izotov (1995): certain fourth powers are Sierpinski WITHOUT a
    covering set. NOTE 2026-07-31: whether Sierpinski numbers with NO
    finite covering set exist is itself Erdos #1113 (open,
    covering-tagged, keyed on A076336, statement present upstream) —
    cite it as the anchor when stating this non-goal. Izotov's route
    is the aurifeuillean factorization
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
