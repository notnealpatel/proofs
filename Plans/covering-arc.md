# Covering-systems arc

The covering-systems campaign as a self-contained formalization
program: landed infrastructure, open lanes C2-C7, non-goals, and
pending user decisions. The Erdos target queue that references these
lanes lives in erdos.md; publication standing lives in standing.md.

Sources: `git show 4901d3b:Plans/PLAN.md` sections COVERING ARC, NON-GOALS, USER DECISIONS PENDING items 1-4; reorganized 2026-08-10.


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
                                     sets — the alpha-layer lane C6 needs
  base-b generalisation     37e5f2e  C1 DONE (wave-3 P13):
                                     IsFixedDivisorSystemBase + base-b
                                     Sierpinski/Riesel, three witnesses,
                                     of_modEq_base transport

Sorry-free except the archived A039669 conjecture. Axioms within
{propext, Classical.choice, Quot.sound}. No native_decide.

## Lanes

  C2  (was A) Abstract sequence-level layer            [S]
      postdoc. ~15 lines: the shared statement both families instantiate
      (Fibonacci-like half landed at 3c7d4ef). Buys STATEMENT reuse only
      — the `decide` pipeline stays in per-family bridges. The shared
      hypothesis is NOT decidable as stated; families satisfy it by
      different mechanisms (ord_p(2) vs alpha(p)). May be partially
      subsumed by `IsFixedDivisorSystemBase` — verify-or-descope
      before dispatch.

  C3  (was B) Brier numbers                            [S]  SWEEP DONE
      postdoc. Simultaneously Sierpinski and Riesel;
      k = 3316923598096294713661 (Clavier), all four fields checked both
      sides, zero uncovered residues, all divisors prime:
        Sierpinski (p | k*2^a + 1), L = 48, 7 triples, max 108 bits
          {(1,2,3),(2,4,5),(4,12,13),(0,8,17),(36,48,97),
           (20,24,241),(12,48,673)}
        Riesel (p | k*2^a - 1), L = 180, 13 triples, max 109 bits
          {(0,2,3),(0,3,7),(9,10,11),(11,18,19),(1,5,31),(23,36,37),
           (7,20,41),(10,60,61),(8,9,73),(5,36,109),(13,15,151),
           (25,30,331),(37,60,1321)}
      Shape: TWO INDEPENDENT `IsFixedDivisorSystem` instances — the
      sides share only the prime 3 and the modulus 2. Loads 336 and 2340
      vs Selfridge's 252, far inside the measured ceiling. BOTH
      CERTIFICATES INDEPENDENTLY RE-VERIFIED 2026-08-05 (coverage,
      divisibility + ord, primality — all PASS; python3/sympy, sage
      absent in the probe environment). Warn: the record k is also the
      smallest — no cheaper fallback witness; do not source covering
      sets from primepuzzles.net without re-verifying (Wesolowski's
      entry fails Riesel coverage). NOVELTY SWEEP DONE 2026-08-05:
      ACL2 HAS mechanically verified Brier numbers — Cowles–Gamboa,
      "Verifying Sierpinski and Riesel Numbers in ACL2" (2011,
      arXiv:1110.4671), Appendix A: five k values with both covers
      checked by verify-sierpinski/verify-riesel macros (smallest
      143665583045350793098657; the word "Brier" never appears but
      the concept is explicit). No Lean/Isabelle/Coq/Mizar/HOL/Agda
      hit. Value framing: first LEAN formalization + the RECORD
      (smallest known) Brier k — Clavier's k is ~10^21, far below
      ACL2's five. Cite Cowles–Gamboa; claim no more.
      Adjacent: formal-conjectures issue #644 tracks Sierpinski/
      Riesel as absent upstream — our landed Sierpinski.lean/
      Riesel.lean already exceed it; possible upstreaming hook.

  C4  (was D) Mirsky–Newman theorem                    [M]
      postdoc. No disjoint distinct covering system exists (conjectured
      Erdos 1950; proved Mirsky–Newman, indep. Davenport–Rado; special
      case of Herzog–Schonheim). Root-of-unity argument, stated directly
      on the committed `IsCoveringSystem`. Strongest classical target in
      reach. GATE RESOLVED 2026-08-05: upstream `ErdosProblems/274.lean`
      was READ — it states Erdős #274 / Herzog–Schönheim over GROUP
      cosets (all three theorems sorry'd; the abelian variant is tagged
      "solved" pointing to an external proof by Jostamon, body still
      sorry). It does NOT state integer Mirsky–Newman — the
      integer-AP statement on our `IsCoveringSystem` is not taken
      upstream. NOVELTY SWEEP DONE 2026-08-05: NO Mirsky–Newman /
      Davenport–Rado proof found in any assistant (GitHub, mathlib4,
      Zulip, erdosproblems threads, AFP-adjacent, arXiv — all
      searched). First-formalization candidate. UNRESOLVED THREAD:
      274.lean's abelian-variant tag reportedly points to an external
      proof by "Jostamon", but the sweep found no such artifact — the
      lane MUST resolve that pointer from the file itself before any
      novelty claim. Paper trail: abelian case is Sun 2004; the
      integer theorem is Mirsky–Newman via the root-of-unity /
      Davenport–Rado argument.

  C5  (was E) Erdős-problem targets                    [S each]
      Measured against the formal-conjectures tree (recursive, API),
      509 files; covering-systems tag = 22 entries.
      PRESENT upstream, do NOT duplicate:
        7, 203, 204, 273, 274, 275, 276, 277, 279, 280, 281, 1113
        (7 and 274 present, 278/1188/1189 absent — re-verified
        against the live tree 2026-08-05)
      Unclaimed AND open (statuses re-pulled from erdosproblems
      2026-08-05):
        #278   fixed-modulus-set covered density. NOT a mere archive —
               the MINIMUM question is SETTLED (minimum at all a_i
               equal; Rogers via Halberstam–Roth *Sequences* (1983)
               5.3 per JonahKlein comment 2026-03-03, three years
               before Simpson [Si86]; Tao writeup 2026-01-19,
               terrytao.wordpress.com "Rogers' theorem on sieving").
               The MAXIMUM question stays open. Provable target:
               postdoc formalizes the Rogers/Simpson minimum
               (inclusion-exclusion over lcms).
        #1188  count of minimal distinct covering systems F(x). Open.
               CAVEAT (Woett/Bloom thread, Apr 2026): the site's
               statement is Bloom's reinterpretation — Erdős's [Er80]
               original asks about moduli distinct ACROSS systems,
               where Hough bounds F(x) uniformly. Archive the site's
               form and say which one it is. Woett's elementary
               F(x) >= floor(log_12 x) is a provable fragment.
        #1189  irreducible covering sets. Open; final sub-question
               settled by Sun 2007 (divisors of 2^(p-1)·p form an
               irreducible covering set — an explicit certificate our
               layer can check); Simpson [Si85]: n_k <= 2^(k-1).
               Archive + the Sun instance as the settled fragment.
      #7 upstream is `erdos_7` over `StrictCoveringSystem Z` (sorry'd,
      Ideal moduli, not decidable) — a decidable restatement is a
      defensible separate contribution, but say so explicitly.

  C6  (was H) Wilf primefree sequence A083216          [M]  PROBE FIRST
      Fibonacci-like, every term composite, consecutive coprime.
      a(0) = 20615674205555510, a(1) = 3794765361567513. Alpha-layer
      LANDED (3c7d4ef) and API CONFIRMED READY 2026-08-05: the
      per-class step is `IsFibonacciLike.forall_mod_eq_dvd`
      (needs only 0 < m, alpha(m) ∣ d, one base divisibility — the
      exact analogue of FixedDivisor's order bridge); non-degeneracy
      discharges from `not_dvd_zero_and_one_of_isCoprime`, which is
      A083216's coprime initial pair. `IsFibonacciLike` is pinned to
      s(n+2) = s(n+1) + s(n) — fine here, but do not promise general
      two-term recurrences. alpha(p), not the Pisano period, plays
      ord_p(2)'s role. `decide` load L*|T| = 8640*18 = 155520, ~600x Selfridge —
      AT the measured practical limit, not inside it: GATE dispatch on a
      scaled decide probe first. Terms are unevaluable (a(8640) ~
      10^1805) — the bridge MUST live entirely in `ZMod p`; a naive port
      of the existing certificate shape will not terminate. Warn: the
      18-triple certificate (L = 8640, coverage verified, gcd(a0,a1)=1)
      was reconstructed computationally from A083216, NOT read off a
      paper — Vsemirnov's 17 published quadruples are for a DIFFERENT
      sequence. Re-derive independently before committing.
      Src: Graham, Math. Mag. 37 (1964) 322–324; Wilf, Math. Mag. 63
      (1990) 284; Vsemirnov, JIS 7 (2004) 04.3.7.

  C7  NEW micro-lane: drop `1 ≤ k` from erdos_1950
      MECHANICS PINNED 2026-08-05. The `1 ≤ k` sits INSIDE the negated
      existential of `erdos_1950_not_two_pow_add_prime` (`¬ ∃ k p,
      1 ≤ k ∧ ...`), so removing it STRENGTHENS the theorem. The k = 0
      case is already paid for: the covering class 0 (mod 2) with
      p = 3 gives 3 ∣ m − 2^0 (docstring on
      `exists_mem_erdosPrimes1950_dvd` says so explicitly), and the
      general-criterion rederivation
      `not_prime_sub_two_pow_of_general` ALREADY dropped the
      hypothesis. Only the bespoke `not_prime_sub_two_pow` + the final
      packaging still carry it. Genuinely small; do it regardless of
      USER decision 3 — it makes the flagship match A006285's k ≥ 0
      convention.


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
  * Attack on HOLD archives stays on hold: A064097 2.5·log upper,
    A267632 2^j case, A000001 non-coprime submultiplicativity, A250109
    (circuit model). Shelved by ruling: A031507, A060748 (no MW layer).


## USER DECISIONS PENDING

  1. Does the covering arc seed a SEPARATE ITP/CPP paper, or join
     the OEIS-first-proofs paper (pointer sheet retired 2026-08-10,
     `git show 7d7a0d8:Documents/first-proofs-and-opn-reduction.md`;
     running order compressed in standing.md) as a fourth
     result? My read: separate — it is a formalization-infrastructure
     paper, not an OEIS-first-proof paper.
  2. Scope Hough–Nielsen yes/no.
  3. A006285 note yes/no (recommendation: no; C7 covers the substance).
  4. Whether to upstream `Basic` + `FixedDivisor` to Mathlib. Mathlib
     has ZERO covering-system content; impact is real and durable,
     review latency is long, and the API would need reshaping first.
  5. (Resolved in progress.) Whether `Manuscripts/` and `.tasks/` stay
     outside version control — `.tasks` retirement is underway; see
     debt.md.
