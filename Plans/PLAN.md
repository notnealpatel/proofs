# PLAN — campaign dispatch plan and target queue

This file is the forward dispatch plan for ALL active arcs. Coalesced
2026-08-09: it absorbed the full prioritized target queue from
`NEXT_TARGETS.md` (deleted); per-lane landed-work records (waves 1–3)
moved to `RESULTS.md`. `Formalize/INDEX` stays the ledger of card
metadata but is NOT the dispatch state of record — it is stale (chore
X2); trust git and the tree over both documents.

Correction history is in `git log -p` on this file and its ancestors
(`PLAN.md`, `NEXT_TARGETS.md` at repo root, then `Plans/`). Several
claims here have been wrong before; when one moves, move it and let the
commit record why.


## PROTOCOL — deltas of 2026-08-05

  Lanes    `prover` = Fable 5 xhigh: scarce-by-cost; holds only the item
           with the largest gap between "stated" and any known formal
           route. `postdoc` = Opus 5 Max: throughput; literature-
           following routes, grindy lanes, statement archives.
  Review   Orchestrator-dispatched ONLY, after a writer lane halts:
           parallel vacuity-cop + reviewer, orchestrator applies fixes,
           one commit per lane, writers never commit. Lanes MUST NOT
           self-audit (prover/postdoc agent files carry the MUST NOT); a
           lane-relayed PASS is an unverified claim — re-audit it.
  Cop      vacuity-cop rung 5 (new): source-fidelity — hunt LLM
           mis-translation, hallucinated conjectures, and prose-to-
           formal divergence against PRIMARY sources (`oeis show`,
           fetched papers), never against the `Formalize/` card, which
           is itself an LLM relay.
  Writers  STYLE.md first; `flock .lake/agent.lock lake build`;
           systemd-run memory fence; `oeis show` ground truth before any
           Lean statement; halt-never-weaken.


## CHORES — cross-cutting, start before or alongside wave dispatch

  X1  Adopt `leanprover-community/axiom-audit` (allowlist-subset check,
      runs over `.olean`, catches transitive deps, community-maintained)
      and retire the five stale hand-rolled sweeps under
      `Proofs/Scratch/` (Ad1AxiomSweep, Aw1AxiomAudit, Le1AxiomAudit,
      Secp256k1AxiomAudit, ShearReviewAudit) with `goof rm` — only
      after parity is demonstrated by planting both a native_decide
      proof and a `sorry` and watching the new tool fire. Measured facts
      behind this are under AXIOM HYGIENE below.
  X2  Refresh `Formalize/INDEX`: record the landed-but-unrecorded files
      — FixedDivisor/Sierpinski/Riesel/Erdos1950Instance (9d873d7,
      5157ca8), RankOfApparition (3c7d4ef), ZumkellerSigmaHalf +
      MultiperfectZumkeller + nine A083207 instances (3e593ab), the
      NederGap stub state, and the ShearEC arc — CORRECTED 2026-08-05:
      T1–T4 are fully covered and sorry-free (T1 =
      TotalDegreeAeval + ShearCircuit, T2 = ShearInversionLB +
      Secp256k1Prime, T3 = ShearQuadraticRank + ShearAddition, T4 =
      ShearAdditionEC + ShortCurveScaling + VariableChangePointEquiv),
      but `ShearAdditionChains.lean` (T5) is a THREE-LINE EMPTY STUB —
      the min-shears-for-x^n = l(n) bridge does not exist; it joins the
      A003313 lane as the natural sibling. Strike the STATEMENTS
      rows that landed; mark queue items 2–5 follow-ons accurately
      (Sierpinski/Riesel follow-on is DONE). Two spec files INDEX
      cites do not exist anywhere (review-vacuity-SlizkovDoubling.md,
      review-vacuity-ErdosLovasz.md) — note the citations as dead.
      X2 should additionally record the wave 2–3 landings (RESULTS.md).


## DISPATCH STATE — as of 2026-08-09

Waves 1–3 (dispatched 2026-08-05) are fully landed; per-lane results,
commits, and brief corrections are in `RESULTS.md`. Wave 5 was briefed
2026-08-06 (`Prompts/User/20260806_WAVE5.md`: C7, C3, C4, P15 Switkay,
P16 defect identity, P17 #376 digits, P18 A222603, and an archive batch
#1213/#384/#673/#1062/#1160/#18) but NONE of its targets have landed —
every wave-5 item remains open in the queue below. Landed outside the
queue since 2026-08-06: Erdős #406 sieve bound + method barrier
(4455bf3, La09 Thm 1.4 λ=1 case) and the Noe original↔repaired bridge
(49f30bd).


# TARGET QUEUE

Updated 2026-08-06 after wave 3 + follow-on lanes; landed rows removed
(see `RESULTS.md`).

## Summary statistics (post wave 3)

- Original candidates: 104
- Landed waves 1–3: ~40
- Remaining open: ~64
- Dropped after audit: 5 (unchanged)

Split cards (archive + provable fragment) are listed once,
in their primary section, with the fragment in Notes.

## 1. Formalize (sorry'd archives)

The sketch files already exist; "landing" a card means:
audit the statement against the primary source
(vacuity-cop rung 5), close the provable sanity-layer
sorrys, and commit with the intended sorry(s) only.

### Tier F1 — Small effort, high infrastructure reuse

| Target | Source | Effort | Reuses | Notes |
|--------|--------|--------|--------|-------|
| A005153 Switkay | OEIS T1 | S | `Nat.Practical`, `StewartCriterion` | Melfi landed → the card's `melfi` sorry becomes an import. Parity reduction provable. |
| Erdős #242 / A192787 Erdős–Straus (merged) | both sweeps | S | none new; cleared-denominator `Nat` form | Archive-primary. Fragments: `erdosStraus_of_prime` + Mordell residue classes (effort M) are P2-grade work the card should carry. |
| Erdős #405 (p−1)!+a^(p−1)=p^k | Erdős B | S | none | Pin the odd-p solution set from Yu–Liu before stating (DB examples use p=2). |
| Erdős #677 lcm blocks | Erdős UB | S | `Erdos440/LcmCount` | Two coincidence witnesses by `decide`. |

### Tier F2 — Medium effort

| Target | Source | Effort | Reuses | Notes |
|--------|--------|--------|--------|-------|
| A131646 Sloane bases | OEIS T2 | M | `Nat.digits` | Base-reduction lemma (only 11..18 matter) provable; 20-term certificates. |
| A141386 Sun quadratic | OEIS T2 | M | none | Bounded-search decidability for the 7 exceptions; GRH-conditional decidability noted in sketch. |
| A007850 Lava Giuga | OEIS T2 | M | fresh `ad` (arithmetic derivative) — reusable infra | Archive-primary; the provable direction (n′=n+1 → Giuga) is a P2-grade fragment the card should close. |
| A349044 non-Brauer | OEIS T2 | M | `IsAddChain`, `l` | Brauer-chain def is the natural sibling of the T5 `ShearAdditionChains` stub; certifying 12509 is expensive but bounded. |
| A293771 Whitney machine | OEIS T2 | M | fresh ~30-line semantics | Quantifier-order trap documented with finite refutation; third computation model beside `complexity` and chains. |
| A309370 Sidon hypercube | OEIS T3 | M | fresh `IsSidon` — reusable | Promote `IsSidon` out of `Scratch` on landing; trivial upper bound provable. |
| A390813 Sidon squares | OEIS T3 | M | `IsSidon` from A309370 | Land after A309370; greedy n^(1/3) lower bound provable. |
| A046094 Agoh–Giuga | OEIS T3 | M | Mathlib `bernoulli`, von Staudt–Clausen | Archive-primary; forward direction (prime → congruence) is a P3 fragment. |
| A209312 symmetric practical | OEIS T3 | M | `Nat.Practical` | Low priority — fiddlier and weaker than Switkay; Hasler parity split is the one useful lemma. |
| A373686 Somu–Tran | OEIS T2 | M | `Nat.Practical`, `StewartCriterion` | Two-squares conjecture archive-only (threshold ~exp(2·10^80)); Thm 1 fragment is P2. |
| A000009 Sun conj 2 | gaps #6 | M | partition machinery from A000041 card | Audit: still open (verified to 2·10^6). Card conj 2 only (a(n) ∤ p(n), p(n)±1); conj 1 is a clone of the marginal A000041 antichain pattern — do not card it. Computable p(n) bridge is the M cost. |
| A003135 factorial products | OEIS T3 | M | `Nat.factorial`, `Multiset` | Statement audit cost is real; finiteness-via-Bertrand fragment is P3. |
| Erdős #781 waves | Erdős B | M | none | GATE: sage-probe the first failing k before committing — Alon–Spencer is asymptotic, small k may satisfy equality. |
| Erdős #895 Schur triples | Erdős B | M | none | Small-n counterexample layer provable; n ≥ 18 needs DRAT/LRAT replay the repo lacks. |
| Erdős #86 C4-free Q_n | Erdős B | M | none | Q_n over `Fin n → Bool`; certificate layer for Q9–Q15. |
| Erdős #81 chordal cliques | Erdős B | M | none | GATE: check Woett's external Lean repo first (a (1/4−1/133)n² bound is already formalized elsewhere). |
| Erdős #5 prime gap limit points | Erdős B | M | `Nat.nth`, `Filter` | Statement archive only; see natural-density gap in cross-cutting notes. |
| Erdős #439 monochromatic squares | Erdős D | M | none | Archive + finite-instance `native_decide` layer. |
| Erdős #362 subset-sum concentration | Erdős D | M | none | `antichain_bound` fragment S–M; check Mathlib Littlewood–Offord via leandoc first. |
| Erdős #203 2D Sierpinski | Erdős UB | M | `Covering/Sierpinski` | Two-parameter covering def; no decidable fragment in reach (audit-confirmed). |
| Erdős #1020 matching conjecture | Erdős UB | M | none | Extremal-family binomial identities provable S–M; Frankl bound is the re-entry point if compression ever ports. |
| Erdős #1093 deficiency | Erdős UB | M | k-smooth predicate (shared with #684/#1094/#1095) | Certificates decidable. |
| Erdős #1094 least prime factor | Erdős UB | M | least-prime-factor lemmas | 14 exceptions decidable. |
| Erdős #548 Erdős–Sós | Erdős UB | M | none | Use the standard (stronger) edge bound, not the DB's "+1" form; Erdős–Gallai path case is a P3 fragment. |
| Erdős #684 smooth part | Erdős UC | M | BINOM valuations | The u·v smooth/rough decomposition def is the deliverable — feeds #1093/#1094/#1095. |
| Erdős #80 books | Erdős C | M | none | Archive; the c > 1/4 slice needs a Turán-type theorem Mathlib lacks — defer the fragment. |

### Tier F3 — Large effort

| Target | Source | Effort | Reuses | Notes |
|--------|--------|--------|--------|-------|
| A323653 | wave-2 P8 batch | L | needs A276086 primorial-base + A003961 prime-shift defs | The one unlanded P8 item; def layer is heavy by prior ruling — keep last. |
| A222603 practical tree | OEIS T3 | L | `Nat.Practical`, `SimpleGraph`; Melfi prerequisite | Successor well-definedness needs Melfi; acyclicity provable, connectivity is the conjecture. |
| A005153 Sun root-decreasing | OEIS T3 | L | `Nat.Practical`, asymptotics toolbox | Limit half known (Weingartner) but needs practical-counting asymptotics; monotonicity open. |
| A000041 Sun antichain | OEIS T3 | L | partition machinery | Sketch's own review: weakest candidate; archive only, never schedule proof work. |
| A265262 Erdős–Turán | OEIS T3 | L | fresh `profile`, `IsBasis2` | Archive-primary; the König tree-equivalence is the valuable P3 fragment. |
| Erdős #577 disjoint C4s | Erdős D | L | none | ~45-page proof; statement archive at most. |

## 2. Proof attempt targets

`prover` is scarce (largest stated-to-route gap only);
everything else is `postdoc`. Efforts are the sketchers'
calls, corrected by audit where noted. The covering lanes
C2–C7 in this tier are detailed under COVERING ARC below.

### Tier P1 — Highest confidence (elementary proof, existing infra)

| Target | Source | Agent | Attack surface | Reuses |
|--------|--------|-------|----------------|--------|
| C2 abstract sequence layer | covering arc | postdoc, S | ~15 lines, piggyback on C1; statement reuse only. | `FixedDivisor`, `RankOfApparition` |
| C3 Brier numbers | covering arc | postdoc, S | Two independent `IsFixedDivisorSystem` instances; both certificates re-verified 2026-08-05; loads far inside the measured ceiling. First Lean + record-k framing; cite Cowles–Gamboa (ACL2). | `FixedDivisor`, `Sierpinski`, `Riesel` |
| C4 Mirsky–Newman | covering arc | postdoc, M | Root-of-unity argument on committed `IsCoveringSystem`; novelty sweep clean; MUST resolve the 274.lean "Jostamon" pointer before claiming first-formalization. | `Covering/Basic` |
| C7 drop `1 ≤ k` | covering arc | postdoc, S | k = 0 case already paid for; strengthens the flagship to A006285's convention. | `NotTwoPowerPlusPrime` |
| Erdős #1213 Hegyvári | Erdős A | postdoc, S | Pigeonhole on interval-sum residues; zero new defs. Best payoff-per-effort in the Erdős sweep. | `Finset.sum` vocabulary |
| Erdős #384 Ecklund | Erdős A | postdoc, S | Corrected statement already in sketch (n ≥ 2k, p ≤ n/2, (7,3) exception); elementary via Bertrand. | Kummer machinery in `Erdos175` |
| Erdős #673 divisor ratios | Erdős C | postdoc, S | Tao's trivial route: τ(n)/4 ≤ G(n) ≤ τ(n) pointwise; density half stays archived. | `Nat.divisors` |
| Erdős #1062 no a∣b, a∣c | Erdős UA | postdoc, S | Interval [m+1, 3m+2] gives f(n) ≥ ⌈2n/3⌉; small exact values decidable. | Finset divisibility |
| Erdős #1160 m = 2, 3 cases | Erdős UB | postdoc, S/M | Skim verdict: `erdos_1160_m2` provable NOW from landed gnu lemmas; m = 3 provable-with-work. Headline stays archived (gnu(64) = 267 is out of certified range). | `GroupCount/Gnu` |

### Tier P2 — Medium confidence

| Target | Source | Agent | Attack surface | Reuses |
|--------|--------|-------|----------------|--------|
| A002093 highly abundant → practical | gaps #6 | postdoc, M | Audit UPGRADE from archive: Eppstein 2015 gives an essentially complete argument (smallest-missing-prime P < p² bound + Stewart criterion + Alaoglu–Erdős divisibility-by-4 for large n). GATE: verify the blog argument end-to-end first; it settles a live OEIS conjecture, so the bar is high. | `StewartCriterion`, `Practical`, Mathlib `sigma` |
| C5 Erdős #278 Rogers minimum | covering arc | postdoc, M | Inclusion–exclusion over lcms (Rogers via Halberstam–Roth; Tao 2026 writeup). Maximum question stays archived. | `Covering/Basic` |
| C6 Wilf A083216 | covering arc | postdoc, M | Alpha-layer API confirmed ready; GATE on the scaled `decide` probe (155520 load is AT the ceiling); bridge must live in `ZMod p`; re-derive the 18-triple certificate independently. | `RankOfApparition`, `IsFibonacciLike` |
| C5 Erdős #1188 fragment | covering arc | postdoc, S | Woett's elementary F(x) ≥ ⌊log₁₂ x⌋; archive the site's (Bloom-reinterpreted) statement and say which form it is. | `Covering/Basic` |
| C5 Erdős #1189 fragment | covering arc | postdoc, S | Sun 2007 irreducible-covering certificate (divisors of 2^(p−1)·p) checked by the existing layer; archive the rest. | `Covering/Basic` |
| Erdős #1058 Luca n!+1 | Erdős A | postdoc, M | Five `decide` certificates + 4-page elementary tail (factorial divisibility + Bertrand). Full closure of an Erdős problem plausible. | certificate-then-tail pattern from `ErdosMinus2k` |
| Erdős #482 Graham–Pollak | Erdős A | postdoc, M | Computable recurrence, short induction; floor-to-binary bridge is the fiddly part. | Mathlib `Real.sqrt`, `Nat.floor` |
| Erdős #916 Thomassen | Erdős A | postdoc, M | ~5-page direct argument; primitives exist; Walk-API friction is the risk. | `SimpleGraph` experience from Erdos715 |
| Erdős #58 Gyárfás headline | Erdős A | postdoc, M | Prove χ ≤ 2k+2, sorry the equality case (L). | Mathlib `chromaticNumber` |
| Erdős #77 Ramsey layer | Erdős C | postdoc, M | R(k) def (~50 lines) + classical bounds (probabilistic lower, pigeonhole upper) + R(3) = 6; unlocks #781 and #112. | new def, high downstream reuse |
| Erdős #699 binomial gcd | Erdős UA | postdoc, M | Finiteness-per-(i,j) + balanced n = 2j case via the product identity; window provable. | BINOM arithmetic; Sylvester–Schur (P3) strengthens it later |
| Erdős #856 lcm sunflowers | Erdős UA | postdoc, M | Er70 upper bound is a short prime-counting inequality; natural second client of Naslund–Sawin. | `Erdos857/NaslundSawin`, Mathlib Chebyshev |
| Erdős #273 moduli p−1 | Erdős UA | postdoc, S–M | Verify Selfridge's p ≥ 3 certificate on the existing layer; gate the p > 877 obstruction on a scaled probe. | `Covering/Basic` |
| Erdős #727 Balakran k=1 | Erdős UC | postdoc, M | (n+1)² ∣ C(2n,n) infinitely often via Catalan numbers (in Mathlib); k ≥ 2 stays open/archived. | Mathlib Catalan + factorial valuations |
| Erdős #901 m(3) = 7 | Erdős UC | postdoc, M | Fano-plane finite theorem + m(2) = 3 + union-bound lower; entry point to finite probabilistic arguments. | proper-2-coloring defs shared with #836 |
| Erdős #18 h(m) layer | Erdős UC | postdoc, M | Define h, prove h(n!) < n, certify the n = 3..11 table. | `Practical.lean` |
| Erdős #849 Singmaster instances | Erdős UC | postdoc, S–M | "C(n,k) = 3003 has exactly 4 solutions" (and a = 120, t = 3) as finite theorems once monotonicity bounds n. | binomial monotonicity |
| Erdős #1100 τ⊥ | Erdős UC | postdoc, M | ω(n) ≤ τ⊥-type bounds on the sorted divisor list; adjacent to Schinzel–Szekeres work. | `Erdos542` |
| Erdős #663 least non-dividing prime | Erdős UC | postdoc, M | Easy (1+o(1))·k·log n bound via primorial growth. | Mathlib Chebyshev-adjacent |
| Erdős #124 BEGL {3,4,7} | Erdős UC | postdoc, M–L | Sorted-partial-sum completeness criterion (belongs in `Enumerative` regardless) + the explicit {3,4,7} bounded target. | complete-sequence defs |
| A351243 SL refutation | OEIS T2 | postdoc, M | Certify 247 as a counterexample via balanced-ternary automaton + proved search bound — formally settles a disproved conjecture. 3^m+4 infinitude stays archived. | `Nat.digits`-style machinery; new A147991 def |
| A045652 Schur numbers | OEIS T2 | postdoc, M | a(2) = 4, a(3) = 13 by witness + `decide`; Schur's 1916 finiteness theorem is missing from Mathlib and is the real prize; archive a(4), a(5). | fresh `SumFree`/`SchurColorable`; `Erdos880` adjacency |
| A007850 provable direction | OEIS T2 | postdoc, M | n′ = n+1 → Giuga via squarefreeness + per-prime condition; lands inside the F2 card. | fresh `ad` def |
| A373686 Thm 1 | OEIS T2 | postdoc, M | Somu–Tran Thm 1 (practical + triangular, NO threshold) is completable; literature-following. | `Practical`, `StewartCriterion` |
| Erdős #834 Li construction | Erdős C | postdoc, M | 9-vertex 3-uniform witness; 3^9 colorings is `native_decide`-sized; seeds the hypergraph def layer. | new hypergraph defs (shared with #836/#901/#1020) |

### Tier P3 — Speculative but worth trying

| Target | Source | Agent | Attack surface | Reuses |
|--------|--------|-------|----------------|--------|
| Erdős #683 Sylvester–Schur | Erdős UC | prover, L | Erdős's elementary proof; not in Mathlib; load-bearing for #699/#1094/#1095 and the #175 remainder. The single most valuable classical target in the BINOM family. | BINOM valuations |
| Erdős #702 Frankl | Erdős C | prover, M–L | Needs a fresh shifting lemma; would deepen the extremal-set lane beyond sunflowers. | `Erdos20` compression experience |
| Barker cliques A135908/09 | gated, now open | prover, S/L | The gate ("after P5, S_n machinery felt out") is now satisfied: P5 landed and `SubgroupCountSn` exists. Max-abelian-subgroup-of-S_n theorem is where it may stall. | `GroupCount`, `SubgroupCountSn` |
| Erdős #112 Hunter–Steiner path variant | Erdős C | postdoc, M | Exact k(n,m) = (n−1)(m−1) for the directed-path variant; ~100 lines of tournament infra Mathlib lacks. | new tournament defs |
| Erdős #130 Anning–Erdős 1945 | Erdős C | postdoc, M–L | Classic self-contained Euclidean argument; opens a `EuclideanSpace` lane the repo has not touched. | none — new lane |
| Erdős #836 intersection bound | Erdős UA | postdoc, M | Erdős–Lovász r/log r bound, same paper as the landed g(k) work. GATE: verify the claimed 2026 proof of the second question against the live entry first. | `ErdosLovasz`, #901 defs |
| Erdős #276 Vsemirnov certificate | Erdős UA | postdoc, M | Direct second instance of the C6 alpha-layer machinery — strictly after C6 lands and its probe passes. | `RankOfApparition`, C6 lane |
| A172161 conditional asymptotic | OEIS T3 | postdoc, M | Recurrence → Θ((3/2)^n) via monotone convergence (verified sound by sketch); the recurrence itself is the open sorry. | asymptotics toolbox |
| Erdős #1178 BES73 lower bound | Erdős UC | postdoc, M | Finite hypergraph construction in existing vocabulary; equality direction (regularity) permanently out of scope. | hypergraph defs |
| Erdős #688 sieving certificates | Erdős UC | postdoc, M | Concrete a_p interval-covering certificates as verified lower-bound data points. | interval-covering def (new, small) |
| Erdős #117 abelian covers | Erdős UC | postdoc, M | Probe first: no computed h(n) table exists anywhere. | `GroupCount` |
| Erdős #1095 EES74 lower bound | Erdős UC | postdoc, M–L | g(k) > k^(1+c); small values decidable via A003458. | BINOM + #376 Kummer layer |
| Erdős #993 tree sweep | Erdős B | postdoc, S–M | `native_decide` unimodality sweep over trees ≤ 15 vertices; a counterexample resolves the problem, a clean sweep is a verified partial result. Either outcome lands. | `SimpleGraph` |

## 3. Unknown/unsorted

| Target | Source | Blocker | Next step |
|--------|--------|---------|-----------|
| A080210 DCS multiplicity | OEIS T2 | Entry defines neither "multiplicity" nor cites a proof; reconstructed reading unverified | Read the Zamojski survey; reclassify or drop. |
| Erdős #1064 φ(n) > φ(n−φ(n)) | gaps #6 | Solved (Luca–Pomerance 2002), but Mathlib has NO natural density — "almost all" is unstatable faithfully (Schnirelmann.lean line 40 TODO, verified live) | Decide on a `naturalDensity` infra lane (see cross-cutting); the 15·2^k counterexample family alone is trivial. |
| Higman PORC | gaps #6 | Open but community-expected false (du Sautoy–Vaughan-Lee 2012 at p^10); high def cost (PORC functions + gnu quantifiers), zero sanity layer | Record as a documentation note in `GroupCount`; no Lean card unless the USER wants a likely-false archive. |
| A000670-egf-family | gated | Needs an EGF layer Mathlib lacks — an infrastructure arc, not a lane | Scope the EGF design separately; do not dispatch. |
| Hough–Nielsen (2 or 3 divides some modulus) | gated | XL; an ITP paper on its own | USER decision 2, unchanged. |
| Excluded-63 re-triage | gaps #6 §1 | Only 8 of 63 upstream files were classified (all stubs); 55 solved problems with unclaimed proofs remain unassessed — #387/#851/#937/#1064 audited, all deep or blocked | Dispatch the Tier-A triage over the remaining ~55; highest expected yield per hour of any process item. |
| Algebraic-complexity lane | gaps #6 §2 | No database indexes the repo's deepest arc; A075099 killed on audit (contested def) | Literature-sourced mining: Bürgisser–Clausen–Shokrollahi problem list + Landsberg open problems. |
| GreensOpenProblems/ + Kourovka/ | gaps #6 §5 | 53-file Green list and Kourovka group-theory tree unmined | Next mining sweep stage; also align defs with `FormalConjecturesForMathlib`. |
| A093682 per-row forms | wave-2 P7 | Commit `f105bf4` names only A092482; whether the A093682 rows (A004793, A033157, A093678–81) landed is unverified | Check the committed file; unlanded rows are P2-grade follow-ons on `StanleyDigits`. |

## Cross-cutting notes

Dropped after the paired audit, with reasons — do not
re-mine these: Erdős #387 (solved negatively, BNPZ26;
sieve theory absent from Mathlib; covering piece already
formalized externally by Naprienko), Erdős #937 (BBC24 is
Mordell–Weil existence, not a checkable family; smallest
example has 111 digits), Erdős #851 (Tao verbatim: "barely
possible... non-trivial challenge"; fundamental lemma of
sieve theory not in Mathlib), A005820/A027687/A046060
(completeness implies no odd perfect number — strictly
harder than OPN, plus a recorded contrary conjecture),
A075099 (unattributed guess on a contested definition;
the def is a DAG-computation model, not ~30 lines).

Natural density is the largest single Mathlib gap this
queue hits: it blocks faithful statements for Erdős #1064,
the density halves of #673 and #1100, parts of #5, and the
A005153 root-decreasing limit. A small `naturalDensity`
def + basic API would upgrade several archive cards at
once. Worth scoping as its own micro-lane before the next
wave.

Sequencing that matters (updated post wave 3):
(1) Melfi LANDED → Switkay/A222603/A373686 NOW unblocked.
(2) Kummer LANDED → #699/#1093/#1094/#1095 unblocked; #406
    also landed. (3) A309370 before A390813 (shared
`IsSidon`). (4) C1 LANDED → C2 unblocked; C7 is ~15 lines;
C3 (Brier) is ~100–150 lines. C6 probe before C6 and
before #276. (5) Hypergraph def layer (#834 first) before
#836/#901/#1020/#1178. (6) Sylvester–Schur (#683) is the
one target where a prover lane changes the reachable set.

Statement-fidelity gates carried over from the sketches:
#405 odd-p solution set, #781 first-failing-k probe, #81
Woett dedup, #836 second-question status, #548 edge-count
form, A141386 literature check, and every 2025–26
AI-assisted site comment cited in `ERDOS_CANDIDATES.md` —
re-fetch before building on any of them. `oeis show` /
`erdos fetch` ground truth before any Lean statement,
per PROTOCOL.

Chores X1 (axiom-audit adoption) and X2 (INDEX refresh)
above remain open and are not proving targets.

## Process recommendations (from MINING_GAPS.md, now deleted)

1. Re-triage the excluded 63 `formalized=yes` stubs — highest
   expected yield per hour (only 8 of 63 checked; all stubs).
2. Add one-hop xref BFS from all carded seeds (33% hit rate).
3. Move OEIS mining off the search endpoint onto bulk dumps
   (`stripped.gz` + full-entry fetches); add "proved by" mining.
4. Mine `GreensOpenProblems/` (53 files) and `Kourovka/` in
   formal-conjectures; align defs with `FormalConjecturesForMathlib`.
5. Open a literature-sourced lane for algebraic-complexity
   (no database will ever index it).
6. Re-pull every entry immediately before carding.
7. Once per campaign, name-check each arc's flagship conjecture.

## New targets from wave 3 (2026-08-06)

Wave 3's 16 commits opened lines of inquiry absent from
the 104-candidate queue. Ranked by value per effort.

| Target | Source | Effort | Reuses | Notes |
|--------|--------|--------|--------|-------|
| Defect exact identity: `v_p(n−e) = v_p(C(n,k)) + v_p(k) + v_p(C(k−1,e))` at defect-1 points | 5af455e docstring | S | `Erdos1063/DefectCarryBound` | P1-grade. `≤` half landed; rest is ultrametric case split, ~30–50 lines. Do NOT card the prime-k strengthening (structural dead end). |
| Erdős #376 digit equivalence (A030979) | 626822b + 4bb6675 | S | `Erdos175.prime_not_dvd_centralBinom_iff_digits` | C(2n,n) coprime to 105 ↔ base-3/5/7 digit conditions. Discharges 4/6 sorrys in `E376.lean`. |
| `of_modEq_base` transport corollaries | 37e5f2e | S | `IsFixedDivisorSystemBase` | Base-14 Sierpiński → all b ≡ 14 (mod 15), ~15 lines. Dispatch alongside C7. |
| A102483 Sloane 1973 archive | 4bb6675 | S | `PowerOfTwoDigits` §8 | Near-free card; a(7) > 10^21 bound archives honestly. |
| Odd non-deficient ∧ 3 ∤ n → n ≥ 5391411025 | 183c590 | M | `OddCovering` density obstruction | 3 ∣ lcm OR lcm ≥ 5.39·10⁹ for any odd covering. CAUTION: "9∣n ∨ 15∣n" proposal was FALSE at 5391411025. |
| Erdős #18 fragments unblocked | Practical.lean | S–M | `Practical.mul_prime_pow` | `practical_factorial` + `representable_of_practical` now dischargeable in `E18.lean`. |
| ALWZ improved sunflower bound (C·(r·log k)^k) | 2026-08-07 review sweep | L | `Erdos20/ErdosRado`, `Erdos20/Sunflower` | Alweiss–Lovett–Wu–Zhang (Ann. Math. 2021). Unformalized in ANY prover (AFP is classical-only; formal-conjectures issue #2284 requests even the statement). Uncontested first; P5 infra gives the definitions and the classical baseline. Spread/refined-encoding argument is the hard part. |

Status changes to existing cards:
- Switkay: drops to S (Melfi sorry now an import).
- A222603: L → M (three sorrys newly provable; connectivity open).
- A209312: `hasler_parity` near-free via `Practical.two_dvd`.
- A373686: unchanged (Melfi is context only).

Covering ranking (confirmed): C7+C3 first, C4 second.
C2 may be partially subsumed by `IsFixedDivisorSystemBase`
— verify-or-descope before dispatch.

Cleanup: `E1063.lean` fully and `E535.lean` mostly
superseded by landed files — `goof rm` candidates.


# COVERING ARC — adopted lanes

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
  base-b generalisation     37e5f2e  C1 DONE (wave-3 P13, see RESULTS):
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


## AXIOM HYGIENE — measured facts (keep until X1 lands)

The five hand-listed sweeps under `Proofs/Scratch` state their criterion
as "no `Lean.ofReduceBool`". That name is never emitted on this
toolchain, so those five detect nothing. Measured on v4.33.0-rc1: a
native_decide proof yields `<decl>._native.native_decide.ax_1_1`.

This is documented upstream behaviour, not a discovery — RFC #12216 /
PR #12217, shipped in Lean v4.29.0 (2026-03-27), moved native
computation to one axiom per computation; `ofReduceBool` was deprecated
2026-02-01. Only an allowlist-SUBSET test works. `RankOfApparition`
section 10 does it that way and `throwError`s, verified to fire by
planting both a native_decide proof and a `sorry`. It cannot close two
limits from inside: `example`s contribute no constant and escape any
such sweep, and the sweep is positional. Mathlib solves the same problem
with a syntactic linter plus periodic lean4checker, and explicitly notes
name-checking is "not airtight".


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


## AXED

  * Old lane C (more Sierpinski/Riesel instantiations, A076336/A101036):
    no firsts anywhere (ACL2 covers several), and framework reusability
    is already evidenced by THREE landed instantiations (Sierpinski,
    Riesel, Erdos1950Instance). Value per line ~zero.
  * The five hand-rolled axiom sweeps — on X1 landing, not before.
  * Old lane I (A006285 note) as a lane — demoted to micro-lane C7 plus,
    at most, a formalization link on the entry. Formally still USER
    decision 3; recommendation is drop the note, keep C7.
  * A062733 (GL(3,2) char table): "bounded" but almost certainly a
    kernel-decide grind, not proving. Stays a card in INDEX, not a lane.


## GATED / DEFERRED

  * Hough–Nielsen 2019 (was F) [XL]: every distinct covering system has
    a modulus divisible by 2 or 3. An ITP paper on its own. GATED on
    USER decision 2.
  * Hough 2015 minimum-modulus (was G) [XXL]: recorded for completeness,
    not dispatch.
  * A000670-egf-family: needs an EGF layer designed first (Mathlib
    gap) — infrastructure arc of its own, not a lane here.

  (Barker cliques A135908/09 moved to the P3 queue — its gate is
  satisfied: P5 landed and `SubgroupCountSn` exists.)


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
     `Manuscripts/Drafts/first-proofs-and-opn-reduction.md` as a fourth
     result? My read: separate — it is a formalization-infrastructure
     paper, not an OEIS-first-proof paper.
  2. Scope Hough–Nielsen yes/no.
  3. A006285 note yes/no (recommendation: no; C7 covers the substance).
  4. Whether to upstream `Basic` + `FixedDivisor` to Mathlib. Mathlib
     has ZERO covering-system content; impact is real and durable,
     review latency is long, and the API would need reshaping first.
  5. Whether `Manuscripts/` and `.tasks/` stay outside version control.
     Six drafts, 17 novelty sweeps and the triage sheet are untracked,
     including the file this plan cites as canonical for novelty
     grading.
