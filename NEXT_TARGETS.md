# Next Proving Targets — Coalesced Action Plan 2026-08-05

Wave 2 is committed: P5 (Erdős–Rado, `decda50`), P6
(A061256 Britnell, `75c4192`), P7 (A092482 closed form,
`f105bf4`), and ten of the eleven P8 archive files
(A003313, A000670-muljadi, A000041-sun, A161682, A002804,
A046098, A332077, A094870, A005432, A273929). A323653 is
NOT in the git log — it stays queued below. The covering
arc C1–C7 was never dispatched. None of the committed
targets are re-suggested here.

This file coalesces four sources into one prioritized
queue: `Formalize/CONJECTURE_CANDIDATES.md` (25 OEIS
sketches in `Proofs/Scratch/Candidates/`),
`Formalize/ERDOS_CANDIDATES.md` (56 sketches in
`Proofs/Scratch/ErdosCandidates/`, issue #5), the mining
meta-sweep (`MINING_GAPS.md`, issue #6), and the pending
remainder of `PLAN.md`. The MINING_GAPS candidates were
flagged single-pass; they received a fresh paired
advocate/skeptic audit this session with live
`goof erdos fetch` / `goof oeis show` / web runs. Verdicts
below cite that audit; the two sweep docs' own paired
audits are trusted as-is.

One dedup: Erdős #242 and A192787 are the same problem
(Erdős–Straus); merged into one card. Melfi's theorem
appears as a sorry inside three sketches
(`A005153Switkay`, `A222603PracticalTree`,
`A373686SomuTran`) but is one lane.

## Summary statistics

- Total unique candidates: 104
  (25 OEIS + 56 Erdős + 11 meta-sweep + 13 PLAN − 1 dedup)
- Formalize (sorry'd): 44
- Proof attempt: 50
- Unknown/unsorted: 5 (+4 process investigations)
- Dropped after audit: 5 (see cross-cutting notes)

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
| `‖2^n‖ = 2n` (UPINT F26) | gaps #6 | S | `complexity`, `complexityRec` | One-line statement; the central open question of the NumberComplexity arc. `decide` window is n ≤ ~10–12 only (`complexityRec 11` already needs maxRecDepth 8192); literature range is n ≤ 39, NOT 41 — Iraids et al. computed to 10^12 and 2^40 > 10^12. |
| A146968 Brocard | OEIS T1 | S | Mathlib `Nat.factorial`, `IsSquare` | Open since 1876; sketch has 4 sorrys, window check cheap. |
| A174865 Noe Zumkeller iff | OEIS T1 | S | `IsZumkeller`, `ZumkellerSigmaHalf` | Strongest adjacency in the OEIS batch; easy direction (`noe_easy_direction'`) is provable now, hard direction is the sorry. |
| A005153 Switkay | OEIS T1 | S | `Nat.Practical`, `StewartCriterion` | Sequence AFTER the Melfi lane (P1): the card's `melfi` sorry becomes an import. Parity reduction provable. |
| A000166 Sun derangements | OEIS T1 | S | Mathlib `numDerangements`; shares `IsPerfectPower` with landed A000041 card | Coprimality warm-up provable; main conjecture Diophantine-hard. |
| A244743 complexity defect | OEIS T1 | S | `complexity` | Well-definedness IS the conjecture; `neg_one_le_defect` provable from `complexity_add_le`. |
| Erdős #242 / A192787 Erdős–Straus (merged) | both sweeps | S | none new; cleared-denominator `Nat` form | Archive-primary. Fragments: `erdosStraus_of_prime` + Mordell residue classes (effort M) are P2-grade work the card should carry. |
| Erdős #1140 n−2x² | Erdős B | S | `ErdosMinus2k` shape | Eight `decide` certificates + `native_decide` window; class-number finiteness archived. |
| Erdős #405 (p−1)!+a^(p−1)=p^k | Erdős B | S | none | Pin the odd-p solution set from Yu–Liu before stating (DB examples use p=2). |
| Erdős #7 odd covering | Erdős UB | S | `Erdos/Covering/Basic` | High audit value given the 2026 rejected-proof churn; decidable restatement vs upstream `StrictCoveringSystem ℤ` must be flagged explicitly. |
| Erdős #406 2^n base 3 | Erdős UB | S | `Nat.digits` | Three witnesses + verified windows; shares digit language with the #376 Kummer layer (P2). |
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
| A323653 | PLAN P8 | L | needs A276086 primorial-base + A003961 prime-shift defs | The one unlanded P8 item; def layer is heavy by prior ruling — keep last. |
| A222603 practical tree | OEIS T3 | L | `Nat.Practical`, `SimpleGraph`; Melfi (P1) prerequisite | Successor well-definedness needs Melfi; acyclicity provable, connectivity is the conjecture. |
| A005153 Sun root-decreasing | OEIS T3 | L | `Nat.Practical`, asymptotics toolbox | Limit half known (Weingartner) but needs practical-counting asymptotics; monotonicity open. |
| A000041 Sun antichain | OEIS T3 | L | partition machinery | Sketch's own review: weakest candidate; archive only, never schedule proof work. |
| A265262 Erdős–Turán | OEIS T3 | L | fresh `profile`, `IsBasis2` | Archive-primary; the König tree-equivalence is the valuable P3 fragment. |
| Erdős #577 disjoint C4s | Erdős D | L | none | ~45-page proof; statement archive at most. |

## 2. Proof attempt targets

`prover` is scarce (largest stated-to-route gap only);
everything else is `postdoc`. Efforts are the sketchers'
calls, corrected by audit where noted.

### Tier P1 — Highest confidence (elementary proof, existing infra)

| Target | Source | Agent | Attack surface | Reuses |
|--------|--------|-------|----------------|--------|
| Melfi 1996: even = practical + practical | gaps #6 | postdoc, M (L risk) | 6-page constructive proof: Stewart-criterion iteration + interval covering via a bounded-ratio practical sequence. Audit: ~60% of prerequisites landed; the twin-practical ratio argument is the L risk. Discharges sorrys in three sketch files. | `StewartCriterion` (697 lines), `Practical.lean` |
| C1 base-b FixedDivisor | PLAN | postdoc, S | Mechanical `2` → `b` port; order bridge `(b:ℤ)^d = 1 [ZMOD p]`; decidability survives. Highest value per line in the covering arc. | `FixedDivisor.lean` |
| C2 abstract sequence layer | PLAN | postdoc, S | ~15 lines, piggyback on C1; statement reuse only. | `FixedDivisor`, `RankOfApparition` |
| C3 Brier numbers | PLAN | postdoc, S | Two independent `IsFixedDivisorSystem` instances; both certificates re-verified 2026-08-05; loads far inside the measured ceiling. First Lean + record-k framing; cite Cowles–Gamboa (ACL2). | `FixedDivisor`, `Sierpinski`, `Riesel` |
| C4 Mirsky–Newman | PLAN | postdoc, M | Root-of-unity argument on committed `IsCoveringSystem`; novelty sweep clean; MUST resolve the 274.lean "Jostamon" pointer before claiming first-formalization. | `Covering/Basic` |
| C7 drop `1 ≤ k` | PLAN | postdoc, S | k = 0 case already paid for; strengthens the flagship to A006285's convention. | `NotTwoPowerPlusPrime` |
| Erdős #1213 Hegyvári | Erdős A | postdoc, S | Pigeonhole on interval-sum residues; zero new defs. Best payoff-per-effort in the Erdős sweep. | `Finset.sum` vocabulary |
| Erdős #384 Ecklund | Erdős A | postdoc, S | Corrected statement already in sketch (n ≥ 2k, p ≤ n/2, (7,3) exception); elementary via Bertrand. | Kummer machinery in `Erdos175` |
| Erdős #673 divisor ratios | Erdős C | postdoc, S | Tao's trivial route: τ(n)/4 ≤ G(n) ≤ τ(n) pointwise; density half stays archived. | `Nat.divisors` |
| Erdős #1062 no a∣b, a∣c | Erdős UA | postdoc, S | Interval [m+1, 3m+2] gives f(n) ≥ ⌈2n/3⌉; small exact values decidable. | Finset divisibility |
| Erdős #1063 near-uniform divisibility | Erdős UA | postdoc, S–M | Erdős–Selfridge defect lemma is self-contained; n_2..n_5 `decide`-scale; lcm upper bound sits on `Erdos440`. | `Erdos440/LcmCount` |
| Erdős #1160 m = 2, 3 cases | Erdős UB | postdoc, S/M | Skim verdict: `erdos_1160_m2` provable NOW from landed gnu lemmas; m = 3 provable-with-work. Headline stays archived (gnu(64) = 267 is out of certified range). | `GroupCount/Gnu` |

### Tier P2 — Medium confidence

| Target | Source | Agent | Attack surface | Reuses |
|--------|--------|-------|----------------|--------|
| A002093 highly abundant → practical | gaps #6 | postdoc, M | Audit UPGRADE from archive: Eppstein 2015 gives an essentially complete argument (smallest-missing-prime P < p² bound + Stewart criterion + Alaoglu–Erdős divisibility-by-4 for large n). GATE: verify the blog argument end-to-end first; it settles a live OEIS conjecture, so the bar is high. | `StewartCriterion`, `Practical`, Mathlib `sigma` |
| C5 Erdős #278 Rogers minimum | PLAN | postdoc, M | Inclusion–exclusion over lcms (Rogers via Halberstam–Roth; Tao 2026 writeup). Maximum question stays archived. | `Covering/Basic` |
| C6 Wilf A083216 | PLAN | postdoc, M | Alpha-layer API confirmed ready; GATE on the scaled `decide` probe (155520 load is AT the ceiling); bridge must live in `ZMod p`; re-derive the 18-triple certificate independently. | `RankOfApparition`, `IsFibonacciLike` |
| C5 Erdős #1188 fragment | PLAN | postdoc, S | Woett's elementary F(x) ≥ ⌊log₁₂ x⌋; archive the site's (Bloom-reinterpreted) statement and say which form it is. | `Covering/Basic` |
| C5 Erdős #1189 fragment | PLAN | postdoc, S | Sun 2007 irreducible-covering certificate (divisors of 2^(p−1)·p) checked by the existing layer; archive the rest. | `Covering/Basic` |
| Erdős #1058 Luca n!+1 | Erdős A | postdoc, M | Five `decide` certificates + 4-page elementary tail (factorial divisibility + Bertrand). Full closure of an Erdős problem plausible. | certificate-then-tail pattern from `ErdosMinus2k` |
| Erdős #482 Graham–Pollak | Erdős A | postdoc, M | Computable recurrence, short induction; floor-to-binary bridge is the fiddly part. | Mathlib `Real.sqrt`, `Nat.floor` |
| Erdős #916 Thomassen | Erdős A | postdoc, M | ~5-page direct argument; primitives exist; Walk-API friction is the risk. | `SimpleGraph` experience from Erdos715 |
| Erdős #58 Gyárfás headline | Erdős A | postdoc, M | Prove χ ≤ 2k+2, sorry the equality case (L). | Mathlib `chromaticNumber` |
| Erdős #77 Ramsey layer | Erdős C | postdoc, M | R(k) def (~50 lines) + classical bounds (probabilistic lower, pigeonhole upper) + R(3) = 6; unlocks #781 and #112. | new def, high downstream reuse |
| Erdős #376 Kummer layer | Erdős UA | postdoc, M | Kummer's theorem (coprimality ↔ digit conditions) as finite carry-counting over `Nat.digits`; the deliverable is the layer, not the $1000 headline. Unlocks #175 remainder, #699, #1093–#1095, #406. | `Nat.digits`, `centralBinom` |
| Erdős #699 binomial gcd | Erdős UA | postdoc, M | Finiteness-per-(i,j) + balanced n = 2j case via the product identity; window provable. | BINOM arithmetic; Sylvester–Schur (P3) strengthens it later |
| Erdős #856 lcm sunflowers | Erdős UA | postdoc, M | Er70 upper bound is a short prime-counting inequality; natural second client of Naslund–Sawin. | `Erdos857/NaslundSawin`, Mathlib Chebyshev |
| Erdős #535 gcd sunflowers | Erdős UA | postdoc, M | Prime-power encoding turns equal-pairwise-gcd r-sets into r-sunflowers; pushing landed Erdős–Rado through gives a new formal bound (audit-promoted). | `Erdos20/ErdosRado` |
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
| Barker cliques A135908/09 | PLAN gated | prover, S/L | PLAN's gate ("after P5, S_n machinery felt out") is now satisfied: P5 landed and `SubgroupCountSn` exists. Max-abelian-subgroup-of-S_n theorem is where it may stall. | `GroupCount`, `SubgroupCountSn` |
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
| A000670-egf-family | PLAN gated | Needs an EGF layer Mathlib lacks — an infrastructure arc, not a lane | Scope the EGF design separately; do not dispatch. |
| Hough–Nielsen (2 or 3 divides some modulus) | PLAN gated | XL; an ITP paper on its own | USER decision 2, unchanged. |
| Excluded-63 re-triage | gaps #6 §1 | Only 8 of 63 upstream files were classified (all stubs); 55 solved problems with unclaimed proofs remain unassessed — #387/#851/#937/#1064 audited this session, all deep or blocked | Dispatch the Tier-A triage over the remaining ~55; highest expected yield per hour of any process item. |
| Algebraic-complexity lane | gaps #6 §2 | No database indexes the repo's deepest arc; A075099 killed on audit (contested def) | Literature-sourced mining: Bürgisser–Clausen–Shokrollahi problem list + Landsberg open problems. |
| GreensOpenProblems/ + Kourovka/ | gaps #6 §5 | 53-file Green list and Kourovka group-theory tree unmined | Next mining sweep stage; also align defs with `FormalConjecturesForMathlib`. |
| A093682 per-row forms | PLAN P7 | Commit `f105bf4` names only A092482; whether the A093682 rows (A004793, A033157, A093678–81) landed is unverified | Check the committed file; unlanded rows are P2-grade follow-ons on `StanleyDigits`. |

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

Sequencing that matters: (1) Melfi before the Switkay,
A222603, and A373686 cards — it is a sorry inside all
three. (2) The #376 Kummer layer before #699/#1093/#1094/
#1095/#406 fragments. (3) A309370 before A390813 (shared
`IsSidon`; promote it out of `Scratch`). (4) C1 before C2;
C6 probe before C6 and before #276. (5) The hypergraph def
layer (#834 first, smallest) before #836/#901/#1020/#1178.
(6) Sylvester–Schur (#683) is the one target where a
prover lane changes the reachable set for a whole family.

Statement-fidelity gates carried over from the sketches:
#405 odd-p solution set, #781 first-failing-k probe, #81
Woett dedup, #836 second-question status, #548 edge-count
form, A141386 literature check, and every 2025–26
AI-assisted site comment cited in `ERDOS_CANDIDATES.md` —
re-fetch before building on any of them. `oeis show` /
`erdos fetch` ground truth before any Lean statement,
per PROTOCOL.

Chores X1 (axiom-audit adoption) and X2 (INDEX refresh)
from `PLAN.md` remain open and are not proving targets;
X2 should additionally record wave 2's ten P8 landings and
the A323653 remainder.
