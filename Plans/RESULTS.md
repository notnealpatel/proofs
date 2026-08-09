# Campaign Results — landed-work ledger and triage summary

Coalesced 2026-08-09: this file is the ledger of landed waves (1–3 and
follow-ons) plus the novel-result triage. Wave 1's records moved here
from `PLAN.md`; the wave-3 archive-batch and follow-on landings moved
here from `NEXT_TARGETS.md` (deleted; queue now in `PLAN.md`).

## Potential novel results — USER triage required

These items may constitute first-formalizations or new formal artifacts.
Each needs a literature sweep before any claim is published.

0. **Noe's odd Zumkeller ↔ no OPN (archive batch, c1097d9)** — proved
   that the forward direction of Noe's conjecture (odd Zumkeller ⊆
   A174865) is equivalent to the nonexistence of odd perfect numbers.
   An odd perfect number is Zumkeller but not abundant, so it escapes
   A174865. **Literature sweep completed 2026-08-07, observation NOT
   FOUND recorded anywhere.** Sources: Rao–Peng 0912.0052 (Fact 2 is
   non-strict σ(n) ≥ 2n, credited to the unpublished Clark et al.
   2008 talk — talk itself unlocatable, absent even from Leach's CV),
   Somu et al. 2310.14149, Mahanta et al. 2008.11096 (has all three
   ingredients on one page, never draws the conclusion), Jokar
   2207.09053 (odd *near*-perfect only), OEIS A083207/A174865,
   ISU Mathematical Abundance Conference 2008 (no surviving program),
   Rosetta Code talk page (informal near-miss, 2021). Verdict: keep —
   first formal artifact; the observation is an elementary but
   apparently unrecorded corollary of recorded facts. Bridge theorem
   LANDED 49f30bd (2026-08-09): pointwise bridge at non-perfect n,
   unconditional `NoeOddZumkeller.repaired`, and original ↔ repaired
   granted no odd perfect number; instantiated at 945
   (`not_perfect_945`) — replaces the file's prose claim.

1. **Melfi's theorem (P9, 2e5b1ab)** — sorry-free proof that every even
   n > 0 is practical + practical. **Dedicated sweep completed
   2026-08-07 (27 auditable queries): no prior formalization of
   practical numbers or Melfi's theorem in Mathlib, Isabelle AFP,
   Coq/Rocq, Mizar, GitHub, or Lean Zulip — first-ITP-formalization
   claim confirmed.** The proof route (two-modulus covering by 2^k and
   2·3^j, gcd 2, both summands kept practical via the σ(m)+1
   multiplier lemma) is likewise unrecorded: no source reproves
   Melfi's theorem this way. Claimed as an apparently new composition,
   with the explicit caveat that its core trick — multiplier lemma
   over a single 2^k modulus family — is standard current practice in
   Somu–Li–Kukla (INTEGERS 2023, square + practical) and Somu–Tran
   (JIS 2024, practical + triangular); the new step is the two-family
   covering of all even numbers, replacing Melfi's twin-practical
   interval argument entirely.

2. **gcd-sunflower bound (P12, 0238c07)** — the Ω-layer bound
   (r−1)^k · k! on equal-pairwise-gcd-free sets of k-almost primes,
   sharp at k = 1. The encoding (prime-power divisors as sunflower
   petals) is classical, but the combination with a machine-checked
   Erdős–Rado bound is new as a formal artifact. Bloom's comment on
   #535 acknowledges the connection exists; no prior formalization found.
   **Sweep 2026-08-07 confirms P5's first-in-Lean claim**: zero
   sunflower content in Mathlib ("sunflower" absent from every file),
   LeanCamCombi explicitly checked and absent, formal-conjectures has
   a statement-request issue only, no Lean repos or Zulip threads.
   AFP entry confirmed: Thiemann, Feb 2021, classical bound only.
   Nobody in any prover has the ALWZ improved bound (→ PLAN.md,
   new targets from wave 3).

3. **base-b covering criterion (P13, 37e5f2e)** — `IsFixedDivisorSystemBase`
   generalises the fixed-divisor criterion to arbitrary bases with three
   concrete witnesses (base-14 Sierpiński, base-6 Riesel, base-b≡34 mod 35
   Riesel). **Confirmed novel by dedicated sweep 2026-08-07.**
   Cowles–Gamboa (ACL2 2011, arXiv:1110.4671) verified base-2 only by
   reading the paper — its lone transport observation moves across k
   (k + 2iP with the same cover), never across bases. No
   Sierpiński/Riesel/covering-congruence formalization exists in
   Mathlib, AFP, Coq/Rocq, Mizar, or Metamath. The `of_modEq_base`
   transport is stated as a theorem nowhere in the checked math
   literature either — folklore-implicit in practitioner tables
   (Dozenal Wiki, MersenneForum); nearest neighbor is
   Filaseta–Groth–Luckner 2023 (arXiv:2305.09219), a stronger
   simultaneous-multi-base result via different cyclotomic machinery.
   Definitions verified against live A123159 (name matches verbatim,
   a(14)=4 is the witness proved) and Wikipedia's Riesel-base-b form.
   Residual: Brunner et al. RIMS kokyuroku 1639 unobtainable in sweep.

4. **Selfridge defect under k ≤ n (P11, 8efac26)** — the Monier 1985 proof
   never needs 2k ≤ n. This strengthening is bookkeeping, NOT a novel
   mathematical result — do not overclaim.

5. **‖3^b‖ = 3b for all b (P14, d657720)** — sorry-free proof via the cube
   bound. This is Iraids et al. Theorem `cbounds2`; the mathematics is
   textbook. **Sweep 2026-08-07: no formalization of integer
   complexity (A005245 / Mahler–Popken) or any theorem about it found
   in Mathlib, AFP, Coq/Rocq, Mizar, Metamath, or HOL Light; the
   Latvia group / Altman / Zelinsky literature is computation only.
   "Likely first" upgraded to first-formalization claim.** Attribution
   audit: `cbounds2` is correctly Iraids et al. (arXiv:1203.6462);
   the earlier vacuity-cop Iraids→Altman fix concerned the separate
   window theorems and does not affect this item.

6. **A092482 closed form (P7, f105bf4)** — promoted from Wave 2 after
   adversarial verification 2026-08-07. Settles a genuinely open OEIS
   conjecture: the live record still says "conjectured and checked up
   to n=512" and companion A093682 still says none of the family's
   formulas are proved; no prior proof in Fried's OEIS-conjecture
   papers (2410.07237, 2607.24832) or elsewhere. Verified: statement
   matches the unambiguous Mathematica rendering against all 57 terms;
   both documented OEIS typos computationally confirmed; greedy
   definition independent of the closed form (no circularity), seed
   derived not assumed; sorry-free on standard axioms. First proof of
   the closed form; mechanism is the standard A003278 base-2/base-3
   greedy argument applied blockwise — no claim of deep novelty.

>>> "For n > 2, a(n+2) = 1 + 2^floor(log_2(n)) + Sum_{k=1..n} (3^A007814(n) + 1)/2 = 1 + A053644(n) + A005836(n)"

---

# Post-wave-3 landings — 2026-08-07/09

- **Erdős #406 sieve bound + method barrier (4455bf3).**
  PowerOfTwoDigitsCount: exact survivor count 2^j for the depth-(j+1)
  congruence sieve and the counting bound N(x) ≤ 2·x^(log₃ 2) — the
  λ = 1 case of Lagarias [La09] Theorem 1.4 (Narkiewicz's sharper
  1.62 constant pinned, not formalised). PowerOfTwoDigitsBarrier:
  the method-barrier package.
- **Noe original↔repaired bridge (49f30bd).** See triage item 0.

---

# Wave 3 Results — 2026-08-05

## P9: Melfi 1996 — even = practical + practical (2e5b1ab)
**POTENTIAL NOVEL.** Sorry-free. 571 lines. Proof uses two-modulus
covering (2^k, 2·3^j), NOT Melfi's twin-practical sequence — the
L risk from the brief was avoided entirely. Discharges `melfi` sorry
in three sketch files. Source: 1995 survey (1996 paper paywalled).
StewartCriterion.lean not imported (direct from practical_iff).

## P10: Kummer carry layer (626822b)
Infra. Sorry-free. Defines `carry` recursion, bridges to Mathlib's
`padicValNat_choose'`. Kummer proper was already in Mathlib — file
builds the missing carry function. Brief overstated downstream: unlocks
#376 + #406 only (not five problems). `Odd p` dropped from
`prime_not_dvd_centralBinom_iff_digits` (sound at p = 2).

## P11: Erdős #1063 Selfridge defect (8efac26)
Sorry-free. Proved under k ≤ n (weaker hypothesis than source's 2k ≤ n;
source form also provided). CORRECTION: brief gloss described #377 not
#1063. Certifies n₂ = 4, n₃ = 6, n₄ = 9, n₅ = 12 (A389360) + Monier's
n_k ≤ k! bound. Strengthening is bookkeeping — not novel.

## P12: Erdős #535 gcd-sunflower bound (0238c07)
**POTENTIAL NOVEL.** Sorry-free. Ω-layer bound (r−1)^k · k! via
prime-power encoding of Erdős–Rado. Sharp at k = 1 (extremal families
= r−1 distinct primes). N-form `fgcd_le_erdos_rado` proved but
explicitly weaker than trivial for all N ≥ 2 — brief's premise was
false. Nontrivial N-form needs Rankin/smooth-rough (not in Mathlib).
The encoding is a one-problem tool — no other Erdős problems reduce
through it (elaborator swept #536, #539, #164, #857, #892, #858).

## P13: covering arc C1 base-b generalisation (37e5f2e)
**POTENTIAL NOVEL.** Sorry-free. 51 new declarations, zero existing
broken. `IsFixedDivisorSystemBase` + `IsSierpinskiNumberBase` +
`IsRieselNumberBase` with three concrete witnesses. `of_modEq_base`
transports one certificate across base congruence classes. Key finding:
n ≥ 1 convention is forced (4·14⁰+1 = 5 is prime). Source-fidelity:
A146563 comment false at n = 0; Wikipedia Riesel sign typo; base-b
certs are covers but NOT covering systems (repeated moduli).

## P14: ‖2^n‖ = 2n archive — Guy F26 (d657720)
One intended sorry (the open hypothesis). Cube bound analytically
certifies a ≤ 9 (brief's decide window was unreachable). BONUS:
‖3^b‖ = 3b proved for all b ≥ 1 (sorry-free). Four citation numbering
errors in the arXiv papers fixed by vacuity-cop (Hyp 1.4→1,
Thm 1.2→1, Thm 1.1→1.7, Iraids→Altman + Thm 1.2→1.6).

## Wave 3 archive batch (one file/commit each)

- A146968 Brocard — 7a1d51f
- A174865 Noe Zumkeller — c1097d9 (forward ↔ no OPN; triage item 0)
- Erdős #1140 n−2x² — da07f72
- A000166 Sun derangements — 6de4495 (coprimality proved ∀n)
- A244743 complexity defect — b43f80d (brief def was wrong)
- Erdős #406 2^n base 3 — 4bb6675 (no sorry, Kummer load-bearing)
- Erdős #7 odd covering — 183c590 (945 lcm bound proved)

## Wave 3 follow-on (prover lanes) — all landed

- Three-smooth: ‖2^a · 3^b‖ = 2a + 3b — 398c7d6
- n_k table: A389360 extended to k = 6–10 — 7f3a26b
- Defect carry bound (P10 × P11 crossover) — 5af455e

## Brief corrections logged

| Lane | Correction |
|------|-----------|
| P10 | Kummer already in Mathlib; downstream is 2 problems not 5 |
| P11 | Brief gloss was #377 not #1063 |
| P12 | N-form weaker than trivial (brief said "still nontrivial") |
| P13 | Order bridge stays ℕ not ℤ; n ≥ 1 forced |
| P14 | Decide window unreachable; 4 citation numbers wrong in arXiv papers |

---

# Wave 2 Results — 2026-08-05

## P5: Erdős–Rado sunflower lemma (decda50)
First-in-Lean. Sorry-free. AFP has it in Isabelle (2021); Mathlib has nothing.
`erdos_rado_sunflower_same_card` — (r−1)^k · k! threshold on Fin n.
Machine-checked that the ≤k variant is false under the nonempty-petal convention.

## P6: commuting triples of permutations (75c4192)
First formalization of Britnell 2012. Sorry-free layer only — full identity
needs wreath-product centralizers + Euler transform (both absent from Mathlib).
A072169(0..4) and A061256(0..4) certified by kernel decide.

## P7: A092482 closed form — first proof (f105bf4)
Settles an open OEIS conjecture ("conjectured and checked up to n=512").
The brief's premise (A093682 family member) was false; corrected.
Two OEIS formula typos documented and worked around.

## P8.1: Knuth–Stolarsky conjecture archive (3010ba5)
One sorry. Proved: v(n) ≤ 2 family, kernel exhaustion n ≤ 16,
subtraction-free iff, satisfiability at n = 15.
Caught and documented a web-search false alarm (Scholz–Brauer disproof ≠ this).

## P8.2: Fubini primes ≡ 1 mod 4 (ceb9085)
Brief budgeted a sorry; proved it outright via mod-3 + mod-4 congruences.
Certifies 13, 541, 47293 as Fubini primes.

## P8.3: Sun partition perfect-power conjecture (07bf2bd)
One sorry. Defines IsPerfectPower locally (Mathlib gap).
Material limitation: Fintype.card (Nat.Partition n) does not kernel-reduce for n ≥ 2.

## P8.4: primes not of the form x³ − y² (ace3c48)
One sorry on infinitude. Proved 3 and 5 are members via Mordell-equation
Jacobi-symbol descents (nonemptiness guard). 39 non-members certified.
Brief's "b-file" claim was nonexistent; caught and documented.

## P8.5: ideal Waring g(n) = 2^n + floor((3/2)^n) − 2 (738640f)
Euler lower bound proved sorry-free. One sorry on the upper bound.
g(1) = 1 and g(2) = 4 proved outright. Tightness checked for n ≤ 40.

## P8.6: squarefree central binomial coefficients (6934073)
One sorry narrowed from ~5·10^7 cases to 331 odd values with digit sum ≤ 2.
Even classification proved via NotSquarefree.lean. All 13 OEIS terms certified.
Ten sub-72 odd values documented as uncovered.

## P8.7: sunflower conjecture archive (750d918)
One sorry. Found and documented the convention gap (OEIS sunflower vs
IsSunflowerWith nonempty petals). Both thresholds defined, relationship
proved sorry-free. Consumes P5's Erdős–Rado for finiteness.

## P8.8: Hegarty AP-avoiding permutation (f8e1f81)
One sorry on lim a(n)/n = 1. Proved sorry-free: permutation property (Thm 3.1),
upper bound a(n) < 3n/2, AP-avoidance. Fetched and grounded against the paper.

## P8.9: Pyber subgroup count of S_n (2dce7f7)
One sorry. Discovered the conjecture was proved in 2025 (Roney-Dougal–Tracey).
Sorry-free reduction: Pyber follows from their Theorem 1.
OEIS comment is stale; documented.

## P8.10: primorial-base exp + prime-shift + Karttunen conjectures (fa6d210)
Sorry-free throughout. A276086 and A003961 defined from scratch.
Sufficient condition for A351458 proved. Second term of A323653 (459818240) certified.
Conjecture 1(c) → forward half of Conjecture 3 reduction proved.

## P8.11: congruent numbers and BSD subset claim (d5dd51f)
One sorry on the BSD-conditional subset. Congruent-number ↔ nontrivial-point
equivalence proved sorry-free via Mathlib WeierstrassCurve.
User ruling followed: no rank functional, no Mordell–Weil.

## Mining: OEIS conjecture candidates (60533e8)
25 candidates in Formalize/CONJECTURE_CANDIDATES.md with sorry'd Lean sketches.
5 corrections applied from adversarial review (A351243 wrong sequence, A373686
threshold, A309370 off-by-one, A007850 direction, A080210 largest not least).

## Mining: Erdős problem candidates (60533e8)
56 candidates in Formalize/ERDOS_CANDIDATES.md (24 solved + 32 unsolved).
8 corrections applied. Top attack targets: E1063 (Selfridge defect),
E376 (Kummer digits), E535 (gcd-sunflower via new Erdős–Rado).

## Mining: methodology gaps (f4606e2)
MINING_GAPS.md — 63 solved Erdős problems excluded by formalized=yes filter
(upstream files are sorry stubs). Algebraic-complexity arc has no database.
xref-chain depth misses: multiperfect cluster, A000009 Sun conjectures.
Classical misses: ‖2^n‖ = 2n, Melfi 1996, Higman PORC.

## Planning: next targets (f4606e2)
NEXT_TARGETS.md — 104 candidates coalesced: 44 formalize, 50 proof attempt,
5 unknown. Melfi 1996 is the P1 flagship. Sylvester–Schur unlocks a family.
Natural density is the largest Mathlib gap blocking ~5 statements.
(2026-08-09: NEXT_TARGETS.md itself has since been folded into PLAN.md.)

## Housekeeping: notes.txt removed
Stale scratch notes; every item was resolved or superseded by landed work.
Moved to ~/.goof/trash/ (recoverable). Incidental: stale Proofs/.lake
directory shadows leandoc discovery.

---

# Wave 1 Results — dispatched 2026-08-05

## P1 (prover): SliceRank pullback-monotonicity + CLP bound
16e7e2b (Task A), edc443d (Task B). `sliceRank_comp_le` (arbitrary
maps, not just injective) in SliceRank.lean § 7. CLP sorry discharged
via Tao's symmetric route in CapsetSliceRank.lean § 5;
`ellenberg_gijswijt` now clean. `peebles_conjecture` untouched
(intended sorry).

## P2 (postdoc): Neder gap ≤ 12
9859682. `nth_isZumkeller_succ_le_add_twelve` +
`exists_isZumkeller_mem_Ico` (settles Noe 2010). Reused in-tree 3·2^k
and coprime-closure proofs. CORRECTION: the brief's Noe framing was
wrong — Noe's conjecture is WEAKER than Neder's, not stronger.

## P3 (postdoc): AdditionChain permissive ≡ ascending
24bb900. `l_eq_lAsc`. Brief's sort+dedup sketch was wrong (chains can
overshoot n); fixed via filter-first `ascNormalize`. Ground checks
n ≤ 8, n = 15.

## P4 (postdoc): ErdosLovasz g(3) = 6
3a4110c. `tripathi_six_le_erdosLovaszNum_three` discharged via
double-counting (not Fin 15 search). `tripathi_erdosLovaszNum_three`
now sorry-free. Attribution corrected: priority is FOT96, not Tr14.
