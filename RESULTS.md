# Campaign Results — triage summary

## Potential novel results — USER triage required

These items may constitute first-formalizations or new formal artifacts.
Each needs a literature sweep before any claim is published.

1. **Melfi's theorem (P9, 2e5b1ab)** — sorry-free proof that every even
   n > 0 is practical + practical. No prior Lean/Isabelle/Coq/Mizar
   formalization found in any sweep. The proof route (two-modulus covering
   by 2^k and 2·3^j) is simpler than Melfi's original twin-practical
   argument — may be folklore, but no citation found. Do NOT claim the
   route as new without a dedicated search.

2. **gcd-sunflower bound (P12, 0238c07)** — the Ω-layer bound
   (r−1)^k · k! on equal-pairwise-gcd-free sets of k-almost primes,
   sharp at k = 1. The encoding (prime-power divisors as sunflower
   petals) is classical, but the combination with a machine-checked
   Erdős–Rado bound is new as a formal artifact. Bloom's comment on
   #535 acknowledges the connection exists; no prior formalization found.

3. **base-b covering criterion (P13, 37e5f2e)** — `IsFixedDivisorSystemBase`
   generalises the fixed-divisor criterion to arbitrary bases with three
   concrete witnesses (base-14 Sierpiński, base-6 Riesel, base-b≡34 mod 35
   Riesel). ACL2 has base-2 Sierpiński/Riesel (Cowles–Gamboa 2011); no
   prior base-b generalisation found in any ITP. The `of_modEq_base`
   transport (one certificate → infinitely many bases) has no analogue
   in the ACL2 work.

4. **Selfridge defect under k ≤ n (P11, 8efac26)** — the Monier 1985 proof
   never needs 2k ≤ n. This strengthening is bookkeeping, NOT a novel
   mathematical result — do not overclaim.

5. **‖3^b‖ = 3b for all b (P14, d657720)** — sorry-free proof via the cube
   bound. This is Iraids et al. Theorem `cbounds2`; likely first
   formalization but the mathematics is textbook.

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

## Brief corrections logged

| Lane | Correction |
|------|-----------|
| P10 | Kummer already in Mathlib; downstream is 2 problems not 5 |
| P11 | Brief gloss was #377 not #1063 |
| P12 | N-form weaker than trivial (brief said "still nontrivial") |
| P13 | Order bridge stays ℕ not ℤ; n ≥ 1 forced |
| P14 | Decide window unreachable; 4 citation numbers wrong in arXiv papers |

## In-flight (prover lanes, wave 3 follow-on)

- Three-smooth: ‖2^a · 3^b‖ = 2a + 3b — prover running
- n_k table: extend A389360 to k = 6–10 — prover running
- Defect carry bound: P10 × P11 crossover — prover running

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

## Housekeeping: notes.txt removed
Stale scratch notes; every item was resolved or superseded by landed work.
Moved to ~/.goof/trash/ (recoverable). Incidental: stale Proofs/.lake
directory shadows leandoc discovery.
