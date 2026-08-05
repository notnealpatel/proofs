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
