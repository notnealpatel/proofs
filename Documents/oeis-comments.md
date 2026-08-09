# Proposed OEIS comments — Noe's odd Zumkeller conjecture and the OPN barrier

```
TODO
- [ ] Public repository URL for the Links entries (placeholder [TODO-URL] below).
- [ ] USER submits via oeis.org edit queue; nothing here is to be posted by an agent.
- [ ] NOT drafted here (separate work items): the ITP/CPP/CICM bundle paper
      (P9 Melfi flagship + P13 base-b covering + P5 Erdős–Rado + P14, framed as
      "formalization-driven proof simplification from the OEIS/Erdős ecosystem");
      the P5 sunflower Mathlib PR (+ ALWZ bound sequel).
```

Provenance: RESULTS.md triage item 0 (commit c1097d9; bridge theorems in
`Proofs/Enumerative/NoeZumkellerOdd.lean`, working tree, verified sorry-free
2026-08-07). The 2026-08-07 literature sweep found the observation recorded
nowhere (Rao–Peng 0912.0052, Somu et al. 2310.14149, Mahanta et al. 2008.11096,
Jokar 2207.09053, the 2008 ISU conference trail, Rosetta Code talk page).
Every mathematical assertion below is machine-checked; see the fact-check table
at the end. Comments are phrased to stand alone — no reference to the
formalization in the comment text itself; the pointer goes in the Links section.
OEIS conventions observed: ASCII math, A-number cross-references, no
self-promotion, signature appended by the submission system.

---

## A083207 (Zumkeller numbers)

**Candidate A1 (full, preferred).**

> The forward half of the conjecture in the Mar 31 2010 comment — that every
> odd Zumkeller number is a term of A174865 — is equivalent to the nonexistence
> of odd perfect numbers. Every perfect number is a Zumkeller number: {n} and
> the set of proper divisors of n are parts with equal sums. So an odd perfect
> number would be an odd Zumkeller number that is not abundant, hence not in
> A174865. Conversely, every Zumkeller number satisfies sigma(n) >= 2*n with
> sigma(n) even; if no odd perfect number exists, the inequality is strict for
> every odd Zumkeller n, which is therefore an odd abundant number of even
> abundance, i.e., a term of A174865.

**Candidate A2 (compact).**

> An odd Zumkeller number n has sigma(n) even and sigma(n) >= 2*n, and it is a
> term of A174865 if and only if it is not perfect. Since every perfect number
> is a Zumkeller number ({n} against the proper divisors), the forward half of
> the Mar 31 2010 conjecture — every odd Zumkeller number is in A174865 — holds
> if and only if there is no odd perfect number. In particular the conjecture,
> as stated, implies that no odd perfect number exists.

**Links-section entry.**

> Neal Patel, <a href="[TODO-URL]">Lean 4 formalization of the equivalence
> between the forward half of Noe's odd Zumkeller conjecture and the
> nonexistence of odd perfect numbers</a>

---

## A171641 (Non-deficient numbers with even sigma which are not Zumkeller)

**Candidate B1 (full, preferred).**

> Conjecture: this sequence contains no odd term. This is the conjecture in the
> Mar 31 2010 comment of A083207 (the odd Zumkeller numbers are exactly
> A174865) with "abundant with even abundance" weakened to "non-deficient with
> even sigma": since every Zumkeller number n satisfies sigma(n) >= 2*n with
> sigma(n) even, the weakened conjecture asserts exactly that no odd number
> belongs to this sequence. The weakened and original forms differ only at odd
> perfect numbers (an odd perfect number would be an odd Zumkeller number not
> in A174865, since it is not abundant); the original implies the weakened form
> unconditionally, and the two are equivalent if no odd perfect number exists.

**Candidate B2 (minimal, if B1 is judged too long for one comment).**

> Conjecture: this sequence contains no odd term. Equivalently, every odd
> non-deficient number with even sigma is a Zumkeller number. This is the
> repaired form of the Mar 31 2010 conjecture at A083207: it differs from the
> original only at odd perfect numbers, and unlike the original it does not
> imply the nonexistence of odd perfect numbers.

**Links-section entry.**

> Neal Patel, <a href="[TODO-URL]">Lean 4 formalization: "A171641 has no odd
> term" is the non-deficient form of Noe's odd Zumkeller conjecture</a>

---

## Fact-check table (comment assertion -> Lean theorem)

All in `Proofs/Enumerative/NoeZumkellerOdd.lean` unless noted; all sorry-free,
axioms {propext, Classical.choice, Quot.sound}.

| Assertion | Theorem |
|---|---|
| perfect => Zumkeller ({n} vs. proper divisors) | `Nat.Perfect.isZumkeller` |
| Zumkeller => 2n <= sigma(n) | `IsZumkeller.two_mul_le_sum_divisors` |
| Zumkeller => sigma(n) even | `IsZumkeller.two_dvd_sum_divisors` (Enumerative/IsZumkeller.lean) |
| forward half <=> no odd perfect number | `noeOddZumkellerForward_iff_not_exists_odd_perfect` |
| original conjecture => no odd perfect number | `NoeOddZumkeller.not_exists_odd_perfect` |
| weakened form <=> "A171641 has no odd term" | `noeOddZumkellerRepaired_iff_forall_isA171641_not_odd` |
| original => weakened, unconditionally | `NoeOddZumkeller.repaired` |
| membership conditions agree at every non-perfect n | `isA174865_iff_isOddNonDeficientEvenSigma_of_not_perfect` |
| granted no OPN, original <=> weakened | `noeOddZumkeller_iff_repaired_of_not_exists_odd_perfect` |
| first-term ground truth (945 odd, Zumkeller, in A174865) | `isZumkeller_945`, `isA174865_945` |
| first-term ground truth for A171641 (738) | `isA171641_738` |

Notes for the submission:
- The observation is an elementary corollary of recorded facts (per RESULTS
  item 0's hedge); the comments claim the equivalence, not any novelty about
  its ingredients. Both ingredients are folklore-recorded (e.g., Rao–Peng
  0912.0052 Fact 2 for sigma(n) >= 2n; Mahanta et al. 2008.11096 has all three
  ingredients on one page without drawing the conclusion).
- Do not edit Noe's existing comments; these are additions.
- A171641 B1/B2 propose a "Conjecture:" line on a sequence that currently
  records no such conjecture; the OEIS terms listed (738..4086) are all even,
  consistent with it.
