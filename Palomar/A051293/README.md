# A051293 — arbitrary-order integer-mean subset asymptotics

## Status and scope

This README recovers the Palomar candidate for A051293. It is a documentation-only recovery: human review is pending, and this workspace contains no claim of Palomar acceptance, fresh verification, or human approval. The scope is the arbitrary-order expansion for nonempty subsets of `{1,…,n}` with integer arithmetic mean, its Fubini coefficients and remainder, and the fixed order-five comparison. No global priority or novelty claim is made.

## Exact mathematical result

The literal sequence is

```lean
def integerMeanSubsetCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S : Finset ℕ =>
    S.Nonempty ∧ S.card ∣ S.sum id)).card
```

The independent statement surface defines `fubiniCoefficient 0 = 1` and

`fubiniCoefficient (n+1) = ∑ k : Fin (n+1), (n+1).choose k.val * fubiniCoefficient k.val`.

Its first six values are `1, 1, 3, 13, 75, 541`. For every `M`, the intended theorem `PalomarA051293.arbitrary_order_asymptotic` states that, eventually for positive `n`,

`integerMeanSubsetCount n − (2^(n+1)/n) * ∑ i≤M fubiniCoefficient i / n^i`

is `o(2^n / n^(M+1))`. The zero branches in the proposed surface only totalize division at `n = 0`; they do not affect an `atTop` statement. `PalomarA051293.fixed_order_five` is the normalized `M = 5` consequence, with parenthesized coefficients `1, 1, 3, 13, 75, 541` and denominator `2^(n+1)/n^6`.

## Recovered formal development and contribution

`Proofs/Enumerative/A051293/Counting.lean` defines `A051293.intMeanSubsets` and `a_comb`, proves the roots-of-unity divisor count (`b_comb_eq_b`), partitions by maximum (`a_comb_eq_sum`), identifies the combinatorial count with the analytic formula (`a_comb_eq_a`), and states `A051293.cloitre_conjecture M` for arbitrary `M`. `Proofs/Enumerative/A051293/Cloitre.lean` adds the literal `a_oeis`, proves `a_comb_eq_a_oeis`, records kernel-`decide` checks through the first ten listed terms, and derives `cloitre_explicit` and `cloitre_explicit_tendsto`.

The recovered attribution is Cloitre’s OEIS A051293 expansion (October 2002), whose coefficients are ordered Bell/Fubini numbers (A000670). The saved published account records the AlphaProof/Nexus fixed order-five formalization and identifies its final normalized limit as `target_theorem_0`; this candidate’s general-`M` route is described as a stronger formalization and a different combinatorial route, not as a priority claim. The saved account also attributes the observed per-`k` identity to OEIS observations by Papadopoulos and Wiseman, without claiming a first proof in the literature.

## Evidence recovered

The old workspace’s `Challenge.lean` matches the literal definition and transparent recurrence above. Its `Solution.lean` attempts a bridge to `Enumerative.A051293.Cloitre`, and its declarations mirror the three intended theorem names. The old journal records that checks were attempted but failed before theorem comparison: the Challenge import lacked the Mathlib Asymptotics object, the Solution could not resolve the `Enumerative` module, and both `lake build` targets were unknown. Those are historical failure records only; no checks were rerun here. The saved policy evidence requires a declaration manifest, provenance and source relationships, review status, and explicit comparator theorem/axiom configuration; those structured artifacts are intentionally not part of this recovery.

## Limitations and next obligations

The proposed Challenge still contains deliberate `sorry` placeholders, and the Solution bridge is therefore **not verified**. Dependency resolution, package/cache setup, proof elaboration, theorem-name alignment, axiom reporting, and the independent challenge/solution comparison remain outstanding. A prover must first reproduce the pinned project environment, complete the Challenge proofs, and establish that the literal independent statement is definitionally/algebraically aligned with `Counting.lean` and `Cloitre.lean`; only then should the policy-required verifier and declaration manifest be run. Source attribution, the remainder convention, and the fixed-order comparison also require human review. No References files were changed.
