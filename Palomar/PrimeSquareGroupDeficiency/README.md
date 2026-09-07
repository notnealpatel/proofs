# Prime-square group deficiency

## Current status

**Mechanically checked candidate; USER review pending.** Challenge and Solution
were checked separately with the pinned Lean toolchain. The Solution, its
counting bridge, and the selected source theorem have only the three permitted
standard axioms. Comparator and the independent verifier were **NOT RUN** because
the required executables are absent. This is not a submission, acceptance,
human-review, novelty, or priority claim.

This package selects only the elementary, known prime-square family. It does
**not** resolve uniqueness of group-perfect numbers, a density conjecture, or
a general classification of finite groups.

## Exact mathematical statement and counting model

The selected fully qualified declaration, identical in both files, is

```lean
Palomar.PrimeSquareGroupDeficiency.groupDeficient_prime_sq :
  ∀ {p : ℕ}, Nat.Prime p → groupCount (p ^ 2) < p ^ 2
```

Here `groupCount n` is not a free function, a supplied answer, or a count of
labeled multiplication tables. It is

```lean
Nat.card (Quotient (groupIsoSetoid n))
```

where the underlying type is **all Mathlib `Group (Fin n)` structures** and the
relation between structures `G` and `H` is

```lean
∃ e : Fin n ≃ Fin n,
  ∀ a b : Fin n, e (G.mul a b) = H.mul (e a) (e b)
```

Thus structures are identified exactly by group isomorphism. The independent
lemma `isomorphic_iff_nonempty_mulEquiv` proves agreement with Mathlib's
`MulEquiv`, explicitly using `G`'s and `H`'s multiplications, not the ambient
arithmetic multiplication on `Fin n`. Every finite group of order `n` admits a
numbering by `Fin n`, so this quotient counts group-isomorphism classes of that
order, not only a restricted family of groups.

Finiteness is proved: group structures inject into their finite multiplication
tables by `Group.ext`, and the quotient is finite. Consequently `Nat.card` is
never using its infinite-type default. At `n = 0`, the type is genuinely empty
because there can be no identity element; `groupCount_zero` proves the count is
zero. Zero is not selected: the explicit prime guard implies `2 ≤ p`, hence
`4 ≤ p ^ 2`. The guards at `p = 2` and `p = 3` are proved in both files; Solution
also proves the corresponding concrete deficiency instances jointly with their
guards.

## Proof and source alignment

The source is `GroupCount.groupDeficient_prime_sq` in
`Proofs/GroupCount/GroupPerfect.lean`, accepted with source revision
`55ab7d253f32b9632581cf31cc4951c2b2119533`. It uses the already proved
`GroupCount.gnu_prime_sq` from `CdoIteration.lean`: there are exactly two groups
of order `p ^ 2` up to isomorphism, and `2 < 4 ≤ p ^ 2`.

Challenge uses only four Mathlib imports. Solution repeats the **same independent
model**, without importing Challenge or replacing its definitions by source
aliases. `Bridge.isoClassEquiv` transports the source equivalence between explicit
tables and Mathlib group structures through the isomorphism quotients.
`Bridge.groupCount_eq_gnu` then proves equality of counts **for every natural
order, including zero**. Only after that equality is established does Solution
apply the selected source theorem.

The paired model block and theorem header were compared byte-for-byte. This is
stronger than observing identical printed theorem names; the semantic bridge is
proved, not deferred to the reviewer. See `verification.md` for hashes, exact
signatures, commands, timing, axiom outputs, and the recorded initial failed
elaboration attempt.

## Attribution, automation, and limitations

The mathematics is the classical classification of groups of order `p²`: the
cyclic group `C_(p²)` and `C_p × C_p` are the two isomorphism classes. The selected
inequality is its elementary corollary, not a new mathematical result. The
repository relates the group count to OEIS A000001 and group-deficiency to the
A090052 terminology. Its `CdoIteration.lean` commentary credits Mitch Harris for
the A000001 entry's formula `a(p²) = 2`; that is not an attribution of the original
classification theorem. No original discoverer, exhaustive literature search,
or external formalization-priority claim is supplied here.

AI assistance was material. The latest prime-square implementation and this
package were prepared using **gpt-6-astra, xhigh**, in the Yah framework. Exact
models and provenance of earlier foundational infrastructure are unknown.
No human formalization author or responsible maintainer has been authoritatively
identified; the corresponding `formalization.yaml` lists are deliberately empty
and are submission blockers. The repository license is MIT; license ownership
alone is not used to infer formalization authorship or review.

**USER is the sole reviewer, and review remains pending.** No agent, subagent,
or parent review is claimed. The imported source archives retain their original
open-conjecture sorries; the fresh selected-closure audits exclude them. JSON/YAML
parsing is not full metadata-schema validation. Missing verifier tools and human
metadata must be resolved before claiming those checks or package readiness.
