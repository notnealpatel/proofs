import NumberComplexity.ComplexityDefect

/-!
# Quarantined admissions

The original source and disclosure documentation is retained below as historical context.
Descriptions of the original file refer to its pre-quarantine layout: independent proven
infrastructure now lives in the imported production module; the admissions and their
admission-dependent consequences live only here. No proof closure is claimed.
-/

/-
  NumberComplexity/ComplexityDefect — OEIS A244743: the smallest `n` at which
  the integer-complexity DROP `‖n-1‖ - ‖n‖` equals `k`.  Both halves of the
  entry's status line are OPEN — that the drop is unbounded, and that the
  sequence is well defined at all — and they are carried here by one intended,
  disclosed `sorry` over a proved sanity layer.

  Also fixes the terminology this lane inherited: the *defect* of the
  Altman–Zelinsky literature is `‖n‖ - 3 log₃ n`, a different quantity, given
  its own section below.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/

/-!
# OEIS A244743 — the complexity drop `‖n-1‖ - ‖n‖`

`NumberComplexity.complexity` (`NumberComplexity/IntComplexity.lean`) is integer
(Mahler–Popken) complexity, OEIS A005245: the least number of `1`'s in a
`{1, +, ×}`-expression evaluating to `n`, written `‖n‖` here and in the
literature.  A005245 is famously non-monotone — `‖11‖ = 8` but `‖12‖ = 7` — and
A244743 indexes exactly how far down it can jump in a single step.

## Primary sources (pinned VERBATIM)

`goof oeis show A244743`, pulled live 2026-08-05 —

> name: "Smallest number n with ||n-1||-||n|| = k where ||n||=A005245(n) denotes
> the complexity of n."

> terms: 6,12,24,108,720,1440,81648,2041200,612360000

> comments:
> "The k-th term of this sequence is the least n with ||n-1||-||n|| = k if such
> an n exists."
> "It is conjectured that ||n-1||-||n|| is not bounded. But there is no proof
> that the sequence is infinite or is well defined."

> xrefs: "Cf. A005245, A252739 (see comments)."

> keywords: nonn,more

The offset is `0`, i.e. `a(0) = 6`: the OEIS internal format line for the entry
is `%O A244743 0,1` (recorded by the source-fidelity re-pull in
`Proofs/Scratch/Candidates/A244743ComplexityDefect.lean`), and it is confirmed
independently below — `A244743_zero`, `A244743_one`, `A244743_two` prove
`a(0) = 6`, `a(1) = 12`, `a(2) = 24` outright by kernel computation.

`goof oeis show A005245`, pulled live 2026-08-05 —

> name: "The (Mahler-Popken) complexity of n: minimal number of 1's required to
> build n using + and *."

> terms: 1,2,3,4,5,5,6,6,6,7,8,7,8,8,8,8,9,8,9,9,9,10,11,9,10,10,9,10,11,10,
> 11,10,11,11,11,10,11,11,11,11,12,11,12,12,11,12,13,11,12,12,12,12,13,11,12,
> 12,12,13,14,12,13,13,12,12,13,13,14,13,14,13,14,12,13,13,13,13,14,13,14

> comment: "The second Altman links proves that {a(n) - 3*log_3(n)} is a
> well-ordered subset of the reals whose intersection with [0,k) has order type
> omega^k for each positive integer k, so this set itself has order type
> omega^omega. - _Jianing Song_, Apr 13 2024"

A252739 (the `see comments` cross-reference), `goof oeis show A252739`, pulled
live 2026-08-05 — the record of a *failed* prediction of further terms, which is
the best available evidence for how little is known:

> "Note how 6, 720 and 612360000 occur in A244743 as its 0th, 4th and 8th term,
> from which my bold conjecture that A244743(12) or A244743(16) =
> 1697781042840960000000000."
> "According to preliminary results from _Janis Iraids_, the value of
> A005245(a(5)) = ||1697781042840960000000000|| = 160, while
> ||1697781042840960000000000 - 1|| = 169, which lays to rest my naive
> conjecture above, as 169 - 160 is neither 12 nor 16. - _Antti Karttunen_,
> Dec 20 2015"

H. Altman, J. Zelinsky, *Numbers with integer complexity close to the lower
bound*, arXiv:1207.4841 (`References/arXiv-1207-4841`, fetched 2026-08-05) —
the definition of the *defect*, verbatim from `paper.tex`:

> \begin{defn}
> The \emph{defect} of a natural number $n$ is given by
> \begin{equation*}\label{defd}
> \dft(n)=\cpx{n}-3\log_3 n
> \end{equation*}
> \end{defn}

> John Selfridge showed that $\cpx{n}\ge 3\log_3 n$ for all $n$.

## TERMINOLOGY — two different quantities, both in scope here

The dispatch brief for this file described "the defect of `n`" as
`complexity n - 3 * Nat.log 3 n` while sourcing the file to A244743.  Those are
not the same object, and neither of them is quite the brief's formula.  Both
real quantities are formalized below, under names that cannot be confused:

* `complexityDrop n = ‖n-1‖ - ‖n‖` (in `ℤ`) — **the A244743 quantity**.  Its
  unboundedness is the open conjecture; `neg_one_le_complexityDrop` is the
  bound the brief asked for under the name `neg_one_le_defect`, and it comes
  from `complexity_add_le` exactly as the brief predicted.
* `defect n = ‖n‖ - 3 logb 3 n` (in `ℝ`) — **the Altman–Zelinsky defect**, with
  the *real* logarithm, as displayed above.  `zero_le_defect` is a THEOREM, not
  a conjecture (Selfridge's bound, already proved in this repo as
  `three_mul_logb_three_le_complexity`), so there is no conjecture here to
  archive.  The brief's floor-logarithm variant appears as
  `three_mul_log_three_le_complexity` — `3 * Nat.log 3 n ≤ ‖n‖` — which is what
  makes the brief's `ℕ`-valued difference well defined in the first place.

See the lane report for the full discrepancy write-up.

## What is proved here, and what is not

* `complexityDrop`, `complexityDropRec`, `complexityDrop_eq_complexityDropRec`
  — the drop, its computable mirror through `complexity_eq_complexityRec`, and
  the bridge.  Junk at `n ≤ 1` is pinned (`complexityDrop_zero`,
  `complexityDrop_one`), and every substantive statement is guarded by `2 ≤ n`.
* `neg_one_le_complexityDrop` — `-1 ≤ ‖n-1‖ - ‖n‖` for `2 ≤ n`, from
  `‖n‖ = ‖(n-1) + 1‖ ≤ ‖n-1‖ + ‖1‖`.  **Proved**, and **sharp**:
  `complexityDrop_two` gives `‖1‖ - ‖2‖ = -1`.  So the conjecture is genuinely
  one-sided — only the upper direction is open.
* `complexityDrop_le` — the crude `‖n-1‖ - ‖n‖ ≤ n - 2`, so each individual
  drop is finite.  **Proved.**  The conjecture is that the *supremum* over `n`
  is not.
* `dropLevel`, `A244743`, `A244743_eq_zero_iff`, `A244743_spec` — the sequence
  as `sInf {n | 2 ≤ n ∧ ‖n-1‖ - ‖n‖ = k}`, its junk value, and its
  characterisation *conditional on the level set being nonempty*.  All
  **proved**; the conditional form is the honest one, because the source says
  outright that no proof of well-definedness is known.
* `dropLevel_nonempty` — THE CONJECTURE, in the form "every `k` is attained",
  i.e. A244743 is well defined at every index.  OPEN; one intended, disclosed
  `sorry`.  `complexityDrop_unbounded` and `A244743_mem_dropLevel` are proved
  *from* it.
* `A244743_zero`, `A244743_one`, `A244743_two` — `a(0) = 6`, `a(1) = 12`,
  `a(2) = 24`, each with its minimality sweep, by kernel `decide` through
  `complexityRec`.  **No `native_decide` anywhere in this file.**
* `defect`, `zero_le_defect`, `defect_three_pow`,
  `three_mul_log_three_le_complexity` — the Altman–Zelinsky defect section
  described above.  All **proved**.

NOT formalized: Altman's order-type theorem quoted in the A005245 comment (the
defect set has order type `ω^ω`).  That needs the ordinal-valued order type of a
well-ordered subset of `ℝ`, a substantial development orthogonal to A244743.

## Cost of the ground-truth window (measured 2026-08-05, this machine)

`complexityFuel` is unmemoised, but the kernel's `whnf` cache supplies the
memoisation during `decide`, so kernel reduction is far cheaper here than the
compiled interpreter.  A scratch run holding both a `#eval` of the drop table to
`n = 41` and the `k ≤ 2` `decide` checks did not finish inside 300 s; the same
`decide` checks alone — which need `‖m‖` for every `m ≤ 24` — cost ≈ 2 s.  So
`#eval` is the wrong instrument for this recurrence and none is used here.

The window stops at `k = 2` on cost grounds, not on principle.  `a(3) = 108` was
verified by kernel `decide` during development and is reproducible:
`complexityDrop 108 = 3` alone costs ≈ 41 s, and adding the minimality sweep
over `m ∈ [2, 108)` brings the pair to ≈ 54 s (the sweep is cheap once the cache
is warm).  That is ~25× the whole rest of this file, so it is left out.
`a(4) = 720` was not attempted.

That development check also corrects the mining sketch
`Proofs/Scratch/Candidates/A244743ComplexityDefect.lean`, which recorded
`‖107‖ = 14`.  The correct value is `‖107‖ = 16`: the drop `‖107‖ - ‖108‖ = 3`
is kernel-checked, and `‖108‖ = 13` — upper bound from
`108 = (1+1)² · (1+1+1)³`, matched below by an exhaustive run of the A005245
recurrence outside Lean.  The `‖108‖ = 13` half is therefore *computed*, not
kernel-proved, in this file; only the drop is.

## Junk-value discipline

`complexity 0 = 0` is junk (`complexity_zero`: `0` is not expressible from `1`
by `+` and `×`, and `Nat.sInf ∅ = 0`).  `complexityDrop n` mentions
`complexity (n - 1)` with `ℕ`-truncated subtraction, so it is junk at `n = 0`
(where `0 - 1 = 0`) and at `n = 1` (where it reads `‖0‖ - ‖1‖`); both are pinned
and every real statement carries `2 ≤ n`.  `A244743 k = 0` is junk too, and
`A244743_eq_zero_iff` shows it happens exactly when the level set is empty —
which is precisely the failure the conjecture rules out.  `Real.logb 3 n` and
`Nat.log 3 n` are guarded by `1 ≤ n`.
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## 4. The conjecture

One intended, disclosed `sorry`.  Everything above is sorry-free, and the two
statements below are proved *from* the sorried one. -/

/-- **OEIS A244743, THE CONJECTURE** — OPEN: every `k` is attained, i.e. for
every `k` there is an `n ≥ 2` with `‖n-1‖ - ‖n‖ = k`, so the sequence A244743 is
well defined (and infinite) at every index.

Verbatim from the entry: "It is conjectured that ||n-1||-||n|| is not bounded.
But there is no proof that the sequence is infinite or is well defined."

This is the *stronger* of the two claims in that sentence: unboundedness alone
would permit the drop to skip a value `k`, leaving `a(k)` undefined while the
sequence still ran off to infinity.  `complexityDrop_unbounded` derives the
weaker, literally-stated form from it.

Status (sweep 2026-08-05): open, with only nine terms known — `a(0) = 6` through
`a(8) = 612360000` — and `keywords: nonn,more`.  Nothing resembling a general
construction is known; the A252739 cross-reference records Karttunen's attempt
to predict `a(12)` or `a(16)` from the pattern `6, 720, 612360000` and Iraids'
computation refuting it.  The obstruction is structural: a large drop at `n`
needs `n` smooth (so `‖n‖` is small) with `n - 1` of provably *large*
complexity, and lower bounds on `‖·‖` beyond Selfridge's `3 log₃ n`
(`three_mul_logb_three_le_complexity`) are the hard direction of the whole
subject — the same wall as `complexity_two_pow` in `DoublingConjecture.lean`.

Non-vacuity: the level set is nonempty for `k = 0, 1, 2` outright, proved below
by `A244743_zero`, `A244743_one`, `A244743_two`. -/
theorem dropLevel_nonempty (k : ℕ) : (dropLevel k).Nonempty := by
  -- INTENDED SORRY: open problem (OEIS A244743, "no proof that the sequence is
  -- infinite or is well defined").  Proved for `k ≤ 2` by the certificates
  -- below; the general case needs complexity lower bounds beyond Selfridge's.
  sorry

/-- **The conjecture as the entry literally states it** — "||n-1||-||n|| is not
bounded" — derived from well-definedness by taking the level `⌈B⌉ + 1`.
Phrased with `<` over an explicit bound rather than as an `iSup`, which would
collapse on an empty index. -/
theorem complexityDrop_unbounded (B : ℤ) : ∃ n : ℕ, 2 ≤ n ∧ B < complexityDrop n := by
  obtain ⟨n, hn2, hnk⟩ := dropLevel_nonempty (B.toNat + 1)
  refine ⟨n, hn2, ?_⟩
  have hself : B ≤ (B.toNat : ℤ) := Int.self_le_toNat B
  rw [hnk]
  push_cast
  omega

/-- The unconditional form of `A244743_spec`, granted the conjecture: the value
`A244743 k` really is the least `n` realising the drop `k`, for every `k`. -/
theorem A244743_mem_dropLevel (k : ℕ) : A244743 k ∈ dropLevel k :=
  Nat.sInf_mem (dropLevel_nonempty k)

end NumberComplexity
