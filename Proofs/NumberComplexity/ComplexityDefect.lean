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
import Mathlib
import NumberComplexity.IntComplexity
import NumberComplexity.DoublingConjecture

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

/-! ## 1. The drop `‖n-1‖ - ‖n‖`

The subtraction of complexities happens in `ℤ`, after casting, because it is
routinely negative: `‖n-1‖ - ‖n‖ = -1` at every `n` whose optimal expression
extends an optimal expression for `n - 1` by `+1`.  The `n - 1` inside the
argument is `ℕ`-truncated and therefore junk at `n = 0`; `complexityDrop_succ`
removes it whenever a caller prefers the shifted index. -/

/-- The **A244743 drop** at `n`: `‖n-1‖ - ‖n‖`, as an integer.  This is the
quantity whose unboundedness OEIS A244743 conjectures, and whose level sets
index the sequence.

JUNK VALUES: `complexityDrop 0 = 0` and `complexityDrop 1 = -1` both involve
`complexity 0 = 0`, which is itself junk; every statement below is guarded by
`2 ≤ n`. -/
noncomputable def complexityDrop (n : ℕ) : ℤ :=
  (complexity (n - 1) : ℤ) - (complexity n : ℤ)

/-- The drop at a successor, with the `ℕ`-truncated subtraction discharged. -/
theorem complexityDrop_succ (n : ℕ) :
    complexityDrop (n + 1) = (complexity n : ℤ) - (complexity (n + 1) : ℤ) := by
  simp only [complexityDrop, Nat.add_sub_cancel]

/-- JUNK-VALUE PIN: at `n = 0` the truncated `0 - 1` is `0`, so the drop reads
`‖0‖ - ‖0‖ = 0`; it says nothing about A005245. -/
theorem complexityDrop_zero : complexityDrop 0 = 0 := by
  simp only [complexityDrop, Nat.zero_sub, sub_self]

/-- JUNK-VALUE PIN: at `n = 1` the drop reads `‖0‖ - ‖1‖ = 0 - 1`, and `‖0‖` is
the empty-infimum junk value, not a complexity. -/
theorem complexityDrop_one : complexityDrop 1 = -1 := by
  simp only [complexityDrop, Nat.sub_self, complexity_zero, complexity_one]
  norm_num

/-- Computable mirror of `complexityDrop`, built from the A005245 recurrence
`complexityRec`; this is what the kernel reduces during `decide`. -/
def complexityDropRec (n : ℕ) : ℤ :=
  (complexityRec (n - 1) : ℤ) - (complexityRec n : ℤ)

/-- The bridge: the drop agrees with its computable mirror everywhere (at the
junk arguments both sides take the same junk value). -/
theorem complexityDrop_eq_complexityDropRec (n : ℕ) :
    complexityDrop n = complexityDropRec n := by
  simp only [complexityDrop, complexityDropRec, complexity_eq_complexityRec]

/-! ## 2. What is provable about the drop

The lower bound is the whole of the currently-known general theory, and it is
sharp.  The upper bound is crude but records that each individual term is
finite — the conjecture is about the supremum, not about any single value. -/

/-- **THE LOWER BOUND** — `-1 ≤ ‖n-1‖ - ‖n‖` for `2 ≤ n`.  Appending `+1` to an
optimal expression for `n - 1` represents `n` at cost `‖n-1‖ + 1`, so
`‖n‖ ≤ ‖n-1‖ + ‖1‖ = ‖n-1‖ + 1`.

This is the bound NEXT_TARGETS F1 requested under the name `neg_one_le_defect`,
and it does come from `complexity_add_le` exactly as predicted there.  It is
**sharp** (`complexityDrop_two`), which is what makes A244743 one-sided: the
drop can never fall below `-1`, and whether it can rise arbitrarily high is the
open question. -/
theorem neg_one_le_complexityDrop {n : ℕ} (hn : 2 ≤ n) : -1 ≤ complexityDrop n := by
  have hpos : 1 ≤ n - 1 := by omega
  have hsplit : (n - 1) + 1 = n := by omega
  have hsub : complexity ((n - 1) + 1) ≤ complexity (n - 1) + complexity 1 :=
    complexity_add_le hpos (le_refl 1)
  rw [hsplit, complexity_one] at hsub
  simp only [complexityDrop]
  omega

/-- Sharpness of `neg_one_le_complexityDrop`, at the first non-junk argument:
`‖1‖ - ‖2‖ = 1 - 2 = -1`. -/
theorem complexityDrop_two : complexityDrop 2 = -1 := by
  rw [complexityDrop_eq_complexityDropRec]
  decide

/-- Each individual drop is finite: `‖n-1‖ - ‖n‖ ≤ n - 2` for `2 ≤ n`, from the
all-ones witness `‖n-1‖ ≤ n - 1` and positivity `1 ≤ ‖n‖`.  Crude, but it makes
the content of the conjecture precise — every term is bounded, and the claim is
that the bounds are not uniform. -/
theorem complexityDrop_le {n : ℕ} (hn : 2 ≤ n) : complexityDrop n ≤ (n : ℤ) - 2 := by
  have hupper : complexity (n - 1) ≤ n - 1 := complexity_le_self (by omega)
  have hlower : 1 ≤ complexity n := one_le_complexity (by omega)
  simp only [complexityDrop]
  omega

/-! ## 3. The sequence A244743

The entry defines `a(k)` as the least `n` with `‖n-1‖ - ‖n‖ = k` "if such an `n`
exists".  That proviso is the whole difficulty, so the definition here is a
total `Nat.sInf` with its junk value pinned, and the characterising property is
stated *conditionally* on the level set being nonempty.  A total unconditional
`def` returning "the least such `n`" would assert what the source denies. -/

/-- The `k`-th level set of the drop: the `n ≥ 2` with `‖n-1‖ - ‖n‖ = k`.
A244743 asks for its least element. -/
def dropLevel (k : ℕ) : Set ℕ := {n : ℕ | 2 ≤ n ∧ complexityDrop n = (k : ℤ)}

/-- **OEIS A244743** (offset `0`): the smallest `n` with `‖n-1‖ - ‖n‖ = k`.

JUNK VALUE: `Nat.sInf ∅ = 0`, so `A244743 k = 0` whenever the level set is
empty (`A244743_eq_zero_iff`).  Whether that ever happens is exactly the open
well-definedness question — see `dropLevel_nonempty`. -/
noncomputable def A244743 (k : ℕ) : ℕ := sInf (dropLevel k)

/-- JUNK-VALUE PIN: `A244743 k = 0` exactly when no `n` realises the drop `k`.
(`0` itself is never in a level set, since every member satisfies `2 ≤ n`.) -/
theorem A244743_eq_zero_iff (k : ℕ) : A244743 k = 0 ↔ dropLevel k = ∅ := by
  rw [A244743, Nat.sInf_eq_zero]
  constructor
  · rintro (hmem | hempty)
    · exact absurd hmem.1 (by omega)
    · exact hempty
  · intro hempty
    exact Or.inr hempty

/-- Membership in a level set, reduced to a kernel computation: `v` realises the
drop `k` as soon as `2 ≤ v` and the computable mirror says so.  This is the
building block of every ground-truth certificate below. -/
theorem mem_dropLevel_of {k v : ℕ} (hv : 2 ≤ v)
    (hval : complexityDropRec v = (k : ℤ)) : v ∈ dropLevel k := by
  refine ⟨hv, ?_⟩
  rw [complexityDrop_eq_complexityDropRec]
  exact hval

/-- **CHARACTERISATION, conditional on well-definedness.**  If the level set is
nonempty then `A244743 k` is a genuine member of it and is the least such — the
entry's "least `n` with `‖n-1‖ - ‖n‖ = k` if such an `n` exists", with the
proviso discharged as a hypothesis rather than assumed away.  Sorry-free: the
open content sits entirely in supplying `h`, which is `dropLevel_nonempty`. -/
theorem A244743_spec {k : ℕ} (h : (dropLevel k).Nonempty) :
    2 ≤ A244743 k ∧ complexityDrop (A244743 k) = (k : ℤ) ∧
      ∀ m : ℕ, 2 ≤ m → complexityDrop m = (k : ℤ) → A244743 k ≤ m := by
  obtain ⟨hge, heq⟩ : A244743 k ∈ dropLevel k := Nat.sInf_mem h
  refine ⟨hge, heq, fun m hm2 hmk => ?_⟩
  exact Nat.sInf_le (show m ∈ dropLevel k from ⟨hm2, hmk⟩)

/-- Certificate schema for a term of A244743: a witness `v` realising the drop
`k`, together with a finite sweep showing no `m ∈ [2, v)` realises it, pins
`A244743 k = v`.  Both hypotheses are `decide`-able at concrete numerals through
`complexityDropRec`. -/
theorem A244743_eq_of {k v : ℕ} (hv : 2 ≤ v)
    (hval : complexityDropRec v = (k : ℤ))
    (hmin : ∀ m ∈ Finset.Ico 2 v, complexityDropRec m ≠ (k : ℤ)) :
    A244743 k = v := by
  have hmem : v ∈ dropLevel k := mem_dropLevel_of hv hval
  have hle : A244743 k ≤ v := Nat.sInf_le hmem
  obtain ⟨hge, heq⟩ : A244743 k ∈ dropLevel k := Nat.sInf_mem ⟨v, hmem⟩
  by_contra hne
  have hlt : A244743 k < v := lt_of_le_of_ne hle hne
  refine hmin (A244743 k) (Finset.mem_Ico.mpr ⟨hge, hlt⟩) ?_
  rw [← complexityDrop_eq_complexityDropRec]
  exact heq

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

/-! ## 5. Ground truth against the A244743 DATA line

`a(0) = 6`, `a(1) = 12`, `a(2) = 24`, each certified *with* its minimality
sweep, so what is checked is the entry's "smallest number `n`" and not merely
"some `n`".  Kernel `decide` only — no `native_decide`, so the trusted base
stays the kernel.  Reading the values off the A005245 DATA line: `‖5‖ = ‖6‖ = 5`
gives drop `0`; `‖11‖ = 8`, `‖12‖ = 7` gives drop `1`; `‖23‖ = 11`, `‖24‖ = 9`
gives drop `2`. -/

set_option maxRecDepth 4000 in
/-- OEIS A244743 `a(0) = 6`: `‖5‖ - ‖6‖ = 5 - 5 = 0`, and no `2 ≤ m < 6` has
drop `0`. -/
theorem A244743_zero : A244743 0 = 6 :=
  A244743_eq_of (by omega) (by decide) (by decide)

set_option maxRecDepth 16000 in
/-- OEIS A244743 `a(1) = 12`: `‖11‖ - ‖12‖ = 8 - 7 = 1`, and no `2 ≤ m < 12` has
drop `1`.  This is the first place where A005245 is non-monotone. -/
theorem A244743_one : A244743 1 = 12 :=
  A244743_eq_of (by omega) (by decide) (by decide)

set_option maxRecDepth 64000 in
/-- OEIS A244743 `a(2) = 24`: `‖23‖ - ‖24‖ = 11 - 9 = 2`, and no `2 ≤ m < 24`
has drop `2`. -/
theorem A244743_two : A244743 2 = 24 :=
  A244743_eq_of (by omega) (by decide) (by decide)

/-! ## 6. The Altman–Zelinsky defect — a *different* quantity

`\dft(n) = \cpx{n} - 3\log_3 n`, with the **real** logarithm, as displayed in
the source pinned in the header.  It is included here only to keep the two
notions apart: nothing about it is open at this level.  `zero_le_defect` is
Selfridge's bound, already proved in this repo, and the deep statement about it
— Altman's theorem that the defect set is well ordered of type `ω^ω`, quoted in
the A005245 comment — is not formalized. -/

/-- The **defect** of `n` (Altman–Zelinsky, arXiv:1207.4841): `‖n‖ - 3 log₃ n`.

NOT the A244743 quantity: that is `complexityDrop`.  The guard `1 ≤ n` on the
statements below keeps `Real.logb 3 n` off `Real.logb 3 0 = 0` and `complexity`
off `complexity 0 = 0`. -/
noncomputable def defect (n : ℕ) : ℝ := (complexity n : ℝ) - 3 * Real.logb 3 n

/-- **Selfridge's bound, as nonnegativity of the defect**: `0 ≤ δ(n)` for
`1 ≤ n`.  A theorem, not a conjecture — this is
`three_mul_logb_three_le_complexity` rearranged. -/
theorem zero_le_defect {n : ℕ} (hn : 1 ≤ n) : 0 ≤ defect n := by
  have h := three_mul_logb_three_le_complexity hn
  simp only [defect]
  linarith

/-- The defect vanishes exactly on the powers of three (here: the "at least"
half, for `1 ≤ b`), because `‖3^b‖ = 3b` and `log₃ 3^b = b`.  This is the
ground-truth check for `defect`, and it is where the constant `3 log₃` in the
definition comes from. -/
theorem defect_three_pow {b : ℕ} (hb : 1 ≤ b) : defect (3 ^ b) = 0 := by
  have hcpx : complexity (3 ^ b) = 3 * b := complexity_three_pow hb
  have hcast : (((3 : ℕ) ^ b : ℕ) : ℝ) = (3 : ℝ) ^ b := by push_cast; ring
  have hlog : Real.logb 3 (((3 : ℕ) ^ b : ℕ) : ℝ) = (b : ℝ) := by
    rw [hcast, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
    ring
  simp only [defect, hcpx, hlog]
  push_cast
  ring

/-- The defect of `1` is `1` — the only value it takes at a number that is not
a multiple of `3` times a smaller leader, and the ground-truth pin at the base
case (`‖1‖ = 1`, `log₃ 1 = 0`). -/
theorem defect_one : defect 1 = 1 := by
  simp only [defect, complexity_one, Nat.cast_one, Real.logb_one]
  ring

/-- **The brief's floor-logarithm form**: `3 * ⌊log₃ n⌋ ≤ ‖n‖` for `1 ≤ n`.  This
is what makes the `ℕ`-valued difference `‖n‖ - 3 * Nat.log 3 n` well defined
(non-truncating); it is strictly weaker than `zero_le_defect`, since
`Nat.log 3 n ≤ logb 3 n`.  Proof: cube the floor-power bound
`3 ^ ⌊log₃ n⌋ ≤ n` and compare with `n ^ 3 ≤ 3 ^ ‖n‖`. -/
theorem three_mul_log_three_le_complexity {n : ℕ} (hn : 1 ≤ n) :
    3 * Nat.log 3 n ≤ complexity n := by
  have hcube : n ^ 3 ≤ 3 ^ complexity n := pow_three_le_three_pow_complexity hn
  have hfloor : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 (by omega)
  have hstep : (3 : ℕ) ^ (3 * Nat.log 3 n) ≤ n ^ 3 := by
    calc (3 : ℕ) ^ (3 * Nat.log 3 n) = (3 ^ Nat.log 3 n) ^ 3 := by
          rw [Nat.mul_comm, pow_mul]
      _ ≤ n ^ 3 := Nat.pow_le_pow_left hfloor 3
  exact (Nat.pow_le_pow_iff_right (by omega)).mp (le_trans hstep hcube)

/-! ## 7. Satisfiability

Every hypothesis-bearing statement above is instantiated jointly at a concrete
model, so none of them is vacuous — including the sorried one, whose conclusion
holds outright at `k = 0, 1, 2`. -/

-- Satisfiability of the sorried conjecture: its conclusion holds outright at
-- `k = 0, 1, 2`, so `dropLevel_nonempty` is not vacuous.
set_option maxRecDepth 4000 in
example : (dropLevel 0).Nonempty := ⟨6, mem_dropLevel_of (by omega) (by decide)⟩

set_option maxRecDepth 16000 in
example : (dropLevel 1).Nonempty := ⟨12, mem_dropLevel_of (by omega) (by decide)⟩

set_option maxRecDepth 64000 in
example : (dropLevel 2).Nonempty := ⟨24, mem_dropLevel_of (by omega) (by decide)⟩

-- `A244743_spec` at a level where nonemptiness is proved, not assumed
set_option maxRecDepth 16000 in
example : 2 ≤ A244743 1 ∧ complexityDrop (A244743 1) = ((1 : ℕ) : ℤ) ∧
    ∀ m : ℕ, 2 ≤ m → complexityDrop m = ((1 : ℕ) : ℤ) → A244743 1 ≤ m :=
  A244743_spec ⟨12, mem_dropLevel_of (by omega) (by decide)⟩

-- the guarded general bounds at a concrete model
example : -1 ≤ complexityDrop 6 := neg_one_le_complexityDrop (by omega)
example : complexityDrop 6 ≤ (6 : ℤ) - 2 := complexityDrop_le (by omega)
example : 0 ≤ defect 6 := zero_le_defect (by omega)
example : defect (3 ^ 4) = 0 := defect_three_pow (by omega)
example : 3 * Nat.log 3 6 ≤ complexity 6 := three_mul_log_three_le_complexity (by omega)
example : A244743 0 = 6 :=
  A244743_eq_of (k := 0) (v := 6) (by omega) (by decide) (by decide)

/-- The guard `2 ≤ n` on `complexityDrop_le` is load-bearing, not decorative:
at the junk argument `n = 0` the drop is `0` while the bound reads `-2`. -/
example : complexityDrop 0 = 0 ∧ ¬(complexityDrop 0 ≤ (0 : ℤ) - 2) := by
  refine ⟨complexityDrop_zero, ?_⟩
  rw [complexityDrop_zero]
  norm_num

/-- The junk arguments are junk for a reason: `complexityDrop 1 = -1` is
arithmetically the same value as the sharp bound `complexityDrop 2 = -1`, but it
is computed from `complexity 0 = 0`, the empty-infimum convention, so it carries
no information about A005245. -/
example : complexityDrop 1 = -1 ∧ complexity 0 = 0 :=
  ⟨complexityDrop_one, complexity_zero⟩

/-- The drop really does take the value `-1` infinitely often in the certified
window, so `complexityDrop_unbounded` is not a statement about a monotone
quantity: `2, 3, 4, 5, 7` all have drop `-1`, interleaved with the drop-`0`
value at `6`. -/
example : ∀ m ∈ ({2, 3, 4, 5, 7} : Finset ℕ), complexityDropRec m = -1 := by decide

/-! ## 8. Axiom audit (sorry-free declarations only)

`dropLevel_nonempty`, `complexityDrop_unbounded` and `A244743_mem_dropLevel`
are omitted: the first is the intended `sorry` and the other two are proved
from it, so all three depend on `sorryAx` by design. -/

#print axioms complexityDrop
#print axioms complexityDrop_succ
#print axioms complexityDrop_zero
#print axioms complexityDrop_one
#print axioms complexityDropRec
#print axioms complexityDrop_eq_complexityDropRec
#print axioms neg_one_le_complexityDrop
#print axioms complexityDrop_two
#print axioms complexityDrop_le
#print axioms dropLevel
#print axioms A244743
#print axioms A244743_eq_zero_iff
#print axioms mem_dropLevel_of
#print axioms A244743_spec
#print axioms A244743_eq_of
#print axioms A244743_zero
#print axioms A244743_one
#print axioms A244743_two
#print axioms defect
#print axioms zero_le_defect
#print axioms defect_three_pow
#print axioms defect_one
#print axioms three_mul_log_three_le_complexity

end NumberComplexity
