/-
# A349044 — the non-Brauer gap: can `l*(n) − l(n)` exceed `1`?

## OEIS source (re-pulled verbatim with `goof oeis show A349044`, 2026-08-05)

```
NAME:     Non-Brauer numbers.
TERMS:    12509,13207,13705,15473,16537,20753,22955,23219,23447,24797,25018,
          26027,26253,26391,26414,26801,27401,27410,30897,30946,31001,32921,
          33065,33074,41489,41506,43755,43927,45867,46355,46419,46797,46871,
          46894,47761,49373,49577,49593,49594,49611,50036,50829,51667
KEYWORDS: nonn
COMMENTS:
  A sequence 1=a_0 < a_1 < a_2 < ... < a_l = n is an addition chain (of length
  l) for n if for each i, 0 < i <= l, there are j_i and k_i such that
  a_i = a_j_i + a_k_i. Such a chain is called a star-chain or Brauer chain if in
  addition each j_i = i-1. A number is a Brauer number if among its shortest
  addition chains there is a Brauer chain, and non-Brauer otherwise.

  The length of a shortest Brauer chain for n is often denoted l^*(n).
  A003313(n) gives the length of a shortest addition chain for n. Thus n is in
  this sequence if and only if A003313(n) < l^*(n).

  For entries at least through 41506, these numbers satisfy
  l^*(n) = A003313(n) + 1. It seems likely that larger differences between
  l^*(n) and A003313(n) occur for later entries in this sequence, but it is
  unclear whether any n with a larger difference have been found.

  These differences between l^*(n) and A003313(n) are highlighted by the
  following formulation: consider a machine which starts with a 1 in "cache" and
  can then at each step execute one of two operations: (1) Add any number that
  has ever been in cache to the current contents of cache, or (2) Restore any
  number that has previously been in cache to the cache, replacing its prior
  contents. Then n is in this sequence if and only if there is a shortest
  program that results in n in cache that includes a "Restore" step. Note
  further that if there is an entry in this sequence such that
  l^*(n) > A003313(n)+1, then all shortest programs producing n in cache would
  contain a "Restore" operation. The definition of A293771 is based on a similar
  machine with a separate "Store" operation that puts the cache value into
  "memory," and one could formulate an analogous conjecture here that the
  "Restore" operation is never necessary for a shortest program. The existence
  or not of an n in this sequence such that l^*(n) > A003313(n)+1 would settle
  this question and provide mild evidence one way or the other on the conjecture
  in A293771.
XREFS:
  Cf. A003313, the length of a shortest addition chain for n.
  Cf. A079301, A079302, the number of shortest addition chains for n which are
  Brauer chains and which are non-Brauer chains, respectively.
```

## Status — **two open questions, in opposite directions**

The entry is careful and the card must be too.  Neither of these is known:

* `∃ n, l*(n) ≥ l(n) + 2` — the entry's "It seems likely".
* `∀ n, l*(n) ≤ l(n) + 1` — its negation, equally unproved.

Stating only one of them would misrepresent the source.  Both appear below.

## Repo adjacency

`Proofs/NumberComplexity/AdditionChain.lean` already has `IsAddChain`,
`chainSteps`, `AdditionChain n`, `l n` (= A003313), the ascending mirror
`IsAscAddChain`/`lAsc`, and `l_eq_lAsc`.  The Brauer variant defined here is a
one-constructor restriction of the existing `IsAddChain` inductive, so it
inherits the whole convention (reversed lists, head = newest element).
-/
import Mathlib
import NumberComplexity.AdditionChain

set_option autoImplicit false

namespace Candidates.A349044

open NumberComplexity

/-! ## Definition layer

Existing repo definitions reused verbatim:

```lean
inductive IsAddChain : List ℕ → Prop
  | one : IsAddChain [1]
  | add {c : List ℕ} {a b : ℕ} (ha : a ∈ c) (hb : b ∈ c) (hc : IsAddChain c) :
      IsAddChain ((a + b) :: c)

def chainSteps (c : List ℕ) : ℕ := c.tail.length
abbrev AdditionChain (n : ℕ) : Type := {c : List ℕ // IsAddChain c ∧ c.head? = some n}
noncomputable def l (n : ℕ) : ℕ := ⨅ c : AdditionChain n, chainSteps c.val
```

Note the repo convention: chains are stored **reversed**, so `c.head?` is the
*newest* element (= `n`) and `IsAddChain.add` prepends.  A **Brauer** (star)
chain is exactly the restriction in which the new element uses the *immediately
previous* element as one summand — i.e. `a` must be the current head.  That is a
one-line change to the inductive, which is why this definition is a natural
extension rather than a parallel universe.

`leandoc` findings: nothing for addition chains in Mathlib
(`leandoc "addition chain"` returns `AddChain`-free noise), so the repo's
definitions are the only ones available and are used. -/

/-- **Brauer (star) chains**, in the repo's reversed-list convention: each new
element is `head + b` for some `b` already in the chain.  Compare
`IsAddChain`, where *both* summands may be arbitrary chain elements. -/
inductive IsBrauerChain : List ℕ → Prop
  | one : IsBrauerChain [1]
  | star {c : List ℕ} {a b : ℕ} (hb : b ∈ (a :: c)) (hc : IsBrauerChain (a :: c)) :
      IsBrauerChain ((a + b) :: a :: c)

/-- A Brauer chain for `n`. -/
abbrev BrauerChain (n : ℕ) : Type := {c : List ℕ // IsBrauerChain c ∧ c.head? = some n}

/-- `lStar n = l*(n)`: the length of a shortest Brauer chain for `n`.
Noncomputable for the same reason as the repo's `l` — it is an `⨅` over a
subtype. -/
noncomputable def lStar (n : ℕ) : ℕ := ⨅ c : BrauerChain n, chainSteps c.val

/-- Membership in A349044: `n` is a **non-Brauer number**, i.e. no shortest
addition chain for `n` is a Brauer chain.  Per the entry's own restatement,
this is equivalent to `l(n) < l*(n)`. -/
def IsNonBrauer (n : ℕ) : Prop := l n < lStar n

/-! ## The statements -/

/-- **The entry's "It seems likely" — open.**

Verbatim: "It seems likely that larger differences between l^*(n) and A003313(n)
occur for later entries in this sequence, but it is unclear whether any n with a
larger difference have been found."

Formalized as: some `n` has gap at least `2`.  Note the source hedges twice
("seems likely", "unclear whether … have been found"), so this is a
*speculation* recorded in the entry, not an asserted conjecture; the card should
not upgrade it, and `nonBrauer_gap_le_one` below states the opposite with equal
weight.

**Mathlib primitives available.**  None for addition chains.  What is available
and relevant: `Nat.sInf`/`iInf` API (`ciInf_le`, `le_ciInf`, `Nat.sInf_le`,
`Nat.le_sInf`), `Nat.log2`/`Nat.size` for the `⌊log₂ n⌋ ≤ l(n)` lower bound,
`Nat.binaryRec` for the binary-method upper bound `l(n) ≤ ⌊log₂ n⌋ + ν(n) − 1`
(`ν` = popcount, `Nat.popCount` exists in core).

**Sketch of what is known.**  Everything here is by search:
* `l*(n) = l(n)` for all `n < 12509` (Knuth, TAOCP 4.6.3, exercise 5.9 and the
  tables there).
* `12509` is the least non-Brauer number (Hansen 1959 gave the first known
  example; Knuth records `12509` as least).
* The gap is `1` for every known non-Brauer number, checked "at least through
  41506" per the entry.
No structural theorem bounds `l*(n) − l(n)`.  Hansen chains (a generalization
sitting between Brauer and general) give the only known lower-bound technique,
and they do not separate the two by more than `1` in any known instance.

**Sketch of an attack on `nonBrauer_gap_le_one`.**  A Brauer chain can simulate
a general chain step `a_i = a_j + a_k` (with `j < i−1`) by *re-deriving* `a_j`,
which costs extra steps — but not obviously only one.  Any proof of the `≤ 1`
bound would have to show one re-derivation always suffices, which is false for
chains with many "old" references; so the honest expectation is that the `≥ 2`
side is true and merely unwitnessed.  Hence the entry's phrasing.

**Tactic families.**  `decide` on `IsBrauerChain`/`IsAddChain` for a *fixed*
candidate chain (both are decidable in the repo's convention);
exhaustive chain search is the expensive part — certifying `lStar 12509 = 18`
means ruling out every Brauer chain of length `17`, which is on the order of
`17!/(something)` and needs the standard pruning (bound by
`a_i ≤ 2^i`, `a_i ≥ n / 2^(l−i)`).  `Nat.sInf_le` gives upper bounds from a
single witness; `Nat.le_sInf` needs the exhaustion.

**Related work in this repo.**  `NumberComplexity.AdditionChain`
(`IsAddChain`, `l`, `lAsc`, `l_eq_lAsc`, `lAsc_eq_A003313_of_le_eight`) — the
permissive/ascending equivalence landed there is the direct precedent for the
`IsBrauerChain → IsAddChain` bridge below.  `A293771WhitneyMachine.lean` in this
directory formalizes the *other* machine the entry's last comment compares
against; the two cards should be read together. -/
theorem nonBrauer_gap_two_exists : ∃ n : ℕ, 0 < n ∧ l n + 2 ≤ lStar n := by
  sorry

/-- **The opposite claim — equally open.**

If this held, then per the entry "all shortest programs producing n in cache
would contain a Restore operation" never happens, and it would be evidence for
the A293771 conjecture.  Stated so the card does not silently pick a side. -/
theorem nonBrauer_gap_le_one : ∀ n : ℕ, 0 < n → lStar n ≤ l n + 1 := by
  sorry

/-- **The entry's verified range**: every listed non-Brauer number up to `41506`
has gap exactly `1`.  A *finite* claim, hence in principle provable — but each
instance needs an exhaustive Brauer-chain search, so it is expensive rather than
open. -/
theorem nonBrauer_gap_one_below_41506 (n : ℕ) (hn : n ≤ 41506) (h : IsNonBrauer n) :
    lStar n = l n + 1 := by
  sorry

/-- `12509` is the least non-Brauer number — the first DATA term.  Finite, and
the natural first certificate target. -/
theorem isNonBrauer_12509 : IsNonBrauer 12509 := by
  sorry

/-- …and nothing below it is. -/
theorem not_isNonBrauer_below_12509 (n : ℕ) (hn : 0 < n) (hlt : n < 12509) :
    ¬ IsNonBrauer n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: every Brauer chain is an addition chain.  This is the bridge that
-- makes `l n ≤ lStar n` a triviality, and it is the first thing to prove.
theorem IsBrauerChain.isAddChain {c : List ℕ} (h : IsBrauerChain c) : IsAddChain c := by
  sorry

-- PROVABLE: hence `l n ≤ lStar n` always, so `IsNonBrauer` is the assertion of
-- *strict* inequality and the gap is nonnegative by construction.
theorem l_le_lStar (n : ℕ) : l n ≤ lStar n := by
  sorry

-- PROVABLE: satisfiability of `IsBrauerChain` — concrete small chains.
-- Reversed convention: `[8, 4, 2, 1]` is the doubling chain for `8`.
example : IsBrauerChain [1] := IsBrauerChain.one
example : IsBrauerChain [2, 1] := IsBrauerChain.star (by simp) IsBrauerChain.one

-- PROVABLE: `lStar` agrees with `l` on the small range, matching A003313's head
-- `0,1,2,2,3,3,4,3` for `n = 1..8` (already proved for `lAsc` in the repo as
-- `lAsc_eq_A003313_of_le_eight`).
example : lStar 1 = 0 ∧ lStar 2 = 1 ∧ lStar 3 = 2 ∧ lStar 4 = 2 ∧
    lStar 5 = 3 ∧ lStar 6 = 3 ∧ lStar 7 = 4 ∧ lStar 8 = 3 := by
  sorry

-- PROVABLE: `l` and `l*` agree for every `n ≤ 100` — the candidates document's
-- proposed sanity layer.  Each value is a bounded search; feasible but not
-- cheap.  Do this *after* a memoised computable mirror of `lStar` exists,
-- mirroring the repo's `complexityRec` trick for `complexity`.
example : ∀ n ∈ Finset.Icc 1 100, l n = lStar n := by
  sorry

-- PROVABLE: nonvacuity guard — `lStar` is an `⨅` over `BrauerChain n`, which is
-- **empty** for `n = 0` (no chain has head `0`), so `lStar 0` is the `⊥` junk
-- value `0`.  Every statement above therefore carries `0 < n`.  This example
-- records the degeneracy rather than hiding it.
example : lStar 0 = 0 := by
  sorry

/-! ## Notes for a follow-up card

The infrastructure deliverables, in order:

1. `IsBrauerChain.isAddChain` and `l_le_lStar` — free, and they establish that
   the "gap" is a nonnegative quantity so the statements are about the right
   thing.
2. A **computable mirror** `lStarRec` with `lStar_eq_lStarRec`, exactly
   paralleling `complexityRec`/`complexity_eq_complexityRec` in
   `NumberComplexity.IntComplexity`.  Without it no `native_decide` sanity check
   is even type-correct (`lStar` is noncomputable).  This is the gating item.
3. `l n = lStar n` for `n ≤ 100`, then push toward `12509`.
4. `isNonBrauer_12509` — the headline certificate.  Needs a pruned exhaustive
   search: standard bounds are `a_i ≤ 2^i` and `a_i · 2^(l−i) ≥ n`.

Reference: Knuth, *TAOCP* Vol. 2, §4.6.3; Hansen, *Zum Scholz–Brauerschen
Problem*, J. reine angew. Math. 202 (1959) 129–136. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES** (no substantive defects)

Independent re-pull of A349044 and A003313 plus a read of
`Proofs/NumberComplexity/AdditionChain.lean`, 2026-08-05.

Confirmed:
* The long A349044 comment block is quoted **word for word**.
* **The `IsBrauerChain` inductive is a correct formalization** of the OEIS's
  "star-chain … each `j_i = i − 1`": traced through, it generates `[1]`,
  `[2,1]`, `[3,2,1]`, `[4,2,1]`, and the `star` rule forces one summand to be
  the current head, exactly matching `j_i = i − 1`.  The first step from `[1]`
  is derivable.
* All repo API cited exists with the claimed signatures: `IsAddChain` (`:101`),
  `chainSteps` (`:231`), `AdditionChain` (`:283`), `l` **noncomputable**
  (`:356`), `IsAscAddChain` (`:742`), `lAsc` (`:987`), `l_eq_lAsc` (`:1034`),
  `lAsc_eq_A003313_of_le_eight` (`:1150`).
* **The `lStar 0 = 0` degeneracy analysis is right**: `Nat.iInf_of_empty`
  gives `⨅` over an empty type `= 0` in `ℕ`, and the repo's own `l_zero` is
  proved that way.  Hence the `0 < n` guards.
* `nonBrauer_gap_two_exists` and `nonBrauer_gap_le_one` are exact negations
  modulo the guard, and the entry genuinely leaves both open.
* `12509` is the first DATA term and is standardly cited as the least
  non-Brauer number.

Notes (not defects):
* The entry's `%F` line (`A079301(n) = 0 iff n occurs in this sequence`) is not
  quoted; the header quotes `%N`, `%C`, `%Y` only.
* "Hansen 1959 gave the first known example" could not be verified to the
  primary source in-session; the phrasing already separates Hansen's example
  from Knuth's "least" record, so no change made.
-/

end Candidates.A349044
