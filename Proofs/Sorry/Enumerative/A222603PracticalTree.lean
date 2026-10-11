/-
# A222603 — Sun: the practical-number successor graph is a tree

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A222603` plus `curl "https://oeis.org/search?q=id:A222603&fmt=text"`:

```
%N A222603 a(1)=1; for n>0, a(n+1) is the least practical number q>a(n) such
           that 2(a(n)+1)-q is practical.
%O A222603 1,2
%A A222603 _Zhi-Wei Sun_, Feb 26 2013
%K A222603 nonn
COMMENTS:
  By a result of Melfi, each positive even number can be written as the sum of
  two practical numbers.
  For a practical number p, define h(p) as the least practical number q>p such
  that 2(p+1)-q is practical. Construct a simple (undirected) graph H as
  follows: The vertex set of H is the set of all practical numbers, and for two
  vertices p and q>p there is an edge connecting p and q if and only if h(p)=q.
  Clearly H contains no cycle.
  Conjecture: The graph H constructed above is connected and hence it is a tree.
XREFS:
  Cf. A005153, A222532, A163846, A163847, A222566.
TERMS: 1,2,4,6,8,12,18,20,24,30,32,36,42,54,56,60,66,78,80,84,90,104,120,162,176,
       192,210,224,234,260,270,272,276,294,320,330,342,378,380,384,390,392,396,
       414,416,420,450,462,464,468,476,486,510,512,522,546,594,620,630,702,704,
       714,726,728,744,750,798,800,810,812,816,920,924,930,966,968,972,980,990,
       992,1014,1040,1050,1088,1122,1232,1242,1254,1280,1290,1302,1316,1332,1350,
       1352,1380,1386,1458,1518,1520
```

**Attribution confirmed.**  The candidates document says "uncredited; likely
Zhi-Wei Sun".  The `%A` line settles it: **Zhi-Wei Sun, Feb 26 2013**.
Offset `1`.

## Why `h` is well defined — this is the load-bearing point

The entry's first comment is not decoration.  `h(p)` requires a practical
`q > p` with `2(p+1) − q` practical.  Melfi's theorem (every positive even
number is a sum of two practical numbers) applies to `2(p+1)`, giving
practicals `q + r = 2p + 2`; then `max(q, r) ≥ p + 1 > p`, and the *other*
summand is `2(p+1) − max(q,r)`, also practical.  So a valid `q` exists and the
"least" is well defined.

**Without Melfi, `h` is a partial function and the conjecture is not even
statable.**  The card therefore carries Melfi as an explicit hypothesis (or as a
`sorry`d theorem), rather than defining `h` with a junk default — which is
exactly the STYLE.md totalized-operator trap.

DATA spot-check: `a(2) = 2`.  `p = 1`, `2(1+1) = 4`.  Least practical `q > 1`
with `4 − q` practical: `q = 2` gives `4 − 2 = 2` practical ✓.
`a(3) = 4`: `p = 2`, `2·3 = 6`.  Least practical `q > 2` with `6 − q` practical:
`q = 4` gives `2` ✓ (`q = 3` is not practical).

## Status

Open.  The candidates document calls this "heavy … and an awkward one", which is
right; the awkwardness is exactly the well-definedness above.
-/
import Mathlib
import Enumerative.Practical

set_option autoImplicit false

namespace Candidates.A222603

/-! ## Definition layer

`leandoc` findings:

* `SimpleGraph` (`Mathlib/Combinatorics/SimpleGraph/Basic.lean`),
  `SimpleGraph.Connected` (a structure: `Preconnected` + `Nonempty`),
  `SimpleGraph.IsAcyclic`, and
  `SimpleGraph.IsTree` — `structure IsTree : Prop extends connected : G.Connected`
  with docstring "A *tree* is a connected acyclic graph."  So the conjecture's
  conclusion ("connected and hence it is a tree") is Mathlib-native.
* `Nat.find` / `Nat.lt_wfRel` for the "least such `q`".
* `Nat.Practical` from the repo.

**Junk-value discipline.**  `h p` is `Nat.find` over "`q > p` practical with
`2(p+1) − q` practical".  `Nat.find` demands a proof of nonemptiness, so `h` is
defined *taking that proof as an argument*.  A total `h : ℕ → ℕ` with a `0`
default would make `successorGraph` silently wrong wherever the default fires,
and the conjecture would then be about the wrong graph.

**`ℕ` subtraction.**  `2 * (p + 1) − q` truncates when `q > 2p + 2`.  The
predicate below bounds `q ≤ 2 * (p + 1)` explicitly, so truncation never
fires. -/

/-- The predicate `h` searches for: `q` is practical, `p < q ≤ 2(p+1)`, and
`2(p+1) − q` is practical.  The upper bound `q ≤ 2(p+1)` is what keeps the
`ℕ` subtraction off its junk value. -/
def HStep (p q : ℕ) : Prop :=
  q.Practical ∧ p < q ∧ q ≤ 2 * (p + 1) ∧ (2 * (p + 1) - q).Practical

instance (p q : ℕ) : Decidable (HStep p q) := by unfold HStep; infer_instance

/-- `h p` = the least `q` with `HStep p q`, given a proof that one exists.
The existence proof is an explicit argument, not an autoParam and not a junk
default — see the header. -/
def h (p : ℕ) (hp : ∃ q, HStep p q) : ℕ := Nat.find hp

/-- **The successor graph `H`.**  Vertices: practical numbers (as a subtype).
Edge `p — q` iff `h p = q` or `h q = p`.  Symmetrized explicitly because the
OEIS says "simple (undirected) graph".

Parametrized by the global existence hypothesis `hex`, which Melfi's theorem
supplies. -/
def successorGraph (hex : ∀ p : ℕ, p.Practical → ∃ q, HStep p q) :
    SimpleGraph {p : ℕ // p.Practical} where
  Adj p q :=
    (h p.1 (hex p.1 p.2) = q.1 ∧ p ≠ q) ∨ (h q.1 (hex q.1 q.2) = p.1 ∧ p ≠ q)
  symm := by intro p q hpq; tauto
  loopless := by intro p hp; rcases hp with ⟨_, hne⟩ | ⟨_, hne⟩ <;> exact hne rfl

/-! ## The statements -/

/-- **Melfi's theorem (1996), the prerequisite.**

Verbatim (entry comment): "By a result of Melfi, each positive even number can
be written as the sum of two practical numbers."

Stated here because without it `h` is a partial function and the whole card is
ill-formed.  It is a *theorem*, not a conjecture, so it is a legitimate
full-proof target.  (It also appears in `A005153Switkay.lean` in this directory;
the two cards should share one proof once either lands.) -/
theorem melfi (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    ∃ q r : ℕ, q.Practical ∧ r.Practical ∧ q + r = n := by
  sorry

/-- `h` is total on practical numbers — the immediate corollary of Melfi, and
the well-definedness the header discusses. -/
theorem hStep_exists (p : ℕ) (hp : p.Practical) : ∃ q, HStep p q := by
  sorry

/-- **Sun's conjecture (A222603, Zhi-Wei Sun, Feb 26 2013).**

Verbatim: "Conjecture: The graph H constructed above is connected and hence it is
a tree."

Note the entry's own "Clearly H contains no cycle" — acyclicity is claimed as
obvious (each vertex has exactly one outgoing `h`-edge, and `h p > p`, so no
cycle can close).  Only **connectivity** is conjectural, and the "hence it is a
tree" is a consequence.  The card separates the two accordingly.

**Mathlib primitives available.**  `SimpleGraph.Connected`,
`SimpleGraph.Preconnected`, `SimpleGraph.IsAcyclic`, `SimpleGraph.IsTree`,
`SimpleGraph.Reachable`, `SimpleGraph.Walk`; `SimpleGraph.isTree_iff`,
`SimpleGraph.IsTree.card_edgeFinset` (finite only).  The graph here is
**infinite**, so the finite tree lemmas do not apply — that is the main
formalization friction.

**Sketch of an attack.**  Connectivity of `H` means: for any two practical
`p, p'`, iterating `h` from each eventually meets.  Since `h` is strictly
increasing (`h p > p`), the `h`-orbit of each `p` is an increasing sequence of
practicals; connectivity is then "all `h`-orbits eventually coincide", i.e. the
functional graph of `h` on the practicals has a single "end".  Concretely one
would want: for every practical `p` there is `k` with `h^k(p) = h^m(1)` for some
`m`, i.e. the orbit of `1` (which is the A222603 sequence itself) absorbs every
orbit.  **That is the sharpest reformulation and is what a card should state**;
`sun_a222603_orbit_absorbs` below does.

No progress is known.  It requires quantitative control of gaps between
practical numbers, which is exactly what Weingartner's density results do *not*
give at the resolution needed.

**Tactic families.**  `SimpleGraph.Reachable` and `Walk` constructors;
`Nat.find_spec` / `Nat.find_min'` for `h`; `decide`/`native_decide` for the
bounded connectivity check; `Nat.strong_induction_on` for orbit arguments.

**Related work in this repo.** `Enumerative.Practical`,
`Enumerative.StewartCriterion`.  Adjacent Sun practical-number cards in this
directory: `A005153Switkay.lean`, `A209312SymmetricPractical.lean`,
`A005153SunRootDecreasing.lean`, `A373686SomuTran.lean`. -/
theorem sun_a222603_isTree (hex : ∀ p : ℕ, p.Practical → ∃ q, HStep p q) :
    (successorGraph hex).IsTree := by
  sorry

/-- Acyclicity alone — the entry's "Clearly H contains no cycle", hence
**provable**, and the half of `IsTree` that is not conjectural. -/
theorem successorGraph_isAcyclic (hex : ∀ p : ℕ, p.Practical → ∃ q, HStep p q) :
    (successorGraph hex).IsAcyclic := by
  sorry

/-- `HStep` carries practicality of the successor — the projection that makes
`hSub` below well typed. -/
theorem HStep.practical {p q : ℕ} (hpq : HStep p q) : q.Practical := hpq.1

/-- `h` as an endofunction **on the subtype of practical numbers**.

Iterating `h` on bare `ℕ` would require a practicality proof at every step;
an earlier draft smuggled one in as `(by sorry)` *inside the statement* of the
orbit theorem, which would have made that statement carry a `sorry` even once
proved.  (Caught by the adversarial reviewer.)  Working on the subtype removes
the problem entirely. -/
def hSub (hex : ∀ p : ℕ, p.Practical → ∃ q, HStep p q)
    (p : {p : ℕ // p.Practical}) : {p : ℕ // p.Practical} :=
  ⟨h p.1 (hex p.1 p.2), HStep.practical (Nat.find_spec (hex p.1 p.2))⟩

/-- The orbit reformulation: every practical number's `h`-orbit meets the orbit
of `1` (which is the A222603 sequence).  This is equivalent to connectivity and
is the form a proof would actually establish. -/
theorem sun_a222603_orbit_absorbs (hex : ∀ p : ℕ, p.Practical → ∃ q, HStep p q)
    (p : {p : ℕ // p.Practical}) :
    ∃ k m : ℕ, (hSub hex)^[k] p = (hSub hex)^[m] ⟨1, Nat.practical_one⟩ := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: `h` is strictly increasing — the fact that makes acyclicity
-- "clear", per the entry.
theorem lt_h (p : ℕ) (hp : ∃ q, HStep p q) : p < h p hp := by
  sorry

-- PROVABLE: the DATA head, via `HStep` witnesses.
--   a(2) = 2:  p = 1, 2(1+1) = 4, q = 2, 4 − 2 = 2 practical.
--   a(3) = 4:  p = 2, 2(2+1) = 6, q = 4, 6 − 4 = 2 practical.
--   a(4) = 6:  p = 4, 2(4+1) = 10, q = 6, 10 − 6 = 4 practical.
--   a(5) = 8:  p = 6, 2(6+1) = 14, q = 8, 14 − 8 = 6 practical.
example : HStep 1 2 := by decide
example : HStep 2 4 := by decide
example : HStep 4 6 := by decide
example : HStep 6 8 := by decide

-- PROVABLE: minimality at the first steps — no smaller `q` works, so the DATA
-- really records the *least* witness.
example : ∀ q ∈ Finset.range 4, ¬ HStep 2 q := by decide
example : ∀ q ∈ Finset.range 6, ¬ HStep 4 q := by decide

-- PROVABLE: `HStep p q` forces `q` practical and `p < q`, so `successorGraph`
-- really has practical endpoints.  Guards against a degenerate graph.
example : ¬ HStep 4 3 := by decide   -- 3 is not practical
example : ¬ HStep 4 4 := by decide   -- q must exceed p

-- PROVABLE (window check): the A222603 sequence, generated by iterating `h`
-- from `1`, reproduces the DATA head `1, 2, 4, 6, 8, 12, 18, 20, 24, 30`.
-- Needs a computable mirror of `h` that does not carry the existence proof;
-- the natural one is a bounded search `q ∈ Finset.Ioc p (2*(p+1))`, which is
-- total because the range is finite.
def hRec (p : ℕ) : ℕ := ((Finset.Ioc p (2 * (p + 1))).filter (HStep p)).min.getD 0

example : List.map (fun k => hRec^[k] 1) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    = [1, 2, 4, 6, 8, 12, 18, 20, 24, 30] := by native_decide

-- PROVABLE (bounded connectivity): every practical `p ≤ 2000` reaches the orbit
-- of `1` under `hRec`.  This is the candidates document's proposed sanity layer
-- ("connectivity of the restriction to practicals ≤ 10^4"), at a size the
-- evaluator can finish; raise after timing.
example : ∀ p ∈ Finset.Icc 1 2000, p.Practical →
    ∃ k ∈ Finset.range 20, ∃ m ∈ Finset.range 40, hRec^[k] p = hRec^[m] 1 := by
  native_decide

/-! ## Notes for a follow-up card

Order of attack:

1. `hRec` and its agreement with `h` — the computable mirror.  Note `hRec` uses
   `Finset.min.getD 0`, which *is* a junk default; the honest version proves
   the filter nonempty first.  Gating item for every ground check.
2. `lt_h` — free, and the reason acyclicity is "clear".
3. `successorGraph_isAcyclic` — provable from `lt_h`, modulo the friction of
   `SimpleGraph.IsAcyclic` on an infinite graph.
4. `melfi` / `hStep_exists` — Melfi's theorem is a *proved* result; formalizing
   it is real work but it is the prerequisite for the graph existing at all, and
   it is shared with `A005153Switkay.lean`.
5. `sun_a222603_isTree` — open.

Reference: Melfi, *On two conjectures about practical numbers*, J. Number Theory
56 (1996) 205–210. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A222603 plus a from-scratch python recomputation,
2026-08-05.

Confirmed:
* NAME, TERMS, all three COMMENTS, `%O 1,2` verbatim.
* **`%A A222603 _Zhi-Wei Sun_, Feb 26 2013`** — the candidates document's guess
  ("uncredited; likely Zhi-Wei Sun") is confirmed by the raw pull.
* **The well-definedness argument is sound**: Melfi gives practical `q + r =
  2(p+1)`; `max(q,r) ≥ p+1 > p` and `2(p+1) − max(q,r) = min(q,r)` is practical,
  so a valid successor exists and "least" is well defined by well-ordering.
* The sequence recomputes to `1, 2, 4, 6, 8, 12, 18, 20, 24, 30`, matching the
  DATA head; the `a(2..5)` spot-checks are correct.
* `successorGraph`'s `symm` (`tauto` on a symmetric disjunction) and `loopless`
  (`hne rfl` in both branches) proofs go through.
* `HStep`'s bound `q ≤ 2(p+1)` excludes no valid `q` (the remainder must be a
  practical number, hence `≥ 1`, so in fact `q ≤ 2p+1`) and prevents `ℕ`
  truncation.
* `Finset.min` returns `WithTop ℕ = Option ℕ`, so `.getD 0` is well typed.
* `SimpleGraph.IsTree` exists as `structure IsTree extends Connected` with an
  `isAcyclic` field, matching the card's usage.

One defect, **FIXED**:
1. `sun_a222603_orbit_absorbs` contained `(by sorry)` **inside the statement**
   (as the practicality proof fed to `hex` at each iteration step).  That would
   have made the statement carry a `sorry` even once proved, rendering it
   unusable as a dependency — and it silently iterated `h` on arbitrary naturals
   rather than on practicals.  Replaced with `HStep.practical` plus `hSub`, an
   endofunction on the subtype `{p // p.Practical}`, so the statement is now
   `sorry`-free.

Note (acknowledged in the file's own follow-up section): `hRec` uses
`Finset.min.getD 0`, a junk default.  It appears only in the sanity layer, never
in a theorem statement.
-/

end Candidates.A222603
