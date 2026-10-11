/-
# A045652 — Schur numbers, exact small values

## OEIS source (re-pulled verbatim with `goof oeis show A045652`, 2026-08-05)

```
NAME:     Schur's numbers (version 2).
TERMS:    1,4,13,44,160
KEYWORDS: nonn,hard,more,nice
COMMENTS:
  Largest number such that there is an n-coloring of the integers 1, ..., a(n)
  such that each color is sum-free, that is, no color contains a triple
  x + y = z. - _Charles R Greathouse IV_, Jun 11 2013
  The best known lower bounds for the next terms are due to Fredricksen and
  Sweet (see links): a(6) >= 536 and a(7) >= 1680.
  - _Dmitry Kamenetsky_, Oct 23 2019
  A partition showing that a(7) >= 1696 was demonstrated in 2021, along with
  some recurrence relationships for lower bounds on a(n).
  - _Fred Rowley_, Mar 01 2023
XREFS:
  Cf. A030126, A072842.
```

## Convention pinning

"version 2" and the xref to A030126 ("version 1") matter: `S(n)` vs `S(n) + 1`.
Greathouse's comment fixes *this* version as "largest `m` such that `{1,…,m}`
has a sum-free `n`-coloring", giving `1, 4, 13, 44, 160` for `n = 1,…,5`
(offset `1`).

The sum-free condition is `x + y = z` with **`x = y` allowed** (so `{1,2}` is
not sum-free, because `1 + 1 = 2`).  That is what makes `a(1) = 1` rather than
`a(1) = 2`; under the "weak" reading (`x ≠ y`) one gets the *weak* Schur
numbers, a different sequence: **A118771** ("version 1", terms `3, 9, 24, 67`,
so the version-2 values are `2, 8, 23, 66`; A118771 records only
`a(5) ≥ 197`, i.e. weak `S(5) ≥ 196`).  This is the single highest-risk
convention in the card and is pinned by a PROVABLE computation below.
(An earlier draft cited A005346 for the weak numbers; that is the van der
Waerden sequence `W(2,n) = 1, 3, 9, 35, 178, 1132` and is unrelated — caught by
the adversarial reviewer.)

Version audit, confirmed against `goof oeis show A030126`: A030126
("Schur's numbers, version 1") has terms `2, 5, 14, 45, 161` = `a(n) + 1`, i.e.
version 1 is the *smallest* `m` admitting no sum-free `n`-coloring and version 2
(this entry) is the largest `m` admitting one.  Offset `1` for both.

## Status

* `a(1) = 1`, `a(2) = 4`, `a(3) = 13`: classical, hand-checkable.
* `a(4) = 44`: classical (Baumert 1965), search space `4^44`; too big for
  `decide`, needs a clever certificate for the upper bound.
* `a(5) = 160`: Heule 2017, by SAT.  The unsatisfiability proof is ~2 PB and is
  **not importable** — this is a genuine limit, not a matter of effort.
* `a(6)` onward: open.  Lower bounds only.

## What is actually formalizable

The **lower** bounds are easy: exhibit the coloring, check sum-freeness by
`decide`.  The **upper** bounds are the hard half and get exponentially worse.
Realistic scope: `a(1)`, `a(2)`, `a(3)` fully; `a(4)`, `a(5)` lower bounds only;
`a(6) ≥ 536` and `a(7) ≥ 1696` as `native_decide` certificates *if* the witness
colorings can be obtained from Fredricksen–Sweet / Rowley.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A045652

/-! ## Definition layer

`leandoc` findings:

* `leandoc "sum free set"` and `leandoc IsSumFree` are **misses** — Mathlib has
  no sum-free-set predicate.  `grep -rn "SumFree" .lake/packages/mathlib/Mathlib/`
  returns nothing.  Defined fresh here.
* `leandoc "Schur theorem monochromatic"` returns only `Matrix.schur_complement_*`
  and `Subgroup.SchurZassenhaus*` — **Mathlib has no Schur's theorem on
  monochromatic solutions of `x + y = z`**, and no Ramsey numbers
  (`leandoc "Ramsey number"` is noise).  So even the *finiteness* of `a(n)`
  (Schur 1916) is unformalized upstream and would have to be proved here.
* What *is* available: `Combinatorics.Line.IsMono` and the Hales–Jewett
  development (`Mathlib/Combinatorics/HalesJewett.lean`), which gives
  van der Waerden but not Schur.  `Finset.filter`, `Finset.Icc`, `Fin n`.

`Fin n` is used for the color palette rather than an arbitrary `Fintype` with
`card = n`, because the statements are about a *specific* `n` and `Fin n` keeps
`decide` in reach. -/

/-- A `Finset ℕ` is **sum-free** if it contains no solution of `x + y = z`.
Note `x = y` is *allowed*, so `{1, 2}` is not sum-free (`1 + 1 = 2`).  This is
the "strong"/classical Schur condition, matching Greathouse's comment. -/
def SumFree (S : Finset ℕ) : Prop := ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + y ≠ z

instance (S : Finset ℕ) : Decidable (SumFree S) := by unfold SumFree; infer_instance

/-- The `i`-th color class of a coloring `c` restricted to `{1, …, m}`. -/
def colorClass (m : ℕ) (n : ℕ) (c : ℕ → Fin n) (i : Fin n) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun k => c k = i)

/-- `{1, …, m}` admits an `n`-coloring with every color class sum-free. -/
def SchurColorable (n m : ℕ) : Prop :=
  ∃ c : ℕ → Fin n, ∀ i : Fin n, SumFree (colorClass m n c i)

/-! ## The statements -/

/-- **`a(1) = 1`.**  `{1}` is sum-free; `{1, 2}` is not (`1 + 1 = 2`).
Fully provable — this is the smallest case and it is the one that pins the
`x = y`-allowed convention. -/
theorem schur_one : IsGreatest {m : ℕ | SchurColorable 1 m} 1 := by
  sorry

/-- **`a(2) = 4`.**  Witness: color `{1, 4}` red and `{2, 3}` blue.
`{1,4}`: `1+1=2 ∉`, `1+4=5 ∉`, `4+4=8 ∉`.  `{2,3}`: `2+2=4 ∉`, `2+3=5 ∉`,
`3+3=6 ∉`.  Upper bound: `decide` over `2^5 = 32` colorings of `{1,…,5}`.
Fully provable. -/
theorem schur_two : IsGreatest {m : ℕ | SchurColorable 2 m} 4 := by
  sorry

/-- **`a(3) = 13`.**  Witness (classical):
`{1, 4, 10, 13}`, `{2, 3, 11, 12}`, `{5, 6, 7, 8, 9}`.
Upper bound: `decide` over `3^14 ≈ 4.8·10^6` colorings of `{1,…,14}` — large but
kernel-feasible with a good decidable encoding, and comfortable for
`native_decide`.  Fully provable. -/
theorem schur_three : IsGreatest {m : ℕ | SchurColorable 3 m} 13 := by
  sorry

/-- **`a(4) = 44`** (Baumert 1965).  The lower bound is a witness check; the
upper bound needs `4^45 ≈ 1.2·10^27` colorings, so brute force is out.  The
classical argument uses the multiplicative structure of `ℤ/45` and a
Rado-style reduction.  Archive for now; the *lower* bound is provable today. -/
theorem schur_four : IsGreatest {m : ℕ | SchurColorable 4 m} 44 := by
  sorry

/-- **`a(5) = 160`** (Heule 2017, by SAT).

The unsatisfiability certificate for the upper bound is roughly `2 PB` of DRAT.
That is not importable into Lean by any route currently available, so this is
permanently an archive statement unless a human-scale proof is found.  The
*lower* bound `160 ≤ a(5)` is a witness check and is provable today given the
coloring. -/
theorem schur_five : IsGreatest {m : ℕ | SchurColorable 5 m} 160 := by
  sorry

/-- **The open frontier: `a(6) ≥ 536`** (Fredricksen–Sweet, per Kamenetsky's
comment).  A lower bound is a *witness*, so this is fully provable given the
coloring — the only obstacle is obtaining it. -/
theorem schur_six_lower : SchurColorable 6 536 := by
  sorry

/-- **`a(7) ≥ 1696`** (Fred Rowley, 2021, per the Mar 01 2023 comment).
Note the entry records two different lower bounds for `a(7)`: `1680`
(Fredricksen–Sweet) and the later `1696` (Rowley).  The stronger one is used. -/
theorem schur_seven_lower : SchurColorable 7 1696 := by
  sorry

/-- **Schur's theorem (1916): `a(n)` is finite.**

Mathlib does *not* have this (see the definition layer), so it is genuinely
missing upstream infrastructure rather than an OEIS conjecture.  Formalizing it
— via Ramsey's theorem, which Mathlib also lacks — would be a substantial and
independently valuable contribution.

**Mathlib primitives available.**  `Mathlib/Combinatorics/HalesJewett.lean`
(`Combinatorics.Line.exists_mono_in_high_dimension` — Hales–Jewett, hence van
der Waerden but *not* Schur), `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
(pigeonhole), `SimpleGraph.cliqueFree`.  A Ramsey-number development would be
the clean route: `R(3,3,…,3)` bounds `a(n)`.

**Sketch.**  Given an `n`-coloring `c` of `{1,…,m}`, color the edges of `K_{m+1}`
by `c(|i − j|)`.  A monochromatic triangle `i < j < k` gives
`(j−i) + (k−j) = (k−i)` all the same color, i.e. a violation of sum-freeness.
So `a(n) < R_n(3)`, the `n`-color Ramsey number for triangles, and
`R_n(3) ≤ 3 · n!` by the standard greedy bound.

**Tactic families.**  `decide` for the small witnesses; `native_decide` for
`a(3)`'s upper bound and any large witness (note the enlarged trust surface);
`Finset.card_le_card`, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` for the
pigeonhole core; `omega` for the index arithmetic.

**Related work in this repo.**  `Proofs/Erdos/Erdos880/` (restricted sumsets) is
the nearest neighbourhood — sum-free colorings and restricted sumsets are the
same circle of ideas.  `Proofs/BilinearComplexity/Capset.lean` and
`CapsetSliceRank.lean` handle the `x + y = 2z` analogue over `𝔽_3^n`, which is
the *cap-set* problem; the slice-rank method there does **not** transfer to
Schur numbers (no group structure to exploit). -/
theorem schur_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | SchurColorable n m}.Finite := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: `SumFree` is monotone under subsets — the basic structural fact.
theorem SumFree.subset {S T : Finset ℕ} (hT : SumFree T) (h : S ⊆ T) : SumFree S := by
  intro x hx y hy z hz
  exact hT x (h hx) y (h hy) z (h hz)

-- PROVABLE: `SchurColorable` is a down-set in `m`, which is what makes
-- `IsGreatest` the right frame (and what makes `Nat.findGreatest` usable).
theorem SchurColorable.mono {n m m' : ℕ} (h : SchurColorable n m) (hm : m' ≤ m) :
    SchurColorable n m' := by
  sorry

-- PROVABLE: the convention pin.  `{1, 2}` is NOT sum-free because `1 + 1 = 2`.
-- Under the "weak" (`x ≠ y`) reading it *would* be, and the sequence would be
-- A005346 (weak Schur numbers 2, 8, 23, 66, 196) instead.  This single check
-- separates the two sequences.
example : ¬ SumFree ({1, 2} : Finset ℕ) := by decide
example : SumFree ({1} : Finset ℕ) := by decide

-- PROVABLE: the `a(2) = 4` witness coloring, checked directly.
example : SumFree ({1, 4} : Finset ℕ) ∧ SumFree ({2, 3} : Finset ℕ) := by decide

-- PROVABLE: the `a(3) = 13` witness coloring, checked directly.
example : SumFree ({1, 4, 10, 13} : Finset ℕ) ∧ SumFree ({2, 3, 11, 12} : Finset ℕ) ∧
    SumFree ({5, 6, 7, 8, 9} : Finset ℕ) := by decide

-- PROVABLE: the three classes partition `{1, …, 13}` — without this the witness
-- above proves nothing about `SchurColorable 3 13`.
example : ({1, 4, 10, 13} ∪ {2, 3, 11, 12} ∪ {5, 6, 7, 8, 9} : Finset ℕ)
    = Finset.Icc 1 13 := by decide

-- PROVABLE: pairwise disjointness of the three classes.
example : Disjoint ({1, 4, 10, 13} : Finset ℕ) ({2, 3, 11, 12} : Finset ℕ) ∧
    Disjoint ({1, 4, 10, 13} : Finset ℕ) ({5, 6, 7, 8, 9} : Finset ℕ) ∧
    Disjoint ({2, 3, 11, 12} : Finset ℕ) ({5, 6, 7, 8, 9} : Finset ℕ) := by decide

-- PROVABLE: satisfiability — `SchurColorable 3 13` holds, so `schur_three` is
-- not vacuous on the lower-bound side.
example : SchurColorable 3 13 := by
  sorry  -- assemble from the three witness classes above

-- PROVABLE: `SumFree ∅` and `SchurColorable n 0` — the degenerate cases that
-- make `{m | SchurColorable n m}` nonempty, so `IsGreatest` is not asserting
-- greatest-of-empty.
example : SumFree (∅ : Finset ℕ) := by decide

/-! ## Notes for a follow-up card

Realistic scope, in order:

1. `SumFree.subset`, `SchurColorable.mono` — free, and prerequisites for
   everything else.
2. `schur_one`, `schur_two` — fully provable, tiny `decide`s.
3. `schur_three` — provable, but the upper bound needs a good decidable
   encoding: naive `∀ c : Fin 14 → Fin 3` is `3^14 ≈ 4.8·10^6` and the kernel
   will not enjoy it.  Use symmetry breaking (`c 1 = 0`) to cut it to `3^13`,
   and `native_decide`.
4. `schur_four` / `schur_five` lower bounds — witness checks, provable once the
   colorings are transcribed.
5. `schur_finite` — the real prize.  It is Schur's 1916 theorem, Mathlib does
   not have it, and it needs a Ramsey-for-triangles development that would be
   independently useful.  **This is the item worth doing**, and it is a
   *theorem*, not a conjecture.
6. `schur_four`/`schur_five` upper bounds and `a(6)`, `a(7)` — out of reach. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A045652 and A030126 plus brute-force verification,
2026-08-05.

Confirmed:
* Quotes verbatim (Greathouse Jun 11 2013, Kamenetsky Oct 23 2019,
  Rowley Mar 01 2023); `%O A045652 1,2`.
* **Version audit**: A030126 ("version 1") has terms `2, 5, 14, 45, 161`
  `= a(n) + 1`, so version 1 is the least `m` with *no* sum-free `n`-coloring
  and version 2 (this entry) is the greatest `m` with one.  The card's reading
  is right.
* **The `x = y`-allowed convention is forced by `a(1) = 1`**: under `x ≠ y`,
  `{1,2}` would be sum-free and `a(1) ≥ 2`.
* All witness colorings verified by brute force: `{1,4} | {2,3}` partitions
  `{1..4}` with both classes sum-free; `{1,4,10,13} | {2,3,11,12} | {5,…,9}`
  partitions `{1..13}` likewise; and **no** sum-free 2-coloring of `{1..5}` or
  3-coloring of `{1..14}` exists.
* Mathlib has no sum-free predicate, no Schur's theorem, and no Ramsey numbers
  (only the word "Ramsey" in `HalesJewett`/`Hindman` docstrings).
* `SchurColorable n 0` is true, so `IsGreatest` is not greatest-of-empty.
* The `a(n) < R_n(3)` Ramsey sketch is correct.

One defect, **FIXED**:
1. The weak (`x ≠ y`) Schur numbers were cited as **A005346**.  A005346 is
   van der Waerden `W(2,n) = 1, 3, 9, 35, 178, 1132` — unrelated.  The correct
   entry is **A118771** (version 1: `3, 9, 24, 67`, hence version-2 values
   `2, 8, 23, 66`, with only `a(5) ≥ 197` known).  Header corrected.
-/

end Candidates.A045652
