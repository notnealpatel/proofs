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

## Literature convention check

The independent literature audit read the later primary research works
Fredricksen–Sweet, *Electronic Journal of Combinatorics* 7 (2000), #R32,
pp. 1–2, and Heule, https://arxiv.org/abs/1711.08076, Introduction and
“Schur Numbers and Variants”.  These support the convention allowing `x = y`,
the greatest values `1, 4, 13` (with the first three-color obstruction at `14`),
and Schur finiteness.  Fredricksen–Sweet p. 2 and Heule report the
computer-assisted determination of the fourth value.  Heule's 2017 preprint
(AAAI 2018) establishes the fifth value `160` with a certificate exceeding
2 PB checked by a formally verified checker.

The original Schur (1916) paper was not independently checked in this audit;
the full Golomb–Baumert (1965) PDF was blocked by HTTP 403.  Historical
attributions here rely on the later works, not an independent reading of
those originals.

## Status

* `a(1) = 1`, `a(2) = 4`, `a(3) = 13`, and finiteness for positive color counts
  are formally proved in production and reused here.
* `a(4) = 44`: a computer-assisted result as reported by Fredricksen–Sweet
  p. 2 and Heule; `schur_four` remains admitted here.
* `a(5) = 160`: Heule, arXiv:1711.08076 (2017 preprint, AAAI 2018), with a
  certificate exceeding 2 PB checked by a formally verified checker.  That
  certificate is not imported here; `schur_five` remains admitted.
* `schur_six_lower` and `schur_seven_lower` also remain admitted: four
  admissions in total.  Exact values from `a(6)` onward remain open in the
  cited sources.

## Current formalization and remaining work

Production proofs supply the first three exact values and finiteness.  The
remaining lower-bound work is to obtain and transcribe witness colorings and
check that they partition the intended intervals into sum-free classes.
The fourth and fifth upper bounds still need formal proofs or checked
certificate bridges.  No such witnesses or certificates for the four
remaining admissions are supplied by this archive; their absence here is
not a claim of impossibility.
-/
import Combinatorics.SchurResults

set_option autoImplicit false

namespace Candidates.A045652

open SchurNumbers

/-! ## Definition layer

The predicates `SumFree`, `colorClass`, and `SchurColorable` are defined in
`Combinatorics.SchurNumbers` and reused here through `Combinatorics.SchurResults`.
`SumFree` excludes solutions with `x = y` as well as those with distinct
summands.  The production module `Combinatorics.SchurFinite` derives a uniform
monochromatic-sum bound from Mathlib's Hindman theorem and Rado selection;
`Combinatorics.SchurResults` connects that bound to sum-free colorings.
These are the actual dependencies, not an exhaustive claim about which
Schur-related definitions or results Mathlib contains.

`Fin n` is used for the color palette rather than an arbitrary `Fintype` with
`card = n`, because the statements are about a *specific* `n` and `Fin n` keeps
`decide` in reach. -/


/-! ## The statements -/

/-- **`a(1) = 1`.**  `{1}` is sum-free; `{1, 2}` is not (`1 + 1 = 2`).
Fully provable — this is the smallest case and it is the one that pins the
`x = y`-allowed convention. -/
theorem schur_one : IsGreatest {m : ℕ | SchurColorable 1 m} 1 :=
  SchurNumbers.schur_one

/-- **`a(2) = 4`.**  Witness: color `{1, 4}` red and `{2, 3}` blue.
`{1,4}`: `1+1=2 ∉`, `1+4=5 ∉`, `4+4=8 ∉`.  `{2,3}`: `2+2=4 ∉`, `2+3=5 ∉`,
`3+3=6 ∉`.  Upper bound: `decide` over `2^5 = 32` colorings of `{1,…,5}`.
Fully provable. -/
theorem schur_two : IsGreatest {m : ℕ | SchurColorable 2 m} 4 :=
  SchurNumbers.schur_two

/-- **`a(3) = 13`.**  Witness (classical):
`{1, 4, 10, 13}`, `{2, 3, 11, 12}`, `{5, 6, 7, 8, 9}`.
Upper bound: the production `SchurThreeCertificate` checks a pruned search
with kernel `decide`, and `SchurResults` connects it to sum-free classes. -/
theorem schur_three : IsGreatest {m : ℕ | SchurColorable 3 m} 13 :=
  SchurNumbers.schur_three

/-- **`a(4) = 44`.**  A computer-assisted result as reported by
Fredricksen–Sweet, EJC 7 (2000), #R32, p. 2, and Heule, arXiv:1711.08076.
This statement remains admitted here; neither a witness coloring nor an
upper-bound proof or certificate is supplied by this archive. -/
theorem schur_four : IsGreatest {m : ℕ | SchurColorable 4 m} 44 := by
  sorry

/-- **`a(5) = 160`.**  Heule, arXiv:1711.08076 (2017 preprint, AAAI 2018),
establishes this value by SAT with a certificate exceeding 2 PB checked by a
formally verified checker.  The certificate is not imported here, and this
statement remains admitted.  A formal lower bound also requires a checked
witness coloring, not supplied by this archive. -/
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

/-- **Schur's theorem (historically attributed to Schur, 1916): `a(n)` is finite.**
The production proof is a modern derivation using a uniform monochromatic-sum
bound obtained from Mathlib's Hindman theorem and Rado selection, then ruling
out every sum-free coloring on an interval reaching that bound.  It is not a
formalization of Schur's original proof, which was not read in this audit. -/
theorem schur_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | SchurColorable n m}.Finite :=
  SchurNumbers.schur_finite n hn

/-! ## Sanity layer -/


-- PROVABLE: the convention pin.  `{1, 2}` is NOT sum-free because `1 + 1 = 2`.
-- Under the "weak" (`x ≠ y`) reading it *would* be, and the sequence would be
-- weak Schur numbers (A118771, in its first-obstruction convention) instead.
-- The corresponding greatest values begin 2, 8, 23, 66; the cited fifth
-- value 196 is only a lower bound, not an asserted exact value.
-- This single check separates the two sequences.
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
example : SchurColorable 3 13 := schur_three_lower

-- PROVABLE: `SumFree ∅`. For positive n, `SchurColorable n 0` also holds;
-- zero colors are impossible because the coloring is a total function.
example : SumFree (∅ : Finset ℕ) := by decide

/-! ## Notes for a follow-up card

Realistic scope, in order:

1. `SumFree.subset`, `SchurColorable.mono`, `schur_one`, `schur_two`,
   `schur_three`, and `schur_finite` are now proved in production.
2. `schur_four` / `schur_five` lower bounds — witness checks, provable once the
   colorings are transcribed.
3. `schur_four`/`schur_five` upper bounds and `a(6)`, `a(7)` remain archived. -/

/-!
## Historical archive note: adversarial review verdict — **PASS-WITH-NOTES**

The following records the earlier OEIS/computational review, not evidence of
the current primary-source literature audit described above.

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
* For positive `n`, `SchurColorable n 0` is true, so `IsGreatest` is not
  greatest-of-empty. For `n = 0`, the total coloring function is impossible.
* The `a(n) < R_n(3)` Ramsey sketch is correct.

One defect, **FIXED**:
1. The weak (`x ≠ y`) Schur numbers were cited as **A005346**.  A005346 is
   van der Waerden `W(2,n) = 1, 3, 9, 35, 178, 1132` — unrelated.  The correct
   entry is **A118771** (version 1: `3, 9, 24, 67`, hence version-2 values
   `2, 8, 23, 66`, with only `a(5) ≥ 197` known).  Header corrected.
-/

end Candidates.A045652
