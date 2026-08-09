import Mathlib

/-!
# A273929: squarefree `n ≡ 5, 6, 7 (mod 8)` are primitive congruent numbers, on BSD

## Source, pinned verbatim

Re-pulled with `goof oeis show A273929` on **2026-08-05**.

`id` (verbatim): `A273929`

`name` (verbatim):

> Numbers that are congruent to {5, 6, 7} mod 8 and are squarefree.

`keywords` (verbatim): `nonn`

`xrefs` (verbatim): `Cf. A005117, A006991, A047574, A062695, A104141.`

`terms` (verbatim, the whole field; line-wrapped here only, the field itself is one line):

> 5,6,7,13,14,15,21,22,23,29,30,31,37,38,39,46,47,53,55,61,62,69,70,71,77,78,79,85,86,
> 87,93,94,95,101,102,103,109,110,111,118,119,127,133,134,141,142,143,149,151,157,158,
> 159,165,166,167,173,174

The archived claim (verbatim, the whole line, the first of the two `comments`):

> It has been shown, conditional on the Birch Swinnerton-Dyer conjecture, that this
> sequence is a subset of the primitive congruent numbers (A006991). The union of this
> sequence with A062695 gives A006991. Also this sequence is the intersection of A047574
> and A005117.

The second comment (verbatim, not formalised here — it is an analytic density claim):

> The asymptotic density of this sequence is 3/Pi^2 (A104141). - _Amiram Eldar_,
> Mar 09 2021

### The cross-referenced entries, pinned verbatim

`goof oeis show A003273`, `name`:

> Congruent numbers: positive integers k for which there exists a right triangle having
> area k and rational sides.

`goof oeis show A006991`, `name` and the first `comments` entry:

> Primitive congruent numbers.

> Squarefree terms of A003273.

`goof oeis show A006991`, the head of the second Mathematica block of the `programs` field
(entry index `3` of `4`) — the entry's own code for deciding membership, which
short-circuits exactly the residue classes archived here:

> CongruentQ[n_] := Module[{x, y, z, ok=False}, (Which[! SquareFreeQ[n], Null[],
> MemberQ[{5, 6, 7}, Mod[n, 8]], ok = True, OddQ@n&&Length@Solve[x^2+2y^2+8z^2==n,
> {x, y, z}, Integers]==2Length@Solve[x^2+2y^2+32z^2==n, {x, y, z}, Integers], ok=True,
> …

preceded by the line (verbatim)

> (* The following self-contained Mathematica code also assumes the truth of the Birch
> and Swinnerton-Dyer conjecture. *)

`goof oeis show A062695`, `name` and its only `comments` entry:

> Squarefree n such that the elliptic curve n*y^2 = x^3 - x arising in the "congruent
> number" problem has rank 2.

> These n are precisely the primitive congruent numbers (A006991) with n==1, n==2, or
> n==3 (mod 8). - _T. D. Noe_, Aug 02 2006

`goof oeis show A047574`, `name`: `Numbers that are congruent to {5, 6, 7} mod 8.`

`goof oeis show A005117`, `name`: `Squarefree numbers: numbers that are not divisible by
a square greater than 1.`

`goof wiki article "Congruent number"` (verbatim), the reformulation this file proves:

> Thus a positive rational number $n$ is congruent if and only if the equation
> $y^{2} = x^{3} − n^{2}x$ has a rational point with $y$ not equal to 0.

and, on the unconditional state of the art (verbatim):

> It is also known that in each of the congruence classes $5, 6, 7 (mod 8)$, for any
> given $k$ there are infinitely many square-free congruent numbers with $k$ prime
> factors.

`goof wiki article "Tunnell's theorem"` (verbatim):

> Tunnell's theorem states that supposing *n* is a congruent number, if *n* is odd then
> 2*An* = *Bn* and if *n* is even then 2*Cn* = *Dn*.  Conversely, if the Birch and
> Swinnerton-Dyer conjecture holds true for elliptic curves of the form
> $y^2 = x^3 - n^2x$, these equalities are sufficient to conclude that *n* is a congruent
> number.

## What is archived and what is proved

Archived with the single intended `sorry`:

* `a273929_subset_a006991` — every squarefree `n ≡ 5, 6, 7 (mod 8)` is a primitive
  congruent number.  This is the first sentence of the pinned comment.  **Status: open**;
  it is a theorem only conditional on the Birch and Swinnerton-Dyer conjecture for
  `y² = x³ − n²x`.

Proved here, `sorry`-free and kernel-checked:

* `isCongruentArea_iff_hasNontrivialPoint` — **the rank-free reformulation**: for
  `0 < n` a rational, `n` is the area of a rational right triangle iff `y² = x³ − n²x`
  has a rational point with `y ≠ 0`.  Both directions are the classical Fermat/Euler
  correspondence, with the sign normalisation done by the 2-torsion translation
  `(x, y) ↦ (−n²/x, n²y/x²)` rather than by a descent.
* `congruentCurve_equation_iff`, `congruentCurve_Δ`, `congruentCurve_nonsingular`,
  `hasNontrivialPoint_iff_nonsingular` — the bridge to Mathlib's `WeierstrassCurve`:
  `Eₙ = ⟨0, 0, 0, −n², 0⟩`, `Δ = 64n⁶`, and (for `n ≠ 0`) every solution of the equation is
  a nonsingular point, so it is a genuine `WeierstrassCurve.Affine.Point`.
* `a273929_subset_iff_hasNontrivialPoint` — the archived claim restated as a point
  existence statement, `sorry`-free (it is an `iff` between two open statements, proved
  from the reformulation).
* `isCongruentNumber_five` … `isCongruentNumber_fifteen` — the first six terms
  `5, 6, 7, 13, 14, 15` of the pinned `terms` field are congruent, by explicit rational
  triangles; and `curvePointSix`, `curvePointFive`, `curvePointSeven` exhibit the
  corresponding `WeierstrassCurve.Affine.Point`s.
* `isPrimitiveCongruentLow_thirtyFour/fortyOne/twoHundredNineteen` — the complementary
  piece is inhabited in each of the residues `2, 1, 3 (mod 8)`.
* `mem_or_low_of_isPrimitiveCongruent` — the **unconditional half** of the union claim:
  `A006991 ⊆ A273929 ∪ A062695`.
* `isPrimitiveCongruent_iff_of_congruent` — the union claim itself, with the missing
  inclusion carried as an explicit *pointwise* hypothesis (so the hypothesis can be, and
  is, discharged at concrete `n`).
* `mem_a273929Prefix_iff` — ground truth: below `175`, `MemA273929` holds at exactly the
  `57` values of the pinned `terms` field.
* `squarefree_iff_forall_mem_Icc`, `mem_residues_of_squarefree` — the squarefree API used
  above: a bounded kernel-checkable form, and the fact that a squarefree `n` has
  `n % 8 ∈ {1, 2, 3, 5, 6, 7}` (this is what makes the union claim a genuine partition).

## Deviations from the dispatching brief, and scope rulings

* **The USER ruling is followed**: only the rank-free point-existence reformulation is
  formalised.  There is no rank functional and no conditional Mordell–Weil layer in this
  file.  In particular `A062695` is *not* formalised at its OEIS definition ("the elliptic
  curve n*y^2 = x^3 - x … has rank 2"); the complementary piece is defined as
  `IsPrimitiveCongruentLow`, i.e. by T. D. Noe's rank-free characterisation pinned above.
  A reader who wants the rank reading must supply Noe's comment as an extra input.
* The subset claim is stated, not a characterisation.  `a273929_subset_a006991` is an
  implication; nothing in this file says or implies that A273929 exhausts A006991 — indeed
  `isPrimitiveCongruentLow_thirtyFour` exhibits a primitive congruent number outside it.
* The entry's second sentence, "The union of this sequence with A062695 gives A006991", is
  written unconditionally in the entry, but it *implies* the first sentence
  (`A273929 ⊆ A273929 ∪ A062695 = A006991`), so it carries the same BSD conditionality.
  `isPrimitiveCongruent_iff_of_congruent` therefore keeps the inclusion as a hypothesis.
* The entry's third sentence, "this sequence is the intersection of A047574 and A005117",
  is the *definition* of `MemA273929` here (`Squarefree n ∧ n % 8 ∈ {5, 6, 7}`), so it is
  true by construction and gets no separate theorem.
* `congruentCurve` duplicates `ShearEC.ShortCurveScaling.congrCurve`: that is
  `shortCurve ℚ (-(n ^ 2)) 0` with `shortCurve R a₄ a₆ = ⟨0, 0, 0, a₄, a₆⟩`, so the two are
  the same term, and `congrCurve_Δ` there is this file's `congruentCurve_Δ`.  It is
  restated rather than imported by choice, not by necessity — cross-library imports inside
  `Proofs/` do exist (`Proofs/BilinearComplexity/CapsetSliceRank.lean` imports `Erdos.…`,
  `Proofs/GroupTPP/CUCapacity.lean` imports `BilinearComplexity.…`) — so that this
  statement archive depends on Mathlib alone and cannot be invalidated by refactoring in
  the `ShearEC` development library.  The five-line duplication is the price.
* `Proofs/Enumerative.lean` is not edited by this lane; the module import line is the
  orchestrator's to add.

## Mathlib gaps this file runs into

* Mathlib has no congruent-number notion: `leandoc CongruentNumber` reports
  `mode: "miss"`, and a full-tree grep for `congruum` / `congruent number` finds nothing.
  So `IsCongruentArea` is defined here from the OEIS `name` of A003273, read literally.
* Mathlib has no Mordell–Weil rank, so the rank formulations of A062695 and of the
  congruent-number problem are not statable at all today — which is what makes the
  point-existence reformulation the only available route, independently of the ruling.
* Mathlib has **no** Fermat right-triangle theorem in any of its equivalent forms.
  `Mathlib/NumberTheory/PythagoreanTriples.lean` classifies triples and never mentions
  their area (a grep for `area` in it is empty), and there is no "1 is not congruent" and
  no rank-0 statement for `y² = x³ − x`.  The nearest result is
  `not_fermat_42 : a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2` in
  `Mathlib/NumberTheory/FLT/Four.lean`; bridging it to `¬ IsCongruentArea 1` needs the
  Pythagorean-triple descent, which is not attempted here.  Consequently this file exhibits
  **no** positive integer that is *not* congruent; the non-degeneracy checks it can give
  are `not_isCongruentArea_zero` and `not_isCongruentArea_neg_one`, which pin down that the
  predicate is supported on the positive rationals.
* `Squarefree` on `ℕ` is decidable in Mathlib but does not reduce in the kernel: `decide`
  on `Squarefree 5` fails with "reduction got stuck at the `Decidable` instance … match
  Nat.minSqFac 5", because `Nat.minSqFacAux` is well-founded (its declaration ends
  `termination_by n k => sqrt n + 2 - k`).  `squarefree_iff_forall_mem_Icc` replaces it
  with a `Finset.Icc 2 n` scan that does reduce; every squarefree fact below is
  kernel-checked through that route.  `native_decide` was not granted for this file and is
  not used.

## Computational orientation (not proofs)

`command -v sage` is empty on this machine, so no `sage` was used and none is claimed.
A plain `python3` script (`fractions.Fraction` only; no `sympy`, no external library)
regenerated the sequence `{n : n % 8 ∈ {5,6,7}, n squarefree}` up to `200` and reproduced
the pinned `terms` field byte for byte, checked `A273929 ∩ [1,159] ⊆ A006991` against the
pinned A006991 prefix, checked that the A006991 prefix is the disjoint union of its
`≡ 5,6,7` and `≡ 1,2,3` parts, and searched Pythagorean parametrisations `(m, l)` for the
explicit triangles used below.  All of that is orientation; every witness it produced is
re-verified in the kernel here.
-/

set_option autoImplicit false

namespace A273929

/-! ## The congruent-number curve as a Mathlib `WeierstrassCurve` -/

/-- The congruent-number curve `Eₙ : y² = x³ − n²x`, as the Weierstrass curve with
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, −n², 0)`.

This is the same curve as `ShearEC.ShortCurveScaling.congrCurve`; see the "Deviations"
section of the module docstring for why it is restated instead of imported. -/
def congruentCurve (n : ℚ) : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -n ^ 2, 0⟩

/-- The `a₁` coefficient of `Eₙ` is `0`. -/
@[simp] lemma congruentCurve_a₁ (n : ℚ) : (congruentCurve n).a₁ = 0 := rfl

/-- The `a₂` coefficient of `Eₙ` is `0`. -/
@[simp] lemma congruentCurve_a₂ (n : ℚ) : (congruentCurve n).a₂ = 0 := rfl

/-- The `a₃` coefficient of `Eₙ` is `0`. -/
@[simp] lemma congruentCurve_a₃ (n : ℚ) : (congruentCurve n).a₃ = 0 := rfl

/-- The `a₄` coefficient of `Eₙ` is `-n²`. -/
@[simp] lemma congruentCurve_a₄ (n : ℚ) : (congruentCurve n).a₄ = -n ^ 2 := rfl

/-- The `a₆` coefficient of `Eₙ` is `0`. -/
@[simp] lemma congruentCurve_a₆ (n : ℚ) : (congruentCurve n).a₆ = 0 := rfl

/-- Ground truth for `congruentCurve`: lying on it is exactly satisfying
`y² = x³ − n²x`. -/
lemma congruentCurve_equation_iff (n x y : ℚ) :
    (congruentCurve n).Equation x y ↔ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [congruentCurve_a₁, congruentCurve_a₂, congruentCurve_a₃, congruentCurve_a₄,
    congruentCurve_a₆]
  constructor <;> intro h <;> linarith

/-- The discriminant of `Eₙ` is `64n⁶`. -/
lemma congruentCurve_Δ (n : ℚ) : (congruentCurve n).Δ = 64 * n ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    congruentCurve_a₁, congruentCurve_a₂, congruentCurve_a₃, congruentCurve_a₄,
    congruentCurve_a₆]
  ring

/-- For `n ≠ 0` the curve is nonsingular, so every solution of `y² = x³ − n²x` is a
genuine `WeierstrassCurve.Affine.Point`. -/
lemma congruentCurve_nonsingular {n x y : ℚ} (hn : n ≠ 0)
    (h : (congruentCurve n).Equation x y) : (congruentCurve n).Nonsingular x y := by
  refine (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero ?_).1 h
  rw [congruentCurve_Δ]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hn)

/-! ## The two predicates -/

/-- `IsCongruentArea n`: the positive rational `n` is the area of a right triangle with
three positive rational sides.

This is OEIS A003273's `name` read literally — "there exists a right triangle having area
k and rational sides" — with the area written as `a * b = 2 * n` to keep division out of
the statement.  Positivity of `n` is not assumed: it is forced (`pos_of_isCongruentArea`),
since `a, b > 0`. -/
def IsCongruentArea (n : ℚ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * n

/-- `HasNontrivialPoint n`: the curve `Eₙ : y² = x³ − n²x` carries a rational point with
`y ≠ 0`.

`y = 0` forces `x³ = n²x`, i.e. `x ∈ {0, n, −n}`, so `y ≠ 0` excludes exactly the three
affine 2-torsion points `(0,0)`, `(n,0)`, `(−n,0)` (the point at infinity is absent from
the affine model to begin with).  This is the "nontrivial" of the wiki sentence "has a
rational point with y not equal to 0". -/
def HasNontrivialPoint (n : ℚ) : Prop :=
  ∃ x y : ℚ, y ≠ 0 ∧ (congruentCurve n).Equation x y

/-- The unfolded form of `HasNontrivialPoint`. -/
lemma hasNontrivialPoint_iff (n : ℚ) :
    HasNontrivialPoint n ↔ ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  simp only [HasNontrivialPoint, congruentCurve_equation_iff]

/-- For `n ≠ 0`, a nontrivial point is a **nonsingular** point, hence a genuine
`WeierstrassCurve.Affine.Point.some`.  This is the form the USER ruling asks for:
"exists a nontrivial rational point on `y² = x³ − n²·x`", statable with Mathlib's
`WeierstrassCurve` today. -/
lemma hasNontrivialPoint_iff_nonsingular {n : ℚ} (hn : n ≠ 0) :
    HasNontrivialPoint n ↔ ∃ x y : ℚ, y ≠ 0 ∧ (congruentCurve n).Nonsingular x y := by
  constructor
  · rintro ⟨x, y, hy, heq⟩
    exact ⟨x, y, hy, congruentCurve_nonsingular hn heq⟩
  · rintro ⟨x, y, hy, hns⟩
    exact ⟨x, y, hy, hns.1⟩

/-- A congruent area is positive: `a, b > 0` and `a * b = 2n`. -/
lemma pos_of_isCongruentArea {n : ℚ} (h : IsCongruentArea n) : 0 < n := by
  obtain ⟨a, b, _, ha, hb, _, _, harea⟩ := h
  nlinarith

/-- Non-degeneracy: `0` is not a congruent area. -/
theorem not_isCongruentArea_zero : ¬ IsCongruentArea 0 := fun h =>
  lt_irrefl (0 : ℚ) (pos_of_isCongruentArea h)

/-- Non-degeneracy: `-1` is not a congruent area, so `IsCongruentArea` is not everything.
(No *positive* non-example is available; see the "Mathlib gaps" section of the module
docstring.) -/
theorem not_isCongruentArea_neg_one : ¬ IsCongruentArea (-1) := fun h => by
  have hpos : (0 : ℚ) < -1 := pos_of_isCongruentArea h
  norm_num at hpos

/-! ## Forward direction: a triangle gives a point

Fermat's map, in the form pinned from the wiki article: `x = n(a+c)/b`,
`y = 2n²(a+c)/b²`.  Because `a * b = 2n`, both are division-free up to a factor of `2`:
`n/b = a/2`, so `x = a(a+c)/2` and `y = a²(a+c)/2`.  `tunnell_x_eq` and `tunnell_y_eq`
record that the two forms agree; the division-free form is what the proof uses, so the
whole direction is one `linear_combination`. -/

/-- The `x`-coordinate of Fermat's map, in the two equivalent forms. -/
lemma tunnell_x_eq {a b c n : ℚ} (hb : b ≠ 0) (harea : a * b = 2 * n) :
    n * (a + c) / b = a * (a + c) / 2 := by
  rw [div_eq_div_iff hb two_ne_zero]
  linear_combination (-(a + c)) * harea

/-- The `y`-coordinate of Fermat's map, in the two equivalent forms. -/
lemma tunnell_y_eq {a b c n : ℚ} (hb : b ≠ 0) (harea : a * b = 2 * n) :
    2 * n ^ 2 * (a + c) / b ^ 2 = a ^ 2 * (a + c) / 2 := by
  rw [div_eq_div_iff (pow_ne_zero 2 hb) two_ne_zero]
  linear_combination (-(a + c) * (a * b + 2 * n)) * harea

/-- Joint satisfiability of the hypotheses of `tunnell_x_eq`, at the `(3, 4, 5)` triangle
of area `6`: `b = 4 ≠ 0` and `a * b = 3 * 4 = 12 = 2 * 6`. -/
example : (6 : ℚ) * (3 + 5) / 4 = 3 * (3 + 5) / 2 :=
  tunnell_x_eq (by norm_num) (by norm_num)

/-- Joint satisfiability of the hypotheses of `tunnell_y_eq`, at the same triangle. -/
example : 2 * (6 : ℚ) ^ 2 * (3 + 5) / 4 ^ 2 = 3 ^ 2 * (3 + 5) / 2 :=
  tunnell_y_eq (by norm_num) (by norm_num)

/-- **A rational right triangle of area `n` gives a rational point of `Eₙ` with
`y ≠ 0`.** -/
theorem hasNontrivialPoint_of_isCongruentArea {n : ℚ} (h : IsCongruentArea n) :
    HasNontrivialPoint n := by
  obtain ⟨a, b, c, ha, hb, hc, hpyth, harea⟩ := h
  refine ⟨a * (a + c) / 2, a ^ 2 * (a + c) / 2, by positivity, ?_⟩
  rw [congruentCurve_equation_iff]
  linear_combination (a * (a + c) * a ^ 2 / 8) * hpyth
    - (a * (a + c) * (a * b + 2 * n) / 8) * harea

/-! ## Sign normalisation

`y² = x(x − n)(x + n)` with `y ≠ 0` and `0 < n` forces `x` into `(−n, 0) ∪ (n, ∞)`.  On
the second interval the inverse map already produces positive sides; the first interval is
carried to the second by translation by the 2-torsion point `(0, 0)`, which on
`y² = x³ + Ax` is `(x, y) ↦ (A/x, −Ay/x²)`, i.e. `(x, y) ↦ (−n²/x, n²y/x²)` here.  No
descent and no torsion computation is needed. -/

/-- The 2-torsion translation `(x, y) ↦ (n²/(−x), n²y/x²)` preserves the curve. -/
lemma translate_equation {n x y : ℚ} (hx : x ≠ 0) (hxy : y ^ 2 = x ^ 3 - n ^ 2 * x) :
    (n ^ 2 * y / x ^ 2) ^ 2 = (n ^ 2 / (-x)) ^ 3 - n ^ 2 * (n ^ 2 / (-x)) := by
  field_simp
  linear_combination n ^ 4 * hxy

/-- Joint satisfiability of the hypotheses of `translate_equation`, at `n = 6` and the
point `(12, 36)` of `E₆`; the translate is `(-3, 9)`, and `9² = (-3)³ - 36·(-3) = 81`. -/
example : ((6 : ℚ) ^ 2 * 36 / 12 ^ 2) ^ 2
    = ((6 : ℚ) ^ 2 / (-12)) ^ 3 - 6 ^ 2 * ((6 : ℚ) ^ 2 / (-12)) :=
  translate_equation (by norm_num) (by norm_num)

/-- **Normalisation.** A nontrivial point of `Eₙ` can be moved to one with `n < x` and
`0 < y`, which is the region where the inverse of Fermat's map has positive output. -/
theorem exists_gt_of_hasNontrivialPoint {n : ℚ} (hn : 0 < n) (h : HasNontrivialPoint n) :
    ∃ x y : ℚ, n < x ∧ 0 < y ∧ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  rw [hasNontrivialPoint_iff] at h
  obtain ⟨x, y, hy, hxy⟩ := h
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hprod : 0 < x ^ 3 - n ^ 2 * x := hxy ▸ hy2
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- `x < 0`: then `−n < x < 0`, and the translate has `n < x'`.
    have hxne : x ≠ 0 := ne_of_lt hx
    have hxn : -n < x := by
      by_contra hcon
      rw [not_lt] at hcon
      have hsign : 0 ≤ (-x) * ((-x) - n) * ((-x) + n) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith [hsign]
    refine ⟨n ^ 2 / (-x), |n ^ 2 * y / x ^ 2|, ?_, abs_pos.2 ?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]
      nlinarith
    · exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hn)) hy) (pow_ne_zero 2 hxne)
    · rw [sq_abs]
      exact translate_equation hxne hxy
  · -- `x = 0` contradicts `y ≠ 0`.
    exact absurd hprod (by rw [hx]; norm_num)
  · -- `0 < x`: then already `n < x`.
    refine ⟨x, |y|, ?_, abs_pos.2 hy, by rw [sq_abs]; exact hxy⟩
    by_contra hcon
    rw [not_lt] at hcon
    have hsign : 0 ≤ x * (n - x) * (x + n) :=
      mul_nonneg (mul_nonneg hx.le (by linarith)) (by linarith)
    nlinarith [hsign]

/-! ## Backward direction: a point gives a triangle -/

/-- **A rational point of `Eₙ` with `y ≠ 0` gives a rational right triangle of area
`n`**, for `0 < n`.  The sides are the wiki's `a = (x²−n²)/y`, `b = 2nx/y`,
`c = (x²+n²)/y`, applied to a normalised point. -/
theorem isCongruentArea_of_hasNontrivialPoint {n : ℚ} (hn : 0 < n)
    (h : HasNontrivialPoint n) : IsCongruentArea n := by
  obtain ⟨x, y, hxn, hy, hxy⟩ := exists_gt_of_hasNontrivialPoint hn h
  have hx : 0 < x := lt_trans hn hxn
  have hyne : y ≠ 0 := ne_of_gt hy
  have hsq : 0 < x ^ 2 - n ^ 2 := by nlinarith
  refine ⟨(x ^ 2 - n ^ 2) / y, 2 * n * x / y, (x ^ 2 + n ^ 2) / y, by positivity,
    by positivity, by positivity, ?_, ?_⟩
  · rw [div_pow, div_pow, div_pow, ← add_div]
    congr 1
    ring
  · rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hyne hyne)]
    linear_combination (-2 * n) * hxy

/-- **The rank-free reformulation of the congruent-number property.**

For a positive rational `n`, `n` is the area of a rational right triangle **iff**
`y² = x³ − n²x` has a rational point with `y ≠ 0`.  Pinned verbatim from the wiki
article:

> Thus a positive rational number $n$ is congruent if and only if the equation
> $y^{2} = x^{3} − n^{2}x$ has a rational point with $y$ not equal to 0.

No rank, no Mordell–Weil, no torsion computation enters: the "positive rank" phrasing of
the same fact needs the extra input that the torsion of `Eₙ(ℚ)` is exactly the three
`y = 0` points, and that input is not used and not available in Mathlib. -/
theorem isCongruentArea_iff_hasNontrivialPoint {n : ℚ} (hn : 0 < n) :
    IsCongruentArea n ↔ HasNontrivialPoint n :=
  ⟨hasNontrivialPoint_of_isCongruentArea, isCongruentArea_of_hasNontrivialPoint hn⟩

/-- Joint satisfiability of the hypothesis and both sides of
`isCongruentArea_iff_hasNontrivialPoint`, at `n = 6`: `0 < 6`, the `(3,4,5)` triangle has
area `6`, and `(12, 36)` lies on `y² = x³ − 36x`. -/
example : IsCongruentArea 6 ↔ HasNontrivialPoint 6 :=
  isCongruentArea_iff_hasNontrivialPoint (by norm_num)

/-- Joint satisfiability of the hypotheses of `exists_gt_of_hasNontrivialPoint`, at
`n = 6` with the point `(12, 36)`. -/
example : ∃ x y : ℚ, (6 : ℚ) < x ∧ 0 < y ∧ y ^ 2 = x ^ 3 - (6 : ℚ) ^ 2 * x :=
  exists_gt_of_hasNontrivialPoint (by norm_num)
    ⟨12, 36, by norm_num, (congruentCurve_equation_iff 6 12 36).2 (by norm_num)⟩

/-- Joint satisfiability of the hypotheses of `isCongruentArea_of_hasNontrivialPoint`, at
the same point. -/
example : IsCongruentArea 6 :=
  isCongruentArea_of_hasNontrivialPoint (by norm_num)
    ⟨12, 36, by norm_num, (congruentCurve_equation_iff 6 12 36).2 (by norm_num)⟩

/-- Joint satisfiability of the hypothesis of `hasNontrivialPoint_iff_nonsingular`. -/
example : HasNontrivialPoint 6 ↔ ∃ x y : ℚ, y ≠ 0 ∧ (congruentCurve 6).Nonsingular x y :=
  hasNontrivialPoint_iff_nonsingular (by norm_num)

/-! ## Squarefree, in a kernel-checkable form -/

/-- `Squarefree n` for `n ≠ 0`, as a bounded scan over `Finset.Icc 2 n`.

Mathlib's `DecidablePred Squarefree` routes through `Nat.minSqFac`, whose auxiliary
`Nat.minSqFacAux` is well-founded, so `decide` gets stuck on it; this form reduces. -/
lemma squarefree_iff_forall_mem_Icc {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ d ∈ Finset.Icc 2 n, ¬ (d * d ∣ n) := by
  constructor
  · intro hsf d hd hdvd
    have hunit := Nat.isUnit_iff.1 (hsf d hdvd)
    have hmem := Finset.mem_Icc.1 hd
    omega
  · intro h x hx
    rcases Nat.lt_or_ge x 2 with hlt | hge
    · interval_cases x
      · simp only [Nat.zero_mul, zero_dvd_iff] at hx
        exact absurd hx hn
      · exact isUnit_one
    · exfalso
      refine h x (Finset.mem_Icc.2 ⟨hge, ?_⟩) hx
      have hle : x * x ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hx
      nlinarith

/-- Ground truth for `squarefree_iff_forall_mem_Icc`, positive side. -/
theorem squarefree_six : Squarefree 6 :=
  (squarefree_iff_forall_mem_Icc (by norm_num)).2 (by decide)

/-- Ground truth for `squarefree_iff_forall_mem_Icc`, negative side: the criterion is not
vacuously true. -/
theorem not_squarefree_twelve : ¬ Squarefree 12 := by
  rw [squarefree_iff_forall_mem_Icc (by norm_num)]
  decide

/-- A squarefree number is never `≡ 0` or `≡ 4 (mod 8)`, because `4 ∣ n` would give
`2 * 2 ∣ n`.  This is what makes `{5,6,7} ⊔ {1,2,3}` a *partition* of the residues
available to a squarefree number, hence what makes the union claim of the pinned comment
a partition statement. -/
lemma mem_residues_of_squarefree {n : ℕ} (h : Squarefree n) :
    n % 8 ∈ ({1, 2, 3, 5, 6, 7} : Finset ℕ) := by
  have hzero : n % 8 ≠ 0 := by
    intro hc
    have hfour : 2 * 2 ∣ n := by omega
    have htwo : (2 : ℕ) = 1 := Nat.isUnit_iff.1 (h 2 hfour)
    omega
  have hfour : n % 8 ≠ 4 := by
    intro hc
    have hdvd : 2 * 2 ∣ n := by omega
    have htwo : (2 : ℕ) = 1 := Nat.isUnit_iff.1 (h 2 hdvd)
    omega
  have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ## The three sequences -/

/-- OEIS A003273 membership: `n` is a congruent number. -/
def IsCongruentNumber (n : ℕ) : Prop := IsCongruentArea (n : ℚ)

/-- OEIS A006991 membership: the primitive congruent numbers, i.e. (pinned verbatim)
"Squarefree terms of A003273". -/
def IsPrimitiveCongruent (n : ℕ) : Prop := Squarefree n ∧ IsCongruentNumber n

/-- OEIS A273929 membership: (pinned verbatim) "Numbers that are congruent to {5, 6, 7}
mod 8 and are squarefree" — equivalently the entry's own third comment sentence, "this
sequence is the intersection of A047574 and A005117". -/
def MemA273929 (n : ℕ) : Prop := Squarefree n ∧ n % 8 ∈ ({5, 6, 7} : Finset ℕ)

/-- The complementary piece of the pinned union claim: the primitive congruent numbers
with `n ≡ 1, 2, 3 (mod 8)`.

OEIS calls this A062695, but its OEIS *definition* is by rank ("Squarefree n such that the
elliptic curve n*y^2 = x^3 - x … has rank 2"), which this file does not formalise.  What
is used is T. D. Noe's rank-free characterisation, pinned verbatim in the module
docstring: "These n are precisely the primitive congruent numbers (A006991) with n==1,
n==2, or n==3 (mod 8)." -/
def IsPrimitiveCongruentLow (n : ℕ) : Prop :=
  IsPrimitiveCongruent n ∧ n % 8 ∈ ({1, 2, 3} : Finset ℕ)

/-- The cast bridge: `IsCongruentNumber n` is `IsCongruentArea (n : ℚ)`, and `(n : ℚ)`
may be replaced by any rational it equals.  Used to move the numeral certificates below
between `ℕ`-indexed and `ℚ`-indexed statements. -/
lemma isCongruentArea_of_isCongruentNumber {n : ℕ} {q : ℚ} (hq : (n : ℚ) = q)
    (h : IsCongruentNumber n) : IsCongruentArea q := hq ▸ h

/-- `0` is not a congruent number, so `IsCongruentNumber` carries the positivity of
A003273's "positive integers k" without a side condition. -/
theorem not_isCongruentNumber_zero : ¬ IsCongruentNumber 0 := fun h =>
  not_isCongruentArea_zero (isCongruentArea_of_isCongruentNumber (by norm_num) h)

/-- A member of A273929 is positive, as a rational. -/
lemma cast_pos_of_memA273929 {n : ℕ} (h : MemA273929 n) : 0 < (n : ℚ) := by
  obtain ⟨-, hres⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hres
  have hn : n ≠ 0 := by omega
  exact_mod_cast Nat.pos_of_ne_zero hn

/-! ## Ground truth against the pinned `terms` field -/

/-- The `terms` field of OEIS A273929 as pulled on 2026-08-05, transcribed in order. -/
def a273929Prefix : List ℕ :=
  [5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31, 37, 38, 39, 46, 47, 53, 55, 61, 62, 69, 70,
   71, 77, 78, 79, 85, 86, 87, 93, 94, 95, 101, 102, 103, 109, 110, 111, 118, 119, 127, 133,
   134, 141, 142, 143, 149, 151, 157, 158, 159, 165, 166, 167, 173, 174]

/-- The pinned prefix has `57` entries. -/
theorem a273929Prefix_length : a273929Prefix.length = 57 := by decide

/-- `MemA273929` in the bounded, kernel-reducible form. -/
lemma memA273929_iff_bounded (n : ℕ) :
    MemA273929 n ↔ (∀ d ∈ Finset.Icc 2 n, ¬ (d * d ∣ n)) ∧ n % 8 ∈ ({5, 6, 7} : Finset ℕ) := by
  constructor
  · rintro ⟨hsf, hres⟩
    have hn : n ≠ 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hres
      omega
    exact ⟨(squarefree_iff_forall_mem_Icc hn).1 hsf, hres⟩
  · rintro ⟨hscan, hres⟩
    have hn : n ≠ 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hres
      omega
    exact ⟨(squarefree_iff_forall_mem_Icc hn).2 hscan, hres⟩

set_option maxRecDepth 100000 in
/-- **Kernel sweep.** Filtering `0, …, 174` by the bounded form of `MemA273929`
reproduces the pinned `terms` field exactly. -/
theorem filter_range_eq_a273929Prefix :
    (List.range 175).filter
        (fun n => decide ((∀ d ∈ Finset.Icc 2 n, ¬ (d * d ∣ n))
          ∧ n % 8 ∈ ({5, 6, 7} : Finset ℕ))) = a273929Prefix := by
  decide

/-- **Ground truth.** Below `175`, `MemA273929` holds at exactly the values published in
the pinned `terms` field. -/
theorem mem_a273929Prefix_iff {n : ℕ} (hn : n < 175) :
    n ∈ a273929Prefix ↔ MemA273929 n := by
  rw [← filter_range_eq_a273929Prefix, List.mem_filter, List.mem_range,
    memA273929_iff_bounded, decide_eq_true_eq]
  exact and_iff_right hn

/-- Nonvacuity of `mem_a273929Prefix_iff`: both sides are inhabited, at the first term. -/
theorem memA273929_five : MemA273929 5 := (mem_a273929Prefix_iff (by norm_num)).1 (by decide)

/-- And the negative side: `4` is `≡ 4 (mod 8)` and absent from the prefix. -/
theorem not_memA273929_four : ¬ MemA273929 4 := by
  rw [← mem_a273929Prefix_iff (by norm_num)]
  decide

/-! ## Small-case certificates: the first six terms are congruent

Each triangle is checked in the kernel: `a² + b² = c²` and `a·b = 2n` with `a, b, c > 0`.
These are exactly the six values `5, 6, 7, 13, 14, 15` that open the pinned `terms`
field. -/

/-- `5` is congruent: the `(3/2, 20/3, 41/6)` triangle. -/
theorem isCongruentNumber_five : IsCongruentNumber 5 :=
  ⟨3 / 2, 20 / 3, 41 / 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `6` is congruent: the `(3, 4, 5)` triangle. -/
theorem isCongruentNumber_six : IsCongruentNumber 6 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `7` is congruent: the `(35/12, 24/5, 337/60)` triangle. -/
theorem isCongruentNumber_seven : IsCongruentNumber 7 :=
  ⟨35 / 12, 24 / 5, 337 / 60, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `13` is congruent: the `(323/30, 780/323, 106921/9690)` triangle. -/
theorem isCongruentNumber_thirteen : IsCongruentNumber 13 :=
  ⟨323 / 30, 780 / 323, 106921 / 9690, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- `14` is congruent: the `(8/3, 21/2, 65/6)` triangle. -/
theorem isCongruentNumber_fourteen : IsCongruentNumber 14 :=
  ⟨8 / 3, 21 / 2, 65 / 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `15` is congruent: the `(4, 15/2, 17/2)` triangle. -/
theorem isCongruentNumber_fifteen : IsCongruentNumber 15 :=
  ⟨4, 15 / 2, 17 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The archived claim holds at the first six terms of the pinned `terms` field.  This is
`a273929_subset_a006991` restricted to `{5, 6, 7, 13, 14, 15}`, proved. -/
theorem isPrimitiveCongruent_of_mem_first_six {n : ℕ}
    (hn : n ∈ ({5, 6, 7, 13, 14, 15} : Finset ℕ)) : IsPrimitiveCongruent n := by
  have hsf : ∀ m : ℕ, m ≠ 0 → (∀ d ∈ Finset.Icc 2 m, ¬ (d * d ∣ m)) → Squarefree m :=
    fun m hm => (squarefree_iff_forall_mem_Icc hm).2
  fin_cases hn
  · exact ⟨hsf 5 (by norm_num) (by decide), isCongruentNumber_five⟩
  · exact ⟨hsf 6 (by norm_num) (by decide), isCongruentNumber_six⟩
  · exact ⟨hsf 7 (by norm_num) (by decide), isCongruentNumber_seven⟩
  · exact ⟨hsf 13 (by norm_num) (by decide), isCongruentNumber_thirteen⟩
  · exact ⟨hsf 14 (by norm_num) (by decide), isCongruentNumber_fourteen⟩
  · exact ⟨hsf 15 (by norm_num) (by decide), isCongruentNumber_fifteen⟩

/-! ## The corresponding points of `Eₙ`

`WeierstrassCurve.Affine.Point.some` requires `Nonsingular`, supplied by
`congruentCurve_nonsingular`; so these are points of Mathlib's point type, not merely
solutions of an equation. -/

/-- The point `(12, 36)` of `E₆ : y² = x³ − 36x`, the image of the `(3, 4, 5)` triangle
under Fermat's map (`x = a(a+c)/2 = 3·8/2`, `y = a²(a+c)/2 = 9·8/2`). -/
def curvePointSix : (congruentCurve 6).Point :=
  .some 12 36 (congruentCurve_nonsingular (by norm_num)
    ((congruentCurve_equation_iff 6 12 36).2 (by norm_num)))

/-- The point `(25/4, 75/8)` of `E₅ : y² = x³ − 25x`. -/
def curvePointFive : (congruentCurve 5).Point :=
  .some (25 / 4) (75 / 8) (congruentCurve_nonsingular (by norm_num)
    ((congruentCurve_equation_iff 5 (25 / 4) (75 / 8)).2 (by norm_num)))

/-- The point `(112/9, 980/27)` of `E₇ : y² = x³ − 49x`. -/
def curvePointSeven : (congruentCurve 7).Point :=
  .some (112 / 9) (980 / 27) (congruentCurve_nonsingular (by norm_num)
    ((congruentCurve_equation_iff 7 (112 / 9) (980 / 27)).2 (by norm_num)))

/-- Ground truth linking the two predicates at `n = 6`: `E₆` has a nontrivial point. -/
theorem hasNontrivialPoint_six : HasNontrivialPoint 6 :=
  hasNontrivialPoint_of_isCongruentArea
    (isCongruentArea_of_isCongruentNumber (by norm_num) isCongruentNumber_six)

/-! ## The complementary piece is inhabited

Explicit primitive congruent numbers in each of the residues `1, 2, 3 (mod 8)`; all three
are terms of the pinned A062695 `terms` field.  Without these,
`isPrimitiveCongruent_iff_of_congruent` could be a statement about an empty right-hand
disjunct. -/

/-- `34 ≡ 2 (mod 8)` is primitive congruent: the `(17/6, 24, 145/6)` triangle. -/
theorem isPrimitiveCongruentLow_thirtyFour : IsPrimitiveCongruentLow 34 :=
  ⟨⟨(squarefree_iff_forall_mem_Icc (by norm_num)).2 (by decide),
    ⟨17 / 6, 24, 145 / 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩,
   by decide⟩

/-- `41 ≡ 1 (mod 8)` is primitive congruent: the `(123/20, 40/3, 881/60)` triangle. -/
theorem isPrimitiveCongruentLow_fortyOne : IsPrimitiveCongruentLow 41 :=
  ⟨⟨(squarefree_iff_forall_mem_Icc (by norm_num)).2 (by decide),
    ⟨123 / 20, 40 / 3, 881 / 60, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩⟩,
   by decide⟩

set_option maxRecDepth 100000 in
/-- `219 ≡ 3 (mod 8)` is primitive congruent: the `(55/4, 1752/55, 7633/220)` triangle.
`maxRecDepth` is raised for the squarefree scan: the elaborator recurses once per element
of `Finset.Icc 2 219` while reducing the decidability instance. -/
theorem isPrimitiveCongruentLow_twoHundredNineteen : IsPrimitiveCongruentLow 219 :=
  ⟨⟨(squarefree_iff_forall_mem_Icc (by norm_num)).2 (by decide),
    ⟨55 / 4, 1752 / 55, 7633 / 220, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩⟩,
   by decide⟩

/-! ## The union claim -/

/-- **The unconditional half of the pinned union claim**: every primitive congruent number
either lies in A273929 or is one of the `≡ 1, 2, 3 (mod 8)` primitive congruent numbers.
Only `mem_residues_of_squarefree` is needed; no BSD, no congruence criterion. -/
theorem mem_or_low_of_isPrimitiveCongruent {n : ℕ} (h : IsPrimitiveCongruent n) :
    MemA273929 n ∨ IsPrimitiveCongruentLow n := by
  obtain ⟨hsf, hcong⟩ := h
  have hres := mem_residues_of_squarefree hsf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hres
  rcases hres with h1 | h2 | h3 | h5 | h6 | h7
  · exact Or.inr ⟨⟨hsf, hcong⟩, by rw [h1]; decide⟩
  · exact Or.inr ⟨⟨hsf, hcong⟩, by rw [h2]; decide⟩
  · exact Or.inr ⟨⟨hsf, hcong⟩, by rw [h3]; decide⟩
  · exact Or.inl ⟨hsf, by rw [h5]; decide⟩
  · exact Or.inl ⟨hsf, by rw [h6]; decide⟩
  · exact Or.inl ⟨hsf, by rw [h7]; decide⟩

/-- Nonvacuity of `mem_or_low_of_isPrimitiveCongruent`: its hypothesis is inhabited at
`n = 6`, where the left disjunct holds. -/
example : MemA273929 6 ∨ IsPrimitiveCongruentLow 6 :=
  mem_or_low_of_isPrimitiveCongruent (isPrimitiveCongruent_of_mem_first_six (by decide))

/-- …and at `n = 34`, where the right disjunct holds. -/
example : MemA273929 34 ∨ IsPrimitiveCongruentLow 34 :=
  mem_or_low_of_isPrimitiveCongruent isPrimitiveCongruentLow_thirtyFour.1

/-- The easy inclusion of the union claim: the complementary piece sits inside A006991 by
construction. -/
theorem isPrimitiveCongruent_of_low {n : ℕ} (h : IsPrimitiveCongruentLow n) :
    IsPrimitiveCongruent n := h.1

/-- **The union claim of the pinned comment**, "The union of this sequence with A062695
gives A006991", with the one missing inclusion carried as an explicit hypothesis.

The hypothesis `hcong` is *pointwise*: it is `a273929_subset_a006991` at the single `n`
under consideration, so it can be discharged at concrete arguments — see the two
`example`s below, one where it is proved (`n = 6`) and one where it is vacuous
(`n = 34`).  The forward direction does not use it at all; only the `MemA273929 n → …`
half of the backward direction does. -/
theorem isPrimitiveCongruent_iff_of_congruent {n : ℕ}
    (hcong : MemA273929 n → IsCongruentNumber n) :
    IsPrimitiveCongruent n ↔ MemA273929 n ∨ IsPrimitiveCongruentLow n := by
  constructor
  · exact mem_or_low_of_isPrimitiveCongruent
  · rintro (hmem | hlow)
    · exact ⟨hmem.1, hcong hmem⟩
    · exact isPrimitiveCongruent_of_low hlow

/-- Satisfiability of the hypothesis of `isPrimitiveCongruent_iff_of_congruent`, at `n = 6`
where it is proved outright. -/
example : IsPrimitiveCongruent 6 ↔ MemA273929 6 ∨ IsPrimitiveCongruentLow 6 :=
  isPrimitiveCongruent_iff_of_congruent (fun _ => isCongruentNumber_six)

/-- Satisfiability again at `n = 34`, where the hypothesis is vacuous (`34 % 8 = 2`) and
the right-hand disjunct is the one that holds. -/
example : IsPrimitiveCongruent 34 ↔ MemA273929 34 ∨ IsPrimitiveCongruentLow 34 :=
  isPrimitiveCongruent_iff_of_congruent (fun h => absurd h.2 (by decide))

/-! ## The archived claim -/

/-- **A273929 is a subset of the primitive congruent numbers A006991 (OEIS, conditional on
the Birch and Swinnerton-Dyer conjecture).**

Verbatim from the entry's `comments` field, pulled 2026-08-05:

> It has been shown, conditional on the Birch Swinnerton-Dyer conjecture, that this
> sequence is a subset of the primitive congruent numbers (A006991). The union of this
> sequence with A062695 gives A006991. Also this sequence is the intersection of A047574
> and A005117.

Only the first sentence is archived here; the second is
`isPrimitiveCongruent_iff_of_congruent` and the third is true by construction (see the
docstring of `MemA273929`).

**Status: open.**  This is the single intended `sorry` of the file.  The claim is a
theorem *conditional* on BSD for the curves `y² = x³ − n²x`, by Tunnell's criterion (whose
converse direction is exactly what BSD supplies — see the verbatim wiki quotation in the
module docstring) together with the observation that the Tunnell counting condition is
automatic in the residue classes `5, 6, 7 (mod 8)`; the entry's own Mathematica program,
pinned verbatim in the module docstring, encodes precisely that short circuit
(`MemberQ[{5, 6, 7}, Mod[n, 8]], ok = True`).

**Equivalent point form.**  By `a273929_subset_iff_hasNontrivialPoint`, this statement is
equivalent to: for every squarefree `n ≡ 5, 6, 7 (mod 8)` the curve `Eₙ` carries a
rational point with `y ≠ 0`.  That is the shape a proof would have to take, and it is why
this file needs no rank functional.

**Why it is hard.**  What has to be produced is an actual rational point, and the residue
condition on its own only supplies the *Tunnell counting condition* — the conditional half
of the pinned wiki sentence is exactly the step "these equalities are sufficient to
conclude that `n` is a congruent number", and that step is the one that needs BSD.  The
unconditional results are all partial.  The wiki records, verbatim:

> if $p ≡ 5 (mod 8)$, then $p$ is a congruent number.

> if $p ≡ 7 (mod 8)$, then $p$ and 2$p$ are congruent numbers.

> It is also known that in each of the congruence classes $5, 6, 7 (mod 8)$, for any given
> $k$ there are infinitely many square-free congruent numbers with $k$ prime factors.

Neither covers all squarefree `n ≡ 5, 6, 7 (mod 8)`, and Mathlib has neither Heegner
points, nor `L`-functions of elliptic curves over `ℚ` in a usable form, nor a Mordell–Weil
theorem.

**The residue classes are not interchangeable.**  The archived claim is specific to
`5, 6, 7 (mod 8)`; the wiki records the opposite behaviour in one of the complementary
classes, verbatim:

> if $p ≡ 3 ([[modular arithmetic|mod]] 8)$, then $p$ is not a congruent number, but 2$p$
> is a congruent number.

So the primitive congruent numbers `≡ 1, 2, 3 (mod 8)` are a *proper* subset of the
squarefree numbers in those classes — which is why `IsPrimitiveCongruentLow` carries
`IsPrimitiveCongruent` as a conjunct and not just the residue.  That negative statement is
not formalised here either (it is another descent; see "Mathlib gaps").

What *is* proved here about this statement: it holds at the first six terms
`5, 6, 7, 13, 14, 15` of the pinned `terms` field
(`isPrimitiveCongruent_of_mem_first_six`), by explicit triangles. -/
theorem a273929_subset_a006991 (n : ℕ) (hn : MemA273929 n) : IsPrimitiveCongruent n := by
  sorry

/-- Nonvacuity of `a273929_subset_a006991`: its hypothesis is inhabited (`memA273929_five`)
and its conclusion is *proved* at that point, so the archived statement is neither vacuous
nor refuted at any term of the pinned prefix that this file can check. -/
example : IsPrimitiveCongruent 5 := isPrimitiveCongruent_of_mem_first_six (by decide)

/-- **The archived claim in its rank-free point form**, `sorry`-free: `A273929 ⊆ A006991`
holds **iff** every squarefree `n ≡ 5, 6, 7 (mod 8)` gives a curve `y² = x³ − n²x` with a
rational point off `y = 0`.

This is an equivalence between two open statements, so it is provable outright — it is the
reformulation `isCongruentArea_iff_hasNontrivialPoint` transported along the cast
`ℕ → ℚ`. -/
theorem a273929_subset_iff_hasNontrivialPoint :
    (∀ n : ℕ, MemA273929 n → IsPrimitiveCongruent n)
      ↔ ∀ n : ℕ, MemA273929 n → HasNontrivialPoint (n : ℚ) := by
  constructor
  · intro h n hn
    exact hasNontrivialPoint_of_isCongruentArea (h n hn).2
  · intro h n hn
    exact ⟨hn.1, isCongruentArea_of_hasNontrivialPoint (cast_pos_of_memA273929 hn) (h n hn)⟩

/-! ## Signature audit -/

#check @congruentCurve
#check @congruentCurve_a₁
#check @congruentCurve_a₂
#check @congruentCurve_a₃
#check @congruentCurve_a₄
#check @congruentCurve_a₆
#check @congruentCurve_equation_iff
#check @congruentCurve_Δ
#check @congruentCurve_nonsingular
#check @IsCongruentArea
#check @HasNontrivialPoint
#check @hasNontrivialPoint_iff
#check @hasNontrivialPoint_iff_nonsingular
#check @pos_of_isCongruentArea
#check @not_isCongruentArea_zero
#check @not_isCongruentArea_neg_one
#check @tunnell_x_eq
#check @tunnell_y_eq
#check @hasNontrivialPoint_of_isCongruentArea
#check @translate_equation
#check @exists_gt_of_hasNontrivialPoint
#check @isCongruentArea_of_hasNontrivialPoint
#check @isCongruentArea_iff_hasNontrivialPoint
#check @squarefree_iff_forall_mem_Icc
#check @squarefree_six
#check @not_squarefree_twelve
#check @mem_residues_of_squarefree
#check @IsCongruentNumber
#check @IsPrimitiveCongruent
#check @MemA273929
#check @IsPrimitiveCongruentLow
#check @isCongruentArea_of_isCongruentNumber
#check @not_isCongruentNumber_zero
#check @cast_pos_of_memA273929
#check @a273929Prefix
#check @a273929Prefix_length
#check @memA273929_iff_bounded
#check @filter_range_eq_a273929Prefix
#check @mem_a273929Prefix_iff
#check @memA273929_five
#check @not_memA273929_four
#check @isCongruentNumber_five
#check @isCongruentNumber_six
#check @isCongruentNumber_seven
#check @isCongruentNumber_thirteen
#check @isCongruentNumber_fourteen
#check @isCongruentNumber_fifteen
#check @isPrimitiveCongruent_of_mem_first_six
#check @curvePointSix
#check @curvePointFive
#check @curvePointSeven
#check @hasNontrivialPoint_six
#check @isPrimitiveCongruentLow_thirtyFour
#check @isPrimitiveCongruentLow_fortyOne
#check @isPrimitiveCongruentLow_twoHundredNineteen
#check @mem_or_low_of_isPrimitiveCongruent
#check @isPrimitiveCongruent_of_low
#check @isPrimitiveCongruent_iff_of_congruent
#check @a273929_subset_a006991
#check @a273929_subset_iff_hasNontrivialPoint

/-! ## Axiom audit

Everything below is `{propext, Classical.choice, Quot.sound}` except
`a273929_subset_a006991`, the single intended `sorry`, which also reports `sorryAx`. -/

#print axioms congruentCurve_equation_iff
#print axioms congruentCurve_Δ
#print axioms congruentCurve_nonsingular
#print axioms hasNontrivialPoint_iff
#print axioms hasNontrivialPoint_iff_nonsingular
#print axioms pos_of_isCongruentArea
#print axioms not_isCongruentArea_zero
#print axioms not_isCongruentArea_neg_one
#print axioms tunnell_x_eq
#print axioms tunnell_y_eq
#print axioms hasNontrivialPoint_of_isCongruentArea
#print axioms translate_equation
#print axioms exists_gt_of_hasNontrivialPoint
#print axioms isCongruentArea_of_hasNontrivialPoint
#print axioms isCongruentArea_iff_hasNontrivialPoint
#print axioms squarefree_iff_forall_mem_Icc
#print axioms squarefree_six
#print axioms not_squarefree_twelve
#print axioms mem_residues_of_squarefree
#print axioms isCongruentArea_of_isCongruentNumber
#print axioms not_isCongruentNumber_zero
#print axioms cast_pos_of_memA273929
#print axioms a273929Prefix_length
#print axioms memA273929_iff_bounded
#print axioms filter_range_eq_a273929Prefix
#print axioms mem_a273929Prefix_iff
#print axioms memA273929_five
#print axioms not_memA273929_four
#print axioms isCongruentNumber_five
#print axioms isCongruentNumber_six
#print axioms isCongruentNumber_seven
#print axioms isCongruentNumber_thirteen
#print axioms isCongruentNumber_fourteen
#print axioms isCongruentNumber_fifteen
#print axioms isPrimitiveCongruent_of_mem_first_six
#print axioms curvePointSix
#print axioms curvePointFive
#print axioms curvePointSeven
#print axioms hasNontrivialPoint_six
#print axioms isPrimitiveCongruentLow_thirtyFour
#print axioms isPrimitiveCongruentLow_fortyOne
#print axioms isPrimitiveCongruentLow_twoHundredNineteen
#print axioms mem_or_low_of_isPrimitiveCongruent
#print axioms isPrimitiveCongruent_of_low
#print axioms isPrimitiveCongruent_iff_of_congruent
#print axioms a273929_subset_iff_hasNontrivialPoint
#print axioms a273929_subset_a006991

end A273929
