/-
  Vp2 — A sorry-skeleton making precise the OPEN QUESTION:

    "The (111) border apolarity test is structurally outside the
     algebraic natural-proofs framework: it is a smoothability search
     in the Hilbert scheme, not the evaluation of a polynomial in the
     tensor entries. Whether this structural distinction constitutes a
     provable escape from the barrier remains an open question."

  This is a FEASIBILITY SURVEY, not a proof campaign. The file's job is
  to (a) give type-level objects for every noun in the sentence above,
  and (b) state the open question as a machine-precise `Prop`, with each
  `sorry` annotated by the Mathlib infrastructure that would be required
  to discharge it. The real deliverable is the dependency-ordered set of
  task cards (blocked on Vp2) for the missing formalizations; see
  `.tasks/research/docs/Vp2.md`.

  FOUNDATIONS NOTE (binding — see `.tasks/research/docs/Vp1.md`).
  The Vp1 resolution is UNPINNED-ANALOGY: *no primary source proves*
  that the (111) test escapes the algebraic natural-proofs barrier.
  Stating "the (111) test escapes" as a `theorem ... := by sorry` would
  assert a proof exists where none does — a mis-stated theorem, which
  the doctrine forbids. Therefore the open question is packaged here as
  a named `Prop` (`Vp2OpenQuestion`), NOT as a theorem we claim to have
  proved. The only `theorem`s with `sorry` below are the two facts the
  sources DO support (Np1 §2): (i) flattening minors are VP-computable
  distinguishers covered by the barrier, and (ii) the (111) verdict has
  the wrong type to be such a distinguisher (it is an existential search
  over candidate graded ideals together with a smoothability witness).
  The final `theorem` records the EQUIVALENCE between the open question
  and a precise inexpressibility statement — formalizing that the open
  question is well-posed, not that it is resolved.

  Mathlib substrate actually reused (survey in docs/Vp2.md):
    · `MvPolynomial (entries) k`        — distinguisher polynomials       [EXISTS]
    · `MvPolynomial.eval`               — evaluation at the tensor entries [EXISTS]
    · `Matrix.det`                      — flattening / Koszul determinants [EXISTS]
    · `MvPolynomial.zeroLocus` /
      `MvPolynomial.vanishingIdeal`     — border rank as poly closure     [EXISTS]
    · `Matrix.rank` + minor lemmas      — flattening rank bounds          [EXISTS]
    · `HomogeneousIdeal (graded ring)`  — Z-graded apolar candidate ideal  [EXISTS]
    · `Module.length`                   — length of a finite scheme        [EXISTS]
    · `IsReduced` / `Ideal.IsRadical`   — reduced = "distinct smooth pts"  [EXISTS]
  Everything genuinely absent (secant/cactus varieties as schemes, the
  Hilbert scheme of points, smoothability, apolarity) is `sorry`-defined
  here and carried by a blocked task card. Border rank itself is NO
  LONGER absent: `Proofs.Vp2.BorderRank` (imported below) defines it for
  real, as polynomial closure. Arithmetic circuits are NO LONGER absent
  either: `Proofs.Vp2.Circuit` defines the model (`Circuit`, `size`,
  `eval`, `ComputedInSize`, `VPFamily`); of the VP leg only the
  family-level retyping of `IsVP` remains (see its annotation).

  CHANGELOG (2026-07-11, task Pf2 — arithmetic circuit model):
    · `Proofs.Vp2.Circuit` (NEW; not imported here — no statement in this
      file changed) provides the repo's first arithmetic-circuit-size
      infrastructure: `Circuit σ k` (expression trees), `size`,
      `eval : Circuit σ k → MvPolynomial σ k`, builders with exact size
      lemmas, the degree bound `totalDegree_eval_le`, completeness
      `exists_circuit` (every polynomial has a circuit, with explicit
      size), and the honest predicates `ComputedInSize s D` / `VPFamily D`.
    · The `isVP` leg's honest content is PROVED there: the flattening
      minor witnessing `exists_flattening_distinguisher` below is
      `ComputedInSize ((r+1)!·(2·(r+1)+4)+1)` — a bound constant in `n` —
      (`computedInSize_flatteningMinor`), and the fixed-r minor family is
      a genuine `VPFamily` (`vpFamily_flatteningMinorFamily`).
    · `IsVP` stays sorry-defined ON PURPOSE: "poly-size" at a single
      fixed `n` is vacuous — `Vp2.exists_computedInSize` proves EVERY
      polynomial is "computed in some size" — and any non-vacuous
      single-n reading would pin an arbitrary threshold, a dishonest
      definition. The honest discharge retypes this file's objects over
      families; recorded at the `IsVP` annotation. No statement here was
      weakened.

  CHANGELOG (2026-07-11, task Pf1 — border rank infrastructure):
    · `BorderRankLE` is no longer `sorry`-defined. Vp2/BorderRank.lean
      defines it as membership of `entries T` in the zero locus of the
      vanishing ideal of the rank-≤ r locus (`MvPolynomial.zeroLocus`,
      `MvPolynomial.vanishingIdeal`; Mathlib.RingTheory.Nullstellensatz).
      Over ℂ this is classical border rank; over a general field it is
      the polynomial-closure notion — exactly the property
      `Distinguisher.vanishes` consumes. See the header of BorderRank.lean.
    · `Tensor3`, `EntryIndex`, `entries`, `flattening` moved VERBATIM to
      Vp2/BorderRank.lean, which now sits upstream of this file.
    · `Distinguisher` / `VPDistinguisher` binders strengthened from
      `CommSemiring k` to `Field k`: the real `BorderRankLE` needs a
      field (Mathlib's `zeroLocus` is field-valued), and every downstream
      theorem here already assumed one.
    · NEW sorry-free `exists_flattening_distinguisher`: flattening minors
      are genuine distinguishers (`ne_zero` + `vanishes` both proved).
      Of `exists_flattening_vpDistinguisher` only the `isVP` leg remains
      open, blocked solely on the `VPCircuit` task card.

  Primary sources (labels/lines as in docs/Vp1.md, docs/Np1.md):
    FSV  arXiv:1701.05328  Defn 2.1 (distinguisher), barrier theorem.
    GKSS arXiv:1701.01717  algebraic natural proofs = succinct hitting set.
    CHL  arXiv:1911.07981  border apolarity, the (210)/(120)/(111) tests.
    Buczynski arXiv:2602.11309  cactus barrier, smoothability = breaking it.

  AI disclosure: skeleton produced with AI assistance (see Proofs/README).
-/
import Proofs.Vp2.BorderRank
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Length

namespace Vp2

open scoped Classical

/-! ## 0. Base objects: tensors and their entry vectors

`Tensor3`, `EntryIndex`, `entries`, and the `j`-flattening `flattening`
now live in `Proofs.Vp2.BorderRank` (imported above, same namespace),
together with the rank-≤ r locus and border rank. -/

/-! ## 1. Border rank  [REAL — Proofs.Vp2.BorderRank]

`BorderRankLE T r` is no longer `sorry`-defined. BorderRank.lean defines
it as membership of `entries T` in
`zeroLocus k (vanishingIdeal k (rankLocus k n r))`: every polynomial
vanishing on all rank-≤ r tensors vanishes at `T` (`borderRankLE_iff`).
Over `ℂ` that is the classical border rank, membership in the r-th
secant variety `σ_r(Seg)` of the Segre (Zariski = Euclidean closure of
the rank-≤ r locus); over a general field it is the polynomial-closure
notion, which is precisely the property `Distinguisher.vanishes` below
consumes. Supporting infrastructure proved there, all sorry-free:
`RankLE.borderRankLE`, monotonicity in `r` of both notions, the
flattening rank bound `RankLE.rank_flattening_le`, minor vanishing
`det_submatrix_eq_zero_of_rank_le`, and the generic flattening minors
(nonzero as polynomials; identically zero on the border-rank locus). -/

/-! ## 2. VP-computable distinguishers  [circuit model: Proofs.Vp2.Circuit]

A distinguisher (FSV Defn 2.1) is a nonzero `D ∈ k[c_{ijk}]` vanishing on
all `T` with `BorderRankLE T r`. It is *VP-natural* when `D` is computed
by a poly(N)-size algebraic circuit (`N = n³`). Mathlib still has no
algebraic computation model ("circuit" = matroid circuit), but this
development now does: `Proofs.Vp2.Circuit` (task Pf2) defines expression
trees with `size`/`eval` into `MvPolynomial`, the honest fixed-bound
predicate `ComputedInSize s D`, and the family-level class `VPFamily`.
`IsVP` remains an opaque sorry-predicate for a TYPE-LEVEL reason, not a
missing model — see its annotation. -/

/-- `IsVP n D` : the polynomial `D` in the `n³` tensor entries is
computable by a poly(`n³`)-size algebraic circuit (the "constructivity"
hypothesis the barrier quantifies over). The circuit MODEL now exists
(`Proofs.Vp2.Circuit`); what keeps this opaque is that "poly-size" is a
property of a family, not of one polynomial at one `n` — see the
annotation in the body. -/
def IsVP {k : Type*} [CommSemiring k] (n : ℕ) (_D : MvPolynomial (EntryIndex n) k) : Prop :=
  -- SORRY[VPCircuit-family]: the circuit model this was blocked on now
  -- EXISTS (`Proofs.Vp2.Circuit`): `Circuit σ k` with `size`/`eval`, the
  -- honest fixed-bound predicate `ComputedInSize s D` (∃ circuit of size
  -- ≤ s computing D), and the family-level class
  --   `VPFamily D := ∃ c, ∀ n, ComputedInSize ((n³ + c)^c) (D n)`.
  -- What remains is a TYPE-LEVEL obstruction, not missing infrastructure:
  -- "poly(n³)-size" is a growth condition on a FAMILY of polynomials,
  -- while this def receives a single `D` at a single fixed `n`. At fixed
  -- `n` the naive unfolding "∃ s, s ≤ poly(n³) ∧ ComputedInSize s D" is
  -- VACUOUS — by circuit completeness every polynomial has some circuit
  -- (`Vp2.exists_computedInSize`), so `IsVP` would be trivially true and
  -- the barrier statement empty — while any non-vacuous single-n reading
  -- must pin an arbitrary size threshold, a dishonest definition
  -- (doctrine: no invented pinned exponents). Discharging this sorry
  -- therefore means retyping `VPDistinguisher`/`DecidedByVP`/
  -- `Vp2OpenQuestion`/`vp2OpenQuestion_iff` over distinguisher FAMILIES
  -- quantified via `VPFamily` — a re-statement of the open question
  -- itself, deliberately out of Pf2's scope; still carried by task card
  -- `VPCircuit` (now reduced to that family retyping). The honest
  -- fragments are already PROVED in Circuit.lean: the concrete
  -- flattening-minor distinguisher is
  -- `ComputedInSize ((r+1)!·(2·(r+1)+4)+1)` — a bound constant in `n` —
  -- (`computedInSize_flatteningMinor`), and the fixed-r minor family is
  -- a genuine `VPFamily` (`vpFamily_flatteningMinorFamily`).
  sorry

/-- A *distinguisher* for `σ_r(Seg)`: a nonzero polynomial in the tensor
entries that vanishes on every tensor of border rank `≤ r` (FSV Defn 2.1,
specialized to the secant variety per Np1 §2c). `[Field k]` because the
real `BorderRankLE` (Vp2/BorderRank.lean) is stated over a field. -/
structure Distinguisher (k : Type*) [Field k] (n r : ℕ) where
  /-- the polynomial in the `n³` entry variables -/
  poly : MvPolynomial (EntryIndex n) k
  /-- it is not identically zero -/
  ne_zero : poly ≠ 0
  /-- it vanishes on the secant variety `σ_r(Seg)` -/
  vanishes : ∀ T : Tensor3 k n, BorderRankLE T r → MvPolynomial.eval (entries T) poly = 0

/-- A *VP-natural proof* against `σ_r(Seg)`: a distinguisher whose
polynomial is additionally VP-computable. This is exactly the object the
algebraic natural-proofs barrier governs (Np1 §2d, item 4). -/
structure VPDistinguisher (k : Type*) [Field k] (n r : ℕ) extends Distinguisher k n r where
  /-- the underlying polynomial is VP-computable -/
  isVP : IsVP n toDistinguisher.poly

/-! ### 2a. Flattenings are VP-distinguishers (the SUPPORTED fact)

The `(j)`-flattening of `T` is the `n × n²` matrix `M_T` with
`(M_T)_{i,(j,k)} = c_{ijk}` (`flattening`, now in BorderRank.lean); if
`BorderRankLE T r` then this matrix has rank `≤ r`, so every
`(r+1)×(r+1)` minor (a degree-`r+1` determinantal polynomial in the
entries) vanishes (Np1 §2; Sager: 84 degree-3 minors witness this for
`n = r = 3`). Both mathematical legs of this supported fact are now
PROVED (`exists_flattening_distinguisher`, sorry-free, via
Vp2/BorderRank.lean): the minor is a nonzero polynomial, and it vanishes
on the whole border-rank-≤ r locus. The only remaining `sorry` is the
VP-computability leg (`exists_flattening_vpDistinguisher`), blocked on a
formal algebraic circuit model. -/

/-- Flattening minors are genuine distinguishers for `σ_r(Seg)` whenever
`r + 1 ≤ n`: a fixed `(r+1)×(r+1)` minor of the generic flattening is a
nonzero polynomial in the tensor entries (BorderRank.lean §5) that
vanishes on every tensor of border rank `≤ r` (BorderRank.lean §6).
Sorry-free — this is the honest, fully-proved part of the SUPPORTED fact
(Np1 §2); only VP-computability of the minor is left open, in
`exists_flattening_vpDistinguisher` below. -/
theorem exists_flattening_distinguisher
    {k : Type*} [Field k] {n r : ℕ} (h : r + 1 ≤ n) :
    Nonempty (Distinguisher k n r) :=
  ⟨{ poly := ((genericFlattening k n).submatrix (Fin.castLE h)
        fun t => (Fin.castLE h t, Fin.castLE h t)).det
     ne_zero := det_genericFlattening_submatrix_ne_zero (Fin.castLE_injective h)
        fun _ _ htt' => Fin.castLE_injective h (congrArg Prod.fst htt')
     vanishes := fun _T hT => hT.eval_det_genericFlattening_submatrix_eq_zero _ _ }⟩

/-- A flattening `(r+1)×(r+1)`-minor distinguisher exists for `σ_r(Seg)`
whenever `r + 1 ≤ n` (so the minor is nontrivial). This packages the
SUPPORTED fact (Np1 §2): such a `D` is a genuine VP-natural proof, hence
the barrier's hypothesis is nonvacuous for the tensor setting. -/
theorem exists_flattening_vpDistinguisher
    {k : Type*} [Field k] {n r : ℕ} (_h : r + 1 ≤ n) :
    Nonempty (VPDistinguisher k n r) := by
  -- SORRY[VPCircuit-family]: legs (i) `ne_zero` and (ii) `vanishes` are
  -- DISCHARGED — `exists_flattening_distinguisher` above builds the
  -- flattening-minor distinguisher sorry-free on the real `BorderRankLE`
  -- (Vp2/BorderRank.lean). Leg (iii) `isVP`'s honest CONTENT is now ALSO
  -- proved, in `Proofs.Vp2.Circuit`: this very minor is computed by an
  -- explicit Leibniz circuit of size ≤ (r+1)!·(2·(r+1)+4)+1, constant in
  -- n (`computedInSize_flatteningMinor`), so the fixed-r minor family is
  -- a genuine VP family (`vpFamily_flatteningMinorFamily`). What still
  -- blocks is only that `IsVP` itself is sorry-defined (single-n
  -- type-level obstruction; see its annotation): nothing can be proved
  -- ABOUT an opaque sorry-Prop, so no bridge `ComputedInSize → IsVP` can
  -- exist yet. Once `IsVP` is retyped at the family level, this proof is
  -- `(exists_flattening_distinguisher _h).map fun D => ⟨D, …⟩` with the
  -- Circuit.lean witnesses.
  sorry

/-! ## 3. The (111) border apolarity test  [ABSENT in Mathlib]

The structurally DIFFERENT object. CHL's algorithm enumerates Borel-fixed
graded ideals (candidate apolar ideals of length-`r` schemes) and checks
rank conditions; the (111) verdict is sound because the candidate must be
the flat limit of ideals of *smooth* (reduced) length-`r` schemes —
i.e. a smoothability search in the Hilbert scheme (Vp1 §2, Cb1 §1).

We model only what is needed to state the type mismatch:
  · a candidate is a `HomogeneousIdeal` (Mathlib: EXISTS) with a length-`r`
    and a smoothability flag;
  · the (111) verdict is `∃` over candidates, not `eval` of a polynomial. -/

variable (S : Type*) [CommRing S]

/-- A candidate apolar ideal for the (111) test: a homogeneous (graded)
ideal of the coordinate/Cox ring `S`, recording its scheme length and
whether it is a flat limit of *smoothable* (reduced) ideals. Mathlib
supplies `HomogeneousIdeal` and `Module.length`; smoothability is opaque.

`𝒜` is the grading datum on `S` (an internal grading by some monoid `ι`). -/
structure ApolarCandidate {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (𝒜 : ι → Submodule ℤ S) [GradedAlgebra 𝒜] where
  /-- the candidate graded ideal `I ⊆ S` (CHL: Borel-fixed; we keep only
  the homogeneity, which is the Mathlib-expressible part) -/
  ideal : HomogeneousIdeal 𝒜
  /-- the length of the quotient scheme `Spec(S/I)`; for an apolar scheme
  of a border-rank-`r` decomposition this equals `r` -/
  length : ℕ
  /-- SMOOTHABILITY witness: `I` is the flat limit of homogeneous ideals
  of *reduced* (distinct-point) length-`length` schemes. This is the
  Hilbert-scheme condition that makes the (111) test sound and is exactly
  what is ABSENT from Mathlib (no Hilbert scheme of points, no smoothable
  component). Opaque pending the `Smoothability` task card. -/
  smoothable : Prop

/-- `Passes111 T r` : the (111) border apolarity verdict for `T` at rank
`r` — there EXISTS a grading, a Borel-fixed candidate apolar ideal of
length `r` annihilating `T`, of codimension `≥ r` on the (111) graded
piece, that is a flat limit of *smoothable* schemes. This is the crux:
its shape is `∃ (graded ring) (candidate) (...)`, a search in the Hilbert
scheme, NOT `MvPolynomial.eval D (entries T)` for any fixed `D`. -/
def Passes111 {k : Type*} {n : ℕ} (_T : Tensor3 k n) (_r : ℕ) : Prop :=
  -- SORRY[Test111]: should unfold to the CHL existential — `∃ grading 𝒜 on
  -- the Cox ring, ∃ ApolarCandidate with length = r, smoothable, ideal ⊆
  -- Ann(T), and the (210)/(120)/(111) rank conditions hold`. Requires:
  -- the apolar algebra `Ann(T)` (apolarity, ABSENT), the multigraded Cox
  -- ring, the rank-of-multiplication-map conditions, and `smoothable`
  -- (Hilbert scheme, ABSENT). See task cards `Apolarity`, `Test111`,
  -- `Smoothability`, `CactusVariety`.
  sorry

/-! ## 4. The open question, made precise

The barrier governs *polynomial* distinguishers (§2). The (111) verdict
(§3) is an existential search. The OPEN QUESTION (Vp1, UNPINNED-ANALOGY)
is whether the (111) verdict can nonetheless be *re-expressed* as the
output of some single VP-computable distinguisher — equivalently, whether
the constructible set `{T : Passes111 T r}` is cut out (as a decision) by
the vanishing of one VP polynomial. No source resolves this either way. -/

/-- `DecidedByVP T-test` says a VP-distinguisher family decides the (111)
test at rank `r`: there is one VP-computable polynomial `D` whose
vanishing at `entries T` matches `Passes111 T r` for *all* `T`. -/
def DecidedByVP (k : Type*) [Field k] (n r : ℕ) : Prop :=
  ∃ D : MvPolynomial (EntryIndex n) k, IsVP n D ∧
    ∀ T : Tensor3 k n, (MvPolynomial.eval (entries T) D = 0 ↔ Passes111 T r)

/-- **The open question (Vp2OpenQuestion).** For matrix-multiplication–type
parameters, the (111) border apolarity verdict is *not* decided by any
VP-computable polynomial in the tensor entries. Packaged as a `Prop`, not
a theorem: Vp1 establishes that no primary source proves or refutes it.
A proof would be a genuine escape from the natural-proofs barrier; a
refutation would place the (111) test back inside it. -/
def Vp2OpenQuestion (k : Type*) [Field k] (n r : ℕ) : Prop :=
  ¬ DecidedByVP k n r

/-- Well-posedness, the formal content actually delivered: the open
question is equivalent to the precise inexpressibility statement "for
every VP-computable `D` there is a tensor `T` on which `D`'s vanishing
disagrees with the (111) verdict." This is a tautological unfolding —
its only purpose is to certify that `Vp2OpenQuestion` is a sharply stated
mathematical proposition, NOT that it has been answered. -/
theorem vp2OpenQuestion_iff (k : Type*) [Field k] (n r : ℕ) :
    Vp2OpenQuestion k n r ↔
      ∀ D : MvPolynomial (EntryIndex n) k, IsVP n D →
        ∃ T : Tensor3 k n, ¬ (MvPolynomial.eval (entries T) D = 0 ↔ Passes111 T r) := by
  -- SORRY[wellposed]: pure logic — push `¬ ∃ ... ∧ ∀ ...` through to
  -- `∀ ... → ∃ ...`. Discharged once the underlying `sorry`-defs typecheck;
  -- no external Mathlib infrastructure needed. (Kept as `sorry` so the
  -- file's open obligations are visible in one `lake build` summary.)
  sorry

/-- Soundness anchor for the test (the supported direction of CHL's
method, Vp1 §2d): if `T` has border rank `≤ r`, then the (111) test
passes — there is a smoothable length-`r` apolar candidate. The converse
(passing ⇒ border rank `≤ r`) is FALSE in general (candidates may fail to
be smoothable), which is precisely why the test is a *search*, not an
equation. -/
theorem passes111_of_borderRankLE
    {k : Type*} [Field k] {n r : ℕ} (T : Tensor3 k n) (h : BorderRankLE T r) :
    Passes111 T r := by
  -- SORRY[Test111-sound]: the necessary-conditions direction of border
  -- apolarity — a border-rank decomposition yields a smoothable apolar
  -- candidate (CHL §7). With `BorderRankLE`/`Passes111` opaque, `h` has no
  -- usable structure, so this is a bare `sorry`; it becomes provable once
  -- `BorderRank`, `Apolarity`, `Test111`, `Smoothability` land.
  sorry

end Vp2
