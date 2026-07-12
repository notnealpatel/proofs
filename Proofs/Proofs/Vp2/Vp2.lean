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
  proved. Of the two facts the sources DO support (Np1 §2), (i)
  "flattening minors are VP-computable distinguishers covered by the
  barrier" is now PROVED sorry-free at the family level
  (`exists_flattening_vpDistinguisher`), while (ii) "the (111) verdict
  has the wrong type to be such a distinguisher (it is an existential
  search over candidate graded ideals together with a smoothability
  witness)" is still carried by the remaining `sorry`s (`Passes111`,
  `passes111_of_borderRankLE`), blocked on absent Mathlib infrastructure
  (apolarity, Hilbert scheme, smoothability). The final `theorem`
  (`vp2OpenQuestion_iff`, now proved) records the EQUIVALENCE between
  the open question and a precise inexpressibility statement —
  formalizing that the open question is well-posed, not that it is
  resolved.

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
  either: `Proofs.Vp2.Circuit` (imported below) defines the model
  (`Circuit`, `size`, `eval`, `ComputedInSize`, `VPFamily`), and the VP
  leg is fully discharged: since the 2026-07-12 family retyping this
  file's statements quantify over distinguisher FAMILIES via `VPFamily`
  (see the CHANGELOG entry below and §2).

  CHANGELOG (2026-07-12, task VPCircuit — the family retyping):
    · `Proofs.Vp2.Circuit` is now imported, and the single-n sorry-def
      `IsVP` is DELETED — discharged exactly as its annotation
      prescribed, by retyping the VP side of this file over FAMILIES
      `D : (n : ℕ) → MvPolynomial (EntryIndex n) k` quantified by the
      honest `VPFamily D` (∃ c, ∀ n, `D n` computed in size (n³ + c)^c,
      Circuit.lean). No pinned single-n size threshold anywhere; no
      statement weakened; three sorrys discharged (`IsVP`,
      `exists_flattening_vpDistinguisher`, `vp2OpenQuestion_iff`).
    · `VPDistinguisher` (single n) replaced by `VPDistinguisherFamily`
      over an n-indexed target rank `r : ℕ → ℕ`, with a `threshold`
      field: members must be nonzero and vanish on the border-rank-≤ r n
      locus for all `n ≥ threshold`. The "for sufficiently large n"
      quantifier is the standard asymptotic convention of the barrier
      literature: FSV (Defn 2.1) and GKSS quantify over poly-size
      circuit FAMILIES, whose size and agreement conditions are
      asymptotic. The fixed-n `Distinguisher` and the sorry-free
      `exists_flattening_distinguisher` STAY unchanged.
    · `exists_flattening_vpDistinguisher` retyped to constant-rank
      families and PROVED sorry-free: witness `flatteningMinorFamily`
      with threshold `r + 1`; legs by `flatteningMinorFamily_of_le` +
      `det_genericFlattening_submatrix_ne_zero`,
      `BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero`, and
      `vpFamily_flatteningMinorFamily` (all Circuit/BorderRank.lean).
    · `DecidedByVP` / `Vp2OpenQuestion` retyped over families: one VP
      family whose vanishing agrees with `Passes111 T (r n)` for all
      `T`, for all `n` beyond some `n₀` (same asymptotic convention).
      `vp2OpenQuestion_iff` restated accordingly and PROVED (pure
      classical logic: unfold + `push Not`, Mathlib's current name for
      push_neg) — the well-posedness certificate is no longer a sorry.
    · Remaining sorrys (2, both on the (111) side, other task cards):
      the def `Passes111` (SORRY[Test111]) and the soundness anchor
      `passes111_of_borderRankLE` (SORRY[Test111-sound]); both are
      single-T, single-r statements, untouched by the retyping apart
      from `Passes111` now being referenced at rank `r n`.

  CHANGELOG (2026-07-11, task Pf2 — arithmetic circuit model):
    · `Proofs.Vp2.Circuit` (NEW; imported here only since 2026-07-12 —
      Pf2 itself changed no statement in this file) provides the repo's
      first arithmetic-circuit-size infrastructure: `Circuit σ k`
      (expression trees), `size`,
      `eval : Circuit σ k → MvPolynomial σ k`, builders with exact size
      lemmas, the degree bound `totalDegree_eval_le`, completeness
      `exists_circuit` (every polynomial has a circuit, with explicit
      size), and the honest predicates `ComputedInSize s D` / `VPFamily D`.
    · The `isVP` leg's honest content is PROVED there: the flattening
      minor witnessing `exists_flattening_distinguisher` below is
      `ComputedInSize ((r+1)!·(2·(r+1)+4)+1)` — a bound constant in `n` —
      (`computedInSize_flatteningMinor`), and the fixed-r minor family is
      a genuine `VPFamily` (`vpFamily_flatteningMinorFamily`).
    · `IsVP` stayed sorry-defined ON PURPOSE at that point: "poly-size"
      at a single fixed `n` is vacuous — `Vp2.exists_computedInSize`
      proves EVERY polynomial is "computed in some size" — and any
      non-vacuous single-n reading would pin an arbitrary threshold, a
      dishonest definition. The honest discharge — retyping this file's
      objects over families — is exactly what the 2026-07-12 entry above
      records. No statement here was weakened.

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
      Of `exists_flattening_vpDistinguisher` only the `isVP` leg remained
      open, blocked solely on the `VPCircuit` task card (discharged
      2026-07-12 — see the entry above).

  Primary sources (labels/lines as in docs/Vp1.md, docs/Np1.md):
    FSV  arXiv:1701.05328  Defn 2.1 (distinguisher), barrier theorem.
    GKSS arXiv:1701.01717  algebraic natural proofs = succinct hitting set.
    CHL  arXiv:1911.07981  border apolarity, the (210)/(120)/(111) tests.
    Buczynski arXiv:2602.11309  cactus barrier, smoothability = breaking it.

  AI disclosure: skeleton produced with AI assistance (see Proofs/README).
-/
import Proofs.Vp2.BorderRank
import Proofs.Vp2.Circuit
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
development does: `Proofs.Vp2.Circuit` (task Pf2, imported above) defines
expression trees with `size`/`eval` into `MvPolynomial`, the honest
fixed-bound predicate `ComputedInSize s D`, and the family-level class
`VPFamily`. "Poly-size" is a growth condition on a FAMILY, not on one
polynomial at one `n` — at any fixed `n` EVERY polynomial is computed in
*some* size (`Vp2.exists_computedInSize`) — so the VP-natural objects
below are families quantified via `VPFamily` directly; the former
single-n `IsVP` sorry-def is gone (see the retrospective note below). -/

/-! #### Retrospective (2026-07-12): the former `IsVP` sorry-def is gone

Until 2026-07-12 this file carried
`def IsVP (n : ℕ) (D : MvPolynomial (EntryIndex n) k) : Prop := sorry`
(SORRY[VPCircuit-family]) — opaque because a non-vacuous "poly(n³)-size"
predicate cannot exist at one fixed `n`: every polynomial is computed in
*some* size (`Vp2.exists_computedInSize`, Circuit.lean), and any
non-vacuous single-n reading would pin an arbitrary size threshold, a
dishonest definition. Its annotation prescribed the honest discharge:
retype `VPDistinguisher` / `DecidedByVP` / `Vp2OpenQuestion` /
`vp2OpenQuestion_iff` over distinguisher FAMILIES quantified by
`VPFamily` (Circuit.lean). That retyping is now done — see
`VPDistinguisherFamily`, `DecidedByVP`, `Vp2OpenQuestion` below — so the
sorry is DISCHARGED BY DELETION: there is no per-`n` "IsVP" predicate to
define, and nothing below is blocked on the circuit model. -/

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

/-- A *VP-natural proof* against the border-rank loci `σ_{r n}(Seg)`, at
the honest family level: for each side `n` a polynomial `poly n` in the
`n³` tensor entries which, for every sufficiently large `n`
(`threshold ≤ n`), is a genuine distinguisher for rank `r n` — nonzero
and vanishing on the whole border-rank-≤ `r n` locus — and which as a
family is VP-computable (`VPFamily`, Circuit.lean). This is exactly the
object the algebraic natural-proofs barrier governs (Np1 §2d, item 4):
FSV Defn 2.1 / GKSS quantify over poly-size circuit FAMILIES, and their
size and agreement conditions are asymptotic, whence the `threshold`
("for sufficiently large n") field. At each `n ≥ threshold` the data
specializes to a fixed-n `Distinguisher k n (r n)`. -/
structure VPDistinguisherFamily (k : Type*) [Field k] (r : ℕ → ℕ) where
  /-- for each side `n`, a polynomial in the `n³` entry variables -/
  poly : (n : ℕ) → MvPolynomial (EntryIndex n) k
  /-- distinguishing is required only from this side on — the standard
  "for sufficiently large `n`" of asymptotic complexity -/
  threshold : ℕ
  /-- beyond the threshold, the member is not identically zero -/
  ne_zero : ∀ n, threshold ≤ n → poly n ≠ 0
  /-- beyond the threshold, the member vanishes on the whole
  border-rank-≤ `r n` locus `σ_{r n}(Seg)` -/
  vanishes : ∀ n, threshold ≤ n → ∀ T : Tensor3 k n,
    BorderRankLE T (r n) → MvPolynomial.eval (entries T) (poly n) = 0
  /-- the family is VP-computable: computed by circuits of size
  polynomial in `n³` -/
  isVP : VPFamily poly

/-! ### 2a. Flattenings are VP-distinguishers (the SUPPORTED fact)

The `(j)`-flattening of `T` is the `n × n²` matrix `M_T` with
`(M_T)_{i,(j,k)} = c_{ijk}` (`flattening`, now in BorderRank.lean); if
`BorderRankLE T r` then this matrix has rank `≤ r`, so every
`(r+1)×(r+1)` minor (a degree-`r+1` determinantal polynomial in the
entries) vanishes (Np1 §2; Sager: 84 degree-3 minors witness this for
`n = r = 3`). ALL legs of this supported fact are now PROVED, sorry-free:
at fixed `n`, `exists_flattening_distinguisher` (via Vp2/BorderRank.lean)
gives the nonzero minor vanishing on the whole border-rank-≤ r locus; at
the family level, `exists_flattening_vpDistinguisher` (via
Vp2/Circuit.lean) adds VP-computability of the minor family. -/

/-- Flattening minors are genuine distinguishers for `σ_r(Seg)` whenever
`r + 1 ≤ n`: a fixed `(r+1)×(r+1)` minor of the generic flattening is a
nonzero polynomial in the tensor entries (BorderRank.lean §5) that
vanishes on every tensor of border rank `≤ r` (BorderRank.lean §6).
Sorry-free — the fixed-`n` part of the SUPPORTED fact (Np1 §2);
VP-computability of the minor family is added, also sorry-free, by
`exists_flattening_vpDistinguisher` below. -/
theorem exists_flattening_distinguisher
    {k : Type*} [Field k] {n r : ℕ} (h : r + 1 ≤ n) :
    Nonempty (Distinguisher k n r) :=
  ⟨{ poly := ((genericFlattening k n).submatrix (Fin.castLE h)
        fun t => (Fin.castLE h t, Fin.castLE h t)).det
     ne_zero := det_genericFlattening_submatrix_ne_zero (Fin.castLE_injective h)
        fun _ _ htt' => Fin.castLE_injective h (congrArg Prod.fst htt')
     vanishes := fun _T hT => hT.eval_det_genericFlattening_submatrix_eq_zero _ _ }⟩

/-- **Flattening minors are a VP-natural proof** (the SUPPORTED fact,
Np1 §2 — now sorry-free end to end). For every fixed target rank `r`,
the family of `(r+1)×(r+1)` diagonal minors of the generic flattening
(`flatteningMinorFamily`, Circuit.lean) is a `VPDistinguisherFamily`
for the constant rank function `fun _ => r`, with threshold `r + 1`
(the side must be large enough for the minor to be nontrivial). Legs:
nonzero on injective picks (`det_genericFlattening_submatrix_ne_zero`);
vanishing on the border-rank-≤ r locus
(`BorderRankLE.eval_det_genericFlattening_submatrix_eq_zero`);
VP-computability (`vpFamily_flatteningMinorFamily` — Leibniz circuits
of size `(r+1)!·(2(r+1)+4)+1`, constant in `n`). Hence the barrier's
hypothesis is nonvacuous for the tensor setting. -/
theorem exists_flattening_vpDistinguisher {k : Type*} [Field k] (r : ℕ) :
    Nonempty (VPDistinguisherFamily k (fun _ => r)) :=
  ⟨{ poly := flatteningMinorFamily k r
     threshold := r + 1
     ne_zero := fun n hn => by
       rw [flatteningMinorFamily_of_le hn]
       exact det_genericFlattening_submatrix_ne_zero (Fin.castLE_injective hn)
         fun _ _ htt' => Fin.castLE_injective hn (congrArg Prod.fst htt')
     vanishes := fun n hn T hT => by
       rw [flatteningMinorFamily_of_le hn]
       exact hT.eval_det_genericFlattening_submatrix_eq_zero _ _
     isVP := vpFamily_flatteningMinorFamily k r }⟩

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

The barrier governs *polynomial* distinguisher families (§2). The (111)
verdict (§3) is an existential search. The OPEN QUESTION (Vp1,
UNPINNED-ANALOGY) is whether the (111) verdict can nonetheless be
*re-expressed* as the output of some VP-computable distinguisher family
— equivalently, whether the constructible sets `{T : Passes111 T (r n)}`
are cut out (as decisions, for all sufficiently large `n`) by the
vanishing of one VP family. No source resolves this either way. -/

/-- `DecidedByVP k r` says a VP family decides the (111) test at target
rank `r n`: there is one VP-computable family `D` of polynomials in the
tensor entries whose vanishing at `entries T` matches `Passes111 T (r n)`
for *all* `T`, for all sufficiently large `n` (the `n₀` cutoff — the same
asymptotic convention as `VPDistinguisherFamily.threshold`). -/
def DecidedByVP (k : Type*) [Field k] (r : ℕ → ℕ) : Prop :=
  ∃ D : (n : ℕ) → MvPolynomial (EntryIndex n) k, VPFamily D ∧
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ T : Tensor3 k n,
      (MvPolynomial.eval (entries T) (D n) = 0 ↔ Passes111 T (r n))

/-- **The open question (Vp2OpenQuestion).** For matrix-multiplication–type
parameters (a target-rank growth `r : ℕ → ℕ`), the (111) border apolarity
verdict is *not* decided by any VP-computable family of polynomials in
the tensor entries. Packaged as a `Prop`, not a theorem: Vp1 establishes
that no primary source proves or refutes it. A proof would be a genuine
escape from the natural-proofs barrier; a refutation would place the
(111) test back inside it. -/
def Vp2OpenQuestion (k : Type*) [Field k] (r : ℕ → ℕ) : Prop :=
  ¬ DecidedByVP k r

/-- Well-posedness, the formal content actually delivered: the open
question is equivalent to the precise inexpressibility statement "for
every VP-computable family `D` and every cutoff `n₀` there are a side
`n ≥ n₀` and a tensor `T` on which the vanishing of `D n` disagrees with
the (111) verdict at rank `r n`". This is a tautological unfolding (pure
classical logic) — its only purpose is to certify that `Vp2OpenQuestion`
is a sharply stated mathematical proposition, NOT that it has been
answered. -/
theorem vp2OpenQuestion_iff (k : Type*) [Field k] (r : ℕ → ℕ) :
    Vp2OpenQuestion k r ↔
      ∀ D : (n : ℕ) → MvPolynomial (EntryIndex n) k, VPFamily D →
        ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ T : Tensor3 k n,
          ¬ (MvPolynomial.eval (entries T) (D n) = 0 ↔ Passes111 T (r n)) := by
  unfold Vp2OpenQuestion DecidedByVP
  push Not
  rfl

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
