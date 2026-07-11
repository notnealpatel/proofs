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
    · `HomogeneousIdeal (graded ring)`  — Z-graded apolar candidate ideal  [EXISTS]
    · `Module.length`                   — length of a finite scheme        [EXISTS]
    · `IsReduced` / `Ideal.IsRadical`   — reduced = "distinct smooth pts"  [EXISTS]
  Everything genuinely absent (border rank, secant/cactus variety, the
  Hilbert scheme of points, smoothability, VP/VNP circuit families,
  apolarity) is `sorry`-defined here and carried by a blocked task card.

  Primary sources (labels/lines as in docs/Vp1.md, docs/Np1.md):
    FSV  arXiv:1701.05328  Defn 2.1 (distinguisher), barrier theorem.
    GKSS arXiv:1701.01717  algebraic natural proofs = succinct hitting set.
    CHL  arXiv:1911.07981  border apolarity, the (210)/(120)/(111) tests.
    Buczynski arXiv:2602.11309  cactus barrier, smoothability = breaking it.

  AI disclosure: skeleton produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Length

namespace Vp2

open scoped Classical

/-! ## 0. Base objects: tensors and their entry vectors -/

/-- A 3-tensor of side `n` over `k`: `T i j k` is the entry `c_{ijk}`.
This is the task-specified concrete shape `Fin n → Fin n → Fin n → k`,
the same object as a point of `kⁿ ⊗ kⁿ ⊗ kⁿ` in the standard basis. -/
abbrev Tensor3 (k : Type*) (n : ℕ) : Type _ := Fin n → Fin n → Fin n → k

/-- The index set of the `n³` tensor entries; these are the variables a
"distinguisher" polynomial `D(c_{ijk})` ranges over (FSV Defn 2.1:
`coeff(f)` ↦ the tensor entries). -/
abbrev EntryIndex (n : ℕ) : Type _ := Fin n × Fin n × Fin n

/-- The entry vector of a tensor, as the evaluation point for a
distinguisher `D : MvPolynomial (EntryIndex n) k`. -/
def entries {k : Type*} {n : ℕ} (T : Tensor3 k n) : EntryIndex n → k :=
  fun ijk => T ijk.1 ijk.2.1 ijk.2.2

/-! ## 1. Border rank as secant-variety membership  [ABSENT in Mathlib]

`BorderRankLE T r` means `T ∈ σ_r(Seg)`, the `r`-th secant variety of
the Segre. Mathlib has neither secant varieties nor the Segre embedding
(survey: ABSENT). Discharging this requires the `BorderRank` task card. -/

/-- `BorderRankLE T r` : the tensor `T` has border rank at most `r`,
i.e. it lies in the Zariski closure of the rank-`≤ r` tensors
(`σ_r(Seg)`). Opaque pending the secant-variety formalization. -/
def BorderRankLE {k : Type*} {n : ℕ} (_T : Tensor3 k n) (_r : ℕ) : Prop :=
  -- SORRY[BorderRank]: should be membership of `entries T` in the vanishing
  -- locus of `I(σ_r(Seg))`. Requires: Segre embedding, join/secant
  -- construction, Zariski closure of a constructible set. None exist in
  -- Mathlib. See task card `BorderRank` (built on `Segre`, `SecantVariety`).
  sorry

/-! ## 2. VP-computable distinguishers  [ABSENT in Mathlib]

A distinguisher (FSV Defn 2.1) is a nonzero `D ∈ k[c_{ijk}]` vanishing on
all `T` with `BorderRankLE T r`. It is *VP-natural* when `D` is computed
by a poly(N)-size algebraic circuit (`N = n³`). Mathlib has no algebraic
computation model at all ("circuit" = matroid circuit); see task card
`VPCircuit`. We carry `IsVP` as an opaque predicate on polynomials. -/

/-- `IsVP n D` : the polynomial `D` in the `n³` tensor entries is
computable by a poly(`n³`)-size algebraic circuit (the "constructivity"
hypothesis the barrier quantifies over). Opaque pending a circuit model. -/
def IsVP {k : Type*} [CommSemiring k] (n : ℕ) (_D : MvPolynomial (EntryIndex n) k) : Prop :=
  -- SORRY[VPCircuit]: should assert existence of an arithmetic circuit
  -- of size ≤ poly(n³) computing `D`. Requires a formal algebraic circuit
  -- model (gates +, ×, leaves = variables/constants; size; the class VP).
  -- Absent in Mathlib. See task card `VPCircuit`.
  sorry

/-- A *distinguisher* for `σ_r(Seg)`: a nonzero polynomial in the tensor
entries that vanishes on every tensor of border rank `≤ r` (FSV Defn 2.1,
specialized to the secant variety per Np1 §2c). -/
structure Distinguisher (k : Type*) [CommSemiring k] (n r : ℕ) where
  /-- the polynomial in the `n³` entry variables -/
  poly : MvPolynomial (EntryIndex n) k
  /-- it is not identically zero -/
  ne_zero : poly ≠ 0
  /-- it vanishes on the secant variety `σ_r(Seg)` -/
  vanishes : ∀ T : Tensor3 k n, BorderRankLE T r → MvPolynomial.eval (entries T) poly = 0

/-- A *VP-natural proof* against `σ_r(Seg)`: a distinguisher whose
polynomial is additionally VP-computable. This is exactly the object the
algebraic natural-proofs barrier governs (Np1 §2d, item 4). -/
structure VPDistinguisher (k : Type*) [CommSemiring k] (n r : ℕ) extends Distinguisher k n r where
  /-- the underlying polynomial is VP-computable -/
  isVP : IsVP n toDistinguisher.poly

/-! ### 2a. Flattenings are VP-distinguishers (the SUPPORTED fact)

The `(j)`-flattening of `T` is the `n × n²` matrix `M_T` with
`(M_T)_{i,(j,k)} = c_{ijk}`; if `BorderRankLE T r` then this matrix has
rank `≤ r`, so every `(r+1)×(r+1)` minor (a degree-`r+1` determinantal
polynomial in the entries) vanishes (Np1 §2; Sager: 84 degree-3 minors
witness this for `n = r = 3`). These minors are `Matrix.det` of
submatrices — manifestly VP-computable. This is the only place the
skeleton claims a *supported* mathematical fact, so it carries the
hardest `sorry`s; everything downstream is type-level plumbing. -/

/-- The `j`-flattening of `T` as an `n × (n × n)` matrix of entries:
row `i`, column `(j, l)` holds `c_{i j l}`. (Reuses `Matrix`/`Matrix.det`
from Mathlib; this object is fully definable, no `sorry`.) -/
def flattening {k : Type*} {n : ℕ} (T : Tensor3 k n) :
    Matrix (Fin n) (Fin n × Fin n) k :=
  fun i jl => T i jl.1 jl.2

/-- A flattening `(r+1)×(r+1)`-minor distinguisher exists for `σ_r(Seg)`
whenever `r + 1 ≤ n` (so the minor is nontrivial). This packages the
SUPPORTED fact (Np1 §2): such a `D` is a genuine VP-natural proof, hence
the barrier's hypothesis is nonvacuous for the tensor setting. -/
theorem exists_flattening_vpDistinguisher
    {k : Type*} [Field k] {n r : ℕ} (_h : r + 1 ≤ n) :
    Nonempty (VPDistinguisher k n r) := by
  -- SORRY[FlatteningMinor]: build `D` = a fixed `(r+1)×(r+1)` minor of the
  -- generic flattening (a `Matrix.det` of `MvPolynomial` entries), then
  -- prove: (i) `ne_zero` — the minor is a nonzero polynomial (needs the
  -- generic-flattening rank fact); (ii) `vanishes` — rank `≤ r` ⇒ minor
  -- `= 0` (needs `BorderRank` ⇒ flattening-rank bound, i.e. the secant
  -- variety formalization); (iii) `isVP` — a determinant is computed by a
  -- poly-size circuit (needs `VPCircuit`). Blocked on `BorderRank`,
  -- `VPCircuit`, `FlatteningMinor`.
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
