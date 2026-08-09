/-
  BilinearComplexity/BooleanRank — matrix rank over the two-element
  Boolean semiring ({0,1}, ∨, ∧): `boolRank A` is the least `r` such
  that `A` factors as an (m×r)·(r×n) Boolean matrix product,
  equivalently (`boolRankLE_iff_pointwise`) the least number of all-ones
  combinatorial rectangles covering exactly the support of `A`.

    · `BoolSemiring`      — the Boolean semiring: `Bool` re-typed, with
                            `+ = or` (so `1 + 1 = 1`) and `* = and`.
                            Mathlib's `Bool` itself carries the xor-based
                            `BooleanRing` — 𝔽₂ arithmetic — so a fresh
                            type synonym is required to keep `∑`/`*`
                            meaning Boolean, not 𝔽₂, arithmetic.
    · `BoolMatrix m n`    — `Fin m → Fin n → BoolSemiring`, curried
                            `Fin`-indexed matrices, matching the `Tensor`
                            representation convention of `Basic.lean`.
    · `BoolRankLE A r`    — `A = B · C` with `B : m × r`, `C : r × n`;
                            decidable by finite search over witnesses.
    · `boolRank A`        — the least such `r`, as `Nat.find` on the
                            decidable predicate `BoolRankLE A ·`, which
                            is nonempty by the identity factorizations
                            `boolRankLE_rows` (`r = m`) and
                            `boolRankLE_cols` (`r = n`) — so the minimum
                            is attained (`boolRankLE_boolRank`), never a
                            vacuous infimum; `boolRank_eq_sInf` links it
                            to the `sInf` convention of `Basic.lean`.
    · anchors             — `boolRank_zero` (`= 0`), `boolRank_allOnes`
                            (`= 1` on nonempty shapes), `boolRank_boolId`
                            (`= n`, by the rectangle pigeonhole), plus
                            kernel-`decide` ground checks at small sizes.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Choose

set_option autoImplicit false

namespace BilinearComplexity

/-! ## 1. The Boolean semiring -/

/-- The two-element Boolean semiring `({0,1}, ∨, ∧)`. The carrier is
`Bool`, but re-typed: Mathlib endows `Bool` itself with the xor-based
`BooleanRing` (𝔽₂ arithmetic, `1 + 1 = 0`), whereas here `0 = false`,
`1 = true`, `+` is `or` (idempotent: `1 + 1 = 1`) and `*` is `and`. -/
def BoolSemiring : Type := Bool

/-- Equality in the Boolean semiring is decidable (it is `Bool`). -/
instance : DecidableEq BoolSemiring := inferInstanceAs (DecidableEq Bool)

/-- The Boolean semiring is a finite type (it is `Bool`). -/
instance : Fintype BoolSemiring := inferInstanceAs (Fintype Bool)

/-- `0 = false` in the Boolean semiring. -/
instance : Zero BoolSemiring := ⟨(false : Bool)⟩

/-- `1 = true` in the Boolean semiring. -/
instance : One BoolSemiring := ⟨(true : Bool)⟩

/-- `+ = or` in the Boolean semiring (idempotent, not xor). -/
instance : Add BoolSemiring := ⟨fun a b => Bool.or a b⟩

/-- `* = and` in the Boolean semiring. -/
instance : Mul BoolSemiring := ⟨fun a b => Bool.and a b⟩

/-- The (or, and) commutative-semiring structure on the two-element
Boolean semiring; all axioms hold by finite enumeration. -/
instance : CommSemiring BoolSemiring where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  nsmul := nsmulRec
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide

/-- The Boolean semiring is nontrivial: `0 ≠ 1`. -/
instance : Nontrivial BoolSemiring := ⟨⟨0, 1, by decide⟩⟩

-- Ground checks: Boolean, not 𝔽₂, arithmetic — `+` is or, `*` is and.
example : (1 : BoolSemiring) + 1 = 1 := by decide
example : (0 : BoolSemiring) + 1 = 1 := by decide
example : (0 : BoolSemiring) + 0 = 0 := by decide
example : (1 : BoolSemiring) * 1 = 1 := by decide
example : (1 : BoolSemiring) * 0 = 0 := by decide
example : (0 : BoolSemiring) ≠ 1 := by decide

namespace BoolSemiring

/-- The Boolean semiring is two-valued: every element is `0` or `1`. -/
theorem eq_zero_or_eq_one : ∀ a : BoolSemiring, a = 0 ∨ a = 1 := by decide

/-- A Boolean sum is `1` iff a summand is (`+` is or). -/
theorem add_eq_one_iff : ∀ a b : BoolSemiring, a + b = 1 ↔ a = 1 ∨ b = 1 := by
  decide

/-- A Boolean product is `1` iff both factors are (`*` is and). -/
theorem mul_eq_one_iff : ∀ a b : BoolSemiring, a * b = 1 ↔ a = 1 ∧ b = 1 := by
  decide

/-- A finite sum in the Boolean semiring is `1` iff some summand is `1`:
`∑` is an iterated or. -/
theorem sum_eq_one_iff {ι : Type*} (t : Finset ι) (f : ι → BoolSemiring) :
    (∑ s ∈ t, f s) = 1 ↔ ∃ s ∈ t, f s = 1 := by
  induction t using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    exact iff_of_false (by decide) (by simp)
  | cons a t ha ih =>
    rw [Finset.sum_cons, add_eq_one_iff, ih]
    constructor
    · rintro (h | ⟨s, hs, hfs⟩)
      · exact ⟨a, Finset.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨s, Finset.mem_cons.mpr (Or.inr hs), hfs⟩
    · rintro ⟨s, hs, hfs⟩
      rcases Finset.mem_cons.mp hs with rfl | hs'
      · exact Or.inl hfs
      · exact Or.inr ⟨s, hs', hfs⟩

end BoolSemiring

/-! ## 2. Boolean matrices and the factorization predicate -/

/-- A Boolean `m × n` matrix: a curried `Fin`-indexed function into the
Boolean semiring, matching the `Tensor` representation convention of
`Basic.lean`. -/
abbrev BoolMatrix (m n : ℕ) : Type := Fin m → Fin n → BoolSemiring

/-- The Boolean identity matrix: `1` on the diagonal, `0` off it. -/
def boolId (n : ℕ) : BoolMatrix n n := fun i j => if i = j then 1 else 0

-- Ground checks for `boolId`.
example : boolId 2 0 0 = 1 := rfl
example : boolId 2 0 1 = 0 := rfl
example : boolId 2 1 0 = 0 := rfl
example : boolId 2 1 1 = 1 := rfl

/-- `BoolRankLE A r` : the Boolean matrix `A` factors through `r` as a
Boolean matrix product `A = B · C` with `B : m × r` and `C : r × n`.
Equivalently (`boolRankLE_iff_pointwise`) the support of `A` is exactly
covered by the `r` all-ones combinatorial rectangles
`{i | B i s = 1} × {j | C s j = 1}`. -/
def BoolRankLE {m n : ℕ} (A : BoolMatrix m n) (r : ℕ) : Prop :=
  ∃ B : BoolMatrix m r, ∃ C : BoolMatrix r n,
    A = fun i j => ∑ s, B i s * C s j

/-- Boolean rank-≤ is decidable: a finite search over factorization
witnesses. -/
instance {m n : ℕ} (A : BoolMatrix m n) (r : ℕ) : Decidable (BoolRankLE A r) :=
  inferInstanceAs (Decidable (∃ B : BoolMatrix m r, ∃ C : BoolMatrix r n,
    A = fun i j => ∑ s, B i s * C s j))

/-- Boolean rank-≤ is monotone in `r`: pad the factorization with zero
columns of `B` and zero rows of `C`. -/
theorem BoolRankLE.mono {m n : ℕ} {A : BoolMatrix m n} {r r' : ℕ}
    (h : BoolRankLE A r) (hrr' : r ≤ r') : BoolRankLE A r' := by
  obtain ⟨B, C, hA⟩ := h
  have key : BoolRankLE A (r + (r' - r)) := by
    refine ⟨fun i => Fin.append (B i) 0, Fin.append C 0, ?_⟩
    subst hA
    funext i j
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rwa [show r + (r' - r) = r' from by omega] at key

/-- Row-count bound: `A = I_m · A`, so `A` factors through `m`. -/
theorem boolRankLE_rows {m n : ℕ} (A : BoolMatrix m n) : BoolRankLE A m := by
  refine ⟨boolId m, A, ?_⟩
  funext i j
  simp [boolId, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]

/-- Column-count bound: `A = A · I_n`, so `A` factors through `n`. -/
theorem boolRankLE_cols {m n : ℕ} (A : BoolMatrix m n) : BoolRankLE A n := by
  refine ⟨A, boolId n, ?_⟩
  funext i j
  simp [boolId, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

/-- Boolean rank-≤ 0 means the matrix is zero (the empty sum). -/
theorem boolRankLE_zero_iff {m n : ℕ} {A : BoolMatrix m n} :
    BoolRankLE A 0 ↔ A = 0 := by
  constructor
  · rintro ⟨B, C, rfl⟩
    funext i j
    simp
  · rintro rfl
    refine ⟨0, 0, ?_⟩
    funext i j
    simp

/-- Rectangle-cover characterization of Boolean factorization: `A = B · C`
iff the support of `A` is exactly the union of the `r` all-ones rectangles
`{i | B i s = 1} × {j | C s j = 1}`, `s : Fin r`. -/
theorem boolRankLE_iff_pointwise {m n r : ℕ} {A : BoolMatrix m n} :
    BoolRankLE A r ↔ ∃ B : BoolMatrix m r, ∃ C : BoolMatrix r n,
      ∀ i j, (A i j = 1 ↔ ∃ s, B i s = 1 ∧ C s j = 1) := by
  constructor
  · rintro ⟨B, C, rfl⟩
    refine ⟨B, C, fun i j => ?_⟩
    simp only [BoolSemiring.sum_eq_one_iff, BoolSemiring.mul_eq_one_iff,
      Finset.mem_univ, true_and]
  · rintro ⟨B, C, hBC⟩
    refine ⟨B, C, ?_⟩
    funext i j
    rcases BoolSemiring.eq_zero_or_eq_one (A i j) with h0 | h1
    · rcases BoolSemiring.eq_zero_or_eq_one (∑ s, B i s * C s j) with hs0 | hs1
      · rw [h0, hs0]
      · exfalso
        obtain ⟨s, -, hs⟩ :=
          (BoolSemiring.sum_eq_one_iff Finset.univ fun s => B i s * C s j).mp hs1
        rw [BoolSemiring.mul_eq_one_iff] at hs
        have hA1 : A i j = 1 := (hBC i j).mpr ⟨s, hs.1, hs.2⟩
        rw [h0] at hA1
        exact (by decide : (0 : BoolSemiring) ≠ 1) hA1
    · obtain ⟨s, hBs, hCs⟩ := (hBC i j).mp h1
      rw [h1]
      symm
      rw [BoolSemiring.sum_eq_one_iff]
      exact ⟨s, Finset.mem_univ s, (BoolSemiring.mul_eq_one_iff _ _).mpr ⟨hBs, hCs⟩⟩

/-! ## 3. Boolean rank -/

/-- Factorization witnesses always exist (at `r = n`, via `A = A · I_n`),
so the Boolean rank's defining search is over a nonempty decidable
predicate — never a vacuous infimum. -/
theorem exists_boolRankLE {m n : ℕ} (A : BoolMatrix m n) :
    ∃ r, BoolRankLE A r :=
  ⟨n, boolRankLE_cols A⟩

/-- The Boolean rank of a matrix: the least `r` such that `A` factors as
an (m×r)·(r×n) Boolean product, i.e. the least number of all-ones
rectangles covering the support. Defined by `Nat.find` over the decidable,
witness-nonempty predicate `BoolRankLE A ·`, so it is a genuine attained
minimum (`boolRankLE_boolRank`, `boolRank_le_of_boolRankLE`) and is
computable. -/
def boolRank {m n : ℕ} (A : BoolMatrix m n) : ℕ :=
  Nat.find (exists_boolRankLE A)

/-- The Boolean rank is attained: `A` factors through `boolRank A`. -/
theorem boolRankLE_boolRank {m n : ℕ} (A : BoolMatrix m n) :
    BoolRankLE A (boolRank A) :=
  Nat.find_spec (exists_boolRankLE A)

/-- Minimality: any factorization bound dominates the Boolean rank. -/
theorem boolRank_le_of_boolRankLE {m n : ℕ} {A : BoolMatrix m n} {r : ℕ}
    (h : BoolRankLE A r) : boolRank A ≤ r :=
  Nat.find_min' (exists_boolRankLE A) h

/-- Any bound at or above the Boolean rank admits a factorization. -/
theorem boolRankLE_of_boolRank_le {m n : ℕ} {A : BoolMatrix m n} {r : ℕ}
    (h : boolRank A ≤ r) : BoolRankLE A r :=
  (boolRankLE_boolRank A).mono h

/-- Order interface: `boolRank A ≤ r` iff `A` factors through `r`. -/
theorem boolRank_le_iff {m n : ℕ} {A : BoolMatrix m n} {r : ℕ} :
    boolRank A ≤ r ↔ BoolRankLE A r :=
  ⟨boolRankLE_of_boolRank_le, boolRank_le_of_boolRankLE⟩

/-- Ground-check driver: `boolRank A = r` iff `A` factors through `r` but
through no `s < r`. Both sides of the conjunction are decidable, so small
concrete instances close by `decide`. -/
theorem boolRank_eq_iff {m n : ℕ} {A : BoolMatrix m n} {r : ℕ} :
    boolRank A = r ↔ BoolRankLE A r ∧ ∀ s < r, ¬BoolRankLE A s :=
  Nat.find_eq_iff (exists_boolRankLE A)

/-- The trivial row-count bound: `boolRank A ≤ m`. -/
theorem boolRank_le_rows {m n : ℕ} (A : BoolMatrix m n) : boolRank A ≤ m :=
  boolRank_le_of_boolRankLE (boolRankLE_rows A)

/-- The trivial column-count bound: `boolRank A ≤ n`. -/
theorem boolRank_le_cols {m n : ℕ} (A : BoolMatrix m n) : boolRank A ≤ n :=
  boolRank_le_of_boolRankLE (boolRankLE_cols A)

/-- The trivial bound: `boolRank A ≤ min m n`. -/
theorem boolRank_le_min {m n : ℕ} (A : BoolMatrix m n) :
    boolRank A ≤ min m n :=
  le_min (boolRank_le_rows A) (boolRank_le_cols A)

/-- `boolRank` agrees with the `sInf`-of-the-bound-set formulation used
for tensor `rank` in `Basic.lean`. -/
theorem boolRank_eq_sInf {m n : ℕ} (A : BoolMatrix m n) :
    boolRank A = sInf {r | BoolRankLE A r} :=
  le_antisymm
    (boolRank_le_of_boolRankLE
      (Nat.sInf_mem (s := {r | BoolRankLE A r}) ⟨n, boolRankLE_cols A⟩))
    (Nat.sInf_le (boolRankLE_boolRank A))

/-! ## 4. Anchors: zero, all-ones, identity -/

/-- The Boolean rank vanishes exactly on the zero matrix. -/
theorem boolRank_eq_zero_iff {m n : ℕ} {A : BoolMatrix m n} :
    boolRank A = 0 ↔ A = 0 := by
  rw [← Nat.le_zero, boolRank_le_iff, boolRankLE_zero_iff]

/-- The zero matrix has Boolean rank `0`. -/
theorem boolRank_zero {m n : ℕ} : boolRank (0 : BoolMatrix m n) = 0 :=
  boolRank_eq_zero_iff.mpr rfl

/-- The all-ones matrix of a nonempty shape has Boolean rank `1`: one
all-ones rectangle covers everything, and a nonzero matrix needs at least
one. (The nonemptiness guards are necessary: an empty-shaped all-ones
matrix is the zero matrix, of rank `0`.) -/
theorem boolRank_allOnes {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    boolRank (fun _ _ => 1 : BoolMatrix m n) = 1 := by
  refine le_antisymm (boolRank_le_of_boolRankLE ⟨fun _ _ => 1, fun _ _ => 1, ?_⟩) ?_
  · funext i j
    simp
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [boolRank_eq_zero_iff] at h0
    have happ := congrFun (congrFun h0 ⟨0, hm⟩) ⟨0, hn⟩
    simp at happ

/-- Rectangle pigeonhole for the identity: any Boolean factorization of
`I_n` needs at least `n` inner indices. A rectangle covering the diagonal
cell `(i, i)` that also covered `(i', i')` would cover the off-diagonal
cell `(i, i')`, so the diagonal's rectangle labels are injective. -/
theorem le_of_boolRankLE_boolId {n r : ℕ} (h : BoolRankLE (boolId n) r) :
    n ≤ r := by
  rw [boolRankLE_iff_pointwise] at h
  obtain ⟨B, C, hBC⟩ := h
  have hdiag : ∀ i : Fin n, ∃ s : Fin r, B i s = 1 ∧ C s i = 1 := by
    intro i
    refine (hBC i i).mp ?_
    simp [boolId]
  choose σ hB hC using hdiag
  have hinj : Function.Injective σ := by
    intro i i' hσ
    by_contra hne
    have hcell : boolId n i i' = 1 := by
      refine (hBC i i').mpr ⟨σ i, hB i, ?_⟩
      rw [hσ]
      exact hC i'
    rw [boolId, if_neg hne] at hcell
    exact (by decide : (0 : BoolSemiring) ≠ 1) hcell
  simpa using Fintype.card_le_of_injective σ hinj

/-- The `n × n` identity has Boolean rank exactly `n`: it factors through
`n` trivially, and no fewer rectangles suffice by the pigeonhole
`le_of_boolRankLE_boolId`. -/
theorem boolRank_boolId (n : ℕ) : boolRank (boolId n) = n :=
  le_antisymm (boolRank_le_cols (boolId n))
    (le_of_boolRankLE_boolId (boolRankLE_boolRank (boolId n)))

/-! ## 5. `decide` ground checks

Kernel-`decide` evaluations of the decidable factorization predicate at
small concrete matrices, grounding the definitions computationally,
independent of the generic anchor theorems above. -/

-- `BoolRankLE` ground checks.
example : BoolRankLE (boolId 2) 2 := by decide
example : ¬BoolRankLE (boolId 2) 1 := by decide

-- Zero matrices have Boolean rank 0.
example : boolRank (0 : BoolMatrix 2 2) = 0 := boolRank_eq_iff.mpr (by decide)
example : boolRank (0 : BoolMatrix 2 3) = 0 := boolRank_eq_iff.mpr (by decide)

-- Degenerate shape: an empty-shaped "all-ones" matrix is zero, rank 0.
example : boolRank (fun _ _ => 1 : BoolMatrix 0 5) = 0 :=
  boolRank_eq_iff.mpr (by decide)

-- All-ones matrices have Boolean rank 1.
example : boolRank (fun _ _ => 1 : BoolMatrix 2 2) = 1 :=
  boolRank_eq_iff.mpr (by decide)
example : boolRank (fun _ _ => 1 : BoolMatrix 2 3) = 1 :=
  boolRank_eq_iff.mpr (by decide)

-- Identity matrices have full Boolean rank. For 3×3 the upper bound is
-- the identity factorization `boolRankLE_cols`; the lower bound is a
-- kernel refutation of every factorization through `r < 3`.
example : boolRank (boolId 1) = 1 := boolRank_eq_iff.mpr (by decide)
example : boolRank (boolId 2) = 2 := boolRank_eq_iff.mpr (by decide)
set_option maxRecDepth 40000 in
example : boolRank (boolId 3) = 3 :=
  boolRank_eq_iff.mpr ⟨boolRankLE_cols (boolId 3), by decide⟩

-- Satisfiability of hypotheses, jointly at concrete models.
example : BoolRankLE (boolId 2) 3 := (boolRankLE_cols (boolId 2)).mono (by omega)
example : boolRank (fun _ _ => 1 : BoolMatrix 2 3) = 1 :=
  boolRank_allOnes (by omega) (by omega)
example : 2 ≤ 2 := le_of_boolRankLE_boolId (boolRankLE_cols (boolId 2))
example : BoolRankLE (boolId 2) 2 := boolRankLE_of_boolRank_le (by
  rw [boolRank_boolId])

-- Cross-check: the generic anchors agree with the `decide` checks.
example : boolRank (boolId 2) = 2 := boolRank_boolId 2
example : boolRank (0 : BoolMatrix 4 7) = 0 := boolRank_zero

-- 𝔽₂-vs-Boolean distinguishing check: `J₃ − I₃` has 𝔽₂-rank `2` but Boolean
-- rank `3` (rectangles avoiding the diagonal need Sperner-many labels); had
-- xor arithmetic leaked into the factorization sums through the `Bool`
-- synonym, the `r = 2` refutation below would fail.
set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
example : boolRank (fun i j => if i = j then 0 else 1 : BoolMatrix 3 3) = 3 :=
  boolRank_eq_iff.mpr ⟨by decide, by decide⟩

end BilinearComplexity
