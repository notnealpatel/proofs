/-
# GKK τ-matrices (Holtz–Schneider), Problem 5: Newton's inequalities, order 3

## Source

O. Holtz and H. Schneider, *Open problems on GKK τ-matrices*,
arXiv:math/0109030 (dated 20 August 2001), Section 2 ("GKK τ-matrix
stability and related problems"), Problem 5.  The same question closes
Chapter 1 of Holtz's thesis (arXiv:math/0512588): "Do the GKK matrices
satisfy (newton)?".  Retrieved and re-read 2026-10-21.

Notation of the paper: `A[α, β] = det A(α, β)` for increasing sequences
`α, β` of equal length, `A[α] = A[α, α]`, `A[∅] = 1`; the *dispersal* of
`A[α, β]` is `#α - #(α ∩ β)`.  `A` is *weakly sign-symmetric* if
`A[α, β] A[β, α] ≥ 0` for all minors of dispersal `1` (the *almost
principal* minors); a weakly sign-symmetric `P`-matrix is called GKK.

Verbatim (Problem 5):

> **5. Newton's inequalities.** For a matrix `A`, let
> `c_j := ∑_{#α = j} A[α] / C(n, j)`, `j = 0, …, n`.
> Does any GKK τ-matrix `A` satisfy the inequalities
> `c_j^2 ≥ c_{j-1} c_{j+1}`, `j = 1, …, n-1`?

## Status

Open in general (the paper: "Whether GKK matrices satisfy Newton's
inequalities, however, is not known yet"; subproblem 5a, `M`-matrices,
was later proved by Holtz, PAMS 133 (2005) 711–717).

## Target formalized here (special case `n = 3`)

For every real `3 × 3` weakly sign-symmetric matrix `A` (no `P`-matrix or
τ-hypothesis is needed), Newton's inequalities `c_j^2 ≥ c_{j-1} c_{j+1}`
hold for `j = 1, 2`.  Equivalently, with `E₁ = trace A`,
`E₂ = ∑_{i<j} (a_ii a_jj - a_ij a_ji)`, `E₃ = det A`:
`3 E₂ ≤ E₁²` and `3 E₁ E₃ ≤ E₂²`.  In particular every GKK τ-matrix of
order `3` satisfies (newton).

Proof: `E₁² - 3E₂ = ∑ a_ii² - ∑_{i<j} a_ii a_jj + 3 ∑_{i<j} a_ij a_ji`;
for `j = 2` use the Desnanot–Jacobi identities
`a_kk det A = A[ki] A[kj] - A[{k,i},{k,j}] A[{k,j},{k,i}]`, sum over `k`,
and `3(xy + yz + zx) ≤ (x + y + z)²`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.GkkTauMatricesHoltz

open Finset

/-! ## Definitions mirroring the paper -/

/-- The principal minor `A[α] = det A(α, α)` of a real `n × n` matrix, for a
set `α` of indices.  The rows and columns are indexed by the subtype `↥α`, so
no ordering is involved; by convention `A[∅] = 1` (the determinant of the
empty matrix). -/
noncomputable def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (α : Finset (Fin n)) : ℝ :=
  (A.submatrix ((↑) : α → Fin n) ((↑) : α → Fin n)).det

/-- `E_j(A) = ∑_{#α = j} A[α]`, the sum of the `j × j` principal minors. -/
noncomputable def principalMinorSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : ℕ) : ℝ :=
  ∑ α ∈ (univ : Finset (Fin n)).powersetCard j, principalMinor A α

/-- The normalized coefficient `c_j = ∑_{#α = j} A[α] / C(n, j)` of
Holtz–Schneider, Problem 5.  It is meaningful for `j ≤ n` (otherwise the
binomial coefficient vanishes and the value is the junk `0`). -/
noncomputable def newtonCoeff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (j : ℕ) : ℝ :=
  principalMinorSum A j / (n.choose j : ℝ)

/-- `A` is *weakly sign-symmetric*: `A[α, β] A[β, α] ≥ 0` for every pair of
increasing sequences `α, β` of the same length `k` whose minor has dispersal
`#α - #(α ∩ β) = #(α \ β) = 1` (the almost principal minors). -/
def WeaklySignSymmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (k : ℕ) (α β : Fin k → Fin n), StrictMono α → StrictMono β →
    (univ.image α \ univ.image β).card = 1 →
      0 ≤ (A.submatrix α β).det * (A.submatrix β α).det

/-- `A` is a `P`-matrix: every nonempty principal minor is positive. -/
def IsPMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ α : Finset (Fin n), α.Nonempty → 0 < principalMinor A α

/-- `A` is GKK (Gantmacher–Krein–Kotelyansky): a weakly sign-symmetric
`P`-matrix. -/
def IsGKK {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsPMatrix A ∧ WeaklySignSymmetric A

/-! ## Computing principal minors -/

/-- A principal minor can be computed along any enumeration `f : Fin k → Fin n`
of `α` without repetition. -/
theorem principalMinor_eq_det_submatrix {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (α : Finset (Fin n)) (f : Fin k → Fin n) (hf : Function.Injective f)
    (hα : ∀ x, x ∈ α ↔ ∃ i, f i = x) :
    principalMinor A α = (A.submatrix f f).det := by
  let e : Fin k ≃ α := Equiv.ofBijective (fun i => ⟨f i, (hα _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j hij => hf (by simpa using hij), fun x => by
      obtain ⟨i, hi⟩ := (hα x.1).1 x.2
      exact ⟨i, Subtype.ext hi⟩⟩
  unfold principalMinor
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

/-- The `2 × 2` principal minors of a `3 × 3` matrix. -/
theorem principalMinor_pair_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    principalMinor A {0, 1} = A 0 0 * A 1 1 - A 0 1 * A 1 0 ∧
    principalMinor A {0, 2} = A 0 0 * A 2 2 - A 0 2 * A 2 0 ∧
    principalMinor A {1, 2} = A 1 1 * A 2 2 - A 1 2 * A 2 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [principalMinor_eq_det_submatrix A _ ![0, 1] (by decide) (by decide),
      Matrix.det_fin_two]
    simp
  · rw [principalMinor_eq_det_submatrix A _ ![0, 2] (by decide) (by decide),
      Matrix.det_fin_two]
    simp
  · rw [principalMinor_eq_det_submatrix A _ ![1, 2] (by decide) (by decide),
      Matrix.det_fin_two]
    simp

/-- `E₀(A) = 1` (the convention `A[∅] = 1`). -/
theorem principalMinorSum_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    principalMinorSum A 0 = 1 := by
  simp [principalMinorSum, principalMinor]

/-- `E₁(A) = trace A` for a `3 × 3` matrix. -/
theorem principalMinorSum_one_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    principalMinorSum A 1 = A.trace := by
  have hP : (univ : Finset (Fin 3)).powersetCard 1 = {{0}, {1}, {2}} := by decide
  have h0 : principalMinor A {0} = A 0 0 := by
    rw [principalMinor_eq_det_submatrix A _ ![0] (by decide) (by decide),
      Matrix.det_fin_one]
    simp
  have h1 : principalMinor A {1} = A 1 1 := by
    rw [principalMinor_eq_det_submatrix A _ ![1] (by decide) (by decide),
      Matrix.det_fin_one]
    simp
  have h2 : principalMinor A {2} = A 2 2 := by
    rw [principalMinor_eq_det_submatrix A _ ![2] (by decide) (by decide),
      Matrix.det_fin_one]
    simp
  rw [principalMinorSum, hP, sum_insert (by decide), sum_insert (by decide),
    sum_singleton, h0, h1, h2, Matrix.trace_fin_three]
  ring

/-- `E₂(A) = ∑_{i<j} (a_ii a_jj - a_ij a_ji)` for a `3 × 3` matrix. -/
theorem principalMinorSum_two_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    principalMinorSum A 2 = (A 0 0 * A 1 1 - A 0 1 * A 1 0) +
      (A 0 0 * A 2 2 - A 0 2 * A 2 0) + (A 1 1 * A 2 2 - A 1 2 * A 2 1) := by
  have hP : (univ : Finset (Fin 3)).powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}} := by
    decide
  obtain ⟨h01, h02, h12⟩ := principalMinor_pair_fin_three A
  rw [principalMinorSum, hP, sum_insert (by decide), sum_insert (by decide),
    sum_singleton, h01, h02, h12]
  ring

/-- `E₃(A) = det A` for a `3 × 3` matrix. -/
theorem principalMinorSum_three_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    principalMinorSum A 3 = A.det := by
  have hP : (univ : Finset (Fin 3)).powersetCard 3 = {univ} := by decide
  rw [principalMinorSum, hP, sum_singleton,
    principalMinor_eq_det_submatrix A _ id Function.injective_id (by simp)]
  rfl

/-! ## Extracting the almost principal minors of order `1` and `2` -/

/-- Weak sign-symmetry of a `3 × 3` matrix yields `a_ij a_ji ≥ 0` (dispersal-one
minors of order `1`) and the three products of almost principal `2 × 2`
minors `A[{k,i},{k,j}] A[{k,j},{k,i}] ≥ 0`. -/
theorem WeaklySignSymmetric.fin_three_entries {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : WeaklySignSymmetric A) :
    0 ≤ A 0 1 * A 1 0 ∧ 0 ≤ A 0 2 * A 2 0 ∧ 0 ≤ A 1 2 * A 2 1 ∧
    0 ≤ (A 0 0 * A 1 2 - A 0 2 * A 1 0) * (A 0 0 * A 2 1 - A 0 1 * A 2 0) ∧
    0 ≤ (A 0 1 * A 1 2 - A 0 2 * A 1 1) * (A 1 0 * A 2 1 - A 1 1 * A 2 0) ∧
    0 ≤ (A 0 1 * A 2 2 - A 0 2 * A 2 1) * (A 1 0 * A 2 2 - A 1 2 * A 2 0) := by
  have one : ∀ i j : Fin 3, i ≠ j → 0 ≤ A i j * A j i := by
    intro i j hij
    have hcard : (univ.image (![i] : Fin 1 → Fin 3) \ univ.image ![j]).card = 1 := by
      revert i j; decide
    have h := hA 1 ![i] ![j] (Subsingleton.strictMono _) (Subsingleton.strictMono _) hcard
    rw [Matrix.det_fin_one, Matrix.det_fin_one] at h
    simpa using h
  have two : ∀ α β : Fin 2 → Fin 3, StrictMono α → StrictMono β →
      (univ.image α \ univ.image β).card = 1 →
      0 ≤ (A (α 0) (β 0) * A (α 1) (β 1) - A (α 0) (β 1) * A (α 1) (β 0)) *
        (A (β 0) (α 0) * A (β 1) (α 1) - A (β 0) (α 1) * A (β 1) (α 0)) := by
    intro α β hα hβ hcard
    have h := hA 2 α β hα hβ hcard
    simpa [Matrix.det_fin_two] using h
  have sm01 : StrictMono (![0, 1] : Fin 2 → Fin 3) := by
    rw [Fin.strictMono_iff_lt_succ]; decide
  have sm02 : StrictMono (![0, 2] : Fin 2 → Fin 3) := by
    rw [Fin.strictMono_iff_lt_succ]; decide
  have sm12 : StrictMono (![1, 2] : Fin 2 → Fin 3) := by
    rw [Fin.strictMono_iff_lt_succ]; decide
  have t0 := two ![0, 1] ![0, 2] sm01 sm02 (by decide)
  have t1 := two ![0, 1] ![1, 2] sm01 sm12 (by decide)
  have t2 := two ![0, 2] ![1, 2] sm02 sm12 (by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at t0 t1 t2
  refine ⟨one 0 1 (by decide), one 0 2 (by decide), one 1 2 (by decide), ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-! ## Sign-symmetric examples -/

/-- Every real symmetric matrix is weakly sign-symmetric, since then
`A[β, α] = A[α, β]` by transposition. -/
theorem weaklySignSymmetric_of_isSymm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) : WeaklySignSymmetric A := by
  intro k α β _ _ _
  have hT : (A.submatrix β α).det = (A.submatrix α β).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_submatrix, hA.eq]
  rw [hT]
  exact mul_self_nonneg _

/-- The identity matrix is GKK (a non-vacuity witness for `IsGKK`). -/
theorem isGKK_one (n : ℕ) : IsGKK (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨fun α _ => ?_, weaklySignSymmetric_of_isSymm Matrix.isSymm_one⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ).submatrix ((↑) : α → Fin n) ((↑) : α → Fin n) = 1 :=
    Matrix.submatrix_one _ Subtype.val_injective
  simp [principalMinor, h1]

/-! ## Main results -/

/-- **Newton's inequalities for weakly sign-symmetric `3 × 3` matrices, in
`E`-form.**  For every real weakly sign-symmetric `3 × 3` matrix `A`,
`3 E₂ ≤ E₁²` and `3 E₁ E₃ ≤ E₂²`, where `E_j` is the sum of the `j × j`
principal minors.  (Order-3 case of Holtz–Schneider, arXiv:math/0109030,
Problem 5, without the `P`-matrix or τ-hypothesis.) -/
theorem newton_principalMinorSum_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : WeaklySignSymmetric A) :
    3 * principalMinorSum A 2 ≤ principalMinorSum A 1 ^ 2 ∧
      3 * principalMinorSum A 1 * principalMinorSum A 3 ≤ principalMinorSum A 2 ^ 2 := by
  obtain ⟨hbd, hcg, hfh, t0, t1, t2⟩ := hA.fin_three_entries
  rw [principalMinorSum_one_fin_three, principalMinorSum_two_fin_three,
    principalMinorSum_three_fin_three, Matrix.trace_fin_three, Matrix.det_fin_three]
  constructor
  · -- `E₁² - 3E₂ = ∑ a_ii² - ∑_{i<j} a_ii a_jj + 3 ∑_{i<j} a_ij a_ji ≥ 0`.
    nlinarith [sq_nonneg (A 0 0 - A 1 1), sq_nonneg (A 0 0 - A 2 2),
      sq_nonneg (A 1 1 - A 2 2)]
  · set D := A.det with hD
    rw [Matrix.det_fin_three] at hD
    set x := A 0 0 * A 1 1 - A 0 1 * A 1 0 with hx
    set y := A 0 0 * A 2 2 - A 0 2 * A 2 0 with hy
    set z := A 1 1 * A 2 2 - A 1 2 * A 2 1 with hz
    -- Desnanot–Jacobi: `a_kk det A = A[ki] A[kj] - A[{k,i},{k,j}] A[{k,j},{k,i}]`.
    have k0 : A 0 0 * D = x * y -
        (A 0 0 * A 1 2 - A 0 2 * A 1 0) * (A 0 0 * A 2 1 - A 0 1 * A 2 0) := by
      rw [hD, hx, hy]; ring
    have k1 : A 1 1 * D = x * z -
        (A 0 1 * A 1 2 - A 0 2 * A 1 1) * (A 1 0 * A 2 1 - A 1 1 * A 2 0) := by
      rw [hD, hx, hz]; ring
    have k2 : A 2 2 * D = y * z -
        (A 0 1 * A 2 2 - A 0 2 * A 2 1) * (A 1 0 * A 2 2 - A 1 2 * A 2 0) := by
      rw [hD, hy, hz]; ring
    have hsum : (A 0 0 + A 1 1 + A 2 2) * D ≤ x * y + x * z + y * z := by
      linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- **Newton's inequalities for weakly sign-symmetric `3 × 3` matrices.**
For every real weakly sign-symmetric `3 × 3` matrix `A` and `j = 1, 2`,
`c_{j-1} c_{j+1} ≤ c_j²`, where `c_j = ∑_{#α = j} A[α] / C(3, j)`.  This
answers Holtz–Schneider (arXiv:math/0109030), Problem 5, affirmatively for
`n = 3`, without needing the `P`-matrix or τ-hypothesis. -/
theorem newton_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : WeaklySignSymmetric A)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    newtonCoeff A (j - 1) * newtonCoeff A (j + 1) ≤ newtonCoeff A j ^ 2 := by
  obtain ⟨h1, h2⟩ := newton_principalMinorSum_fin_three A hA
  interval_cases j
  · simp only [newtonCoeff, Nat.reduceSub, Nat.reduceAdd, principalMinorSum_zero]
    norm_num [Nat.choose]
    nlinarith
  · simp only [newtonCoeff, Nat.reduceSub, Nat.reduceAdd]
    norm_num [Nat.choose]
    nlinarith

/-- **GKK matrices of order 3 satisfy Newton's inequalities** (Holtz–Schneider,
arXiv:math/0109030, Problem 5, case `n = 3`): if `A` is a real `3 × 3` GKK
matrix, then `c_{j-1} c_{j+1} ≤ c_j²` for `j = 1, 2`. -/
theorem newton_of_isGKK_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsGKK A)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    newtonCoeff A (j - 1) * newtonCoeff A (j + 1) ≤ newtonCoeff A j ^ 2 :=
  newton_fin_three A hA.2 j hj1 hj2

/-! ## Ground truth and sharpness checks -/

/-- `E₂` of the `3 × 3` identity is `3`, so `c₂ = 1`. -/
example : principalMinorSum (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 = 3 := by
  rw [principalMinorSum_two_fin_three]
  simp only [Matrix.one_apply_eq, mul_one, Fin.isValue, ne_eq, zero_ne_one,
    not_false_eq_true, Matrix.one_apply_ne, one_ne_zero, mul_zero, sub_zero, Fin.reduceEq]
  norm_num

/-- A concrete `E`-computation: for `!![1, 2, 0; 3, 4, 0; 0, 0, 5]`,
`E₁ = 10`, `E₂ = (4 - 6) + 5 + 20 = 23`, `E₃ = -10`. -/
example :
    principalMinorSum !![(1 : ℝ), 2, 0; 3, 4, 0; 0, 0, 5] 1 = 10 ∧
    principalMinorSum !![(1 : ℝ), 2, 0; 3, 4, 0; 0, 0, 5] 2 = 23 ∧
    principalMinorSum !![(1 : ℝ), 2, 0; 3, 4, 0; 0, 0, 5] 3 = -10 := by
  rw [principalMinorSum_one_fin_three, principalMinorSum_two_fin_three,
    principalMinorSum_three_fin_three, Matrix.trace_fin_three, Matrix.det_fin_three]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val, one_mul, mul_zero,
    sub_zero, add_zero, zero_mul]
  norm_num

/-- Satisfiability of the hypothesis at a non-diagonal matrix. -/
example : WeaklySignSymmetric !![(2 : ℝ), 1, 0; 1, 2, 1; 0, 1, 2] := by
  apply weaklySignSymmetric_of_isSymm
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The weak sign-symmetry hypothesis cannot be dropped: the rotation block
`!![0, -1, 0; 1, 0, 0; 0, 0, 0]` has `E₁ = 0`, `E₂ = 1`, so `3 E₂ ≤ E₁²` fails;
it is not weakly sign-symmetric since `a₁₂ a₂₁ = -1`. -/
example :
    ¬ WeaklySignSymmetric !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] ∧
    ¬ 3 * principalMinorSum !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] 2 ≤
        principalMinorSum !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0] 1 ^ 2 := by
  constructor
  · intro h
    have h01 := h.fin_three_entries.1
    norm_num at h01
  · rw [principalMinorSum_one_fin_three, principalMinorSum_two_fin_three,
      Matrix.trace_fin_three]
    simp

end Candidates.GkkTauMatricesHoltz
