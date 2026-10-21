/-
# Magnitude and matrix inequalities: `Mag(X) ≤ #X` for negative type

## Source

* arXiv 2509.24221, Kiyonori Gomi and Mark Meckes, *Magnitude and matrix
  inequalities*.
* Section 1, Theorem 1.1 (`thm:main_upper_bound`), verbatim:
  "If $X$ is a finite metric space of negative type, then
  $\Mag(X) \le \# X$."
* Section 3.1, Theorem 3.1 (`thm:main_upper_bound_repeated`), verbatim:
  "Let $X$ be an $n$-point metric space. If $X$ is of negative type, then
  we have $\Mag(tX) \le n$ for any $t > 0$."
* Section 3.1, Theorem 3.2 (`thm:weak_assumption`), verbatim:
  "Let $X = (X, d)$ be an $n$-point metric space. If
  $\frac{1}{2}X = (X, \frac{1}{2}d)$ is positive definite, then
  $\Mag(X) \le n$."
* Section 2 definitions: the zeta matrix is $Z_X = (e^{-d(i,j)})$; a
  weighting is $w \in \R^n$ with $Z_X w = \1$, and $\Mag(X) = \sum_i w_i$
  (independent of the weighting); $tX = (X, t d)$; $X$ is positive definite
  when $Z_X$ is positive definite, and of negative type when $Z_{tX}$ is
  positive definite for all $t > 0$.

Recorded 2026-10-21.

## Status

Proved in the paper (via Styan's inequality
$2 (R \circ R)^{-1} \le R^{-1} \circ R + I$).  The strict inequality
$\Mag(X) < \#X$ for negative type and $\#X > 1$ was proved later by Asao and
Gomi (cited in the paper as [AsGo, Theorem 1.1]).

## What this module formalizes

The argument here does not use Styan's inequality.  Write the half-scale
zeta matrix as a Gram matrix `R = Bᵀ B` (positive semidefiniteness), so its
columns `b_i` are unit vectors.  For `S = ∑ᵢ wᵢ bᵢ bᵢᵀ` one has
`tr S = ∑ w` and `‖S‖_F² = wᵀ (R ∘ R) w = wᵀ Z w = ∑ w`, and Cauchy–Schwarz on
the diagonal of `S` gives `(∑ w)² ≤ n ∑ w`.

* `gram_sq_bound`: for unit vectors `bᵢ ∈ ℝᵐ` and any `v`,
  `(∑ vᵢ)² ≤ m ∑ᵢⱼ vᵢ vⱼ ⟨bᵢ, bⱼ⟩²`.
* `sum_le_card_of_posSemidef`: matrix form, `R` positive semidefinite with
  unit diagonal and `(R ∘ R) w = 1` imply `∑ w ≤ n`.
* `sum_lt_card_of_posDef`: strict form when `R` is positive definite and has a
  nonzero off-diagonal entry.
* `weighting_sum_le_card_of_posSemidef` (strengthening of Theorem 3.2:
  semidefinite suffices), `thm_3_2`, `thm_3_1`, `thm_1_1`.
* `weighting_sum_lt_card_of_posDef`: `Mag(X) < #X` whenever `(X, d/2)` is
  positive definite and `#X ≥ 2` (implies the Asao–Gomi strict bound for
  negative type).
* Non-vacuity: equilateral finite spaces are of negative type and carry an
  explicit weighting (`isNegativeType_of_equilateral`,
  `isWeighting_const_of_equilateral`), instantiated on the two-point space
  `{0, 1} ⊆ ℝ`.

The metric statements are made over `PseudoMetricSpace`, which contains every
metric space; the proofs never use `d(x, y) = 0 → x = y`.
-/
import Mathlib

set_option autoImplicit false

namespace PolynomialClosure.MagnitudeMatrixInequalitiesGomi

open Finset Matrix

/-! ## The Gram-vector inequality -/

/-- Trace identity: for unit vectors `bᵢ`, the trace of `∑ᵢ vᵢ bᵢ bᵢᵀ` is `∑ᵢ vᵢ`. -/
theorem gram_trace {m n : Type*} [Fintype m] [Fintype n] (b : n → m → ℝ)
    (hb : ∀ i, ∑ k, b i k ^ 2 = 1) (v : n → ℝ) :
    ∑ k, ∑ i, v i * b i k * b i k = ∑ i, v i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← mul_one (v i), ← hb i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Frobenius identity: the squared Frobenius norm of `∑ᵢ vᵢ bᵢ bᵢᵀ` equals
`∑ᵢⱼ vᵢ vⱼ ⟨bᵢ, bⱼ⟩²`. -/
theorem gram_frob {m n : Type*} [Fintype m] [Fintype n] (b : n → m → ℝ) (v : n → ℝ) :
    ∑ k, ∑ l, (∑ i, v i * b i k * b i l) ^ 2 =
      ∑ i, ∑ j, v i * v j * (∑ k, b i k * b j k) ^ 2 := by
  set F : n → n → m → m → ℝ := fun i j k l => v i * v j * (b i k * b j k) * (b i l * b j l)
    with hF
  calc ∑ k, ∑ l, (∑ i, v i * b i k * b i l) ^ 2 = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [hF, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
    _ = ∑ i, ∑ j, v i * v j * (∑ k, b i k * b j k) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [hF]
        ring

/-- **Gram-vector inequality.** If `b₁, …, bₙ` are unit vectors in `ℝᵐ`, then for every
`v ∈ ℝⁿ`, `(∑ᵢ vᵢ)² ≤ m · ∑ᵢⱼ vᵢ vⱼ ⟨bᵢ, bⱼ⟩²`. -/
theorem gram_sq_bound {m n : Type*} [Fintype m] [Fintype n] (b : n → m → ℝ)
    (hb : ∀ i, ∑ k, b i k ^ 2 = 1) (v : n → ℝ) :
    (∑ i, v i) ^ 2 ≤
      (Fintype.card m : ℝ) * ∑ i, ∑ j, v i * v j * (∑ k, b i k * b j k) ^ 2 := by
  set S : m → m → ℝ := fun k l => ∑ i, v i * b i k * b i l with hS
  have htrace : ∑ k, S k k = ∑ i, v i := gram_trace b hb v
  have hfrob : ∑ k, ∑ l, S k l ^ 2 = ∑ i, ∑ j, v i * v j * (∑ k, b i k * b j k) ^ 2 :=
    gram_frob b v
  have hdiag : ∑ k, S k k ^ 2 ≤ ∑ k, ∑ l, S k l ^ 2 := by
    refine Finset.sum_le_sum fun k _ => ?_
    exact Finset.single_le_sum (f := fun l => S k l ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ k)
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset m)) (f := fun k => S k k)
  rw [← htrace, ← hfrob]
  calc (∑ k, S k k) ^ 2 ≤ (Fintype.card m : ℝ) * ∑ k, S k k ^ 2 := by
        simpa using hcs
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)

/-! ## Matrix form -/

open scoped MatrixOrder in
/-- A real positive semidefinite matrix is a Gram matrix: `R = Bᵀ B` for some square `B`. -/
theorem exists_eq_transpose_mul_self_of_posSemidef {n : Type*} [Fintype n]
    {R : Matrix n n ℝ} (hR : R.PosSemidef) :
    ∃ B : Matrix n n ℝ, R = Bᵀ * B := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  exact ⟨B, by simpa [Matrix.star_eq_conjTranspose] using hB⟩

/-- If `R = Bᵀ B` and `(R ∘ R) w = 1`, then `∑ᵢⱼ wᵢ wⱼ ⟨bᵢ, bⱼ⟩² = ∑ᵢ wᵢ`, where `bᵢ` is the
`i`-th column of `B`. -/
theorem quad_hadamard_eq_sum {n : Type*} [Fintype n] (R B : Matrix n n ℝ)
    (hRB : R = Bᵀ * B) (w : n → ℝ) (hw : (R ⊙ R) *ᵥ w = 1) :
    ∑ i, ∑ j, w i * w j * (∑ k, B k i * B k j) ^ 2 = ∑ i, w i := by
  have hRij : ∀ i j, R i j = ∑ k, B k i * B k j := by
    intro i j
    rw [hRB, Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
  have hrow : ∀ i, ∑ j, R i j * R i j * w j = 1 := by
    intro i
    simpa [Matrix.mulVec, dotProduct, Matrix.hadamard] using congrFun hw i
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← mul_one (w i), ← hrow i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hRij i j]
  ring

/-- Columns of a Gram factor of a matrix with unit diagonal are unit vectors. -/
theorem sum_sq_col_eq_one {n : Type*} [Fintype n] (R B : Matrix n n ℝ)
    (hRB : R = Bᵀ * B) (hdiag : ∀ i, R i i = 1) (i : n) :
    ∑ k, B k i ^ 2 = 1 := by
  rw [← hdiag i, hRB, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, sq]

/-- **Matrix form of the upper bound.** If `R` is a real positive semidefinite matrix with
unit diagonal and `w` solves `(R ∘ R) w = 1` (Hadamard square), then `∑ᵢ wᵢ ≤ n`. -/
theorem sum_le_card_of_posSemidef {n : Type*} [Fintype n] (R : Matrix n n ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (w : n → ℝ)
    (hw : (R ⊙ R) *ᵥ w = 1) : ∑ i, w i ≤ Fintype.card n := by
  obtain ⟨B, hRB⟩ := exists_eq_transpose_mul_self_of_posSemidef hR
  have hgram := gram_sq_bound (fun i k => B k i) (sum_sq_col_eq_one R B hRB hdiag) w
  rw [quad_hadamard_eq_sum R B hRB w hw] at hgram
  rcases le_or_gt (∑ i, w i) 0 with hle | hpos
  · exact hle.trans (Nat.cast_nonneg _)
  · nlinarith

/-- **Strict matrix form.** If `R` is a real positive definite matrix with unit diagonal and
some nonzero off-diagonal entry `R i j` (`i ≠ j`), and `w` solves `(R ∘ R) w = 1`, then
`∑ᵢ wᵢ < n`. -/
theorem sum_lt_card_of_posDef {n : Type*} [Fintype n] (R : Matrix n n ℝ)
    (hR : R.PosDef) (hdiag : ∀ i, R i i = 1) {i j : n} (hij : i ≠ j) (hRij : R i j ≠ 0)
    (w : n → ℝ) (hw : (R ⊙ R) *ᵥ w = 1) : ∑ i, w i < Fintype.card n := by
  classical
  have hle := sum_le_card_of_posSemidef R hR.posSemidef hdiag w hw
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨B, hRB⟩ := exists_eq_transpose_mul_self_of_posSemidef hR.posSemidef
  set N : ℝ := (Fintype.card n : ℝ) with hNdef
  have hN : 0 < N := by
    have : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [hNdef]
    exact_mod_cast this
  set b : n → n → ℝ := fun i k => B k i with hb
  set S : n → n → ℝ := fun k l => ∑ i, w i * b i k * b i l with hS
  have hcol : ∀ i, ∑ k, b i k ^ 2 = 1 := sum_sq_col_eq_one R B hRB hdiag
  have htrace : ∑ k, S k k = N := (gram_trace b hcol w).trans heq
  have hfrob : ∑ k, ∑ l, S k l ^ 2 = N :=
    (gram_frob b w).trans ((quad_hadamard_eq_sum R B hRB w hw).trans heq)
  have hdle : ∀ k, S k k ^ 2 ≤ ∑ l, S k l ^ 2 := fun k =>
    Finset.single_le_sum (f := fun l => S k l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  have hdiagsum : ∑ k, S k k ^ 2 ≤ N := hfrob ▸ Finset.sum_le_sum fun k _ => hdle k
  have hcs : (∑ k, S k k) ^ 2 ≤ N * ∑ k, S k k ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset n)) (f := fun k => S k k)
  rw [htrace] at hcs
  have hsq : ∑ k, S k k ^ 2 = N := by nlinarith
  -- diagonal entries of `S` are all `1`
  have hSdiag : ∀ k, S k k = 1 := by
    have hexp : ∑ k, (S k k - 1) ^ 2 = ∑ k, S k k ^ 2 - 2 * ∑ k, S k k + N := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNdef]
    have hzero : ∑ k, (S k k - 1) ^ 2 = 0 := by rw [hexp, hsq, htrace]; ring
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (S k k - 1))).mp hzero k
      (Finset.mem_univ k)
    nlinarith [sq_nonneg (S k k - 1)]
  -- off-diagonal entries of `S` vanish
  have hSoff : ∀ k l, k ≠ l → S k l = 0 := by
    have hzero : ∑ k, (∑ l, S k l ^ 2 - S k k ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib, hfrob, hsq, sub_self]
    intro k l hkl
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.mpr (hdle k))).mp
      hzero k (Finset.mem_univ k)
    have herase : ∑ l ∈ Finset.univ.erase k, S k l ^ 2 = 0 := by
      have := Finset.add_sum_erase Finset.univ (fun l => S k l ^ 2) (Finset.mem_univ k)
      linarith
    have hl := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (S k l))).mp herase l
      (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hl
  -- hence `B diag(w) Bᵀ = 1`
  have hSone : B * diagonal w * Bᵀ = 1 := by
    ext k l
    have hent : (B * diagonal w * Bᵀ) k l = S k l := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply, hS, hb]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hent]
    by_cases hkl : k = l
    · subst hkl
      rw [hSdiag, Matrix.one_apply_eq]
    · rw [hSoff k l hkl, Matrix.one_apply_ne hkl]
  have hRDR : R * (diagonal w * R) = R * 1 := by
    calc R * (diagonal w * R) = Bᵀ * (B * diagonal w * Bᵀ) * B := by
          rw [hRB]; simp only [Matrix.mul_assoc]
      _ = R * 1 := by rw [hSone, Matrix.mul_one, Matrix.mul_one, hRB]
  have hDR : diagonal w * R = 1 := hR.isUnit.mul_left_cancel hRDR
  have hii : w i * R i i = 1 := by
    have := congrFun (congrFun hDR i) i
    rwa [Matrix.diagonal_mul, Matrix.one_apply_eq] at this
  have hij' : w i * R i j = 0 := by
    have := congrFun (congrFun hDR i) j
    rwa [Matrix.diagonal_mul, Matrix.one_apply_ne hij] at this
  rw [hdiag i, mul_one] at hii
  rw [hii, one_mul] at hij'
  exact hRij hij'

/-! ## Finite metric spaces: zeta matrices, weightings, negative type -/

/-- The zeta matrix `Z_{tX} = (e^{-t·d(x,y)})` of the rescaled space `tX = (X, t·d)`
(Section 2 of the paper; `zetaMatrix X 1` is `Z_X`). -/
noncomputable def zetaMatrix (X : Type*) [PseudoMetricSpace X] (t : ℝ) : Matrix X X ℝ :=
  Matrix.of fun x y => Real.exp (-(t * dist x y))

/-- `w` is a weighting on `tX`: `Z_{tX} w = 𝟙`.  When one exists, the magnitude `Mag(tX)` is
`∑ₓ w x` (independent of the weighting). -/
def IsWeighting (X : Type*) [Fintype X] [PseudoMetricSpace X] (t : ℝ) (w : X → ℝ) : Prop :=
  zetaMatrix X t *ᵥ w = 1

/-- `X` is of negative type: `Z_{tX}` is positive definite for every `t > 0`. -/
def IsNegativeType (X : Type*) [Fintype X] [PseudoMetricSpace X] : Prop :=
  ∀ t : ℝ, 0 < t → (zetaMatrix X t).PosDef

/-- Diagonal entries of a zeta matrix are `e⁰ = 1`. -/
@[simp] theorem zetaMatrix_apply_self {X : Type*} [PseudoMetricSpace X] (t : ℝ) (x : X) :
    zetaMatrix X t x x = 1 := by
  simp [zetaMatrix]

/-- Entries of a zeta matrix are positive. -/
theorem zetaMatrix_pos {X : Type*} [PseudoMetricSpace X] (t : ℝ) (x y : X) :
    0 < zetaMatrix X t x y :=
  Real.exp_pos _

/-- The Hadamard square of the half-scale zeta matrix is the zeta matrix:
`Z_{(t/2)X} ∘ Z_{(t/2)X} = Z_{tX}`. -/
theorem zetaMatrix_half_hadamard (X : Type*) [PseudoMetricSpace X] (t : ℝ) :
    zetaMatrix X (t / 2) ⊙ zetaMatrix X (t / 2) = zetaMatrix X t := by
  ext x y
  simp only [Matrix.hadamard, zetaMatrix, Matrix.of_apply, ← Real.exp_add]
  congr 1
  ring

/-- **Upper bound, semidefinite form (strengthens Theorem 3.2).** If the half-scale zeta
matrix `Z_{(t/2)X}` of a finite (pseudo)metric space is positive *semi*definite, then every
weighting `w` on `tX` has `Mag(tX) = ∑ w ≤ #X`. -/
theorem weighting_sum_le_card_of_posSemidef {X : Type*} [Fintype X] [PseudoMetricSpace X]
    {t : ℝ} (hR : (zetaMatrix X (t / 2)).PosSemidef) {w : X → ℝ} (hw : IsWeighting X t w) :
    ∑ x, w x ≤ Fintype.card X := by
  refine sum_le_card_of_posSemidef (zetaMatrix X (t / 2)) hR (zetaMatrix_apply_self _) w ?_
  rw [zetaMatrix_half_hadamard]
  exact hw

/-- **Theorem 3.2 (Gomi–Meckes, arXiv 2509.24221).** Let `X` be an `n`-point metric space. If
`½X = (X, ½d)` is positive definite, then `Mag(X) ≤ n`: every weighting `w` (`Z_X w = 𝟙`)
satisfies `∑ w ≤ #X`. -/
theorem thm_3_2 {X : Type*} [Fintype X] [PseudoMetricSpace X]
    (hX : (zetaMatrix X (1 / 2)).PosDef) {w : X → ℝ} (hw : IsWeighting X 1 w) :
    ∑ x, w x ≤ Fintype.card X :=
  weighting_sum_le_card_of_posSemidef (t := 1) hX.posSemidef hw

/-- **Theorem 3.1 (Gomi–Meckes, arXiv 2509.24221).** Let `X` be an `n`-point metric space of
negative type. Then `Mag(tX) ≤ n` for every `t > 0`: every weighting `w` on `tX` satisfies
`∑ w ≤ #X`. -/
theorem thm_3_1 {X : Type*} [Fintype X] [PseudoMetricSpace X] (hX : IsNegativeType X)
    {t : ℝ} (ht : 0 < t) {w : X → ℝ} (hw : IsWeighting X t w) :
    ∑ x, w x ≤ Fintype.card X :=
  weighting_sum_le_card_of_posSemidef (hX (t / 2) (half_pos ht)).posSemidef hw

/-- **Theorem 1.1 (Gomi–Meckes, arXiv 2509.24221).** If `X` is a finite metric space of
negative type, then `Mag(X) ≤ #X`: every weighting `w` (`Z_X w = 𝟙`) satisfies `∑ w ≤ #X`. -/
theorem thm_1_1 {X : Type*} [Fintype X] [PseudoMetricSpace X] (hX : IsNegativeType X)
    {w : X → ℝ} (hw : IsWeighting X 1 w) :
    ∑ x, w x ≤ Fintype.card X :=
  thm_3_1 hX one_pos hw

/-- **Strict upper bound.** If the half-scale zeta matrix `Z_{(t/2)X}` of a finite
(pseudo)metric space with at least two points is positive definite, then every weighting `w`
on `tX` satisfies `Mag(tX) = ∑ w < #X`. -/
theorem weighting_sum_lt_card_of_posDef {X : Type*} [Fintype X] [PseudoMetricSpace X]
    {t : ℝ} (hR : (zetaMatrix X (t / 2)).PosDef) (hcard : 1 < Fintype.card X)
    {w : X → ℝ} (hw : IsWeighting X t w) :
    ∑ x, w x < Fintype.card X := by
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
  refine sum_lt_card_of_posDef (zetaMatrix X (t / 2)) hR (zetaMatrix_apply_self _) hxy
    (zetaMatrix_pos _ x y).ne' w ?_
  rw [zetaMatrix_half_hadamard]
  exact hw

/-- **Strict upper bound for negative type** (the Asao–Gomi strengthening of Theorem 1.1).
If `X` is a finite metric space of negative type with `#X ≥ 2`, then `Mag(tX) < #X` for every
`t > 0`. -/
theorem weighting_sum_lt_card_of_isNegativeType {X : Type*} [Fintype X] [PseudoMetricSpace X]
    (hX : IsNegativeType X) (hcard : 1 < Fintype.card X) {t : ℝ} (ht : 0 < t)
    {w : X → ℝ} (hw : IsWeighting X t w) :
    ∑ x, w x < Fintype.card X :=
  weighting_sum_lt_card_of_posDef (hX (t / 2) (half_pos ht)) hcard hw

/-! ## Non-vacuity: equilateral spaces -/

/-- In an equilateral space (all distinct points at distance `c`), the zeta matrix of `tX` is
`(1 - a)·I + a·J` with `a = e^{-tc}` and `J` the all-ones matrix. -/
theorem zetaMatrix_eq_of_equilateral {X : Type*} [Fintype X] [DecidableEq X]
    [PseudoMetricSpace X] {c : ℝ} (h : ∀ x y : X, x ≠ y → dist x y = c) (t : ℝ) :
    zetaMatrix X t = (1 - Real.exp (-(t * c))) • (1 : Matrix X X ℝ) +
      Real.exp (-(t * c)) • vecMulVec (fun _ => (1 : ℝ)) (star fun _ => (1 : ℝ)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [vecMulVec_apply]
  · simp [zetaMatrix, h x y hxy, hxy, vecMulVec_apply]

/-- A finite equilateral space (all distinct points at a common positive distance `c`) is of
negative type. -/
theorem isNegativeType_of_equilateral {X : Type*} [Fintype X] [PseudoMetricSpace X] {c : ℝ}
    (hc : 0 < c) (h : ∀ x y : X, x ≠ y → dist x y = c) : IsNegativeType X := by
  classical
  intro t ht
  rw [zetaMatrix_eq_of_equilateral h t]
  have hlt : Real.exp (-(t * c)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  refine Matrix.PosDef.add_posSemidef (Matrix.PosDef.one.smul (sub_pos.mpr hlt)) ?_
  exact (posSemidef_vecMulVec_self_star _).smul (Real.exp_pos _).le

/-- In a finite equilateral space with common distance `c`, the constant vector with value
`1 / (1 + (n - 1)·e^{-tc})` is a weighting on `tX`, where `n = #X`. -/
theorem isWeighting_const_of_equilateral {X : Type*} [Fintype X] [PseudoMetricSpace X]
    {c : ℝ} (h : ∀ x y : X, x ≠ y → dist x y = c) (t : ℝ) :
    IsWeighting X t fun _ =>
      1 / (1 + ((Fintype.card X : ℝ) - 1) * Real.exp (-(t * c))) := by
  classical
  set a := Real.exp (-(t * c)) with ha
  funext x
  have hne : Nonempty X := ⟨x⟩
  have hpos : 0 < 1 + ((Fintype.card X : ℝ) - 1) * a := by
    have hone : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
    nlinarith [Real.exp_pos (-(t * c))]
  have hrow : ∑ y, zetaMatrix X t x y = 1 + ((Fintype.card X : ℝ) - 1) * a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), zetaMatrix_apply_self]
    have hoff : ∀ y ∈ Finset.univ.erase x, zetaMatrix X t x y = a := by
      intro y hy
      simp [zetaMatrix, h x y (Finset.ne_of_mem_erase hy).symm, ha]
    rw [Finset.sum_congr rfl hoff, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ x), Finset.card_univ, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
    simp
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, ← Finset.sum_mul, hrow]
  field_simp

/-! ## Ground truth on small spaces -/

/-- The two-point metric space `{0, 1} ⊆ ℝ` (distance `1` between its points). -/
abbrev TwoPoint : Type := ↥({0, 1} : Finset ℝ)

/-- The two points of `TwoPoint` are at distance `1`. -/
theorem twoPoint_dist {x y : TwoPoint} (hxy : x ≠ y) : dist x y = 1 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rw [Subtype.dist_eq, Real.dist_eq]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp at hxy ⊢

/-- `TwoPoint` has two points. -/
theorem card_twoPoint : Fintype.card TwoPoint = 2 := by simp

/-- `TwoPoint` is of negative type. -/
theorem isNegativeType_twoPoint : IsNegativeType TwoPoint :=
  isNegativeType_of_equilateral one_pos fun _ _ hxy => twoPoint_dist hxy

/-- The weighting of `TwoPoint` is constant `(1 + e⁻¹)⁻¹`. -/
theorem isWeighting_twoPoint :
    IsWeighting TwoPoint 1 fun _ => (1 + Real.exp (-1))⁻¹ := by
  have hw := isWeighting_const_of_equilateral (X := TwoPoint) (c := 1)
    (fun _ _ hxy => twoPoint_dist hxy) 1
  rw [card_twoPoint] at hw
  norm_num at hw
  exact hw

/-- Ground truth: the off-diagonal entry of `Z_{TwoPoint}` is `e⁻¹`. -/
example : zetaMatrix TwoPoint 1 ⟨0, by simp⟩ ⟨1, by simp⟩ = Real.exp (-1) := by
  simp [zetaMatrix, Subtype.dist_eq, Real.dist_eq]

/-- Ground truth: the zeta matrix of a one-point space is `1`. -/
example (t : ℝ) : zetaMatrix PUnit t = 1 := by
  ext x y
  simp [zetaMatrix]

/-- Ground truth: the weighting of a one-point space is `1`, so `Mag(pt) = 1`. -/
example : IsWeighting PUnit 1 fun _ => 1 := by
  funext x
  simp [zetaMatrix, Matrix.mulVec, dotProduct]

/-- Satisfiability of the hypotheses of `thm_1_1` and the strict bound, jointly, at the
two-point space; here `Mag = 2 / (1 + e⁻¹) < 2`. -/
example : ∃ w : TwoPoint → ℝ,
    IsNegativeType TwoPoint ∧ IsWeighting TwoPoint 1 w ∧ 1 < Fintype.card TwoPoint ∧
      ∑ x, w x = 2 / (1 + Real.exp (-1)) :=
  ⟨_, isNegativeType_twoPoint, isWeighting_twoPoint, by rw [card_twoPoint]; norm_num, by
    simp only [Finset.sum_const, Finset.card_univ, card_twoPoint, nsmul_eq_mul]
    ring⟩

end PolynomialClosure.MagnitudeMatrixInequalitiesGomi
