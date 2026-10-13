import Mathlib.Algebra.Field.ZMod
import BilinearComplexity.BorderRankCompression
import BilinearComplexity.KoszulFlattening

/-!
The `n = 2` specialization of Landsberg--Ottaviani, Corollary 1.2
(arXiv:1112.6007v3), using their first-factor polynomial multiplication
projection and the p=1 Koszul flattening. The six-coordinate block inverse
uses no division, so the polynomial-closure conclusion holds over every field.
The general p=n-1 injectivity theorem and the bridge from classical sequential
border rank to polynomial closure are not asserted here.
-/

set_option autoImplicit false

namespace BilinearComplexity

/-- Degree-one polynomial multiplication on the first matrix factor. -/
def matMul22Projection (k : Type*) [Field k] : Matrix (Fin 3) (Fin 4) k :=
  fun t x => if t.val = ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm x).1.val +
    ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm x).2.val then 1 else 0

example : matMul22Projection ℚ 1 1 = 1 := rfl
example : matMul22Projection ℚ 2 0 = 0 := rfl

/-- The projected rectangular matrix multiplication tensor has the polynomial
multiplication indicator, retaining the shared rectangular index. -/
theorem matMul22Projection_contract_apply {k : Type*} [Field k] {ℓ : ℕ}
    (t : Fin 3) (i j : Fin 2) (h h' : Fin ℓ) :
    contract₁ (matMul22Projection k) (matMulTensor k 2 2 ℓ) t
      (finProdFinEquiv (j, h)) (finProdFinEquiv (h', i)) =
        if h = h' ∧ t.val = i.val + j.val then 1 else 0 := by
  simp only [contract₁, matMulTensor_apply, Equiv.symm_apply_apply]
  fin_cases i <;> fin_cases j <;> fin_cases t <;>
    simp [matMul22Projection, Fin.sum_univ_succ,
      finProdFinEquiv, Fin.divNat, Fin.modNat]

private abbrev p01 : KoszulPair 3 := ⟨(0, 1), by decide⟩
private abbrev p02 : KoszulPair 3 := ⟨(0, 2), by decide⟩
private abbrev p12 : KoszulPair 3 := ⟨(1, 2), by decide⟩

private def block (k : Type*) [Field k] : Matrix (Fin 6) (Fin 6) k :=
  ![![0,1,0,-1,0,0], ![0,0,1,0,0,0], ![0,0,0,0,0,1],
    ![-1,0,0,0,0,0], ![0,0,0,-1,0,0], ![0,0,1,0,-1,0]]

private def blockInverse (k : Type*) [Field k] : Matrix (Fin 6) (Fin 6) k :=
  ![![0,0,0,-1,0,0], ![1,0,0,0,-1,0], ![0,1,0,0,0,0],
    ![0,0,0,0,-1,0], ![0,1,0,0,0,-1], ![0,0,1,0,0,0]]

example : block ℚ 0 3 = -1 := rfl
example : blockInverse ℚ 1 4 = -1 := rfl

private theorem block_mul_inverse (k : Type*) [Field k] :
    block k * blockInverse k = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [block, blockInverse, Fin.sum_univ_succ]

private def groupedRows {ℓ : ℕ} (x : Fin ℓ × Fin 6) :
    Fin (ℓ * 2) × KoszulPair 3 :=
  ![(finProdFinEquiv (x.1, 0), p01), (finProdFinEquiv (x.1, 0), p02),
    (finProdFinEquiv (x.1, 0), p12), (finProdFinEquiv (x.1, 1), p01),
    (finProdFinEquiv (x.1, 1), p02), (finProdFinEquiv (x.1, 1), p12)] x.2

private def groupedCols {ℓ : ℕ} (x : Fin ℓ × Fin 6) :
    Fin (2 * ℓ) × Fin 3 :=
  ![(finProdFinEquiv (0, x.1), 0), (finProdFinEquiv (0, x.1), 1),
    (finProdFinEquiv (0, x.1), 2), (finProdFinEquiv (1, x.1), 0),
    (finProdFinEquiv (1, x.1), 1), (finProdFinEquiv (1, x.1), 2)] x.2

example : groupedRows ((0 : Fin 1), 0) = (0, p01) := rfl
example : groupedCols ((0 : Fin 1), 5) = (1, 2) := rfl

private def diagonalBlocks {k : Type*} [Field k] (ℓ : ℕ)
    (A : Matrix (Fin 6) (Fin 6) k) : Matrix (Fin ℓ × Fin 6) (Fin ℓ × Fin 6) k :=
  fun x y => if x.1 = y.1 then A x.2 y.2 else 0

example : diagonalBlocks 1 (block ℚ) (0, 0) (0, 3) = -1 := rfl

private theorem grouped_eq_blocks {k : Type*} [Field k] (ℓ : ℕ) :
    (koszulMatrix (contract₁ (matMul22Projection k) (matMulTensor k 2 2 ℓ))).submatrix
      groupedRows groupedCols = diagonalBlocks ℓ (block k) := by
  ext ⟨h, u⟩ ⟨h', v⟩
  by_cases hh : h = h' <;>
    fin_cases u <;> fin_cases v <;>
      simp [Matrix.submatrix_apply, groupedRows, groupedCols, koszulMatrix_apply,
        matMul22Projection_contract_apply, diagonalBlocks, block, eq_comm, hh]

private theorem diagonalBlocks_mul {k : Type*} [Field k] (ℓ : ℕ)
    (A B : Matrix (Fin 6) (Fin 6) k) :
    diagonalBlocks ℓ A * diagonalBlocks ℓ B = diagonalBlocks ℓ (A * B) := by
  classical
  ext ⟨h, u⟩ ⟨h', v⟩
  simp only [Matrix.mul_apply, diagonalBlocks, Fintype.sum_prod_type]
  by_cases hh : h = h'
  · subst h'
    simp
  · simp [hh]

private theorem diagonalBlocks_one {k : Type*} [Field k] (ℓ : ℕ) :
    diagonalBlocks ℓ (1 : Matrix (Fin 6) (Fin 6) k) = 1 := by
  classical
  ext ⟨h, u⟩ ⟨h', v⟩
  by_cases hh : h = h' <;> by_cases huv : u = v <;>
    simp [diagonalBlocks, Matrix.one_apply, hh, huv, Prod.ext_iff]

private theorem blocks_det_ne_zero {k : Type*} [Field k] (ℓ : ℕ) :
    (diagonalBlocks ℓ (block k)).det ≠ 0 := by
  classical
  apply Matrix.det_ne_zero_of_right_inverse (B := diagonalBlocks ℓ (blockInverse k))
  rw [diagonalBlocks_mul, block_mul_inverse, diagonalBlocks_one]

/-- The full `6ℓ` Koszul minor of the projected matrix multiplication tensor
has nonzero determinant, certified by the division-free six-coordinate inverse. -/
theorem matMul22_koszul_det_ne_zero {k : Type*} [Field k] (ℓ : ℕ) :
    ((koszulLinear k 3 (2 * ℓ) (ℓ * 2)
      (contract₁ (matMul22Projection k) (matMulTensor k 2 2 ℓ))).submatrix
        (groupedRows ∘ (finProdFinEquiv : Fin ℓ × Fin 6 ≃ Fin (ℓ * 6)).symm)
        (groupedCols ∘ (finProdFinEquiv : Fin ℓ × Fin 6 ≃ Fin (ℓ * 6)).symm)).det ≠ 0 := by
  classical
  rw [koszulLinear_apply, ← Matrix.submatrix_submatrix, grouped_eq_blocks,
    Matrix.det_submatrix_equiv_self]
  exact blocks_det_ne_zero ℓ

/-- Signed coordinate-variable lift for the p=1 Koszul flattening. -/
noncomputable def symbolicKoszul (k : Type*) [Field k] (a b c : ℕ) :
    SymbolicMatrixLift (koszulLinear k a b c) where
  matrix row col :=
    if col.2 = row.2.1.2 then MvPolynomial.X (row.2.1.1, col.1, row.1)
    else if col.2 = row.2.1.1 then -MvPolynomial.X (row.2.1.2, col.1, row.1)
    else 0
  eval_matrix T row col := by
    simp only [koszulLinear_apply, koszulMatrix_apply]
    split_ifs <;> simp [entries]

example : (symbolicKoszul ℚ 3 1 1).matrix (0, p01) (0, 1) =
    MvPolynomial.X (0, 0, 0) := rfl

/-- A Koszul minor larger than the simple-tensor capacity times `r` cannot
remain nonzero in the polynomial closure of the rank-at-most-`r` locus. -/
theorem BorderRankLE.koszul_det_eq_zero {k : Type*} [Field k]
    {a b c r m : ℕ} {T : Tensor k a b c} (hT : BorderRankLE T r)
    (hm : r * a.pred < m) (ri : Fin m → Fin c × KoszulPair a)
    (ci : Fin m → Fin b × Fin a) :
    ((koszulLinear k a b c T).submatrix ri ci).det = 0 := by
  classical
  let L := symbolicKoszul k a b c
  rw [← L.eval_det_submatrix T ri ci]
  apply borderRankLE_iff.mp hT
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro x ⟨S, hS, rfl⟩
  simp only [MvPolynomial.aeval_eq_eval]
  rw [L.eval_det_submatrix]
  by_contra hdet
  have hminor := le_rank_of_submatrix_det_ne_zero
    (koszulLinear k a b c S) ri ci hdet
  have hrank := koszul_rank_le_mul_of_rankLE hS
  exact (not_le_of_gt hm) (hminor.trans hrank)

/-- Source-derived `n=2` specialization: over every field, rectangular
`2 × 2 × ℓ` matrix multiplication is not in the polynomial closure of tensors
of rank at most `r` when `1 ≤ ℓ` and `r < 3ℓ`. This is polynomial-closure
border rank, not a classical sequential-border-rank identification. -/
theorem matMul22_not_borderRankLE {k : Type*} [Field k] {ℓ r : ℕ}
    (_hℓ : 1 ≤ ℓ) (hr : r < 3 * ℓ) :
    ¬ BorderRankLE (matMulTensor k 2 2 ℓ) r := by
  intro hborder
  have hprojected := hborder.contract₁ (matMul22Projection k)
  have hsize : r * (3 : ℕ).pred < ℓ * 6 := by
    change r * 2 < ℓ * 6
    omega
  exact matMul22_koszul_det_ne_zero ℓ
    (hprojected.koszul_det_eq_zero hsize _ _)

example : (1 ≤ (1 : ℕ)) ∧ (2 < 3 * (1 : ℕ)) ∧
    Nonempty (Fin 1) ∧ Nonempty (Fin 4) ∧ Nonempty (Fin 3) := by
  exact ⟨by decide, by decide, ⟨0⟩, ⟨0⟩, ⟨0⟩⟩

example : ¬ BorderRankLE (matMulTensor ℚ 2 2 1) 2 :=
  matMul22_not_borderRankLE (by decide) (by decide)

example : ¬ BorderRankLE (matMulTensor (ZMod 2) 2 2 1) 2 :=
  matMul22_not_borderRankLE (by decide) (by decide)

example : BorderRankLE (0 : Tensor ℚ 3 1 1) 0 ∧ 0 * (3 : ℕ).pred < 1 := by
  constructor
  · apply RankLE.borderRankLE
    refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    ext i j l
    simp
  · decide

example : matMulTensor ℚ 2 2 1 0 0 0 = 1 := by
  decide

end BilinearComplexity
