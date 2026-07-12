/-
  BilinearComplexity/Flattening — rectangular flattenings and the
  flattening lower bound n² ≤ R⟨n,n,n⟩ (port of the Vp2 cubic bound).

    · `flattening T`     — the first-factor flattening of a rectangular
                           3-tensor, an `a × (b*c)` matrix with columns
                           indexed by `Fin b × Fin c` (rectangular port
                           of `Vp2.flattening`).
    · `RankLE.rank_flattening_le` — a rank-≤ r tensor has flattening
                           rank ≤ r: the flattening factors through
                           `Fin r` as an `a × r` times `r × (b*c)`
                           product (port of
                           `Vp2.RankLE.rank_flattening_le`).
    · `rank_flattening_matMulTensor` — the flattening of `⟨n,n,n⟩` has
                           FULL rank `n * n`: the submatrix on the
                           distinguished columns
                           `y₀(i,j) = ((j,0), (0,i))` is the identity
                           matrix (the δ-conditions pin the unique
                           nonzero row), so `rank_submatrix_le` gives
                           the lower bound and the row count the upper.
    · `sq_le_rank_matMulTensor` — the payoff `n ^ 2 ≤ rank ⟨n,n,n⟩`:
                           the classical flattening lower bound on the
                           rank of matrix multiplication.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Proofs.BilinearComplexity.Basic

namespace BilinearComplexity

/-! ## 1. The flattening and its rank bound -/

/-- The first-factor flattening of a rectangular 3-tensor, as an
`a × (b*c)` matrix: row `i`, column `(j, l)` holds `T i j l`. -/
def flattening {k : Type*} {a b c : ℕ} (T : Tensor k a b c) :
    Matrix (Fin a) (Fin b × Fin c) k :=
  fun i jl => T i jl.1 jl.2

/-- A rank-≤ r tensor has flattening rank ≤ r: the flattening factors as
an `a × r` times `r × (b*c)` matrix product, so its rank is bounded by
the inner dimension. -/
theorem RankLE.rank_flattening_le {k : Type*} [CommRing k] [Nontrivial k]
    {a b c : ℕ} {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    (flattening T).rank ≤ r := by
  obtain ⟨u, v, w, rfl⟩ := h
  have hfac : flattening (fun i j l => ∑ s, u s i * v s j * w s l) =
      Matrix.of (fun i (s : Fin r) => u s i) *
        Matrix.of (fun (s : Fin r) jl => v s jl.1 * w s jl.2) := by
    ext i jl
    simp [flattening, Matrix.mul_apply, mul_assoc]
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin r))

/-! ## 2. The flattening of the matmul tensor has full rank -/

/-- The flattening of the matrix multiplication tensor `⟨n,n,n⟩` has full
rank `n * n`. Lower bound: for each row `x = (i,j)` the distinguished
column `y₀ x = ((j,0), (0,i))` has its unique nonzero entry `1` in row
`x` — the δ-conditions `j = j'`, `l = l' = 0`, `i' = i` pin the row — so
the square submatrix on the columns `y₀` is the identity matrix, whose
rank `n * n` bounds the flattening rank from below
(`Matrix.rank_submatrix_le`). Upper bound: the matrix has `n * n` rows. -/
theorem rank_flattening_matMulTensor (k : Type*) [CommRing k] [Nontrivial k]
    (n : ℕ) : (flattening (matMulTensor k n n n)).rank = n * n := by
  refine le_antisymm
    ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin _)) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hsub : (flattening (matMulTensor k n n n)).submatrix id
      (fun x : Fin (n * n) =>
        (finProdFinEquiv ((finProdFinEquiv.symm x).2, ⟨0, hn⟩),
         finProdFinEquiv (⟨0, hn⟩, (finProdFinEquiv.symm x).1))) = 1 := by
    ext x x'
    simp only [Matrix.submatrix_apply, id_eq, flattening, matMulTensor_apply,
      Equiv.symm_apply_apply, Matrix.one_apply]
    by_cases h : x = x'
    · subst h; simp
    · rw [if_neg h]
      refine if_neg ?_
      rintro ⟨h1, -, h3⟩
      exact h (finProdFinEquiv.symm.injective (Prod.ext h3.symm h1))
  calc n * n = Fintype.card (Fin (n * n)) := (Fintype.card_fin _).symm
    _ = (1 : Matrix (Fin (n * n)) (Fin (n * n)) k).rank := Matrix.rank_one.symm
    _ = ((flattening (matMulTensor k n n n)).submatrix id
          (fun x : Fin (n * n) =>
            (finProdFinEquiv ((finProdFinEquiv.symm x).2, ⟨0, hn⟩),
             finProdFinEquiv (⟨0, hn⟩, (finProdFinEquiv.symm x).1)))).rank := by
        rw [hsub]
    _ ≤ (flattening (matMulTensor k n n n)).rank :=
        Matrix.rank_submatrix_le _ _ _

/-! ## 3. The payoff: n² ≤ R⟨n,n,n⟩ -/

/-- The flattening lower bound on the rank of matrix multiplication:
`n ^ 2 ≤ rank ⟨n,n,n⟩`. Any decomposition of `⟨n,n,n⟩` into `r` triads
bounds the flattening rank by `r` (`RankLE.rank_flattening_le`), and the
flattening has full rank `n²` (`rank_flattening_matMulTensor`). -/
theorem sq_le_rank_matMulTensor (k : Type*) [CommRing k] [Nontrivial k]
    (n : ℕ) : n ^ 2 ≤ rank (matMulTensor k n n n) :=
  calc n ^ 2 = n * n := pow_two n
    _ = (flattening (matMulTensor k n n n)).rank :=
        (rank_flattening_matMulTensor k n).symm
    _ ≤ rank (matMulTensor k n n n) :=
        (rankLE_rank (matMulTensor k n n n)).rank_flattening_le

end BilinearComplexity
