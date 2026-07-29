/-
  Block-matrix embedding identity for the symmetrized matrix
  multiplication tensor (the CHIL+O reduction step).

  Statement provenance: Chiantini–Hauenstein–Ikenmeyer–Landsberg–
  Ottaviani, "Polynomials and the exponent of matrix multiplication",
  arXiv:1706.05074, proof of Theorem 1.1 (Section 2, "Proof of
  (SMnom)"): for n×n matrices A, B, C over a commutative ring and the
  3n×3n block matrix

        X = ⎡ 0  0  A ⎤
            ⎢ C  0  0 ⎥
            ⎣ 0  B  0 ⎦

  the cube is block-diagonal, X³ = diag(ABC, CAB, BCA), hence

        trace (X·X·X) = 3 · trace (A·B·C)

  by cyclicity of the trace. This is the identity that recovers the
  matrix multiplication tensor M_n from the symmetrized tensor
  sM_{3n}(Y) = trace(Y³). The rank-transfer consequences
  (R(M_n) ≤ R(sM_{3n}), R_s bounds, etc.) are out of scope here.

  Representation choice: X is the (Fin 3 × m)-indexed matrix obtained
  by flattening (`Matrix.comp`) the 3×3 matrix-of-matrices
  `!![0, 0, A; C, 0, 0; 0, B, 0]`, so block (i,j) of X is entry (i,j)
  of that literal: `X (i, a) (j, b) = !![0,0,A; C,0,0; 0,B,0] i j a b`
  definitionally. Stated over an arbitrary `CommSemiring R` (subsumes
  the commutative-ring statement) and an arbitrary `Fintype m`
  (`m := Fin n` gives the paper's 3n×3n statement; `n ≥ 1` is not
  needed).

  Headline theorem:
    `CHILO.trace_cyclicBlock_mul_cyclicBlock_mul_cyclicBlock` —
        trace (X * X * X) = 3 * trace (A * B * C)
  with the power form `CHILO.trace_cyclicBlock_pow_three` and the
  block-diagonal cube exposed as
  `CHILO.cyclicBlock_mul_cyclicBlock_mul_cyclicBlock`.

  Mathlib gaps encountered:
  * `Matrix.trace_comp` (trace of a flattened block matrix equals the
    trace of the matrix-valued trace) is missing — Composition.lean
    has no trace API at all. Proved below; upstreamable.
  * Everything else was available: `Matrix.comp`/`compRingEquiv`
    (Data/Matrix/Composition.lean); the `!![...]`-literal simp normal
    form (`Matrix.cons_mul`, `Matrix.vecMul_cons`, ...) computes the
    block-level cube by itself; `Matrix.trace_fin_three_of` and
    `Matrix.trace_mul_cycle` finish the trace computation.

  AI disclosure: formalized with AI assistance (see Proofs/README).
-/
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

open Matrix

/-- The trace of a flattened block matrix (`Matrix.comp`) is the trace
of its matrix-valued trace. Missing from Mathlib's
`Data/Matrix/Composition.lean` as of 2026-06. -/
theorem Matrix.trace_comp {I K R : Type*} [Fintype I] [Fintype K] [AddCommMonoid R]
    (M : Matrix I I (Matrix K K R)) :
    (Matrix.comp I I K K R M).trace = M.trace.trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.sum_apply, Fintype.sum_prod_type,
    Finset.sum_comm (γ := I)]

namespace CHILO

variable {R : Type*} [CommSemiring R] {m : Type*} [Fintype m]

/-- The CHIL+O cyclic block matrix
`X = [[0, 0, A], [C, 0, 0], [0, B, 0]]` of arXiv:1706.05074, Thm 1.1,
realized as a `(Fin 3 × m)`-indexed matrix: `X (i,a) (j,b)` is entry
`(a,b)` of block `(i,j)`. -/
def cyclicBlock (A B C : Matrix m m R) : Matrix (Fin 3 × m) (Fin 3 × m) R :=
  Matrix.comp (Fin 3) (Fin 3) m m R !![0, 0, A; C, 0, 0; 0, B, 0]

/-- Cube of the 3×3 matrix-of-matrices: block-level computation. -/
private lemma cube_aux (A B C : Matrix m m R) :
    (!![0, 0, A; C, 0, 0; 0, B, 0] : Matrix (Fin 3) (Fin 3) (Matrix m m R)) *
        !![0, 0, A; C, 0, 0; 0, B, 0] * !![0, 0, A; C, 0, 0; 0, B, 0] =
      !![A * B * C, 0, 0; 0, C * A * B, 0; 0, 0, B * C * A] := by
  simp

/-- X³ is block diagonal with diagonal blocks ABC, CAB, BCA
(arXiv:1706.05074, proof of Thm 1.1). -/
theorem cyclicBlock_mul_cyclicBlock_mul_cyclicBlock (A B C : Matrix m m R) :
    cyclicBlock A B C * cyclicBlock A B C * cyclicBlock A B C =
      Matrix.comp (Fin 3) (Fin 3) m m R
        !![A * B * C, 0, 0; 0, C * A * B, 0; 0, 0, B * C * A] := by
  simp only [cyclicBlock, ← Matrix.compRingEquiv_apply, ← map_mul, cube_aux]

/-- **CHIL+O block-matrix embedding identity** (arXiv:1706.05074,
proof of Theorem 1.1): for the 3n×3n cyclic block matrix
`X = [[0,0,A],[C,0,0],[0,B,0]]`, `trace (X·X·X) = 3·trace (A·B·C)`. -/
theorem trace_cyclicBlock_mul_cyclicBlock_mul_cyclicBlock (A B C : Matrix m m R) :
    trace (cyclicBlock A B C * cyclicBlock A B C * cyclicBlock A B C) =
      3 * trace (A * B * C) := by
  rw [cyclicBlock_mul_cyclicBlock_mul_cyclicBlock, Matrix.trace_comp,
    Matrix.trace_fin_three_of, Matrix.trace_add, Matrix.trace_add,
    ← Matrix.trace_mul_cycle A B C, Matrix.trace_mul_cycle B C A]
  ring

/-- Power form of the embedding identity: `trace (X³) = 3·trace (ABC)`,
matching `sM(X) = trace (X³)`. -/
theorem trace_cyclicBlock_pow_three [DecidableEq m] (A B C : Matrix m m R) :
    trace (cyclicBlock A B C ^ 3) = 3 * trace (A * B * C) := by
  rw [pow_three']
  exact trace_cyclicBlock_mul_cyclicBlock_mul_cyclicBlock A B C

/- Statement smoke test (non-vacuous instance, 1×1 blocks over ℤ):
trace (X·X·X) = 3·(3·5·7) = 315 ≠ 0, so `cyclicBlock` encodes a
genuinely nonzero X and the identity is not vacuous. -/
example :
    trace (cyclicBlock !![3] !![5] !![7] * cyclicBlock !![3] !![5] !![7] *
        cyclicBlock !![3] !![5] !![7] : Matrix (Fin 3 × Fin 1) (Fin 3 × Fin 1) ℤ) = 315 := by
  decide

end CHILO
