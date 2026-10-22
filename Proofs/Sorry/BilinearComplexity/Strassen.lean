/-
  BilinearComplexity/Strassen — Strassen's seven-triad decomposition:
  R⟨2,2,2⟩ ≤ 7 (Strassen 1969). Card Pf10.

  The witness: seven rank-one triads `u_s ⊗ v_s ⊗ w_s` summing to
  `matMulTensor k 2 2 2 : Tensor k 4 4 4`, one per Strassen product

    M1 = (A11+A22)(B11+B22)   M5 = (A11+A12)B22
    M2 = (A21+A22)B11         M6 = (A21−A11)(B11+B12)
    M3 = A11(B12−B22)         M7 = (A12−A22)(B21+B22)

    C11 = M1+M4−M5+M7   C12 = M3+M5      M4 = A22(B21−B11)
    C21 = M2+M4         C22 = M1−M2+M3+M6

  (product table verified against Wikipedia "Strassen algorithm"; the full
  64-entry tensor identity and the symbolic 2×2 product were independently
  re-verified in Sage before encoding).

  INDEX PACKING (see Basic.lean header): all three modes are row-major
  `finProdFinEquiv`-packed — `x = 2i+j` over A-positions, `y = 2j+l` over
  B-positions, and the THIRD mode `z = 2l+i` packs C *transposed*:
  `matMulTensor` is the structure tensor of `trace (X*Y*Z)`, so `w s` at
  `z = 2l+i` carries the coefficient of `M_s` in `C_{il}`. Support of
  `matMulTensor ℤ 2 2 2` (re-verified by `#eval` this session):
    (0,0,0) (0,1,2) (1,2,0) (1,3,2) (2,0,1) (2,1,3) (3,2,1) (3,3,3)
  = { (2i+j, 2j+l, 2l+i) | i,j,l ∈ {0,1} }.

  Certificates: plain `decide` over ℤ; `decide +kernel` over ℚ — the
  elaborator's evaluator gets stuck on `Rat.add`'s normalization
  (`Nat.gcd` is well-founded recursion), while the kernel evaluates it
  through its built-in accelerated `Nat.gcd`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Fin.VecNotation
import BilinearComplexity.Basic

namespace BilinearComplexity

/-- A-side coefficient vectors of Strassen's seven products, on the
row-major packed index `x = 2i+j`, i.e. over `[A11, A12, A21, A22]`:
row `s` holds the coefficients of the A-factor of `M_{s+1}`. -/
def strassenU (k : Type*) [Ring k] : Fin 7 → Fin 4 → k :=
  ![![1, 0, 0, 1],   -- M1 : A11 + A22
    ![0, 0, 1, 1],   -- M2 : A21 + A22
    ![1, 0, 0, 0],   -- M3 : A11
    ![0, 0, 0, 1],   -- M4 : A22
    ![1, 1, 0, 0],   -- M5 : A11 + A12
    ![-1, 0, 1, 0],  -- M6 : A21 − A11
    ![0, 1, 0, -1]]  -- M7 : A12 − A22

/-- B-side coefficient vectors of Strassen's seven products, on the
row-major packed index `y = 2j+l`, i.e. over `[B11, B12, B21, B22]`:
row `s` holds the coefficients of the B-factor of `M_{s+1}`. -/
def strassenV (k : Type*) [Ring k] : Fin 7 → Fin 4 → k :=
  ![![1, 0, 0, 1],   -- M1 : B11 + B22
    ![1, 0, 0, 0],   -- M2 : B11
    ![0, 1, 0, -1],  -- M3 : B12 − B22
    ![-1, 0, 1, 0],  -- M4 : B21 − B11
    ![0, 0, 0, 1],   -- M5 : B22
    ![1, 1, 0, 0],   -- M6 : B11 + B12
    ![0, 0, 1, 1]]   -- M7 : B21 + B22

/-- C-side coefficient vectors of Strassen's decomposition, on the
row-major packed *transposed* index `z = 2l+i`, i.e. over
`[C11, C21, C12, C22]` (the third mode of `matMulTensor` packs `(l,i)` —
see the file header): row `s`, entry `2l+i` is the coefficient of
`M_{s+1}` in `C_{il}`. -/
def strassenW (k : Type*) [Ring k] : Fin 7 → Fin 4 → k :=
  ![![1, 0, 0, 1],   -- M1 → C11,  C22
    ![0, 1, 0, -1],  -- M2 → C21, −C22
    ![0, 0, 1, 1],   -- M3 → C12,  C22
    ![1, 1, 0, 0],   -- M4 → C11,  C21
    ![-1, 0, 1, 0],  -- M5 → −C11, C12
    ![0, 0, 0, 1],   -- M6 → C22
    ![1, 0, 0, 0]]   -- M7 → C11

/-- **Strassen (1969)**: the 2×2 matrix multiplication tensor over ℤ is a
sum of seven rank-one triads. The 64-entry × 7-summand identity is
certified by `decide`. -/
theorem strassen_rankLE : RankLE (matMulTensor ℤ 2 2 2) 7 :=
  ⟨strassenU ℤ, strassenV ℤ, strassenW ℤ, by decide⟩

/-- Strassen's rank bound `rank ⟨2,2,2⟩ ≤ 7` over ℤ. -/
theorem rank_matMulTensor_le_seven : rank (matMulTensor ℤ 2 2 2) ≤ 7 :=
  rank_le_of_rankLE strassen_rankLE

/-- **Strassen (1969)** over ℚ: the same seven triads with ℚ entries.
Certified by `decide +kernel` (the kernel's accelerated `Nat.gcd` evaluates
`Rat` arithmetic; the elaborator's evaluator cannot — see file header). -/
theorem strassen_rankLE_rat : RankLE (matMulTensor ℚ 2 2 2) 7 :=
  ⟨strassenU ℚ, strassenV ℚ, strassenW ℚ, by decide +kernel⟩

/-- Strassen's rank bound `rank ⟨2,2,2⟩ ≤ 7` over ℚ. -/
theorem rank_matMulTensor_le_seven_rat : rank (matMulTensor ℚ 2 2 2) ≤ 7 :=
  rank_le_of_rankLE strassen_rankLE_rat

end BilinearComplexity
