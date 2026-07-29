/-
  Conner's rank-18 Waring decomposition of the symmetrized 3×3 matrix
  multiplication tensor sM₍₃₎, certified as a polynomial identity.

  Statement provenance: Austin Conner, "A rank 18 Waring decomposition
  of sM_⟨3⟩ with 432 symmetries", arXiv:1711.05796, Theorem 1: the 18
  matrices m₁, …, m₁₈ listed there satisfy 6·sM₍₃₎ = Σᵢ mᵢ^(3).
  Evaluated on a single matrix argument A (sM₍₃₎(A,A,A) = tr A³) and
  with the Frobenius pairing L_m(A) = Σᵢⱼ mᵢⱼ Aᵢⱼ as the linear form
  of m, this is the polynomial identity

        Σᵢ₌₁¹⁸ L_{mᵢ}(A)³ = 6 · tr(A³)

  in the 9 entries of A. This file proves it over an arbitrary
  commutative ring R containing elements ω, a with ω² + ω + 1 = 0
  (primitive cube root of unity) and a³ = −2, for EVERY matrix A over
  R. Universality over all such R is the strongest form of the
  165-monomial-coefficient identity: instantiating R at a multivariate
  polynomial ring over ℤ[ω,a]/(ω²+ω+1, a³+2) with A the matrix of
  indeterminates recovers the coefficient-wise statement verbatim.
  Instantiations below: ℂ (with ω = (−1+√3·i)/2, a = −2^{1/3}; the
  headline upper bound R_s(sM₍₃₎) ≤ 18 lives over ℂ) and the decidable
  smoke test ZMod 31 (ω = 5, a = 27), which also witnesses that the
  hypotheses on (R, ω, a) are nontrivially satisfiable.

  ERRATUM (documented in `.tasks/research/infodumps/errata-1711-05796.md`
  and Wd1): the paper prints the scalar summand constant as
  a = −2^{−1/3}; the decomposition reproduces tr A³ only with a³ = −2,
  i.e. a = −2^{1/3} (with the paper's printed value the identity fails
  already at A = I: 9.75 ≠ 3). This file certifies the corrected
  constant: hypothesis `ha : a³ = −2`, and the ℂ-instantiation uses
  a = −2^{1/3} explicitly. Exact transcription of the mᵢ was verified
  against the paper's TeX source by exact arithmetic over
  ℤ[ω]/(ω²+ω+1) before formalization (Cn1 campaign; the numerical
  oracle of `cmd/probe-waring` agrees to 7.9e−16).

  Proof structure: the 18 forms organize into six cube-root-of-unity
  triples sharing integer linear data (u, v, w):

      (u+v+w)³ + (u+ωv+ω²w)³ + (u+ω²v+ωw)³ = 3(u³+v³+w³) + 18uvw

  — triples (m₁,m₆,m₈), (m₉,m₂,m₄), (m₅,m₃,m₇) on the Hesse block,
  (m₁₈,m₁₁,m₁₃), (m₁₄,m₁₆,m₁₂) on the permutation block, and
  (m₁₅,m₁₇) on the diagonal block, whose missing third member u+v+w =
  tr A is supplied (scaled by a) by the scalar summand m₁₀ = a·I —
  this is where a³ = −2 enters. The cofactor certificates for
  `linear_combination` were computed by hand and verified exactly.

  AI disclosure: formalized with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

namespace CHILO

variable {R : Type*} [CommRing R]

/-- Frobenius pairing of two 3×3 matrices, `⟪m, A⟫ = Σᵢⱼ mᵢⱼ·Aᵢⱼ`:
the linear form on matrix space determined by `m`. -/
def frob (m A : Matrix (Fin 3) (Fin 3) R) : R := ∑ i, ∑ j, m i j * A i j

/-- The 18 matrices of Conner's Waring decomposition of `6·sM₍₃₎`
(arXiv:1711.05796, Theorem 1), over any commutative ring: `ω` plays
ζ = e^{2πi/3} and `a` plays the scalar constant. The paper prints
`a = −2^{−1/3}`; the corrected value (see header) satisfies `a³ = −2`. -/
def conner (ω a : R) : Fin 18 → Matrix (Fin 3) (Fin 3) R :=
  ![!![1, -1, 0; -1, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, -ω; 0, -ω ^ 2, 1],
    !![1, 0, -ω; 0, 0, 0; -ω ^ 2, 0, 1],
    !![0, 0, 0; 0, 1, -ω ^ 2; 0, -ω, 1],
    !![1, 0, -1; 0, 0, 0; -1, 0, 1],
    !![1, -ω, 0; -ω ^ 2, 1, 0; 0, 0, 0],
    !![1, 0, -ω ^ 2; 0, 0, 0; -ω, 0, 1],
    !![1, -ω ^ 2, 0; -ω, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, -1; 0, -1, 1],
    !![a, 0, 0; 0, a, 0; 0, 0, a],
    !![0, 1, 0; 0, 0, ω; ω ^ 2, 0, 0],
    !![0, 0, 1; ω ^ 2, 0, 0; 0, ω, 0],
    !![0, 1, 0; 0, 0, ω ^ 2; ω, 0, 0],
    !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2],
    !![0, 0, 1; ω, 0, 0; 0, ω ^ 2, 0],
    !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, ω],
    !![0, 1, 0; 0, 0, 1; 1, 0, 0]]

/-- Classical cube-root-of-unity triple identity: for `ω² + ω + 1 = 0`,
`(u+v+w)³ + (u+ωv+ω²w)³ + (u+ω²v+ωw)³ = 3(u³+v³+w³) + 18uvw`.
Each of Conner's six form-triples contributes through this identity. -/
theorem cube_triple (ω : R) (hω : ω ^ 2 + ω + 1 = 0) (u v w : R) :
    (u + v + w) ^ 3 + (u + ω * v + ω ^ 2 * w) ^ 3 + (u + ω ^ 2 * v + ω * w) ^ 3 =
      3 * (u ^ 3 + v ^ 3 + w ^ 3) + 18 * (u * v * w) := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  linear_combination
    (3 * u ^ 2 * v + 3 * u ^ 2 * w + 3 * u * v ^ 2 + 3 * u * w ^ 2 +
      3 * v ^ 2 * w + 3 * v * w ^ 2) * hω +
    (3 * ω * u * v ^ 2 + 3 * ω * u * w ^ 2 + 12 * u * v * w +
      (ω ^ 3 + 2) * (v ^ 3 + w ^ 3) + (3 * ω + 3 * ω ^ 2) * (v ^ 2 * w + v * w ^ 2)) * h3

/-- **Conner's rank-18 Waring decomposition of sM₍₃₎**
(arXiv:1711.05796, Theorem 1; scalar constant corrected to `a³ = −2`):
over any commutative ring with a primitive cube root of unity `ω` and
a cube root `a` of `−2`, the cubes of the 18 linear forms
`⟪mᵢ, ·⟫` sum to `6·tr(A³)`. Universally quantified over `R` and `A`,
this is exactly the 165-coefficient polynomial identity
`Σᵢ L_{mᵢ}³ = 6·sM₍₃₎` in the 9 matrix entries, certifying
`R_s(sM₍₃₎) ≤ 18`. -/
theorem conner_waring (ω a : R) (hω : ω ^ 2 + ω + 1 = 0) (ha : a ^ 3 = -2)
    (A : Matrix (Fin 3) (Fin 3) R) :
    ∑ i : Fin 18, (frob (conner ω a i) A) ^ 3 = 6 * (A * A * A).trace := by
  have hA := cube_triple ω hω (A 0 0 + A 1 1) (-(A 0 1)) (-(A 1 0))
  have hB := cube_triple ω hω (A 1 1 + A 2 2) (-(A 1 2)) (-(A 2 1))
  have hC := cube_triple ω hω (A 0 0 + A 2 2) (-(A 0 2)) (-(A 2 0))
  have hD := cube_triple ω hω (A 0 1) (A 1 2) (A 2 0)
  have hE := cube_triple ω hω (A 0 2) (A 1 0) (A 2 1)
  have hF := cube_triple ω hω (A 0 0) (A 1 1) (A 2 2)
  -- stage 1: peel the Fin 18 sum with `frob` still folded (no Fin 3 sums in
  -- sight), so `Fin.sum_univ_succ` cannot reach the inner index-3 sums and
  -- produce non-numeral `Fin.succ` atoms
  simp only [conner, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  -- stage 2: expand `frob`, matrix products, and the trace with numeral-indexed
  -- `Fin.sum_univ_three`, reducing all matrix-literal entries
  simp only [frob, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply,
    Matrix.trace_fin_three, Matrix.mul_apply]
  linear_combination hA + hB + hC + hD + hE + hF + (A 0 0 + A 1 1 + A 2 2) ^ 3 * ha

section Instantiations

/-- A primitive cube root of unity in ℂ: `ω = (−1 + √3·i)/2`. -/
noncomputable def omegaC : ℂ := (-1 + Real.sqrt 3 * Complex.I) / 2

theorem omegaC_rel : omegaC ^ 2 + omegaC + 1 = 0 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  unfold omegaC
  linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + (-(1:ℂ) / 4) * h3

/-- The real cube root of 2. -/
noncomputable def cbrt2 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

theorem cbrt2_cube : cbrt2 ^ 3 = 2 := by
  rw [cbrt2, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Conner's decomposition over ℂ with the explicit (erratum-corrected)
constants `ω = (−1+√3·i)/2 = e^{2πi/3}` and `a = −2^{1/3}`: the headline
certificate of `R_s(sM₍₃₎) ≤ 18`. -/
theorem conner_waring_complex (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ i : Fin 18, (frob (conner omegaC (-(cbrt2 : ℂ)) i) A) ^ 3 = 6 * (A * A * A).trace := by
  refine conner_waring _ _ omegaC_rel ?_ A
  have h : ((cbrt2 : ℝ) : ℂ) ^ 3 = 2 := by
    rw [← Complex.ofReal_pow, cbrt2_cube]
    norm_num
  linear_combination -h

/-- Decidable smoke test: in `ZMod 31`, `ω = 5` and `a = 27` satisfy the
hypotheses (`5² + 5 + 1 = 31 ≡ 0`, `27³ = (−4)³ = −64 ≡ −2`), so the
identity specializes to a true statement of modular arithmetic — and in
particular the hypotheses on `(R, ω, a)` are nontrivially satisfiable. -/
example (A : Matrix (Fin 3) (Fin 3) (ZMod 31)) :
    ∑ i : Fin 18, (frob (conner 5 27 i) A) ^ 3 = 6 * (A * A * A).trace :=
  conner_waring 5 27 (by decide) (by decide) A

end Instantiations

end CHILO
