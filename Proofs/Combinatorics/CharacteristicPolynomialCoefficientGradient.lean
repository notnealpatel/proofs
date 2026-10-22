/-
# Bivariate Cayley–Hamilton theorem (gradient of characteristic-polynomial coefficients)

## Source

Christian Ikenmeyer, "On the gradient of the coefficient of the characteristic polynomial
(bivariate Cayley–Hamilton theorem)", arXiv:2511.04954.
Section "The Bivariate Cayley--Hamilton Theorem", Theorem `thm:CayleyHamilton`;
corollaries `cor:CayHam` and `cor:adjugate` in Section "Corollaries".

Definitions (paper, eqs. (cpct), (cpcS)): `X_n = (x_{i,j})` is the generic `n × n` matrix,
`det (X_n + t I) = ∑_{d ≥ 0} c_{n,n-d} t^d`, equivalently
`c_{n,d} = ∑_{S ∈ binom([n], d)} det ([X_n]_{S,S})`; `∇f` is the `n × n` matrix with
`(i, j)` entry `∂f/∂x_{i,j}`. Everything is over an arbitrary commutative ring `R`.

Theorem `thm:CayleyHamilton`: for all `n, d ∈ ℕ`,
`(∇ c_{n,d+1})ᵀ = ∑_{i=0}^d (-1)^i c_{n,d-i} X_n^i`.

Corollary `cor:CayHam`: `0 = ∑_{i=0}^n (-1)^i c_{n,n-i} X_n^i`.
Corollary `cor:adjugate`: `(∇ det_n)ᵀ = ∑_{i=0}^{n-1} (-1)^i c_{n,n-1-i} X_n^i`.

## Proof

The paper uses clow sequences. Here the proof is algebraic: `∂/∂x_{b,a} [t^(k+1)] det (1 + t X_n) = [t^k] adj (1 + t X_n)_{a,b}` (the
determinant is affine in the entry `(b, a)`), and comparing `t`-coefficients in
`adj (1 + t X) (1 + t X) = det (1 + t X) • 1` gives the closed form of `[t^d] adj (1 + t X)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.CharacteristicPolynomialCoefficientGradient

open Matrix

section Recurrence

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- The matrix `1 + t M` over `A[t]`. -/
noncomputable def oneAddTMul (M : Matrix ι ι A) : Matrix ι ι (Polynomial A) :=
  1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C

/-- The `t^k` coefficient matrix of `adj (1 + t M)`. -/
noncomputable def adjCoeff (M : Matrix ι ι A) (k : ℕ) : Matrix ι ι A :=
  Matrix.of fun i j => ((oneAddTMul M).adjugate i j).coeff k

/-- `adj (1 + t M) + t (adj (1 + t M) * M) = det (1 + t M) • 1`, the identity
`adj N * N = det N • 1` with `N = 1 + t M` expanded. -/
theorem adjugate_add_X_smul_mul (M : Matrix ι ι A) :
    (oneAddTMul M).adjugate +
        (Polynomial.X : Polynomial A) • ((oneAddTMul M).adjugate * M.map Polynomial.C) =
      (oneAddTMul M).det • (1 : Matrix ι ι (Polynomial A)) := by
  have key := adjugate_mul (oneAddTMul M)
  conv_lhs at key => rw [oneAddTMul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  exact key

/-- The `t^k` coefficient of the `(i, j)` entry of `adj (1 + t M) * M.map C`. -/
theorem coeff_adjugate_mul_map_C (M : Matrix ι ι A) (k : ℕ) (i j : ι) :
    (((oneAddTMul M).adjugate * M.map Polynomial.C) i j).coeff k = (adjCoeff M k * M) i j := by
  simp only [Matrix.mul_apply, Polynomial.finsetSum_coeff, Matrix.map_apply,
    Polynomial.coeff_mul_C, adjCoeff, Matrix.of_apply]

/-- Comparing coefficients in `adj (1 + t M) * (1 + t M) = det (1 + t M) • 1`:
the constant coefficient. -/
theorem adjCoeff_zero (M : Matrix ι ι A) :
    adjCoeff M 0 = ((oneAddTMul M).det.coeff 0) • (1 : Matrix ι ι A) := by
  ext i j
  have hij := congrArg (fun N : Matrix ι ι (Polynomial A) => (N i j).coeff 0)
    (adjugate_add_X_smul_mul M)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.coeff_add,
    Polynomial.coeff_X_mul_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero] at hij
  simp only [adjCoeff, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, hij]
  split_ifs <;> simp

/-- Comparing coefficients in `adj (1 + t M) * (1 + t M) = det (1 + t M) • 1`:
the `t^(k+1)` coefficient. -/
theorem adjCoeff_succ (M : Matrix ι ι A) (k : ℕ) :
    adjCoeff M (k + 1) =
      ((oneAddTMul M).det.coeff (k + 1)) • (1 : Matrix ι ι A) - adjCoeff M k * M := by
  ext i j
  have hij := congrArg (fun N : Matrix ι ι (Polynomial A) => (N i j).coeff (k + 1))
    (adjugate_add_X_smul_mul M)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.coeff_add,
    Polynomial.coeff_X_mul, coeff_adjugate_mul_map_C, Matrix.one_apply, mul_ite, mul_one,
    mul_zero] at hij
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  change ((oneAddTMul M).adjugate i j).coeff (k + 1) = _
  rw [eq_sub_of_add_eq hij]
  split_ifs <;> simp

/-- Closed form of the coefficient matrices of `adj (1 + t M)`:
`[t^d] adj (1 + t M) = ∑_{i=0}^{d} (-1)^i e_{d-i} M^i`, where `e_k = [t^k] det (1 + t M)`.
The natural subtraction `d - i` is guarded by `i ∈ range (d + 1)`. -/
theorem adjCoeff_eq_sum (M : Matrix ι ι A) (d : ℕ) :
    adjCoeff M d = ∑ i ∈ Finset.range (d + 1),
      ((-1 : A) ^ i * (oneAddTMul M).det.coeff (d - i)) • M ^ i := by
  induction d with
  | zero => simp [adjCoeff_zero]
  | succ d ih =>
    set c : ℕ → A := fun k => (oneAddTMul M).det.coeff k with hc
    have hterm : ∀ i ∈ Finset.range (d + 1),
        ((-1 : A) ^ (i + 1) * c (d + 1 - (i + 1))) • M ^ (i + 1) =
          -(((-1 : A) ^ i * c (d - i)) • M ^ i * M) := by
      intro i _
      rw [Nat.add_sub_add_right, smul_mul_assoc, ← pow_succ, pow_succ, ← neg_smul]
      ring_nf
    rw [adjCoeff_succ, ih, Finset.sum_mul, Finset.sum_range_succ' _ (d + 1),
      Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    simp only [pow_zero, one_mul, Nat.sub_zero]
    abel

end Recurrence

section Generic

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The generic `n × n` matrix `X_n = (x_{i,j})` over `R[x_{i,j}]`. -/
noncomputable def genericMatrix : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

/-- The coefficient polynomial `c_{n,d} = ∑_{S ⊆ [n], |S| = d} det ([X_n]_{S,S})`,
the sum of the principal `d × d` minors of the generic matrix (paper, eq. (cpcS)). -/
noncomputable def cpc (d : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
    ((genericMatrix R n).submatrix (Subtype.val : s → Fin n) Subtype.val).det

/-- `c_{n,d}` is the `t^d` coefficient of `det (1 + t X_n)`. -/
theorem cpc_eq_coeff_det (d : ℕ) :
    cpc R n d = (oneAddTMul (genericMatrix R n)).det.coeff d :=
  (coeff_det_one_add_X_smul_eq_sum_minors _ d).symm

variable {R n}

/-- A polynomial in `t` whose coefficients avoid a variable: if a matrix over `S[t]` is the
image of a matrix over `P[t]`, `P` the subalgebra of polynomials not involving `x_{b,a}`, then
every `t`-coefficient of its determinant has zero partial derivative in `x_{b,a}`. -/
theorem pderiv_coeff_det_map_supported (b a : Fin n)
    (N : Matrix (Fin n) (Fin n)
      (Polynomial (MvPolynomial.supported R ({(b, a)}ᶜ : Set (Fin n × Fin n))))) (k : ℕ) :
    MvPolynomial.pderiv (b, a)
      ((N.map (Polynomial.map
        (MvPolynomial.supported R ({(b, a)}ᶜ : Set (Fin n × Fin n))).val.toRingHom)).det.coeff k)
      = 0 := by
  have hdet := (RingHom.map_det (Polynomial.mapRingHom
    (MvPolynomial.supported R ({(b, a)}ᶜ : Set (Fin n × Fin n))).val.toRingHom) N).symm
  rw [RingHom.mapMatrix_apply, Polynomial.coe_mapRingHom] at hdet
  rw [hdet, Polynomial.coeff_map]
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  have hsub := (MvPolynomial.mem_supported.mp (N.det.coeff k).2) hmem
  simp at hsub

/-- Jacobi's formula, coefficientwise, for the generic matrix:
`∂/∂x_{b,a} [t^(k+1)] det (1 + t X_n) = [t^k] adj (1 + t X_n)_{a,b}`. -/
theorem pderiv_coeff_succ_det (a b : Fin n) (k : ℕ) :
    MvPolynomial.pderiv (b, a) ((oneAddTMul (genericMatrix R n)).det.coeff (k + 1)) =
      adjCoeff (genericMatrix R n) k a b := by
  classical
  let s : Set (Fin n × Fin n) := {(b, a)}ᶜ
  let φ := (MvPolynomial.supported R s).val.toRingHom
  -- the generic matrix with the `(b, a)` entry replaced by `0`, over the subalgebra `P`
  let X₀ : Matrix (Fin n) (Fin n) (MvPolynomial.supported R s) := Matrix.of fun i j =>
    if h : (i, j) = (b, a) then 0 else
      ⟨MvPolynomial.X (i, j), by
        rw [MvPolynomial.supported_eq_adjoin_X]
        exact Algebra.subset_adjoin ⟨(i, j), h, rfl⟩⟩
  let N₀ := (oneAddTMul X₀).map (Polynomial.map φ)
  let N₁ := ((oneAddTMul X₀).updateRow b (Pi.single a 1)).map (Polynomial.map φ)
  have hN₀_apply : ∀ i j, N₀ i j = (1 : Matrix (Fin n) (Fin n) _) i j +
      Polynomial.X * Polynomial.C (if (i, j) = (b, a) then 0 else MvPolynomial.X (i, j)) := by
    intro i j
    simp only [N₀, oneAddTMul, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    congr 1
    · rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · congr 2
      simp only [X₀, Matrix.of_apply]
      split_ifs
      · exact map_zero φ
      · rfl
  have hoff : ∀ i j, i ≠ b → oneAddTMul (genericMatrix R n) i j = N₀ i j := by
    intro i j hi
    rw [hN₀_apply, if_neg (fun h => hi (Prod.mk.inj h).1)]
    simp only [oneAddTMul, genericMatrix, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  have hdecomp : oneAddTMul (genericMatrix R n) = N₀.updateRow b
      (N₀ b + (Polynomial.X * Polynomial.C (MvPolynomial.X (b, a))) • Pi.single a 1) := by
    ext1 i j
    by_cases hi : i = b
    · subst hi
      rw [updateRow_self, Pi.add_apply, Pi.smul_apply, hN₀_apply]
      by_cases hj : j = a
      · subst hj
        simp [oneAddTMul, genericMatrix]
      · have hne : (i, j) ≠ (i, a) := fun h => hj (Prod.mk.inj h).2
        simp [oneAddTMul, genericMatrix, hne, hj]
    · rw [updateRow_ne hi, hoff i j hi]
  have hN₀ : N₀.updateRow b (Pi.single a 1) = N₁ := by
    have hsingle : (Polynomial.map φ) ∘ (Pi.single a 1 : Fin n → Polynomial _) =
        Pi.single a 1 := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp [hj]
    simp only [N₁, map_updateRow, hsingle, N₀]
  have hrow : (oneAddTMul (genericMatrix R n)).updateRow b (Pi.single a 1) = N₁ := by
    rw [← hN₀]
    ext1 i j
    by_cases hi : i = b
    · subst hi
      rw [updateRow_self, updateRow_self]
    · rw [updateRow_ne hi, updateRow_ne hi, hoff i j hi]
  have hdet : (oneAddTMul (genericMatrix R n)).det = N₀.det +
      (Polynomial.X * Polynomial.C (MvPolynomial.X (b, a))) * N₁.det := by
    rw [hdecomp, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, hN₀]
  have hadj : adjCoeff (genericMatrix R n) k a b = N₁.det.coeff k := by
    rw [adjCoeff, Matrix.of_apply, adjugate_apply, hrow]
  rw [hdet, hadj, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul, map_add, Derivation.leibniz, MvPolynomial.pderiv_X_self,
    pderiv_coeff_det_map_supported, pderiv_coeff_det_map_supported]
  simp

/-- The gradient `∇f`: the `n × n` matrix whose `(i, j)` entry is `∂f/∂x_{i,j}`. -/
noncomputable def gradient (f : MvPolynomial (Fin n × Fin n) R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun i j => MvPolynomial.pderiv (i, j) f

/-- `c_{n,0} = 1`. -/
theorem cpc_zero : cpc R n 0 = 1 := by
  simp [cpc]

/-- `c_{n,1} = tr X_n` (paper: "`c_{n,1} = tr_n` is the trace"). -/
theorem cpc_one : cpc R n 1 = (genericMatrix R n).trace := by
  rw [cpc_eq_coeff_det]
  exact coeff_det_one_add_X_smul_one _

/-- `c_{n,n} = det X_n` (paper: "`c_{d,d} = det_d`"). -/
theorem cpc_self : cpc R n n = (genericMatrix R n).det := by
  have huniv : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [cpc, huniv, Finset.sum_singleton]
  exact det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) _

/-- `c_{n,d} = 0` for `n < d`: there are no `d`-subsets of `[n]`. -/
theorem cpc_eq_zero_of_lt {d : ℕ} (hd : n < d) : cpc R n d = 0 := by
  rw [cpc, Finset.powersetCard_eq_empty.mpr (by simpa using hd), Finset.sum_empty]

/-- Bridge to the paper's defining equation (cpct): `det (X_n + t I) = ∑_d c_{n,n-d} t^d`,
i.e. for `d ≤ n` the coefficient of `t^(n-d)` in `charpoly (-X_n) = det (t I + X_n)` is
`c_{n,d}`. -/
theorem charpoly_neg_coeff_eq_cpc {d : ℕ} (hd : d ≤ n) :
    (-genericMatrix R n).charpoly.coeff (n - d) = cpc R n d := by
  have h := charpoly_coeff_eq_sum_minors (-genericMatrix R n) d (by simpa using hd)
  rw [Fintype.card_fin] at h
  rw [h, cpc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hneg : (-genericMatrix R n).submatrix (Subtype.val : t → Fin n) (Subtype.val : t → Fin n) =
      -((genericMatrix R n).submatrix (Subtype.val : t → Fin n) (Subtype.val : t → Fin n)) := rfl
  rw [hneg, det_neg, Fintype.card_coe, (Finset.mem_powersetCard.mp ht).2, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **Bivariate Cayley–Hamilton theorem** (Ikenmeyer, arXiv:2511.04954,
Theorem `thm:CayleyHamilton`), entrywise: for all `n, d` and positions `(a, b)`,
`[(∇ c_{n,d+1})ᵀ]_{a,b} = ∂c_{n,d+1}/∂x_{b,a} = [∑_{i=0}^{d} (-1)^i c_{n,d-i} X_n^i]_{a,b}`.
The natural subtraction `d - i` is guarded by `i ∈ range (d + 1)`. -/
theorem bivariate_cayley_hamilton_apply (d : ℕ) (a b : Fin n) :
    MvPolynomial.pderiv (b, a) (cpc R n (d + 1)) =
      (∑ i ∈ Finset.range (d + 1),
        ((-1 : MvPolynomial (Fin n × Fin n) R) ^ i * cpc R n (d - i)) •
          genericMatrix R n ^ i) a b := by
  rw [cpc_eq_coeff_det, pderiv_coeff_succ_det, adjCoeff_eq_sum]
  simp only [cpc_eq_coeff_det]

/-- **Bivariate Cayley–Hamilton theorem** (Ikenmeyer, arXiv:2511.04954,
Theorem `thm:CayleyHamilton`): over any commutative ring `R`, for all `n, d`,
`(∇ c_{n,d+1})ᵀ = ∑_{i=0}^{d} (-1)^i c_{n,d-i} X_n^i`. -/
theorem bivariate_cayley_hamilton (d : ℕ) :
    (gradient (cpc R n (d + 1)))ᵀ =
      ∑ i ∈ Finset.range (d + 1),
        ((-1 : MvPolynomial (Fin n × Fin n) R) ^ i * cpc R n (d - i)) • genericMatrix R n ^ i := by
  ext a b
  rw [transpose_apply, gradient, of_apply, bivariate_cayley_hamilton_apply]

/-- **Cayley–Hamilton theorem** (paper, Corollary `cor:CayHam`), obtained from the bivariate
theorem at `d = n`: `0 = ∑_{i=0}^{n} (-1)^i c_{n,n-i} X_n^i`. -/
theorem cayley_hamilton :
    ∑ i ∈ Finset.range (n + 1),
        ((-1 : MvPolynomial (Fin n × Fin n) R) ^ i * cpc R n (n - i)) • genericMatrix R n ^ i =
      0 := by
  rw [← bivariate_cayley_hamilton, cpc_eq_zero_of_lt (Nat.lt_succ_self n)]
  ext a b
  simp [gradient]

/-- **Faddeev–LeVerrier adjugate formula** (paper, Corollary `cor:adjugate`), obtained from the
bivariate theorem at `d = n - 1` for `1 ≤ n`:
`(∇ det_n)ᵀ = ∑_{i=0}^{n-1} (-1)^i c_{n,n-1-i} X_n^i`. -/
theorem gradient_det_transpose_eq_sum (hn : 1 ≤ n) :
    (gradient (genericMatrix R n).det)ᵀ =
      ∑ i ∈ Finset.range n,
        ((-1 : MvPolynomial (Fin n × Fin n) R) ^ i * cpc R n (n - 1 - i)) •
          genericMatrix R n ^ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← cpc_self, bivariate_cayley_hamilton, Nat.add_sub_cancel]

/-! ### Examples on `n = 2` -/

example : cpc ℤ 2 1 = MvPolynomial.X (0, 0) + MvPolynomial.X (1, 1) := by
  rw [cpc_one, Matrix.trace_fin_two]
  rfl

example : cpc ℤ 2 2 = MvPolynomial.X (0, 0) * MvPolynomial.X (1, 1) -
    MvPolynomial.X (0, 1) * MvPolynomial.X (1, 0) := by
  rw [cpc_self, Matrix.det_fin_two]
  rfl

example : cpc ℤ 2 3 = 0 := cpc_eq_zero_of_lt (by norm_num)

/- Gradient semantics: `∂ det X_2 / ∂x_{0,0} = x_{1,1}` and `∂ det X_2 / ∂x_{0,1} = -x_{1,0}`,
so `[(∇ det X_2)ᵀ]_{1,0} = -x_{1,0}`, matching `tr(X) I - X` from the theorem at `d = 1`. -/
example : gradient (cpc ℤ 2 2) 0 0 = MvPolynomial.X (1, 1) := by
  rw [cpc_self, Matrix.det_fin_two]
  simp [gradient, genericMatrix, MvPolynomial.pderiv_X]

example : (gradient (cpc ℤ 2 2))ᵀ 1 0 = -MvPolynomial.X (1, 0) := by
  rw [cpc_self, Matrix.det_fin_two]
  simp [gradient, genericMatrix, MvPolynomial.pderiv_X]

end Generic

end Candidates.CharacteristicPolynomialCoefficientGradient
