/-
  BilinearComplexity/GroupTensorWedderburn — the Wedderburn transport step of
  Cohn–Umans Theorem 4.1: over ℂ, the rank of the group-algebra multiplication
  tensor is at most the sum of the matrix-multiplication tensor ranks of the
  character degrees,

    R(mulTensor ℂ G) ≤ ∑_{d ∈ charDegrees G} R⟨d,d,d⟩.

  Route (no invertibility, no direct sums — a bare triad construction). Fix a
  Wedderburn decomposition `e : ℂ[G] ≃ₐ[ℂ] Π i, Mat_{dᵢ}(ℂ)`
  (`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`; the block-size
  multiset is `charDegrees G` by `charDegrees_eq_of_algEquiv`). Writing
  `τ : ℂ[G] → ℂ` for the coefficient-of-identity functional and
  `λ = τ ∘ e.symm`, the tensor entry is a trilinear evaluation

    mulTensor ℂ G x y z = [gₓ g_y g_z = 1] = τ(gₓ g_y g_z)
                        = λ(e gₓ * e g_y * e g_z),

  and `λ` splits over the blocks as `λ M = ∑ i, tr(Λᵢ · Mᵢ)` for fixed matrices
  `Λᵢ` (every linear functional on a matrix algebra is `tr(Λ · —)`). Since
  `tr(Λᵢ XYZ) = tr((Λᵢ X) Y Z)` and `⟨d,d,d⟩` is the structure tensor of
  `(X,Y,Z) ↦ tr(XYZ)`, a rank-`rᵢ` triad decomposition of
  `matMulTensor ℂ dᵢ dᵢ dᵢ` evaluates to

    tr((Λᵢ X) Y Z) = ∑_{s<rᵢ} φᵢₛ(Λᵢ X) ψᵢₛ(Y) χᵢₛ(Z),

  a sum of rᵢ products of linear functionals. Composing with `X := (e gₓ)ᵢ`
  etc. exhibits `mulTensor ℂ G` as a sum of `∑ᵢ rᵢ` rank-one triads:

    RankLE (mulTensor ℂ G) (∑ i, R⟨dᵢ,dᵢ,dᵢ⟩).

  Main results:
    · `RankLE.of_fintype_sum` — a triad decomposition indexed by an arbitrary
      `Fintype` witnesses `RankLE T (Fintype.card ι)`.
    · `rankLE_mulTensor_of_algEquiv` — the transport along a fixed Wedderburn
      decomposition (no `NeZero` hypotheses needed).
    · `rank_mulTensor_le_sum_charDegrees` — the headline, packaged over
      `GroupTPP.CharDegrees.charDegrees G`.

  Reference: H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, arXiv:math/0307321, Theorem 4.1 (middle step).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import BilinearComplexity.GroupTensor
import BilinearComplexity.RankCalculus
import GroupTPP.CharDegrees

noncomputable section

namespace BilinearComplexity

open GroupTPP.CharDegrees

/-! ## 1. Fintype-indexed triad decompositions -/

/-- A triad decomposition indexed by an arbitrary `Fintype ι` witnesses
`RankLE T (Fintype.card ι)`: transport the index along `Fintype.equivFin`. -/
theorem RankLE.of_fintype_sum {k : Type*} [CommSemiring k] {a b c : ℕ}
    {ι : Type*} [Fintype ι] {T : Tensor k a b c}
    (u : ι → Fin a → k) (v : ι → Fin b → k) (w : ι → Fin c → k)
    (hT : ∀ i j l, T i j l = ∑ s : ι, u s i * v s j * w s l) :
    RankLE T (Fintype.card ι) := by
  refine ⟨fun s => u ((Fintype.equivFin ι).symm s),
          fun s => v ((Fintype.equivFin ι).symm s),
          fun s => w ((Fintype.equivFin ι).symm s), ?_⟩
  funext i j l
  rw [hT i j l]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm
    (fun t => u t i * v t j * w t l)).symm

/-! ## 2. The flattening pairing: `matMulTensor` as the trace form -/

/-- Row-major flattening of a square matrix, matching the
`finProdFinEquiv` packing convention of `matMulTensor`. -/
private def flat {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Fin (d * d) → ℂ :=
  fun x => X (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2

/-- The trilinear pairing of `matMulTensor` against three flattened matrices
is the trace form `tr (X * Y * Z)`. -/
private theorem trace_eq_pair {d : ℕ} (X Y Z : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (X * Y * Z)
      = ∑ x, ∑ y, ∑ z, matMulTensor ℂ d d d x y z
          * (flat X x * flat Y y * flat Z z) := by
  simp only [← Equiv.sum_comp (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)),
    matMulTensor_apply, flat, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- Pairing a triad-decomposed tensor against three vectors factors as a sum
of products of linear evaluations. -/
private theorem pair_of_decomp {a b c r : ℕ} (u : Fin r → Fin a → ℂ)
    (v : Fin r → Fin b → ℂ) (w : Fin r → Fin c → ℂ)
    (X : Fin a → ℂ) (Y : Fin b → ℂ) (Z : Fin c → ℂ) :
    ∑ x, ∑ y, ∑ z, (∑ s, u s x * v s y * w s z) * (X x * Y y * Z z)
      = ∑ s, (∑ x, u s x * X x) * (∑ y, v s y * Y y) * (∑ z, w s z * Z z) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  have h1 : ∀ (F : Fin a → Fin b → Fin c → Fin r → ℂ),
      ∑ x, ∑ y, ∑ z, ∑ s, F x y z s = ∑ s, ∑ x, ∑ y, ∑ z, F x y z s := fun F =>
    calc ∑ x, ∑ y, ∑ z, ∑ s, F x y z s
        = ∑ x, ∑ y, ∑ s, ∑ z, F x y z s :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_comm
      _ = ∑ x, ∑ s, ∑ y, ∑ z, F x y z s :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ s, ∑ x, ∑ y, ∑ z, F x y z s := Finset.sum_comm
  have h2 : ∀ (F : Fin a → Fin b → Fin c → ℂ),
      ∑ z, ∑ y, ∑ x, F x y z = ∑ x, ∑ y, ∑ z, F x y z := fun F =>
    calc ∑ z, ∑ y, ∑ x, F x y z
        = ∑ z, ∑ x, ∑ y, F x y z :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ x, ∑ z, ∑ y, F x y z := Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ z, F x y z :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [h1]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h2]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => by ring

/-! ## 3. Linear functionals on a matrix algebra are `tr (Λ · —)` -/

/-- The representing matrix of a linear functional `μ` on `d × d` matrices:
`lamMat μ q p = μ (E p q)`, so that `tr (lamMat μ * W) = μ W`. -/
private def lamMat {d : ℕ} (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun q p => μ (Matrix.single p q 1)

/-- Every linear functional on the matrix algebra is trace against its
representing matrix: `tr (lamMat μ * W) = μ W`. -/
private theorem trace_lamMat_mul {d : ℕ}
    (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (lamMat μ * W) = μ W := by
  have hL : Matrix.trace (lamMat μ * W)
      = ∑ q, ∑ p, μ (Matrix.single p q 1) * W p q := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, lamMat,
      Matrix.of_apply]
  have hR : μ W = ∑ p, ∑ q, W p q * μ (Matrix.single p q 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single W]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show Matrix.single p q (W p q) = (W p q) • Matrix.single p q (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  rw [hL, hR, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    mul_comm _ _

/-! ## 4. The per-block decomposition -/

/-- **The block lemma.** A triad decomposition of `matMulTensor ℂ d d d`
turns any linear functional of a triple matrix product `μ (X * Y * Z)` into a
sum of `r` products of three linear evaluations — the mode-1 evaluations
absorbing the representing matrix of `μ`. -/
private theorem blockDecomp {d r : ℕ} {u v w : Fin r → Fin (d * d) → ℂ}
    (h : matMulTensor ℂ d d d = fun x y z => ∑ s, u s x * v s y * w s z)
    (μ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ)
    (X Y Z : Matrix (Fin d) (Fin d) ℂ) :
    μ (X * Y * Z)
      = ∑ s, (∑ x', u s x' * flat (lamMat μ * X) x')
          * (∑ y', v s y' * flat Y y')
          * (∑ z', w s z' * flat Z z') := by
  rw [← trace_lamMat_mul μ (X * Y * Z),
    show lamMat μ * (X * Y * Z) = lamMat μ * X * Y * Z by
      simp only [mul_assoc],
    trace_eq_pair, h]
  exact pair_of_decomp u v w (flat (lamMat μ * X)) (flat Y) (flat Z)

/-! ## 5. The coefficient-of-identity functional on the group algebra -/

/-- The coefficient-of-identity functional `τ : ℂ[G] →ₗ[ℂ] ℂ`, `f ↦ f 1`. -/
private def evalOne (G : Type*) [Group G] : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem evalOne_apply {G : Type*} [Group G] (f : MonoidAlgebra ℂ G) :
    evalOne G f = f.coeff 1 :=
  rfl

/-! ## 6. The Wedderburn transport -/

section Transport

variable {G : Type*} [Group G] [Fintype G] {N : ℕ} {d : Fin N → ℕ}

/-- The transported functional `λ = τ ∘ e.symm` on the matrix side. -/
private def wLam
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] ℂ :=
  (evalOne G).comp e.symm.toLinearMap

/-- The per-block component of `wLam`: precompose with the block inclusion. -/
private def wMu
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin N) : Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] ℂ :=
  (wLam e).comp (LinearMap.single ℂ (fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i)

/-- The matrix image of the `x`-th group basis element. -/
private def wA
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (x : Fin (Fintype.card G)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  e (MonoidAlgebra.single ((Fintype.equivFin G).symm x) 1)

omit [Fintype G] in
private theorem wLam_e_apply
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (W : MonoidAlgebra ℂ G) : wLam e (e W) = W.coeff 1 := by
  simp [wLam, evalOne_apply]

/-- The tensor entry is the transported functional of the triple product. -/
private theorem mulTensor_eq_wLam [DecidableEq G]
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (x y z : Fin (Fintype.card G)) :
    mulTensor ℂ G x y z = wLam e (wA e x * wA e y * wA e z) := by
  have hprod : wA e x * wA e y * wA e z
      = e (MonoidAlgebra.single ((Fintype.equivFin G).symm x
          * (Fintype.equivFin G).symm y * (Fintype.equivFin G).symm z) 1) := by
    simp only [wA, ← map_mul, MonoidAlgebra.single_mul_single, one_mul]
  rw [mulTensor_apply, hprod, wLam_e_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

omit [Fintype G] in
/-- The transported functional splits over the matrix blocks. -/
private theorem wLam_split
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (M : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    wLam e M = ∑ i, wMu e i (M i) := by
  conv_lhs => rw [← LinearMap.sum_single_apply _ M]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **Wedderburn transport of the group-tensor rank** (Cohn–Umans Thm 4.1,
middle step), decomposition form: along any algebra isomorphism
`e : ℂ[G] ≃ₐ[ℂ] Π i, Mat_{dᵢ}(ℂ)`, the group tensor decomposes into
`∑ i, R⟨dᵢ,dᵢ,dᵢ⟩` rank-one triads. No `NeZero` hypothesis on the block
sizes is needed. -/
theorem rankLE_mulTensor_of_algEquiv [DecidableEq G]
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    RankLE (mulTensor ℂ G)
      (∑ i, rank (matMulTensor ℂ (d i) (d i) (d i))) := by
  -- optimal triad decompositions of the block matmul tensors
  have hdec : ∀ i : Fin N, RankLE (matMulTensor ℂ (d i) (d i) (d i))
      (rank (matMulTensor ℂ (d i) (d i) (d i))) := fun i => rankLE_rank _
  choose u v w huvw using hdec
  -- the entrywise triad identity, indexed by Σ i, Fin rᵢ
  have key : ∀ x y z, mulTensor ℂ G x y z
      = ∑ p : Σ i : Fin N, Fin (rank (matMulTensor ℂ (d i) (d i) (d i))),
          (∑ x', u p.1 p.2 x' * flat (lamMat (wMu e p.1) * wA e x p.1) x')
        * (∑ y', v p.1 p.2 y' * flat (wA e y p.1) y')
        * (∑ z', w p.1 p.2 z' * flat (wA e z p.1) z') := by
    intro x y z
    rw [mulTensor_eq_wLam e x y z, wLam_split]
    conv_rhs => rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun i _ =>
      blockDecomp (huvw i) (wMu e i) (wA e x i) (wA e y i) (wA e z i)
  have hR := RankLE.of_fintype_sum
      (fun (p : Σ i : Fin N, Fin (rank (matMulTensor ℂ (d i) (d i) (d i)))) x =>
        ∑ x', u p.1 p.2 x' * flat (lamMat (wMu e p.1) * wA e x p.1) x')
      (fun p y => ∑ y', v p.1 p.2 y' * flat (wA e y p.1) y')
      (fun p z => ∑ z', w p.1 p.2 z' * flat (wA e z p.1) z') key
  simpa using hR

end Transport

/-- **Wedderburn transport of the group-tensor rank** (Cohn–Umans
arXiv:math/0307321, Theorem 4.1, middle step): over `ℂ`, the rank of the
group-algebra multiplication tensor is at most the sum, over the character
degrees `d` of `G`, of the matrix-multiplication tensor ranks `R⟨d,d,d⟩`. -/
theorem rank_mulTensor_le_sum_charDegrees (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] :
    rank (mulTensor ℂ G)
      ≤ ((charDegrees G).map (fun d => rank (matMulTensor ℂ d d d))).sum := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨N, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hd
  have hEq : ((charDegrees G).map (fun m => rank (matMulTensor ℂ m m m))).sum
      = ∑ i, rank (matMulTensor ℂ (d i) (d i) (d i)) := by
    rw [charDegrees_eq_of_algEquiv G e, Multiset.map_map]
    rfl
  rw [hEq]
  exact rank_le_of_rankLE (rankLE_mulTensor_of_algEquiv e)

end BilinearComplexity
