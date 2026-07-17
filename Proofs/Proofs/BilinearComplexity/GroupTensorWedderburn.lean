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
      `Xlib.CharDegrees.charDegrees G`.

  Reference: H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, arXiv:math/0307321, Theorem 4.1 (middle step).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Proofs.BilinearComplexity.GroupTensor
import Proofs.BilinearComplexity.RankCalculus
import Xlib.CharDegrees

noncomputable section

namespace BilinearComplexity

open Xlib.CharDegrees

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
  sorry

/-- Pairing a triad-decomposed tensor against three vectors factors as a sum
of products of linear evaluations. -/
private theorem pair_of_decomp {a b c r : ℕ} (u : Fin r → Fin a → ℂ)
    (v : Fin r → Fin b → ℂ) (w : Fin r → Fin c → ℂ)
    (X : Fin a → ℂ) (Y : Fin b → ℂ) (Z : Fin c → ℂ) :
    ∑ x, ∑ y, ∑ z, (∑ s, u s x * v s y * w s z) * (X x * Y y * Z z)
      = ∑ s, (∑ x, u s x * X x) * (∑ y, v s y * Y y) * (∑ z, w s z * Z z) := by
  sorry

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
  sorry

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
  sorry

/-! ## 5. The coefficient-of-identity functional on the group algebra -/

/-- The coefficient-of-identity functional `τ : ℂ[G] →ₗ[ℂ] ℂ`, `f ↦ f 1`. -/
private def evalOne (G : Type*) [Group G] : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem evalOne_apply {G : Type*} [Group G] (f : MonoidAlgebra ℂ G) :
    evalOne G f = f 1 :=
  rfl

/-! ## 6. The Wedderburn transport -/

/-- **Wedderburn transport of the group-tensor rank** (Cohn–Umans Thm 4.1,
middle step), decomposition form: along any algebra isomorphism
`e : ℂ[G] ≃ₐ[ℂ] Π i, Mat_{dᵢ}(ℂ)`, the group tensor decomposes into
`∑ i, R⟨dᵢ,dᵢ,dᵢ⟩` rank-one triads. No `NeZero` hypothesis on the block
sizes is needed. -/
theorem rankLE_mulTensor_of_algEquiv {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {N : ℕ} {d : Fin N → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    RankLE (mulTensor ℂ G)
      (∑ i, rank (matMulTensor ℂ (d i) (d i) (d i))) := by
  classical
  -- optimal triad decompositions of the block matmul tensors
  have hdec : ∀ i : Fin N, RankLE (matMulTensor ℂ (d i) (d i) (d i))
      (rank (matMulTensor ℂ (d i) (d i) (d i))) := fun i => rankLE_rank _
  choose u v w huvw using hdec
  -- the functional λ = τ ∘ e.symm and its per-block components
  let lam : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] ℂ :=
    (evalOne G).comp e.symm.toLinearMap
  let mu : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] ℂ :=
    fun i => lam.comp (LinearMap.single ℂ (fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i)
  -- the matrix images of the group basis
  let A : Fin (Fintype.card G) → ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
    fun x => e (MonoidAlgebra.single ((Fintype.equivFin G).symm x) 1)
  -- the entrywise triad identity, indexed by Σ i, Fin rᵢ
  have key : ∀ x y z, mulTensor ℂ G x y z
      = ∑ p : Σ i : Fin N, Fin (rank (matMulTensor ℂ (d i) (d i) (d i))),
          (∑ x', u p.1 p.2 x' * flat (lamMat (mu p.1) * A x p.1) x')
        * (∑ y', v p.1 p.2 y' * flat (A y p.1) y')
        * (∑ z', w p.1 p.2 z' * flat (A z p.1) z') := by
    sorry
  have hR := RankLE.of_fintype_sum
      (fun (p : Σ i : Fin N, Fin (rank (matMulTensor ℂ (d i) (d i) (d i)))) x =>
        ∑ x', u p.1 p.2 x' * flat (lamMat (mu p.1) * A x p.1) x')
      (fun p y => ∑ y', v p.1 p.2 y' * flat (A y p.1) y')
      (fun p z => ∑ z', w p.1 p.2 z' * flat (A z p.1) z') key
  simpa using hR

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
