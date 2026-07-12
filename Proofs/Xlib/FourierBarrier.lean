import Xlib.TPP

/-!
# The Fourier/Parseval layer for the BCGPU `n(G)` barrier

This file builds the nonabelian Fourier-analytic toolkit needed for BCGPU
Theorem 3.2 (`thm:gowerstrick`, arXiv:2204.03826) on top of an *arbitrary*
indexed Wedderburn decomposition `e : ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`.

The Fourier transform of `x : ℂ[G]` at the "irrep" `i` *is* the block `(e x) i`;
no representation-theoretic vocabulary is needed.  The layer has six parts:

1. **Counting** (`gowersElt_apply_one`, `coeff_star_a/b/c`, `mass_gowersElt`):
   the coefficients at `1` of the six-fold Gowers element
   `(1_S ⋆ 1_{T⁻¹}) (1_T ⋆ 1_{U⁻¹}) (1_U ⋆ 1_{S⁻¹})` and of the three four-fold
   Parseval elements, computed from the Triple Product Property.
2. **Fourier inversion** (`inversion`): `|G| · x(1) = Σᵢ dᵢ · Tr((e x)ᵢ)`, proved
   by computing the trace of left multiplication by `x` on both sides of `e`.
3. **Frobenius norm toolkit** (`sq_frobenius_norm`, `trace_conjTranspose_mul_self`,
   `norm_trace_mul_le`): the trace/Hilbert–Schmidt Cauchy–Schwarz inequalities,
   using the scoped `Norms.Frobenius` instances.
4. **The unitarian trick** (`exists_isUnitary`): every decomposition can be
   conjugated blockwise (by the positive factor of the averaged Gram matrix
   `Qᵢ = Σ_g ρᵢ(g)ᴴρᵢ(g)`) into one satisfying
   `e (single g⁻¹ 1) i = ((e (single g 1)) i)ᴴ` — i.e. all blocks are unitary
   representations.  This is where `ℂ` (star, positivity) enters irreducibly.
5. **Unitary consequences**: Parseval (`parseval_norm_sum`), nonnegativity of
   one-dimensional blocks of the Gowers element (`trace_gowersElt_one_dim`),
   the trivial block (`exists_trivial_block`, via the central idempotent
   `|G|⁻¹ Σ_g g`), and `exists_one_lt_dim_of_nonabelian`.
6. **The master bound** (`master_bound`): for a unitary decomposition and any
   `n ≥ 2` lower-bounding all block dimensions `> 1`, a TPP triple of nonempty
   sets satisfies `|S||T||U| ≤ |G|^{3/2}/√n + |G|`.

`Xlib.BCGPUBarrier` instantiates `n := minNontrivIrrepDim G` through the
`Xlib.CharDegrees` bridge to obtain BCGPU Theorem 3.2 and its corollaries.
-/

open scoped BigOperators

namespace Xlib.FourierBarrier

open Xlib.TPP

noncomputable section

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Indicator elements of the group algebra -/

/-- The indicator element `Σ_{x ∈ X} x` of a finset `X ⊆ G` in `ℂ[G]`. -/
def ind (X : Finset G) : MonoidAlgebra ℂ G :=
  ∑ x ∈ X, MonoidAlgebra.single x 1

/-- The inverted indicator element `Σ_{x ∈ X} x⁻¹`, the formal star of `ind X`. -/
def indInv (X : Finset G) : MonoidAlgebra ℂ G :=
  ∑ x ∈ X, MonoidAlgebra.single x⁻¹ 1

/-- The six-fold **Gowers element** `(1_S 1_{T⁻¹}) · (1_T 1_{U⁻¹}) · (1_U 1_{S⁻¹})`
whose coefficient at `1` counts the TPP-collisions. -/
def gowersElt (S T U : Finset G) : MonoidAlgebra ℂ G :=
  ind S * indInv T * (ind T * indInv U) * (ind U * indInv S)

/-! ### Coefficient counting under the TPP -/

/-- Product of two indicator-type sums as a single sum over the product finset. -/
private lemma sum_single_mul {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → G) (g : κ → G) :
    ((∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) *
        (∑ b ∈ B, MonoidAlgebra.single (g b) (1 : ℂ)))
      = ∑ p ∈ A ×ˢ B, MonoidAlgebra.single (f p.1 * g p.2) (1 : ℂ) := by
  rw [Finset.sum_mul_sum, Finset.sum_product]
  simp [MonoidAlgebra.single_mul_single]

/-- Evaluating an indicator-type sum at a point counts the fiber. -/
private lemma sum_single_apply {ι : Type*} (A : Finset ι) (f : ι → G) (h : G) :
    (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) h
      = ((A.filter (fun a => f a = h)).card : ℂ) := by
  classical
  rw [Finsupp.finset_sum_apply]
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [MonoidAlgebra.single_apply]

/-- Total mass of an indicator-type sum. -/
private lemma sum_single_mass {ι : Type*} (A : Finset ι) (f : ι → G) :
    (∑ g : G, (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) g) = (A.card : ℂ) := by
  classical
  rw [Finset.sum_comm' (t' := A) (s' := fun _ => Finset.univ)
      (by simp)]
  · simp [Finsupp.finset_sum_apply, MonoidAlgebra.single_apply]
  sorry

/-- The Gowers element as one sum over the six-fold product finset. -/
private lemma gowersElt_eq_sum (S T U : Finset G) :
    gowersElt S T U
      = ∑ p ∈ ((S ×ˢ T) ×ˢ (T ×ˢ U)) ×ˢ (U ×ˢ S),
          MonoidAlgebra.single
            (p.1.1.1 * p.1.1.2⁻¹ * (p.1.2.1 * p.1.2.2⁻¹) * (p.2.1 * p.2.2⁻¹))
            (1 : ℂ) := by
  unfold gowersElt ind indInv
  rw [sum_single_mul S T id (·⁻¹), sum_single_mul T U id (·⁻¹),
    sum_single_mul (S ×ˢ T) (T ×ˢ U) (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹),
    sum_single_mul (((S ×ˢ T) ×ˢ (T ×ˢ U))) (U ×ˢ S)
      (fun p => p.1.1 * p.1.2⁻¹ * (p.2.1 * p.2.2⁻¹)) (fun p => p.1 * p.2⁻¹)]

/-- **The six-fold TPP count**: the coefficient of the Gowers element at the
identity is exactly `|S| |T| |U|`. -/
theorem gowersElt_apply_one {S T U : Finset G} (h : TripleProductProperty S T U) :
    gowersElt S T U 1 = ((S.card * T.card * U.card : ℕ) : ℂ) := by
  sorry

/-- **Total mass of the Gowers element** is `(|S| |T| |U|)²` (no TPP needed). -/
theorem mass_gowersElt (S T U : Finset G) :
    (∑ g : G, gowersElt S T U g) = (((S.card * T.card * U.card : ℕ) : ℂ)) ^ 2 := by
  sorry

/-- **Parseval count for `a = 1_S 1_{T⁻¹}`**: the coefficient of `a⋆ a` at `1`
is `|S| |T|` (needs `U` nonempty to run the TPP). -/
theorem coeff_star_a {S T U : Finset G} (h : TripleProductProperty S T U)
    (hU : U.Nonempty) :
    ((ind T * indInv S) * (ind S * indInv T)) 1 = ((S.card * T.card : ℕ) : ℂ) := by
  sorry

/-- **Parseval count for `b = 1_T 1_{U⁻¹}`** (needs `S` nonempty). -/
theorem coeff_star_b {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) :
    ((ind U * indInv T) * (ind T * indInv U)) 1 = ((T.card * U.card : ℕ) : ℂ) := by
  sorry

/-- **Parseval count for `c = 1_U 1_{S⁻¹}`** (needs `T` nonempty). -/
theorem coeff_star_c {S T U : Finset G} (h : TripleProductProperty S T U)
    (hT : T.Nonempty) :
    ((ind S * indInv U) * (ind U * indInv S)) 1 = ((U.card * S.card : ℕ) : ℂ) := by
  sorry

/-! ### Fourier inversion: the trace of left multiplication -/

/-- Coordinates of a matrix in the standard basis. -/
private lemma stdBasis_repr {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) (p : m × n) :
    (Matrix.stdBasis ℂ m n).repr M p = M p.1 p.2 := by
  sorry

/-- Left multiplication in a product ring hits `Pi.single` componentwise. -/
private lemma mul_pi_single {k : ℕ} {d : Fin k → ℕ}
    (y : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : Fin k)
    (M : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    y * Pi.single i M = Pi.single i (y i * M) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- The trace of left multiplication by `x` on `ℂ[G]` is `|G| · x(1)`:
each basis vector `g` contributes the diagonal coefficient `x(1)`. -/
theorem trace_mulLeft_monoidAlgebra (x : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G) (LinearMap.mulLeft ℂ x)
      = (Fintype.card G : ℂ) * x 1 := by
  sorry

/-- The trace of left multiplication by `y` on `Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`
is `Σ i, d i · Tr(y i)`: block `i` consists of `d i` copies of the column module. -/
theorem trace_mulLeft_piMat {k : ℕ} {d : Fin k → ℕ}
    (y : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (LinearMap.mulLeft ℂ y)
      = ∑ i, (d i : ℂ) * (y i).trace := by
  sorry

/-- **Fourier inversion at the identity**: for any algebra isomorphism
`e : ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`,
\[ |G| \cdot x(1) = \sum_i d_i \operatorname{Tr}((e x)_i). \]
Both sides compute the trace of left multiplication by `x`, which is invariant
under transport along `e`. -/
theorem inversion {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (x : MonoidAlgebra ℂ G) :
    (Fintype.card G : ℂ) * x 1 = ∑ i, (d i : ℂ) * ((e x) i).trace := by
  sorry

/-! ### The Frobenius norm toolkit -/

open scoped Norms.Frobenius in
/-- The squared Frobenius norm as an entry sum. -/
private lemma sq_frobenius_norm {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ‖M‖ ^ 2 = ∑ r, ∑ c, ‖M r c‖ ^ 2 := by
  sorry

open scoped Norms.Frobenius in
/-- `Tr(Mᴴ M)` is the (real, nonnegative) squared Frobenius norm. -/
private lemma trace_conjTranspose_mul_self {m : Type*} [Fintype m]
    (M : Matrix m m ℂ) : (Mᴴ * M).trace = ((‖M‖ ^ 2 : ℝ) : ℂ) := by
  sorry

open scoped Norms.Frobenius in
/-- **Hilbert–Schmidt Cauchy–Schwarz**: `|Tr(M N)| ≤ ‖M‖ ‖N‖` in the Frobenius
norm. -/
private lemma norm_trace_mul_le {m : Type*} [Fintype m]
    (M N : Matrix m m ℂ) : ‖(M * N).trace‖ ≤ ‖M‖ * ‖N‖ := by
  sorry

/-! ### The unitarian trick: upgrading a decomposition to a star-compatible one -/

/-- A Wedderburn decomposition is **unitary** when it intertwines the canonical
stars: the block of `g⁻¹` is the conjugate transpose of the block of `g`.
Equivalently, every block map `g ↦ (e (single g 1)) i` is a unitary matrix
representation of `G`. -/
def IsUnitary {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) : Prop :=
  ∀ (g : G) (i : Fin k),
    (e (MonoidAlgebra.single g⁻¹ 1)) i = ((e (MonoidAlgebra.single g 1)) i)ᴴ

/-- Blockwise conjugation by units, as an algebra automorphism of the product
of matrix algebras. -/
private def piConjAlgEquiv {k : ℕ} {d : Fin k → ℕ}
    (u : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℂ)ˣ) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₐ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) where
  toFun y := fun i => (u i : Matrix _ _ ℂ) * y i * ((u i)⁻¹ : (Matrix _ _ ℂ)ˣ)
  invFun y := fun i => ((u i)⁻¹ : (Matrix _ _ ℂ)ˣ) * y i * (u i : Matrix _ _ ℂ)
  left_inv y := by
    funext i
    simp [← mul_assoc]
  right_inv y := by
    funext i
    simp [← mul_assoc]
  map_mul' y z := by
    funext i
    simp only [Pi.mul_apply]
    calc (u i : Matrix _ _ ℂ) * (y i * z i) * ((u i)⁻¹ : (Matrix _ _ ℂ)ˣ)
        = (u i : Matrix _ _ ℂ) * y i * (((u i)⁻¹ : (Matrix _ _ ℂ)ˣ) *
            (u i : Matrix _ _ ℂ)) * z i * ((u i)⁻¹ : (Matrix _ _ ℂ)ˣ) := by
          simp [mul_assoc]
      _ = _ := by simp [mul_assoc]
  map_add' y z := by
    funext i
    simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    funext i
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [Matrix.mul_smul_one_eq_smul_mul_one]
    sorry

/-- **The unitarian trick** (Weyl): any indexed Wedderburn decomposition of the
group algebra can be conjugated blockwise into a *unitary* one with the same
block dimensions.  Conjugate block `i` by the positive factor `B i` of the
averaged Gram matrix `Q i = Σ_g ρᵢ(g)ᴴ ρᵢ(g) = (B i)ᴴ (B i)`. -/
theorem exists_isUnitary {k : ℕ} {d : Fin k → ℕ}
    (e₀ : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ,
      IsUnitary e := by
  sorry

/-! ### Consequences of unitarity -/

section Unitary

variable {k : ℕ} {d : Fin k → ℕ}
  {e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ}

/-- Under a unitary decomposition, the block of `indInv X` is the conjugate
transpose of the block of `ind X`. -/
theorem IsUnitary.e_indInv (he : IsUnitary e) (X : Finset G) (i : Fin k) :
    (e (indInv X)) i = ((e (ind X)) i)ᴴ := by
  unfold ind indInv
  rw [map_sum, map_sum]
  simp only [Finset.sum_apply]
  rw [← Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun x _ => he x i

/-- The block of the reversed product `1_Y 1_{X⁻¹}` is the conjugate transpose
of the block of `1_X 1_{Y⁻¹}`. -/
theorem IsUnitary.e_star_prod (he : IsUnitary e) (X Y : Finset G) (i : Fin k) :
    (e (ind Y * indInv X)) i = ((e (ind X * indInv Y)) i)ᴴ := by
  rw [map_mul, map_mul]
  simp only [Pi.mul_apply]
  rw [he.e_indInv X i, he.e_indInv Y i, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

open scoped Norms.Frobenius in
/-- **Parseval for an indicator product**: if the coefficient of `x⋆ x` at `1`
is `|X| |Y|` (a TPP count), then the Fourier blocks of `x = 1_X 1_{Y⁻¹}` satisfy
\[ \sum_i d_i \, \|(e x)_i\|^2 = |G| \, |X| \, |Y|. \] -/
theorem parseval_norm_sum (he : IsUnitary e) (X Y : Finset G)
    (hcount : ((ind Y * indInv X) * (ind X * indInv Y)) 1
      = ((X.card * Y.card : ℕ) : ℂ)) :
    ∑ i, (d i : ℝ) * ‖(e (ind X * indInv Y)) i‖ ^ 2
      = (Fintype.card G : ℝ) * X.card * Y.card := by
  sorry

/-- In a one-dimensional block, the trace of a product is the product of the
traces. -/
private lemma trace_mul_dim_one {m : ℕ} (hm : m = 1)
    (M N : Matrix (Fin m) (Fin m) ℂ) : (M * N).trace = M.trace * N.trace := by
  subst hm
  simp [Matrix.trace, Matrix.mul_apply]

/-- **One-dimensional blocks of the Gowers element are nonnegative reals**:
in a `d i = 1` block the six factors multiply to `|z_S|² |z_T|² |z_U|² ≥ 0`. -/
theorem trace_gowersElt_one_dim (he : IsUnitary e) {i : Fin k} (hd : d i = 1)
    (S T U : Finset G) :
    ∃ r : ℝ, 0 ≤ r ∧ ((e (gowersElt S T U)) i).trace = (r : ℂ) := by
  sorry

end Unitary

/-! ### The trivial block and the nonabelian dimension witness -/

/-- **The trivial block.** Any decomposition has a distinguished index `i₀` with
`d i₀ = 1` on which every `x` acts by its total mass: `(e x) i₀ = (Σ_g x g) • 1`.
It is located by chasing the central idempotent `p = |G|⁻¹ Σ_g g`. -/
theorem exists_trivial_block {k : ℕ} {d : Fin k → ℕ} [∀ i, NeZero (d i)]
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ i₀ : Fin k, d i₀ = 1 ∧
      ∀ x : MonoidAlgebra ℂ G, (e x) i₀ = (∑ g : G, x g) • 1 := by
  sorry

/-- A nonabelian group has a block of dimension `> 1`: otherwise the product of
`≤ 1`-dimensional matrix algebras would be commutative, hence so would `ℂ[G]`,
hence so would `G`. -/
theorem exists_one_lt_dim_of_nonabelian {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hG : ∃ a b : G, a * b ≠ b * a) :
    ∃ i, 1 < d i := by
  sorry

/-! ### The master bound -/

open scoped Norms.Frobenius in
/-- **The master Gowers-trick bound** (the analytic core of BCGPU Theorem 3.2).

Let `e` be a unitary Wedderburn decomposition of `ℂ[G]` with block dimensions
`d i ≥ 1`, and let `n ≥ 2` lower-bound every block dimension exceeding `1`.
Then any TPP triple of nonempty sets satisfies
\[ |S|\,|T|\,|U| \le \frac{|G|^{3/2}}{\sqrt n} + |G|. \]

Proof: Fourier inversion evaluates `|G| |S||T||U|` as `Σᵢ dᵢ Tr((e(abc))ᵢ)` for
the Gowers element `abc`; the trivial block contributes `(|S||T||U|)²`, the other
one-dimensional blocks are nonnegative, and each block of dimension `> 1` is
bounded through the Hilbert–Schmidt Cauchy–Schwarz inequality and Parseval by
`√(|G||S||T|/n) · √(|G||T||U|) · √(|G||U||S|)` in total. -/
theorem master_bound {k : ℕ} {d : Fin k → ℕ} [∀ i, NeZero (d i)]
    {e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ}
    (he : IsUnitary e) {n : ℕ} (hn : 2 ≤ n) (hnd : ∀ i, 1 < d i → n ≤ d i)
    {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty) :
    (S.card * T.card * U.card : ℝ)
      ≤ (Fintype.card G : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt n
        + (Fintype.card G : ℝ) := by
  sorry

end

end Xlib.FourierBarrier
