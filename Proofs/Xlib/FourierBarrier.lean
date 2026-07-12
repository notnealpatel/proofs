import Xlib.TPP

/-!
# The Fourier/Parseval layer for the BCGPU `n(G)` barrier

This file builds the nonabelian Fourier-analytic toolkit needed for BCGPU
Theorem 3.2 (`thm:gowerstrick`, arXiv:2204.03826) on top of an *arbitrary*
indexed Wedderburn decomposition
`e : ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`.

The Fourier transform of `x : ℂ[G]` at the "irrep" `i` *is* the block `(e x) i`;
no representation-theoretic vocabulary is needed.  The layer has six parts:

1. **Counting** (`gowersElt_apply_one`, `coeff_star_a/b/c`, `mass_gowersElt`):
   the coefficients at `1` of the six-fold Gowers element
   `(1_S 1_{T⁻¹}) (1_T 1_{U⁻¹}) (1_U 1_{S⁻¹})` and of the three four-fold
   Parseval elements, computed from the Triple Product Property.
2. **Fourier inversion** (`inversion`): `|G| · x(1) = Σᵢ dᵢ · Tr((e x)ᵢ)`, proved
   by computing the trace of left multiplication by `x` on both sides of `e`.
3. **Frobenius norm toolkit** (`sq_frobenius_norm`, `trace_conjTranspose_mul_self`,
   `norm_trace_mul_le`): the trace/Hilbert–Schmidt Cauchy–Schwarz inequalities,
   using the scoped `Matrix.Norms.Frobenius` instances.
4. **The unitarian trick** (`exists_isUnitary`): every decomposition can be
   conjugated blockwise (by the positive factor of the averaged Gram matrix
   `Qᵢ = Σ_g ρᵢ(g)ᴴρᵢ(g)`) into one satisfying
   `e (single g⁻¹ 1) i = ((e (single g 1)) i)ᴴ` — i.e. all blocks are unitary
   representations.  This is where `ℂ` (star, positivity) enters irreducibly.
5. **Unitary consequences**: Parseval (`parseval_norm_sum`), nonnegativity of
   one-dimensional blocks of the Gowers element (`trace_gowersElt_one_dim`),
   the trivial block (`exists_trivial_block`, via the central idempotent
   `p = |G|⁻¹ Σ_g g`), and `exists_one_lt_dim_of_nonabelian`.
6. **The master bound** (`master_bound`): for a unitary decomposition and any
   `n ≥ 2` lower-bounding all block dimensions `> 1`, a TPP triple of nonempty
   sets satisfies `|S||T||U| ≤ |G|^{3/2}/√n + |G|`.

`Xlib.BCGPUBarrier` instantiates `n := minNontrivIrrepDim G` through the
`Xlib.CharDegrees` bridge to obtain BCGPU Theorem 3.2 and its corollaries.
-/

open scoped BigOperators
open scoped Matrix

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
whose coefficient at `1` counts the TPP collisions. -/
def gowersElt (S T U : Finset G) : MonoidAlgebra ℂ G :=
  ind S * indInv T * (ind T * indInv U) * (ind U * indInv S)

/-! ### Coefficient counting under the TPP -/

omit [Fintype G] [DecidableEq G] in
/-- Product of two indicator-type sums as a single sum over the product finset. -/
private lemma sum_single_mul {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → G) (g : κ → G) :
    ((∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) *
        (∑ b ∈ B, MonoidAlgebra.single (g b) (1 : ℂ)))
      = ∑ p ∈ A ×ˢ B, MonoidAlgebra.single (f p.1 * g p.2) (1 : ℂ) := by
  rw [Finset.sum_mul_sum, Finset.sum_product]
  simp [MonoidAlgebra.single_mul_single]

omit [Fintype G] in
/-- Evaluating an indicator-type sum at a point counts the fiber. -/
private lemma sum_single_apply {ι : Type*} (A : Finset ι) (f : ι → G) (h : G) :
    (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) h
      = ((A.filter (fun a => f a = h)).card : ℂ) := by
  classical
  calc (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) h
      = ∑ a ∈ A, (MonoidAlgebra.single (f a) (1 : ℂ) : MonoidAlgebra ℂ G) h :=
        Finset.sum_apply' h
    _ = ∑ a ∈ A, if f a = h then (1 : ℂ) else 0 :=
        Finset.sum_congr rfl fun a _ => Finsupp.single_apply
    _ = ((A.filter (fun a => f a = h)).card : ℂ) := Finset.sum_boole _ _

/-- Total mass of an indicator-type sum. -/
private lemma sum_single_mass {ι : Type*} (A : Finset ι) (f : ι → G) :
    (∑ g : G, (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) g) = (A.card : ℂ) := by
  classical
  calc ∑ g : G, (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) g
      = ∑ g : G, ∑ a ∈ A, (MonoidAlgebra.single (f a) (1 : ℂ) : MonoidAlgebra ℂ G) g :=
        Finset.sum_congr rfl fun g _ => Finset.sum_apply' g
    _ = ∑ a ∈ A, ∑ g : G, (MonoidAlgebra.single (f a) (1 : ℂ) : MonoidAlgebra ℂ G) g :=
        Finset.sum_comm
    _ = ∑ _a ∈ A, (1 : ℂ) :=
        Finset.sum_congr rfl fun a _ => by simp [Finsupp.single_apply]
    _ = (A.card : ℂ) := by simp

/-- The Gowers element as one sum over the six-fold product finset. -/
private lemma gowersElt_eq_sum (S T U : Finset G) :
    gowersElt S T U
      = ∑ p ∈ ((S ×ˢ T) ×ˢ (T ×ˢ U)) ×ˢ (U ×ˢ S),
          MonoidAlgebra.single
            (p.1.1.1 * p.1.1.2⁻¹ * (p.1.2.1 * p.1.2.2⁻¹) * (p.2.1 * p.2.2⁻¹))
            (1 : ℂ) := by
  unfold gowersElt ind indInv
  rw [sum_single_mul S T (fun x => x) (·⁻¹), sum_single_mul T U (fun x => x) (·⁻¹),
    sum_single_mul U S (fun x => x) (·⁻¹),
    sum_single_mul (S ×ˢ T) (T ×ˢ U) (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹),
    sum_single_mul (((S ×ˢ T) ×ˢ (T ×ˢ U))) (U ×ˢ S)
      (fun p => p.1.1 * p.1.2⁻¹ * (p.2.1 * p.2.2⁻¹)) (fun p => p.1 * p.2⁻¹)]

/-- **The six-fold TPP count**: the coefficient of the Gowers element at the
identity is exactly `|S| |T| |U|`. -/
theorem gowersElt_apply_one {S T U : Finset G} (h : TripleProductProperty S T U) :
    gowersElt S T U 1 = ((S.card * T.card * U.card : ℕ) : ℂ) := by
  classical
  rw [gowersElt_eq_sum, sum_single_apply]
  norm_cast
  have hcard : (S ×ˢ T ×ˢ U).card = S.card * T.card * U.card := by
    rw [Finset.card_product, Finset.card_product]; ring
  rw [← hcard]
  refine Finset.card_bij' (fun p _ => (p.1.1.1, p.1.1.2, p.1.2.2))
    (fun q _ => (((q.1, q.2.1), (q.2.1, q.2.2)), (q.2.2, q.1))) ?hi ?hj ?left ?right
  case hi =>
    -- i maps into S ×ˢ T ×ˢ U
    rintro ⟨⟨⟨s, t⟩, ⟨t', u⟩⟩, ⟨u', s'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_product]
    exact ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2.2⟩
  case hj =>
    -- j maps into the filtered set
    rintro ⟨s, t, u⟩ hq
    simp only [Finset.mem_product] at hq
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨⟨⟨hq.1, hq.2.1⟩, hq.2.1, hq.2.2⟩, hq.2.2, hq.1⟩, ?_⟩
    group
  case left =>
    -- j ∘ i = id on the filtered set (this is where the TPP enters)
    rintro ⟨⟨⟨s, t⟩, ⟨t', u⟩⟩, ⟨u', s'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨⟨hs, ht⟩, ht', hu⟩, hu', hs'⟩, hrel⟩ := hp
    have hrel' : s'⁻¹ * s * t⁻¹ * t' * u⁻¹ * u' = 1 := by
      have hconj : s'⁻¹ * s * t⁻¹ * t' * u⁻¹ * u'
          = s'⁻¹ * (s * t⁻¹ * (t' * u⁻¹) * (u' * s'⁻¹)) * s' := by group
      rw [hconj, hrel]; group
    obtain ⟨hss', htt', huu'⟩ := h s hs s' hs' t' ht' t ht u' hu' u hu hrel'
    subst_vars
    rfl
  case right =>
    -- i ∘ j = id on S ×ˢ T ×ˢ U
    rintro ⟨s, t, u⟩ _
    rfl

/-- **Total mass of the Gowers element** is `(|S| |T| |U|)²` (no TPP needed). -/
theorem mass_gowersElt (S T U : Finset G) :
    (∑ g : G, gowersElt S T U g) = (((S.card * T.card * U.card : ℕ) : ℂ)) ^ 2 := by
  classical
  calc (∑ g : G, gowersElt S T U g)
      = ((((S ×ˢ T) ×ˢ (T ×ˢ U)) ×ˢ (U ×ˢ S)).card : ℂ) := by
        rw [Finset.sum_congr rfl fun g _ => by rw [gowersElt_eq_sum]]
        exact sum_single_mass _ _
    _ = _ := by
        simp only [Finset.card_product]
        push_cast
        ring

/-- **Parseval count for `a = 1_S 1_{T⁻¹}`**: the coefficient of `a⋆ a` at `1`
is `|S| |T|` (needs `U` nonempty to run the TPP). -/
theorem coeff_star_a {S T U : Finset G} (h : TripleProductProperty S T U)
    (hU : U.Nonempty) :
    ((ind T * indInv S) * (ind S * indInv T)) 1 = ((S.card * T.card : ℕ) : ℂ) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hU
  have hexp : (ind T * indInv S) * (ind S * indInv T)
      = ∑ p ∈ (T ×ˢ S) ×ˢ (S ×ˢ T),
          MonoidAlgebra.single (p.1.1 * p.1.2⁻¹ * (p.2.1 * p.2.2⁻¹)) (1 : ℂ) := by
    unfold ind indInv
    rw [sum_single_mul T S (fun x => x) (·⁻¹), sum_single_mul S T (fun x => x) (·⁻¹),
      sum_single_mul (T ×ˢ S) (S ×ˢ T) (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹)]
  rw [hexp, sum_single_apply]
  norm_cast
  have hcard : (T ×ˢ S).card = S.card * T.card := by
    rw [Finset.card_product]; ring
  rw [← hcard]
  refine Finset.card_bij' (fun p _ => p.1)
    (fun q _ => ((q.1, q.2), (q.2, q.1))) ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨⟨t, s⟩, ⟨s', t'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_product.mpr ⟨hp.1.1.1, hp.1.1.2⟩
  case hj =>
    rintro ⟨t, s⟩ hq
    simp only [Finset.mem_product] at hq
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hq.1, hq.2⟩, hq.2, hq.1⟩, by group⟩
  case left =>
    rintro ⟨⟨t, s⟩, ⟨s', t'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨ht, hs⟩, hs', ht'⟩, hrel⟩ := hp
    have hrel' : s⁻¹ * s' * t'⁻¹ * t * u₀⁻¹ * u₀ = 1 := by
      have hconj : s⁻¹ * s' * t'⁻¹ * t * u₀⁻¹ * u₀
          = t⁻¹ * (t * s⁻¹ * (s' * t'⁻¹)) * t := by group
      rw [hconj, hrel]; group
    obtain ⟨hss', htt', -⟩ := h s' hs' s hs t ht t' ht' u₀ hu₀ u₀ hu₀ hrel'
    subst_vars
    rfl
  case right =>
    rintro ⟨t, s⟩ _
    rfl

/-- **Parseval count for `b = 1_T 1_{U⁻¹}`** (needs `S` nonempty). -/
theorem coeff_star_b {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : S.Nonempty) :
    ((ind U * indInv T) * (ind T * indInv U)) 1 = ((T.card * U.card : ℕ) : ℂ) := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  have hexp : (ind U * indInv T) * (ind T * indInv U)
      = ∑ p ∈ (U ×ˢ T) ×ˢ (T ×ˢ U),
          MonoidAlgebra.single (p.1.1 * p.1.2⁻¹ * (p.2.1 * p.2.2⁻¹)) (1 : ℂ) := by
    unfold ind indInv
    rw [sum_single_mul U T (fun x => x) (·⁻¹), sum_single_mul T U (fun x => x) (·⁻¹),
      sum_single_mul (U ×ˢ T) (T ×ˢ U) (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹)]
  rw [hexp, sum_single_apply]
  norm_cast
  have hcard : (U ×ˢ T).card = T.card * U.card := by
    rw [Finset.card_product]; ring
  rw [← hcard]
  refine Finset.card_bij' (fun p _ => p.1)
    (fun q _ => ((q.1, q.2), (q.2, q.1))) ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨⟨u, t⟩, ⟨t', u'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_product.mpr ⟨hp.1.1.1, hp.1.1.2⟩
  case hj =>
    rintro ⟨u, t⟩ hq
    simp only [Finset.mem_product] at hq
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hq.1, hq.2⟩, hq.2, hq.1⟩, by group⟩
  case left =>
    rintro ⟨⟨u, t⟩, ⟨t', u'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hu, ht⟩, ht', hu'⟩, hrel⟩ := hp
    have hrel' : s₀⁻¹ * s₀ * t⁻¹ * t' * u'⁻¹ * u = 1 := by
      have hconj : s₀⁻¹ * s₀ * t⁻¹ * t' * u'⁻¹ * u
          = u⁻¹ * (u * t⁻¹ * (t' * u'⁻¹)) * u := by group
      rw [hconj, hrel]; group
    obtain ⟨-, htt', huu'⟩ := h s₀ hs₀ s₀ hs₀ t' ht' t ht u hu u' hu' hrel'
    subst_vars
    rfl
  case right =>
    rintro ⟨u, t⟩ _
    rfl

/-- **Parseval count for `c = 1_U 1_{S⁻¹}`** (needs `T` nonempty). -/
theorem coeff_star_c {S T U : Finset G} (h : TripleProductProperty S T U)
    (hT : T.Nonempty) :
    ((ind S * indInv U) * (ind U * indInv S)) 1 = ((U.card * S.card : ℕ) : ℂ) := by
  classical
  obtain ⟨t₀, ht₀⟩ := hT
  have hexp : (ind S * indInv U) * (ind U * indInv S)
      = ∑ p ∈ (S ×ˢ U) ×ˢ (U ×ˢ S),
          MonoidAlgebra.single (p.1.1 * p.1.2⁻¹ * (p.2.1 * p.2.2⁻¹)) (1 : ℂ) := by
    unfold ind indInv
    rw [sum_single_mul S U (fun x => x) (·⁻¹), sum_single_mul U S (fun x => x) (·⁻¹),
      sum_single_mul (S ×ˢ U) (U ×ˢ S) (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹)]
  rw [hexp, sum_single_apply]
  norm_cast
  have hcard : (S ×ˢ U).card = U.card * S.card := by
    rw [Finset.card_product]; ring
  rw [← hcard]
  refine Finset.card_bij' (fun p _ => p.1)
    (fun q _ => ((q.1, q.2), (q.2, q.1))) ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨⟨s, u⟩, ⟨u', s'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_product.mpr ⟨hp.1.1.1, hp.1.1.2⟩
  case hj =>
    rintro ⟨s, u⟩ hq
    simp only [Finset.mem_product] at hq
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hq.1, hq.2⟩, hq.2, hq.1⟩, by group⟩
  case left =>
    rintro ⟨⟨s, u⟩, ⟨u', s'⟩⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hs, hu⟩, hu', hs'⟩, hrel⟩ := hp
    have hrel' : s'⁻¹ * s * t₀⁻¹ * t₀ * u⁻¹ * u' = 1 := by
      have hconj : s'⁻¹ * s * t₀⁻¹ * t₀ * u⁻¹ * u'
          = s'⁻¹ * (s * u⁻¹ * (u' * s'⁻¹)) * s' := by group
      rw [hconj, hrel]; group
    obtain ⟨hss', -, huu'⟩ := h s hs s' hs' t₀ ht₀ t₀ ht₀ u' hu' u hu hrel'
    subst_vars
    rfl
  case right =>
    rintro ⟨s, u⟩ _
    rfl

/-! ### Fourier inversion: the trace of left multiplication -/

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Coordinates of a matrix in the standard basis. -/
private lemma stdBasis_repr {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) (p : m × n) :
    (Matrix.stdBasis ℂ m n).repr M p = M p.1 p.2 := by
  unfold Matrix.stdBasis
  rw [Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Pi.basis_repr]
  simp [Pi.basisFun_repr, Equiv.sigmaEquivProd]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Left multiplication in a product ring hits `Pi.single` componentwise. -/
private lemma mul_pi_single {k : ℕ} {d : Fin k → ℕ}
    (y : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : Fin k)
    (M : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    y * Pi.single i M = Pi.single i (y i * M) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Diagonal double sum over a square index. -/
private lemma sum_prod_diag {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ∑ p : Fin m × Fin m, A p.1 p.1 = (m : ℂ) * A.trace := by
  rw [Fintype.sum_prod_type]
  simp [Matrix.trace, Finset.mul_sum]

/-- The trace of left multiplication by `x` on `ℂ[G]` is `|G| · x(1)`:
each basis vector `g` contributes the diagonal coefficient `x(1)`. -/
theorem trace_mulLeft_monoidAlgebra (x : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G) (LinearMap.mulLeft ℂ x)
      = (Fintype.card G : ℂ) * x 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  have hdiag : ∀ g : G, (LinearMap.toMatrix (MonoidAlgebra.basis G ℂ)
      (MonoidAlgebra.basis G ℂ) (LinearMap.mulLeft ℂ x)).diag g = x 1 := by
    intro g
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    simp only [MonoidAlgebra.basis_apply, LinearMap.mulLeft_apply]
    show (x * MonoidAlgebra.single g 1 : MonoidAlgebra ℂ G) g = x 1
    rw [MonoidAlgebra.mul_single_apply]
    simp
  rw [Finset.sum_congr rfl fun g _ => hdiag g]
  simp [mul_comm]

/-- The trace of left multiplication by `y` on `Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`
is `Σ i, d i · Tr(y i)`: block `i` consists of `d i` copies of the column module. -/
theorem trace_mulLeft_piMat {k : ℕ} {d : Fin k → ℕ}
    (y : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (LinearMap.mulLeft ℂ y)
      = ∑ i, (d i : ℂ) * (y i).trace := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ
    (Pi.basis fun i : Fin k => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i))), Matrix.trace]
  have hdiag : ∀ σ : Σ i : Fin k, Fin (d i) × Fin (d i),
      (LinearMap.toMatrix (Pi.basis fun i : Fin k => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i)))
        (Pi.basis fun i : Fin k => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i)))
        (LinearMap.mulLeft ℂ y)).diag σ = y σ.1 σ.2.1 σ.2.1 := by
    intro σ
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_apply,
      LinearMap.mulLeft_apply, mul_pi_single, Pi.basis_repr, Pi.single_eq_same,
      Matrix.stdBasis_eq_single, stdBasis_repr]
    rw [Matrix.mul_single_apply_same]
    simp
  rw [Finset.sum_congr rfl fun σ _ => hdiag σ, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun i _ => sum_prod_diag (y i)

/-- **Fourier inversion at the identity**: for any algebra isomorphism
`e : ℂ[G] ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`,
\[ |G| \cdot x(1) = \sum_i d_i \operatorname{Tr}((e x)_i). \]
Both sides compute the trace of left multiplication by `x`, which is invariant
under transport along `e`. -/
theorem inversion {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (x : MonoidAlgebra ℂ G) :
    (Fintype.card G : ℂ) * x 1 = ∑ i, (d i : ℂ) * ((e x) i).trace := by
  rw [← trace_mulLeft_monoidAlgebra, ← trace_mulLeft_piMat]
  have hconj : LinearMap.mulLeft ℂ (e x)
      = e.toLinearEquiv.conj (LinearMap.mulLeft ℂ x) := by
    ext y
    simp [LinearEquiv.conj_apply, map_mul]
  rw [hconj, LinearMap.trace_conj']

/-! ### The Frobenius norm toolkit -/

section Frobenius

open scoped Matrix.Norms.Frobenius

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The squared Frobenius norm as an entry sum. -/
private lemma sq_frobenius_norm {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ‖M‖ ^ 2 = ∑ r, ∑ c, ‖M r c‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity)]
  norm_num

omit [Group G] [Fintype G] [DecidableEq G] in
/-- `Tr(Mᴴ M)` is the (real, nonnegative) squared Frobenius norm. -/
private lemma trace_conjTranspose_mul_self {m : Type*} [Fintype m]
    (M : Matrix m m ℂ) : (Mᴴ * M).trace = ((‖M‖ ^ 2 : ℝ) : ℂ) := by
  have hentry : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  calc (Mᴴ * M).trace
      = ∑ c, ∑ r, (starRingEnd ℂ) (M r c) * M r c := by
        simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diag]
    _ = ∑ c, ∑ r, ((‖M r c‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => hentry _
    _ = ((‖M‖ ^ 2 : ℝ) : ℂ) := by
        rw [sq_frobenius_norm]
        push_cast
        rw [Finset.sum_comm]

omit [Group G] [Fintype G] [DecidableEq G] in
/-- **Hilbert–Schmidt Cauchy–Schwarz**: `|Tr(M N)| ≤ ‖M‖ ‖N‖` in the Frobenius
norm. -/
private lemma norm_trace_mul_le {m : Type*} [Fintype m]
    (M N : Matrix m m ℂ) : ‖(M * N).trace‖ ≤ ‖M‖ * ‖N‖ := by
  have h1 : ‖(M * N).trace‖ ≤ ∑ r : m, ∑ c : m, ‖M r c‖ * ‖N c r‖ := by
    calc ‖(M * N).trace‖ = ‖∑ r : m, ∑ c : m, M r c * N c r‖ := by
          simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
      _ ≤ ∑ r : m, ‖∑ c : m, M r c * N c r‖ := norm_sum_le _ _
      _ ≤ ∑ r : m, ∑ c : m, ‖M r c * N c r‖ :=
          Finset.sum_le_sum fun r _ => norm_sum_le _ _
      _ = ∑ r : m, ∑ c : m, ‖M r c‖ * ‖N c r‖ := by simp
  have h2 : ∑ r : m, ∑ c : m, ‖M r c‖ * ‖N c r‖ ≤ ‖M‖ * ‖N‖ := by
    have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (m × m))
      (fun p => ‖M p.1 p.2‖) (fun p => ‖N p.2 p.1‖)
    have hM : ∑ p : m × m, ‖M p.1 p.2‖ ^ 2 = ‖M‖ ^ 2 := by
      rw [sq_frobenius_norm, Fintype.sum_prod_type]
    have hN : ∑ p : m × m, ‖N p.2 p.1‖ ^ 2 = ‖N‖ ^ 2 := by
      rw [sq_frobenius_norm, Fintype.sum_prod_type]
      exact Finset.sum_comm
    calc ∑ r : m, ∑ c : m, ‖M r c‖ * ‖N c r‖
        = ∑ p : m × m, ‖M p.1 p.2‖ * ‖N p.2 p.1‖ := (Fintype.sum_prod_type _).symm
      _ ≤ Real.sqrt (∑ p : m × m, ‖M p.1 p.2‖ ^ 2)
            * Real.sqrt (∑ p : m × m, ‖N p.2 p.1‖ ^ 2) := hCS
      _ = ‖M‖ * ‖N‖ := by
          rw [hM, hN, Real.sqrt_sq (norm_nonneg M), Real.sqrt_sq (norm_nonneg N)]
  exact h1.trans h2

end Frobenius

/-! ### The unitarian trick -/

/-- A Wedderburn decomposition is **unitary** when it intertwines the canonical
stars: the block of `g⁻¹` is the conjugate transpose of the block of `g`.
Equivalently, every block map `g ↦ (e (single g 1)) i` is a unitary matrix
representation of `G`. -/
def IsUnitary {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) : Prop :=
  ∀ (g : G) (i : Fin k),
    (e (MonoidAlgebra.single g⁻¹ 1)) i = ((e (MonoidAlgebra.single g 1)) i)ᴴ

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Conjugation by an inverse pair, as an algebra automorphism of a matrix
algebra. -/
private def conjAlgEquiv {m : ℕ} (B B' : Matrix (Fin m) (Fin m) ℂ)
    (hBB' : B * B' = 1) (hB'B : B' * B = 1) :
    Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun y := B * y * B'
  invFun y := B' * y * B
  left_inv y := by
    calc B' * (B * y * B') * B
        = (B' * B) * y * (B' * B) := by noncomm_ring
      _ = y := by rw [hB'B, one_mul, mul_one]
  right_inv y := by
    calc B * (B' * y * B) * B'
        = (B * B') * y * (B * B') := by noncomm_ring
      _ = y := by rw [hBB', one_mul, mul_one]
  map_mul' y z := by
    calc B * (y * z) * B'
        = (B * y) * (B' * B) * (z * B') := by noncomm_ring
      _ = B * y * B' * (B * z * B') := by rw [hB'B]; noncomm_ring
  map_add' y z := by
    simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hBB']

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Blockwise conjugation by an inverse pair, as an algebra automorphism of the
product of matrix algebras. -/
private def piConjAlgEquiv {k : ℕ} {d : Fin k → ℕ}
    (B B' : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hBB' : ∀ i, B i * B' i = 1) (hB'B : ∀ i, B' i * B i = 1) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₐ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  AlgEquiv.piCongrRight fun i => conjAlgEquiv (B i) (B' i) (hBB' i) (hB'B i)

omit [Group G] [Fintype G] [DecidableEq G] in
private lemma piConjAlgEquiv_apply {k : ℕ} {d : Fin k → ℕ}
    (B B' : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hBB' : ∀ i, B i * B' i = 1) (hB'B : ∀ i, B' i * B i = 1)
    (y : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : Fin k) :
    piConjAlgEquiv B B' hBB' hB'B y i = B i * y i * B' i :=
  rfl

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
  calc ∑ x ∈ X, (e (MonoidAlgebra.single x⁻¹ 1)) i
      = ∑ x ∈ X, ((e (MonoidAlgebra.single x 1)) i)ᴴ :=
        Finset.sum_congr rfl fun x _ => he x i
    _ = (∑ x ∈ X, (e (MonoidAlgebra.single x 1)) i)ᴴ :=
        (Matrix.conjTranspose_sum _ _).symm

/-- The block of the reversed product `1_Y 1_{X⁻¹}` is the conjugate transpose
of the block of `1_X 1_{Y⁻¹}`. -/
theorem IsUnitary.e_star_prod (he : IsUnitary e) (X Y : Finset G) (i : Fin k) :
    (e (ind Y * indInv X)) i = ((e (ind X * indInv Y)) i)ᴴ := by
  rw [map_mul, map_mul]
  simp only [Pi.mul_apply]
  rw [he.e_indInv X i, he.e_indInv Y i, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

open scoped Matrix.Norms.Frobenius in
/-- **Parseval for an indicator product**: if the coefficient of `x⋆ x` at `1`
is `|X| |Y|` (a TPP count), then the Fourier blocks of `x = 1_X 1_{Y⁻¹}` satisfy
`Σᵢ dᵢ ‖(e x)ᵢ‖² = |G| |X| |Y|`. -/
theorem parseval_norm_sum (he : IsUnitary e) (X Y : Finset G)
    (hcount : ((ind Y * indInv X) * (ind X * indInv Y)) 1
      = ((X.card * Y.card : ℕ) : ℂ)) :
    ∑ i, (d i : ℝ) * ‖(e (ind X * indInv Y)) i‖ ^ 2
      = (Fintype.card G : ℝ) * X.card * Y.card := by
  have hinv := inversion e ((ind Y * indInv X) * (ind X * indInv Y))
  rw [hcount] at hinv
  have hterm : ∀ i, ((e ((ind Y * indInv X) * (ind X * indInv Y))) i).trace
      = ((‖(e (ind X * indInv Y)) i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [map_mul]
    simp only [Pi.mul_apply]
    rw [he.e_star_prod X Y i, trace_conjTranspose_mul_self]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hterm i])] at hinv
  have hcast : ((∑ i, (d i : ℝ) * ‖(e (ind X * indInv Y)) i‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card G : ℝ) * X.card * Y.card : ℝ) : ℂ) := by
    push_cast at hinv ⊢
    rw [← hinv]
    ring
  exact_mod_cast hcast

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

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Matrices of size `≤ 1` commute. -/
private lemma matrix_mul_comm_of_le_one {m : ℕ} (hm : m ≤ 1)
    (M N : Matrix (Fin m) (Fin m) ℂ) : M * N = N * M := by
  interval_cases m
  · exact Subsingleton.elim _ _
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, mul_comm]

/-- A nonabelian group has a block of dimension `> 1`: otherwise the product of
`≤ 1`-dimensional matrix algebras would be commutative, hence so would `ℂ[G]`,
hence so would `G`. -/
theorem exists_one_lt_dim_of_nonabelian {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hG : ∃ a b : G, a * b ≠ b * a) :
    ∃ i, 1 < d i := by
  by_contra hall
  push_neg at hall
  obtain ⟨a, b, hab⟩ := hG
  apply hab
  have hcomm : ∀ y z : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ), y * z = z * y := by
    intro y z
    funext i
    exact matrix_mul_comm_of_le_one (hall i) (y i) (z i)
  have hsingle : MonoidAlgebra.single (a * b) (1 : ℂ)
      = MonoidAlgebra.single (b * a) (1 : ℂ) := by
    rw [show MonoidAlgebra.single (a * b) (1 : ℂ)
        = MonoidAlgebra.single a 1 * MonoidAlgebra.single b 1 from by
          rw [MonoidAlgebra.single_mul_single, one_mul],
      show MonoidAlgebra.single (b * a) (1 : ℂ)
        = MonoidAlgebra.single b 1 * MonoidAlgebra.single a 1 from by
          rw [MonoidAlgebra.single_mul_single, one_mul]]
    apply e.injective
    rw [map_mul, map_mul, hcomm]
  exact Finsupp.single_left_injective one_ne_zero hsingle

/-! ### The master bound -/

open scoped Matrix.Norms.Frobenius in
/-- **The master Gowers-trick bound** (the analytic core of BCGPU Theorem 3.2).

Let `e` be a unitary Wedderburn decomposition of `ℂ[G]` with block dimensions
`d i ≥ 1`, and let `n ≥ 2` lower-bound every block dimension exceeding `1`.
Then any TPP triple of nonempty sets satisfies
\[ |S|\,|T|\,|U| \le \frac{|G|^{3/2}}{\sqrt n} + |G|. \]

Fourier inversion evaluates `|G| |S||T||U|` as `Σᵢ dᵢ Tr((e(abc))ᵢ)` for the
Gowers element `abc`; the trivial block contributes `(|S||T||U|)²`, the other
one-dimensional blocks are nonnegative, and the blocks of dimension `> 1` are
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
