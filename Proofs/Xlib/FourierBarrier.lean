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

omit [Group G] [Fintype G] in
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

omit [Group G] in
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

omit [Fintype G] [DecidableEq G] in
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

omit [Fintype G] in
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

omit [Fintype G] in
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

omit [Fintype G] in
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

omit [Fintype G] in
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
  simp

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
/-- The squared Frobenius norm as an entry sum.
Immediate from `Matrix.frobenius_norm_def`. -/
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
        = ∑ p : m × m, ‖M p.1 p.2‖ * ‖N p.2 p.1‖ :=
          (Fintype.sum_prod_type (f := fun p : m × m => ‖M p.1 p.2‖ * ‖N p.2 p.1‖)).symm
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
    show B' * (B * y * B') * B = y
    rw [show B' * (B * y * B') * B = (B' * B) * y * (B' * B) from by
      simp only [mul_assoc], hB'B]
    simp
  right_inv y := by
    show B * (B' * y * B) * B' = y
    rw [show B * (B' * y * B) * B' = (B * B') * y * (B * B') from by
      simp only [mul_assoc], hBB']
    simp
  map_mul' y z := by
    show B * (y * z) * B' = B * y * B' * (B * z * B')
    rw [show B * y * B' * (B * z * B') = B * y * (B' * B) * (z * B') from by
      simp only [mul_assoc], hB'B]
    simp only [mul_assoc, mul_one]
  map_add' y z := by
    simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hBB']

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Blockwise conjugation by an inverse pair, as an algebra automorphism of the
product of matrix algebras.  Wraps `AlgEquiv.piCongrRight` applied to
`conjAlgEquiv` at each block. -/
private def piConjAlgEquiv {k : ℕ} {d : Fin k → ℕ}
    (B B' : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hBB' : ∀ i, B i * B' i = 1) (hB'B : ∀ i, B' i * B i = 1) :
    (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₐ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  AlgEquiv.piCongrRight fun i => conjAlgEquiv (B i) (B' i) (hBB' i) (hB'B i)

omit [DecidableEq G] in
open scoped ComplexOrder MatrixOrder in
/-- **The unitarian trick** (Weyl): any indexed Wedderburn decomposition of the
group algebra can be conjugated blockwise into a *unitary* one with the same
block dimensions.  Conjugate block `i` by the positive factor `B i` of the
averaged Gram matrix `Q i = Σ_g ρᵢ(g)ᴴ ρᵢ(g) = (B i)ᴴ (B i)`. -/
theorem exists_isUnitary {k : ℕ} {d : Fin k → ℕ}
    (e₀ : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ,
      IsUnitary e := by
  classical
  -- multiplicativity of the block representations
  have ρ_mul : ∀ (i : Fin k) (g h : G),
      (e₀ (MonoidAlgebra.single (g * h) 1)) i
        = (e₀ (MonoidAlgebra.single g 1)) i * (e₀ (MonoidAlgebra.single h 1)) i := by
    intro i g h
    rw [show (MonoidAlgebra.single (g * h) (1 : ℂ))
        = MonoidAlgebra.single g 1 * MonoidAlgebra.single h 1 from by
      rw [MonoidAlgebra.single_mul_single, one_mul], map_mul]
    rfl
  have ρ_one : ∀ i : Fin k, (e₀ (MonoidAlgebra.single (1 : G) 1)) i = 1 := by
    intro i
    rw [show (MonoidAlgebra.single (1 : G) (1 : ℂ)) = 1 from rfl, map_one]
    rfl
  have ρ_mul_inv : ∀ (i : Fin k) (g : G),
      (e₀ (MonoidAlgebra.single g 1)) i * (e₀ (MonoidAlgebra.single g⁻¹ 1)) i = 1 := by
    intro i g
    rw [← ρ_mul, mul_inv_cancel, ρ_one]
  have ρ_unit : ∀ (i : Fin k) (g : G), IsUnit ((e₀ (MonoidAlgebra.single g 1)) i) :=
    fun i g => IsUnit.of_mul_eq_one _ (ρ_mul_inv i g)
  -- the averaged Gram matrices
  set Q : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ := fun i =>
    ∑ g : G, ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (e₀ (MonoidAlgebra.single g 1)) i
    with hQdef
  have hQPD : ∀ i, (Q i).PosDef := by
    intro i
    refine Matrix.posDef_sum Finset.univ_nonempty fun g _ => ?_
    refine (Matrix.posSemidef_conjTranspose_mul_self _).posDef_iff_det_ne_zero.mpr ?_
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    have hu : IsUnit ((e₀ (MonoidAlgebra.single g 1)) i).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (ρ_unit i g)
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨star_ne_zero.mpr hu.ne_zero, hu.ne_zero⟩
  -- invariance of the Gram matrix under right translation
  have hQinv : ∀ (i : Fin k) (g : G),
      ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * Q i * (e₀ (MonoidAlgebra.single g 1)) i
        = Q i := by
    intro i g
    calc ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * Q i * (e₀ (MonoidAlgebra.single g 1)) i
        = ∑ h : G, ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ *
            (((e₀ (MonoidAlgebra.single h 1)) i)ᴴ * (e₀ (MonoidAlgebra.single h 1)) i) *
            (e₀ (MonoidAlgebra.single g 1)) i := by
          rw [hQdef, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ h : G, ((e₀ (MonoidAlgebra.single (h * g) 1)) i)ᴴ *
            (e₀ (MonoidAlgebra.single (h * g) 1)) i := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [ρ_mul i h g, Matrix.conjTranspose_mul]
          simp only [mul_assoc]
      _ = Q i := by
          rw [hQdef]
          exact Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _
            fun h => rfl
  -- factor `Q i = (B i)ᴴ (B i)` with `B i` invertible
  have hfac : ∀ i, ∃ B : Matrix (Fin (d i)) (Fin (d i)) ℂ, Q i = Bᴴ * B := by
    intro i
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hQPD i).posSemidef.nonneg
    exact ⟨B, by simpa [Matrix.star_eq_conjTranspose] using hB⟩
  choose B hB using hfac
  have hBunit : ∀ i, IsUnit (B i) := by
    intro i
    have hQu : IsUnit ((B i)ᴴ * B i) := by rw [← hB]; exact (hQPD i).isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hQu ⊢
    rw [Matrix.det_mul, Matrix.det_conjTranspose] at hQu
    exact isUnit_of_mul_isUnit_right hQu
  have hBinv : ∀ i, ∃ B' : Matrix (Fin (d i)) (Fin (d i)) ℂ,
      B i * B' = 1 ∧ B' * B i = 1 := by
    intro i
    obtain ⟨u, hu⟩ := hBunit i
    exact ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv, by rw [← hu]; exact u.inv_mul⟩
  choose B' hBB' hB'B using hBinv
  refine ⟨e₀.trans (piConjAlgEquiv B B' hBB' hB'B), ?_⟩
  intro g i
  show B i * (e₀ (MonoidAlgebra.single g⁻¹ 1)) i * B' i
      = (B i * (e₀ (MonoidAlgebra.single g 1)) i * B' i)ᴴ
  -- the key intertwining relation `Q ρ(g⁻¹) = ρ(g)ᴴ Q`
  have hkey : Q i * (e₀ (MonoidAlgebra.single g⁻¹ 1)) i
      = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * Q i := by
    conv_lhs => rw [← hQinv i g]
    rw [mul_assoc, ρ_mul_inv i g, mul_one]
  -- rewrite the conjugate transpose of the right-hand side
  have hrhs : (B i * (e₀ (MonoidAlgebra.single g 1)) i * B' i)ᴴ
      = (B' i)ᴴ * ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ← mul_assoc]
  rw [hrhs]
  -- cancel the invertible factor `(B i)ᴴ` on the left
  have hBH : IsUnit (B i)ᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (hBunit i)).star
  apply hBH.mul_left_cancel
  have hL : (B i)ᴴ * (B i * (e₀ (MonoidAlgebra.single g⁻¹ 1)) i * B' i)
      = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ := by
    calc (B i)ᴴ * (B i * (e₀ (MonoidAlgebra.single g⁻¹ 1)) i * B' i)
        = Q i * (e₀ (MonoidAlgebra.single g⁻¹ 1)) i * B' i := by
          rw [hB i]; simp only [mul_assoc]
      _ = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * Q i * B' i := by rw [hkey]
      _ = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ * (B i * B' i) := by
          rw [hB i]; simp only [mul_assoc]
      _ = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ := by
          rw [hBB' i, mul_one]
  have hR : (B i)ᴴ * ((B' i)ᴴ * ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ)
      = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ := by
    calc (B i)ᴴ * ((B' i)ᴴ * ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ)
        = ((B i)ᴴ * (B' i)ᴴ) * (((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ) := by
          simp only [mul_assoc]
      _ = (B' i * B i)ᴴ * (((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ) := by
          rw [Matrix.conjTranspose_mul]
      _ = ((e₀ (MonoidAlgebra.single g 1)) i)ᴴ * (B i)ᴴ := by
          rw [hB'B i, Matrix.conjTranspose_one, one_mul]
  rw [hL, hR]

/-! ### Consequences of unitarity -/

section Unitary

variable {k : ℕ} {d : Fin k → ℕ}
  {e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ}

omit [Fintype G] [DecidableEq G] in
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

omit [Fintype G] [DecidableEq G] in
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

omit [Fintype G] [DecidableEq G] in
/-- **One-dimensional blocks of the Gowers element are nonnegative reals**:
in a `d i = 1` block the six factors multiply to `|z_S|² |z_T|² |z_U|² ≥ 0`. -/
theorem trace_gowersElt_one_dim (he : IsUnitary e) {i : Fin k} (hd : d i = 1)
    (S T U : Finset G) :
    ∃ r : ℝ, 0 ≤ r ∧ ((e (gowersElt S T U)) i).trace = (r : ℂ) := by
  have hconj : ∀ X : Finset G,
      ((e (indInv X)) i).trace = (starRingEnd ℂ) (((e (ind X)) i).trace) := by
    intro X
    rw [he.e_indInv X i, Matrix.trace_conjTranspose]
    rfl
  have hsix : ((e (gowersElt S T U)) i).trace
      = (((e (ind S)) i).trace * (starRingEnd ℂ) (((e (ind T)) i).trace))
        * (((e (ind T)) i).trace * (starRingEnd ℂ) (((e (ind U)) i).trace))
        * (((e (ind U)) i).trace * (starRingEnd ℂ) (((e (ind S)) i).trace)) := by
    unfold gowersElt
    rw [map_mul, map_mul, map_mul, map_mul, map_mul]
    simp only [Pi.mul_apply]
    rw [trace_mul_dim_one hd, trace_mul_dim_one hd, trace_mul_dim_one hd,
      trace_mul_dim_one hd, trace_mul_dim_one hd, hconj S, hconj T, hconj U]
  refine ⟨Complex.normSq (((e (ind S)) i).trace)
      * Complex.normSq (((e (ind T)) i).trace)
      * Complex.normSq (((e (ind U)) i).trace),
    mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _), ?_⟩
  rw [hsix]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj, ← Complex.mul_conj]
  ring

end Unitary

/-! ### The trivial block and the nonabelian dimension witness -/

/-- **The trivial block.** Any decomposition has a distinguished index `i₀` with
`d i₀ = 1` on which every `x` acts by its total mass: `(e x) i₀ = (Σ_g x g) • 1`.
It is located by chasing the central idempotent `p = |G|⁻¹ Σ_g g`. -/
theorem exists_trivial_block {k : ℕ} {d : Fin k → ℕ} [∀ i, NeZero (d i)]
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ i₀ : Fin k, d i₀ = 1 ∧
      ∀ x : MonoidAlgebra ℂ G, (e x) i₀ = (∑ g : G, x g) • 1 := by
  classical
  have hcard0 : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set P : MonoidAlgebra ℂ G := ∑ g : G, MonoidAlgebra.single g 1 with hPdef
  -- pointwise values and total mass of `P`
  have hPapply : ∀ g : G, P g = 1 := by
    intro g
    rw [hPdef, sum_single_apply Finset.univ (fun h => h) g]
    rw [show Finset.univ.filter (fun h : G => h = g) = {g} from by
      ext h; simp]
    simp
  have hPmass : (∑ g : G, P g) = (Fintype.card G : ℂ) := by
    rw [Finset.sum_congr rfl fun g _ => hPapply g]
    simp
  -- one-sided absorption on group elements
  have hsingle_mul : ∀ h : G, (MonoidAlgebra.single h (1 : ℂ)) * P = P := by
    intro h
    rw [hPdef, Finset.mul_sum]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _
      fun g => by rw [MonoidAlgebra.single_mul_single, one_mul]
  have hmul_single : ∀ h : G, P * (MonoidAlgebra.single h (1 : ℂ)) = P := by
    intro h
    rw [hPdef, Finset.sum_mul]
    exact Fintype.sum_bijective (· * h) (Group.mulRight_bijective h) _ _
      fun g => by rw [MonoidAlgebra.single_mul_single, one_mul]
  -- `x * P = mass(x) • P` and symmetrically
  have hxP : ∀ x : MonoidAlgebra ℂ G, x * P = (∑ g : G, x g) • P := by
    intro x
    have hxdec : x = ∑ g : G, MonoidAlgebra.single g (x g) :=
      (Finsupp.univ_sum_single x).symm
    conv_lhs => rw [hxdec]
    rw [Finset.sum_mul]
    have hterm : ∀ g : G,
        (MonoidAlgebra.single g (x g) : MonoidAlgebra ℂ G) * P = x g • P := by
      intro g
      have h1 : (MonoidAlgebra.single g (x g) : MonoidAlgebra ℂ G)
          = x g • MonoidAlgebra.single g 1 := by
        rw [← MonoidAlgebra.of_apply, MonoidAlgebra.smul_of]
      rw [h1, smul_mul_assoc, hsingle_mul]
    rw [Finset.sum_congr rfl fun g _ => hterm g, ← Finset.sum_smul]
  have hPx : ∀ x : MonoidAlgebra ℂ G, P * x = (∑ g : G, x g) • P := by
    intro x
    have hxdec : x = ∑ g : G, MonoidAlgebra.single g (x g) :=
      (Finsupp.univ_sum_single x).symm
    conv_lhs => rw [hxdec]
    rw [Finset.mul_sum]
    have hterm : ∀ g : G,
        P * (MonoidAlgebra.single g (x g) : MonoidAlgebra ℂ G) = x g • P := by
      intro g
      have h1 : (MonoidAlgebra.single g (x g) : MonoidAlgebra ℂ G)
          = x g • MonoidAlgebra.single g 1 := by
        rw [← MonoidAlgebra.of_apply, MonoidAlgebra.smul_of]
      rw [h1, mul_smul_comm, hmul_single]
    rw [Finset.sum_congr rfl fun g _ => hterm g, ← Finset.sum_smul]
  -- `P` is nonzero and satisfies `P² = |G| P`
  have hPP : P * P = (Fintype.card G : ℂ) • P := by rw [hxP P, hPmass]
  have hPne : P ≠ 0 := by
    intro h0
    have h1 : P 1 = 0 := by rw [h0]; rfl
    rw [hPapply 1] at h1
    exact one_ne_zero h1
  -- transport to the matrix side
  set q := e P with hqdef
  have hqq : q * q = (Fintype.card G : ℂ) • q := by
    rw [hqdef, ← map_mul, hPP, map_smul]
  have hqcentral : ∀ y, y * q = q * y := by
    intro y
    calc y * q = e (e.symm y * P) := by rw [map_mul, e.apply_symm_apply]
      _ = e (P * e.symm y) := by rw [hxP (e.symm y), hPx (e.symm y)]
      _ = q * y := by rw [map_mul, e.apply_symm_apply]
  have hqne : q ≠ 0 := by
    intro h0
    apply hPne
    have h1 : e.symm (e P) = e.symm 0 := by rw [← hqdef, h0]
    simpa using h1
  -- each block of `q` is a scalar
  have hscalar : ∀ i, ∃ c : ℂ, q i = c • 1 := by
    intro i
    have hcomm : ∀ N : Matrix (Fin (d i)) (Fin (d i)) ℂ, N * q i = q i * N := by
      intro N
      have := congrFun (hqcentral (Pi.single i N)) i
      simpa [Pi.mul_apply, Pi.single_eq_same] using this
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun a b => hcomm _)
    refine ⟨c, ?_⟩
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  choose c hc using hscalar
  -- the scalars satisfy `c² = |G| c`, so each is `0` or `|G|`
  have hcid : ∀ i, c i = 0 ∨ c i = (Fintype.card G : ℂ) := by
    intro i
    have hq2 := congrFun hqq i
    rw [Pi.mul_apply, Pi.smul_apply, hc i] at hq2
    have h2 : (c i * c i) • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)
        = ((Fintype.card G : ℂ) * c i) • 1 := by
      rw [← smul_smul, ← smul_smul, ← hq2, smul_mul_assoc, mul_smul_comm, mul_one]
    have h3 : c i * c i = (Fintype.card G : ℂ) * c i := by
      have h4 := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩)
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩
      simpa [Matrix.one_apply] using h4
    have h5 : c i * (c i - (Fintype.card G : ℂ)) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h5 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  -- some block carries `q i₀ = |G| • 1`
  obtain ⟨i₀, hi₀ne⟩ : ∃ i, q i ≠ 0 := by
    by_contra hall
    exact hqne (funext fun i => by
      by_contra hne
      exact hall ⟨i, hne⟩)
  have hci₀ : c i₀ = (Fintype.card G : ℂ) := by
    rcases hcid i₀ with h0 | h1
    · exact absurd (by rw [hc i₀, h0, zero_smul]) hi₀ne
    · exact h1
  have hqi₀ : q i₀ = (Fintype.card G : ℂ) • 1 := by rw [hc i₀, hci₀]
  -- the universal mass property, after cancelling the factor `|G|`
  have huniv : ∀ x : MonoidAlgebra ℂ G, (e x) i₀ = (∑ g : G, x g) • 1 := by
    intro x
    have hchain : (Fintype.card G : ℂ) • ((e x) i₀)
        = (Fintype.card G : ℂ) • ((∑ g : G, x g) • 1) := by
      calc (Fintype.card G : ℂ) • ((e x) i₀)
          = (e x) i₀ * ((Fintype.card G : ℂ) • 1) := by
            rw [mul_smul_comm, mul_one]
        _ = (e x) i₀ * q i₀ := by rw [hqi₀]
        _ = (e (x * P)) i₀ := by rw [map_mul, Pi.mul_apply]
        _ = (e ((∑ g : G, x g) • P)) i₀ := by rw [hxP]
        _ = (∑ g : G, x g) • q i₀ := by rw [map_smul, hqdef, Pi.smul_apply]
        _ = (Fintype.card G : ℂ) • ((∑ g : G, x g) • 1) := by
            rw [hqi₀, smul_comm]
    exact smul_right_injective _ hcard0 hchain
  -- the block is one-dimensional
  refine ⟨i₀, ?_, huniv⟩
  by_contra hne
  have h2le : 2 ≤ d i₀ := by
    have h1 := Nat.pos_of_ne_zero (NeZero.ne (d i₀))
    omega
  have hr01 : (⟨0, by omega⟩ : Fin (d i₀)) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hM := huniv (e.symm (Pi.single i₀
    (Matrix.single (⟨0, by omega⟩ : Fin (d i₀)) (⟨1, by omega⟩ : Fin (d i₀)) 1)))
  rw [e.apply_symm_apply, Pi.single_eq_same] at hM
  have hentry := congrFun (congrFun hM ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [Matrix.single_apply, Matrix.smul_apply, Matrix.one_apply_ne hr01] at hentry
  simp at hentry

omit [Group G] [Fintype G] [DecidableEq G] in
/-- Matrices of size `≤ 1` commute. -/
private lemma matrix_mul_comm_of_le_one {m : ℕ} (hm : m ≤ 1)
    (M N : Matrix (Fin m) (Fin m) ℂ) : M * N = N * M := by
  interval_cases m
  · exact Subsingleton.elim _ _
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]

omit [Fintype G] [DecidableEq G] in
/-- A nonabelian group has a block of dimension `> 1`: otherwise the product of
`≤ 1`-dimensional matrix algebras would be commutative, hence so would `ℂ[G]`,
hence so would `G`. -/
theorem exists_one_lt_dim_of_nonabelian {k : ℕ} {d : Fin k → ℕ}
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hG : ∃ a b : G, a * b ≠ b * a) :
    ∃ i, 1 < d i := by
  by_contra hall
  obtain ⟨a, b, hab⟩ := hG
  apply hab
  have hcomm : ∀ y z : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ), y * z = z * y := by
    intro y z
    funext i
    refine matrix_mul_comm_of_le_one ?_ (y i) (z i)
    by_contra hgt
    exact hall ⟨i, by omega⟩
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
  classical
  set N : ℝ := (Fintype.card G : ℝ) with hNdef
  set P : ℝ := (S.card * T.card * U.card : ℝ) with hPdef
  have hNpos : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  have hPpos : 0 < P := by
    rw [hPdef]
    have h1 : 0 < S.card * T.card * U.card :=
      Nat.mul_pos (Nat.mul_pos hS.card_pos hT.card_pos) hU.card_pos
    exact_mod_cast h1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- Fourier inversion of the Gowers element, real form
  have hinv := inversion e (gowersElt S T U)
  rw [gowersElt_apply_one h] at hinv
  have hsix : N * P = ∑ i, (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re := by
    have hre := congrArg Complex.re hinv
    rw [Complex.re_sum] at hre
    rw [hNdef, hPdef]
    calc (Fintype.card G : ℝ) * ((S.card : ℝ) * T.card * U.card)
        = ((Fintype.card G : ℂ) * ((S.card * T.card * U.card : ℕ) : ℂ)).re := by
          simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
          push_cast
          ring
      _ = ∑ i, ((d i : ℂ) * ((e (gowersElt S T U)) i).trace).re := hre
      _ = ∑ i, (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Complex.mul_re]
  -- the three Parseval identities
  have hPa : ∑ i, (d i : ℝ) * ‖(e (ind S * indInv T)) i‖ ^ 2
      = N * S.card * T.card := by
    rw [hNdef]; exact parseval_norm_sum he S T (coeff_star_a h hU)
  have hPb : ∑ i, (d i : ℝ) * ‖(e (ind T * indInv U)) i‖ ^ 2
      = N * T.card * U.card := by
    rw [hNdef]; exact parseval_norm_sum he T U (coeff_star_b h hS)
  have hPc : ∑ i, (d i : ℝ) * ‖(e (ind U * indInv S)) i‖ ^ 2
      = N * U.card * S.card := by
    rw [hNdef]; exact parseval_norm_sum he U S (coeff_star_c h hT)
  -- the trivial block contributes `P²`
  obtain ⟨i₀, hdi₀, hi₀⟩ := exists_trivial_block e
  have htriv : ((e (gowersElt S T U)) i₀).trace = ((P ^ 2 : ℝ) : ℂ) := by
    rw [hi₀ (gowersElt S T U), mass_gowersElt, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, hdi₀, hPdef]
    push_cast [smul_eq_mul]
    ring
  -- one-dimensional blocks are nonnegative
  have hone : ∀ i, d i = 1 → 0 ≤ ((e (gowersElt S T U)) i).trace.re := by
    intro i hdi
    obtain ⟨r, hr0, hr⟩ := trace_gowersElt_one_dim he hdi S T U
    rw [hr, Complex.ofReal_re]
    exact hr0
  -- factor the Gowers block
  have hsplit_e : ∀ i, (e (gowersElt S T U)) i
      = (e (ind S * indInv T)) i * (e (ind T * indInv U)) i
        * (e (ind U * indInv S)) i := by
    intro i
    show (e (ind S * indInv T * (ind T * indInv U) * (ind U * indInv S))) i = _
    rw [map_mul, map_mul]
    rfl
  -- Hilbert–Schmidt bound per block
  have hblock : ∀ i, ‖((e (gowersElt S T U)) i).trace‖
      ≤ ‖(e (ind S * indInv T)) i‖ * ‖(e (ind T * indInv U)) i‖
        * ‖(e (ind U * indInv S)) i‖ := by
    intro i
    rw [hsplit_e i]
    calc ‖((e (ind S * indInv T)) i * (e (ind T * indInv U)) i
          * (e (ind U * indInv S)) i).trace‖
        ≤ ‖(e (ind S * indInv T)) i * (e (ind T * indInv U)) i‖
            * ‖(e (ind U * indInv S)) i‖ := norm_trace_mul_le _ _
      _ ≤ ‖(e (ind S * indInv T)) i‖ * ‖(e (ind T * indInv U)) i‖
            * ‖(e (ind U * indInv S)) i‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  -- the per-irrep Frobenius bound for the `a`-part
  have hnormA : ∀ i, 1 < d i → ‖(e (ind S * indInv T)) i‖
      ≤ Real.sqrt (N * S.card * T.card / n) := by
    intro i hi
    have h1 : (n : ℝ) * ‖(e (ind S * indInv T)) i‖ ^ 2 ≤ N * S.card * T.card := by
      calc (n : ℝ) * ‖(e (ind S * indInv T)) i‖ ^ 2
          ≤ (d i : ℝ) * ‖(e (ind S * indInv T)) i‖ ^ 2 := by
            have hle : (n : ℝ) ≤ d i := by exact_mod_cast hnd i hi
            exact mul_le_mul_of_nonneg_right hle (by positivity)
        _ ≤ ∑ j, (d j : ℝ) * ‖(e (ind S * indInv T)) j‖ ^ 2 :=
            Finset.single_le_sum
              (f := fun j => (d j : ℝ) * ‖(e (ind S * indInv T)) j‖ ^ 2)
              (fun j _ => by positivity) (Finset.mem_univ i)
        _ = N * S.card * T.card := hPa
    have h2 : ‖(e (ind S * indInv T)) i‖ ^ 2 ≤ N * S.card * T.card / n := by
      rw [le_div_iff₀ hnpos]
      linarith
    calc ‖(e (ind S * indInv T)) i‖
        = Real.sqrt (‖(e (ind S * indInv T)) i‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (N * S.card * T.card / n) := Real.sqrt_le_sqrt h2
  -- the big-block set
  set F : Finset (Fin k) := Finset.univ.filter (fun i => 1 < d i) with hFdef
  -- filtered Parseval sums
  have hCb : ∑ i ∈ F, (d i : ℝ) * ‖(e (ind T * indInv U)) i‖ ^ 2
      ≤ N * T.card * U.card := by
    rw [← hPb]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (fun i _ _ => by positivity)
  have hCc : ∑ i ∈ F, (d i : ℝ) * ‖(e (ind U * indInv S)) i‖ ^ 2
      ≤ N * U.card * S.card := by
    rw [← hPc]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (fun i _ _ => by positivity)
  -- Cauchy–Schwarz across the big blocks
  have hCS : ∑ i ∈ F, (d i : ℝ)
        * (‖(e (ind T * indInv U)) i‖ * ‖(e (ind U * indInv S)) i‖)
      ≤ Real.sqrt (N * T.card * U.card) * Real.sqrt (N * U.card * S.card) := by
    calc ∑ i ∈ F, (d i : ℝ)
          * (‖(e (ind T * indInv U)) i‖ * ‖(e (ind U * indInv S)) i‖)
        = ∑ i ∈ F, Real.sqrt ((d i : ℝ) * ‖(e (ind T * indInv U)) i‖ ^ 2)
            * Real.sqrt ((d i : ℝ) * ‖(e (ind U * indInv S)) i‖ ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.sqrt_mul (by positivity)]
          rw [show (d i : ℝ) * ‖(e (ind T * indInv U)) i‖ ^ 2
              * ((d i : ℝ) * ‖(e (ind U * indInv S)) i‖ ^ 2)
              = ((d i : ℝ) * (‖(e (ind T * indInv U)) i‖
                  * ‖(e (ind U * indInv S)) i‖)) ^ 2 from by ring]
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (∑ i ∈ F, (d i : ℝ) * ‖(e (ind T * indInv U)) i‖ ^ 2)
            * Real.sqrt (∑ i ∈ F, (d i : ℝ) * ‖(e (ind U * indInv S)) i‖ ^ 2) :=
          Real.sum_sqrt_mul_sqrt_le F (fun i => by positivity)
            (fun i => by positivity)
      _ ≤ Real.sqrt (N * T.card * U.card) * Real.sqrt (N * U.card * S.card) :=
          mul_le_mul (Real.sqrt_le_sqrt hCb) (Real.sqrt_le_sqrt hCc)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the total big-block estimate
  have hsqrtN3 : Real.sqrt (N ^ (3 : ℕ)) = N ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast N 3, ← Real.rpow_mul hNpos.le]
    norm_num
  have hbig : ∑ i ∈ F, (d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖
      ≤ N ^ ((3 : ℝ) / 2) * P / Real.sqrt n := by
    calc ∑ i ∈ F, (d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖
        ≤ ∑ i ∈ F, Real.sqrt (N * S.card * T.card / n)
            * ((d i : ℝ) * (‖(e (ind T * indInv U)) i‖
                * ‖(e (ind U * indInv S)) i‖)) := by
          refine Finset.sum_le_sum fun i hiF => ?_
          have hiF' : 1 < d i := by
            rw [hFdef] at hiF
            exact (Finset.mem_filter.mp hiF).2
          calc (d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖
              ≤ (d i : ℝ) * (‖(e (ind S * indInv T)) i‖
                  * ‖(e (ind T * indInv U)) i‖ * ‖(e (ind U * indInv S)) i‖) :=
                mul_le_mul_of_nonneg_left (hblock i) (by positivity)
            _ = ((d i : ℝ) * (‖(e (ind T * indInv U)) i‖
                  * ‖(e (ind U * indInv S)) i‖)) * ‖(e (ind S * indInv T)) i‖ := by
                ring
            _ ≤ ((d i : ℝ) * (‖(e (ind T * indInv U)) i‖
                  * ‖(e (ind U * indInv S)) i‖))
                  * Real.sqrt (N * S.card * T.card / n) :=
                mul_le_mul_of_nonneg_left (hnormA i hiF') (by positivity)
            _ = Real.sqrt (N * S.card * T.card / n)
                  * ((d i : ℝ) * (‖(e (ind T * indInv U)) i‖
                      * ‖(e (ind U * indInv S)) i‖)) := by ring
      _ = Real.sqrt (N * S.card * T.card / n)
            * ∑ i ∈ F, (d i : ℝ) * (‖(e (ind T * indInv U)) i‖
                * ‖(e (ind U * indInv S)) i‖) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt (N * S.card * T.card / n)
            * (Real.sqrt (N * T.card * U.card) * Real.sqrt (N * U.card * S.card)) :=
          mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg _)
      _ = N ^ ((3 : ℝ) / 2) * P / Real.sqrt n := by
          rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ N * S.card * T.card),
            div_mul_eq_mul_div]
          congr 1
          rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ N * T.card * U.card),
            ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ N * S.card * T.card)]
          rw [show N * (S.card : ℝ) * T.card * (N * T.card * U.card
              * (N * U.card * S.card)) = N ^ (3 : ℕ) * P ^ 2 from by
            rw [hPdef]; ring]
          rw [Real.sqrt_mul (by positivity) (P ^ 2), Real.sqrt_sq hPpos.le, hsqrtN3]
  -- split the inversion sum: trivial block + one-dimensional + big blocks
  have hi₀F : i₀ ∉ F := by
    rw [hFdef]
    simp [hdi₀]
  have hterm₀ : (d i₀ : ℝ) * ((e (gowersElt S T U)) i₀).trace.re = P ^ 2 := by
    rw [htriv, Complex.ofReal_re, hdi₀]
    norm_num
  have hFeq : (Finset.univ.erase i₀).filter (fun i => 1 < d i) = F := by
    rw [hFdef]
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
      and_true]
    constructor
    · rintro ⟨-, hj⟩
      exact hj
    · intro hj
      refine ⟨?_, hj⟩
      rintro rfl
      rw [hdi₀] at hj
      omega
  have hsum_split : ∑ i, (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re
      ≥ P ^ 2 - ∑ i ∈ F, (d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖ := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hterm₀,
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i₀)
        (fun i => 1 < d i), hFeq]
    have hpos : 0 ≤ ∑ i ∈ (Finset.univ.erase i₀).filter (fun i => ¬ 1 < d i),
        (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re := by
      refine Finset.sum_nonneg fun i hi => ?_
      simp only [Finset.mem_filter] at hi
      have hd1 : d i = 1 := by
        have h1 := Nat.pos_of_ne_zero (NeZero.ne (d i))
        omega
      exact mul_nonneg (by positivity) (hone i hd1)
    have hFbound : ∑ i ∈ F, (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re
        ≥ -∑ i ∈ F, (d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖ := by
      rw [ge_iff_le, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hre : -‖((e (gowersElt S T U)) i).trace‖
          ≤ ((e (gowersElt S T U)) i).trace.re :=
        (abs_le.mp (Complex.abs_re_le_norm _)).1
      calc -((d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖)
          = (d i : ℝ) * (-‖((e (gowersElt S T U)) i).trace‖) := by ring
        _ ≤ (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re :=
            mul_le_mul_of_nonneg_left hre (by positivity)
    linarith
  -- assemble and divide by `P`
  have hmain : N * P ≥ P ^ 2 - N ^ ((3 : ℝ) / 2) * P / Real.sqrt n := by
    rw [hsix]
    calc ∑ i, (d i : ℝ) * ((e (gowersElt S T U)) i).trace.re
        ≥ P ^ 2 - ∑ i ∈ F, (d i : ℝ) * ‖((e (gowersElt S T U)) i).trace‖ :=
          hsum_split
      _ ≥ P ^ 2 - N ^ ((3 : ℝ) / 2) * P / Real.sqrt n := by linarith
  have hmain' : N * P ≥ P ^ 2 - (N ^ ((3 : ℝ) / 2) / Real.sqrt n) * P := by
    have h2 : N ^ ((3 : ℝ) / 2) * P / Real.sqrt n
        = (N ^ ((3 : ℝ) / 2) / Real.sqrt n) * P := by ring
    linarith [hmain, h2.le, h2.ge]
  have h1 : P * P ≤ (N ^ ((3 : ℝ) / 2) / Real.sqrt n + N) * P := by nlinarith
  exact le_of_mul_le_mul_right (by linarith : P * P
    ≤ (N ^ ((3 : ℝ) / 2) / Real.sqrt n + N) * P) hPpos

end

end Xlib.FourierBarrier
