import Mathlib
import GroupTPP.TPP
import GroupTPP.TPPLift

/-!
# The no-cancellation lemma for monomial realizations

A **monomial realization** of matrix multiplication over a finite group `G`
assigns to each standard basis matrix `E_{ij}` a scalar multiple of a single
group element. The **no-cancellation lemma** says that such a realization
forces the triple product property (TPP) on the index maps: the only way
`a(i,j) * b(j',k) * c(k',i') = 1` is `j = j' /\ k = k' /\ i = i'`.

The proof is by coefficient comparison: evaluating the trilinear identity at
standard basis matrices produces the equation

  `alpha(i,j) * beta(j',k) * gamma(k',i') * [a(i,j) * b(j',k) * c(k',i') = 1_G]`
  `= [j = j'] * [k = k'] * [i = i']`

(using `[P]` for the 0/1 indicator of `P`). Since `alpha`, `beta`, `gamma` are
nonzero, a collision `a(i,j) * b(j',k) * c(k',i') = 1` at an off-diagonal
index triple produces a nonzero left-hand side but a zero right-hand side --
contradiction. No cancellation between distinct colliding triples is possible
over any field, including characteristic 2.

## Statement provenance

This lemma is folklore in the Cohn-Umans matrix multiplication program; it
is implicit in [math/0307321, Theorem 2.3 and Definition 2.4]. The explicit
coefficient-comparison formulation and its connection to the collision form
of the TPP (`GroupTPP.TPP.IsTPPTriple`) were developed in discussion (2026-07).
The statement was verified computationally before formalization (see
`Scratch/verify_tpp.sage`).

## Main definitions

* `GroupTPP.MonomialRealization.IsMonomialRealization` -- the coefficient-level
  identity that a monomial realization satisfies.
* `GroupTPP.MonomialRealization.IsSemanticMonomialRealization` -- the semantic
  identity: `trace(A*B*C) = Phi(phiA(A), phiB(B), phiC(C))` for all matrices.
* `GroupTPP.MonomialRealization.coeffOne` -- the coefficient of `1_G` in a group
  algebra element.
* `GroupTPP.MonomialRealization.Phi` -- the group trilinear form.
* `GroupTPP.MonomialRealization.phiA`, `phiB`, `phiC` -- monomial embeddings.

## Main results

* `GroupTPP.MonomialRealization.IsSemanticMonomialRealization.toMonomialRealization`
  -- the semantic identity implies the coefficient-level identity.
* `GroupTPP.MonomialRealization.no_cancellation` -- **Claim 1**: a monomial
  realization forces `a(i,j) * b(j',k) * c(k',i') = 1 -> j = j' /\ k = k' /\ i = i'`.
* `GroupTPP.MonomialRealization.diagonal_coeff` -- the diagonal coefficient
  identity: `alpha(i,j) * beta(j,k) * gamma(k,i) = 1`.
* `GroupTPP.MonomialRealization.diagonal_group_prod_eq_one` -- the diagonal
  group products are always `1`.
* `GroupTPP.MonomialRealization.collision_preimages_diagonal` -- **Claim 2**:
  the set-level collision form, connecting to preimage consistency.
* `GroupTPP.MonomialRealization.prod` -- **Claim 3**: the Kronecker product of
  two monomial realizations is a monomial realization for the product group.

## Semantic derivation of the coefficient identity

The coefficient identity `coeff_identity` is derived from the honest semantic
definition of a monomial realization: given the group trilinear form
`Phi(x,y,z) = coefficient of 1_G in x*y*z` on the group algebra `F[G]`, and
monomial embeddings `phiA(A) = sum_{i,j} A(i,j) * alpha(i,j) * e_{a(i,j)}` (and
similarly `phiB`, `phiC`), the semantic identity is:
`forall A B C, trace(A*B*C) = Phi(phiA(A), phiB(B), phiC(C))`.

The constructor `IsSemanticMonomialRealization.toMonomialRealization` proves that
this semantic identity (plus nonzero scalars) implies `IsMonomialRealization`,
by evaluating both sides at standard basis matrices `E_{ij}`:
- **LHS:** `trace(E_ij * E_j'k * E_k'i') = [j=j' /\ k=k' /\ i=i']`
- **RHS:** `Phi(single(a_ij, alpha_ij), single(b_j'k, beta_j'k), single(c_k'i', gamma_k'i'))`
  `= alpha * beta * gamma * [a*b*c = 1_G]`

## Discrepancies with the informal claims

**Claim 2 (bridge to IsTPPTriple):** The informal claim suggested the bridge
connects directly to `IsTPPTriple` on image subsets. The honest situation: the
no-cancellation is an INDEX-LEVEL statement (indices must be diagonal), which
does not directly imply the LEFT-QUOTIENT `TripleProductProperty` on images
(that involves six independent preimages and a product `s'^{-1} s t'^{-1} t
u'^{-1} u = 1`). The no-cancellation gives the COLLISION FORM
`s * t * u = 1 -> indices diagonal` on the images. This connects to
`IsTPPTriple` only when the images are subgroups containing `1` AND every
subgroup element occurs as some index map value -- a non-trivial additional
hypothesis. We formalize the honest collision-form statement and note the gap.

## References

* H. Cohn, C. Umans, *A group-theoretic approach to fast matrix
  multiplication*, [arXiv:math/0307321].
* I. Murthy, *Capacity of the triple product property*, [arXiv:2512.16730].
-/

namespace GroupTPP.MonomialRealization

open GroupTPP.TPP Finset Matrix MonoidAlgebra

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]

/-! ### Semantic definitions -/

/-- The coefficient of `1_G` in a group algebra element `x ∈ F[G]`. -/
noncomputable def coeffOne (x : MonoidAlgebra F G) : F := x.coeff 1

/-- The group trilinear form: the coefficient of `1_G` in the product `x * y * z`
in the group algebra `F[G]`. -/
noncomputable def Phi (x y z : MonoidAlgebra F G) : F := coeffOne (x * y * z)

variable {n m p : ℕ}

/-- The monomial embedding of the `A`-factor: sends a matrix
`A : Matrix (Fin n) (Fin m) F` to the group-algebra element
`∑_{i,j} A(i,j) · α(i,j) · e_{a(i,j)}`. -/
noncomputable def phiA
    (a : Fin n → Fin m → G) (α : Fin n → Fin m → F) (A : Matrix (Fin n) (Fin m) F) :
    MonoidAlgebra F G :=
  ∑ i, ∑ j, MonoidAlgebra.single (a i j) (A i j * α i j)

/-- The monomial embedding of the `B`-factor. -/
noncomputable def phiB
    (b : Fin m → Fin p → G) (β : Fin m → Fin p → F) (B : Matrix (Fin m) (Fin p) F) :
    MonoidAlgebra F G :=
  ∑ j, ∑ k, MonoidAlgebra.single (b j k) (B j k * β j k)

/-- The monomial embedding of the `C`-factor. -/
noncomputable def phiC
    (c : Fin p → Fin n → G) (γ : Fin p → Fin n → F) (C : Matrix (Fin p) (Fin n) F) :
    MonoidAlgebra F G :=
  ∑ k, ∑ i, MonoidAlgebra.single (c k i) (C k i * γ k i)

/-- The **semantic monomial realization** identity: for all matrices `A`, `B`, `C`,
the trace of `A * B * C` equals the group trilinear form applied to the monomial
embeddings. This is the honest mathematical definition from which `coeff_identity`
is derived by evaluating at standard basis matrices. -/
structure IsSemanticMonomialRealization
    (a : Fin n → Fin m → G) (b : Fin m → Fin p → G) (c : Fin p → Fin n → G)
    (α : Fin n → Fin m → F) (β : Fin m → Fin p → F) (γ : Fin p → Fin n → F) :
    Prop where
  alpha_ne_zero : ∀ i j, α i j ≠ 0
  beta_ne_zero : ∀ j k, β j k ≠ 0
  gamma_ne_zero : ∀ k i, γ k i ≠ 0
  trilinear_identity : ∀ (A : Matrix (Fin n) (Fin m) F) (B : Matrix (Fin m) (Fin p) F)
    (C : Matrix (Fin p) (Fin n) F),
    Matrix.trace (A * B * C) = Phi (phiA a α A) (phiB b β B) (phiC c γ C)

/-! ### Reduction lemmas for the constructor -/

omit [Group G] [DecidableEq G] in
/-- A double sum of group-algebra singles weighted by a standard basis matrix
collapses to a single term. Used to evaluate `phiA`, `phiB`, `phiC` at basis
matrices. -/
lemma phi_sum_single_collapse
    (f : Fin n → Fin m → G) (α : Fin n → Fin m → F) (i₀ : Fin n) (j₀ : Fin m) :
    (∑ i : Fin n, ∑ j : Fin m,
      MonoidAlgebra.single (f i j) (Matrix.single i₀ j₀ (1 : F) i j * α i j)) =
    MonoidAlgebra.single (f i₀ j₀) (α i₀ j₀) := by
  have step_j : ∀ i, ∑ j : Fin m,
      MonoidAlgebra.single (f i j) (Matrix.single i₀ j₀ (1 : F) i j * α i j) =
      MonoidAlgebra.single (f i j₀) (Matrix.single i₀ j₀ (1 : F) i j₀ * α i j₀) := by
    intro i
    apply Finset.sum_eq_single j₀
    · intro j _ hj
      have h0 : Matrix.single i₀ j₀ (1 : F) i j = 0 := by
        apply Matrix.single_apply_of_ne; intro ⟨_, h2⟩; exact hj h2.symm
      rw [h0, zero_mul]; exact MonoidAlgebra.single_zero _
    · exact fun h => absurd (Finset.mem_univ _) h
  simp_rw [step_j]
  have step_i :
    ∑ i : Fin n, MonoidAlgebra.single (f i j₀) (Matrix.single i₀ j₀ (1 : F) i j₀ * α i j₀) =
    MonoidAlgebra.single (f i₀ j₀) (Matrix.single i₀ j₀ (1 : F) i₀ j₀ * α i₀ j₀) := by
    apply Finset.sum_eq_single i₀
    · intro i _ hi
      have h0 : Matrix.single i₀ j₀ (1 : F) i j₀ = 0 := by
        apply Matrix.single_apply_of_ne; intro ⟨h1, _⟩; exact hi h1.symm
      rw [h0, zero_mul]; exact MonoidAlgebra.single_zero _
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [step_i, Matrix.single_apply_same, one_mul]

omit [Group G] [DecidableEq G] in
lemma phiA_single (a : Fin n → Fin m → G) (α : Fin n → Fin m → F)
    (i₀ : Fin n) (j₀ : Fin m) :
    phiA a α (Matrix.single i₀ j₀ 1) = MonoidAlgebra.single (a i₀ j₀) (α i₀ j₀) :=
  phi_sum_single_collapse a α i₀ j₀

omit [Group G] [DecidableEq G] in
lemma phiB_single (b : Fin m → Fin p → G) (β : Fin m → Fin p → F)
    (j₀ : Fin m) (k₀ : Fin p) :
    phiB b β (Matrix.single j₀ k₀ 1) = MonoidAlgebra.single (b j₀ k₀) (β j₀ k₀) :=
  phi_sum_single_collapse b β j₀ k₀

omit [Group G] [DecidableEq G] in
lemma phiC_single (c : Fin p → Fin n → G) (γ : Fin p → Fin n → F)
    (k₀ : Fin p) (i₀ : Fin n) :
    phiC c γ (Matrix.single k₀ i₀ 1) = MonoidAlgebra.single (c k₀ i₀) (γ k₀ i₀) :=
  phi_sum_single_collapse c γ k₀ i₀

/-- The trace of a triple product of standard basis matrices equals the
Kronecker delta `[j = j' ∧ k = k' ∧ i = i']`. -/
lemma trace_basis_triple
    (i i' : Fin n) (j j' : Fin m) (k k' : Fin p) :
    Matrix.trace
      ((Matrix.single i j (1 : F)) * (Matrix.single j' k (1 : F)) *
       (Matrix.single k' i' (1 : F))) =
    if j = j' ∧ k = k' ∧ i = i' then 1 else 0 := by
  rw [Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one, Matrix.single_apply]
  by_cases hjk : j' = j ∧ k = k'
  · obtain ⟨hj, hk⟩ := hjk
    subst hj; subst hk
    simp only [and_self, ite_true]
    by_cases hi : i = i'
    · subst hi; simp [Matrix.trace_single_eq_same]
    · rw [if_neg (by tauto)]
      simp [Matrix.trace, hi]
  · rw [if_neg hjk, Matrix.single_zero, Matrix.trace_zero, if_neg]
    intro ⟨hj, hk, _⟩
    exact hjk ⟨hj.symm, hk⟩

/-- The trilinear form `Phi` applied to three group-algebra singles reduces to
a coefficient-times-indicator expression. -/
lemma Phi_single_single_single
    (g₁ g₂ g₃ : G) (r₁ r₂ r₃ : F) :
    Phi (MonoidAlgebra.single g₁ r₁) (MonoidAlgebra.single g₂ r₂)
        (MonoidAlgebra.single g₃ r₃) =
    r₁ * r₂ * r₃ * if g₁ * g₂ * g₃ = 1 then 1 else 0 := by
  unfold Phi coeffOne
  rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, mul_assoc]
  split_ifs <;> ring

/-- The **monomial realization identity**: the coefficient-level equation that a
monomial realization of `(n, m, p)`-matrix multiplication over a group `G` with
field `F` must satisfy.

`a : Fin n -> Fin m -> G` is the index map for the `A`-factor,
`b : Fin m -> Fin p -> G` for `B`, `c : Fin p -> Fin n -> G` for `C`.
`alpha`, `beta`, `gamma` are the corresponding nonzero scalar functions.

The identity says: for all index sextuples `(i, j, j', k, k', i')`,
the product `alpha_{ij} * beta_{j'k} * gamma_{k'i'}` times the
group-collision indicator `[a(i,j) * b(j',k) * c(k',i') = 1_G]` equals
the Kronecker delta `[j = j'] * [k = k'] * [i = i']`.

This is obtained by evaluating the trilinear form identity at standard basis
matrices and comparing coefficients of `1_G` in the group algebra. -/
structure IsMonomialRealization {n m p : ℕ}
    (a : Fin n → Fin m → G) (b : Fin m → Fin p → G) (c : Fin p → Fin n → G)
    (α : Fin n → Fin m → F) (β : Fin m → Fin p → F) (γ : Fin p → Fin n → F) :
    Prop where
  alpha_ne_zero : ∀ i j, α i j ≠ 0
  beta_ne_zero : ∀ j k, β j k ≠ 0
  gamma_ne_zero : ∀ k i, γ k i ≠ 0
  coeff_identity : ∀ (i i' : Fin n) (j j' : Fin m) (k k' : Fin p),
    α i j * β j' k * γ k' i' *
      (if a i j * b j' k * c k' i' = 1 then (1 : F) else 0)
    = if j = j' ∧ k = k' ∧ i = i' then 1 else 0

/-! ### Constructor: semantic identity implies coefficient identity -/

/-- **Constructor:** the semantic monomial realization identity implies the
coefficient-level identity `IsMonomialRealization`. The proof evaluates the
trilinear identity at standard basis matrices `E_{ij}, E_{j'k}, E_{k'i'}` and
compares the trace side (Kronecker delta) with the group-algebra side
(coefficient extraction). -/
theorem IsSemanticMonomialRealization.toMonomialRealization
    {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
    {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}
    (h : IsSemanticMonomialRealization a b c α β γ) :
    IsMonomialRealization a b c α β γ where
  alpha_ne_zero := h.alpha_ne_zero
  beta_ne_zero := h.beta_ne_zero
  gamma_ne_zero := h.gamma_ne_zero
  coeff_identity := by
    intro i i' j j' k k'
    have key := h.trilinear_identity
      (Matrix.single i j 1) (Matrix.single j' k 1) (Matrix.single k' i' 1)
    rw [trace_basis_triple] at key
    rw [phiA_single, phiB_single, phiC_single, Phi_single_single_single] at key
    simp only [mul_assoc] at key ⊢
    exact key.symm

variable {n m p : ℕ}
variable {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
variable {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}

/-! ### Claim 1: No cancellation -/

/-- **No cancellation (Claim 1).** If `(a, alpha), (b, beta), (c, gamma)` is a
monomial realization, then `a(i,j) * b(j',k) * c(k',i') = 1` forces
`j = j'`, `k = k'`, and `i = i'`.

Proof: if the group product is `1` but the index triple is off-diagonal,
the LHS of the realization identity is `alpha * beta * gamma /= 0` but the
RHS is `0`. -/
theorem no_cancellation
    (h : IsMonomialRealization a b c α β γ)
    {i i' : Fin n} {j j' : Fin m} {k k' : Fin p}
    (hcol : a i j * b j' k * c k' i' = 1) :
    j = j' ∧ k = k' ∧ i = i' := by
  have key := h.coeff_identity i i' j j' k k'
  rw [if_pos hcol, mul_one] at key
  have hne : α i j * β j' k * γ k' i' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (h.alpha_ne_zero i j) (h.beta_ne_zero j' k))
      (h.gamma_ne_zero k' i')
  by_contra h_neg
  rw [if_neg h_neg] at key
  exact hne key

/-- The diagonal group products are always `1`. This follows from the
realization identity: at the diagonal, the RHS is `1`, so the LHS must be
nonzero, hence the indicator must be `1`, hence the group product is `1`. -/
theorem diagonal_group_prod_eq_one
    (h : IsMonomialRealization a b c α β γ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    a i j * b j k * c k i = 1 := by
  have key := h.coeff_identity i i j j k k
  simp only [and_self, ite_true] at key
  -- key : α i j * β j k * γ k i * (if a i j * b j k * c k i = 1 then 1 else 0) = 1
  by_contra hne
  rw [if_neg hne, mul_zero] at key
  exact one_ne_zero key.symm

/-- **Diagonal coefficient identity.** At the diagonal, the coefficient product
equals `1`: `alpha(i,j) * beta(j,k) * gamma(k,i) = 1`. -/
theorem diagonal_coeff
    (h : IsMonomialRealization a b c α β γ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    α i j * β j k * γ k i = 1 := by
  have key := h.coeff_identity i i j j k k
  simp only [and_self, ite_true] at key
  rw [if_pos (diagonal_group_prod_eq_one h i j k), mul_one] at key
  exact key

/-! ### Restatement with reordered conclusion -/

/-- **Restatement with conclusion `i = i' /\ j = j' /\ k = k'`.** -/
theorem collision_forces_diagonal
    (h : IsMonomialRealization a b c α β γ)
    {i i' : Fin n} {j j' : Fin m} {k k' : Fin p}
    (hcol : a i j * b j' k * c k' i' = 1) :
    i = i' ∧ j = j' ∧ k = k' := by
  have ⟨hj, hk, hi⟩ := no_cancellation h hcol
  exact ⟨hi, hj, hk⟩

/-! ### Claim 2: Set-level collision form

The no-cancellation gives a set-level collision form: for any `s` in the image
of `a`, `t` in the image of `b`, `u` in the image of `c`, if `s * t * u = 1`,
then the preimage indices must match -- they form a consistent diagonal triple.

This is the honest content of "Claim 2": the bridge to the TPP at the level of
group elements, without forcing a false strengthening to `IsTPPTriple` on
arbitrary image sets. -/

/-- **Set-level collision form (Claim 2).** For any `s` in the image of `a`,
`t` in the image of `b`, `u` in the image of `c`, if `s * t * u = 1`, then
the preimage indices form a consistent diagonal triple:
`s = a(i,j)`, `t = b(j,k)`, `u = c(k,i)` for some `i, j, k`. -/
theorem collision_preimages_diagonal
    (h : IsMonomialRealization a b c α β γ)
    {s t u : G}
    {i : Fin n} {j₁ : Fin m} (hs : s = a i j₁)
    {j₂ : Fin m} {k₁ : Fin p} (ht : t = b j₂ k₁)
    {k₂ : Fin p} {i' : Fin n} (hu : u = c k₂ i')
    (hcol : s * t * u = 1) :
    j₁ = j₂ ∧ k₁ = k₂ ∧ i = i' := by
  subst hs; subst ht; subst hu
  exact no_cancellation (i := i) (i' := i') (j := j₁) (j' := j₂) (k := k₁) (k' := k₂) h hcol

/-! ### Claim 3: Kronecker product of monomial realizations

The Kronecker (tensor) product of two monomial realizations is again a monomial
realization, for the product group `G_1 x G_2` and the product index maps.

To avoid `Fin` type coercions, we generalize `IsMonomialRealization` to
arbitrary `DecidableEq` + `Fintype` index types. The original `Fin`-indexed
version is a special case. -/

/-- Generalized monomial realization over arbitrary finite index types. -/
structure IsMonomialRealizationGen
    {I J K : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {F : Type*} [Field F] {G : Type*} [Group G] [DecidableEq G]
    (a : I → J → G) (b : J → K → G) (c : K → I → G)
    (α : I → J → F) (β : J → K → F) (γ : K → I → F) : Prop where
  alpha_ne_zero : ∀ i j, α i j ≠ 0
  beta_ne_zero : ∀ j k, β j k ≠ 0
  gamma_ne_zero : ∀ k i, γ k i ≠ 0
  coeff_identity : ∀ (i i' : I) (j j' : J) (k k' : K),
    α i j * β j' k * γ k' i' *
      (if a i j * b j' k * c k' i' = 1 then (1 : F) else 0)
    = if j = j' ∧ k = k' ∧ i = i' then 1 else 0

/-- `IsMonomialRealization` implies `IsMonomialRealizationGen`. -/
theorem IsMonomialRealization.toGen
    (h : IsMonomialRealization a b c α β γ) :
    IsMonomialRealizationGen a b c α β γ where
  alpha_ne_zero := h.alpha_ne_zero
  beta_ne_zero := h.beta_ne_zero
  gamma_ne_zero := h.gamma_ne_zero
  coeff_identity := h.coeff_identity

/-- No cancellation for the generalized version. -/
theorem IsMonomialRealizationGen.no_cancellation
    {I J K : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {F : Type*} [Field F] {G : Type*} [Group G] [DecidableEq G]
    {a : I → J → G} {b : J → K → G} {c : K → I → G}
    {α : I → J → F} {β : J → K → F} {γ : K → I → F}
    (h : IsMonomialRealizationGen a b c α β γ)
    {i i' : I} {j j' : J} {k k' : K}
    (hcol : a i j * b j' k * c k' i' = 1) :
    j = j' ∧ k = k' ∧ i = i' := by
  have key := h.coeff_identity i i' j j' k k'
  rw [if_pos hcol, mul_one] at key
  have hne : α i j * β j' k * γ k' i' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (h.alpha_ne_zero i j) (h.beta_ne_zero j' k))
      (h.gamma_ne_zero k' i')
  by_contra h_neg
  rw [if_neg h_neg] at key
  exact hne key

/-- Diagonal group products are `1` for the generalized version. -/
theorem IsMonomialRealizationGen.diagonal_group_prod_eq_one
    {I J K : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq K]
    {F : Type*} [Field F] {G : Type*} [Group G] [DecidableEq G]
    {a : I → J → G} {b : J → K → G} {c : K → I → G}
    {α : I → J → F} {β : J → K → F} {γ : K → I → F}
    (h : IsMonomialRealizationGen a b c α β γ)
    (i : I) (j : J) (k : K) :
    a i j * b j k * c k i = 1 := by
  have key := h.coeff_identity i i j j k k
  simp only [and_self, ite_true] at key
  by_contra hne
  rw [if_neg hne, mul_zero] at key
  exact one_ne_zero key.symm

/-- **Kronecker product of monomial realizations (Claim 3).**

The product index maps `a((i_1,i_2), (j_1,j_2)) = (a_1(i_1,j_1), a_2(i_2,j_2))`
with coefficient products form a monomial realization of matrix multiplication
over `G_1 x G_2`. -/
theorem IsMonomialRealizationGen.prod
    {I₁ J₁ K₁ : Type*} [DecidableEq I₁] [DecidableEq J₁] [DecidableEq K₁]
    {I₂ J₂ K₂ : Type*} [DecidableEq I₂] [DecidableEq J₂] [DecidableEq K₂]
    {G₁ : Type*} [Group G₁] [DecidableEq G₁]
    {G₂ : Type*} [Group G₂] [DecidableEq G₂]
    {a₁ : I₁ → J₁ → G₁} {b₁ : J₁ → K₁ → G₁} {c₁ : K₁ → I₁ → G₁}
    {α₁ : I₁ → J₁ → F} {β₁ : J₁ → K₁ → F} {γ₁ : K₁ → I₁ → F}
    {a₂ : I₂ → J₂ → G₂} {b₂ : J₂ → K₂ → G₂} {c₂ : K₂ → I₂ → G₂}
    {α₂ : I₂ → J₂ → F} {β₂ : J₂ → K₂ → F} {γ₂ : K₂ → I₂ → F}
    (h₁ : IsMonomialRealizationGen (F := F) a₁ b₁ c₁ α₁ β₁ γ₁)
    (h₂ : IsMonomialRealizationGen (F := F) a₂ b₂ c₂ α₂ β₂ γ₂) :
    IsMonomialRealizationGen (F := F)
      (fun (i : I₁ × I₂) (j : J₁ × J₂) => (a₁ i.1 j.1, a₂ i.2 j.2))
      (fun (j : J₁ × J₂) (k : K₁ × K₂) => (b₁ j.1 k.1, b₂ j.2 k.2))
      (fun (k : K₁ × K₂) (i : I₁ × I₂) => (c₁ k.1 i.1, c₂ k.2 i.2))
      (fun (i : I₁ × I₂) (j : J₁ × J₂) => α₁ i.1 j.1 * α₂ i.2 j.2)
      (fun (j : J₁ × J₂) (k : K₁ × K₂) => β₁ j.1 k.1 * β₂ j.2 k.2)
      (fun (k : K₁ × K₂) (i : I₁ × I₂) => γ₁ k.1 i.1 * γ₂ k.2 i.2) where
  alpha_ne_zero i j :=
    mul_ne_zero (h₁.alpha_ne_zero i.1 j.1) (h₂.alpha_ne_zero i.2 j.2)
  beta_ne_zero j k :=
    mul_ne_zero (h₁.beta_ne_zero j.1 k.1) (h₂.beta_ne_zero j.2 k.2)
  gamma_ne_zero k i :=
    mul_ne_zero (h₁.gamma_ne_zero k.1 i.1) (h₂.gamma_ne_zero k.2 i.2)
  coeff_identity := by
    intro ⟨i₁, i₂⟩ ⟨i₁', i₂'⟩ ⟨j₁, j₂⟩ ⟨j₁', j₂'⟩ ⟨k₁, k₂⟩ ⟨k₁', k₂'⟩
    -- Product in G₁ x G₂ equals 1 iff both components equal 1
    have hone : (a₁ i₁ j₁, a₂ i₂ j₂) * (b₁ j₁' k₁, b₂ j₂' k₂) *
        (c₁ k₁' i₁', c₂ k₂' i₂') = 1 ↔
        a₁ i₁ j₁ * b₁ j₁' k₁ * c₁ k₁' i₁' = 1 ∧
        a₂ i₂ j₂ * b₂ j₂' k₂ * c₂ k₂' i₂' = 1 := by
      simp only [Prod.mk_mul_mk, Prod.mk_eq_one]
    -- Diagonal condition splits componentwise
    have hdiag : ((j₁, j₂) = (j₁', j₂') ∧ (k₁, k₂) = (k₁', k₂') ∧
        (i₁, i₂) = (i₁', i₂')) ↔
        (j₁ = j₁' ∧ k₁ = k₁' ∧ i₁ = i₁') ∧
        (j₂ = j₂' ∧ k₂ = k₂' ∧ i₂ = i₂') := by
      simp only [Prod.mk.injEq]
      tauto
    -- Coefficient factoring
    have hcoeff : α₁ i₁ j₁ * α₂ i₂ j₂ * (β₁ j₁' k₁ * β₂ j₂' k₂) *
        (γ₁ k₁' i₁' * γ₂ k₂' i₂') =
        (α₁ i₁ j₁ * β₁ j₁' k₁ * γ₁ k₁' i₁') *
        (α₂ i₂ j₂ * β₂ j₂' k₂ * γ₂ k₂' i₂') := by ring
    -- Strategy: reduce the generalized realization to its component realizations.
    -- The key factorization: the product identity for (G₁ x G₂) factors as
    -- the product of component identities for G₁ and G₂.
    -- We use a helper that does the ite factoring.
    have key₁ := h₁.coeff_identity i₁ i₁' j₁ j₁' k₁ k₁'
    have key₂ := h₂.coeff_identity i₂ i₂' j₂ j₂' k₂ k₂'
    -- Normalize all Prod operations to components
    simp only [Prod.mk_mul_mk, Prod.mk_eq_one, Prod.mk.injEq]
    -- Goal is now:
    -- α₁ i₁ j₁ * α₂ i₂ j₂ * (β₁ j₁' k₁ * β₂ j₂' k₂) * (γ₁ k₁' i₁' * γ₂ k₂' i₂') *
    --   ite(comp₁ = 1 ∧ comp₂ = 1) = ite((j₁=j₁' ∧ j₂=j₂') ∧ (k₁=k₁' ∧ k₂=k₂') ∧ i₁=i₁' ∧ i₂=i₂')
    -- Rewrite: ite(P ∧ Q) with 0/1 = ite(P)*ite(Q) (as field elements)
    -- and the coefficient factors as (c₁*c₂).
    -- Reduce to (c₁*ite(p₁))*(c₂*ite(p₂)) = ite(d₁)*ite(d₂)
    -- which is key₁ * key₂.
    -- Direct computation by case split
    by_cases hc₁ : a₁ i₁ j₁ * b₁ j₁' k₁ * c₁ k₁' i₁' = 1 <;>
    by_cases hc₂ : a₂ i₂ j₂ * b₂ j₂' k₂ * c₂ k₂' i₂' = 1
    -- All 4 cases share the pattern: LHS = coeff * 0 = 0 (when one component /= 1),
    -- or LHS = coeff * 1 (when both = 1). RHS = 0 or 1 by the diagonal.
    -- Helper: when the conjunction is false, both sides are 0.
    · -- pos/pos: both group products = 1
      rw [if_pos ⟨hc₁, hc₂⟩, hcoeff, mul_one]
      rw [if_pos hc₁, mul_one] at key₁
      rw [if_pos hc₂, mul_one] at key₂
      have nd₁ := h₁.no_cancellation hc₁
      have nd₂ := h₂.no_cancellation hc₂
      rw [key₁, key₂, if_pos ⟨nd₁.1, nd₁.2.1, nd₁.2.2⟩, if_pos ⟨nd₂.1, nd₂.2.1, nd₂.2.2⟩]
      have hd : (j₁ = j₁' ∧ j₂ = j₂') ∧ (k₁ = k₁' ∧ k₂ = k₂') ∧ i₁ = i₁' ∧ i₂ = i₂' :=
        And.intro (And.intro nd₁.1 nd₂.1) (And.intro (And.intro nd₁.2.1 nd₂.2.1) (And.intro nd₁.2.2 nd₂.2.2))
      simp [hd]
    · -- pos/neg: second component /= 1
      rw [if_neg (fun h => hc₂ h.2), mul_zero, if_neg]
      rintro ⟨⟨_, hj₂⟩, ⟨_, hk₂⟩, _, hi₂⟩
      exact hc₂ (by rw [hj₂, hk₂, hi₂]; exact h₂.diagonal_group_prod_eq_one _ _ _)
    · -- neg/pos: first component /= 1
      rw [if_neg (fun h => hc₁ h.1), mul_zero, if_neg]
      rintro ⟨⟨hj₁, _⟩, ⟨hk₁, _⟩, hi₁, _⟩
      exact hc₁ (by rw [hj₁, hk₁, hi₁]; exact h₁.diagonal_group_prod_eq_one _ _ _)
    · -- neg/neg: first component /= 1
      rw [if_neg (fun h => hc₁ h.1), mul_zero, if_neg]
      rintro ⟨⟨hj₁, _⟩, ⟨hk₁, _⟩, hi₁, _⟩
      exact hc₁ (by rw [hj₁, hk₁, hi₁]; exact h₁.diagonal_group_prod_eq_one _ _ _)

end GroupTPP.MonomialRealization
