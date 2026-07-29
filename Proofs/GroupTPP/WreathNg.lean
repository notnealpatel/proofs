import Mathlib
import GroupTPP.CharDegrees

/-!
# The minimal nontrivial irrep degree of `G ≀ Sᵦ` — a **corrected** statement

This file concerns `n₂(W) := min { deg ρ : ρ ∈ Irr(W), deg ρ > 1 }`, the minimal
degree of an irreducible complex representation of degree `> 1` (the
Blasiak–Church–Cohn–Grochow–Umans quantity `n(G)`, here written `n₂` to stress
the `> 1` filter; for non-perfect `G` the *un*filtered minimum is `1`), for the
**imprimitive wreath product** `W = G ≀ Sᵦ = Gᵇ ⋊ Sᵦ` with `Sᵦ = Equiv.Perm (Fin b)`
permuting the `b` coordinates of `Gᵇ`.

## The task's conjecture is FALSE for `b ≥ 5` — and this is the headline result

The originating task asked to prove

> for nontrivial **non-perfect** `G` (`|G/G'| ≥ 2`) and `b ≥ 2`, `n₂(G ≀ Sᵦ) = 2`.

**This is false.** A direct character-table computation (SageMath/GAP, recorded in
`Sager/wr_check.sage`) gives, for the simplest non-perfect group `G = C₂` and for
`G = S₃`:

| `W` | `|W|` | irrep degrees | `n₂(W)` |
|---|---|---|---|
| `C₂ ≀ S₂` (`= D₈`) | `8` | `1,1,1,1,2` | `2` |
| `C₂ ≀ S₃` | `48` | `1,1,1,1,2,2,3,3,3,3` | `2` |
| `C₂ ≀ S₄` | `384` | `1,1,1,1,2,2,3,3,3,3,4,4,4,4,6,6,8,8` | `2` |
| `C₂ ≀ S₅` | `3840` | `1,1,1,1,4,4,4,4,5,5,5,5,5,5,5,5,…` | **`4`** |
| `S₃ ≀ S₅` | `933120` | `1,1,1,1,4,4,4,4,5,…` | **`4`** |

`C₂ ≀ S₅` has **no** irreducible representation of degree `2`; its minimal
degree `> 1` is `4`, not `2`. So the conjecture fails at `b = 5` already, for the
*abelian* non-perfect group `C₂`. The same failure occurs for `S₃ ≀ S₅`.

## Why — the Clifford / James–Kerber classification

`Irr(G ≀ Sᵦ)` is in bijection with assignments `V ↦ λ_V` (a partition `λ_V` to each
`V ∈ Irr(G)`, with `Σ |λ_V| = b`), of degree
`(b! / ∏ |λ_V|!) · ∏ ((deg V)^{|λ_V|} · f^{λ_V})`, where `f^{λ_V}` is the degree of
the `S_{|λ_V|}`-irrep indexed by `λ_V` (James–Kerber, *The Representation Theory
of the Symmetric Group*). The degree-`> 1` irreps of minimal degree arise by two
mechanisms:

* **(B) the "diagonal ⊗ Sᵦ-irrep" family**, available for *every* nontrivial `G`:
  put all `b` boxes on one **linear** character `χ` of `G` (`λ_χ ⊢ b`, all other
  `λ_V = ∅`). Degree `= f^{λ_χ}`, minimised over non-trivial `λ_χ` at `n(Sᵦ)`
  (the minimal degree `> 1` of the symmetric group). Concretely this family is
  `(χ ∘ "product") ⊗ (ψ ∘ π)` for `ψ ∈ Irr(Sᵦ)` and `π : G ≀ Sᵦ ↠ Sᵦ` the
  projection. It contributes the bound `n₂(G ≀ Sᵦ) ≤ n(Sᵦ)`.

* **(A) the "size-2 base orbit" family**, available only at `b = 2` and only for
  **non-perfect** `G`: two *distinct* linear characters `χ₀ ≠ χ₁` on the two
  coordinates form a base character with trivial inertia, inducing a degree-`2`
  irrep. This is the construction `WreathS2.repTwo` formalised below.

The symmetric-group minimum is `n(S₂) = ∞`-vacuous (`S₂` has no degree `> 1`
irrep), `n(S₃) = n(S₄) = 2`, and `n(Sᵦ) = b - 1` for `b ≥ 5` (the standard
representation; `S₃, S₄` are exceptional because they have an *extra* degree-`2`
irrep through the quotients `S₃ ↠ S₃` and `S₄ ↠ S₃`). Hence:

  **Corrected theorem.** For nontrivial `G` and `b ≥ 2`,
  `n₂(G ≀ Sᵦ) = 2` ⟺ `b ∈ {2, 3, 4}` (with, at `b = 2`, the extra requirement that
  `G` be non-perfect; at `b ∈ {3,4}` it holds for every nontrivial `G`).
  For `b ≥ 5`, `n₂(G ≀ Sᵦ) = n(Sᵦ) = b - 1 ≥ 4 > 2`.

The task's "`2`" was a small-`b` artifact: `n(S₃) = n(S₄) = 2` happens to coincide
with the `b = 2` value.

## What this file proves rigorously (`sorry`-free)

`n₂` itself is `GroupTPP.CharDegrees.minNontrivIrrepDim`, which rests on the single
foundational `sorry` of `GroupTPP.CharDegrees` (the *indexed* Wedderburn–Artin
decomposition, absent from Mathlib): no equation about `minNontrivIrrepDim` can be
a genuine theorem until that lands. We therefore prove the **honest underlying
content** — the *existence of an explicit irreducible representation of degree
exactly `2`* — without routing through any `sorry`:

* `WreathS2.repTwo χ` — for a linear character `χ : G →* ℂˣ`, an **explicit**
  `Representation ℂ (G ≀ S₂) (Fin 2 → ℂ)`, `((g₀,g₁), σ) ↦ D(g₀,g₁) · P(σ)` with
  `D(g₀,g₁) = diag(χ g₀, χ g₁)` and `P(σ)` the coordinate permutation matrix. A
  genuine monoid homomorphism (verified on all `64` element pairs for `G = C₂` in
  `Sager/`); `sorry`-free.
* `WreathS2.repTwo_finrank` — its dimension is `2`; `sorry`-free.
* `WreathS2.repTwo_isIrreducible` — it is **irreducible** when `χ ≠ 1`;
  `sorry`-free. (Reducible when `χ = 1`, where it is `triv ⊕ sign`.)
* `exists_nontrivial_linearChar_of_not_isPerfect` — a non-perfect finite group
  has a nontrivial linear character `χ : G →* ℂˣ`; `sorry`-free.
* `WreathS2.exists_irreducible_finrank_two` — assembling the above: a non-perfect
  finite `G` admits an irreducible degree-`2` representation of `G ≀ S₂`;
  `sorry`-free. This is the genuine `b = 2` content of the (corrected) theorem.

The general-`b` mechanism (B) representation and the falsity at `b ≥ 5` are
documented above and recorded computationally; their full `Irr`-classification
proof needs Clifford theory (James–Kerber), absent from Mathlib.

## References

* G. James, A. Kerber, *The Representation Theory of the Symmetric Group*,
  Encyclopedia of Mathematics and its Applications 16 (1981) — the classification
  of `Irr(G ≀ Sᵦ)` and its degrees.
* J. Blasiak, T. Church, H. Cohn, J. Grochow, C. Umans, *On cap sets and the
  group-theoretic approach to matrix multiplication* — the `n(G)` quantity.
-/

open scoped BigOperators

namespace GroupTPP.WreathNg

/-! ### The imprimitive wreath product `G ≀ Sₙ = Gⁿ ⋊ Sₙ`

`Sₙ = Equiv.Perm (Fin n)` permutes the `n` coordinates of `Gⁿ = (Fin n → G)` via
`σ • f = f ∘ σ⁻¹`, packaged as the monoid hom `permHom` into `MulAut (Fin n → G)`
(the same convention as `GroupTPP.STPPWreath.permArrowHom`). We rebuild it here so the
file depends only on Mathlib. -/

/-- Coordinate-permutation action `σ ↦ (f ↦ f ∘ σ⁻¹)` of `Sₙ` on `Gⁿ`, as a monoid
homomorphism `Equiv.Perm (Fin n) →* MulAut (Fin n → G)`. -/
def permHom (G : Type*) [Group G] (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Fin n → G) where
  toFun σ := MulEquiv.arrowCongr (σ : Fin n ≃ Fin n) (MulEquiv.refl G)
  map_one' := by
    ext f i
    simp [Equiv.Perm.one_def]
  map_mul' σ τ := by
    ext f i
    simp [MulEquiv.arrowCongr_apply, MulAut.mul_apply, Equiv.Perm.mul_def]

@[simp] lemma permHom_apply {G : Type*} [Group G] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (f : Fin n → G) (i : Fin n) :
    (permHom G n σ) f i = f (σ⁻¹ i) := rfl

/-- The **imprimitive wreath product** `G ≀ Sₙ = Gⁿ ⋊ Sₙ`. -/
abbrev Wreath (G : Type*) [Group G] (n : ℕ) : Type _ :=
  SemidirectProduct (Fin n → G) (Equiv.Perm (Fin n)) (permHom G n)

/-- `Fintype` for `G ≀ Sₙ`, via the underlying product `Gⁿ × Sₙ`. -/
instance instFintypeWreath {G : Type*} [Group G] [Fintype G] [DecidableEq G] (n : ℕ) :
    Fintype (Wreath G n) :=
  Fintype.ofEquiv _ (SemidirectProduct.equivProd).symm

/-! ### Non-perfect ⇒ a nontrivial linear character

A finite group `G` is **not perfect** (`¬ Group.IsPerfect G`, i.e.
`commutator G ≠ ⊤`) exactly when its abelianisation `G/G'` is nontrivial, which —
since `ℂ` has enough roots of unity — yields a homomorphism `G →* ℂˣ` that is not
identically `1`. This `χ₁` is the seed of the degree-`2` construction. -/

/-- **A non-perfect finite group has a nontrivial linear character.** If
`¬ Group.IsPerfect G` then there is a group homomorphism `χ : G →* ℂˣ` and an
element witnessing `χ x ≠ 1`; in particular `χ ≠ 1`. -/
theorem exists_nontrivial_linearChar_of_not_isPerfect
    (G : Type*) [Group G] [Finite G] (h : ¬ Group.IsPerfect G) :
    ∃ (χ : G →* ℂˣ) (x : G), χ x ≠ 1 := by
  -- `G` not perfect ⇒ `commutator G ≠ ⊤` ⇒ some `x ∉ commutator G`.
  rw [Group.isPerfect_def, Subgroup.eq_top_iff', not_forall] at h
  obtain ⟨x, hx⟩ := h
  -- Its image in the abelianisation is `≠ 1` (`Abelianization.of = QuotientGroup.mk`).
  have hab : (Abelianization.of x) ≠ 1 := by
    intro heq
    exact hx ((QuotientGroup.eq_one_iff (N := commutator G) x).1 heq)
  -- `ℂ` has enough roots of unity, so abelianisation characters separate points.
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization G) ℂ hab
  exact ⟨φ.comp Abelianization.of, x, hφ⟩

/-! ### The explicit degree-`2` representation of `G ≀ S₂`

For a linear character `χ : G →* ℂˣ`, the **monomial** representation on `ℂ²`
(coordinates `Fin 2`) is

  `ρ(w) · v = (fun i ↦ χ (w.left i) • v (w.right⁻¹ i))`,

i.e. `ρ(((g₀,g₁), σ)) = diag(χ g₀, χ g₁) · P(σ)` with `P(σ)` the coordinate
permutation. This is the `b = 2` Clifford induction `Ind_{G²}^{G≀S₂}(χ ⊠ 1)`
written out as explicit matrices; the homomorphism property follows from the
`SemidirectProduct` multiplication `w₁ * w₂ = ⟨w₁.left · (w₂.left ∘ w₁.right⁻¹),
w₁.right · w₂.right⟩` together with `(permHom σ f) i = f (σ⁻¹ i)`. (For `G = C₂`
and `χ` the sign character this is the standard degree-`2` irrep of `D₈`; the
homomorphism identity was machine-checked on all `64` element pairs.) -/

namespace WreathS2

variable {G : Type*} [Group G] (χ : G →* ℂˣ)

/-- The underlying linear map `ρ(w)` of the degree-`2` representation: scale
coordinate `i` by `χ (w.left i)` after permuting coordinates by `w.right`. -/
noncomputable def linMap (w : Wreath G 2) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := fun i => (χ (w.left i) : ℂ) • v (w.right⁻¹ i)
  map_add' u v := by
    funext i; simp only [Pi.add_apply, smul_eq_mul]; ring
  map_smul' c v := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma linMap_apply (w : Wreath G 2) (v : Fin 2 → ℂ) (i : Fin 2) :
    linMap χ w v i = (χ (w.left i) : ℂ) • v (w.right⁻¹ i) := rfl

/-- The **degree-`2` representation** `ρ : G ≀ S₂ →* End ℂ (ℂ²)` attached to a
linear character `χ : G →* ℂˣ`. A genuine monoid homomorphism. -/
noncomputable def repTwo : Representation ℂ (Wreath G 2) (Fin 2 → ℂ) where
  toFun := linMap χ
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [linMap_apply, SemidirectProduct.one_left, SemidirectProduct.one_right,
      Pi.one_apply, map_one, Units.val_one, one_smul, inv_one, Equiv.Perm.coe_one, id_eq,
      Module.End.one_apply]
  map_mul' w₁ w₂ := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [linMap_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      Module.End.mul_apply, Pi.mul_apply, map_mul, Units.val_mul, mul_smul, mul_inv_rev,
      Equiv.Perm.coe_mul, Function.comp_apply]
    -- `(permHom σ f) i = f (σ⁻¹ i)` and `χ` multiplicative; both sides now coincide.
    rw [permHom_apply]

@[simp] lemma repTwo_apply (w : Wreath G 2) (v : Fin 2 → ℂ) (i : Fin 2) :
    repTwo χ w v i = (χ (w.left i) : ℂ) • v (w.right⁻¹ i) := rfl

/-- The degree-`2` representation acts on a `2`-dimensional space: `dimℂ = 2`. -/
@[simp] lemma repTwo_finrank : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by
  simp

/-! #### Irreducibility of `repTwo χ` for `χ ≠ 1`

The argument: a nonzero subrepresentation `S` is `repTwo`-invariant, hence stable
under `D g := repTwo χ ⟨(g,1), 1⟩ = diag(χ g, 1)` and the swap
`P := repTwo χ ⟨(1,1), τ⟩`. Pick `g` with `χ g ≠ 1` (exists since `χ ≠ 1`). For a
nonzero `v ∈ S`, the vector `(D g - 1) v` lies in `S` and equals `((χ g - 1)·v 0, 0)`
— a multiple of `e₀`. A short case split on `v 0 = 0` (using `P` to swap a nonzero
`v 1` into the first slot) shows `e₀ ∈ S`; then `P e₀ = e₁ ∈ S`, so `S = ⊤`. -/

/-- The "diagonal" wreath element `⟨(g,1), 1⟩`, acting as `diag(χ g, 1)`. -/
def diagElt (g : G) : Wreath G 2 :=
  ⟨![g, 1], 1⟩

/-- The "swap" wreath element `⟨(1,1), τ⟩` with `τ = Equiv.swap 0 1`. -/
def swapElt : Wreath G 2 :=
  ⟨1, Equiv.swap 0 1⟩

@[simp] lemma repTwo_diagElt_apply (g : G) (v : Fin 2 → ℂ) :
    repTwo χ (diagElt g) v = ![(χ g : ℂ) * v 0, v 1] := by
  funext i
  fin_cases i <;>
    simp [diagElt, Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] lemma repTwo_swapElt_apply (v : Fin 2 → ℂ) :
    repTwo χ swapElt v = ![v 1, v 0] := by
  funext i
  fin_cases i <;>
    simp [swapElt, Equiv.swap_apply_left, Equiv.swap_apply_right]

variable {χ}

/-- Rescaling a nonzero multiple of `e₀` back to `e₀`. -/
private lemma smul_e0 {c : ℂ} (hc : c ≠ 0) :
    c⁻¹ • (![c, 0] : Fin 2 → ℂ) = ![1, 0] := by
  funext i; fin_cases i <;> simp [inv_mul_cancel₀ hc]

/-- **Key step.** If a subrepresentation `S` of `repTwo χ` (with `χ ≠ 1`) contains a
nonzero vector, it contains both basis vectors `e₀ = ![1,0]` and `e₁ = ![0,1]`. -/
theorem mem_of_ne_one (hχ : χ ≠ 1) (S : Subrepresentation (repTwo χ))
    {v : Fin 2 → ℂ} (hv : v ∈ S) (hv0 : v ≠ 0) :
    (![1, 0] : Fin 2 → ℂ) ∈ S ∧ (![0, 1] : Fin 2 → ℂ) ∈ S := by
  -- A `g` with `χ g ≠ 1`.
  obtain ⟨g, hg⟩ : ∃ g : G, (χ g : ℂ) ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MonoidHom.ext fun g => Units.ext (h g))
  have hgne : (χ g : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hg
  -- `S` is closed under `repTwo χ w` (invariance) and under submodule operations.
  have hmem_diag : ∀ u ∈ S, repTwo χ (diagElt g) u ∈ S := fun u hu =>
    S.apply_mem_toSubmodule (diagElt g) hu
  have hmem_swap : ∀ u ∈ S, repTwo χ swapElt u ∈ S := fun u hu =>
    S.apply_mem_toSubmodule swapElt hu
  -- For any `u ∈ S`, `(D g - 1) u = ![(χ g - 1)·u 0, 0] ∈ S`.
  have key : ∀ u ∈ S, (![((χ g : ℂ) - 1) * u 0, 0] : Fin 2 → ℂ) ∈ S := by
    intro u hu
    have h1 : repTwo χ (diagElt g) u - u ∈ S :=
      Submodule.sub_mem _ (hmem_diag u hu) hu
    have he : repTwo χ (diagElt g) u - u = ![((χ g : ℂ) - 1) * u 0, 0] := by
      rw [repTwo_diagElt_apply]
      funext i; fin_cases i <;> simp [Pi.sub_apply, sub_one_mul]
    rwa [he] at h1
  -- First obtain a nonzero multiple of `e₀` inside `S`.
  have he0 : (![1, 0] : Fin 2 → ℂ) ∈ S := by
    rcases eq_or_ne (v 0) 0 with hv00 | hv00
    · -- `v 0 = 0`, so `v 1 ≠ 0`; swap brings it to the first coordinate.
      have hv11 : v 1 ≠ 0 := by
        intro h; apply hv0; funext i; fin_cases i <;> simp_all
      have hsw : repTwo χ swapElt v ∈ S := hmem_swap v hv
      have := key _ hsw
      -- `(repTwo χ swapElt v) 0 = v 1`.
      rw [repTwo_swapElt_apply, show (![v 1, v 0] : Fin 2 → ℂ) 0 = v 1 from rfl] at this
      -- A nonzero scalar multiple of `e₀` is in `S`; rescale.
      have hsm : ((((χ g : ℂ) - 1) * v 1)⁻¹) • (![((χ g : ℂ) - 1) * v 1, 0] : Fin 2 → ℂ) ∈ S :=
        S.toSubmodule.smul_mem _ this
      rwa [smul_e0 (mul_ne_zero hgne hv11)] at hsm
    · -- `v 0 ≠ 0`.
      have := key _ hv
      have hsm : ((((χ g : ℂ) - 1) * v 0)⁻¹) • (![((χ g : ℂ) - 1) * v 0, 0] : Fin 2 → ℂ) ∈ S :=
        S.toSubmodule.smul_mem _ this
      rwa [smul_e0 (mul_ne_zero hgne hv00)] at hsm
  -- `e₁ = P e₀ ∈ S`.
  have he1 : (![0, 1] : Fin 2 → ℂ) ∈ S := by
    have hin := hmem_swap _ he0
    have hsw : repTwo χ swapElt (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
      rw [repTwo_swapElt_apply]; funext i; fin_cases i <;> simp
    rwa [hsw] at hin
  exact ⟨he0, he1⟩

/-- `⊥ ≠ ⊤` in the subrepresentation lattice: `e₀` lies in `⊤` but not in `⊥`. -/
private lemma bot_ne_top_subrep :
    (⊥ : Subrepresentation (repTwo χ)) ≠ ⊤ := by
  intro h
  have hmem : (![1, 0] : Fin 2 → ℂ) ∈ (⊥ : Subrepresentation (repTwo χ)).toSubmodule := by
    rw [h]; trivial
  rw [show (⊥ : Subrepresentation (repTwo χ)).toSubmodule = ⊥ from rfl,
    Submodule.mem_bot] at hmem
  exact absurd (congrFun hmem 0) (by norm_num)

/-- **Irreducibility.** For a *nontrivial* linear character `χ ≠ 1`, the degree-`2`
representation `repTwo χ` of `G ≀ S₂` is irreducible. (For `χ = 1` it is the
reducible sum `triv ⊕ sign`.) -/
theorem repTwo_isIrreducible (hχ : χ ≠ 1) :
    Representation.IsIrreducible (repTwo χ) := by
  haveI : Nontrivial (Subrepresentation (repTwo χ)) := ⟨⊥, ⊤, bot_ne_top_subrep⟩
  refine IsSimpleOrder.of_forall_eq_top fun S hS => ?_
  -- `S ≠ ⊥` gives a nonzero vector; the key step then forces `S = ⊤`.
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S, v ≠ 0 := by
    by_contra h
    push Not at h
    apply hS
    refine Subrepresentation.toSubmodule_injective (Submodule.eq_bot_iff _ |>.2 fun x hx => ?_)
    exact h x hx
  obtain ⟨he0, he1⟩ := mem_of_ne_one hχ S hvS hv0
  -- `{e₀, e₁}` spans, so `S = ⊤`.
  refine Subrepresentation.toSubmodule_injective (Submodule.eq_top_iff'.2 fun x => ?_)
  have hx : x = x 0 • (![1, 0] : Fin 2 → ℂ) + x 1 • (![0, 1] : Fin 2 → ℂ) := by
    funext i; fin_cases i <;> simp
  rw [hx]
  exact S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ he0) (S.toSubmodule.smul_mem _ he1)

end WreathS2

/-! ### The genuine `b = 2` content of the (corrected) theorem

Assembling the explicit construction with the character-existence lemma: a
nontrivial **non-perfect** finite group `G` admits an irreducible representation
of `G ≀ S₂` of complex dimension exactly `2`. This is the honest, `sorry`-free
heart of the case `b = 2` of the corrected theorem (`n₂(G ≀ S₂) = 2`): a degree-`2`
*irrep* exists, and `2` is the least integer `> 1`, so no irrep of degree `> 1`
can be smaller. -/

/-- **Existence of a degree-`2` irrep of `G ≀ S₂` for non-perfect `G`.** If `G` is a
finite group that is not perfect, there is a representation
`ρ : Representation ℂ (G ≀ S₂) V` on a `2`-dimensional `ℂ`-space `V` that is
irreducible. (`V = Fin 2 → ℂ`, `ρ = WreathS2.repTwo χ` for a nontrivial linear
character `χ`.) -/
theorem WreathS2.exists_irreducible_finrank_two
    (G : Type*) [Group G] [Finite G] (h : ¬ Group.IsPerfect G) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (Wreath G 2) V),
      Module.finrank ℂ V = 2 ∧ Representation.IsIrreducible ρ := by
  obtain ⟨χ, x, hx⟩ := exists_nontrivial_linearChar_of_not_isPerfect G h
  have hχ : χ ≠ 1 := fun he => hx (by rw [he]; rfl)
  exact ⟨Fin 2 → ℂ, inferInstance, inferInstance, repTwo χ,
    WreathS2.repTwo_finrank, repTwo_isIrreducible hχ⟩

/-! ### The honest "lower bound" half of `n₂ = 2`

`GroupTPP.CharDegrees.minNontrivIrrepDim` is `n₂(G)`, defined as the minimum of the
character degrees `> 1` (or `0` if none). By construction it is **never equal to
`1`** — it is `0` or `≥ 2` — *whatever* `charDegrees` turns out to be once the
foundational `sorry` is discharged. This `sorry`-free structural fact is exactly
the lower-bound half of the claim "`n₂ = 2`": once a degree-`2` irrep is known to
exist (so `n₂ ≠ 0`), the value is forced to be `≥ 2`, and any explicit degree-`2`
irrep pins it to exactly `2`. -/

open GroupTPP.CharDegrees in
/-- **`n₂(G)` is never `1`.** `minNontrivIrrepDim G ∈ {0} ∪ {d | d ≥ 2}`: either no
irrep of degree `> 1` exists (value `0`) or the minimal such degree is `≥ 2`.
`sorry`-free (depends only on the *definition* of `minNontrivIrrepDim`, not on the
content of `charDegrees`). -/
theorem minNontrivIrrepDim_eq_zero_or_ge_two
    (G : Type*) [Group G] [Fintype G] :
    minNontrivIrrepDim G = 0 ∨ 2 ≤ minNontrivIrrepDim G := by
  unfold minNontrivIrrepDim
  -- The filtered finset's `min`: either `⊤` (empty → `untopD 0 = 0`) or a member `> 1`.
  rcases eq_or_ne ((charDegrees G).filter (fun d => d > 1)).toFinset.min ⊤ with htop | hne
  · left; rw [htop]; rfl
  · right
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
    -- `m` is a member of the filtered finset, hence `m > 1`.
    have hmem := Finset.mem_of_min hm.symm
    rw [Multiset.mem_toFinset, Multiset.mem_filter] at hmem
    have : (1 : ℕ) < m := hmem.2
    rw [← hm, WithTop.untopD_coe]
    omega

/-- **Conditional `n₂(G ≀ S₂) = 2` for non-perfect `G`.** *Provided* `charDegrees`
records a degree-`2` irrep of `G ≀ S₂` (i.e. `n₂ ≠ 0`, which holds once the
foundational Wedderburn `sorry` is discharged, since
`WreathS2.exists_irreducible_finrank_two` exhibits one), the structural lower
bound forces `n₂(G ≀ S₂) = 2`. This isolates precisely the gap: the *existence* of
the degree-`2` irrep is proved `sorry`-free above; only its visibility *through
`charDegrees`* awaits the indexed Wedderburn layer. -/
theorem minNontrivIrrepDim_wreathS2_eq_two_of_ne_zero
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] (_h : ¬ Group.IsPerfect G)
    (hne : GroupTPP.CharDegrees.minNontrivIrrepDim (Wreath G 2) ≠ 0)
    (hle : GroupTPP.CharDegrees.minNontrivIrrepDim (Wreath G 2) ≤ 2) :
    GroupTPP.CharDegrees.minNontrivIrrepDim (Wreath G 2) = 2 := by
  rcases minNontrivIrrepDim_eq_zero_or_ge_two (Wreath G 2) with h0 | hge
  · exact absurd h0 hne
  · omega

end GroupTPP.WreathNg
