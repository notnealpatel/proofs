import Mathlib

/-!
# One multiply-add shear cannot clean the ancilla in reversible EC point addition

Context (secp256k1, but nothing here is prime-specific). For a fixed point
`P = (a, b)` and a varying `Q`, the affine group law reduces — after the slope
`λ` is in hand — to the "remaining transformation"

  `(c, λ) ↦ (a - c, c·λ - b) = (X, Y)`,  where `c = a - X`.

The only nonlinear primitive is the **reversible multiply-add shear**
`M (u, v, w) = (u, v, w + u·v)` on `k³`, with affine bijections otherwise free.
This is the `k`-algebraic analogue of a Toffoli gate; `M` is the single
"nonscalar multiplication" in the arithmetic-circuit cost model.

This file formalises the folklore obstruction (a Bennett compute–uncompute
statement / a baby multiplicative-complexity lower bound):

* `Xlib.ShearAddition.shear` — the primitive `M` as an `Equiv` (it is reversible,
  with inverse `w ↦ w - u·v`).
* `Xlib.ShearAddition.singleShear` — the concrete one-shear realisation
  `(c, λ, 0) ↦ (X, Y, λ)`: it *does* place the answer with a single `M` using the
  initially-zero register as accumulator (conditions 1–2 of the design), but the
  third register is left holding `λ`.
* `Xlib.ShearAddition.no_reversible_clean_shear_addition` — **the impossibility
  (condition 3)**: *no* bijection of `k³` can restrict to
  `(c, λ, 0) ↦ (a - c, c·λ - b, 0)` on the whole input plane, because that target
  collapses the fibre `c = 0` (all `λ` land on `(a, -b)`) and hence is not
  injective. Since every composite `A₂ ∘ M ∘ A₁` of a shear with affine (indeed
  arbitrary) bijections is itself a bijection, a single shear can never return the
  ancilla to zero.  Recorded as `single_shear_cannot_clean`.
* `Xlib.ShearAddition.ancilla_carries_lambda` — **the invariant**: any injective
  `F` that outputs the correct `(X, Y)` in the first two registers must have a
  third register that is injective in `λ` on the fibre `c = 0`; the ancilla
  necessarily carries `λ` (in particular it cannot be `0`).  This is exactly the
  garbage that a clean circuit must uncompute — matching the quantum-ECC counts of
  Roetteler et al. and Häner et al., where the slope is computed *and* uncomputed.
* `Xlib.ShearAddition.shear_comp_normal_form` — **the rank ≤ 1 normal form**: any
  `A₂ ∘ M ∘ A₁` (affine `Aᵢ`) equals an affine map plus a *single* product of two
  affine forms times a fixed vector `ℓ`; its quadratic part has "rank ≤ 1". Hence
  any target whose quadratic part has rank ≥ 2 needs ≥ 2 shears.
* `Xlib.ShearAddition.shearComp` / `shearComp_bijective_and_normal_form` — **payload
  item (1) in full**: for affine *bijections* `Aᵢ x = Lᵢ x + tᵢ` (`Lᵢ` linear equivs),
  the composite `F = A₂ ∘ M ∘ A₁` is packaged as an `Equiv` (so it *is a bijection*)
  and simultaneously carries the rank ≤ 1 normal form.

## Grounding

`Xlib.ShearAdditionEC` proves that on any Weierstrass curve with
`a₁ = a₂ = a₃ = 0` (secp256k1 in particular) the map `(c, λ) ↦ (a - c, c·λ - b)`
studied here **is** Mathlib's verified group law on the chord locus
(`some_add_some`, `singleShear_computes_add`), and that the exceptional fibre
`c = 0` is exactly `P + Q = -P`, i.e. `Q = -(2 • P)`
(`c_eq_zero_iff_add_eq_neg`, `c_eq_zero_iff_eq_neg_two_smul`).
`Xlib.ShearCircuit` generalises the one-shear model to circuits of `s` shears
(degree `≤ 2^s`), and `Xlib.ShearInversionLB` derives the flagship consequence:
clean modular inversion — the step that builds `λ` — needs `≥ ⌈log₂(p-2)⌉`
shears.

## References

* C. H. Bennett, *Logical reversibility of computation*, IBM J. Res. Dev. 17 (1973).
* M. Roetteler, M. Naehrig, K. Svore, K. Lauter, *Quantum resource estimates for
  computing elliptic curve discrete logarithms*, ASIACRYPT 2017, arXiv:1706.06752
  (the slope is computed and uncomputed → 4 modular inversions per addition).
* T. Häner, S. Jaques, M. Naehrig, M. Roetteler, M. Soeken, *Improved quantum
  circuits for elliptic curve discrete logarithms*, PQCrypto 2020, arXiv:2001.09580.
-/

namespace Xlib.ShearAddition

variable {k : Type*} [Field k]

/-- The reversible multiply-add **shear** `M (u, v, w) = (u, v, w + u·v)` on `k³`,
packaged as an `Equiv`; its inverse is `w ↦ w - u·v`. This is the single permitted
nonlinear primitive. -/
def shear : (k × k × k) ≃ (k × k × k) where
  toFun x := (x.1, x.2.1, x.2.2 + x.1 * x.2.1)
  invFun y := (y.1, y.2.1, y.2.2 - y.1 * y.2.1)
  left_inv := fun x => by
    obtain ⟨u, v, w⟩ := x
    refine Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨rfl, ?_⟩⟩
    show w + u * v - u * v = w
    ring
  right_inv := fun y => by
    obtain ⟨u, v, w⟩ := y
    refine Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨rfl, ?_⟩⟩
    show w - u * v + u * v = w
    ring

@[simp] lemma shear_apply (x : k × k × k) :
    shear x = (x.1, x.2.1, x.2.2 + x.1 * x.2.1) := rfl

/-- Scaling the third basis vector. -/
lemma smul_e3 (r : k) : r • ((0, 0, 1) : k × k × k) = (0, 0, r) := by
  simp

/-- The shear as "identity plus a rank-one quadratic bump": the only nonlinearity is
the single product `u·v`, deposited along the third coordinate. -/
lemma shear_eq_add_smul (y : k × k × k) :
    shear y = y + (y.1 * y.2.1) • ((0, 0, 1) : k × k × k) := by
  obtain ⟨u, v, w⟩ := y
  rw [shear_apply]
  dsimp only
  rw [smul_e3]
  simp only [Prod.mk_add_mk, add_zero]

/-- **Normal form / rank ≤ 1 quadratic part.** Any composite `A₂ ∘ M ∘ A₁` of the
shear with affine maps `Aᵢ x = Lᵢ x + tᵢ` is an affine map `L · + t` plus a *single*
product of two affine forms `(σ₁· + d₁)` and `(σ₂· + d₂)`, scaled by a fixed vector
`ℓ`. So one nonscalar multiplication yields a quadratic part of rank ≤ 1; a target
whose quadratic part has rank ≥ 2 provably needs ≥ 2 shears.

Note the EC-step target itself never triggers this criterion: its quadratic part
is the single product `c·λ` (product-rank 1), which is exactly why `singleShear`
achieves it in one shear. A genuine rank-2 separation witness is `X₀X₁ + X₂X₃`
(`Xlib.ShearQuadraticRank.not_isSumOfProducts_one_quad` /
`two_le_shearCount_of_quad`). -/
theorem shear_comp_normal_form
    (L₁ L₂ : (k × k × k) →ₗ[k] (k × k × k)) (t₁ t₂ : k × k × k) :
    ∃ (L : (k × k × k) →ₗ[k] (k × k × k)) (t ℓ : k × k × k)
      (s₁ s₂ : (k × k × k) → k) (σ₁ σ₂ : (k × k × k) →ₗ[k] k) (d₁ d₂ : k),
      (∀ x, L₂ (shear (L₁ x + t₁)) + t₂ = (L x + t) + (s₁ x * s₂ x) • ℓ) ∧
      (∀ x, s₁ x = σ₁ x + d₁) ∧ (∀ x, s₂ x = σ₂ x + d₂) := by
  refine ⟨L₂ ∘ₗ L₁, L₂ t₁ + t₂, L₂ (0, 0, 1),
          (fun x => (L₁ x + t₁).1), (fun x => (L₁ x + t₁).2.1),
          LinearMap.fst k k (k × k) ∘ₗ L₁,
          LinearMap.fst k k k ∘ₗ LinearMap.snd k k (k × k) ∘ₗ L₁,
          t₁.1, t₁.2.1, ?_, ?_, ?_⟩
  · intro x
    rw [shear_eq_add_smul, map_add, map_smul, map_add]
    simp only [LinearMap.comp_apply]
    abel
  · intro x; rfl
  · intro x; rfl

/-- An affine bijection `x ↦ L x + t` of `k³` (with `L` a linear equivalence), as an
`Equiv`. -/
def affineEquiv (L : (k × k × k) ≃ₗ[k] (k × k × k)) (t : k × k × k) :
    (k × k × k) ≃ (k × k × k) where
  toFun x := L x + t
  invFun y := L.symm (y - t)
  left_inv x := by simp
  right_inv y := by simp

/-- The single-shear composite `A₂ ∘ M ∘ A₁` framed by two affine bijections
`Aᵢ x = Lᵢ x + tᵢ`, packaged as an `Equiv` — so it is a bijection by construction. -/
def shearComp (L₁ L₂ : (k × k × k) ≃ₗ[k] (k × k × k)) (t₁ t₂ : k × k × k) :
    (k × k × k) ≃ (k × k × k) :=
  (affineEquiv L₁ t₁).trans (shear.trans (affineEquiv L₂ t₂))

@[simp] lemma shearComp_apply (L₁ L₂ : (k × k × k) ≃ₗ[k] (k × k × k))
    (t₁ t₂ x : k × k × k) :
    shearComp L₁ L₂ t₁ t₂ x = L₂ (shear (L₁ x + t₁)) + t₂ := rfl

/-- **Payload lemma (1), in full.** For affine bijections `Aᵢ x = Lᵢ x + tᵢ`, the
single-shear composite `F = A₂ ∘ M ∘ A₁`:

* **is a bijection** of `k³` (`Function.Bijective`), and
* has a **rank ≤ 1 quadratic part**: `F` is an affine map `L · + t` plus a single
  product of two affine forms `(σ₁· + d₁)(σ₂· + d₂)` scaled by a fixed vector `ℓ`.

One nonscalar multiplication buys exactly one rank of nonlinearity; any target whose
quadratic part has rank ≥ 2 needs ≥ 2 shears. (Not the EC step itself — its
quadratic part `c·λ` has product-rank 1; see `Xlib.ShearQuadraticRank` for a
genuine separation, `X₀X₁ + X₂X₃`.) -/
theorem shearComp_bijective_and_normal_form
    (L₁ L₂ : (k × k × k) ≃ₗ[k] (k × k × k)) (t₁ t₂ : k × k × k) :
    Function.Bijective (shearComp L₁ L₂ t₁ t₂) ∧
      ∃ (L : (k × k × k) →ₗ[k] (k × k × k)) (t ℓ : k × k × k)
        (s₁ s₂ : (k × k × k) → k) (σ₁ σ₂ : (k × k × k) →ₗ[k] k) (d₁ d₂ : k),
        (∀ x, shearComp L₁ L₂ t₁ t₂ x = (L x + t) + (s₁ x * s₂ x) • ℓ) ∧
        (∀ x, s₁ x = σ₁ x + d₁) ∧ (∀ x, s₂ x = σ₂ x + d₂) := by
  refine ⟨(shearComp L₁ L₂ t₁ t₂).bijective, ?_⟩
  obtain ⟨L, t, ℓ, s₁, s₂, σ₁, σ₂, d₁, d₂, hF, hs₁, hs₂⟩ :=
    shear_comp_normal_form (L₁ : (k × k × k) →ₗ[k] (k × k × k))
      (L₂ : (k × k × k) →ₗ[k] (k × k × k)) t₁ t₂
  refine ⟨L, t, ℓ, s₁, s₂, σ₁, σ₂, d₁, d₂, ?_, hs₁, hs₂⟩
  intro x
  rw [shearComp_apply, ← hF x]
  simp

variable (a b : k)

/-- The post-shear affine bijection `(u, v, w) ↦ (a - u, w - b, v)`, used to route the
shear output into `(X, Y, ancilla)`. -/
def addWrap : (k × k × k) ≃ (k × k × k) where
  toFun p := (a - p.1, p.2.2 - b, p.2.1)
  invFun q := (a - q.1, q.2.2, q.2.1 + b)
  left_inv := fun p => by
    obtain ⟨u, v, w⟩ := p
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨rfl, ?_⟩⟩
    · show a - (a - u) = u
      ring
    · show w - b + b = w
      ring
  right_inv := fun q => by
    obtain ⟨x, y, z⟩ := q
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, rfl⟩⟩
    · show a - (a - x) = x
      ring
    · show y + b - b = y
      ring

/-- The concrete **single-shear realisation** of the point-addition step:
`A₂ ∘ M`. On input `(c, λ, w)` it returns `(a - c, (w + c·λ) - b, λ)`.

Input-model caveat: the input `c = a - X = 2a + x - λ²` is quadratic in `λ`,
so the reparametrization `(x, λ) ↦ (c, λ)` is *not* affine — forming `c`
from `(x, λ)` costs one further shear (the `λ·λ` square). The impossibility
and lower-bound results hold a fortiori (granting `c` for free only
strengthens them), but the one-shear *achievability* is specific to this
c-given input model, consistent with the classical two-multiplication count
for the post-slope step. -/
def singleShear : (k × k × k) ≃ (k × k × k) := shear.trans (addWrap a b)

@[simp] lemma singleShear_apply (c lam w : k) :
    singleShear a b (c, lam, w) = (a - c, (w + c * lam) - b, lam) := rfl

/-- With the third register initialised to `0` (condition 2), a **single** shear places
the answer `(X, Y) = (a - c, c·λ - b)` in the first two registers (condition 1) — but
the third register is left holding `λ`, *not* `0`. -/
lemma singleShear_zero (c lam : k) :
    singleShear a b (c, lam, 0) = (a - c, c * lam - b, lam) := by
  rw [singleShear_apply, zero_add]

/-- **Impossibility (condition 3).** No bijection of `k³` can implement the clean
addition step `(c, λ, 0) ↦ (a - c, c·λ - b, 0)` for all `(c, λ)`: at `c = 0` every `λ`
maps to `(a, -b, 0)`, so the target is not injective. In particular no composite of the
shear with affine (or any reversible) pre and post processing can return the ancilla to
zero with a single multiply-add. -/
theorem no_reversible_clean_shear_addition
    (F : k × k × k → k × k × k) (hF : Function.Injective F)
    (hspec : ∀ c lam : k, F (c, lam, 0) = (a - c, c * lam - b, 0)) : False := by
  have hEq : F (0, 0, 0) = F (0, 1, 0) := by
    rw [hspec 0 0, hspec 0 1]; simp
  have h := hF hEq
  exact absurd (congrArg (fun p : k × k × k => p.2.1) h) zero_ne_one

/-- Specialisation to a single shear framed by two reversible maps `A₁, A₂` (affine
bijections are a special case): still impossible. -/
theorem single_shear_cannot_clean
    (A₁ A₂ : (k × k × k) ≃ (k × k × k))
    (hspec : ∀ c lam : k, A₂ (shear (A₁ (c, lam, 0))) = (a - c, c * lam - b, 0)) :
    False := by
  refine no_reversible_clean_shear_addition a b (fun x => A₂ (shear (A₁ x))) ?_ hspec
  exact A₂.injective.comp (shear.injective.comp A₁.injective)

/-- **The invariant: the ancilla necessarily carries `λ`.** If an injective `F` outputs
the correct first two coordinates `(X, Y) = (a - c, c·λ - b)`, then on the exceptional
fibre `c = 0` its third coordinate is an injective function of `λ`. So the ancilla
cannot be constant there — in particular it cannot be `0` — and clearing it requires
recovering `λ`, i.e. a second nonlinear step (the modular inverse that built `λ`). -/
theorem ancilla_carries_lambda
    (F : k × k × k → k × k × k) (hF : Function.Injective F)
    (hX : ∀ c lam : k, (F (c, lam, 0)).1 = a - c)
    (hY : ∀ c lam : k, (F (c, lam, 0)).2.1 = c * lam - b) :
    Function.Injective (fun lam : k => (F (0, lam, 0)).2.2) := by
  intro l1 l2 hl
  have key : F (0, l1, 0) = F (0, l2, 0) := by
    have e1 : (F (0, l1, 0)).1 = (F (0, l2, 0)).1 := by rw [hX 0 l1, hX 0 l2]
    have e2 : (F (0, l1, 0)).2.1 = (F (0, l2, 0)).2.1 := by rw [hY 0 l1, hY 0 l2]; ring
    exact Prod.ext_iff.mpr ⟨e1, Prod.ext_iff.mpr ⟨e2, hl⟩⟩
  have h := hF key
  simpa using congrArg (fun p : k × k × k => p.2.1) h

end Xlib.ShearAddition
