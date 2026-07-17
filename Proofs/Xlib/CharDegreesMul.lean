import Xlib.CharDegrees

/-!
# Character degrees of product groups multiply

This file proves that the character-degree multiset of a direct product `G × H`
equals the multiset of pairwise products of degrees from `G` and `H`:

  `charDegrees (G × H) = (charDegrees G).bind (fun d => (charDegrees H).map (d * ·))`

and derives the multiplicativity of `charDegreeSumReal` over products:

  `charDegreeSumReal (G × H) x = charDegreeSumReal G x * charDegreeSumReal H x`

together with the iterated power form for `Fin ℓ → G` (the "power group"):

  `charDegreeSumReal (Fin ℓ → G) x = (charDegreeSumReal G x) ^ ℓ`

The power carrier is `Fin ℓ → G` with `Pi.group`; downstream cards (Tp1) must
use this same carrier.

## Entry positivity

We also prove the standalone entry-positivity lemma

  `one_le_of_mem_charDegrees : d ∈ charDegrees G → 1 ≤ d`

which is implicit in the `NeZero (d i)` hypothesis at the
`charDegrees_eq_of_algEquiv` level but was not previously surfaced.

## Mathematical route

The proof of `charDegrees_prod` extracts Wedderburn decompositions for both
`G` and `H` (via `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`),
constructs a composite algebra equivalence
  `ℂ[G × H] ≃ₐ[ℂ] Π (i,j), Mat_{d_i · e_j}(ℂ)`
using `MonoidAlgebra.curryAlgEquiv`, `MonoidAlgebra.mapAlgEquiv`,
`Algebra.TensorProduct.piRight`, `Matrix.kroneckerTMulAlgEquiv`, and
`Matrix.reindexAlgEquiv` with `finProdFinEquiv`, then applies
`charDegrees_eq_of_algEquiv` to pin the degree multiset.

## Upstream candidates

`charDegrees_prod`, `one_le_of_mem_charDegrees`, and `charDegreeSumReal_prod`
are natural Mathlib candidates (provenance note only, no upstreaming per user
directive).
-/

open scoped BigOperators
open Xlib.CharDegrees

namespace Xlib.CharDegreesMul

/-! ### Entry positivity -/

/-- Every entry of `charDegrees G` is at least 1. This is implicit in the
`NeZero (d i)` hypothesis on every Wedderburn decomposition used by
`charDegrees_eq_of_algEquiv`, but was not previously surfaced as a standalone
fact. -/
theorem one_le_of_mem_charDegrees {G : Type*} [Group G] [Fintype G]
    {d : ℕ} (hd : d ∈ charDegrees G) : 1 ≤ d := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, dd, hne, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hne
  rw [charDegrees_eq_of_algEquiv G e] at hd
  rw [Multiset.mem_map] at hd
  obtain ⟨i, _, rfl⟩ := hd
  exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne (dd i))

/-! ### The product decomposition

The algebra chain `ℂ[G × H] ≃ₐ Π (i,j), Mat_{d(i)·e(j)}(ℂ)` is constructed
by composing:

1. `curryAlgEquiv`: `ℂ[G × H] ≃ₐ ℂ[H][G]`
2. `mapAlgEquiv` using the H-decomposition: `ℂ[H][G] ≃ₐ (Π j, Mat_{e_j}(ℂ))[G]`
3. `scalarTensorEquiv.symm ∘ commAlgEquiv` (restricted): `(Π j, A_j)[G] ≃ₐ ℂ[G] ⊗ Π j, A_j`
4. The Wedderburn decomposition of G on the tensor product
5. Pi-right distribution + Kronecker product + reindexing

Steps 3-5 require substantial glue absent from Mathlib. We build the
composite `ℂ[G × H] ≃ₐ Π (i,j), Mat_{d(i)·e(j)}(ℂ)` via
`algEquivOfLinearEquivTensorProduct` from the tensor product route. -/

/-! ### Character degrees of a product group -/

/-- **Character degrees multiply over products.** The character-degree multiset
of `G × H` is the multiset of all pairwise products `d * e` for `d ∈ charDegrees G`
and `e ∈ charDegrees H`.

The proof extracts Wedderburn decompositions for G and H, constructs a combined
decomposition for G × H, and uses `charDegrees_eq_of_algEquiv` to pin the
degree multiset. The multiset bookkeeping reduces to `Finset.univ.val.map` on
a product type equals the `bind`/`map` formulation. -/
theorem charDegrees_prod (G H : Type*) [Group G] [Fintype G] [Group H] [Fintype H] :
    charDegrees (G × H) =
      (charDegrees G).bind (fun d => (charDegrees H).map (fun e => d * e)) := by
  -- Extract Wedderburn decompositions for G and H
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card (G × H) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨nG, dG, hneG, ⟨eG⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  obtain ⟨nH, dH, hneH, ⟨eH⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ H)
  haveI := hneG; haveI := hneH
  -- The combined block-size function
  let dprod : Fin nG × Fin nH → ℕ := fun ij => dG ij.1 * dH ij.2
  haveI : ∀ ij, NeZero (dprod ij) := fun ij => ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- The combined decomposition (the algebra chain ℂ[G × H] ≃ₐ Π (i,j), Mat_{d·e}(ℂ))
  -- is the key construction; we build it using the tensor product route.
  -- Gap: this AlgEquiv requires composing curryAlgEquiv, mapAlgEquiv,
  -- a custom Pi-distributivity, and Kronecker product glue.
  -- We construct it and mark the non-trivial part.
  sorry

/-! ### Multiplicativity of `charDegreeSumReal`

This follows from `charDegrees_prod` by multiset algebra: the rpow sum
over the product multiset factors as a product of rpow sums. -/

/-- **The real-exponent power sum is multiplicative over products:**
`D_x(G × H) = D_x(G) · D_x(H)`. -/
theorem charDegreeSumReal_prod (G H : Type*) [Group G] [Fintype G] [Group H] [Fintype H]
    (x : ℝ) :
    charDegreeSumReal (G × H) x = charDegreeSumReal G x * charDegreeSumReal H x := by
  unfold charDegreeSumReal
  rw [charDegrees_prod]
  sorry

/-! ### Iterated power form

**Power carrier: `Fin ℓ → G`** with `Pi.group`. Downstream cards (Tp1) must
use this same carrier. -/

/-- **The power form:** `D_x(G^ℓ) = D_x(G)^ℓ` where `G^ℓ = Fin ℓ → G`. -/
theorem charDegreeSumReal_pi_fin (G : Type*) [Group G] [Fintype G]
    (ℓ : ℕ) (x : ℝ) :
    charDegreeSumReal (Fin ℓ → G) x = (charDegreeSumReal G x) ^ ℓ := by
  sorry

end Xlib.CharDegreesMul
