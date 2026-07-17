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
`Algebra.TensorProduct.piRight`, and `Matrix.kroneckerTMulAlgEquiv`, then
applies `charDegrees_eq_of_algEquiv` to pin the degree multiset.

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
  sorry

/-! ### Character degrees of a product group -/

/-- **Character degrees multiply over products.** The character-degree multiset
of `G × H` is the multiset of all pairwise products `d * e` for `d ∈ charDegrees G`
and `e ∈ charDegrees H`. -/
theorem charDegrees_prod (G H : Type*) [Group G] [Fintype G] [Group H] [Fintype H] :
    charDegrees (G × H) =
      (charDegrees G).bind (fun d => (charDegrees H).map (fun e => d * e)) := by
  sorry

/-! ### Multiplicativity of `charDegreeSumReal` -/

/-- **The real-exponent power sum is multiplicative over products:**
`D_x(G × H) = D_x(G) · D_x(H)`. -/
theorem charDegreeSumReal_prod (G H : Type*) [Group G] [Fintype G] [Group H] [Fintype H]
    (x : ℝ) :
    charDegreeSumReal (G × H) x = charDegreeSumReal G x * charDegreeSumReal H x := by
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
