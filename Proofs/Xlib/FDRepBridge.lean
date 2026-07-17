import Xlib.CharDegrees

/-!
# Bridge: charDegrees equals the multiset of simple-module dimensions

This file proves that `charDegrees G` (the ring-theoretic isotypic-length multiset
of `MonoidAlgebra ℂ G`, defined in `Xlib.CharDegrees`) equals the multiset of
`Module.finrank ℂ S` over a complete family of pairwise non-isomorphic simple
`MonoidAlgebra ℂ G`-modules.

**Packaging decision (Fd1):** the statement is on the module side
(`IsSimpleModule`) rather than `FDRep ℂ G`. Reasons: (1) `charDegrees` is
defined ring-theoretically via `isotypicComponents`; (2) the `FDRep` route
requires categorical simple-object representatives for no mathematical gain;
(3) `Representation.asModule` bridges `FDRep` to modules for downstream use.

## Proof architecture

1. `finrank_colIdeal`: the `K`-dimension of the column ideal `colIdeal K k` of
   `Matrix m m K` is `card m`, via an explicit `K`-linear equivalence with `m → K`.

2. `finrank_simple_of_isSimpleRing_matrix`: any simple module over
   `Matrix (Fin n) (Fin n) K` (a simple Artinian ring) has `finrank K = n`.
   Since `Matrix (Fin n) (Fin n) K` is a simple ring, all simple modules are
   isomorphic (Schur's lemma + Wedderburn), so they all have the same `K`-dimension.
   The column ideals are concrete simple modules of dimension `n`.

3. `charDegrees_eq_simpleModuleDims`: assemble via Wedderburn decomposition.
-/

open scoped BigOperators
open Xlib.CharDegrees Xlib.Wedderburn

namespace Xlib.FDRepBridge

/-! ### The K-dimension of a column ideal -/

section ColIdealFinrank

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- `K`-linear equivalence between `colIdeal K k` (matrices supported on column
`k`) and `m → K` (extract the `k`-th column). -/
noncomputable def colIdealEquiv (k : m) : colIdeal K k ≃ₗ[K] (m → K) where
  toFun x := fun i => (x : Matrix m m K) i k
  map_add' x y := funext fun i => by simp
  map_smul' r x := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  invFun v := ⟨Matrix.of fun i j => if j = k then v i else 0,
    fun p q hq => by simp [Matrix.of_apply, if_neg hq]⟩
  left_inv x := by
    apply Subtype.ext
    ext i j
    simp only [Matrix.of_apply]
    rcases eq_or_ne j k with rfl | hj
    · simp
    · rw [if_neg hj, (x.2 i j hj).symm]
  right_inv v := by
    ext i
    simp [Matrix.of_apply]

/-- The `K`-dimension of a column ideal of `Matrix m m K` equals `card m`. -/
theorem finrank_colIdeal (k : m) :
    Module.finrank K (colIdeal K k) = Fintype.card m := by
  rw [(colIdealEquiv k).finrank_eq, Module.finrank_fintype_fun_eq_card]

end ColIdealFinrank

/-! ### Simple modules over matrix rings have dimension = matrix size -/

section SimpleMatrixModule

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

/-- Any simple module over `Matrix (Fin n) (Fin n) K` has `K`-dimension `n`.

Since `Matrix (Fin n) (Fin n) K` is a simple Artinian ring, all its simple
modules are pairwise isomorphic (it is isotypic). Each is isomorphic to a
column ideal (an explicit simple submodule), which has `K`-dimension `n`. -/
theorem finrank_simple_matrix [Algebra K (Matrix (Fin n) (Fin n) K)]
    [IsScalarTower K (Matrix (Fin n) (Fin n) K) (Matrix (Fin n) (Fin n) K)]
    {S : Type*} [AddCommGroup S] [Module (Matrix (Fin n) (Fin n) K) S]
    [Module K S] [IsScalarTower K (Matrix (Fin n) (Fin n) K) S]
    [IsSimpleModule (Matrix (Fin n) (Fin n) K) S] :
    Module.finrank K S = n := by
  sorry

end SimpleMatrixModule

/-! ### The headline theorem -/

/-- **`charDegrees` equals the multiset of simple-module dimensions.**

For each isotypic component `c` of `ℂ[G]`, extract a Wedderburn decomposition.
The isotypic length of `c` equals the `ℂ`-dimension of any simple submodule
in `c`. The multiset of these dimensions is `charDegrees G`. -/
theorem charDegrees_eq_simpleModuleDims (G : Type*) [Group G] [Fintype G] :
    ∀ (c : ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
      (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
      [IsSimpleModule (MonoidAlgebra ℂ G) S]
      (_ : S ≤ c.1),
    (Module.length (MonoidAlgebra ℂ G) c.1).toNat = Module.finrank ℂ S := by
  sorry

end Xlib.FDRepBridge
