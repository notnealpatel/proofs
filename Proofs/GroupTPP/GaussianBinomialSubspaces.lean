/-
# Gaussian-binomial count of `k`-dimensional subspaces of `F_q^n`

## Source (classical)

* J. Goldman and G.-C. Rota, "On the foundations of combinatorial theory IV:
  finite vector spaces and Eulerian generating functions", Stud. Appl. Math.
  49 (1970), 239–258.
* R. P. Stanley, *Enumerative Combinatorics*, Vol. 1 (2nd ed.), Prop. 1.7.2.
* R. Lidl and H. Niederreiter, *Finite Fields*.

## Informal statement (as recorded in the target spec)

> For a finite field K with q elements and k <= n, the number of k-dimensional
> subspaces of K^n equals the Gaussian binomial
> [n choose k]_q = prod_{i<k} (q^n - q^i) / prod_{i<k} (q^k - q^i).

Date: 2026-10-21.

## Formalization notes

* The count is stated multiplied out, `#{U} * ∏_{i<k} (q^k - q^i) =
  ∏_{i<k} (q^n - q^i)`, so no division appears; a quotient form is derived
  afterwards together with the positivity of the denominator.  The natural
  subtractions `q ^ k - q ^ i` are never truncated because `i < k` and `1 < q`
  (proved below as `pow_sub_pow_pos`).
* The result is proved for an arbitrary finite `K`-vector space `V` with
  `finrank K V = n`, then specialised to `V = Fin n → K`.
* Mathlib check (2026-10-21, `leandoc` "number of subspaces finite field
  finrank card", "Grassmannian card finite field", "q-binomial coefficient",
  "card submodule finrank eq"; grep for `gaussBinom|qBinom|Gaussian binomial`):
  no subspace count.  The ingredient `card_linearIndependent`
  (`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean`) counts
  linearly independent `k`-tuples.
* Proof: the map `s ↦ span (range s)` from linearly independent `k`-tuples to
  `k`-dimensional subspaces has, over each `U`, fibre equivalent to the
  linearly independent `k`-tuples of `U`, of which there are
  `∏_{i<k} (q^k - q^i)`.
-/
import Mathlib
import GroupTPP.ExtraspecialLattice

set_option autoImplicit false

namespace GroupTPP.GaussianBinomialSubspaces

open Module

section General

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- The span map: a linearly independent `k`-tuple goes to the `k`-dimensional
subspace it spans. -/
noncomputable def spanMap (k : ℕ) :
    { s : Fin k → V // LinearIndependent K s } → { U : Submodule K V // finrank K U = k } :=
  fun s => ⟨Submodule.span K (Set.range s.1), by
    rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The fibre of `spanMap` over a `k`-dimensional subspace `U` is equivalent to
the linearly independent `k`-tuples of vectors of `U`. -/
noncomputable def fiberEquiv (k : ℕ) (U : { U : Submodule K V // finrank K U = k }) :
    { s // spanMap (K := K) (V := V) k s = U } ≃
      { t : Fin k → U.1 // LinearIndependent K t } where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have hU : (spanMap (K := K) (V := V) k s.1).1 = U.1 := congrArg Subtype.val s.2
      rw [← hU]
      exact Submodule.subset_span (Set.mem_range_self i)⟩, by
      apply LinearIndependent.of_comp U.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨U.1.subtype ∘ t.1, t.2.map' U.1.subtype (Submodule.ker_subtype U.1)⟩, by
      have hli : LinearIndependent K (U.1.subtype ∘ t.1) :=
        t.2.map' U.1.subtype (Submodule.ker_subtype U.1)
      apply Subtype.ext
      show Submodule.span K (Set.range (U.1.subtype ∘ t.1)) = U.1
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [finrank_span_eq_card hli, Fintype.card_fin, U.2]⟩
  left_inv s := by
    rfl
  right_inv t := by
    rfl

/-- Each fibre of `spanMap` has `∏_{i<k} (q^k - q^i)` elements: the number of
ordered bases of a `k`-dimensional space over `K`. -/
theorem card_fiber (k : ℕ) (U : { U : Submodule K V // finrank K U = k }) :
    Nat.card { s // spanMap (K := K) (V := V) k s = U } =
      ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) := by
  rw [Nat.card_congr (fiberEquiv k U), card_linearIndependent U.2.ge, U.2]

/-- **Gaussian-binomial count, multiplied out.**  If `V` is a finite vector
space of dimension `n` over a finite field `K` with `q` elements and `k ≤ n`,
then `#{k-dimensional subspaces of V} * ∏_{i<k} (q^k - q^i) =
∏_{i<k} (q^n - q^i)`. -/
theorem card_dimSubspaces_mul {n k : ℕ} (hn : finrank K V = n) (hk : k ≤ n) :
    Nat.card { U : Submodule K V // finrank K U = k } *
        ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin k, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
  classical
  letI : Fintype { U : Submodule K V // finrank K U = k } := Fintype.ofFinite _
  have hli : Nat.card { s : Fin k → V // LinearIndependent K s } =
      ∏ i : Fin k, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) := by
    rw [card_linearIndependent (hn ▸ hk), hn]
  have hsum : Nat.card { s : Fin k → V // LinearIndependent K s } =
      ∑ U : { U : Submodule K V // finrank K U = k },
        Nat.card { s // spanMap (K := K) (V := V) k s = U } := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (K := K) (V := V) k)),
      Nat.card_sigma]
  rw [← hli, hsum, Finset.sum_congr rfl (fun U _ => card_fiber k U), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- Each factor `q^k - q^i` with `i < k` of the Gaussian-binomial denominator
is positive, so the natural subtraction is not truncated. -/
theorem pow_sub_pow_pos {k i : ℕ} (hi : i < k) :
    0 < Fintype.card K ^ k - Fintype.card K ^ i := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq hi)

/-- The Gaussian-binomial denominator `∏_{i<k} (q^k - q^i)` is positive. -/
theorem prod_pow_sub_pow_pos (k : ℕ) :
    0 < ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) :=
  Finset.prod_pos fun i _ => pow_sub_pow_pos (K := K) i.2

/-- **Gaussian-binomial count, quotient form.**  For a finite vector space `V`
of dimension `n` over a finite field with `q` elements and `k ≤ n`, the number
of `k`-dimensional subspaces equals
`∏_{i<k} (q^n - q^i) / ∏_{i<k} (q^k - q^i)` (the division is exact). -/
theorem card_dimSubspaces_eq_div {n k : ℕ} (hn : finrank K V = n) (hk : k ≤ n) :
    Nat.card { U : Submodule K V // finrank K U = k } =
      (∏ i : Fin k, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ))) /
        ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) := by
  rw [← card_dimSubspaces_mul hn hk,
    Nat.mul_div_cancel _ (prod_pow_sub_pow_pos (K := K) k)]

end General

section Coordinate

variable (K : Type*) [Field K] [Fintype K]

/-- **Gaussian-binomial count of subspaces of `K^n`** (Goldman–Rota 1970;
Stanley, EC1 Prop. 1.7.2), multiplied out: for a finite field `K` with `q`
elements and `k ≤ n`, `#{k-dimensional subspaces of K^n} * ∏_{i<k} (q^k - q^i)
= ∏_{i<k} (q^n - q^i)`. -/
theorem card_subspaces_fin_mul {n k : ℕ} (hk : k ≤ n) :
    Nat.card { U : Submodule K (Fin n → K) // finrank K U = k } *
        ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin k, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) :=
  card_dimSubspaces_mul (Module.finrank_fin_fun K) hk

/-- **Gaussian-binomial count of subspaces of `K^n`**, quotient form: for a
finite field `K` with `q` elements and `k ≤ n`, the number of `k`-dimensional
subspaces of `K^n` is `[n choose k]_q = ∏_{i<k} (q^n - q^i) / ∏_{i<k} (q^k - q^i)`,
the division being exact. -/
theorem card_subspaces_fin_eq_div {n k : ℕ} (hk : k ≤ n) :
    Nat.card { U : Submodule K (Fin n → K) // finrank K U = k } =
      (∏ i : Fin k, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ))) /
        ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) :=
  card_dimSubspaces_eq_div (Module.finrank_fin_fun K) hk

end Coordinate

/-- Closed form for the repository's `ExtraspecialLattice.fixedDimSubspaces`:
over a finite field with `q` elements, a finite space of dimension `n` has
`#{m-dimensional subspaces} * ∏_{i<m} (q^m - q^i) = ∏_{i<m} (q^n - q^i)`
whenever `m ≤ n`. -/
theorem card_fixedDimSubspaces_mul {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [Finite V] {n m : ℕ} (hn : finrank K V = n) (hm : m ≤ n) :
    Nat.card (ExtraspecialLattice.fixedDimSubspaces K V m) *
        ∏ i : Fin m, (Fintype.card K ^ m - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin m, (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ)) :=
  card_dimSubspaces_mul hn hm

/-! ## Sanity checks -/

/-- Non-vacuity of the hypotheses: `ZMod 2` is a finite field and `2 ≤ 4`. -/
example : Nat.card { U : Submodule (ZMod 2) (Fin 4 → ZMod 2) //
    finrank (ZMod 2) U = 2 } = 35 := by
  rw [card_subspaces_fin_eq_div (ZMod 2) (by norm_num : 2 ≤ 4), ZMod.card]
  decide

/-- Over `ZMod 3`, `K^3` has `13` lines (`[3 choose 1]_3 = 13`). -/
example : Nat.card { U : Submodule (ZMod 3) (Fin 3 → ZMod 3) //
    finrank (ZMod 3) U = 1 } = 13 := by
  rw [card_subspaces_fin_eq_div (ZMod 3) (by norm_num : 1 ≤ 3), ZMod.card]
  decide

end GroupTPP.GaussianBinomialSubspaces
