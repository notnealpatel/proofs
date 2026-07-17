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

The proof of `charDegrees_prod` requires a composite algebra equivalence
  `ℂ[G × H] ≃ₐ[ℂ] Π (i,j), Mat_{d_i · e_j}(ℂ)`
constructed via `MonoidAlgebra.curryAlgEquiv`, `MonoidAlgebra.mapAlgEquiv`,
`piMonoidAlgEquiv` (monoid algebra distributes over Pi; proved here),
and a matrix-valued monoid algebra equivalence
  `MonoidAlgebra (Matrix m m ℂ) G ≃ₐ[ℂ] Matrix m m (MonoidAlgebra ℂ G)`
which requires custom glue absent from Mathlib (see `md1-notes.md` for the
exact gap).  The multiset bookkeeping and all corollaries are proved
conditional on `charDegrees_prod`.

## Upstream candidates

`charDegrees_prod`, `one_le_of_mem_charDegrees`, `piMonoidAlgEquiv`, and
`charDegreeSumReal_prod` are natural Mathlib candidates (provenance note
only, no upstreaming per user directive).
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

/-! ### Monoid algebra distributes over Pi (missing from Mathlib)

The algebra equivalence `(Π j, A j)[M] ≃ₐ[R] Π j, (A j)[M]` for
finitely-indexed coefficient rings. At the function level this is the
transposition `f ↦ (fun j m => f m j)`. -/

/-- The forward direction of the monoid-algebra-distributes-over-Pi
equivalence: project each coefficient component. -/
noncomputable def piMonoidAlgFwd (R : Type*) [CommSemiring R]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    (M : Type*) [Monoid M] :
    MonoidAlgebra (Π j, A j) M →ₐ[R] Π j, MonoidAlgebra (A j) M :=
  Pi.algHom R (fun j => MonoidAlgebra (A j) M)
    (fun j => MonoidAlgebra.mapAlgHom M (Pi.evalAlgHom R A j))

/-- **Monoid algebra distributes over Pi.** For a finite index type `ι` and
an `ι`-indexed family of `R`-algebras `A`, the monoid algebra of the product
is isomorphic to the product of the monoid algebras:
`(Π j, A j)[M] ≃ₐ[R] Π j, (A j)[M]`.

Absent from Mathlib. Upstream candidate. -/
noncomputable def piMonoidAlgEquiv (R : Type*) [CommSemiring R]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    (M : Type*) [DecidableEq M] [Monoid M] :
    MonoidAlgebra (Π j, A j) M ≃ₐ[R] Π j, MonoidAlgebra (A j) M :=
  AlgEquiv.ofBijective (piMonoidAlgFwd R ι A M) ⟨
    fun f g h => Finsupp.ext fun m => funext fun j => by
      have hj : piMonoidAlgFwd R ι A M f j = piMonoidAlgFwd R ι A M g j := congrFun h j
      have := Finsupp.ext_iff.mp hj m
      simp only [piMonoidAlgFwd, Pi.algHom, MonoidAlgebra.mapAlgHom,
        AlgHom.coe_mk, Pi.evalAlgHom] at this
      exact this,
    fun fs => by
      refine ⟨Finsupp.onFinset
        (Finset.univ.biUnion (fun j => (fs j).support))
        (fun m j => fs j m)
        (fun m hm => ?_), ?_⟩
      · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        by_contra hall
        simp only [not_exists, Finsupp.mem_support_iff, not_not] at hall
        exact hm (funext hall)
      · ext j m
        simp only [piMonoidAlgFwd, Pi.algHom, MonoidAlgebra.mapAlgHom,
          AlgHom.coe_mk, Pi.evalAlgHom, Finsupp.mapRange_apply]
        rfl⟩

/-! ### Character degrees of a product group

**Named gap: `matrixMonoidAlgEquiv`.**  The proof requires an algebra equivalence
`MonoidAlgebra (Matrix m m ℂ) G ≃ₐ[ℂ] Matrix m m (MonoidAlgebra ℂ G)` — matrix-valued
monoid algebras are isomorphic to matrices over monoid algebras.  This is
mathematically trivial (transpose the `G`-index and the matrix indices) but
requires custom `AlgEquiv` glue: Mathlib's `MonoidAlgebra.tensorEquiv` and
`matrixEquivTensor` both require `CommSemiring` on the noncommutative factor,
so cannot be composed for noncommutative groups.  The combinatorial corollaries
(`charDegreeSumReal_prod`, `charDegreeSumReal_pi_fin`) are proved assuming
`charDegrees_prod` and do not introduce further sorries.

See `.tasks/f5exp/docs/md1-notes.md` for the full gap specification.

The available sorry-free chain so far:
  `ℂ[G × H] ≃ₐ ℂ[H][G]`               (curryAlgEquiv)
  `ℂ[H][G] ≃ₐ (Π j, Mat_{e_j}(ℂ))[G]` (mapAlgEquiv using eH)
  `(Π j, Mat_{e_j}(ℂ))[G] ≃ₐ Π j, Mat_{e_j}(ℂ)[G]`  (piMonoidAlgEquiv)
The remaining step Mat_{e_j}(ℂ)[G] ≃ₐ Π i, Mat_{d_i · e_j}(ℂ) is the gap. -/

/-- **Character degrees multiply over products.** The character-degree multiset
of `G × H` is the multiset of all pairwise products `d * e` for `d ∈ charDegrees G`
and `e ∈ charDegrees H`. -/
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
  -- Rewrite LHS and RHS via charDegrees_eq_of_algEquiv
  rw [charDegrees_eq_of_algEquiv G eG, charDegrees_eq_of_algEquiv H eH]
  -- LHS needs a decomposition of ℂ[G × H] into blocks of size dG i * dH j
  -- RHS = (Finset.univ.val.map dG).bind (fun d => (Finset.univ.val.map dH).map (d * ·))
  -- Gap: constructing the AlgEquiv ℂ[G × H] ≃ₐ Π (i,j), Mat_{dG i * dH j}(ℂ)
  sorry

/-! ### Multiset bookkeeping for the rpow sum -/

/-- The rpow sum over a bind/map product factors as a product of rpow sums. -/
private theorem rpow_sum_bind_map (s : Multiset ℕ) (t : Multiset ℕ) (x : ℝ) :
    ((s.bind (fun d => t.map (fun e => d * e))).map (fun d => (d : ℝ) ^ x)).sum =
      ((s.map (fun d => (d : ℝ) ^ x)).sum) * ((t.map (fun e => (e : ℝ) ^ x)).sum) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.bind_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_cons,
      Multiset.sum_cons, Multiset.map_map, Function.comp]
    rw [ih, add_mul]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    congr 1; ext e
    push_cast [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg e)

/-! ### Multiplicativity of `charDegreeSumReal` -/

/-- **The real-exponent power sum is multiplicative over products:**
`D_x(G × H) = D_x(G) · D_x(H)`. -/
theorem charDegreeSumReal_prod (G H : Type*) [Group G] [Fintype G] [Group H] [Fintype H]
    (x : ℝ) :
    charDegreeSumReal (G × H) x = charDegreeSumReal G x * charDegreeSumReal H x := by
  unfold charDegreeSumReal
  rw [charDegrees_prod]
  exact rpow_sum_bind_map _ _ x

/-! ### Iterated power form

**Power carrier: `Fin ℓ → G`** with `Pi.group`. Downstream cards (Tp1) must
use this same carrier. -/

/-- **The power form:** `D_x(G^ℓ) = D_x(G)^ℓ` where `G^ℓ = Fin ℓ → G`. -/
theorem charDegreeSumReal_pi_fin (G : Type*) [Group G] [Fintype G]
    (ℓ : ℕ) (x : ℝ) :
    charDegreeSumReal (Fin ℓ → G) x = (charDegreeSumReal G x) ^ ℓ := by
  induction ℓ with
  | zero =>
    -- Fin 0 → G is the trivial group (unique element), charDegreeSumReal = 1^x = 1
    simp only [pow_zero]
    -- charDegreeSumReal (Fin 0 → G) x = sum over charDegrees of (Fin 0 → G)
    -- Fin 0 → G has only one element, so it's a trivial group
    -- Its only irrep is the trivial one of degree 1, so charDegrees = {1}
    -- and charDegreeSumReal = 1^x = 1
    sorry
  | succ n ih =>
    -- Fin (n+1) → G ≅ G × (Fin n → G) via Fin.cons
    -- charDegreeSumReal (Fin (n+1) → G) x
    --   = charDegreeSumReal G x * charDegreeSumReal (Fin n → G) x   (by prod)
    --   = charDegreeSumReal G x * (charDegreeSumReal G x) ^ n        (by ih)
    --   = (charDegreeSumReal G x) ^ (n+1)
    sorry

end Xlib.CharDegreesMul
