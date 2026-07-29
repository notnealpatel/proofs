import GroupTPP.CharDegrees

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

The proof of `charDegrees_prod` builds a composite algebra equivalence
  `ℂ[G × H] ≃ₐ[ℂ] Π (i,j), Mat_{d_i · e_j}(ℂ)`
from Wedderburn decompositions `eG : ℂ[G] ≃ₐ Π i, Mat_{d_i}(ℂ)` and
`eH : ℂ[H] ≃ₐ Π j, Mat_{e_j}(ℂ)`, via `MonoidAlgebra.curryAlgEquiv`,
`MonoidAlgebra.mapAlgEquiv`, and three planks proved here because they are
absent from Mathlib:

* `piMonoidAlgEquiv` — monoid algebra distributes over Pi,
* `matrixMonoidAlgEquiv` — matrix-valued monoid algebras are matrices over
  monoid algebras, `MonoidAlgebra (Matrix m m A) G ≃ₐ[R] Matrix m m (MonoidAlgebra A G)`
  (Mathlib's `MonoidAlgebra.tensorEquiv` requires commutative coefficients and
  a commutative monoid, so it cannot produce this; built directly from
  `liftNCAlgHom`),
* `piProdAlgEquiv` — Pi over a product index curries,
* `Matrix.piAlgEquiv` (Mathlib) — matrices distribute over Pi.

Everything is `sorry`-free; `charDegrees_eq_of_algEquiv` (Wedderburn
uniqueness) transports the block multisets on both sides, and the multiset
bookkeeping is `univ_val_map_mul_finProdFinEquiv_symm`.

Note on coercions: `charDegreeSumReal` elaborates its `ℕ → ℝ` cast as the
*monadic container cast* `do let a ← s; pure ↑a`, not as `Multiset.map (↑·)`;
`rpow_sum_bind_map` normalizes this via `Multiset.bind_def`/`pure_def`/
`bind_singleton` before transferring to the `Multiset ℝ` version.

## Upstream candidates

`charDegrees_prod`, `one_le_of_mem_charDegrees`, `piMonoidAlgEquiv`,
`matrixMonoidAlgEquiv`, `charDegrees_eq_of_mulEquiv`, and
`charDegreeSumReal_prod` are natural Mathlib candidates (provenance note
only, no upstreaming per user directive).
-/

open scoped BigOperators
open GroupTPP.CharDegrees

namespace GroupTPP.CharDegreesMul

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
    fun f g h => by
      ext m j
      have hj : piMonoidAlgFwd R ι A M f j = piMonoidAlgFwd R ι A M g j := congrFun h j
      have hmj := Finsupp.ext_iff.mp (congrArg MonoidAlgebra.coeff hj) m
      simp only [piMonoidAlgFwd, Pi.algHom, MonoidAlgebra.mapAlgHom,
        AlgHom.coe_mk, Pi.evalAlgHom] at hmj
      exact hmj,
    fun fs => by
      refine ⟨⟨Finsupp.onFinset
        (Finset.univ.biUnion (fun j => (fs j).coeff.support))
        (fun m j => (fs j).coeff m)
        (fun m hm => ?_)⟩, ?_⟩
      · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        by_contra hall
        simp only [not_exists, Finsupp.mem_support_iff, not_not] at hall
        exact hm (funext hall)
      · ext j m
        simp only [piMonoidAlgFwd, Pi.algHom, MonoidAlgebra.mapAlgHom,
          AlgHom.coe_mk, Pi.evalAlgHom]
        rfl⟩

/-- **Pi over a product index curries.**
`(Π i, Π j, C i j) ≃ₐ[R] Π p : ι × κ, C p.1 p.2`; all fields are definitional. -/
noncomputable def piProdAlgEquiv (R : Type*) [CommSemiring R] (ι κ : Type*)
    (C : ι → κ → Type*) [∀ i j, Semiring (C i j)] [∀ i j, Algebra R (C i j)] :
    (Π i, Π j, C i j) ≃ₐ[R] Π p : ι × κ, C p.1 p.2 where
  toFun f p := f p.1 p.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-! ### Matrix-valued monoid algebras are matrices over monoid algebras

This was the named gap of Md1: an algebra equivalence
  `MonoidAlgebra (Matrix m m A) G ≃ₐ[R] Matrix m m (MonoidAlgebra A G)`.
Mathlib's `MonoidAlgebra.tensorEquiv` / `scalarTensorEquiv` require
`CommSemiring` coefficients **and** a `CommMonoid` monoid, so they cannot be
used for noncommutative `Matrix m m ℂ` over a noncommutative group.  We build
the equivalence directly: the forward algebra homomorphism is
`MonoidAlgebra.liftNCAlgHom` on the generators (coefficient matrices go to
matrices of `single 1` coefficients; group elements go to scalar matrices
`single g 1 • 1`), whose pointwise value is the index transposition
`x g i j` (proved by `induction_linear`); bijectivity is then immediate from
the explicit formula. -/

/-- The forward algebra homomorphism
`MonoidAlgebra (Matrix m m A) G →ₐ[R] Matrix m m (MonoidAlgebra A G)`,
via the non-commutative universal property `liftNCAlgHom`. -/
noncomputable def matrixMonoidAlgFwd (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] (m : Type*) [Fintype m] [DecidableEq m] (G : Type*) [Monoid G] :
    MonoidAlgebra (Matrix m m A) G →ₐ[R] Matrix m m (MonoidAlgebra A G) :=
  MonoidAlgebra.liftNCAlgHom
    (AlgHom.mapMatrix (MonoidAlgebra.singleOneAlgHom :
      A →ₐ[R] MonoidAlgebra A G))
    ((Matrix.scalar m).toMonoidHom.comp (MonoidAlgebra.of A G))
    (fun X g => by
      show _ * _ = _ * _
      ext i j
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
        Function.comp_apply, MonoidAlgebra.of_apply, Matrix.scalar_apply,
        AlgHom.mapMatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.map_apply, MonoidAlgebra.singleOneAlgHom_apply,
        MonoidAlgebra.single_mul_single, one_mul, mul_one])

/-- The pointwise value of `matrixMonoidAlgFwd` is the index transposition. -/
private theorem matrixMonoidAlgFwd_apply (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] (m : Type*) [Fintype m] [DecidableEq m] (G : Type*) [Monoid G]
    (x : MonoidAlgebra (Matrix m m A) G) (i j : m) (g : G) :
    (matrixMonoidAlgFwd R A m G x i j).coeff g = x.coeff g i j := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; rfl
  | add f h hf hh => simp [hf, hh]
  | single g' X =>
    simp only [matrixMonoidAlgFwd, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      MonoidAlgebra.coe_liftNCAlgHom,
      MonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidAlgebra.of_apply,
      Matrix.scalar_apply, AlgHom.mapMatrix_apply, Matrix.mul_diagonal, Matrix.map_apply,
      MonoidAlgebra.singleOneAlgHom_apply, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    split_ifs <;> simp

/-- **Matrix-valued monoid algebras are matrices over monoid algebras**:
`MonoidAlgebra (Matrix m m A) G ≃ₐ[R] Matrix m m (MonoidAlgebra A G)`.

This was the named gap of Md1.  Mathlib cannot provide it via tensor products
(`MonoidAlgebra.tensorEquiv` requires commutative coefficients and a
commutative monoid), so it is built directly from `liftNCAlgHom` and the
pointwise transposition formula.  Absent from Mathlib. -/
noncomputable def matrixMonoidAlgEquiv (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] (m : Type*) [Fintype m] [DecidableEq m] (G : Type*) [Monoid G] :
    MonoidAlgebra (Matrix m m A) G ≃ₐ[R] Matrix m m (MonoidAlgebra A G) :=
  AlgEquiv.ofBijective (matrixMonoidAlgFwd R A m G) ⟨
    fun x y h => by
      ext g i j
      have h' : (matrixMonoidAlgFwd R A m G x i j).coeff g =
          (matrixMonoidAlgFwd R A m G y i j).coeff g := by rw [h]
      rwa [matrixMonoidAlgFwd_apply, matrixMonoidAlgFwd_apply] at h',
    fun M => by
      classical
      refine ⟨⟨Finsupp.onFinset
        (Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (M i j).coeff.support)
        (fun g => Matrix.of fun i j => (M i j).coeff g) (fun g hg => ?_)⟩, ?_⟩
      · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        by_contra hall
        simp only [not_exists, Finsupp.mem_support_iff, not_not] at hall
        exact hg (by ext i j; exact hall i j)
      · ext i j g
        rw [matrixMonoidAlgFwd_apply]
        simp⟩

/-! ### Character degrees of a product group

The equivalence chain (Wedderburn data `eG : ℂ[G] ≃ₐ Π i, Mat_{d_i}(ℂ)` and
`eH : ℂ[H] ≃ₐ Π j, Mat_{e_j}(ℂ)`):

  `ℂ[G × H] ≃ₐ ℂ[H × G]`                                   (domCongr prodComm)
  `ℂ[H × G] ≃ₐ ℂ[G][H]`                                    (curryAlgEquiv)
  `ℂ[G][H] ≃ₐ (Π i, Mat_{d_i}(ℂ))[H]`                      (mapAlgEquiv eG)
  `(Π i, Mat_{d_i}(ℂ))[H] ≃ₐ Π i, Mat_{d_i}(ℂ)[H]`         (piMonoidAlgEquiv)
  `Π i, Mat_{d_i}(ℂ)[H] ≃ₐ Π i, Mat_{d_i}(ℂ[H])`           (matrixMonoidAlgEquiv)
  `Π i, Mat_{d_i}(ℂ[H]) ≃ₐ Π i, Mat_{d_i}(Π j, Mat_{e_j})` (mapMatrix eH)
  `≃ₐ Π i, Π j, Mat_{d_i}(Mat_{e_j}(ℂ))`                   (Matrix.piAlgEquiv)
  `≃ₐ Π i, Π j, Mat_{d_i · e_j}(ℂ)`                        (compAlgEquiv, reindex)
  `≃ₐ Π p : Fin n_G × Fin n_H, Mat_{d_{p.1} · e_{p.2}}(ℂ)` (piProdAlgEquiv)
  `≃ₐ Π k : Fin (n_G · n_H), Mat_{dd k}(ℂ)`                (piCongrLeft')

and then `charDegrees_eq_of_algEquiv` on both sides plus multiset bookkeeping
(`univ_val_map_mul_finProdFinEquiv_symm`). -/

/-- Multiset bookkeeping: enumerating `dG p.1 * dH p.2` over the flattened index
`Fin (nG * nH)` (via `finProdFinEquiv.symm`) gives exactly the bind/map multiset
of pairwise products. -/
private theorem univ_val_map_mul_finProdFinEquiv_symm {nG nH : ℕ}
    (dG : Fin nG → ℕ) (dH : Fin nH → ℕ) :
    (Finset.univ.val.map (fun k : Fin (nG * nH) =>
        dG (finProdFinEquiv.symm k).1 * dH (finProdFinEquiv.symm k).2)) =
      (Finset.univ.val.map dG).bind
        (fun d => (Finset.univ.val.map dH).map (fun e => d * e)) := by
  rw [← Finset.map_univ_equiv (finProdFinEquiv : Fin nG × Fin nH ≃ Fin (nG * nH)),
    Finset.map_val, Multiset.map_map]
  have h1 : (Finset.univ.val.map
      ((fun k : Fin (nG * nH) => dG (finProdFinEquiv.symm k).1 * dH (finProdFinEquiv.symm k).2)
        ∘ (finProdFinEquiv : Fin nG × Fin nH ≃ Fin (nG * nH)).toEmbedding)) =
      Finset.univ.val.map (fun p : Fin nG × Fin nH => dG p.1 * dH p.2) :=
    Multiset.map_congr rfl fun p _ => by
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  rw [h1, ← Finset.univ_product_univ, Finset.product_val]
  show ((Finset.univ.val.bind fun a => Finset.univ.val.map (Prod.mk a)).map
    (fun p : Fin nG × Fin nH => dG p.1 * dH p.2)) = _
  rw [Multiset.map_bind, Multiset.bind_map]
  exact Multiset.bind_congr fun a _ => by rw [Multiset.map_map, Multiset.map_map]; rfl

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
  letI : DecidableEq H := Classical.decEq H
  obtain ⟨nG, dG, hneG, ⟨eG⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  obtain ⟨nH, dH, hneH, ⟨eH⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ H)
  haveI := hneG; haveI := hneH
  haveI : ∀ k : Fin (nG * nH),
      NeZero (dG (finProdFinEquiv.symm k).1 * dH (finProdFinEquiv.symm k).2) :=
    fun k => ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  -- Assemble the block decomposition of ℂ[G × H] with blocks of size dG i * dH j
  have E : MonoidAlgebra ℂ (G × H) ≃ₐ[ℂ] Π k : Fin (nG * nH),
      Matrix (Fin (dG (finProdFinEquiv.symm k).1 * dH (finProdFinEquiv.symm k).2))
        (Fin (dG (finProdFinEquiv.symm k).1 * dH (finProdFinEquiv.symm k).2)) ℂ :=
    (MonoidAlgebra.domCongr ℂ ℂ (MulEquiv.prodComm : G × H ≃* H × G)).trans <|
      (MonoidAlgebra.curryAlgEquiv ℂ).trans <|
        (MonoidAlgebra.mapAlgEquiv ℂ H eG).trans <|
          (piMonoidAlgEquiv ℂ (Fin nG) (fun i => Matrix (Fin (dG i)) (Fin (dG i)) ℂ) H).trans <|
            (AlgEquiv.piCongrRight fun i =>
              (matrixMonoidAlgEquiv ℂ ℂ (Fin (dG i)) H).trans <|
                (AlgEquiv.mapMatrix eH).trans <|
                  (Matrix.piAlgEquiv ℂ).trans <|
                    AlgEquiv.piCongrRight fun j =>
                      (Matrix.compAlgEquiv (Fin (dG i)) (Fin (dH j)) ℂ ℂ).trans
                        (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv)).trans <|
              (piProdAlgEquiv ℂ (Fin nG) (Fin nH)
                (fun i j => Matrix (Fin (dG i * dH j)) (Fin (dG i * dH j)) ℂ)).trans <|
                AlgEquiv.piCongrLeft' ℂ
                  (fun p : Fin nG × Fin nH =>
                    Matrix (Fin (dG p.1 * dH p.2)) (Fin (dG p.1 * dH p.2)) ℂ)
                  finProdFinEquiv
  rw [charDegrees_eq_of_algEquiv (G × H) E, charDegrees_eq_of_algEquiv G eG,
    charDegrees_eq_of_algEquiv H eH]
  exact univ_val_map_mul_finProdFinEquiv_symm dG dH

/-- **`charDegrees` is a group-isomorphism invariant**: transport along
`MonoidAlgebra.domCongr` and apply Wedderburn uniqueness on both sides. -/
theorem charDegrees_eq_of_mulEquiv {G : Type*} [Group G] [Fintype G] {H : Type*} [Group H]
    [Fintype H] (e : G ≃* H) : charDegrees G = charDegrees H := by
  haveI : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, d, hne, ⟨eH⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ H)
  haveI := hne
  rw [charDegrees_eq_of_algEquiv H eH,
    charDegrees_eq_of_algEquiv G ((MonoidAlgebra.domCongr ℂ ℂ e).trans eH)]

/-! ### Multiset bookkeeping for the rpow sum -/

/-- The rpow sum over a bind/map product factors as a product of rpow sums. -/
-- Use ℝ-valued multiset versions to avoid ℕ→ℝ coercion/monadic friction
private theorem rpow_sum_bind_map_real (s t : Multiset ℝ) (x : ℝ)
    (hs : ∀ d ∈ s, (0 : ℝ) ≤ d) (ht : ∀ e ∈ t, (0 : ℝ) ≤ e) :
    ((s.bind (fun d => t.map (fun e => d * e))).map (· ^ x)).sum =
      ((s.map (· ^ x)).sum) * ((t.map (· ^ x)).sum) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.map_add, Multiset.sum_add,
      ih (fun d hd => hs d (Multiset.mem_cons_of_mem hd)),
      Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
    congr 1
    exact Multiset.map_congr rfl fun e he =>
      Real.mul_rpow (hs a (Multiset.mem_cons_self a s)) (ht e he)

private theorem rpow_sum_bind_map (s : Multiset ℕ) (t : Multiset ℕ) (x : ℝ) :
    ((s.bind (fun d => t.map (fun e => d * e))).map (fun d => (d : ℝ) ^ x)).sum =
      ((s.map (fun d => (d : ℝ) ^ x)).sum) * ((t.map (fun e => (e : ℝ) ^ x)).sum) := by
  -- The ℕ→ℝ coercion in the statement elaborates as the monadic container
  -- cast `do let a ← s; pure ↑a`; normalize it to `Multiset.map` first, then
  -- push the cast through bind/map and apply the ℝ-valued version.
  have key : (s.bind (fun d => t.map (fun e => d * e))).map (fun (a : ℕ) => (a : ℝ)) =
      (s.map (fun (a : ℕ) => (a : ℝ))).bind
        (fun d => (t.map (fun (a : ℕ) => (a : ℝ))).map (fun e => d * e)) := by
    rw [Multiset.map_bind, Multiset.bind_map]
    exact Multiset.bind_congr fun a _ => by
      rw [Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => by simp
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton]
  rw [key]
  exact rpow_sum_bind_map_real _ _ x
    (fun d hd => by
      obtain ⟨d', _, rfl⟩ := Multiset.mem_map.mp hd
      exact Nat.cast_nonneg d')
    (fun e he => by
      obtain ⟨e', _, rfl⟩ := Multiset.mem_map.mp he
      exact Nat.cast_nonneg e')

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

/-- **`charDegreeSumReal` is a group-isomorphism invariant.** -/
theorem charDegreeSumReal_congr {G : Type*} [Group G] [Fintype G] {H : Type*} [Group H]
    [Fintype H] (e : G ≃* H) (x : ℝ) : charDegreeSumReal G x = charDegreeSumReal H x := by
  unfold charDegreeSumReal
  rw [charDegrees_eq_of_mulEquiv e]

/-- The group isomorphism `(Fin (n+1) → G) ≃* G × (Fin n → G)`: evaluation at
`0` paired with the tail (`Fin.consEquiv`, upgraded — multiplication on both
sides is componentwise, so `map_mul` is definitional). -/
private def piFinSuccMulEquiv (n : ℕ) (G : Type*) [Group G] :
    (Fin (n + 1) → G) ≃* G × (Fin n → G) :=
  { (Fin.consEquiv (fun _ : Fin (n + 1) => G)).symm with
    map_mul' := fun _ _ => rfl }

/-- **The power form:** `D_x(G^ℓ) = D_x(G)^ℓ` where `G^ℓ = Fin ℓ → G`. -/
theorem charDegreeSumReal_pi_fin (G : Type*) [Group G] [Fintype G]
    (ℓ : ℕ) (x : ℝ) :
    charDegreeSumReal (Fin ℓ → G) x = (charDegreeSumReal G x) ^ ℓ := by
  induction ℓ with
  | zero =>
    -- `Fin 0 → G` is the trivial group: exactly one conjugacy class, so exactly
    -- one character degree `d`, and `d² = |Fin 0 → G| = 1` forces `d = 1`.
    haveI : Subsingleton (ConjClasses (Fin 0 → G)) :=
      ConjClasses.mk_surjective.subsingleton
    have hcard : Multiset.card (charDegrees (Fin 0 → G)) = 1 := by
      rw [card_charDegrees, Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, ⟨ConjClasses.mk 1⟩⟩
    obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp hcard
    have h2 : d ^ 2 = 1 := by
      have h := charDegreeSum_two (Fin 0 → G)
      rw [Fintype.card_unique] at h
      unfold charDegreeSum at h
      rw [hd] at h
      simpa using h
    have hd1 : d = 1 := (pow_eq_one_iff_left two_ne_zero).mp h2
    unfold charDegreeSumReal
    rw [hd, hd1, pow_zero]
    simp
  | succ n ih =>
    rw [charDegreeSumReal_congr (piFinSuccMulEquiv n G) x, charDegreeSumReal_prod, ih,
      ← pow_succ']

end GroupTPP.CharDegreesMul
