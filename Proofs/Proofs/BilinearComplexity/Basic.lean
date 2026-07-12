/-
  BilinearComplexity/Basic — rectangular 3-tensors, tensor rank, and the
  matrix multiplication tensor.

  Foundation of the tensor-rank calculus campaign (roadmap priority 2).
  It generalizes the deliberately cubic `Vp2.Tensor3`
  (`Proofs.Vp2.BorderRank`, left untouched) to rectangular shape and adds
  the rank function and the matrix multiplication tensor:

    · `Tensor k a b c`   — concrete rectangular 3-tensors
                           `Fin a → Fin b → Fin c → k`.
    · `RankLE T r`       — `T` is a sum of at most `r` rank-one triads
                           (rectangular lift of `Vp2.RankLE`), with
                           `RankLE.mono` and the trivial decompositions
                           `rankLE_mul` (r = a*b) and, for the matrix
                           multiplication tensor, `rankLE_matMulTensor`
                           (r = a*b*c).
    · `rank T`           — the least such `r` (`sInf`; total by
                           `rankLE_mul`), with the order API
                           `rankLE_rank`, `rank_le_of_rankLE`,
                           `rankLE_of_rank_le`, `rank_le_iff`,
                           `rank_zero`, `rank_eq_zero_iff`, `rank_le_mul`.
    · `matMulTensor k a b c` — the matrix multiplication tensor
                           `⟨a,b,c⟩ : Tensor k (a*b) (b*c) (c*a)`, with
                           the sanity anchors `rank_matMulTensor_le`
                           (≤ a*b*c) and `rank_matMulTensor_one` (= 1).

  INDEX-PACKING CONVENTION (Pf8/Pf9/Pf10 depend on this; do not change).
  Pairs are packed by Mathlib's
  `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`, whose forward map is
  `(i, j) ↦ j + n * i`: the FIRST component `i` is the slow (row) index,
  recovered as `x.divNat = x / n`; the SECOND component `j` is the fast
  (column) index, recovered as `x.modNat = x % n`. This is row-major
  order. Unpacking `x : Fin (a * b)` as
  `finProdFinEquiv.symm x : Fin a × Fin b` therefore yields `.1 = i`
  (slow, `Fin a`) and `.2 = j` (fast, `Fin b`).

  `matMulTensor k a b c x y z`, for `x = (i,j) : Fin (a*b)`,
  `y = (j',l) : Fin (b*c)`, `z = (l',i') : Fin (c*a)` (all row-major
  packed), is `1` iff `j = j' ∧ l = l' ∧ i' = i`, else `0`: it is the
  structure tensor of the trilinear form
  `(X, Y, Z) ↦ trace (X * Y * Z)` on row-major-flattened matrices
  `X : a × b`, `Y : b × c`, `Z : c × a`. The cyclic rotation
  `fun y z x => matMulTensor k a b c x y z` agrees entrywise with
  `matMulTensor k b c a : Tensor k (b*c) (c*a) (a*b)` — the types match
  on the nose, and the if-conditions match up to `and_rotate` (theorem
  owned by card Pf8, `RankCalculus.lean`).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Equiv.Fin.Basic

namespace BilinearComplexity

/-! ## 1. Rectangular tensors and the rank-≤ r predicate -/

/-- A rectangular 3-tensor of shape `a × b × c` over `k`: `T i j l` is the
entry `c_{ijl}`. This is the rectangular generalization of `Vp2.Tensor3`,
the same object as a point of `kᵃ ⊗ kᵇ ⊗ kᶜ` in the standard basis. -/
abbrev Tensor (k : Type*) (a b c : ℕ) : Type _ := Fin a → Fin b → Fin c → k

section Rank

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- `RankLE T r` : the tensor `T` is a sum of at most `r` rank-one (simple)
triads — the honest, closure-free rank-≤ r condition. Rectangular lift of
`Vp2.RankLE`. -/
def RankLE (T : Tensor k a b c) (r : ℕ) : Prop :=
  ∃ u : Fin r → Fin a → k, ∃ v : Fin r → Fin b → k, ∃ w : Fin r → Fin c → k,
    T = fun i j l => ∑ s, u s i * v s j * w s l

/-- Rank is monotone in `r`: pad the decomposition with zero triads. -/
theorem RankLE.mono {T : Tensor k a b c} {r r' : ℕ} (h : RankLE T r)
    (hrr' : r ≤ r') : RankLE T r' := by
  obtain ⟨u, v, w, hT⟩ := h
  have key : RankLE T (r + (r' - r)) := by
    refine ⟨Fin.append u 0, Fin.append v 0, Fin.append w 0, ?_⟩
    subst hT
    funext i j l
    simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rwa [show r + (r' - r) = r' from by omega] at key

/-- Every tensor of shape `a × b × c` has rank at most `a * b`: the trivial
decomposition with one triad `e_i ⊗ e_j ⊗ T i j ·` per matrix position
`(i, j)`, indexed by the row-major packing `finProdFinEquiv`. -/
theorem rankLE_mul (T : Tensor k a b c) : RankLE T (a * b) := by
  refine ⟨fun s i => if (finProdFinEquiv.symm s).1 = i then 1 else 0,
          fun s j => if (finProdFinEquiv.symm s).2 = j then 1 else 0,
          fun s l => T (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2 l,
          ?_⟩
  funext i j l
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin a × Fin b ≃ Fin (a * b))]
  simp [Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq']

/-! ## 2. Rank -/

/-- The rank of a tensor: the least `r` admitting an `r`-triad
decomposition. The defining set is nonempty by `rankLE_mul`, so the `sInf`
is a genuine minimum (`rankLE_rank`). -/
noncomputable def rank (T : Tensor k a b c) : ℕ :=
  sInf {r | RankLE T r}

/-- The rank is attained: every tensor admits a decomposition into
`rank T` triads. -/
theorem rankLE_rank (T : Tensor k a b c) : RankLE T (rank T) :=
  Nat.sInf_mem (s := {r | RankLE T r}) ⟨a * b, rankLE_mul T⟩

theorem rank_le_of_rankLE {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    rank T ≤ r :=
  Nat.sInf_le h

theorem rankLE_of_rank_le {T : Tensor k a b c} {r : ℕ} (h : rank T ≤ r) :
    RankLE T r :=
  (rankLE_rank T).mono h

theorem rank_le_iff {T : Tensor k a b c} {r : ℕ} :
    rank T ≤ r ↔ RankLE T r :=
  ⟨rankLE_of_rank_le, rank_le_of_rankLE⟩

/-- The trivial rank bound: `rank T ≤ a * b`. -/
theorem rank_le_mul (T : Tensor k a b c) : rank T ≤ a * b :=
  rank_le_of_rankLE (rankLE_mul T)

/-- Rank ≤ 0 means the tensor is zero (the empty sum of triads). -/
theorem rankLE_zero_iff {T : Tensor k a b c} : RankLE T 0 ↔ T = 0 := by
  constructor
  · rintro ⟨u, v, w, rfl⟩
    funext i j l
    simp
  · rintro rfl
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, by funext i j l; simp⟩

theorem rank_zero : rank (0 : Tensor k a b c) = 0 :=
  Nat.le_zero.mp (rank_le_of_rankLE (rankLE_zero_iff.mpr rfl))

theorem rank_eq_zero_iff {T : Tensor k a b c} : rank T = 0 ↔ T = 0 := by
  rw [← Nat.le_zero, rank_le_iff, rankLE_zero_iff]

end Rank

/-! ## 3. The matrix multiplication tensor -/

/-- The matrix multiplication tensor `⟨a,b,c⟩`, the structure tensor of
`(X, Y, Z) ↦ trace (X * Y * Z)` for `X : a × b`, `Y : b × c`, `Z : c × a`:
with all three sides row-major packed by `finProdFinEquiv`
(`.1` = slow index, `.2` = fast index — see the file header), the entry at
`(x, y, z) = ((i,j), (j',l), (l',i'))` is `1` iff
`j = j' ∧ l = l' ∧ i' = i`, else `0`. -/
def matMulTensor (k : Type*) [CommSemiring k] (a b c : ℕ) :
    Tensor k (a * b) (b * c) (c * a) := fun x y z =>
  if (finProdFinEquiv.symm x).2 = (finProdFinEquiv.symm y).1
      ∧ (finProdFinEquiv.symm y).2 = (finProdFinEquiv.symm z).1
      ∧ (finProdFinEquiv.symm z).2 = (finProdFinEquiv.symm x).1
    then 1 else 0

/-- Entry formula for `matMulTensor`, as a `rfl`-lemma for rewriting. -/
theorem matMulTensor_apply (k : Type*) [CommSemiring k] (a b c : ℕ)
    (x : Fin (a * b)) (y : Fin (b * c)) (z : Fin (c * a)) :
    matMulTensor k a b c x y z =
      if (finProdFinEquiv.symm x).2 = (finProdFinEquiv.symm y).1
          ∧ (finProdFinEquiv.symm y).2 = (finProdFinEquiv.symm z).1
          ∧ (finProdFinEquiv.symm z).2 = (finProdFinEquiv.symm x).1
        then 1 else 0 :=
  rfl

/-- The standard `a*b*c`-triad decomposition of the matrix multiplication
tensor, one triad `e_{ij} ⊗ e_{jl} ⊗ e_{li}` per index triple `(i, j, l)`:
`⟨a,b,c⟩ = ∑_{(i,j,l)} e_{ij} ⊗ e_{jl} ⊗ e_{li}`. The triad index
`s : Fin (a*b*c)` unpacks as `((i,j),l)` via two `finProdFinEquiv.symm`s. -/
theorem rankLE_matMulTensor (k : Type*) [CommSemiring k] (a b c : ℕ) :
    RankLE (matMulTensor k a b c) (a * b * c) := by
  refine ⟨fun s x =>
      if (finProdFinEquiv.symm (finProdFinEquiv.symm s).1).1
            = (finProdFinEquiv.symm x).1
          ∧ (finProdFinEquiv.symm (finProdFinEquiv.symm s).1).2
            = (finProdFinEquiv.symm x).2
        then 1 else 0,
    fun s y =>
      if (finProdFinEquiv.symm (finProdFinEquiv.symm s).1).2
            = (finProdFinEquiv.symm y).1
          ∧ (finProdFinEquiv.symm s).2 = (finProdFinEquiv.symm y).2
        then 1 else 0,
    fun s z =>
      if (finProdFinEquiv.symm s).2 = (finProdFinEquiv.symm z).1
          ∧ (finProdFinEquiv.symm z).2
            = (finProdFinEquiv.symm (finProdFinEquiv.symm s).1).1
        then 1 else 0,
    ?_⟩
  funext x y z
  rw [← Equiv.sum_comp
    ((finProdFinEquiv.prodCongr (Equiv.refl (Fin c))).trans finProdFinEquiv)]
  simp only [matMulTensor, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply', id_eq, Equiv.symm_apply_apply,
    Fintype.sum_prod_type, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.sum_const_zero, Finset.mem_univ, if_true]
  split_ifs <;> simp_all

/-- Rank bound for the matrix multiplication tensor from the standard
decomposition: `rank ⟨a,b,c⟩ ≤ a*b*c`. (The generic `rank_le_mul` would
only give the weaker `(a*b) * (b*c)`.) -/
theorem rank_matMulTensor_le (k : Type*) [CommSemiring k] (a b c : ℕ) :
    rank (matMulTensor k a b c) ≤ a * b * c :=
  rank_le_of_rankLE (rankLE_matMulTensor k a b c)

/-- Sanity anchor: `⟨1,1,1⟩` (multiplication of scalars) has rank ≤ 1. -/
theorem rankLE_matMulTensor_one (k : Type*) [CommSemiring k] :
    RankLE (matMulTensor k 1 1 1) 1 := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  rw [matMulTensor_apply, if_pos ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _⟩]
  simp

/-- Sanity anchor: over a nontrivial semiring, `⟨1,1,1⟩` has rank exactly 1
(it is a nonzero tensor of rank ≤ 1). -/
theorem rank_matMulTensor_one (k : Type*) [CommSemiring k] [Nontrivial k] :
    rank (matMulTensor k 1 1 1) = 1 := by
  refine le_antisymm (rank_le_of_rankLE (rankLE_matMulTensor_one k)) ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [rank_eq_zero_iff] at h0
  have h1 : matMulTensor k 1 1 1 ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
    rw [h0]; rfl
  rw [matMulTensor_apply, if_pos ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _⟩] at h1
  exact one_ne_zero h1

end BilinearComplexity
