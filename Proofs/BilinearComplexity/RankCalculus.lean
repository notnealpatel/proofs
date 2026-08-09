/-
  BilinearComplexity/RankCalculus — the rank calculus for rectangular
  3-tensors: direct-sum subadditivity, Kronecker submultiplicativity,
  cyclic (S₃-rotation) symmetry including `cyc_matMulTensor`, GL
  invariance of rank via mode contractions, and reindexing invariance.

  Everything is stated over `CommSemiring k`, including GL invariance,
  which is phrased with `Invertible M` (meaningful in the square-matrix
  semiring; no determinants needed). Index pairs are packed row-major by
  `finProdFinEquiv` exactly as in `Basic.lean` (first component slow);
  `kron` uses the same orientation, so Kronecker powers of `matMulTensor`
  stay aligned with the packing convention.

    · `directSum T T'`     — block-diagonal sum;
                             `rank (directSum T T') ≤ rank T + rank T'`.
    · `kron T T'`          — Kronecker (outer) product;
                             `rank (kron T T') ≤ rank T * rank T'`.
    · `cyc T`              — cyclic rotation `cyc T j l i = T i j l`, with
                             `cyc³ = id` definitionally;
                             `rank (cyc T) = rank T`, and
                             `cyc (matMulTensor k a b c) = matMulTensor k b c a`
                             on the nose, whence `R⟨a,b,c⟩ = R⟨b,c,a⟩`
                             (`rank_matMulTensor_cyc`).
    · `contract₁/₂/₃ M T`  — contraction of one mode by a matrix; rank
                             never increases (`rank_contractᵢ_le`) and is
                             preserved for `Invertible M`
                             (`rank_contractᵢ_of_invertible`).
    · `reindex ea eb ec T` — mode-wise `Fin`-equiv relabeling; rank is
                             invariant (`rank_reindex`).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import BilinearComplexity.Basic

namespace BilinearComplexity

/-! ## 1. Direct sum -/

section DirectSum

variable {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}

/-- The direct sum `T ⊕ T'` of two 3-tensors: block-diagonal, equal to `T`
on the `(lo,lo,lo)` block, to `T'` on the `(hi,hi,hi)` block, and `0` on
all six mixed blocks. -/
def directSum (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    Tensor k (a + a') (b + b') (c + c') :=
  Fin.append
    (fun i => Fin.append (fun j => Fin.append (T i j) 0) fun _ => 0)
    (fun i => Fin.append (fun _ => 0) fun j => Fin.append 0 (T' i j))

/-- The `(lo,lo,lo)` block of a direct sum is the first summand. -/
@[simp] theorem directSum_apply_left (T : Tensor k a b c) (T' : Tensor k a' b' c')
    (i : Fin a) (j : Fin b) (l : Fin c) :
    directSum T T' (Fin.castAdd a' i) (Fin.castAdd b' j) (Fin.castAdd c' l)
      = T i j l := by
  simp [directSum]

/-- The `(hi,hi,hi)` block of a direct sum is the second summand. -/
@[simp] theorem directSum_apply_right (T : Tensor k a b c) (T' : Tensor k a' b' c')
    (i : Fin a') (j : Fin b') (l : Fin c') :
    directSum T T' (Fin.natAdd a i) (Fin.natAdd b j) (Fin.natAdd c l)
      = T' i j l := by
  simp [directSum]

/-- Rank is subadditive under direct sums: concatenate the two triad
families with `Fin.append`, extending every vector by zero on the foreign
block. -/
theorem RankLE.directSum {T : Tensor k a b c} {T' : Tensor k a' b' c'} {r r' : ℕ}
    (h : RankLE T r) (h' : RankLE T' r') : RankLE (directSum T T') (r + r') := by
  obtain ⟨u, v, w, rfl⟩ := h
  obtain ⟨u', v', w', rfl⟩ := h'
  refine ⟨Fin.append (fun s => Fin.append (u s) 0) fun s => Fin.append 0 (u' s),
          Fin.append (fun s => Fin.append (v s) 0) fun s => Fin.append 0 (v' s),
          Fin.append (fun s => Fin.append (w s) 0) fun s => Fin.append 0 (w' s),
          ?_⟩
  funext i j l
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      cases l using Fin.addCases <;>
    simp [BilinearComplexity.directSum, Fin.sum_univ_add]

/-- `rank (T ⊕ T') ≤ rank T + rank T'`. -/
theorem rank_directSum_le (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    rank (directSum T T') ≤ rank T + rank T' :=
  rank_le_of_rankLE ((rankLE_rank T).directSum (rankLE_rank T'))

end DirectSum

/-! ## 2. Kronecker product -/

section Kron

variable {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}

/-- The Kronecker (outer/tensor) product `T ⊗ T'` of two 3-tensors, with
each pair of modes packed row-major by `finProdFinEquiv` (first component
slow), matching the packing convention of `matMulTensor`. -/
def kron (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    Tensor k (a * a') (b * b') (c * c') := fun i j l =>
  T (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm l).1
    * T' (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm l).2

/-- Entry formula for `kron`, as a `rfl`-lemma for rewriting. -/
theorem kron_apply (T : Tensor k a b c) (T' : Tensor k a' b' c')
    (i : Fin (a * a')) (j : Fin (b * b')) (l : Fin (c * c')) :
    kron T T' i j l =
      T (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm l).1
        * T' (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm l).2 :=
  rfl

/-- Rank is submultiplicative under Kronecker products: triads multiply
pairwise, the product family being indexed by `Fin (r * r')` through the
same row-major packing. -/
theorem RankLE.kron {T : Tensor k a b c} {T' : Tensor k a' b' c'} {r r' : ℕ}
    (h : RankLE T r) (h' : RankLE T' r') : RankLE (kron T T') (r * r') := by
  obtain ⟨u, v, w, rfl⟩ := h
  obtain ⟨u', v', w', rfl⟩ := h'
  refine ⟨fun s i => u (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm i).1
            * u' (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm i).2,
          fun s j => v (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm j).1
            * v' (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm j).2,
          fun s l => w (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm l).1
            * w' (finProdFinEquiv.symm s).2 (finProdFinEquiv.symm l).2,
          ?_⟩
  funext i j l
  simp only [kron_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin r × Fin r' ≃ Fin (r * r'))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

/-- `rank (T ⊗ T') ≤ rank T * rank T'`. -/
theorem rank_kron_le (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    rank (kron T T') ≤ rank T * rank T' :=
  rank_le_of_rankLE ((rankLE_rank T).kron (rankLE_rank T'))

end Kron

/-! ## 3. Cyclic rotation -/

section CycDef

variable {k : Type*} {a b c : ℕ}

/-- Cyclic rotation of a 3-tensor: `cyc T j l i = T i j l` — mode 1 moves
to the back, so an `a × b × c` tensor becomes `b × c × a`. Three rotations
are the identity, definitionally (`cyc_cyc_cyc`). -/
def cyc (T : Tensor k a b c) : Tensor k b c a := fun j l i => T i j l

@[simp] theorem cyc_apply (T : Tensor k a b c) (j : Fin b) (l : Fin c) (i : Fin a) :
    cyc T j l i = T i j l := rfl

@[simp] theorem cyc_cyc_cyc (T : Tensor k a b c) : cyc (cyc (cyc T)) = T := rfl

end CycDef

section Cyc

variable {k : Type*} [CommSemiring k] {a b c : ℕ}

/-- Rank does not increase under cyclic rotation: rotate the roles of the
three vector families in a triad decomposition. -/
theorem RankLE.cyc {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    RankLE (cyc T) r := by
  obtain ⟨u, v, w, rfl⟩ := h
  refine ⟨v, w, u, ?_⟩
  funext j l i
  show ∑ s, u s i * v s j * w s l = ∑ s, v s j * w s l * u s i
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Rank-≤ is invariant under cyclic rotation (rotate twice more to come
back around, using `cyc³ = id`). -/
theorem rankLE_cyc_iff {T : Tensor k a b c} {r : ℕ} :
    RankLE (cyc T) r ↔ RankLE T r :=
  ⟨fun h => h.cyc.cyc, RankLE.cyc⟩

/-- Rank is invariant under cyclic rotation. -/
@[simp] theorem rank_cyc (T : Tensor k a b c) : rank (cyc T) = rank T :=
  le_antisymm (rank_le_of_rankLE (rankLE_rank T).cyc)
    (rank_le_of_rankLE ((rankLE_rank (cyc T)).cyc.cyc))

end Cyc

/-- Rotating the matrix multiplication tensor gives the rotated matrix
multiplication tensor, on the nose: `cyc ⟨a,b,c⟩ = ⟨b,c,a⟩`. With the
row-major packing convention both sides have type
`Tensor k (b*c) (c*a) (a*b)` syntactically, and the two δ-conditions are
cyclic rotations of each other (`and_rotate`). -/
theorem cyc_matMulTensor (k : Type*) [CommSemiring k] (a b c : ℕ) :
    cyc (matMulTensor k a b c) = matMulTensor k b c a := by
  funext y z x
  simp only [cyc_apply, matMulTensor_apply]
  exact if_congr and_rotate rfl rfl

/-- The fundamental rotation symmetry of matrix multiplication complexity:
`R⟨a,b,c⟩ = R⟨b,c,a⟩`. -/
theorem rank_matMulTensor_cyc (k : Type*) [CommSemiring k] (a b c : ℕ) :
    rank (matMulTensor k a b c) = rank (matMulTensor k b c a) := by
  rw [← cyc_matMulTensor k a b c, rank_cyc]

/-! ## 4. Mode contractions and GL invariance -/

section Contract

variable {k : Type*} [CommSemiring k] {a b c a' b' c' a'' b'' c'' : ℕ}

/-- Contraction of mode 1 by a matrix:
`contract₁ M T i' j l = ∑ i, M i' i * T i j l`. For invertible `M` this is
base change on the first mode. -/
def contract₁ (M : Matrix (Fin a') (Fin a) k) (T : Tensor k a b c) :
    Tensor k a' b c := fun i' j l => ∑ i, M i' i * T i j l

/-- Contraction of mode 2 by a matrix:
`contract₂ M T i j' l = ∑ j, M j' j * T i j l`. -/
def contract₂ (M : Matrix (Fin b') (Fin b) k) (T : Tensor k a b c) :
    Tensor k a b' c := fun i j' l => ∑ j, M j' j * T i j l

/-- Contraction of mode 3 by a matrix:
`contract₃ M T i j l' = ∑ l, M l' l * T i j l`. -/
def contract₃ (M : Matrix (Fin c') (Fin c) k) (T : Tensor k a b c) :
    Tensor k a b c' := fun i j l' => ∑ l, M l' l * T i j l

/-- Mode-2 contraction is mode-1 contraction conjugated by cyclic
rotations — definitionally. -/
theorem contract₂_eq_cyc (M : Matrix (Fin b') (Fin b) k) (T : Tensor k a b c) :
    contract₂ M T = cyc (cyc (contract₁ M (cyc T))) := rfl

/-- Mode-3 contraction is mode-1 contraction conjugated by cyclic
rotations — definitionally. -/
theorem contract₃_eq_cyc (M : Matrix (Fin c') (Fin c) k) (T : Tensor k a b c) :
    contract₃ M T = cyc (contract₁ M (cyc (cyc T))) := rfl

/-- Contracting mode 1 never increases rank: apply `M` to the mode-1
vectors of a decomposition. -/
theorem RankLE.contract₁ (M : Matrix (Fin a') (Fin a) k) {T : Tensor k a b c}
    {r : ℕ} (h : RankLE T r) : RankLE (contract₁ M T) r := by
  obtain ⟨u, v, w, rfl⟩ := h
  refine ⟨fun s i' => ∑ i, M i' i * u s i, v, w, ?_⟩
  funext i' j l
  show ∑ i, M i' i * ∑ s, u s i * v s j * w s l
      = ∑ s, (∑ i, M i' i * u s i) * v s j * w s l
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring

/-- Contracting mode 2 never increases rank. -/
theorem RankLE.contract₂ (M : Matrix (Fin b') (Fin b) k) {T : Tensor k a b c}
    {r : ℕ} (h : RankLE T r) : RankLE (contract₂ M T) r :=
  ((h.cyc.contract₁ M).cyc).cyc

/-- Contracting mode 3 never increases rank. -/
theorem RankLE.contract₃ (M : Matrix (Fin c') (Fin c) k) {T : Tensor k a b c}
    {r : ℕ} (h : RankLE T r) : RankLE (contract₃ M T) r :=
  (h.cyc.cyc.contract₁ M).cyc

theorem rank_contract₁_le (M : Matrix (Fin a') (Fin a) k) (T : Tensor k a b c) :
    rank (contract₁ M T) ≤ rank T :=
  rank_le_of_rankLE ((rankLE_rank T).contract₁ M)

theorem rank_contract₂_le (M : Matrix (Fin b') (Fin b) k) (T : Tensor k a b c) :
    rank (contract₂ M T) ≤ rank T :=
  rank_le_of_rankLE ((rankLE_rank T).contract₂ M)

theorem rank_contract₃_le (M : Matrix (Fin c') (Fin c) k) (T : Tensor k a b c) :
    rank (contract₃ M T) ≤ rank T :=
  rank_le_of_rankLE ((rankLE_rank T).contract₃ M)

@[simp] theorem contract₁_one (T : Tensor k a b c) :
    contract₁ (1 : Matrix (Fin a) (Fin a) k) T = T := by
  funext i j l
  simp [contract₁, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

@[simp] theorem contract₂_one (T : Tensor k a b c) :
    contract₂ (1 : Matrix (Fin b) (Fin b) k) T = T := by
  funext i j l
  simp [contract₂, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

@[simp] theorem contract₃_one (T : Tensor k a b c) :
    contract₃ (1 : Matrix (Fin c) (Fin c) k) T = T := by
  funext i j l
  simp [contract₃, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

/-- Contraction turns matrix multiplication into composition on mode 1. -/
theorem contract₁_mul (M : Matrix (Fin a'') (Fin a') k) (N : Matrix (Fin a') (Fin a) k)
    (T : Tensor k a b c) :
    contract₁ (M * N) T = contract₁ M (contract₁ N T) := by
  funext i j l
  simp only [contract₁, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- Contraction turns matrix multiplication into composition on mode 2. -/
theorem contract₂_mul (M : Matrix (Fin b'') (Fin b') k) (N : Matrix (Fin b') (Fin b) k)
    (T : Tensor k a b c) :
    contract₂ (M * N) T = contract₂ M (contract₂ N T) := by
  funext i j l
  simp only [contract₂, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- Contraction turns matrix multiplication into composition on mode 3. -/
theorem contract₃_mul (M : Matrix (Fin c'') (Fin c') k) (N : Matrix (Fin c') (Fin c) k)
    (T : Tensor k a b c) :
    contract₃ (M * N) T = contract₃ M (contract₃ N T) := by
  funext i j l
  simp only [contract₃, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- GL invariance on mode 1: contracting by an invertible matrix preserves
rank (`⅟M` contracts back). -/
theorem rank_contract₁_of_invertible (M : Matrix (Fin a) (Fin a) k) [Invertible M]
    (T : Tensor k a b c) : rank (contract₁ M T) = rank T := by
  refine le_antisymm (rank_contract₁_le M T) ?_
  have hM : contract₁ (⅟M) (contract₁ M T) = T := by
    rw [← contract₁_mul, invOf_mul_self, contract₁_one]
  calc rank T = rank (contract₁ (⅟M) (contract₁ M T)) := by rw [hM]
    _ ≤ rank (contract₁ M T) := rank_contract₁_le _ _

/-- GL invariance on mode 2. -/
theorem rank_contract₂_of_invertible (M : Matrix (Fin b) (Fin b) k) [Invertible M]
    (T : Tensor k a b c) : rank (contract₂ M T) = rank T := by
  refine le_antisymm (rank_contract₂_le M T) ?_
  have hM : contract₂ (⅟M) (contract₂ M T) = T := by
    rw [← contract₂_mul, invOf_mul_self, contract₂_one]
  calc rank T = rank (contract₂ (⅟M) (contract₂ M T)) := by rw [hM]
    _ ≤ rank (contract₂ M T) := rank_contract₂_le _ _

/-- GL invariance on mode 3. -/
theorem rank_contract₃_of_invertible (M : Matrix (Fin c) (Fin c) k) [Invertible M]
    (T : Tensor k a b c) : rank (contract₃ M T) = rank T := by
  refine le_antisymm (rank_contract₃_le M T) ?_
  have hM : contract₃ (⅟M) (contract₃ M T) = T := by
    rw [← contract₃_mul, invOf_mul_self, contract₃_one]
  calc rank T = rank (contract₃ (⅟M) (contract₃ M T)) := by rw [hM]
    _ ≤ rank (contract₃ M T) := rank_contract₃_le _ _

end Contract

/-! ## 4b. Linearity of mode contractions over subtraction -/

section ContractSub

variable {k : Type*} [CommRing k] {a b c a' b' c' : ℕ}

/-- Mode-1 contraction distributes over subtraction. -/
theorem contract₁_sub (M : Matrix (Fin a') (Fin a) k) (T T' : Tensor k a b c) :
    contract₁ M (T - T') = contract₁ M T - contract₁ M T' := by
  funext i' j l
  simp only [contract₁, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Mode-2 contraction distributes over subtraction. -/
theorem contract₂_sub (M : Matrix (Fin b') (Fin b) k) (T T' : Tensor k a b c) :
    contract₂ M (T - T') = contract₂ M T - contract₂ M T' := by
  funext i j' l
  simp only [contract₂, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Mode-3 contraction distributes over subtraction. -/
theorem contract₃_sub (M : Matrix (Fin c') (Fin c) k) (T T' : Tensor k a b c) :
    contract₃ M (T - T') = contract₃ M T - contract₃ M T' := by
  funext i j l'
  simp only [contract₃, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Triple contraction distributes over subtraction. -/
theorem contract_sub (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (T t : Tensor k a b c) :
    contract₁ M₁ (contract₂ M₂ (contract₃ M₃ (T - t)))
    = contract₁ M₁ (contract₂ M₂ (contract₃ M₃ T))
      - contract₁ M₁ (contract₂ M₂ (contract₃ M₃ t)) := by
  rw [contract₃_sub, contract₂_sub, contract₁_sub]

/-- If a triple contraction stabilizes both `T` and `t`, it stabilizes `T - t`. -/
theorem stab_residual (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (T t : Tensor k a b c)
    (hT : contract₁ M₁ (contract₂ M₂ (contract₃ M₃ T)) = T)
    (ht : contract₁ M₁ (contract₂ M₂ (contract₃ M₃ t)) = t) :
    contract₁ M₁ (contract₂ M₂ (contract₃ M₃ (T - t))) = T - t := by
  rw [contract_sub, hT, ht]

end ContractSub

/-! ## 5. Reindexing invariance -/

section ReindexDef

variable {k : Type*} {a b c a' b' c' : ℕ}

/-- Relabel each mode of a tensor along `Fin`-equivalences:
`reindex ea eb ec T i j l = T (ea.symm i) (eb.symm j) (ec.symm l)`. -/
def reindex (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b') (ec : Fin c ≃ Fin c')
    (T : Tensor k a b c) : Tensor k a' b' c' := fun i j l =>
  T (ea.symm i) (eb.symm j) (ec.symm l)

@[simp] theorem reindex_symm_reindex (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (ec : Fin c ≃ Fin c') (T : Tensor k a b c) :
    reindex ea.symm eb.symm ec.symm (reindex ea eb ec T) = T := by
  funext i j l
  simp [reindex]

end ReindexDef

section Reindex

variable {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}

/-- Rank-≤ is preserved by relabeling the modes: precompose every vector
of a decomposition with the inverse relabeling. -/
theorem RankLE.reindex (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (ec : Fin c ≃ Fin c') {T : Tensor k a b c} {r : ℕ} (h : RankLE T r) :
    RankLE (reindex ea eb ec T) r := by
  obtain ⟨u, v, w, rfl⟩ := h
  exact ⟨fun s i => u s (ea.symm i), fun s j => v s (eb.symm j),
         fun s l => w s (ec.symm l), rfl⟩

/-- Rank-≤ is invariant under relabeling the modes. -/
theorem rankLE_reindex_iff (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (ec : Fin c ≃ Fin c') {T : Tensor k a b c} {r : ℕ} :
    RankLE (reindex ea eb ec T) r ↔ RankLE T r := by
  constructor
  · intro h
    have h' := h.reindex ea.symm eb.symm ec.symm
    rwa [reindex_symm_reindex] at h'
  · exact fun h => h.reindex ea eb ec

/-- Rank is invariant under relabeling the modes. -/
@[simp] theorem rank_reindex (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (ec : Fin c ≃ Fin c') (T : Tensor k a b c) :
    rank (reindex ea eb ec T) = rank T :=
  le_antisymm
    (rank_le_of_rankLE ((rankLE_reindex_iff ea eb ec).mpr (rankLE_rank T)))
    (rank_le_of_rankLE ((rankLE_reindex_iff ea eb ec).mp (rankLE_rank _)))

end Reindex

end BilinearComplexity
