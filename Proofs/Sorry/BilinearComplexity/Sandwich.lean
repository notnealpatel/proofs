import BilinearComplexity.RankCalculus

set_option autoImplicit false

namespace BilinearComplexity.P2Sweep

open Matrix

/-- Kronecker product of matrices, packed row-major by `finProdFinEquiv`
(first component slow), matching the packing of `matMulTensor` and `kron`. -/
def matKron {k : Type*} [Mul k] {a b a' b' : ℕ} (M : Matrix (Fin a) (Fin b) k)
    (N : Matrix (Fin a') (Fin b') k) : Matrix (Fin (a * a')) (Fin (b * b')) k :=
  fun i j => M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    * N (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

/-- Simultaneous contraction of all three modes. -/
def sandwich {k : Type*} [CommSemiring k] {a b c : ℕ}
    (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (T : Tensor k a b c) : Tensor k a b c :=
  contract₁ M₁ (contract₂ M₂ (contract₃ M₃ T))

example : matKron (fun _ _ : Fin 1 => (2 : ℕ)) (fun _ _ : Fin 1 => (3 : ℕ))
    0 0 = 6 := rfl

example : sandwich (fun _ _ : Fin 1 => (2 : ℕ)) (fun _ _ : Fin 1 => (3 : ℕ))
    (fun _ _ : Fin 1 => (4 : ℕ)) (fun _ _ _ => 5) 0 0 0 = 120 := by
  simp [sandwich, contract₁, contract₂, contract₃]

/-- The matrix multiplication indicator collapses a sandwich to three input sums. -/
private theorem sandwich_matMulTensor_sum {k : Type*} [CommSemiring k] {a b c : ℕ}
    (P : Matrix (Fin a) (Fin a) k) (Q : Matrix (Fin b) (Fin b) k)
    (R : Matrix (Fin c) (Fin c) k) (PI : Matrix (Fin a) (Fin a) k)
    (QI : Matrix (Fin b) (Fin b) k) (RI : Matrix (Fin c) (Fin c) k)
    (x : Fin (a*b)) (y : Fin (b*c)) (z : Fin (c*a)) :
    sandwich (matKron P QIᵀ) (matKron Q RIᵀ) (matKron R PIᵀ)
      (matMulTensor k a b c) x y z =
    ∑ i : Fin a, ∑ j : Fin b, ∑ l : Fin c,
      (P (finProdFinEquiv.symm x).1 i * QI j (finProdFinEquiv.symm x).2) *
      ((Q (finProdFinEquiv.symm y).1 j * RI l (finProdFinEquiv.symm y).2) *
      (R (finProdFinEquiv.symm z).1 l * PI i (finProdFinEquiv.symm z).2)) := by
  simp only [sandwich, contract₁, contract₂, contract₃]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin a × Fin b ≃ Fin (a*b))]
  simp only [Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp (finProdFinEquiv : Fin b × Fin c ≃ Fin (b*c))]
  simp_rw [← Equiv.sum_comp (finProdFinEquiv : Fin c × Fin a ≃ Fin (c*a))]
  simp only [Fintype.sum_prod_type, matKron, matMulTensor, transpose_apply,
    Equiv.symm_apply_apply, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.sum_const_zero, Finset.mem_univ, if_true, Finset.mul_sum]

/-- Invertible changes of matrix bases in the three factors fix the rectangular
matrix multiplication tensor, including when any dimension is zero. -/
theorem p2_c1 {k : Type*} [CommSemiring k] {a b c : ℕ}
    (P : Matrix (Fin a) (Fin a) k) (Q : Matrix (Fin b) (Fin b) k)
    (R : Matrix (Fin c) (Fin c) k) [Invertible P] [Invertible Q] [Invertible R] :
    sandwich (matKron P (⅟Q)ᵀ) (matKron Q (⅟R)ᵀ) (matKron R (⅟P)ᵀ)
      (matMulTensor k a b c) = matMulTensor k a b c := by
  funext x y z
  rw [sandwich_matMulTensor_sum]
  have hfactor :
      (∑ i : Fin a, ∑ j : Fin b, ∑ l : Fin c,
        (P (finProdFinEquiv.symm x).1 i * (⅟Q) j (finProdFinEquiv.symm x).2) *
        ((Q (finProdFinEquiv.symm y).1 j * (⅟R) l (finProdFinEquiv.symm y).2) *
        (R (finProdFinEquiv.symm z).1 l * (⅟P) i (finProdFinEquiv.symm z).2))) =
      (R * ⅟R) (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm y).2 *
      (Q * ⅟Q) (finProdFinEquiv.symm y).1 (finProdFinEquiv.symm x).2 *
      (P * ⅟P) (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm z).2 := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hfactor, mul_invOf_self, mul_invOf_self, mul_invOf_self]
  simp only [Matrix.one_apply, matMulTensor]
  split_ifs <;> simp_all

/-- Contraction in mode 1 commutes with the packed Kronecker product. -/
theorem contract₁_matKron {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}
    (M : Matrix (Fin a) (Fin a) k) (N : Matrix (Fin a') (Fin a') k)
    (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    contract₁ (matKron M N) (kron T T') = kron (contract₁ M T) (contract₁ N T') := by
  funext i j l
  simp only [contract₁, kron, matKron]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin a × Fin a' ≃ Fin (a*a'))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  ring
/-- Contraction in mode 2 commutes with the packed Kronecker product. -/
theorem contract₂_matKron {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}
    (M : Matrix (Fin b) (Fin b) k) (N : Matrix (Fin b') (Fin b') k)
    (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    contract₂ (matKron M N) (kron T T') = kron (contract₂ M T) (contract₂ N T') := by
  funext i j l
  simp only [contract₂, kron, matKron]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin b × Fin b' ≃ Fin (b*b'))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  ring
/-- Contraction in mode 3 commutes with the packed Kronecker product. -/
theorem contract₃_matKron {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}
    (M : Matrix (Fin c) (Fin c) k) (N : Matrix (Fin c') (Fin c') k)
    (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    contract₃ (matKron M N) (kron T T') = kron (contract₃ M T) (contract₃ N T') := by
  funext i j l
  simp only [contract₃, kron, matKron]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin c × Fin c' ≃ Fin (c*c'))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Sandwiching commutes with Kronecker products of the acting matrices and tensors. -/
theorem sandwich_matKron {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}
    (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (N₁ : Matrix (Fin a') (Fin a') k)
    (N₂ : Matrix (Fin b') (Fin b') k) (N₃ : Matrix (Fin c') (Fin c') k)
    (T : Tensor k a b c) (T' : Tensor k a' b' c') :
    sandwich (matKron M₁ N₁) (matKron M₂ N₂) (matKron M₃ N₃) (kron T T') =
      kron (sandwich M₁ M₂ M₃ T) (sandwich N₁ N₂ N₃ T') := by
  simp only [sandwich, contract₃_matKron, contract₂_matKron, contract₁_matKron]

/-- Stabilizing triples multiply under the packed Kronecker product. -/
theorem p2_c2 {k : Type*} [CommSemiring k] {a b c a' b' c' : ℕ}
    (M₁ : Matrix (Fin a) (Fin a) k) (M₂ : Matrix (Fin b) (Fin b) k)
    (M₃ : Matrix (Fin c) (Fin c) k) (N₁ : Matrix (Fin a') (Fin a') k)
    (N₂ : Matrix (Fin b') (Fin b') k) (N₃ : Matrix (Fin c') (Fin c') k)
    (T : Tensor k a b c) (T' : Tensor k a' b' c')
    (hT : sandwich M₁ M₂ M₃ T = T) (hT' : sandwich N₁ N₂ N₃ T' = T') :
    sandwich (matKron M₁ N₁) (matKron M₂ N₂) (matKron M₃ N₃) (kron T T')
      = kron T T' := by
  rw [sandwich_matKron, hT, hT']

example : Nonempty (Invertible (1 : Matrix (Fin 1) (Fin 1) ℕ) ×
    Invertible (1 : Matrix (Fin 1) (Fin 1) ℕ) ×
    Invertible (1 : Matrix (Fin 1) (Fin 1) ℕ)) :=
  ⟨invertibleOne, invertibleOne, invertibleOne⟩

example :
    sandwich (1 : Matrix (Fin 1) (Fin 1) ℕ)
      (1 : Matrix (Fin 1) (Fin 1) ℕ) (1 : Matrix (Fin 1) (Fin 1) ℕ) (fun _ _ _ => 1) = (fun _ _ _ => 1) ∧
    sandwich (1 : Matrix (Fin 1) (Fin 1) ℕ)
      (1 : Matrix (Fin 1) (Fin 1) ℕ) (1 : Matrix (Fin 1) (Fin 1) ℕ) (fun _ _ _ => 2) = (fun _ _ _ => 2) := by
  constructor <;> funext i j l <;>
    simp [sandwich, contract₁, contract₂, contract₃, Matrix.one_apply,
      Subsingleton.elim i 0, Subsingleton.elim j 0, Subsingleton.elim l 0]

/-- A single rank-one triad `u ⊗ v ⊗ w`. -/
def triad {k : Type*} [Mul k] {a b c : ℕ} (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) : Tensor k a b c := fun i j l => u i * v j * w l

/-- The vectorized identity matrix, `vec(Iₙ)` in row-major packing. -/
def vecI (k : Type*) [Zero k] [One k] (n : ℕ) : Fin (n * n) → k :=
  fun x => if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm x).2 then 1 else 0

/-- The identity triad `vec(Iₙ) ⊗ vec(Iₙ) ⊗ vec(Iₙ)` — the distinguished
symmetry-fixed term of both the Strassen and Smirnov-1 decompositions. -/
def identityTriad (k : Type*) [CommSemiring k] (n : ℕ) :
    Tensor k (n * n) (n * n) (n * n) :=
  triad (vecI k n) (vecI k n) (vecI k n)


example : triad (fun _ : Fin 1 => (2 : ℕ)) (fun _ : Fin 1 => 3)
    (fun _ : Fin 1 => 4) 0 0 0 = 24 := rfl

example : vecI ℕ 2 (finProdFinEquiv (0, 0)) = 1 := rfl
example : vecI ℕ 2 (finProdFinEquiv (0, 1)) = 0 := rfl
example : identityTriad ℕ 1 0 0 0 = 1 := rfl

/-- The diagonal packed change of basis fixes the vectorized identity. -/
theorem matKron_mul_vecI {k : Type*} [CommSemiring k] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) k) [Invertible P] (x : Fin (n * n)) :
    (∑ y, matKron P (⅟P)ᵀ x y * vecI k n y) = vecI k n x := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n))]
  simp only [Fintype.sum_prod_type, matKron, vecI, Equiv.symm_apply_apply,
    transpose_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  change (P * ⅟P) (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 = _
  rw [mul_invOf_self]
  rfl

/-- Contracting the first vector of a triad contracts its first tensor mode. -/
private theorem contract₁_triad {k : Type*} [CommSemiring k] {a b c : ℕ}
    (M : Matrix (Fin a) (Fin a) k) (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) :
    contract₁ M (triad u v w) = triad (fun i => ∑ s, M i s * u s) v w := by
  funext i j l
  simp only [contract₁, triad, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Contracting the second vector of a triad contracts its second tensor mode. -/
private theorem contract₂_triad {k : Type*} [CommSemiring k] {a b c : ℕ}
    (M : Matrix (Fin b) (Fin b) k) (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) :
    contract₂ M (triad u v w) = triad u (fun j => ∑ s, M j s * v s) w := by
  funext i j l
  simp only [contract₂, triad, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Contracting the third vector of a triad contracts its third tensor mode. -/
private theorem contract₃_triad {k : Type*} [CommSemiring k] {a b c : ℕ}
    (M : Matrix (Fin c) (Fin c) k) (u : Fin a → k) (v : Fin b → k)
    (w : Fin c → k) :
    contract₃ M (triad u v w) = triad u v (fun l => ∑ s, M l s * w s) := by
  funext i j l
  simp only [contract₃, triad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- The diagonal sandwich fixes the identity triad in every dimension. -/
theorem sandwich_identityTriad {k : Type*} [CommSemiring k] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) k) [Invertible P] :
    sandwich (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ)
      (identityTriad k n) = identityTriad k n := by
  simp only [sandwich, identityTriad, contract₃_triad, contract₂_triad,
    contract₁_triad, matKron_mul_vecI]

/-- The diagonal sandwich fixes the residual obtained by subtracting the identity
triad from the square matrix multiplication tensor. -/
theorem p2_c4 {k : Type*} [CommRing k] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) k) [Invertible P] :
    sandwich (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ)
        (matMulTensor k n n n - identityTriad k n)
      = matMulTensor k n n n - identityTriad k n := by
  exact stab_residual (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ) (matKron P (⅟P)ᵀ)
    (matMulTensor k n n n) (identityTriad k n)
    (p2_c1 P P P) (sandwich_identityTriad n P)

example : Nonempty (Invertible (1 : Matrix (Fin 2) (Fin 2) ℤ)) := ⟨invertibleOne⟩
example : (matMulTensor ℤ 2 2 2 - identityTriad ℤ 2)
    (finProdFinEquiv (0, 1)) (finProdFinEquiv (1, 0)) (finProdFinEquiv (0, 0)) = 1 := rfl

end BilinearComplexity.P2Sweep
