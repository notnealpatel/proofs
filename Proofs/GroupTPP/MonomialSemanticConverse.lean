import GroupTPP.MonomialRealization

set_option autoImplicit false

namespace GroupTPP.MonomialRealization

open Finset

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [DecidableEq G]
variable {n m p : ℕ}

omit [DecidableEq G] in
private lemma Phi_sum_left {ι : Type*} (s : Finset ι)
    (x : ι → MonoidAlgebra F G) (y z : MonoidAlgebra F G) :
    Phi (∑ t ∈ s, x t) y z = ∑ t ∈ s, Phi (x t) y z := by
  simp only [Phi, coeffOne, Finset.sum_mul, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]

omit [DecidableEq G] in
private lemma Phi_sum_middle {ι : Type*} (s : Finset ι)
    (x : MonoidAlgebra F G) (y : ι → MonoidAlgebra F G) (z : MonoidAlgebra F G) :
    Phi x (∑ t ∈ s, y t) z = ∑ t ∈ s, Phi x (y t) z := by
  simp only [Phi, coeffOne, Finset.mul_sum, Finset.sum_mul,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

omit [DecidableEq G] in
private lemma Phi_sum_right {ι : Type*} (s : Finset ι)
    (x y : MonoidAlgebra F G) (z : ι → MonoidAlgebra F G) :
    Phi x y (∑ t ∈ s, z t) = ∑ t ∈ s, Phi x y (z t) := by
  simp only [Phi, coeffOne, Finset.mul_sum, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]

/-- The coefficient identity implies the semantic identity for all matrices,
by distributing the finite sums and retaining exactly the diagonal triples. -/
theorem IsMonomialRealization.toSemanticMonomialRealization
    {a : Fin n → Fin m → G} {b : Fin m → Fin p → G} {c : Fin p → Fin n → G}
    {α : Fin n → Fin m → F} {β : Fin m → Fin p → F} {γ : Fin p → Fin n → F}
    (h : IsMonomialRealization a b c α β γ) :
    IsSemanticMonomialRealization a b c α β γ where
  alpha_ne_zero := h.alpha_ne_zero
  beta_ne_zero := h.beta_ne_zero
  gamma_ne_zero := h.gamma_ne_zero
  trilinear_identity := by
    intro A B C
    have expansion :
        Phi (phiA a α A) (phiB b β B) (phiC c γ C) =
          ∑ i, ∑ j, ∑ j', ∑ k, ∑ k', ∑ i',
            Phi (MonoidAlgebra.single (a i j) (A i j * α i j))
              (MonoidAlgebra.single (b j' k) (B j' k * β j' k))
              (MonoidAlgebra.single (c k' i') (C k' i' * γ k' i')) := by
      unfold phiA phiB phiC
      simp_rw [Phi_sum_left, Phi_sum_middle, Phi_sum_right]
    have summand : ∀ (i i' : Fin n) (j j' : Fin m) (k k' : Fin p),
        Phi (MonoidAlgebra.single (a i j) (A i j * α i j))
          (MonoidAlgebra.single (b j' k) (B j' k * β j' k))
          (MonoidAlgebra.single (c k' i') (C k' i' * γ k' i')) =
        (A i j * B j' k * C k' i') *
          (if j = j' ∧ k = k' ∧ i = i' then 1 else 0) := by
      intro i i' j j' k k'
      rw [Phi_single_single_single]
      calc
        _ = (A i j * B j' k * C k' i') *
            (α i j * β j' k * γ k' i' *
              (if a i j * b j' k * c k' i' = 1 then 1 else 0)) := by ring
        _ = _ := by rw [h.coeff_identity]
    rw [expansion]
    simp_rw [summand]
    have collapse :
        (∑ i, ∑ j, ∑ j', ∑ k, ∑ k', ∑ i',
          (A i j * B j' k * C k' i') *
            (if j = j' ∧ k = k' ∧ i = i' then 1 else 0)) =
        ∑ i, ∑ j, ∑ k, A i j * B j k * C k i := by
      simp [ite_and, mul_ite]
    rw [collapse]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]

example : IsMonomialRealization
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : Multiplicative ℤ))
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : Multiplicative ℤ))
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : Multiplicative ℤ))
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ))
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ))
    (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ)) where
  alpha_ne_zero := by intro i j; norm_num
  beta_ne_zero := by intro j k; norm_num
  gamma_ne_zero := by intro k i; norm_num
  coeff_identity := by
    intro i i' j j' k k'
    simp [Subsingleton.elim i i', Subsingleton.elim j j', Subsingleton.elim k k']

end GroupTPP.MonomialRealization
