import BilinearComplexity.P2MovingTriad
import BilinearComplexity.CyclicIntertwiners

set_option autoImplicit false

namespace BilinearComplexity.P2Sweep

open Matrix

private theorem packed_left_action (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (u : Fin (3 * 3) → ZMod 2) (i j : Fin 3) :
    (∑ x, matKron A 1 (finProdFinEquiv (i,j)) x * u x) =
      ∑ s, A i s * u (finProdFinEquiv (s,j)) := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3*3))]
  simp [Fintype.sum_prod_type, matKron, Matrix.one_apply]

private theorem packed_right_action (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (u : Fin (3 * 3) → ZMod 2) (i j : Fin 3) :
    (∑ x, matKron 1 Bᵀ (finProdFinEquiv (i,j)) x * u x) =
      ∑ s, u (finProdFinEquiv (i,s)) * B s j := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3*3))]
  simp [Fintype.sum_prod_type, matKron, Matrix.one_apply, mul_comm]

private theorem packed_difference_kills (A B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (u : Fin (3 * 3) → ZMod 2)
    (h : A * (Matrix.of (fun i j => u (finProdFinEquiv (i,j)))) =
      (Matrix.of (fun i j => u (finProdFinEquiv (i,j)))) * B) :
    ∀ x : Fin (3 * 3), ∑ y : Fin (3 * 3), ((matKron A 1 - matKron 1 Bᵀ) : Matrix (Fin (3*3)) (Fin (3*3)) (ZMod 2)) x y * u y = 0 := by
  intro x
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective x
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [packed_left_action, packed_right_action]
  have hij := congrArg (fun M => M i j) h
  exact sub_eq_zero.mpr hij

private theorem scalar_difference (A B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (r : ZMod 2) (h : matKron A 1 - matKron 1 Bᵀ = r • 1) :
    ∃ a b : ZMod 2, A = a • 1 ∧ B = b • 1 := by
  have he (i j p q : Fin 3) :
      A i p * (if j = q then 1 else 0) - (if i = p then 1 else 0) * B q j =
        r * (if i = p ∧ j = q then 1 else 0) := by
    have hh := congrArg (fun M => M (finProdFinEquiv (i,j)) (finProdFinEquiv (p,q))) h
    simpa only [Matrix.sub_apply, matKron, Equiv.symm_apply_apply,
      Matrix.transpose_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      finProdFinEquiv.injective.eq_iff, Prod.mk.injEq] using hh
  have hAoff (i p : Fin 3) (hip : i ≠ p) : A i p = 0 := by
    simpa [hip] using he i 0 p 0
  have hBoff (q j : Fin 3) (hqj : q ≠ j) : B q j = 0 := by
    have hh : - B q j = 0 := by simpa [Ne.symm hqj] using he 0 j 0 q
    exact neg_eq_zero.mp hh
  have hd (i j : Fin 3) : A i i - B j j = r := by simpa using he i j i j
  have hAd (i : Fin 3) : A i i = r + B 0 0 := (sub_eq_iff_eq_add).mp (hd i 0)
  have hBd (j : Fin 3) : B j j = B 0 0 :=
    sub_right_inj.mp ((hd 0 j).trans (hd 0 0).symm)
  refine ⟨r + B 0 0, B 0 0, ?_, ?_⟩
  · ext i p
    by_cases hip : i = p
    · subst p; simp [hAd]
    · simp [hAoff i p hip, hip]
  · ext q j
    by_cases hqj : q = j
    · subst j; simp [hBd]
    · simp [hBoff q j hqj, hqj]

private theorem cyclic_infStab (A B C : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    InfStab (matKron A 1 - matKron 1 Bᵀ)
      (matKron B 1 - matKron 1 Cᵀ) (matKron C 1 - matKron 1 Aᵀ)
      (matMulTensor (ZMod 2) 3 3 3) := by
  intro x y z
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨k,l⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨m,h⟩, rfl⟩ := finProdFinEquiv.surjective z
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp_rw [← Equiv.sum_comp (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3*3))]
  simp only [matKron, Nat.reduceMul, Equiv.symm_apply_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, matMulTensor, ite_and, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_const_zero, transpose_apply, ite_mul,
    one_mul, zero_mul]
  by_cases hjk : j = k <;> by_cases hlm : l = m <;> by_cases hhi : h = i
  all_goals
    simp only [(eq_comm : i = h ↔ h = i), (eq_comm : k = j ↔ j = k),
      (eq_comm : m = l ↔ l = m), hjk, hlm, hhi, if_true, if_false]
    ring

private theorem killed_triad_infStab
    (X Y Z : Matrix (Fin (3*3)) (Fin (3*3)) (ZMod 2))
    (u v w : Fin (3*3) → ZMod 2)
    (hu : ∀ i, ∑ s, X i s * u s = 0)
    (hv : ∀ j, ∑ s, Y j s * v s = 0)
    (hw : ∀ l, ∑ s, Z l s * w s = 0) : InfStab X Y Z (triad u v w) := by
  intro i j l
  have h₁ : (∑ s, X i s * triad u v w s j l) =
      (∑ s, X i s * u s) * v j * w l := by
    simp only [triad, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have h₂ : (∑ s, Y j s * triad u v w i s l) =
      u i * (∑ s, Y j s * v s) * w l := by
    simp only [triad, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have h₃ : (∑ s, Z l s * triad u v w i j s) =
      u i * v j * (∑ s, Z l s * w s) := by
    simp only [triad, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [h₁, h₂, h₃, hu i, hv j, hw l]
  ring

private theorem infStab_sub
    (X Y Z : Matrix (Fin (3*3)) (Fin (3*3)) (ZMod 2))
    (T t : Tensor (ZMod 2) (3*3) (3*3) (3*3))
    (hT : InfStab X Y Z T) (ht : InfStab X Y Z t) : InfStab X Y Z (T-t) := by
  intro i j l
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  calc
    _ = ((∑ s, X i s * T s j l) + (∑ s, Y j s * T i s l) +
        (∑ s, Z l s * T i j s)) -
        ((∑ s, X i s * t s j l) + (∑ s, Y j s * t i s l) +
        (∑ s, Z l s * t i j s)) := by ring
    _ = 0 := by rw [hT i j l, ht i j l, sub_self]

/-- Every binary three-by-three matrix multiplication tensor, after subtracting
an arbitrary rank-one triad (including zero), has an infinitesimal stabilizer
outside the two-dimensional scalar stabilizer space. -/
theorem p2_c8 (u v w : Fin (3*3) → ZMod 2) :
    ∃ X₁ X₂ X₃ : Matrix (Fin (3*3)) (Fin (3*3)) (ZMod 2),
      InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 3 3 3 - triad u v w) ∧
      ¬ ∃ α β : ZMod 2,
        X₁ = α • 1 ∧ X₂ = β • 1 ∧ X₃ = (α + β) • 1 := by
  let U : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => u (finProdFinEquiv (i,j))
  let V : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => v (finProdFinEquiv (i,j))
  let W : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => w (finProdFinEquiv (i,j))
  obtain ⟨A,B,C,hAB,hBC,hCA,hn⟩ := exists_nonscalar_cyclic_intertwiners U V W
  have hu := packed_difference_kills A B u hAB
  have hv := packed_difference_kills B C v hBC
  have hw := packed_difference_kills C A w hCA
  refine ⟨matKron A 1 - matKron 1 Bᵀ, matKron B 1 - matKron 1 Cᵀ,
    matKron C 1 - matKron 1 Aᵀ, ?_, ?_⟩
  · exact infStab_sub _ _ _ _ _ (cyclic_infStab A B C)
      (killed_triad_infStab _ _ _ u v w hu hv hw)
  · rintro ⟨α,β,h₁,h₂,h₃⟩
    obtain ⟨a,b,hA,hB⟩ := scalar_difference A B α h₁
    obtain ⟨b',c,hB',hC⟩ := scalar_difference B C β h₂
    exact hn ⟨a,b,c,hA,hB,hC⟩

example : Nonempty (Fin (3*3)) := ⟨0⟩

example : ∃ X₁ X₂ X₃ : Matrix (Fin (3*3)) (Fin (3*3)) (ZMod 2),
    InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 3 3 3) ∧
    ¬ ∃ α β : ZMod 2, X₁ = α • 1 ∧ X₂ = β • 1 ∧ X₃ = (α + β) • 1 := by
  have hz : triad (fun _ : Fin (3*3) => (0 : ZMod 2))
      (fun _ : Fin (3*3) => (0 : ZMod 2)) (fun _ : Fin (3*3) => (0 : ZMod 2)) = 0 := by
    funext i j l
    simp [triad]
  have h := p2_c8 (fun _ => 0) (fun _ => 0) (fun _ => 0)
  rw [hz, sub_zero] at h
  exact h

example : ∃ X₁ X₂ X₃ : Matrix (Fin (3*3)) (Fin (3*3)) (ZMod 2),
    InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 3 3 3 - (fun _ _ _ => 1)) ∧
    ¬ ∃ α β : ZMod 2, X₁ = α • 1 ∧ X₂ = β • 1 ∧ X₃ = (α + β) • 1 := by
  have ho : triad (fun _ : Fin (3*3) => (1 : ZMod 2))
      (fun _ : Fin (3*3) => (1 : ZMod 2)) (fun _ : Fin (3*3) => (1 : ZMod 2)) =
      (fun _ _ _ => 1) := by
    funext i j l
    simp [triad]
  have h := p2_c8 (fun _ => 1) (fun _ => 1) (fun _ => 1)
  rw [ho] at h
  exact h

end BilinearComplexity.P2Sweep
