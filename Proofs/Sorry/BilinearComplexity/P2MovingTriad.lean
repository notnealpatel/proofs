import Sorry.BilinearComplexity.Sandwich
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace BilinearComplexity.P2Sweep

open Matrix

/-- Infinitesimal (Lie-algebra) stabilizer condition: `(X₁,X₂,X₃)` is a
derivation annihilating `T`. Over F₂ the triple `(α•1, β•1, (α+β)•1)`
satisfies this for every tensor — the 2-dimensional trivial space. -/
def InfStab {k : Type*} [CommSemiring k] {a b c : ℕ}
    (X₁ : Matrix (Fin a) (Fin a) k) (X₂ : Matrix (Fin b) (Fin b) k)
    (X₃ : Matrix (Fin c) (Fin c) k) (T : Tensor k a b c) : Prop :=
  ∀ i j l, (∑ i', X₁ i i' * T i' j l) + (∑ j', X₂ j j' * T i j' l)
    + (∑ l', X₃ l l' * T i j l') = 0

example : InfStab (0 : Matrix (Fin 1) (Fin 1) ℕ) (0 : Matrix (Fin 1) (Fin 1) ℕ)
    (0 : Matrix (Fin 1) (Fin 1) ℕ) (fun _ _ _ => 1) := by
  simp [InfStab]

private theorem binary (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem binary_add_self (x : ZMod 2) : x + x = 0 := by
  rcases binary x with h | h
  · simp [h]
  · subst x; decide

private theorem nonzero_coords {a b c : ℕ} (u : Fin a → ZMod 2)
    (v : Fin b → ZMod 2) (w : Fin c → ZMod 2) (ht : triad u v w ≠ 0) :
    ∃ i j l, u i = 1 ∧ v j = 1 ∧ w l = 1 := by
  classical
  by_contra h
  apply ht
  funext i j l
  rcases binary (u i) with hu | hu
  · simp [triad, hu]
  rcases binary (v j) with hv | hv
  · simp [triad, hv]
  rcases binary (w l) with hw | hw
  · simp [triad, hw]
  exact False.elim (h ⟨i,j,l,hu,hv,hw⟩)

private theorem kron_one {k : Type*} [CommSemiring k] (n : ℕ) :
    matKron (1 : Matrix (Fin n) (Fin n) k) (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext x y
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨s,t⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [matKron, Equiv.symm_apply_apply, Matrix.one_apply, Prod.ext_iff,
    finProdFinEquiv.injective.eq_iff]
  split_ifs <;> simp_all

private theorem kron_mul {k : Type*} [CommSemiring k] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) k) :
    matKron (A * B) (C * D) = matKron A C * matKron B D := by
  ext x y
  simp only [Matrix.mul_apply, matKron]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin n ≃ Fin (n*n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem kron_unit {n : ℕ} (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : A * A = 1) (hB : B * B = 1) : IsUnit (matKron A B) := by
  let K := matKron A B
  have hK : K * K = 1 := by rw [← kron_mul, hA, hB, kron_one]
  exact ⟨⟨K, K, hK, hK⟩, rfl⟩

private theorem left_action {k : Type*} [CommSemiring k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (u : Fin (n*n) → k) (i j : Fin n) :
    (∑ x, matKron A 1 (finProdFinEquiv (i,j)) x * u x) =
      ∑ s, A i s * u (finProdFinEquiv (s,j)) := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin n ≃ Fin (n*n))]
  simp [Fintype.sum_prod_type, matKron, Matrix.one_apply]

private theorem moving_contract₁ {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (u v w : Fin n → ZMod 2) :
    contract₁ M (triad u v w) = triad (fun i => ∑ s, M i s * u s) v w := by
  funext i j l
  simp only [contract₁, triad, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  ring

private theorem moving_contract₂ {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (u v w : Fin n → ZMod 2) :
    contract₂ M (triad u v w) = triad u (fun j => ∑ s, M j s * v s) w := by
  funext i j l
  simp only [contract₂, triad, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  ring

private theorem moving_contract₃ {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (u v w : Fin n → ZMod 2) :
    contract₃ M (triad u v w) = triad u v (fun l => ∑ s, M l s * w s) := by
  funext i j l
  simp only [contract₃, triad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

private theorem action_triad {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (ZMod 2)) (u v w : Fin n → ZMod 2) :
    sandwich A B C (triad u v w) =
    triad (fun i => ∑ s, A i s * u s) (fun j => ∑ s, B j s * v s)
      (fun l => ∑ s, C l s * w s) := by
  simp only [sandwich, moving_contract₃, moving_contract₂, moving_contract₁]

private theorem first_factor {n : ℕ} (u v w u' w' : Fin n → ZMod 2)
    (ht : triad u v w ≠ 0) (h : triad u' v w' = triad u v w) : u' = u := by
  obtain ⟨a,b,c,ha,hb,hc⟩ := nonzero_coords u v w ht
  have hslice := congrFun (congrFun (congrFun h a) b) c
  simp only [triad, ha, hb, hc, mul_one] at hslice
  have hw' : w' c = 1 := by
    rcases binary (w' c) with hz | ho
    · simp [hz] at hslice
    · exact ho
  funext i
  have hi := congrFun (congrFun (congrFun h i) b) c
  simpa [triad, hb, hc, hw'] using hi

/-- Every nonzero binary rank-one tensor is moved by an invertible stabilizer
of the square matrix multiplication tensor when the matrix size is at least two. -/
theorem p2_c3 (n : ℕ) (hn : 2 ≤ n) (u v w : Fin (n * n) → ZMod 2)
    (ht : triad u v w ≠ 0) :
    ∃ (M₁ M₂ M₃ : Matrix (Fin (n * n)) (Fin (n * n)) (ZMod 2)),
      IsUnit M₁ ∧ IsUnit M₂ ∧ IsUnit M₃ ∧
      sandwich M₁ M₂ M₃ (matMulTensor (ZMod 2) n n n) = matMulTensor (ZMod 2) n n n ∧
      sandwich M₁ M₂ M₃ (triad u v w) ≠ triad u v w := by
  classical
  obtain ⟨a,b,c,ha,hb,hc⟩ := nonzero_coords u v w ht
  obtain ⟨⟨s,q⟩, hsq⟩ := finProdFinEquiv.surjective a
  have hu : u (finProdFinEquiv (s,q)) = 1 := hsq ▸ ha
  let r : Fin n := if s = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hrs : r ≠ s := by
    dsimp [r]
    split_ifs with h
    · rw [h]; intro heq; have hv := congrArg Fin.val heq; simp at hv
    · exact Ne.symm h
  let E : Matrix (Fin n) (Fin n) (ZMod 2) :=
    Matrix.of fun i j => if i = r ∧ j = s then 1 else 0
  have hE : E * E = 0 := by
    funext i j
    rw [Matrix.mul_apply]
    change (∑ t, E i t * E t j) = 0
    apply Finset.sum_eq_zero
    intro t ht
    by_cases htr : t = r
    · subst t; simp [E, hrs]
    · simp [E, htr]
  let P := (1 : Matrix (Fin n) (Fin n) (ZMod 2)) + E
  have hP : P * P = 1 := by
    simp only [P, add_mul, mul_add, one_mul, mul_one, hE, add_zero]
    ext i j
    simp only [Matrix.add_apply]
    have hz := binary_add_self (E i j)
    rw [add_assoc, hz, add_zero]
  letI : Invertible P := ⟨P, hP, hP⟩
  letI : Invertible (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := invertibleOne
  have hinv : ⅟P = P := invOf_eq_right_inv hP
  have hPT : Pᵀ * Pᵀ = 1 := by rw [← transpose_mul, hP, transpose_one]
  refine ⟨matKron P 1, 1, matKron 1 Pᵀ,
    kron_unit P 1 hP (one_mul 1), isUnit_one,
    kron_unit 1 Pᵀ (one_mul 1) hPT, ?_, ?_⟩
  · simpa only [hinv, invOf_one, transpose_one, kron_one] using
      (p2_c1 P (1 : Matrix (Fin n) (Fin n) (ZMod 2))
        (1 : Matrix (Fin n) (Fin n) (ZMod 2)))
  · intro hfix
    rw [action_triad] at hfix
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at hfix
    have hf := first_factor u v w _ _ ht hfix
    have hr := congrFun hf (finProdFinEquiv (r,q))
    rw [left_action] at hr
    simp only [P, Matrix.add_apply, Matrix.one_apply, E, add_mul,
      Finset.sum_add_distrib, ite_mul, one_mul, zero_mul] at hr
    simp [hu] at hr

private theorem infStab_triad_of_sub {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (ZMod 2))
    (T t : Tensor (ZMod 2) n n n) (hT : InfStab A B C T)
    (hsub : InfStab A B C (T - t)) : InfStab A B C t := by
  intro i j l
  have h₁ := hT i j l
  have h₂ := hsub i j l
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h₂
  have heq :
      (∑ s, A i s * T s j l) - (∑ s, A i s * t s j l) +
      ((∑ s, B j s * T i s l) - (∑ s, B j s * t i s l)) +
      ((∑ s, C l s * T i j s) - (∑ s, C l s * t i j s)) =
      ((∑ s, A i s * T s j l) + (∑ s, B j s * T i s l) +
      (∑ s, C l s * T i j s)) -
      ((∑ s, A i s * t s j l) + (∑ s, B j s * t i s l) +
      (∑ s, C l s * t i j s)) := by ring
  rw [heq, h₁, zero_sub] at h₂
  exact neg_eq_zero.mp h₂

private theorem derivative_slice {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (ZMod 2)) (u v w : Fin n → ZMod 2)
    (h : InfStab A 0 C (triad u v w)) (b c : Fin n)
    (hb : v b = 1) (hc : w c = 1) (i : Fin n) :
    (∑ s, A i s * u s) + u i * (∑ s, C c s * w s) = 0 := by
  have hi := h i b c
  simp only [triad, hb, hc, mul_one, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero] at hi
  have heq : (∑ s, C c s * (u i * w s)) = u i * (∑ s, C c s * w s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rwa [heq] at hi

private theorem elementary_infStab (r s : Fin 2) :
    InfStab (matKron (Matrix.of (fun i j : Fin 2 =>
      if i = r ∧ j = s then (1 : ZMod 2) else 0)) (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)))
      0 (matKron (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
      (Matrix.of (fun i j : Fin 2 => if i = r ∧ j = s then (1 : ZMod 2) else 0))ᵀ)
      (matMulTensor (ZMod 2) 2 2 2) := by
  fin_cases r <;> fin_cases s <;> unfold InfStab <;> decide

/-- Some infinitesimal symmetry of binary two-by-two matrix multiplication
fails to stabilize the residual after any nonzero rank-one peel. -/
theorem p2_c9 (u v w : Fin (2 * 2) → ZMod 2) (ht : triad u v w ≠ 0) :
    ∃ (X₁ X₂ X₃ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) (ZMod 2)),
      InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 2 2 2) ∧
      ¬ InfStab X₁ X₂ X₃ (matMulTensor (ZMod 2) 2 2 2 - triad u v w) := by
  classical
  obtain ⟨a,b,c,ha,hb,hc⟩ := nonzero_coords u v w ht
  obtain ⟨⟨s,q⟩, hsq⟩ := finProdFinEquiv.surjective a
  have hu : u (finProdFinEquiv (s,q)) = 1 := hsq ▸ ha
  let r : Fin 2 := if s = 0 then 1 else 0
  have hrs : r ≠ s := by
    dsimp [r]
    split_ifs with h
    · rw [h]; decide
    · exact Ne.symm h
  let E : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    Matrix.of fun i j => if i = r ∧ j = s then 1 else 0
  let A := matKron E (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
  let C := matKron (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) Eᵀ
  have hT : InfStab A 0 C (matMulTensor (ZMod 2) 2 2 2) := elementary_infStab r s
  refine ⟨A, 0, C, hT, ?_⟩
  intro hsub
  have ht' := infStab_triad_of_sub A 0 C _ _ hT hsub
  have hs := derivative_slice A C u v w ht' b c hb hc (finProdFinEquiv (s,q))
  have hr := derivative_slice A C u v w ht' b c hb hc (finProdFinEquiv (r,q))
  change (∑ x, matKron E 1 (finProdFinEquiv (s,q)) x * u x) + _ = 0 at hs
  change (∑ x, matKron E 1 (finProdFinEquiv (r,q)) x * u x) + _ = 0 at hr
  rw [left_action] at hs hr
  simp [E, Ne.symm hrs, hu] at hs
  simp [E, hu, hs] at hr

example : 2 ≤ (2 : ℕ) ∧
    triad (fun _ : Fin (2*2) => (1 : ZMod 2)) (fun _ : Fin (2*2) => (1 : ZMod 2))
      (fun _ : Fin (2*2) => (1 : ZMod 2)) ≠ 0 := by
  constructor
  · decide
  · intro h
    have heq := congrFun (congrFun (congrFun h 0) 0) 0
    have hne : (1 : ZMod 2) ≠ 0 := by decide
    have heq' : (1 : ZMod 2) = 0 := by
      simpa only [triad, one_mul, Pi.zero_apply] using heq
    exact hne heq'

end BilinearComplexity.P2Sweep
