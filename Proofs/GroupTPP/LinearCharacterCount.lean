import GroupTPP.CharDegreesComm
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.GroupTheory.Abelianization.Defs

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.CharDegrees

private theorem single_one_sum {n : ℕ} (d : Fin n → ℕ) :
    (∑ i, Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) = 1 := by
  classical
  ext i a b
  simp

private theorem selected_block {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)]
    (f : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] ℂ) :
    ∃ i : Fin n, d i = 1 ∧ ∀ x, f x = x i ⟨0, Nat.pos_of_neZero _⟩ ⟨0, Nat.pos_of_neZero _⟩ := by
  classical
  have hex : ∃ i, f (Pi.single i 1) ≠ 0 := by
    by_contra h
    have hz : ∀ i, f (Pi.single i 1) = 0 := by simpa using h
    have hs := congrArg f (single_one_sum d)
    simp [map_sum, hz] at hs
  obtain ⟨i, hi⟩ := hex
  have hid : f (Pi.single i 1) = 1 := by
    have he : f (Pi.single i 1) * f (Pi.single i 1) = f (Pi.single i 1) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    exact (mul_eq_left₀ hi).mp he
  have hmul (x : Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
      Pi.single i 1 * x = Pi.single i (x i) := by
    ext j a b
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  have hfactor (x : Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
      f x = f (Pi.single i (x i)) := by
    rw [← hmul, map_mul, hid, one_mul]
  let g : Matrix (Fin (d i)) (Fin (d i)) ℂ →ₐ[ℂ] ℂ :=
    { toFun := fun A => f (Pi.single i A)
      map_zero' := by simp
      map_one' := hid
      map_add' := fun A B => by rw [Pi.single_add, map_add]
      map_mul' := fun A B => by rw [Pi.single_mul, map_mul]
      commutes' := fun r => by
        have h := hfactor (algebraMap ℂ (Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) r)
        exact h.symm.trans (f.commutes r) }
  haveI : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_neZero _⟩⟩
  have hinj := g.toRingHom.injective
  have hle : d i ≤ 1 := CharDegreesComm.matrix_comm_imp_dim_le_one (fun A B =>
    hinj (by simp only [map_mul]; exact mul_comm _ _))
  have hd : d i = 1 := by have hp := Nat.pos_of_neZero (d i); omega
  refine ⟨i, hd, ?_⟩
  intro x
  have hscalar : x i = algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (x i ⟨0, Nat.pos_of_neZero _⟩ ⟨0, Nat.pos_of_neZero _⟩) := by
    ext a b
    have ha : a = ⟨0, Nat.pos_of_neZero _⟩ := Fin.ext (by have h := a.isLt; omega)
    have hb : b = ⟨0, Nat.pos_of_neZero _⟩ := Fin.ext (by have h := b.isLt; omega)
    subst a; subst b
    simp [Algebra.algebraMap_eq_smul_one]
  calc f x = g (x i) := hfactor x
    _ = _ := by rw [hscalar, g.commutes]; rfl

/-- Evaluation on a matrix block of dimension one is a complex algebra homomorphism. -/
private noncomputable def blockEval {n : ℕ} (d : Fin n → ℕ)
    (i : {i // d i = 1}) : (Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) →ₐ[ℂ] ℂ := by
  classical
  let z : Fin (d i.val) := ⟨0, by rw [i.property]; decide⟩
  have huniv : (Finset.univ : Finset (Fin (d i.val))) = {z} := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Fin.ext
    have ha := a.isLt
    have hd := i.property
    change a.val = 0
    omega
  exact
    { toFun := fun x => x i.val z z
      map_zero' := rfl
      map_one' := by simp
      map_add' := fun _ _ => rfl
      map_mul' := fun x y => by
        simp only [Pi.mul_apply, Matrix.mul_apply, huniv, Finset.sum_singleton]
      commutes' := fun r => by simp [Algebra.algebraMap_eq_smul_one] }

private theorem blockEval_apply {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)]
    (i : {i // d i = 1}) (x : Π j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    blockEval d i x = x i.val ⟨0, Nat.pos_of_neZero _⟩ ⟨0, Nat.pos_of_neZero _⟩ := rfl

private theorem blockEval_bijective {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)] :
    Function.Bijective (blockEval d) := by
  classical
  constructor
  · intro i j h
    apply Subtype.ext
    by_contra hij
    have he := congrArg (fun f => f (Pi.single i.val 1)) h
    rw [blockEval_apply, blockEval_apply] at he
    simp [Pi.single_eq_of_ne (show j.val ≠ i.val from fun hji => hij hji.symm)] at he
  · intro f
    obtain ⟨i, hi, hf⟩ := selected_block d f
    refine ⟨⟨i, hi⟩, ?_⟩
    ext x
    exact (blockEval_apply d ⟨i, hi⟩ x).trans (hf x).symm

/-- The number of one-dimensional irreducible complex characters equals the
number of complex algebra homomorphisms from the group algebra to the scalars. -/
theorem count_one_charDegrees_eq_card_algHom (G : Type*) [Group G] [Fintype G] :
    (charDegrees G).count 1 = Nat.card (MonoidAlgebra ℂ G →ₐ[ℂ] ℂ) := by
  classical
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  haveI := hd
  have hcount : (Finset.univ.val.map d).count 1 = Nat.card {i // d i = 1} := by
    rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [eq_comm (a := 1), ← Finset.filter_val]
    rfl
  rw [charDegrees_eq_of_algEquiv G e, hcount]
  calc Nat.card {i // d i = 1} =
      Nat.card ((Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] ℂ) :=
        Nat.card_congr (Equiv.ofBijective (blockEval d) (blockEval_bijective d))
    _ = Nat.card (MonoidAlgebra ℂ G →ₐ[ℂ] ℂ) :=
      (Nat.card_congr (e.arrowCongr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ))).symm

example : (charDegrees Unit).count 1 = 1 := by
  rw [CharDegreesComm.charDegrees_of_commGroup]
  simp

example : Nonempty (MonoidAlgebra ℂ Unit →ₐ[ℂ] ℂ) :=
  ⟨MonoidAlgebra.lift ℂ ℂ Unit (1 : Unit →* ℂ)⟩

/-- A complex-valued homomorphism from a group has unit-valued image. -/
private def complexHomUnitsEquiv (G : Type*) [Group G] :
    (G →* ℂ) ≃ (G →* ℂˣ) where
  toFun := MonoidHom.toHomUnits
  invFun := fun f => (Units.coeHom ℂ).comp f
  left_inv f := by
    ext g
    rfl
  right_inv f := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    rfl

private theorem complexHomUnitsEquiv_apply (G : Type*) [Group G]
    (f : G →* ℂ) (g : G) :
    (complexHomUnitsEquiv G f g : ℂ) = f g := rfl

/-- The number of one-dimensional irreducible complex characters of a finite
group is the order of its abelianization, the quotient by its commutator subgroup. -/
theorem count_one_charDegrees_eq_card_abelianization (G : Type*) [Group G] [Fintype G] :
    (charDegrees G).count 1 = Nat.card (G ⧸ commutator G) := by
  classical
  letI : Fintype (Abelianization G) := Fintype.ofFinite _
  let e : (MonoidAlgebra ℂ G →ₐ[ℂ] ℂ) ≃
      (MonoidAlgebra ℂ (Abelianization G) →ₐ[ℂ] ℂ) :=
    (MonoidAlgebra.lift ℂ ℂ G).symm |>.trans (complexHomUnitsEquiv G)
      |>.trans (Abelianization.lift (G := G) (A := ℂˣ))
      |>.trans (complexHomUnitsEquiv (Abelianization G)).symm
      |>.trans (MonoidAlgebra.lift ℂ ℂ (Abelianization G))
  calc (charDegrees G).count 1 = Nat.card (MonoidAlgebra ℂ G →ₐ[ℂ] ℂ) :=
      count_one_charDegrees_eq_card_algHom G
    _ = Nat.card (MonoidAlgebra ℂ (Abelianization G) →ₐ[ℂ] ℂ) := Nat.card_congr e
    _ = (charDegrees (Abelianization G)).count 1 :=
      (count_one_charDegrees_eq_card_algHom (Abelianization G)).symm
    _ = Nat.card (Abelianization G) := by
      rw [CharDegreesComm.charDegrees_of_commGroup]
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card (G ⧸ commutator G) := rfl

example : (charDegrees Unit).count 1 = Nat.card (Unit ⧸ commutator Unit) :=
  count_one_charDegrees_eq_card_abelianization Unit

end GroupTPP.CharDegrees
