import Sorry.Quarantine.GroupTPP.STPPWreath
import Sorry.GroupTPP.IsoclinismInvariants

set_option autoImplicit false

open scoped BigOperators

namespace GroupTPP.STPPWreath

/-- Multiply the coordinate classes in the abelianization of the base group. -/
noncomputable def wreathBaseAbelianization (D : Type*) [Group D] (n : ℕ) :
    (Fin n → D) →* Abelianization D where
  toFun f := ∏ i, Abelianization.of (f i)
  map_one' := by simp
  map_mul' f g := by simp [Finset.prod_mul_distrib]

example (D : Type*) [Group D] (n : ℕ) :
    wreathBaseAbelianization D n 1 = 1 := map_one _

/-- The product of the coordinate classes is invariant under permutation. -/
theorem wreathBaseAbelianization_perm (D : Type*) [Group D] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (f : Fin n → D) :
    wreathBaseAbelianization D n (permArrowHom D n σ f) =
      wreathBaseAbelianization D n f := by
  change (∏ i, Abelianization.of (f (σ.symm i))) = ∏ i, Abelianization.of (f i)
  exact Equiv.prod_comp σ.symm (fun i => Abelianization.of (f i))

/-- The abelian coordinate product and permutation sign homomorphism. -/
noncomputable def wreathAbelianizationMap (D : Type*) [Group D] (n : ℕ) :
    ImprimitiveWreathProduct D n →* Abelianization D × ℤˣ where
  toFun x := (wreathBaseAbelianization D n x.left, Equiv.Perm.sign x.right)
  map_one' := by simp
  map_mul' x y := by
    apply Prod.ext
    · change wreathBaseAbelianization D n (x.left * permArrowHom D n x.right y.left) = _
      rw [map_mul, wreathBaseAbelianization_perm]
      rfl
    · exact map_mul Equiv.Perm.sign x.right y.right

example (D : Type*) [Group D] (n : ℕ) : wreathAbelianizationMap D n 1 = 1 :=
  map_one _

/-- Supported base coordinates contribute exactly their own abelian class. -/
theorem wreathBaseAbelianization_mulSingle (D : Type*) [Group D] (n : ℕ)
    (i : Fin n) (d : D) :
    wreathBaseAbelianization D n (Pi.mulSingle i d) = Abelianization.of d := by
  classical
  simp only [wreathBaseAbelianization, MonoidHom.coe_mk, OneHom.coe_mk,
    Pi.mulSingle_apply, apply_ite, map_one]
  simp

/-- The map to coordinate classes and sign is onto once there are two coordinates. -/
theorem wreathAbelianizationMap_surjective (D : Type*) [Group D] (n : ℕ)
    (hn : 2 ≤ n) : Function.Surjective (wreathAbelianizationMap D n) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro x
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective x.1
  obtain ⟨σ, hσ⟩ := Equiv.Perm.sign_surjective (α := Fin n) x.2
  let i : Fin n := ⟨0, by omega⟩
  refine ⟨⟨Pi.mulSingle i d, σ⟩, ?_⟩
  apply Prod.ext
  · exact (wreathBaseAbelianization_mulSingle D n i d).trans hd
  · exact hσ


open Equiv Equiv.Perm

private theorem threeCycle_map_eq_one {n : ℕ} {A : Type*} [CommGroup A] (F : Perm (Fin n) →* A)
    (σ : Perm (Fin n)) (hσ : σ.IsThreeCycle) : F σ = 1 := by
  have hs : σ.support.Nonempty := Finset.card_pos.mp (by rw [hσ.card_support]; decide)
  obtain ⟨a, ha⟩ := hs
  have hn := hσ.nodup_iff_mem_support.mpr ha
  have hnd : (a ≠ σ a ∧ a ≠ σ (σ a)) ∧ a ≠ σ a := by simpa using hn
  have hab : a ≠ σ a := hnd.1.1
  have hbc : σ a ≠ σ (σ a) := fun h => hab (σ.injective h)
  have heq := swap_mul_swap_mul_swap (x := σ a) (y := a) (z := σ (σ a)) hab.symm hbc
  have hcancel : F (swap a (σ (σ a))) * F (swap a (σ (σ a))) = 1 := by
    rw [← map_mul]; simp
  have hswap : F (swap (σ a) (σ (σ a))) = F (swap a (σ a)) := by
    rw [swap_comm (σ a) (σ (σ a))]
    rw [← heq, map_mul, map_mul, mul_comm (F (swap a (σ (σ a)))), mul_assoc,
      hcancel, mul_one, swap_comm (σ a) a]
  rw [hσ.eq_swap_mul_swap_iff_mem_support.mpr ha, map_mul, hswap, ← map_mul]
  simp

/-- An abelian image kills every even permutation, including in degrees below five. -/
theorem even_perm_map_eq_one {n : ℕ} {A : Type*} [CommGroup A]
    (F : Perm (Fin n) →* A) (σ : Perm (Fin n)) (hσ : sign σ = 1) : F σ = 1 := by
  have hle : alternatingGroup (Fin n) ≤ F.ker := by
    rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro τ hτ
    exact MonoidHom.mem_ker.mpr (threeCycle_map_eq_one F τ hτ)
  exact MonoidHom.mem_ker.mp (hle (mem_alternatingGroup.mpr hσ))


/-- All supported copies of a base element coincide in an abelian image of the wreath product. -/
theorem wreath_coordinate_map_eq {D A : Type*} [Group D] [CommGroup A] {n : ℕ}
    (F : ImprimitiveWreathProduct D n →* A) (i j : Fin n) (d : D) :
    F (SemidirectProduct.inl (Pi.mulSingle i d)) =
      F (SemidirectProduct.inl (Pi.mulSingle j d)) := by
  let σ := Equiv.swap i j
  have hperm : permArrowHom D n σ (Pi.mulSingle i d) = Pi.mulSingle j d := by
    funext k
    simp only [permArrowHom, MonoidHom.coe_mk, OneHom.coe_mk,
      MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, Pi.mulSingle_apply]
    simp only [Equiv.symm_apply_eq, show σ i = j from Equiv.swap_apply_left i j]
  have hconj := congrArg F (SemidirectProduct.inl_aut (φ := permArrowHom D n) σ
    (Pi.mulSingle i d))
  rw [hperm] at hconj
  simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using hconj.symm

/-- On the base subgroup, an abelian image factors through the product of base classes. -/
theorem wreath_base_map_factor {D A : Type*} [Group D] [CommGroup A] {n : ℕ}
    (F : ImprimitiveWreathProduct D n →* A) (j : Fin n) :
    F.comp SemidirectProduct.inl =
      (Abelianization.lift (F.comp (SemidirectProduct.inl.comp (MonoidHom.mulSingle (fun _ : Fin n => D) j)))).comp
        (wreathBaseAbelianization D n) := by
  apply MonoidHom.pi_ext
  intro i d
  simp only [MonoidHom.comp_apply, wreathBaseAbelianization_mulSingle,
    Abelianization.lift_apply_of, MonoidHom.mulSingle_apply]
  exact wreath_coordinate_map_eq F i j d

/-- Every embedded even permutation belongs to the wreath commutator subgroup. -/
theorem wreath_inr_mem_commutator {D : Type*} [Group D] {n : ℕ}
    (σ : Perm (Fin n)) (hσ : sign σ = 1) :
    (SemidirectProduct.inr σ : ImprimitiveWreathProduct D n) ∈
      commutator (ImprimitiveWreathProduct D n) := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact even_perm_map_eq_one (Abelianization.of.comp SemidirectProduct.inr) σ hσ

/-- The wreath commutator is exactly the kernel of the base-class product and sign. -/
theorem wreathAbelianizationMap_ker (D : Type*) [Group D] (n : ℕ) (hn : 2 ≤ n) :
    (wreathAbelianizationMap D n).ker = commutator (ImprimitiveWreathProduct D n) := by
  apply le_antisymm
  · intro x hx
    have hΦ : wreathAbelianizationMap D n x = 1 := MonoidHom.mem_ker.mp hx
    have hb : wreathBaseAbelianization D n x.left = 1 := congrArg Prod.fst hΦ
    have hσ : sign x.right = 1 := congrArg Prod.snd hΦ
    let j : Fin n := ⟨0, by omega⟩
    have hbase : (SemidirectProduct.inl x.left : ImprimitiveWreathProduct D n) ∈
        commutator (ImprimitiveWreathProduct D n) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      have hf := DFunLike.congr_fun (wreath_base_map_factor
        (Abelianization.of : ImprimitiveWreathProduct D n →* _) j) x.left
      simpa only [MonoidHom.comp_apply, hb, map_one] using hf
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    exact (commutator _).mul_mem hbase (wreath_inr_mem_commutator x.right hσ)
  · exact Abelianization.commutator_subset_ker (wreathAbelianizationMap D n)

example : 2 ≤ (2 : ℕ) ∧
    wreathAbelianizationMap (Multiplicative (ZMod 1)) 2 1 = 1 := by
  constructor
  · decide
  · exact map_one _


/-- For a finite base and at least two coordinates, the wreath commutator has
order `|D|^(n-1) * |D'| * (n!/2)`. -/
theorem wreath_commutator_card (D : Type*) [Group D] [Finite D] (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card (commutator (ImprimitiveWreathProduct D n)) =
      Nat.card D ^ (n - 1) * Nat.card (commutator D) * (n.factorial / 2) := by
  have hquot : Nat.card (ImprimitiveWreathProduct D n ⧸
      (wreathAbelianizationMap D n).ker) = Nat.card (Abelianization D) * 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (wreathAbelianizationMap D n) (wreathAbelianizationMap_surjective D n hn)).toEquiv,
      Nat.card_prod, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int]
  rw [wreathAbelianizationMap_ker D n hn] at hquot
  have hw := (commutator (ImprimitiveWreathProduct D n)).card_eq_card_quotient_mul_card_subgroup
  rw [ImprimitiveWreathProduct.card, hquot] at hw
  have hd : Nat.card D = Nat.card (Abelianization D) * Nat.card (commutator D) :=
    (commutator D).card_eq_card_quotient_mul_card_subgroup
  have hfac : n.factorial / 2 * 2 = n.factorial :=
    Nat.div_mul_cancel (by simpa using Nat.factorial_dvd_factorial hn)
  have hpow : Nat.card D ^ n = Nat.card D ^ (n - 1) * Nat.card D := by
    have hs : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hs, pow_succ]
  have heq : (Nat.card (Abelianization D) * 2) *
      (Nat.card D ^ (n - 1) * Nat.card (commutator D) * (n.factorial / 2)) =
      Nat.card D ^ n * n.factorial := by
    calc
      _ = (Nat.card D ^ (n - 1) *
          (Nat.card (Abelianization D) * Nat.card (commutator D))) *
          (n.factorial / 2 * 2) := by ring
      _ = Nat.card D ^ n * n.factorial := by rw [← hd, hfac, ← hpow]
  have hpos : 0 < Nat.card (Abelianization D) * 2 := by
    exact Nat.mul_pos Nat.card_pos (by decide)
  exact Nat.eq_of_mul_eq_mul_left hpos (hw.symm.trans heq.symm)

/-- Adding a nontrivial finite abelian factor to the base changes the derived-group
order of the two-coordinate wreath product, so the wreath products are not isoclinic. -/
theorem not_isoclinic_wreath_prod_comm (G A : Type*) [Group G] [Finite G]
    [CommGroup A] [Finite A] (hA : 1 < Nat.card A) :
    ¬ IsoclinismInvariants.Isoclinic (ImprimitiveWreathProduct G 2)
      (ImprimitiveWreathProduct (G × A) 2) := by
  intro h
  obtain ⟨φ, ψ, hcompat⟩ := h.exists_iso
  have heq := Nat.card_congr ψ.toEquiv
  have hc : Nat.card (commutator G) = Nat.card (commutator (G × A)) :=
    Nat.card_congr (IsoclinismInvariants.commIso G A).toEquiv
  rw [wreath_commutator_card G 2 (by decide),
    wreath_commutator_card (G × A) 2 (by decide), Nat.card_prod, ← hc] at heq
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one,
    show Nat.factorial 2 / 2 = 1 from rfl, mul_one] at heq
  have hmul : (Nat.card G * Nat.card (commutator G)) * Nat.card A =
      (Nat.card G * Nat.card (commutator G)) * 1 := by
    calc
      _ = Nat.card G * Nat.card A * Nat.card (commutator G) := by ring
      _ = Nat.card G * Nat.card (commutator G) := heq.symm
      _ = _ := by rw [mul_one]
  have hpos : 0 < Nat.card G * Nat.card (commutator G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have ha : Nat.card A = 1 := Nat.eq_of_mul_eq_mul_left hpos hmul
  omega

example : 1 < Nat.card (Multiplicative (ZMod 2)) := by
  simp [Nat.card_eq_fintype_card]

end GroupTPP.STPPWreath
