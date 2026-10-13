import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace GroupCount.OrderEightRelations

private def rotation {G : Type*} [Group G] (a : G) (i : ZMod 4) : G := a ^ i.val

private lemma rotation_zero {G : Type*} [Group G] (a : G) : rotation a 0 = 1 := by
  simp [rotation]

private lemma rotation_add {G : Type*} [Group G] (a : G) (ha : orderOf a = 4)
    (i j : ZMod 4) : rotation a (i + j) = rotation a i * rotation a j := by
  unfold rotation
  rw [ZMod.val_add]
  have hp := pow_mod_orderOf a (i.val + j.val)
  rw [ha] at hp
  rw [hp, pow_add]

private lemma rotation_neg {G : Type*} [Group G] (a : G) (ha : orderOf a = 4)
    (i : ZMod 4) : rotation a (-i) = (rotation a i)⁻¹ := by
  have h := rotation_add a ha i (-i)
  simp only [add_neg_cancel, rotation_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private lemma rotation_injective {G : Type*} [Group G] (a : G) (ha : orderOf a = 4) :
    Function.Injective (rotation a) := by
  intro i j h
  apply ZMod.val_injective
  have hp := (pow_inj_mod).mp h
  simpa only [ha, Nat.mod_eq_of_lt (ZMod.val_lt i),
    Nat.mod_eq_of_lt (ZMod.val_lt j)] using hp

private lemma rotation_mem {G : Type*} [Group G] (a : G) (i : ZMod 4) :
    rotation a i ∈ Subgroup.zpowers a :=
  (Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) _

private lemma arms_ne {G : Type*} [Group G] (a b : G)
    (hb : b ∉ Subgroup.zpowers a) (i j : ZMod 4) :
    rotation a i ≠ b * rotation a j := by
  intro h
  have he : b = rotation a i * (rotation a j)⁻¹ := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  apply hb
  rw [he]
  exact (Subgroup.zpowers a).mul_mem (rotation_mem a i)
    ((Subgroup.zpowers a).inv_mem (rotation_mem a j))

private lemma bijective_of_card {S G : Type*} [Finite S] [Finite G]
    (f : S → G) (hf : Function.Injective f) (hc : Nat.card S = Nat.card G) :
    Function.Bijective f := by
  letI := Fintype.ofFinite S
  letI := Fintype.ofFinite G
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  exact ⟨hf, by simpa only [Nat.card_eq_fintype_card] using hc⟩

private lemma rotation_move {G : Type*} [Group G] (a b : G)
    (ha : orderOf a = 4) (h : b * a * b⁻¹ = a⁻¹) (i : ZMod 4) :
    rotation a i * b = b * rotation a (-i) := by
  have hc : ∀ j : ZMod 4, b * rotation a j * b⁻¹ = (rotation a j)⁻¹ := by
    intro j
    have hh : (MulAut.conj b) a = a⁻¹ := h
    have hp := map_pow (MulAut.conj b) a j.val
    rw [hh] at hp
    simpa only [MulAut.conj_apply, rotation, inv_pow] using hp
  have ht := congrArg (fun x : G => x * b) (hc (-i))
  simpa only [rotation_neg a ha, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using ht.symm

private lemma rotation_sub {G : Type*} [Group G] (a : G) (ha : orderOf a = 4)
    (i j : ZMod 4) : rotation a (j - i) = rotation a (-i) * rotation a j := by
  rw [sub_eq_add_neg, add_comm, rotation_add a ha]

private def dihedralMap {G : Type*} [Group G] (a b : G) : DihedralGroup 4 → G
  | .r i => rotation a i
  | .sr i => b * rotation a i

private lemma dihedralMap_injective {G : Type*} [Group G] (a b : G)
    (ha : orderOf a = 4) (hb : b ∉ Subgroup.zpowers a) :
    Function.Injective (dihedralMap a b) := by
  intro x y h
  cases x with
  | r i =>
    cases y with
    | r j => exact congrArg DihedralGroup.r (rotation_injective a ha h)
    | sr j => exact False.elim (arms_ne a b hb i j h)
  | sr i =>
    cases y with
    | r j => exact False.elim (arms_ne a b hb j i h.symm)
    | sr j =>
      exact congrArg DihedralGroup.sr (rotation_injective a ha (mul_left_cancel h))

private def dihedralHom {G : Type*} [Group G] (a b : G) (ha : orderOf a = 4)
    (hinv : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = 1) : DihedralGroup 4 →* G where
  toFun := dihedralMap a b
  map_one' := rotation_zero a
  map_mul' := by
    intro x y
    cases x with
    | r i =>
      cases y with
      | r j => exact rotation_add a ha i j
      | sr j =>
        change b * rotation a (j - i) = rotation a i * (b * rotation a j)
        rw [rotation_sub a ha, ← mul_assoc, ← rotation_move a b ha hinv, mul_assoc]
    | sr i =>
      cases y with
      | r j =>
        change b * rotation a (i + j) = (b * rotation a i) * rotation a j
        rw [rotation_add a ha, mul_assoc]
      | sr j =>
        change rotation a (j - i) = (b * rotation a i) * (b * rotation a j)
        rw [mul_assoc b, ← mul_assoc (rotation a i), rotation_move a b ha hinv]
        rw [← mul_assoc b (b * rotation a (-i)), ← mul_assoc b b, ← pow_two, hsq, one_mul, rotation_sub a ha]

/-- An order-eight group with the dihedral generator relations is isomorphic to D8. -/
noncomputable def dihedralMulEquiv {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a b : G) (ha : orderOf a = 4)
    (hb : b ∉ Subgroup.zpowers a) (hinv : b * a * b⁻¹ = a⁻¹)
    (hsq : b ^ 2 = 1) : G ≃* DihedralGroup 4 :=
  (MulEquiv.ofBijective (dihedralHom a b ha hinv hsq)
    (bijective_of_card _ (dihedralMap_injective a b ha hb)
      (by rw [DihedralGroup.nat_card, hcard]))).symm

private def quaternionMap {G : Type*} [Group G] (a b : G) : QuaternionGroup 2 → G
  | .a i => rotation a i
  | .xa i => b * rotation a i

private lemma quaternionMap_injective {G : Type*} [Group G] (a b : G)
    (ha : orderOf a = 4) (hb : b ∉ Subgroup.zpowers a) :
    Function.Injective (quaternionMap a b) := by
  intro x y h
  cases x with
  | a i =>
    cases y with
    | a j => exact congrArg QuaternionGroup.a (rotation_injective a ha h)
    | xa j => exact False.elim (arms_ne a b hb i j h)
  | xa i =>
    cases y with
    | a j => exact False.elim (arms_ne a b hb j i h.symm)
    | xa j =>
      exact congrArg QuaternionGroup.xa (rotation_injective a ha (mul_left_cancel h))

private def quaternionHom {G : Type*} [Group G] (a b : G) (ha : orderOf a = 4)
    (hinv : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = a ^ 2) : QuaternionGroup 2 →* G where
  toFun := quaternionMap a b
  map_one' := rotation_zero a
  map_mul' := by
    intro x y
    cases x with
    | a i =>
      cases y with
      | a j => exact rotation_add a ha i j
      | xa j =>
        change b * rotation a (j - i) = rotation a i * (b * rotation a j)
        rw [rotation_sub a ha, ← mul_assoc, ← rotation_move a b ha hinv, mul_assoc]
    | xa i =>
      cases y with
      | a j =>
        change b * rotation a (i + j) = (b * rotation a i) * rotation a j
        rw [rotation_add a ha, mul_assoc]
      | xa j =>
        change rotation a (2 + j - i) = (b * rotation a i) * (b * rotation a j)
        rw [mul_assoc b, ← mul_assoc (rotation a i), rotation_move a b ha hinv]
        rw [← mul_assoc b (b * rotation a (-i)), ← mul_assoc b b]
        have hbb : b * b = a ^ 2 := by simpa only [pow_two] using hsq
        rw [hbb]
        rw [sub_eq_add_neg, rotation_add a ha, rotation_add a ha]
        have hc : rotation a j * rotation a (-i) = rotation a (-i) * rotation a j := by
          rw [← rotation_add a ha, ← rotation_add a ha, add_comm]
        rw [mul_assoc, hc]
        change a ^ 2 * (rotation a (-i) * rotation a j) =
          a ^ 2 * rotation a (-i) * rotation a j
        rw [mul_assoc]

/-- An order-eight group with the quaternion generator relations is isomorphic to Q8. -/
noncomputable def quaternionMulEquiv {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a b : G) (ha : orderOf a = 4)
    (hb : b ∉ Subgroup.zpowers a) (hinv : b * a * b⁻¹ = a⁻¹)
    (hsq : b ^ 2 = a ^ 2) : G ≃* QuaternionGroup 2 :=
  (MulEquiv.ofBijective (quaternionHom a b ha hinv hsq)
    (bijective_of_card _ (quaternionMap_injective a b ha hb)
      (by rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hcard]))).symm

private lemma two_values (e : ZMod 2) : e = 0 ∨ e = 1 := by
  have hlt := ZMod.val_lt e
  have hv : e.val = 0 ∨ e.val = 1 := by omega
  rcases hv with hz | ho
  · left
    apply ZMod.val_injective 2
    simpa only [ZMod.val_zero] using hz
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one] using ho

private def productMap {G : Type*} [Group G] (a b : G)
    (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) : G :=
  rotation a x.1.toAdd * b ^ x.2.toAdd.val

private lemma productMap_injective {G : Type*} [Group G] (a b : G)
    (ha : orderOf a = 4) (hb : b ∉ Subgroup.zpowers a) (hc : Commute a b) :
    Function.Injective (productMap a b) := by
  rintro ⟨i, e⟩ ⟨j, f⟩ h
  change ZMod 4 at i j
  change ZMod 2 at e f
  change rotation a i * b ^ e.val = rotation a j * b ^ f.val at h
  change (i, e) = (j, f)
  have hi : rotation a i * b = b * rotation a i := (hc.pow_left i.val).eq
  have hj : rotation a j * b = b * rotation a j := (hc.pow_left j.val).eq
  rcases two_values e with rfl | rfl <;> rcases two_values f with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, mul_one] at h
    exact Prod.ext (rotation_injective a ha h) rfl
  · simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, mul_one] at h
    rw [hj] at h
    exact False.elim (arms_ne a b hb i j h)
  · simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, mul_one] at h
    rw [hi] at h
    exact False.elim (arms_ne a b hb j i h.symm)
  · simp only [ZMod.val_one, pow_one] at h
    exact Prod.ext (rotation_injective a ha (mul_right_cancel h)) rfl

private lemma involution_add {G : Type*} [Group G] (b : G) (hsq : b ^ 2 = 1)
    (e f : ZMod 2) : b ^ (e + f).val = b ^ e.val * b ^ f.val := by
  rcases two_values e with rfl | rfl <;> rcases two_values f with rfl | rfl
  · simp
  · simp
  · simp
  · change b ^ 0 = b ^ 1 * b ^ 1
    simpa only [pow_zero, pow_one, pow_two] using hsq.symm

private def productHom {G : Type*} [Group G] (a b : G) (ha : orderOf a = 4)
    (hc : Commute a b) (hsq : b ^ 2 = 1) :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 2) →* G where
  toFun := productMap a b
  map_one' := by simp [productMap, rotation]
  map_mul' := by
    rintro ⟨i, e⟩ ⟨j, f⟩
    change rotation a (i.toAdd + j.toAdd) * b ^ (e.toAdd + f.toAdd).val =
      (rotation a i.toAdd * b ^ e.toAdd.val) * (rotation a j.toAdd * b ^ f.toAdd.val)
    rw [rotation_add a ha, involution_add b hsq]
    have hcomm : b ^ e.toAdd.val * rotation a j.toAdd =
        rotation a j.toAdd * b ^ e.toAdd.val :=
      ((hc.pow_left j.toAdd.val).pow_right e.toAdd.val).symm.eq
    simp only [mul_assoc]
    rw [← mul_assoc (b ^ e.toAdd.val), hcomm, mul_assoc]

/-- An order-eight group with commuting order-four and outside involution generators is C4 × C2. -/
noncomputable def commutingMulEquiv {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (a b : G) (ha : orderOf a = 4)
    (hb : b ∉ Subgroup.zpowers a) (hc : Commute a b)
    (hsq : b ^ 2 = 1) : G ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) :=
  (MulEquiv.ofBijective (productHom a b ha hc hsq)
    (bijective_of_card _ (productMap_injective a b ha hb hc)
      (by rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_zmod, hcard]))).symm

example : Nat.card (DihedralGroup 4) = 8 ∧
    orderOf (DihedralGroup.r (1 : ZMod 4)) = 4 ∧
    DihedralGroup.sr (0 : ZMod 4) ∉ Subgroup.zpowers (DihedralGroup.r (1 : ZMod 4)) ∧
    DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.r (1 : ZMod 4) *
      (DihedralGroup.sr (0 : ZMod 4))⁻¹ = (DihedralGroup.r (1 : ZMod 4))⁻¹ ∧
    (DihedralGroup.sr (0 : ZMod 4)) ^ 2 = 1 := by
  have ha : orderOf (DihedralGroup.r (1 : ZMod 4)) = 4 := by
    rw [DihedralGroup.orderOf_r]
    change 4 / Nat.gcd 4 1 = 4
    decide
  refine ⟨DihedralGroup.nat_card, ha, ?_, by decide, by decide⟩
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  decide

example : Nat.card (QuaternionGroup 2) = 8 ∧
    orderOf (QuaternionGroup.a (n := 2) (1 : ZMod 4)) = 4 ∧
    QuaternionGroup.xa (n := 2) (0 : ZMod 4) ∉ Subgroup.zpowers (QuaternionGroup.a (n := 2) (1 : ZMod 4)) ∧
    QuaternionGroup.xa (n := 2) (0 : ZMod 4) * QuaternionGroup.a (n := 2) (1 : ZMod 4) *
      (QuaternionGroup.xa (n := 2) (0 : ZMod 4))⁻¹ = (QuaternionGroup.a (n := 2) (1 : ZMod 4))⁻¹ ∧
    (QuaternionGroup.xa (n := 2) (0 : ZMod 4)) ^ 2 = (QuaternionGroup.a (n := 2) (1 : ZMod 4)) ^ 2 := by
  have ha : orderOf (QuaternionGroup.a (n := 2) (1 : ZMod 4)) = 4 := by
    rw [QuaternionGroup.orderOf_a]
    change 4 / Nat.gcd 4 1 = 4
    decide
  refine ⟨by rw [Nat.card_eq_fintype_card, QuaternionGroup.card], ha, ?_, by decide, by decide⟩
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  decide

example : let a : Multiplicative (ZMod 4) × Multiplicative (ZMod 2) :=
      (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)
    let b : Multiplicative (ZMod 4) × Multiplicative (ZMod 2) :=
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)
    Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) = 8 ∧
      orderOf a = 4 ∧ b ∉ Subgroup.zpowers a ∧ Commute a b ∧ b ^ 2 = 1 := by
  dsimp only
  have ha : orderOf ((Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) :
      Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) = 4 := by
    apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  refine ⟨?_, ha, ?_, ?_, by decide⟩
  · rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_zmod]
  · rw [mem_zpowers_iff_mem_range_orderOf, ha]
    decide
  · change (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) *
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) =
      (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) *
      ((Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) :
        Multiplicative (ZMod 4) × Multiplicative (ZMod 2))
    decide

example {G : Type*} [Group G] (a : G) : rotation a 0 = 1 := rotation_zero a
example {G : Type*} [Group G] (a : G) : rotation a 1 = a := by
  change a ^ 1 = a
  exact pow_one a
example {G : Type*} [Group G] (a b : G) : dihedralMap a b (.r 0) = 1 := rotation_zero a
example {G : Type*} [Group G] (a b : G) : dihedralMap a b (.sr 0) = b := by
  simp [dihedralMap, rotation_zero]
example {G : Type*} [Group G] (a b : G) : quaternionMap a b (.a 0) = 1 := rotation_zero a
example {G : Type*} [Group G] (a b : G) : quaternionMap a b (.xa 0) = b := by
  simp [quaternionMap, rotation_zero]
example {G : Type*} [Group G] (a b : G) : productMap a b (1, 1) = 1 := by
  simp [productMap, rotation]

example {G : Type*} [Group G] (a b : G) (ha : orderOf a = 4)
    (hinv : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = 1) (i : ZMod 4) :
    dihedralHom a b ha hinv hsq (.r i) = rotation a i := rfl
example {G : Type*} [Group G] (a b : G) (ha : orderOf a = 4)
    (hinv : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = a ^ 2) (i : ZMod 4) :
    quaternionHom a b ha hinv hsq (.a i) = rotation a i := rfl
example {G : Type*} [Group G] (a b : G) (ha : orderOf a = 4)
    (hc : Commute a b) (hsq : b ^ 2 = 1)
    (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) :
    productHom a b ha hc hsq x = productMap a b x := rfl

example {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 8)
    (a b : G) (ha : orderOf a = 4) (hb : b ∉ Subgroup.zpowers a)
    (hinv : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = 1) :
    (dihedralMulEquiv hcard a b ha hb hinv hsq).symm (.sr 0) = b := by
  change b * rotation a 0 = b
  rw [rotation_zero, mul_one]
example {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 8)
    (a b : G) (ha : orderOf a = 4) (hb : b ∉ Subgroup.zpowers a)
    (hinv : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = a ^ 2) :
    (quaternionMulEquiv hcard a b ha hb hinv hsq).symm (.xa 0) = b := by
  change b * rotation a 0 = b
  rw [rotation_zero, mul_one]
example {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 8)
    (a b : G) (ha : orderOf a = 4) (hb : b ∉ Subgroup.zpowers a)
    (hc : Commute a b) (hsq : b ^ 2 = 1) :
    (commutingMulEquiv hcard a b ha hb hc hsq).symm
      (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) = a := by
  change a ^ 1 * b ^ 0 = a
  rw [pow_one, pow_zero, mul_one]

end GroupCount.OrderEightRelations
