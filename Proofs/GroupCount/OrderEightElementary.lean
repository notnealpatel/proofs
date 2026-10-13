import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace GroupCount.OrderEightElementary

/-- Square-one elements in a group commute. -/
theorem mul_comm_of_square_one {G : Type*} [Group G]
    (hsq : ∀ g : G, g ^ 2 = 1) (a b : G) : a * b = b * a := by
  have hinv (g : G) : g⁻¹ = g := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hsq g
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b, hinv a]

/-- A finite group of order eight in which every square is one is isomorphic
to the nested product of three cyclic groups represented by `Multiplicative (ZMod 2)`. -/
theorem nonempty_mulEquiv_of_card_eight_of_square_one {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (hsq : ∀ g : G, g ^ 2 = 1) :
    Nonempty (G ≃* ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
      Multiplicative (ZMod 2))) := by
  letI : CommGroup G := { (inferInstance : Group G) with
    mul_comm := mul_comm_of_square_one hsq }
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule
    (fun g => show 2 • g = 0 from hsq g.toMul)
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive G) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive G) = Nat.card (Additive G) := by
        simpa [Nat.card_eq_fintype_card, ZMod.card] using h.symm
      _ = Nat.card G := (Nat.card_congr Additive.ofMul).symm
      _ = 8 := hcard
  have hrank : Module.finrank (ZMod 2) (Additive G) = 3 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    exact hpow
  let coordinates : Additive G ≃+ (Fin 3 → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hrank).equivFun.toAddEquiv
  let triple : (Fin 3 → ZMod 2) ≃+ ((ZMod 2 × ZMod 2) × ZMod 2) := {
    toFun := fun f => ((f 0, f 1), f 2)
    invFun := fun p => ![p.1.1, p.1.2, p.2]
    left_inv := by
      intro f
      funext i
      fin_cases i <;> rfl
    right_inv := by
      intro p
      rfl
    map_add' := by
      intro f g
      rfl }
  let split : Multiplicative ((ZMod 2 × ZMod 2) × ZMod 2) ≃*
      ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) :=
    (MulEquiv.prodMultiplicative (G := ZMod 2 × ZMod 2) (H := ZMod 2)).trans
      (MulEquiv.prodCongr
        (MulEquiv.prodMultiplicative (G := ZMod 2) (H := ZMod 2)) (MulEquiv.refl _))
  exact ⟨(AddEquiv.toMultiplicativeRight (coordinates.trans triple)).trans split⟩

example : Nonempty
    ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2)) :=
  ⟨1⟩

example :
    (Nat.card ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
      Multiplicative (ZMod 2)) = 8) ∧
    (∀ g : ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
      Multiplicative (ZMod 2)), g ^ 2 = 1) := by
  constructor
  · rw [Nat.card_eq_fintype_card]
    decide
  · decide

end GroupCount.OrderEightElementary
