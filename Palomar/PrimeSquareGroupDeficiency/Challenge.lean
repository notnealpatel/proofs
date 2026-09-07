import Mathlib.Algebra.Group.Ext
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Prime-square group deficiency: independent challenge

The count is the natural cardinality of the quotient of all Mathlib group
structures on `Fin n` by multiplication-preserving bijections. The type of
structures and its quotient are finite. No classification value is assumed.
-/

set_option autoImplicit false

namespace Palomar.PrimeSquareGroupDeficiency

/-- Two group structures on `Fin n` are isomorphic if a bijection preserves
multiplication. Identity and inverses are then preserved automatically. -/
def Isomorphic {n : ℕ} (G H : Group (Fin n)) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ a b : Fin n, e (G.mul a b) = H.mul (e a) (e b)

/-- The table-preserving bijection definition is exactly Mathlib group isomorphism,
with the two group multiplications supplied explicitly rather than ambient Fin arithmetic. -/
theorem isomorphic_iff_nonempty_mulEquiv {n : ℕ} (G H : Group (Fin n)) :
    Isomorphic G H ↔ Nonempty (@MulEquiv (Fin n) (Fin n) G.toMul H.toMul) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨@MulEquiv.mk (Fin n) (Fin n) G.toMul H.toMul e he⟩
  · rintro ⟨e⟩
    exact ⟨@MulEquiv.toEquiv (Fin n) (Fin n) G.toMul H.toMul e,
      @MulEquiv.map_mul' (Fin n) (Fin n) G.toMul H.toMul e⟩

/-- There are finitely many group structures on `Fin n`: a group structure is
uniquely determined by its multiplication table, and there are finitely many tables. -/
instance finiteGroupStructures (n : ℕ) : Finite (Group (Fin n)) :=
  Finite.of_injective (fun G : Group (Fin n) => G.mul) (fun _ _ h => Group.ext h)

/-- Group isomorphism is an equivalence relation: the witnesses are the identity,
inverse, and composite bijections. -/
def groupIsoSetoid (n : ℕ) : Setoid (Group (Fin n)) where
  r := Isomorphic
  iseqv := by
    constructor
    · intro G
      exact ⟨Equiv.refl _, fun _ _ => rfl⟩
    · intro G H h
      obtain ⟨e, he⟩ := h
      refine ⟨e.symm, fun a b => e.injective ?_⟩
      rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · intro G H K hGH hHK
      obtain ⟨e, he⟩ := hGH
      obtain ⟨f, hf⟩ := hHK
      refine ⟨e.trans f, fun a b => ?_⟩
      rw [Equiv.trans_apply, he, hf, Equiv.trans_apply, Equiv.trans_apply]

example (n : ℕ) (G H : Group (Fin n)) :
    (groupIsoSetoid n).r G H ↔ Isomorphic G H := Iff.rfl

/-- The isomorphism-class quotient is finite at every order, including zero;
there is no infinite-cardinality default hidden in the natural count. -/
theorem finite_isoClasses (n : ℕ) : Finite (Quotient (groupIsoSetoid n)) := inferInstance

/-- The number of isomorphism classes of groups of order `n`. All Mathlib group
structures on `Fin n` are included, and only isomorphic structures are identified.
Every finite group of order `n` can be numbered by `Fin n`. -/
noncomputable def groupCount (n : ℕ) : ℕ := Nat.card (Quotient (groupIsoSetoid n))

/-- There is no group on the empty carrier. The count at zero is zero, not a
prime-square instance of the selected theorem. -/
theorem groupCount_zero : groupCount 0 = 0 := by
  letI : IsEmpty (Group (Fin 0)) := ⟨fun G => G.one.elim0⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Both the smallest prime and the next prime satisfy the selected guard. -/
theorem prime_guards : Nat.Prime 2 ∧ Nat.Prime 3 := ⟨Nat.prime_two, Nat.prime_three⟩

end Palomar.PrimeSquareGroupDeficiency

namespace Palomar.PrimeSquareGroupDeficiency

/-- Every prime square is group-deficient: fewer than `p ^ 2` group-isomorphism
classes have order `p ^ 2`. This is an elementary consequence of their classification. -/
theorem groupDeficient_prime_sq {p : ℕ} (hp : p.Prime) : groupCount (p ^ 2) < p ^ 2 := by
  sorry

#check @Isomorphic
set_option pp.explicit true in
#check @isomorphic_iff_nonempty_mulEquiv
#check @finite_isoClasses
#check @groupCount
#check @groupDeficient_prime_sq
#print axioms groupCount
#print axioms groupCount_zero
#print axioms prime_guards
#print axioms groupDeficient_prime_sq

end Palomar.PrimeSquareGroupDeficiency
