import GroupCount.GroupPerfect

/-!
# Prime-square group deficiency: solution

The independent model below is repeated verbatim from the challenge, not replaced
by source aliases. A quotient equivalence identifies its natural count with the
source count at every natural order. The selected theorem then uses the proved
prime-square deficiency result, not either archived open conjecture.
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

namespace Palomar.PrimeSquareGroupDeficiency.Bridge

/-- Reading the tables of a Mathlib group structure gives exactly the source
representation. The equivalence preserves and reflects the isomorphism relation,
so it descends to an equivalence of the class quotients at every order. -/
def isoClassEquiv (n : ℕ) :
    Quotient (groupIsoSetoid n) ≃ GroupCount.IsoClass n :=
  Quotient.congr (GroupCount.GroupStructure.equivGroup n).symm (fun _ _ => Iff.rfl)

/-- The independently defined count equals the source `gnu` for every natural
order, including zero. This is a cardinality consequence of the quotient equivalence. -/
theorem groupCount_eq_gnu (n : ℕ) : groupCount n = GroupCount.gnu n := by
  rw [groupCount, GroupCount.gnu_eq_natCard]
  exact Nat.card_congr (isoClassEquiv n)

end Palomar.PrimeSquareGroupDeficiency.Bridge

namespace Palomar.PrimeSquareGroupDeficiency

/-- Every prime square is group-deficient: fewer than `p ^ 2` group-isomorphism
classes have order `p ^ 2`. This is an elementary consequence of their classification. -/
theorem groupDeficient_prime_sq {p : ℕ} (hp : p.Prime) : groupCount (p ^ 2) < p ^ 2 := by
  rw [Bridge.groupCount_eq_gnu]
  exact GroupCount.groupDeficient_prime_sq hp

example : Nat.Prime 2 ∧ groupCount (2 ^ 2) < 2 ^ 2 :=
  ⟨Nat.prime_two, groupDeficient_prime_sq Nat.prime_two⟩
example : Nat.Prime 3 ∧ groupCount (3 ^ 2) < 3 ^ 2 :=
  ⟨Nat.prime_three, groupDeficient_prime_sq Nat.prime_three⟩

#check @Isomorphic
set_option pp.explicit true in
#check @isomorphic_iff_nonempty_mulEquiv
#check @finite_isoClasses
#check @groupCount
#check @Bridge.isoClassEquiv
#check @Bridge.groupCount_eq_gnu
#check @GroupCount.groupDeficient_prime_sq
#check @groupDeficient_prime_sq
#print axioms groupCount
#print axioms groupCount_zero
#print axioms prime_guards
#print axioms isomorphic_iff_nonempty_mulEquiv
#print axioms finite_isoClasses
#print axioms Bridge.isoClassEquiv
#print axioms Bridge.groupCount_eq_gnu
#print axioms GroupCount.groupDeficient_prime_sq
#print axioms groupDeficient_prime_sq

end Palomar.PrimeSquareGroupDeficiency
