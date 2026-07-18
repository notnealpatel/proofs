import Xlib.CharDegreesComm

/-! Micro-probe: isolate the `IsSimpleModule.congr` instance clash. Throwaway. -/

-- P1: is the AddCommMonoid diamond defeq at all (abstract ring)?
example (R : Type*) [Ring R] (I : Ideal R) :
    (Submodule.addCommMonoid I) = (Submodule.addCommGroup I).toAddCommMonoid := rfl

-- P2: is it defeq for the concrete MonoidAlgebra ring?
example (H : Type*) [Group H] (I : Ideal (MonoidAlgebra ℂ H)) :
    (Submodule.addCommMonoid I) = (Submodule.addCommGroup I).toAddCommMonoid := rfl

-- P3: the exact Mathlib usage pattern, abstract ring
example (R : Type*) [Ring R] [IsSemisimpleRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : True := by
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  haveI : IsSimpleModule R ↥I := IsSimpleModule.congr e.symm
  trivial

-- P4: same with concrete ring, abstract module
example (H : Type*) [Group H] [Finite H] [NeZero (Nat.card H : ℂ)]
    (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℂ H) M]
    [IsSimpleModule (MonoidAlgebra ℂ H) M] : True := by
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (MonoidAlgebra ℂ H) M
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) ↥I := IsSimpleModule.congr e.symm
  trivial
