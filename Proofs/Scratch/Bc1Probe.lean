import Mathlib

/-! Probe round 3: sum application on MonoidAlgebra; stdBasis repr. -/

open scoped Matrix

noncomputable section

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

-- P1a: term-mode Finset.sum_apply'
example {ι : Type*} (A : Finset ι) (f : ι → G) (h : G) :
    (∑ a ∈ A, MonoidAlgebra.single (f a) (1 : ℂ)) h
      = ∑ a ∈ A, (MonoidAlgebra.single (f a) (1 : ℂ) : MonoidAlgebra ℂ G) h :=
  Finset.sum_apply' h

-- P13a: stdBasis repr with trace through the goal
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) (p : m × n) :
    (Matrix.stdBasis ℂ m n).repr M p = M p.1 p.2 := by
  unfold Matrix.stdBasis
  rw [Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Pi.basis_repr]
  simp [Pi.basisFun_repr, Equiv.sigmaEquivProd]

end
