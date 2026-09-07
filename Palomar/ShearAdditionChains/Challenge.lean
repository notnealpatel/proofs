import Mathlib.Order.Lattice.Nat

/-!
# Addition chains and fresh-target monomial shear programs

The challenge compares two independently specified minima. An ordinary addition
chain starts at exponent `1` and prepends sums of two older exponents. A
monomial shear program starts with one register of exponent `1`; every counted
instruction selects two existing source registers, allocates a new target whose
exponent is their sum, and retains all old registers. Exponent traces are stored
newest first.

This restricted syntax has no free affine mixing and makes no clean-scratch,
unrestricted-circuit, elliptic-curve, or inversion optimality claim.
-/

set_option autoImplicit false

namespace Palomar.ShearAdditionChains

/-- A newest-first ordinary addition chain: `[1]` is the initial chain, and a
new head is the sum of two entries in the older tail. -/
inductive IsAddChain : List ℕ → Prop
  | one : IsAddChain [1]
  | add {exponents : List ℕ} {left right : ℕ}
      (hleft : left ∈ exponents) (hright : right ∈ exponents)
      (chain : IsAddChain exponents) :
      IsAddChain ((left + right) :: exponents)

example : IsAddChain [1] := .one
example : IsAddChain [2, 1] :=
  .add (left := 1) (right := 1) (by simp) (by simp) .one

/-- Every ordinary addition chain has a nonempty exponent trace. -/
theorem IsAddChain.ne_nil {exponents : List ℕ} (chain : IsAddChain exponents) :
    exponents ≠ [] := by
  cases chain <;> simp

/-- The number of additions recorded by a newest-first exponent list. Its value
on the non-chain empty list is the junk value `0`. -/
def chainSteps (exponents : List ℕ) : ℕ := exponents.tail.length

example : chainSteps [1] = 0 := rfl
example : chainSteps [2, 1] = 1 := rfl
example : chainSteps ([] : List ℕ) = 0 := rfl

/-- A chain trace has one more entry than its number of additions. -/
theorem IsAddChain.length_eq_chainSteps_add_one {exponents : List ℕ}
    (chain : IsAddChain exponents) :
    exponents.length = chainSteps exponents + 1 := by
  obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil chain.ne_nil
  simp [chainSteps]

/-- An ordinary addition chain whose newest exponent is `n`. -/
def AdditionChain (n : ℕ) :=
  {exponents : List ℕ // IsAddChain exponents ∧ exponents.head? = some n}

example : Nonempty (AdditionChain 1) := ⟨⟨[1], .one, rfl⟩⟩

/-- The shortest ordinary addition-chain length. At `n = 0`, the empty indexed
infimum has the junk value `0`; positive `n` is the intended domain. -/
noncomputable def l (n : ℕ) : ℕ :=
  ⨅ chain : AdditionChain n, chainSteps chain.val

/-- Every exponent occurring in an ordinary addition chain is positive. -/
theorem IsAddChain.one_le_of_mem {exponents : List ℕ}
    (chain : IsAddChain exponents) :
    ∀ exponent ∈ exponents, 1 ≤ exponent := by
  induction chain with
  | one =>
      intro exponent hexponent
      simp only [List.mem_singleton] at hexponent
      subst exponent
      exact le_rfl
  | @add exponents left right hleft _hright _chain ih =>
      intro exponent hexponent
      rcases List.mem_cons.mp hexponent with heq | hold
      · subst exponent
        exact Nat.le_add_right_of_le (ih left hleft)
      · exact ih exponent hold

/-- No ordinary addition chain computes exponent zero. -/
instance instIsEmptyAdditionChainZero : IsEmpty (AdditionChain 0) :=
  ⟨fun chain => by
    have hzero : 0 ∈ chain.val := by
      apply List.mem_of_head?
      exact chain.property.2
    exact (Nat.not_succ_le_zero 0) (chain.property.1.one_le_of_mem 0 hzero)⟩

example : l 0 = 0 := by
  exact Nat.iInf_of_empty _

/-- A restricted fresh-target monomial shear program indexed by its newest-first
register-exponent trace. Source indices are explicit program data. -/
inductive MonomialShearProgram : List ℕ → Type
  | input : MonomialShearProgram [1]
  | shear {exponents : List ℕ} (program : MonomialShearProgram exponents)
      (left right : Fin exponents.length) :
      MonomialShearProgram
        ((exponents.get left + exponents.get right) :: exponents)

/-- The number of allocated fresh-target shears in a monomial program. -/
def MonomialShearProgram.shearCount :
    {exponents : List ℕ} → MonomialShearProgram exponents → ℕ
  | _, .input => 0
  | _, .shear program _ _ => program.shearCount + 1

example : Nonempty (MonomialShearProgram [1]) := ⟨.input⟩
example : Nonempty (MonomialShearProgram [2, 1]) :=
  ⟨.shear .input ⟨0, by decide⟩ ⟨0, by decide⟩⟩
example :
    MonomialShearProgram.shearCount
        (.shear .input ⟨0, by decide⟩ ⟨0, by decide⟩ :
          MonomialShearProgram [2, 1]) = 1 := rfl

/-- A restricted monomial shear computation whose newest register has exponent
`n`; older power registers are retained as unrestricted garbage. -/
structure MonomialShearComputation (n : ℕ) where
  exponents : List ℕ
  program : MonomialShearProgram exponents
  output_eq : exponents.head? = some n

example : Nonempty (MonomialShearComputation 1) :=
  ⟨⟨[1], .input, rfl⟩⟩
example : Nonempty (MonomialShearComputation 2) :=
  ⟨⟨[2, 1], .shear .input ⟨0, by decide⟩ ⟨0, by decide⟩, rfl⟩⟩

/-- Forgetting explicit source indices gives the ordinary addition chain traced
by a monomial shear program. -/
theorem MonomialShearProgram.isAddChain : {exponents : List ℕ} →
    MonomialShearProgram exponents → IsAddChain exponents
  | _, .input => .one
  | _, .shear program left right =>
      .add (List.get_mem _ left) (List.get_mem _ right) program.isAddChain

/-- No restricted monomial shear computation from exponent `1` computes
exponent zero. -/
instance instIsEmptyMonomialShearComputationZero :
    IsEmpty (MonomialShearComputation 0) :=
  ⟨fun computation => by
    have hzero : 0 ∈ computation.exponents := by
      apply List.mem_of_head?
      exact computation.output_eq
    exact (Nat.not_succ_le_zero 0)
      (computation.program.isAddChain.one_le_of_mem 0 hzero)⟩

/-- The minimum number of fresh-target monomial shears among actual indexed
program computations of exponent `n`. At `n = 0` its empty infimum is the junk
value `0`. -/
noncomputable def minimumMonomialShears (n : ℕ) : ℕ :=
  ⨅ computation : MonomialShearComputation n,
    computation.program.shearCount

example : minimumMonomialShears 0 = 0 := by
  exact Nat.iInf_of_empty _

/-- For nonzero `n`, the minimum number of restricted fresh-target monomial
shears computing exponent `n` equals the shortest ordinary addition-chain
length. -/
theorem minimumMonomialShears_eq_l (n : ℕ) (hn : n ≠ 0) :
    minimumMonomialShears n = l n := by
  sorry

-- The guard is jointly satisfiable and the syntax has a concrete computation.
example : (2 : ℕ) ≠ 0 := by decide

#check @minimumMonomialShears_eq_l

end Palomar.ShearAdditionChains
