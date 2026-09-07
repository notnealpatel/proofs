import ShearEC.ShearAdditionChain

/-!
# Addition chains and fresh-target monomial shear programs

This solution repeats the challenge definitions without importing the challenge.
It proves their correspondence with the repository's independently defined
addition chains and with the source-indexed monomial program theorem in
`ShearEC.ShearAdditionChain`.

The restricted syntax has no free affine mixing and makes no clean-scratch,
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

/-- A program's number of shears is the addition cost of its exponent trace. -/
theorem MonomialShearProgram.shearCount_eq_chainSteps
    {exponents : List ℕ} (program : MonomialShearProgram exponents) :
    program.shearCount = chainSteps exponents := by
  induction program with
  | input => rfl
  | @shear exponents program left right ih =>
      rw [shearCount, ih]
      change chainSteps exponents + 1 = exponents.length
      rw [program.isAddChain.length_eq_chainSteps_add_one]

/-- Every challenge addition chain admits concrete source indices, producing a
restricted monomial shear program with the same trace. -/
theorem nonempty_monomialShearProgram_of_isAddChain {exponents : List ℕ}
    (chain : IsAddChain exponents) :
    Nonempty (MonomialShearProgram exponents) := by
  induction chain with
  | one => exact ⟨.input⟩
  | @add exponents left right hleft hright _chain ih =>
      obtain ⟨program⟩ := ih
      obtain ⟨leftIndex, hleftIndex⟩ := List.get_of_mem hleft
      obtain ⟨rightIndex, hrightIndex⟩ := List.get_of_mem hright
      refine ⟨?_⟩
      simpa only [hleftIndex, hrightIndex] using
        (MonomialShearProgram.shear program leftIndex rightIndex)

/-- The independently declared challenge chain predicate is equivalent to the
repository chain predicate, list by list. -/
theorem isAddChain_iff_source {exponents : List ℕ} :
    IsAddChain exponents ↔ NumberComplexity.IsAddChain exponents := by
  constructor
  · intro chain
    induction chain with
    | one => exact .one
    | add hleft hright _chain ih => exact .add hleft hright ih
  · intro chain
    induction chain with
    | one => exact .one
    | add hleft hright _chain ih => exact .add hleft hright ih

/-- Translate the duplicate challenge syntax to the repository's
source-indexed program syntax without changing its exponent trace. -/
def MonomialShearProgram.toSource : {exponents : List ℕ} →
    MonomialShearProgram exponents →
      ShearEC.ShearAdditionChain.MonomialShearProgram exponents
  | _, .input => .input
  | _, .shear program left right => .shear program.toSource left right

/-- Translate a repository monomial program to the duplicate challenge syntax
without changing its exponent trace. -/
def MonomialShearProgram.ofSource : {exponents : List ℕ} →
    ShearEC.ShearAdditionChain.MonomialShearProgram exponents →
      MonomialShearProgram exponents
  | _, .input => .input
  | _, .shear program left right =>
      .shear (MonomialShearProgram.ofSource program) left right

example : MonomialShearProgram.toSource (.input) =
    (ShearEC.ShearAdditionChain.MonomialShearProgram.input) := rfl
example : MonomialShearProgram.ofSource
    (ShearEC.ShearAdditionChain.MonomialShearProgram.input) =
      MonomialShearProgram.input := rfl

/-- Translation to the repository program syntax preserves the counted cost. -/
theorem MonomialShearProgram.shearCount_toSource {exponents : List ℕ}
    (program : MonomialShearProgram exponents) :
    program.toSource.shearCount = program.shearCount := by
  induction program with
  | input => rfl
  | shear program left right ih =>
      simp only [toSource,
        ShearEC.ShearAdditionChain.MonomialShearProgram.shearCount,
        shearCount, ih]

/-- Translation from the repository program syntax preserves the counted cost. -/
theorem MonomialShearProgram.shearCount_ofSource {exponents : List ℕ}
    (program : ShearEC.ShearAdditionChain.MonomialShearProgram exponents) :
    (MonomialShearProgram.ofSource program).shearCount =
      program.shearCount := by
  induction program with
  | input => rfl
  | shear program left right ih =>
      simp only [ofSource, shearCount,
        ShearEC.ShearAdditionChain.MonomialShearProgram.shearCount, ih]

/-- Translate a challenge computation to the repository computation type,
preserving its target and trace. -/
def MonomialShearComputation.toSource {n : ℕ}
    (computation : MonomialShearComputation n) :
    ShearEC.ShearAdditionChain.MonomialShearComputation n :=
  ⟨computation.exponents, computation.program.toSource, computation.output_eq⟩

/-- Translate a repository computation to the challenge computation type,
preserving its target and trace. -/
def MonomialShearComputation.ofSource {n : ℕ}
    (computation : ShearEC.ShearAdditionChain.MonomialShearComputation n) :
    MonomialShearComputation n :=
  ⟨computation.exponents,
    MonomialShearProgram.ofSource computation.program,
    computation.output_eq⟩

example (computation : MonomialShearComputation 1) :
    computation.toSource.exponents = computation.exponents := rfl
example (computation :
    ShearEC.ShearAdditionChain.MonomialShearComputation 1) :
    (MonomialShearComputation.ofSource computation).exponents =
      computation.exponents := rfl

/-- On positive inputs, the independently declared chain minimum equals the
repository's shortest-chain function. -/
theorem l_eq_source_l (n : ℕ) (hn : n ≠ 0) :
    l n = NumberComplexity.l n := by
  apply le_antisymm
  · obtain ⟨sourceChain, hsourceCost⟩ :=
      NumberComplexity.exists_chainSteps_eq_l hn
    let chain : AdditionChain n :=
      ⟨sourceChain.val, isAddChain_iff_source.mpr sourceChain.property.1,
        sourceChain.property.2⟩
    calc
      l n ≤ chainSteps chain.val := Nat.sInf_le (Set.mem_range_self chain)
      _ = NumberComplexity.chainSteps sourceChain.val := rfl
      _ = NumberComplexity.l n := hsourceCost
  · haveI : Nonempty (AdditionChain n) := by
      let ⟨sourceChain⟩ := NumberComplexity.nonempty_additionChain_of_ne_zero hn
      exact ⟨⟨sourceChain.val,
        isAddChain_iff_source.mpr sourceChain.property.1,
        sourceChain.property.2⟩⟩
    have hmem : l n ∈ Set.range fun chain : AdditionChain n =>
        chainSteps chain.val := Nat.sInf_mem (Set.range_nonempty _)
    obtain ⟨chain, hchain⟩ := hmem
    rw [← hchain]
    exact NumberComplexity.l_le_chainSteps
      ⟨chain.val, isAddChain_iff_source.mp chain.property.1,
        chain.property.2⟩

/-- Every positive target has a challenge monomial computation. -/
theorem nonempty_monomialShearComputation_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Nonempty (MonomialShearComputation n) := by
  let ⟨sourceChain⟩ := NumberComplexity.nonempty_additionChain_of_ne_zero hn
  have chain : IsAddChain sourceChain.val :=
    isAddChain_iff_source.mpr sourceChain.property.1
  obtain ⟨program⟩ := nonempty_monomialShearProgram_of_isAddChain chain
  exact ⟨⟨sourceChain.val, program, sourceChain.property.2⟩⟩

/-- On positive targets, the challenge program-cost infimum is attained. -/
theorem exists_shearCount_eq_minimumMonomialShears {n : ℕ} (hn : n ≠ 0) :
    ∃ computation : MonomialShearComputation n,
      computation.program.shearCount = minimumMonomialShears n := by
  haveI : Nonempty (MonomialShearComputation n) :=
    nonempty_monomialShearComputation_of_ne_zero hn
  have hmem : minimumMonomialShears n ∈
      Set.range fun computation : MonomialShearComputation n =>
        computation.program.shearCount :=
    Nat.sInf_mem (Set.range_nonempty _)
  rwa [Set.mem_range] at hmem

/-- On positive inputs, the independent program infimum equals the repository
program infimum through the two cost-preserving syntax translations. -/
theorem minimumMonomialShears_eq_source (n : ℕ) (hn : n ≠ 0) :
    minimumMonomialShears n =
      ShearEC.ShearAdditionChain.minimumMonomialShears n := by
  apply le_antisymm
  · obtain ⟨sourceComputation, hsourceCost⟩ :=
      ShearEC.ShearAdditionChain.exists_shearCount_eq_minimumMonomialShears hn
    calc
      minimumMonomialShears n ≤
          (MonomialShearComputation.ofSource sourceComputation).program.shearCount :=
        Nat.sInf_le (Set.mem_range_self
          (MonomialShearComputation.ofSource sourceComputation))
      _ = sourceComputation.program.shearCount :=
        MonomialShearProgram.shearCount_ofSource sourceComputation.program
      _ = ShearEC.ShearAdditionChain.minimumMonomialShears n := hsourceCost
  · obtain ⟨computation, hcost⟩ :=
      exists_shearCount_eq_minimumMonomialShears hn
    calc
      ShearEC.ShearAdditionChain.minimumMonomialShears n ≤
          computation.toSource.program.shearCount :=
        ShearEC.ShearAdditionChain.minimumMonomialShears_le computation.toSource
      _ = computation.program.shearCount :=
        computation.program.shearCount_toSource
      _ = minimumMonomialShears n := hcost

/-- For nonzero `n`, the minimum number of restricted fresh-target monomial
shears computing exponent `n` equals the shortest ordinary addition-chain
length. -/
theorem minimumMonomialShears_eq_l (n : ℕ) (hn : n ≠ 0) :
    minimumMonomialShears n = l n := by
  rw [minimumMonomialShears_eq_source n hn,
    ShearEC.ShearAdditionChain.minimumMonomialShears_eq_l n hn,
    l_eq_source_l n hn]

-- The guard is jointly satisfiable and the syntax has a concrete computation.
example : (2 : ℕ) ≠ 0 := by decide

#check @minimumMonomialShears_eq_l
#check @ShearEC.ShearAdditionChain.minimumMonomialShears_eq_l
#print axioms Palomar.ShearAdditionChains.isAddChain_iff_source
#print axioms Palomar.ShearAdditionChains.MonomialShearProgram.shearCount_toSource
#print axioms Palomar.ShearAdditionChains.MonomialShearProgram.shearCount_ofSource
#print axioms Palomar.ShearAdditionChains.minimumMonomialShears_eq_source
#print axioms Palomar.ShearAdditionChains.l_eq_source_l
#print axioms ShearEC.ShearAdditionChain.minimumMonomialShears_eq_l
#print axioms Palomar.ShearAdditionChains.minimumMonomialShears_eq_l

end Palomar.ShearAdditionChains
