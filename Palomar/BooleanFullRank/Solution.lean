import BilinearComplexity.BooleanRankGeneric

/-!
# Proof that almost every Boolean matrix has full Boolean row rank

This module repeats the challenge declarations without importing the challenge.
It then transports the repository's counting bound and limit theorem across the
transparent duplicate definitions.  Boolean row rank here is minimization over
subsets of existing rows generating the same coordinatewise-`or` span; no
factorization-rank or `ZMod 2` rank is substituted.
-/

set_option autoImplicit false

namespace Palomar.BooleanFullRank

open Finset Filter

/-- The two-element Boolean semiring, retyped so addition is `or` rather than
exclusive-or. -/
def BoolSemiring : Type := Bool

instance : DecidableEq BoolSemiring := inferInstanceAs (DecidableEq Bool)
instance : Fintype BoolSemiring := inferInstanceAs (Fintype Bool)
instance : Zero BoolSemiring := ⟨(false : Bool)⟩
instance : One BoolSemiring := ⟨(true : Bool)⟩
instance : Add BoolSemiring := ⟨Bool.or⟩
instance : Mul BoolSemiring := ⟨Bool.and⟩

instance : CommSemiring BoolSemiring where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  nsmul := nsmulRec
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide

instance : Nontrivial BoolSemiring := ⟨⟨0, 1, by decide⟩⟩

example : (1 : BoolSemiring) + 1 = 1 := by decide
example : (0 : BoolSemiring) + 1 = 1 := by decide
example : (1 : BoolSemiring) * 0 = 0 := by decide

/-- A Boolean `m × n` matrix, represented as a curried finite function. -/
abbrev BoolMatrix (m n : ℕ) : Type := Fin m → Fin n → BoolSemiring

example : BoolMatrix 1 1 := fun _ _ => 0

/-- The coordinatewise Boolean sum of the rows indexed by `T`. -/
def rowsSum {m n : ℕ} (A : BoolMatrix m n) (T : Finset (Fin m)) :
    Fin n → BoolSemiring :=
  fun j => ∑ i ∈ T, A i j

example : rowsSum (fun _ _ => 0 : BoolMatrix 1 1) {0} = 0 := by decide

/-- The finite coordinatewise-`or` span of the rows indexed by `S`, including
the empty sum. -/
def rowSpan {m n : ℕ} (A : BoolMatrix m n) (S : Finset (Fin m)) :
    Finset (Fin n → BoolSemiring) :=
  S.powerset.image (rowsSum A)

example : rowSpan (fun _ _ => 0 : BoolMatrix 1 1) {0} = {0} := by decide

/-- At most `r` existing rows generate the same Boolean row span as all rows. -/
def BoolRowRankLE {m n : ℕ} (A : BoolMatrix m n) (r : ℕ) : Prop :=
  ∃ S : Finset (Fin m), S.card ≤ r ∧ rowSpan A S = rowSpan A Finset.univ

instance {m n : ℕ} (A : BoolMatrix m n) (r : ℕ) : Decidable (BoolRowRankLE A r) :=
  inferInstanceAs (Decidable
    (∃ S : Finset (Fin m), S.card ≤ r ∧ rowSpan A S = rowSpan A Finset.univ))

example : BoolRowRankLE (0 : BoolMatrix 1 1) 0 := by decide

/-- Every finite Boolean matrix has a finite spanning-row bound. -/
theorem exists_boolRowRankLE {m n : ℕ} (A : BoolMatrix m n) :
    ∃ r, BoolRowRankLE A r :=
  ⟨m, Finset.univ, by simp, rfl⟩

/-- Boolean row rank is the least cardinality of a subset of the existing rows
whose coordinatewise-`or` span is the full row span. -/
def boolRowRank {m n : ℕ} (A : BoolMatrix m n) : ℕ :=
  Nat.find (exists_boolRowRankLE A)

example : boolRowRank (0 : BoolMatrix 1 1) = 0 := by
  rw [boolRowRank, Nat.find_eq_iff]
  exact ⟨by decide, by simp⟩

/-- The number of square Boolean matrices whose Boolean row rank is the number
of their rows. -/
def fullRowRankCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A = n).card

example (n : ℕ) : fullRowRankCount n =
    (Finset.univ.filter fun A : BoolMatrix n n => boolRowRank A = n).card := rfl

/-- The proportion of all `n × n` Boolean matrices having full Boolean row
rank.  Its denominator is the positive number `2^(n*n)`. -/
noncomputable def fullRowRankFraction (n : ℕ) : ℝ :=
  (fullRowRankCount n : ℝ) / 2 ^ (n * n)

example (n : ℕ) : fullRowRankFraction n =
    (fullRowRankCount n : ℝ) / 2 ^ (n * n) := rfl

/-- For `2 ≤ n`, the union bound gives the quantitative lower bound
`1 - n^2 (3/4)^n` for the full Boolean-row-rank fraction. -/
theorem one_sub_le_fullRowRankFraction {n : ℕ} (h2 : 2 ≤ n) :
    1 - (n : ℝ) ^ 2 * (3 / 4) ^ n ≤ fullRowRankFraction n := by
  exact BilinearComplexity.one_sub_le_fullRowRankFraction h2

/-- The full Boolean-row-rank fraction is at most one. -/
theorem fullRowRankFraction_le_one (n : ℕ) : fullRowRankFraction n ≤ 1 := by
  exact BilinearComplexity.fullRowRankFraction_le_one n

/-- The fraction of uniformly counted square Boolean matrices having full
Boolean row rank tends to one. -/
theorem fullRowRankFraction_tendsto_one :
    Tendsto fullRowRankFraction atTop (nhds 1) := by
  exact BilinearComplexity.fullRowRankFraction_tendsto_one

-- The quantitative theorem has a jointly satisfiable hypothesis.
example : 2 ≤ (2 : ℕ) := le_rfl

#check @one_sub_le_fullRowRankFraction
#check @fullRowRankFraction_le_one
#check @fullRowRankFraction_tendsto_one
#print axioms Palomar.BooleanFullRank.one_sub_le_fullRowRankFraction
#print axioms Palomar.BooleanFullRank.fullRowRankFraction_le_one
#print axioms Palomar.BooleanFullRank.fullRowRankFraction_tendsto_one

end Palomar.BooleanFullRank
