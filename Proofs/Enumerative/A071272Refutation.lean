/-
Refutation of Wu's criterion for OEIS A071272 (Chai Wah Wu, May 30 2026).

A term is a positive palindrome m for which 11m is an even-length palindrome
(A066492 and A056524; David A. Corneth's restatement, May 30 2026).
The palindrome 19091 satisfies the stated middle-pair digit bound but
11*19091=210001 is not palindromic, refuting the proposed equivalence.
The broader adjacent-pair no-carry criterion below is only defined and tested;
its equivalence with sequence membership is not proved.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A071272Refutation

/-- `n` is a decimal palindrome: its base-10 digit list equals its reverse. -/
def IsPal (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

instance : DecidablePred IsPal := fun _ => inferInstanceAs (Decidable (_ = _))

/-- Membership in A066492: `m` is a positive integer with `11 * m` an
even-length palindrome (i.e. `11 * m ∈ A056524`). -/
def InA066492 (m : ℕ) : Prop :=
  0 < m ∧ IsPal (11 * m) ∧ Even (Nat.digits 10 (11 * m)).length

instance : DecidablePred InA066492 := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Membership in A071272: `m` is a palindrome lying in A066492. -/
def IsTerm (m : ℕ) : Prop :=
  IsPal m ∧ InA066492 m

instance : DecidablePred IsTerm := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The `i`-th decimal digit of `n` counted from the left, `1`-indexed
(`i = 1` is the leading digit).  Only used with `1 ≤ i ≤ length`. -/
def digitFromLeft (n i : ℕ) : ℕ :=
  (Nat.digits 10 n).reverse.getD (i - 1) 0

/-- Wu's criterion: `1 ≤ m ≤ 9`, or `m` is a palindrome of odd length `2k+1`
(with `1 ≤ k`, so that the `k`-th digit exists) whose `k`-th and `(k+1)`-th
decimal digits sum to at most `9`. -/
def WuCriterion (m : ℕ) : Prop :=
  (1 ≤ m ∧ m ≤ 9) ∨
    (IsPal m ∧ ∃ k : ℕ, 1 ≤ k ∧ (Nat.digits 10 m).length = 2 * k + 1 ∧
      digitFromLeft m k + digitFromLeft m (k + 1) ≤ 9)

/-- Wu's criterion is decidable: the witness `k` is bounded by the digit
length, since `length = 2 * k + 1`. -/
instance : DecidablePred WuCriterion := fun m =>
  decidable_of_iff
    ((1 ≤ m ∧ m ≤ 9) ∨
      (IsPal m ∧ ∃ k < (Nat.digits 10 m).length, 1 ≤ k ∧
        (Nat.digits 10 m).length = 2 * k + 1 ∧
        digitFromLeft m k + digitFromLeft m (k + 1) ≤ 9)) (by
    unfold WuCriterion
    constructor
    · rintro (hsmall | ⟨hpal, k, -, hk⟩)
      · exact Or.inl hsmall
      · exact Or.inr ⟨hpal, k, hk⟩
    · rintro (hsmall | ⟨hpal, k, hk1, hlen, hsum⟩)
      · exact Or.inl hsmall
      · exact Or.inr ⟨hpal, k, by omega, hk1, hlen, hsum⟩)

/-- **Wu's conjecture (A071272, Chai Wah Wu, May 30 2026).**
"m is a term if and only if 1<=m<=9 or m is a palindrome of odd length 2k+1
such that the sum of the k-th and (k+1)-th decimal digits is less than or
equal to 9." -/
def Conjecture : Prop :=
  ∀ m : ℕ, IsTerm m ↔ WuCriterion m

/-! ## Examples -/

example : (Nat.digits 10 19091) = [1, 9, 0, 9, 1] := by norm_num

example : IsTerm 1 ∧ IsTerm 9 ∧ IsTerm 101 ∧ IsTerm 909 ∧ IsTerm 10001 := by
  decide

-- `91 ∈ A066492` (since `11 * 91 = 1001`) but is not a palindrome;
-- `191` is a palindrome with `11 * 191 = 2101` not a palindrome;
-- `11` is a palindrome with `11 * 11 = 121` of odd length.
example : InA066492 91 ∧ ¬ IsTerm 91 ∧ ¬ IsTerm 191 ∧ ¬ IsTerm 11 ∧ ¬ IsTerm 0 := by
  decide

-- The terms below `10002` are exactly the listed DATA terms.
example : (List.range 10002).filter (fun m => decide (IsTerm m)) =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 101, 111, 121, 131, 141, 151, 161, 171, 181, 202,
      212, 222, 232, 242, 252, 262, 272, 303, 313, 323, 333, 343, 353, 363, 404,
      414, 424, 434, 444, 454, 505, 515, 525, 535, 545, 606, 616, 626, 636, 707,
      717, 727, 808, 818, 909, 10001] := by
  decide +kernel

-- Wu's criterion agrees with the definition on some small cases.
example : WuCriterion 5 ∧ WuCriterion 181 ∧ ¬ WuCriterion 191 ∧ WuCriterion 10001 := by
  decide

/-! ## The refutation -/

/-- `19091` satisfies Wu's criterion: it is a palindrome of length `5 = 2*2+1`
whose 2nd and 3rd digits `9, 0` sum to `9`. -/
theorem wuCriterion_19091 : WuCriterion 19091 := by
  right
  exact ⟨by decide, 2, by norm_num, by decide, by decide⟩

/-- `19091` is not a term: `11 * 19091 = 210001` is not a palindrome. -/
theorem not_isTerm_19091 : ¬ IsTerm 19091 := by
  decide

/-- Wu's A071272 criterion is false: the odd-length palindrome `19091` has
central digits `9,0` summing to `9`, but `11*19091=210001` is not palindromic. -/
theorem wuConjecture_false : ¬ Conjecture := fun h =>
  not_isTerm_19091 ((h 19091).mpr wuCriterion_19091)

/-! ## A no-carry criterion (finite examples only) -/

/-- A positive odd-length palindrome with every adjacent digit pair summing
to at most `9`. Its equivalence with sequence membership is not proved here. -/
def NoCarryCriterion (m : ℕ) : Prop :=
  0 < m ∧ IsPal m ∧ Odd (Nat.digits 10 m).length ∧
    ∀ i < (Nat.digits 10 m).length - 1,
      (Nat.digits 10 m).getD i 0 + (Nat.digits 10 m).getD (i + 1) 0 ≤ 9

instance : DecidablePred NoCarryCriterion := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

-- Finite evidence only: the no-carry criterion agrees with membership for
-- every `m < 20000`, a window containing the counterexample `19091`
-- (which fails the no-carry criterion at the pair `1, 9`).
example : (List.range 20000).all
    (fun m => decide (IsTerm m) == decide (NoCarryCriterion m)) = true := by
  decide +kernel

example : ¬ NoCarryCriterion 19091 := by
  decide

end Candidates.A071272Refutation
