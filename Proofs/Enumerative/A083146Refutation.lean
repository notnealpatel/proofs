/-
# A counterexample for A083146 and A083145

The unsigned OEIS A083146 conjecture asserts finitely many differing indices,
exactly 5 through 9. At index 74 the positive palindrome is 656:
A083145 is 656656, a concatenation of two copies, whereas A083146 is 2133312.
This refutes the exact-index clause and hence the conjunction; it does not
settle finiteness or Franklin T. Adams-Watters' infinitude conjecture
(May 16 2006). Positive palindromes are indexed from 1.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A083146Refutation

/-! ## Definitions -/

/-- A natural number is a (base-10) palindrome when its decimal digit list
reads the same reversed. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- `IsPal` is decided by comparing digit lists. -/
instance : DecidablePred IsPal := fun m =>
  inferInstanceAs (Decidable ((Nat.digits 10 m).reverse = Nat.digits 10 m))

/-- The `IsPal` predicate is `List.Palindrome` of the decimal digits. -/
theorem isPal_iff_palindrome (m : ℕ) : IsPal m ↔ (Nat.digits 10 m).Palindrome :=
  List.Palindrome.iff_reverse_eq.symm

/-- The positive palindromes `1, 2, …, 9, 11, 22, …` (A002113 without `0`). -/
def IsPosPal (m : ℕ) : Prop := 0 < m ∧ IsPal m

/-- `IsPosPal` is decidable. -/
instance : DecidablePred IsPosPal := fun m =>
  inferInstanceAs (Decidable (0 < m ∧ IsPal m))

/-- The `n`-th positive palindrome, indexed from `n = 1`
(meaningful for `1 ≤ n`; the conjecture below only uses such `n`). -/
noncomputable def nthPal (n : ℕ) : ℕ := Nat.nth IsPosPal (n - 1)

/-- `q` is a concatenation of copies of `p` in decimal: its digit string is
`j` copies of the digit string of `p`.  (`Nat.digits` is little-endian; the
concatenation of copies of a word is invariant under reversing all of them.) -/
def IsConcatCopies (p q : ℕ) : Prop :=
  ∃ j, Nat.digits 10 q = (List.replicate j (Nat.digits 10 p)).flatten

/-- `IsA083145 n q`: `q` is A083145(n), the smallest palindromic multiple of
the `n`-th palindrome `p` other than `p` itself (multiples are positive, so
"other than `p`" is `p < q`). -/
def IsA083145 (n q : ℕ) : Prop :=
  IsPal q ∧ nthPal n ∣ q ∧ nthPal n < q ∧
    ∀ r, IsPal r → nthPal n ∣ r → nthPal n < r → q ≤ r

/-- `IsA083146 n q`: `q` is A083146(n), the smallest palindromic multiple of
the `n`-th palindrome `p` that is not a concatenation of copies of `p`. -/
def IsA083146 (n q : ℕ) : Prop :=
  IsPal q ∧ nthPal n ∣ q ∧ nthPal n < q ∧ ¬ IsConcatCopies (nthPal n) q ∧
    ∀ r, IsPal r → nthPal n ∣ r → nthPal n < r → ¬ IsConcatCopies (nthPal n) r → q ≤ r


/-! ## Reduction lemmas

The minimality clauses quantify over all naturals; the lemmas below reduce
them to finite checks over multipliers `k`, which the kernel then decides. -/

/-- A number `pK` is A083145(n) when `p = nthPal n > 0`, `2 ≤ K`, `pK` is a
palindrome, and no `pk` with `2 ≤ k < K` is a palindrome. -/
theorem isA083145_of_mul {n p K : ℕ} (hp : nthPal n = p) (hp0 : 0 < p) (hK : 2 ≤ K)
    (hpal : IsPal (p * K)) (hmin : ∀ k < K, 2 ≤ k → ¬ IsPal (p * k)) :
    IsA083145 n (p * K) := by
  subst hp
  refine ⟨hpal, dvd_mul_right _ _, ?_, ?_⟩
  · calc nthPal n = nthPal n * 1 := (mul_one _).symm
      _ < nthPal n * K := Nat.mul_lt_mul_of_pos_left (by omega) hp0
  · rintro r hr ⟨k, rfl⟩ hlt
    have hk2 : 2 ≤ k := by
      by_contra hk
      interval_cases k <;> simp at hlt
    by_contra hle
    have hkK : k < K := by
      by_contra hkK
      exact hle (Nat.mul_le_mul_left _ (by omega))
    exact hmin k hkK hk2 hr

/-- A number `pK` is A083146(n) when `p = nthPal n > 0`, `2 ≤ K`, `pK` is a
palindrome that is not a concatenation of copies of `p`, and every palindrome
`pk` with `2 ≤ k < K` is such a concatenation. -/
theorem isA083146_of_mul {n p K : ℕ} (hp : nthPal n = p) (hp0 : 0 < p) (hK : 2 ≤ K)
    (hpal : IsPal (p * K)) (hnc : ¬ IsConcatCopies p (p * K))
    (hmin : ∀ k < K, 2 ≤ k → IsPal (p * k) → IsConcatCopies p (p * k)) :
    IsA083146 n (p * K) := by
  subst hp
  refine ⟨hpal, dvd_mul_right _ _, ?_, hnc, ?_⟩
  · calc nthPal n = nthPal n * 1 := (mul_one _).symm
      _ < nthPal n * K := Nat.mul_lt_mul_of_pos_left (by omega) hp0
  · rintro r hr ⟨k, rfl⟩ hlt hrc
    have hk2 : 2 ≤ k := by
      by_contra hk
      interval_cases k <;> simp at hlt
    by_contra hle
    have hkK : k < K := by
      by_contra hkK
      exact hle (Nat.mul_le_mul_left _ (by omega))
    exact hrc (hmin k hkK hk2 hr)

/-- For `0 < p`, the number of copies in a concatenation is bounded by the
digit length of `q`, so `IsConcatCopies p q` is a bounded search. -/
theorem isConcatCopies_iff_bounded {p : ℕ} (hp : 0 < p) (q : ℕ) :
    IsConcatCopies p q ↔
      ∃ j < (Nat.digits 10 q).length + 1,
        Nat.digits 10 q = (List.replicate j (Nat.digits 10 p)).flatten := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, hj⟩
    have hlen : (Nat.digits 10 q).length = j * (Nat.digits 10 p).length := by
      rw [hj]; simp
    have hpos : 0 < (Nat.digits 10 p).length :=
      List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hp.ne')
    have hjle : j ≤ j * (Nat.digits 10 p).length := Nat.le_mul_of_pos_right j hpos
    omega
  · rintro ⟨j, -, hj⟩
    exact ⟨j, hj⟩

/-- The value of `nthPal` at an index, from a count of smaller palindromes. -/
theorem nthPal_eq {n m : ℕ} (hm : IsPosPal m) (hc : Nat.count IsPosPal m + 1 = n) :
    nthPal n = m := by
  subst hc
  simp only [nthPal, Nat.add_sub_cancel]
  exact Nat.nth_count hm


/-- A083145 values are unique: the minimality clause pins them down. -/
theorem IsA083145.unique {n q q' : ℕ} (h : IsA083145 n q) (h' : IsA083145 n q') :
    q = q' :=
  le_antisymm (h.2.2.2 q' h'.1 h'.2.1 h'.2.2.1) (h'.2.2.2 q h.1 h.2.1 h.2.2.1)

/-- A083146 values are unique: the minimality clause pins them down. -/
theorem IsA083146.unique {n q q' : ℕ} (h : IsA083146 n q) (h' : IsA083146 n q') :
    q = q' :=
  le_antisymm (h.2.2.2.2 q' h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1)
    (h'.2.2.2.2 q h.1 h.2.1 h.2.2.1 h.2.2.2.1)

/-! ## Examples -/

example : nthPal 1 = 1 := nthPal_eq (by decide) (by decide +kernel)
example : nthPal 9 = 9 := nthPal_eq (by decide) (by decide +kernel)
example : nthPal 10 = 11 := nthPal_eq (by decide) (by decide +kernel)
example : nthPal 14 = 55 := nthPal_eq (by decide) (by decide +kernel)
example : nthPal 19 = 101 := nthPal_eq (by decide) (by decide +kernel)
example : nthPal 39 = 303 := nthPal_eq (by decide) (by decide +kernel)

/-! A083145 terms `a(1) = 2`, `a(4) = 8`, `a(5) = 55`, `a(9) = 99`, `a(10) = 22`,
`a(14) = 5005`, `a(39) = 606`. -/

example : IsA083145 1 (1 * 2) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)
example : IsA083145 4 (4 * 2) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)
example : IsA083145 5 (5 * 11) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)
example : IsA083145 9 (9 * 11) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)
example : IsA083145 10 (11 * 2) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)
example : IsA083145 14 (55 * 91) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)
example : IsA083145 39 (303 * 2) :=
  isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by decide +kernel)

/-! A083146 terms `a(5..9) = 505,222,161,232,171`, `a(1) = 2`, `a(14) = 5005`. -/

example : IsA083146 1 (1 * 2) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (fun k hk hk2 => absurd hk (by omega))
example : IsA083146 5 (5 * 101) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (by simp only [isConcatCopies_iff_bounded (show 0 < 5 by norm_num)]; decide +kernel)
example : IsA083146 6 (6 * 37) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (by simp only [isConcatCopies_iff_bounded (show 0 < 6 by norm_num)]; decide +kernel)
example : IsA083146 7 (7 * 23) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (by simp only [isConcatCopies_iff_bounded (show 0 < 7 by norm_num)]; decide +kernel)
example : IsA083146 8 (8 * 29) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (by simp only [isConcatCopies_iff_bounded (show 0 < 8 by norm_num)]; decide +kernel)
example : IsA083146 9 (9 * 19) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (by simp only [isConcatCopies_iff_bounded (show 0 < 9 by norm_num)]; decide +kernel)
example : IsA083146 14 (55 * 91) :=
  isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
    (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
    (by simp only [isConcatCopies_iff_bounded (show 0 < 55 by norm_num)]; decide +kernel)

/-- The concatenation `55` of two `5`s is excluded from A083146(5). -/
example : IsConcatCopies 5 55 := ⟨2, by decide⟩

/-! ## The conjecture -/

/-- A083146 differs from A083145 at index `n`: both terms exist and are
different. -/
def Differs (n : ℕ) : Prop := ∃ q r, IsA083145 n q ∧ IsA083146 n r ∧ q ≠ r

/-- Part (1) of the A083146 conjecture (original entry): "The sequence
differs from A083145 only for finitely many values of n." -/
def ConjecturePart1 : Prop := {n : ℕ | 1 ≤ n ∧ Differs n}.Finite

/-- Part (2) of the A083146 conjecture (original entry): "Values of n are
5,6,7,8 and 9", i.e. for `n ≥ 1` the sequences differ exactly at `5 ≤ n ≤ 9`. -/
def ConjecturePart2 : Prop := ∀ n, 1 ≤ n → (Differs n ↔ 5 ≤ n ∧ n ≤ 9)

/-- The original A083146 conjecture: finitely many differing indices,
exactly 5 through 9. The conjunction is refuted through its second clause. -/
def Conjecture : Prop := ConjecturePart1 ∧ ConjecturePart2

/-- The sequences differ at `n = 5`
(`55` versus `505`). -/
example : Differs 5 :=
  ⟨5 * 11, 5 * 101,
    isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
      (by decide) (by decide +kernel),
    isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
      (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
      (by simp only [isConcatCopies_iff_bounded (show 0 < 5 by norm_num)]; decide +kernel),
    by norm_num⟩

/-- The sequences agree at `n = 14` (both `5005`). -/
example : ¬ Differs 14 := by
  rintro ⟨q, r, hq, hr, hne⟩
  have h145 : IsA083145 14 (55 * 91) :=
    isA083145_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
      (by decide) (by decide +kernel)
  have h146 : IsA083146 14 (55 * 91) :=
    isA083146_of_mul (nthPal_eq (by decide) (by decide +kernel)) (by norm_num) (by norm_num)
      (by decide) (by rw [isConcatCopies_iff_bounded (by norm_num)]; decide +kernel)
      (by simp only [isConcatCopies_iff_bounded (show 0 < 55 by norm_num)]; decide +kernel)
  exact hne ((hq.unique h145).trans (hr.unique h146).symm)

/-! ## The counterexample at `n = 74` (palindrome `656`) -/

/-- The `74`-th palindrome is `656`: there are `73` positive palindromes
below it (`9` of one digit, `9` of two digits, `55` of the form `aba < 656`). -/
theorem nthPal_74 : nthPal 74 = 656 :=
  nthPal_eq (by decide) (by decide +kernel)

set_option maxRecDepth 20000 in
/-- No `656 * k` with `2 ≤ k < 3252`, `k ≠ 1001`, is a palindrome
(kernel check over `3250` multipliers). -/
theorem not_isPal_656_mul :
    ∀ k < 3252, 2 ≤ k → k ≠ 1001 → ¬ IsPal (656 * k) := by
  decide +kernel


/-- `656656 = 656 * 1001` is a concatenation of two copies of `656`. -/
theorem isConcatCopies_656_656656 : IsConcatCopies 656 (656 * 1001) :=
  ⟨2, by decide⟩

/-- `2133312 = 656 * 3252` is not a concatenation of copies of `656`: it has
`7` digits, and `j` copies of `656` have `3 * j` digits. -/
theorem not_isConcatCopies_656_2133312 : ¬ IsConcatCopies 656 (656 * 3252) := by
  rintro ⟨j, hj⟩
  have hq : Nat.digits 10 (656 * 3252) = [2, 1, 3, 3, 3, 1, 2] := by decide
  have hp : Nat.digits 10 656 = [6, 5, 6] := by decide
  rw [hq, hp] at hj
  have hlen := congrArg List.length hj
  simp only [List.length_cons, List.length_nil, List.length_flatten, List.map_replicate,
    List.sum_replicate, smul_eq_mul] at hlen
  omega

/-- A083145(74) = 656656. -/
theorem isA083145_74 : IsA083145 74 (656 * 1001) :=
  isA083145_of_mul nthPal_74 (by norm_num) (by norm_num) (by decide)
    (fun k hk hk2 => not_isPal_656_mul k (by omega) hk2 (by omega))

/-- A083146(74) = 2133312. -/
theorem isA083146_74 : IsA083146 74 (656 * 3252) := by
  refine isA083146_of_mul nthPal_74 (by norm_num) (by norm_num) (by decide)
    not_isConcatCopies_656_2133312 ?_
  intro k hk hk2 hpal
  by_cases h1001 : k = 1001
  · subst h1001
    exact isConcatCopies_656_656656
  · exact absurd hpal (not_isPal_656_mul k hk hk2 h1001)


/-- The sequences differ at `n = 74`: A083145(74) = 656656 while
A083146(74) = 2133312. -/
theorem differs_74 : Differs 74 :=
  ⟨656 * 1001, 656 * 3252, isA083145_74, isA083146_74, by norm_num⟩

/-- Part (2) of the A083146 conjecture is false: the sequences also differ
at `n = 74`. -/
theorem conjecturePart2_false : ¬ ConjecturePart2 := fun h => by
  have h74 := (h 74 (by norm_num)).mp differs_74
  omega

/-- The exact-index clause, and hence the A083146 conjunction, fails at
`n=74`: the least nontrivial palindromic multiple of 656 is 656656,
whereas the least non-concatenation palindromic multiple is 2133312.
The finiteness clause and Adams-Watters' infinitude conjecture are not settled. -/
theorem conjecture_false : ¬ Conjecture := fun h => conjecturePart2_false h.2

end Candidates.A083146Refutation
