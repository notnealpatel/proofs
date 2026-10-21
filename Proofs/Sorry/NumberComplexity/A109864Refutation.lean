/-
# A109864 — the zero set of "least palindromic prime beginning with n"

## OEIS source (retrieved with `oeis show A109864` and the live entry, 2026-10-21)

```
NAME:     Least palindromic prime beginning with n, or 0 if no such prime exists.
OFFSET:   1
TERMS:    11,2,3,0,5,0,7,0,919,101,11,12421,131,14341,151,16061,17471,181,191,
          0,0,0,0,0,0,0,0,0,0,30103,313,32323,33533,34543,353,36263,373,383,
          39293,0,0,0,...
KEYWORDS: base,nonn
COMMENT (the conjecture; unsigned in the entry):
  Conjecture: a(n) = 0 if and only if n > 3 and n begins with 2,4,6,8 or 5
  (most significant digit).
AUTHOR:   Amarnath Murthy, Jul 08 2005
EXTENSIONS: Corrected and extended by Giovanni Resta, Feb 07 2006
```

No later comment retracts or corrects the conjecture.

## Status

**False** as literally stated.  This module refutes it at `n = 5`: the
right-hand side holds (`5 > 3` and `5` begins with `5`), but `5` is itself a
palindromic prime beginning with `5`, so `a(5) = 5 ≠ 0` (the fifth listed term).

Computational re-validation (Python, 2026-10-21): the first 39 listed terms are
reproduced by a direct search up to `10^6`, `a(5) = 5`, and for `n < 100` the
two sides of the conjecture disagree only at `n = 5` (and at `n = 99`, an
artefact of the search bound: `a(99)` exceeds `10^6`).

The evidently intended statement replaces `n > 3` by `n ∉ {2, 5}`.  Its "if"
direction is proved below as `a_eq_zero_of_beginsWith` (a palindrome beginning
with `d` ends with `d`, so it is divisible by `2` or `5`).  Its "only if"
direction — every `n` with leading digit `1, 3, 7` or `9` begins some
palindromic prime — is open and is not claimed here.

## Formal conventions

* Decimal expansions are `Nat.digits 10`, least significant digit first, so
  "the expansion of `p` begins with `n`" is `(digits n).reverse <+: (digits p).reverse`.
* "`n` begins with the digit `d`" is the same relation `BeginsWith d n`.
* `a 0` is junk (`digits 10 0 = []` is a prefix of everything); the conjecture
  is quantified over `0 < n`, matching the offset.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A109864Refutation

/-! ## Definition layer -/

/-- The decimal expansion of `p` begins with the decimal expansion of `n`
(most significant digits first). -/
def BeginsWith (n p : ℕ) : Prop :=
  (Nat.digits 10 n).reverse <+: (Nat.digits 10 p).reverse

/-- `p` is a decimal palindrome. -/
def IsPalindrome (p : ℕ) : Prop :=
  (Nat.digits 10 p).reverse = Nat.digits 10 p

instance (n p : ℕ) : Decidable (BeginsWith n p) := by
  unfold BeginsWith; infer_instance

instance (p : ℕ) : Decidable (IsPalindrome p) := by
  unfold IsPalindrome; infer_instance

/-- `p` is a palindromic prime whose decimal expansion begins with `n`. -/
def IsCandidate (n p : ℕ) : Prop :=
  BeginsWith n p ∧ IsPalindrome p ∧ p.Prime

instance (n p : ℕ) : Decidable (IsCandidate n p) := by
  unfold IsCandidate; infer_instance

open Classical in
/-- A109864: the least palindromic prime beginning with `n`, or `0` if none. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ p, IsCandidate n p then Nat.find h else 0

/-- `a n = v` as soon as `v` is a candidate and no smaller number is. -/
theorem a_eq_of_isLeast {n v : ℕ} (hv : IsCandidate n v)
    (hmin : ∀ m < v, ¬ IsCandidate n m) : a n = v := by
  classical
  have hex : ∃ p, IsCandidate n p := ⟨v, hv⟩
  rw [a, dif_pos hex, Nat.find_eq_iff]
  exact ⟨hv, hmin⟩

/-- `a n = 0` exactly when no palindromic prime begins with `n`. -/
theorem a_eq_zero_iff {n : ℕ} : a n = 0 ↔ ¬ ∃ p, IsCandidate n p := by
  classical
  by_cases hex : ∃ p, IsCandidate n p
  · rw [a, dif_pos hex]
    have hspec : IsCandidate n (Nat.find hex) := Nat.find_spec hex
    have hne : Nat.find hex ≠ 0 := hspec.2.2.ne_zero
    simp only [hne, false_iff, not_not, hex]
  · rw [a, dif_neg hex]
    simp only [hex, not_false_eq_true]

/-! ## Ground truth -/

example : BeginsWith 12 12421 ∧ IsPalindrome 12421 := by decide
example : ¬ BeginsWith 12 1342 ∧ ¬ IsPalindrome 12 := by decide

-- `a(1), a(2), a(3), a(5), a(7) = 11, 2, 3, 5, 7` (listed terms 1, 2, 3, 5, 7).
example : a 1 = 11 := a_eq_of_isLeast (by decide) (by decide)
example : a 2 = 2 := a_eq_of_isLeast (by decide) (by decide)
example : a 3 = 3 := a_eq_of_isLeast (by decide) (by decide)
example : a 5 = 5 := a_eq_of_isLeast (by decide) (by decide)
example : a 7 = 7 := a_eq_of_isLeast (by decide) (by decide)
-- `a(10), a(11), a(13), a(15), a(18), a(19) = 101, 11, 131, 151, 181, 191`.
example : a 10 = 101 := a_eq_of_isLeast ⟨by decide, by decide, by norm_num⟩ (by decide)
example : a 11 = 11 := a_eq_of_isLeast (by decide) (by decide)
example : a 13 = 131 := a_eq_of_isLeast ⟨by decide, by decide, by norm_num⟩ (by decide)
example : a 15 = 151 := a_eq_of_isLeast ⟨by decide, by decide, by norm_num⟩ (by decide)
set_option maxRecDepth 4000 in
example : a 18 = 181 := a_eq_of_isLeast ⟨by decide, by decide, by norm_num⟩ (by decide)
set_option maxRecDepth 4000 in
example : a 19 = 191 := a_eq_of_isLeast ⟨by decide, by decide, by norm_num⟩ (by decide)
/-! ## The conjecture -/

/-- **The A109864 conjecture (unsigned comment in the entry).**

Verbatim: "Conjecture: a(n) = 0 if and only if n > 3 and n begins with
2,4,6,8 or 5 (most significant digit)."

Stated for `0 < n` (the offset is `1`); "n begins with the digit `d`" is
`BeginsWith d n`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n →
    (a n = 0 ↔ 3 < n ∧ ∃ d ∈ ({2, 4, 5, 6, 8} : Finset ℕ), BeginsWith d n)

/-! ## The refutation -/

/-- `5` is a palindromic prime beginning with `5`, so `a 5 ≠ 0`. -/
theorem a_five_ne_zero : a 5 ≠ 0 := by
  rw [Ne, a_eq_zero_iff, not_not]
  exact ⟨5, by decide⟩

/-- **The A109864 conjecture is false**, with counterexample `n = 5`: the
right-hand side holds (`3 < 5` and `5` begins with the digit `5`), but
`a(5) = 5 ≠ 0`.  The author presumably intended the hypothesis `n ∉ {2, 5}`
in place of `n > 3`; see `a_eq_zero_of_beginsWith` for its "if" direction. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hrhs : 3 < 5 ∧ ∃ d ∈ ({2, 4, 5, 6, 8} : Finset ℕ), BeginsWith d 5 :=
    ⟨by norm_num, 5, by decide, by decide⟩
  exact a_five_ne_zero ((hconj 5 (by norm_num)).2 hrhs)

/-! ## The intended "if" direction -/

/-- A palindrome whose expansion begins with the nonzero digit `d` ends in `d`. -/
theorem mod_ten_eq_of_beginsWith {d p : ℕ} (hd0 : d ≠ 0) (hd : d < 10)
    (hb : BeginsWith d p) (hpal : IsPalindrome p) : p % 10 = d := by
  have hdig : Nat.digits 10 d = [d] := Nat.digits_of_lt 10 d hd0 hd
  have hpre : [d] <+: Nat.digits 10 p := by
    have hb' := hb
    rw [BeginsWith, hdig, hpal] at hb'
    simpa using hb'
  obtain ⟨t, ht⟩ := hpre
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; simp at ht
    · exact h0
  rw [Nat.digits_def' (by norm_num) hp0] at ht
  simp only [List.singleton_append, List.cons.injEq] at ht
  exact ht.1.symm

/-- **The intended "if" direction.** If `n` begins with one of the digits
`2, 4, 5, 6, 8` and `n ∉ {2, 5}`, then no palindromic prime begins with `n`,
so `a n = 0`. -/
theorem a_eq_zero_of_beginsWith {n d : ℕ} (hd : d ∈ ({2, 4, 5, 6, 8} : Finset ℕ))
    (hdn : BeginsWith d n) (hn2 : n ≠ 2) (hn5 : n ≠ 5) : a n = 0 := by
  rw [a_eq_zero_iff]
  rintro ⟨p, hnp, hpal, hprime⟩
  have hdp : BeginsWith d p := hdn.trans hnp
  have hd0 : d ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have hd10 : d < 10 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have hmod : p % 10 = d := mod_ten_eq_of_beginsWith hd0 hd10 hdp hpal
  -- `p` is divisible by `2` or `5`, hence `p = d` with `d ∈ {2, 5}`.
  have hpd : p = d ∧ (d = 2 ∨ d = 5) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have h2 : d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8 → p = 2 := fun h =>
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).1 (by omega)).symm
    have h5 : d = 5 → p = 5 := fun h =>
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hprime).1 (by omega)).symm
    omega
  obtain ⟨rfl, hd25⟩ := hpd
  -- `n` is a nonzero number whose expansion is a prefix of the one-digit `[p]`.
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [BeginsWith, Nat.digits_zero, List.reverse_nil, List.prefix_nil,
      List.reverse_eq_nil_iff] at hdn
    exact hd0 (Nat.digits_eq_nil_iff_eq_zero.1 hdn)
  have hnp' : (Nat.digits 10 n).reverse <+: [p] := by
    have hdig : Nat.digits 10 p = [p] := Nat.digits_of_lt 10 p hd0 hd10
    rw [BeginsWith, hdig] at hnp
    simpa using hnp
  have hnd : Nat.digits 10 n = [p] := by
    rcases hrev : (Nat.digits 10 n).reverse with _ | ⟨x, t⟩
    · rw [List.reverse_eq_nil_iff, Nat.digits_eq_nil_iff_eq_zero] at hrev
      exact absurd hrev hn0
    · rw [hrev, List.cons_prefix_cons, List.prefix_nil] at hnp'
      obtain ⟨rfl, rfl⟩ := hnp'
      rw [← List.reverse_reverse (Nat.digits 10 n), hrev]
      rfl
  have hnval : n = p := by
    rw [← Nat.ofDigits_digits 10 n, hnd]
    simp [Nat.ofDigits]
  omega

-- The zero terms `a(4) = a(6) = a(8) = a(20) = a(25) = 0` (listed terms 4, 6, 8,
-- 20, 25) as instances of the corrected direction; this also exhibits its
-- hypotheses as jointly satisfiable.
example : a 4 = 0 :=
  a_eq_zero_of_beginsWith (d := 4) (by decide) (by decide) (by decide) (by decide)
example : a 6 = 0 :=
  a_eq_zero_of_beginsWith (d := 6) (by decide) (by decide) (by decide) (by decide)
example : a 8 = 0 :=
  a_eq_zero_of_beginsWith (d := 8) (by decide) (by decide) (by decide) (by decide)
example : a 20 = 0 :=
  a_eq_zero_of_beginsWith (d := 2) (by decide) (by decide) (by decide) (by decide)
example : a 25 = 0 :=
  a_eq_zero_of_beginsWith (d := 2) (by decide) (by decide) (by decide) (by decide)

end Candidates.A109864Refutation
