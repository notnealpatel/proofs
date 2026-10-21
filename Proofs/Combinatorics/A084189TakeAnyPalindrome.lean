/-
# A084189 — Earls: palindromic factors of palindromic semiprimes have a digit ≤ 3

## OEIS source (retrieved with `oeis show A084189` and https://oeis.org/A084189, 2026-10-21)

```
NAME:     Minimum digit out of both prime factors of the numbers in A046376.
TERMS:    2,2,3,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,1,0,0,0,0,0,0,1,1,1,1,1,
          0,0,1,0,0,0,1,0,0,0,0,2,2,0,0,0,2,0,0,0,1,1,1,1,1,1,1,0,1,1,0,0,...
COMMENT:  Conjecture: a(n) is never greater than 3.
COMMENT:  Suggested by this old JRM problem: "Find a composite palindrome larger
          than 343 whose prime factors are palindromes consisting of digits
          greater than 3."
AUTHOR:   Jason Earls, Jun 20 2003
```

The conjecture comment is unsigned; it belongs to the original submission
(Jason Earls, Jun 20 2003).

A046376 (the index set): "Palindromes with exactly 2 palindromic prime factors
(counted with multiplicity), and no other prime factors", i.e. palindromic
semiprimes `p * q` (`p ≤ q` prime) whose prime factors are palindromes.
Terms: 4, 6, 9, 22, 33, 55, 77, 121, 202, 262, 303, ...

## Status

Triage: "open" in the entry and in the literature as far as the triage could
tell.  This module proves it (statement `a084189_conjecture`) by a
leading/trailing-digit argument: a palindromic prime all of whose digits are
`≥ 4` is `5` or ends (hence starts) in `7` or `9`; the leading digit of the
product then lies in a range that never contains its last digit.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A084189TakeAnyPalindrome

/-! ## Definition layer -/

/-- A natural number is a (base-10) palindrome when its digit list reads the
same reversed.  `Nat.digits 10 n` is little-endian; reversal symmetry is
independent of the endianness.  (`0` has the empty digit list and counts as a
palindrome; this plays no role, since all numbers below are positive.) -/
def IsPal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

instance : DecidablePred IsPal := fun _ => inferInstanceAs (Decidable (_ = _))

/-- Membership in A046376: `n` is a palindrome of the form `p * q` with
`p ≤ q` primes that are both palindromes. -/
def InA046376 (n : ℕ) : Prop :=
  IsPal n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ IsPal p ∧ IsPal q ∧ p * q = n

/-- The A084189 term attached to the factorization `p * q`: the minimum
decimal digit occurring in `p` or in `q`.  It is computed as a right fold of
`min` starting at `9`; since every decimal digit is `≤ 9`, this is exactly the
minimum digit whenever the digit list is nonempty (e.g. `p` prime). -/
def minFactorDigit (p q : ℕ) : ℕ := (Nat.digits 10 p ++ Nat.digits 10 q).foldr min 9

/-! ### Ground truth against the first terms of A046376 and A084189 -/

example : IsPal 121 := by decide
example : ¬ IsPal 25 := by decide
example : IsPal 3443 := by decide

/-- `4 = 2 * 2` is the first term of A046376. -/
example : InA046376 4 := ⟨by decide, 2, 2, by norm_num, by norm_num, le_rfl, by decide,
  by decide, rfl⟩

/-- `22 = 2 * 11` is the fourth term of A046376. -/
example : InA046376 22 := ⟨by decide, 2, 11, by norm_num, by norm_num, by norm_num,
  by decide, by decide, rfl⟩

/-- `3443 = 11 * 313` is a term of A046376. -/
example : InA046376 3443 := ⟨by decide, 11, 313, by norm_num, by norm_num, by norm_num,
  by decide, by decide, rfl⟩

/-- First terms of A084189: `4 = 2*2, 6 = 2*3, 9 = 3*3, 22 = 2*11, 33 = 3*11,
55 = 5*11, 77 = 7*11, 121 = 11*11, 202 = 2*101` give `2, 2, 3, 1, 1, 1, 1, 1, 0`. -/
example : [minFactorDigit 2 2, minFactorDigit 2 3, minFactorDigit 3 3, minFactorDigit 2 11,
    minFactorDigit 3 11, minFactorDigit 5 11, minFactorDigit 7 11, minFactorDigit 11 11,
    minFactorDigit 2 101] = [2, 2, 3, 1, 1, 1, 1, 1, 0] := by decide

/-- Bridge: `minFactorDigit p q ≤ 3` says exactly that some digit of `p` or `q`
is `≤ 3`. -/
theorem minFactorDigit_le_three_iff (p q : ℕ) :
    minFactorDigit p q ≤ 3 ↔ ∃ d ∈ Nat.digits 10 p ++ Nat.digits 10 q, d ≤ 3 := by
  unfold minFactorDigit
  induction Nat.digits 10 p ++ Nat.digits 10 q with
  | nil => simp
  | cons a l ih => simp [ih]

/-! ## Digit lemmas -/

/-- A positive palindrome `n` with last digit `c = n % 10` also has leading
digit `c`: for some `m`, `c * 10 ^ m ≤ n < (c + 1) * 10 ^ m`. -/
theorem exists_lead_bounds_of_isPal (n : ℕ) (hn : 0 < n) (hpal : IsPal n) :
    ∃ m : ℕ, (n % 10) * 10 ^ m ≤ n ∧ n < (n % 10 + 1) * 10 ^ m := by
  set c := n % 10 with hc
  set L := Nat.digits 10 n with hL
  have hpal' : L.reverse = L := hpal
  have hne : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  have hcons : L = c :: Nat.digits 10 (n / 10) := Nat.digits_def' (by norm_num) hn
  have hlast : L.getLast hne = c := by
    have h1 : L.getLast? = some c := by
      rw [← List.head?_reverse, hpal', hcons, List.head?_cons]
    rw [List.getLast?_eq_some_getLast hne] at h1
    exact Option.some_injective _ h1
  have hsplit : n = Nat.ofDigits 10 L.dropLast + 10 ^ L.dropLast.length * c := by
    have h := List.dropLast_append_getLast hne
    rw [hlast] at h
    calc n = Nat.ofDigits 10 L := (Nat.ofDigits_digits 10 n).symm
      _ = Nat.ofDigits 10 (L.dropLast ++ [c]) := by rw [h]
      _ = _ := by rw [Nat.ofDigits_append, Nat.ofDigits_singleton]
  have hlt : Nat.ofDigits 10 L.dropLast < 10 ^ L.dropLast.length :=
    Nat.ofDigits_lt_base_pow_length (by norm_num) fun x hx =>
      Nat.digits_lt_base (m := n) (by norm_num) (List.mem_of_mem_dropLast hx)
  refine ⟨L.dropLast.length, ?_, ?_⟩
  · generalize Nat.ofDigits 10 L.dropLast = A at hsplit hlt
    generalize 10 ^ L.dropLast.length = t at hsplit hlt ⊢
    rw [hsplit, mul_comm c t]
    exact Nat.le_add_left _ _
  · generalize Nat.ofDigits 10 L.dropLast = A at hsplit hlt
    generalize 10 ^ L.dropLast.length = t at hsplit hlt ⊢
    rw [add_mul, one_mul, mul_comm c t]
    omega

/-- A prime all of whose decimal digits are `≥ 4` is `5` or ends in `7` or `9`. -/
theorem eq_five_or_mod_ten_of_prime (p : ℕ) (hp : p.Prime)
    (hd : ∀ d ∈ Nat.digits 10 p, 4 ≤ d) : p = 5 ∨ p % 10 = 7 ∨ p % 10 = 9 := by
  have hmem : p % 10 ∈ Nat.digits 10 p := by
    rw [Nat.digits_def' (by norm_num) hp.pos]
    exact List.mem_cons_self
  have h4 : 4 ≤ p % 10 := hd _ hmem
  have hlt : p % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have h2 : ¬ 2 ∣ p := by
    intro h2
    have hp2 : p = 2 := ((hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)).symm
    omega
  have h5 : 5 ∣ p → p = 5 := fun h5 =>
    ((hp.eq_one_or_self_of_dvd 5 h5).resolve_left (by norm_num)).symm
  have hodd : p % 2 = 1 := by omega
  by_cases hfive : p % 10 = 5
  · exact Or.inl (h5 (by omega))
  · right; omega

/-- Comparison of two powers of ten: `10 ^ m` is at most `10 ^ s`, equal to
`10 * 10 ^ s`, or at least `100 * 10 ^ s`. -/
theorem ten_pow_trichotomy (m s : ℕ) :
    10 ^ m ≤ 10 ^ s ∨ 10 ^ m = 10 * 10 ^ s ∨ 100 * 10 ^ s ≤ 10 ^ m := by
  rcases Nat.lt_or_ge s m with h | h
  · rcases Nat.lt_or_ge (s + 1) m with h' | h'
    · right; right
      calc 100 * 10 ^ s = 10 ^ (s + 2) := by ring
        _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) h'
    · right; left
      rw [show m = s + 1 by omega, pow_succ, mul_comm]
  · left; exact Nat.pow_le_pow_right (by norm_num) h

/-! ## The core case analysis -/

/-- If `p = 5` and `q` is `5` or a positive number whose leading and last digit
are both `7` or both `9`, then `p * q` is not a palindrome. -/
theorem not_isPal_five_mul (q : ℕ) (hq : q = 5 ∨
    ((q % 10 = 7 ∨ q % 10 = 9) ∧ ∃ b : ℕ, (q % 10) * 10 ^ b ≤ q ∧ q < (q % 10 + 1) * 10 ^ b)) :
    ¬ IsPal (5 * q) := by
  intro hpal
  have hpos : 0 < 5 * q := by rcases hq with h | ⟨h, -⟩ <;> omega
  obtain ⟨m, hm1, hm2⟩ := exists_lead_bounds_of_isPal _ hpos hpal
  rcases hq with h | ⟨he, b, hb1, hb2⟩
  · subst h
    rcases ten_pow_trichotomy m 0 with ht | ht | ht <;> norm_num at hm1 hm2 ht <;> omega
  · have hc : 5 * q % 10 = 5 := by omega
    rw [hc] at hm1 hm2
    rcases ten_pow_trichotomy m b with ht | ht | ht <;>
    rcases he with he | he <;> rw [he] at hb1 hb2 <;> omega

/-- If `p` and `q` both have leading digit equal to their last digit, and that
digit is `7` or `9`, then `p * q` is not a palindrome. -/
theorem not_isPal_mul_of_lead (p q : ℕ) (hp : p % 10 = 7 ∨ p % 10 = 9)
    (hq : q % 10 = 7 ∨ q % 10 = 9)
    (hpb : ∃ a : ℕ, (p % 10) * 10 ^ a ≤ p ∧ p < (p % 10 + 1) * 10 ^ a)
    (hqb : ∃ b : ℕ, (q % 10) * 10 ^ b ≤ q ∧ q < (q % 10 + 1) * 10 ^ b) :
    ¬ IsPal (p * q) := by
  intro hpal
  obtain ⟨a, ha1, ha2⟩ := hpb
  obtain ⟨b, hb1, hb2⟩ := hqb
  have hpos : 0 < p * q := Nat.mul_pos (by omega) (by omega)
  obtain ⟨m, hm1, hm2⟩ := exists_lead_bounds_of_isPal _ hpos hpal
  have hc : p * q % 10 = (p % 10) * (q % 10) % 10 := Nat.mul_mod _ _ _
  have hN1 : (p % 10) * (q % 10) * 10 ^ (a + b) ≤ p * q := by
    calc (p % 10) * (q % 10) * 10 ^ (a + b) = ((p % 10) * 10 ^ a) * ((q % 10) * 10 ^ b) := by
          ring
      _ ≤ p * q := Nat.mul_le_mul ha1 hb1
  have hN2 : p * q < (p % 10 + 1) * (q % 10 + 1) * 10 ^ (a + b) := by
    calc p * q < ((p % 10 + 1) * 10 ^ a) * ((q % 10 + 1) * 10 ^ b) :=
          Nat.mul_lt_mul'' ha2 hb2
      _ = (p % 10 + 1) * (q % 10 + 1) * 10 ^ (a + b) := by ring
  rw [hc] at hm1 hm2
  have ht := ten_pow_trichotomy m (a + b)
  generalize p * q = N at hm1 hm2 hN1 hN2
  generalize 10 ^ m = M at hm1 hm2 ht
  generalize 10 ^ (a + b) = T at hN1 hN2 ht
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq] at hm1 hm2 hN1 hN2 <;>
    norm_num at hm1 hm2 hN1 hN2 <;> omega

/-! ## The conjecture -/

/-- **Equivalent form (A084189 comment).** No palindromic semiprime `p * q`
has palindromic prime factors `p, q` made only of digits `4, …, 9`. -/
theorem not_isPal_mul_of_digits_ge_four (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpp : IsPal p) (hqp : IsPal q)
    (hd : ∀ d ∈ Nat.digits 10 p ++ Nat.digits 10 q, 4 ≤ d) : ¬ IsPal (p * q) := by
  have hdp : ∀ d ∈ Nat.digits 10 p, 4 ≤ d := fun d h => hd d (List.mem_append_left _ h)
  have hdq : ∀ d ∈ Nat.digits 10 q, 4 ≤ d := fun d h => hd d (List.mem_append_right _ h)
  rcases eq_five_or_mod_ten_of_prime p hp hdp with hp5 | hp79 <;>
  rcases eq_five_or_mod_ten_of_prime q hq hdq with hq5 | hq79
  · subst hp5 hq5; decide
  · subst hp5
    exact not_isPal_five_mul q
      (Or.inr ⟨hq79, exists_lead_bounds_of_isPal q hq.pos hqp⟩)
  · subst hq5
    rw [mul_comm]
    exact not_isPal_five_mul p
      (Or.inr ⟨hp79, exists_lead_bounds_of_isPal p hp.pos hpp⟩)
  · exact not_isPal_mul_of_lead p q hp79 hq79 (exists_lead_bounds_of_isPal p hp.pos hpp)
      (exists_lead_bounds_of_isPal q hq.pos hqp)

/-- **A084189 conjecture (Jason Earls, Jun 20 2003): "a(n) is never greater
than 3."**  For every term `n = p * q` of A046376 (`n` a palindrome, `p ≤ q`
primes that are palindromes), the minimum digit occurring in `p` or `q` is at
most `3`.  The factorization of a semiprime is unique, so `minFactorDigit p q`
is the term `a(n)`. -/
theorem a084189_conjecture (n p q : ℕ) (hn : IsPal n) (hp : p.Prime) (hq : q.Prime)
    (_hpq : p ≤ q) (hpp : IsPal p) (hqp : IsPal q) (hnpq : p * q = n) :
    minFactorDigit p q ≤ 3 := by
  rw [minFactorDigit_le_three_iff]
  by_contra hcon
  have hd : ∀ d ∈ Nat.digits 10 p ++ Nat.digits 10 q, 4 ≤ d := fun d hd => by
    by_contra hlt
    exact hcon ⟨d, hd, by omega⟩
  exact not_isPal_mul_of_digits_ge_four p q hp hq hpp hqp hd (hnpq ▸ hn)

/-- The conjecture phrased over A046376 membership. -/
theorem a084189_conjecture_of_mem (n : ℕ) (hn : InA046376 n) :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → IsPal p → IsPal q → p * q = n →
      minFactorDigit p q ≤ 3 :=
  fun p q hp hq hpq hpp hqp hnpq => a084189_conjecture n p q hn.1 hp hq hpq hpp hqp hnpq

end Candidates.A084189TakeAnyPalindrome
