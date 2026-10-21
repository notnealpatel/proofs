/-
# A016789 — Breysens: `3n + 2 = n XOR A005351(n+1) XOR A005352(n+1)`

## OEIS source (retrieved with `oeis show A016789`, 2026-10-21)

```
NAME:     a(n) = 3*n + 2.
TERMS:    2,5,8,11,14,17,20,23,26,29,32,35,38,41,44,47,50,53,56,59,62,65,68,...
FORMULA (the conjecture):
  Conjecture: a(n) = n XOR A005351(n+1) XOR A005352(n+1).
  - Gilian Breysens, Jul 21 2017
```

Cross-referenced entries (retrieved with `oeis show`, 2026-10-21):

```
A005351  NAME:  Base -2 representation for n regarded as base 2, then evaluated.
         TERMS: 0,1,6,7,4,5,26,27,24,25,30,31,28,29,18,19,16,17,22,23,...  (offset 0)
A005352  NAME:  Base -2 representation of -n reinterpreted as binary.
         TERMS: 3,2,13,12,15,14,9,8,11,10,53,52,55,54,49,48,51,50,61,60,...  (offset 1)
```

## Status

Triage: open. The entry records the identity as a conjecture; the entry's
"mentions proof" flag refers to a different (Detlefs) comment, so no proof of
this XOR identity is recorded in the entry, and the triage found none in the
literature. Numerically checked for `n < 400000` and 20000 random `n < 10^30`
(2026-10-21) before formalization.

## Result

Proved here (`breysens_xor`), with no `sorry`. The argument is a simultaneous
strong induction on two companion identities
* `P(n)`: `nb(n+1) XOR nb(-(n+1)) = n XOR (3n+2)`;
* `Q(n)`: `nb(-n) XOR nb(n+1) = n XOR (3n+1)`;
using the digit recursions `nb(2k) = 2 nb(-k)`, `nb(2k+1) = 2 nb(-k) + 1`,
the bitwise rules `(2a+r) XOR (2b+s) = 2 (a XOR b) + (r XOR s)`, and the
carry lemma `(j+1) XOR (3j+3) = j XOR (3j+2)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A016789XorBaseDigit

/-! ## Definition layer -/

/-- The base `-2` (negabinary) digit string of the integer `x`, read as a binary
numeral. The least digit is `x % 2 ∈ {0, 1}` and the remaining digits are those
of `-(x / 2)`, since `x = x % 2 + (-2) * (-(x / 2))`. -/
def negabin (x : ℤ) : ℕ :=
  if x = 0 then 0 else (x % 2).toNat + 2 * negabin (-(x / 2))
termination_by 2 * x.natAbs + (if x < 0 then 1 else 0)
decreasing_by
  split_ifs <;> omega

/-- OEIS A005351: the base `-2` representation of `n` regarded as base `2`. -/
def a005351 (n : ℕ) : ℕ := negabin n

/-- OEIS A005352: the base `-2` representation of `-n` reinterpreted as binary
(offset `1`). -/
def a005352 (n : ℕ) : ℕ := negabin (-(n : ℤ))

/-- OEIS A016789: `a(n) = 3 n + 2`. -/
def a016789 (n : ℕ) : ℕ := 3 * n + 2

/-! ## Ground truth against the DATA lines -/

example : (List.range 30).map a005351 =
    [0, 1, 6, 7, 4, 5, 26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23,
      20, 21, 106, 107, 104, 105, 110, 111, 108, 109] := by
  decide +kernel

example : (List.range 30).map (fun i => a005352 (i + 1)) =
    [3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 53, 52, 55, 54, 49, 48, 51, 50, 61, 60,
      63, 62, 57, 56, 59, 58, 37, 36, 39, 38] := by
  decide +kernel

example : (List.range 10).map a016789 = [2, 5, 8, 11, 14, 17, 20, 23, 26, 29] := by
  decide

-- The conjectured right-hand side matches the first DATA terms of A016789.
example : (List.range 20).map (fun n => n ^^^ a005351 (n + 1) ^^^ a005352 (n + 1)) =
    [2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 38, 41, 44, 47, 50, 53, 56, 59] := by
  decide +kernel

/-! ## Bitwise and digit recursions -/

/-- `(2a) XOR (2b) = 2 (a XOR b)`. -/
theorem xor_two_mul_two_mul (a b : ℕ) : (2 * a) ^^^ (2 * b) = 2 * (a ^^^ b) := by
  simpa [Nat.bit_val] using Nat.xor_bit false a false b

/-- `(2a+1) XOR (2b+1) = 2 (a XOR b)`. -/
theorem xor_two_mul_add_one_two_mul_add_one (a b : ℕ) :
    (2 * a + 1) ^^^ (2 * b + 1) = 2 * (a ^^^ b) := by
  simpa [Nat.bit_val] using Nat.xor_bit true a true b

/-- `(2a) XOR (2b+1) = 2 (a XOR b) + 1`. -/
theorem xor_two_mul_two_mul_add_one (a b : ℕ) :
    (2 * a) ^^^ (2 * b + 1) = 2 * (a ^^^ b) + 1 := by
  simpa [Nat.bit_val] using Nat.xor_bit false a true b

/-- `(2a+1) XOR (2b) = 2 (a XOR b) + 1`. -/
theorem xor_two_mul_add_one_two_mul (a b : ℕ) :
    (2 * a + 1) ^^^ (2 * b) = 2 * (a ^^^ b) + 1 := by
  simpa [Nat.bit_val] using Nat.xor_bit true a false b

/-- Negabinary digit recursion at an even integer: `nb(2k) = 2 nb(-k)`. -/
theorem negabin_two_mul (k : ℤ) : negabin (2 * k) = 2 * negabin (-k) := by
  rw [negabin]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simp [negabin]
  · have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k) / 2 = k := by omega
    rw [h1, h2]
    simp

/-- Negabinary digit recursion at an odd integer: `nb(2k+1) = 2 nb(-k) + 1`. -/
theorem negabin_two_mul_add_one (k : ℤ) :
    negabin (2 * k + 1) = 2 * negabin (-k) + 1 := by
  rw [negabin, if_neg (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2]
  simp only [Int.toNat_one]
  ring

/-- Carry lemma: `(j+1) XOR (3j+3) = j XOR (3j+2)`. Both `j+1` and `3(j+1)` have
the same number of trailing zeros followed by a `1`, so subtracting `1` flips the
same low bits of each. -/
theorem xor_succ_three_mul (j : ℕ) : (j + 1) ^^^ (3 * j + 3) = j ^^^ (3 * j + 2) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · have e2 : 3 * (2 * i) + 3 = 2 * (3 * i + 1) + 1 := by ring
    have e3 : 3 * (2 * i) + 2 = 2 * (3 * i + 1) := by ring
    rw [e2, e3, xor_two_mul_add_one_two_mul_add_one, xor_two_mul_two_mul]
  · have hi : (i + 1) ^^^ (3 * i + 3) = i ^^^ (3 * i + 2) := ih i (by omega)
    have e1 : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
    have e2 : 3 * (2 * i + 1) + 3 = 2 * (3 * i + 3) := by ring
    have e4 : 3 * (2 * i + 1) + 2 = 2 * (3 * i + 2) + 1 := by ring
    rw [e1, e2, e4, xor_two_mul_two_mul, xor_two_mul_add_one_two_mul_add_one, hi]

/-! ## The simultaneous induction -/

/-- The two companion identities, proved together by strong induction on `n`:
`nb(n+1) XOR nb(-(n+1)) = n XOR (3n+2)` and `nb(-n) XOR nb(n+1) = n XOR (3n+1)`. -/
theorem negabin_xor_pair (n : ℕ) :
    negabin ((n : ℤ) + 1) ^^^ negabin (-((n : ℤ) + 1)) = n ^^^ (3 * n + 2) ∧
    negabin (-(n : ℤ)) ^^^ negabin ((n : ℤ) + 1) = n ^^^ (3 * n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- `n = 2k`
    rcases k with _ | k
    · refine ⟨?_, ?_⟩ <;> decide +kernel
    · obtain ⟨_, hQ⟩ := ih (k + 1) (by omega)
      obtain ⟨hP, _⟩ := ih k (by omega)
      refine ⟨?_, ?_⟩
      · -- first identity at `n = 2(k+1)`, from the second at `k + 1`
        have a1 : ((2 * (k + 1) : ℕ) : ℤ) + 1 = 2 * ((k : ℤ) + 1) + 1 := by
          push_cast; ring
        have a2 : -(((2 * (k + 1) : ℕ) : ℤ) + 1) = 2 * (-((k : ℤ) + 1) - 1) + 1 := by
          push_cast; ring
        have a3 : -(-((k : ℤ) + 1) - 1) = ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
        have a4 : -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
        have e2 : 3 * (2 * (k + 1)) + 2 = 2 * (3 * (k + 1) + 1) := by ring
        rw [a2, a1, negabin_two_mul_add_one, negabin_two_mul_add_one, a3, a4,
          xor_two_mul_add_one_two_mul_add_one, hQ, e2, xor_two_mul_two_mul]
      · -- second identity at `n = 2(k+1)`, from the first at `k`
        have a1 : -(((2 * (k + 1) : ℕ) : ℤ)) = 2 * (-((k : ℤ) + 1)) := by push_cast; ring
        have a2 : (((2 * (k + 1) : ℕ) : ℤ) + 1) = 2 * ((k : ℤ) + 1) + 1 := by
          push_cast; ring
        have e2 : 3 * (2 * (k + 1)) + 1 = 2 * (3 * k + 3) + 1 := by ring
        rw [a1, a2, negabin_two_mul, negabin_two_mul_add_one, neg_neg,
          xor_two_mul_two_mul_add_one, hP, e2, xor_two_mul_two_mul_add_one,
          xor_succ_three_mul]
  · -- `n = 2k + 1`, both identities from the first at `k`
    obtain ⟨hP, _⟩ := ih k (by omega)
    refine ⟨?_, ?_⟩
    · have a1 : ((2 * k + 1 : ℕ) : ℤ) + 1 = 2 * ((k : ℤ) + 1) := by push_cast; ring
      have a2 : -(((2 * k + 1 : ℕ) : ℤ) + 1) = 2 * (-((k : ℤ) + 1)) := by push_cast; ring
      have e2 : 3 * (2 * k + 1) + 2 = 2 * (3 * k + 2) + 1 := by ring
      rw [a2, a1, negabin_two_mul, negabin_two_mul, neg_neg, xor_two_mul_two_mul,
        Nat.xor_comm, hP, e2, xor_two_mul_add_one_two_mul_add_one]
    · have a1 : -(((2 * k + 1 : ℕ) : ℤ)) = 2 * (-(k : ℤ) - 1) + 1 := by push_cast; ring
      have a2 : ((2 * k + 1 : ℕ) : ℤ) + 1 = 2 * ((k : ℤ) + 1) := by push_cast; ring
      have a3 : -(-(k : ℤ) - 1) = (k : ℤ) + 1 := by ring
      have e2 : 3 * (2 * k + 1) + 1 = 2 * (3 * k + 2) := by ring
      rw [a1, a2, negabin_two_mul_add_one, negabin_two_mul, a3,
        xor_two_mul_add_one_two_mul, hP, e2, xor_two_mul_add_one_two_mul]

/-! ## The conjecture -/

/-- **Breysens' conjecture (A016789, Gilian Breysens, Jul 21 2017), proved.**

Verbatim: "Conjecture: a(n) = n XOR A005351(n+1) XOR A005352(n+1)." where
`a(n) = 3n + 2`, `A005351(m)` is the base `-2` digit string of `m` read in base
`2`, and `A005352(m)` is that of `-m`. Holds for every `n ≥ 0`. -/
theorem breysens_xor (n : ℕ) : a016789 n = n ^^^ a005351 (n + 1) ^^^ a005352 (n + 1) := by
  have hpair := (negabin_xor_pair n).1
  have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  simp only [a016789, a005351, a005352, hcast]
  rw [Nat.xor_assoc, hpair, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

end Candidates.A016789XorBaseDigit
