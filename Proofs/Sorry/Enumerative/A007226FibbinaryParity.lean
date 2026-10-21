/-
# A007226 — Bala: parity of `2 C(3n,n)/(n+1)` and the odd Fibbinary numbers

## OEIS source (retrieved with `oeis show A007226`, 2026-10-21)

```
NAME:     a(n) = 2*det(M(n; -1))/det(M(n; 0)), where M(n; m) is the n X n matrix
          with (i,j)-th element equal to 1/binomial(n + i + j + m, n).
OFFSET:   0
TERMS:    2,3,10,42,198,1001,5304,29070,163438,937365,5462730,32256120,
          192565800,1160346492,7048030544,43108428198,265276342782,...
KEYWORDS: nonn,easy
FORMULA:  a(n) = (2/(n + 1))*binomial(3*n, n).
FORMULA:  a(n) = 2*C(3*n, n) - C(3*n, n+1) for n >= 0. - _David Callan_, Oct 25 2004
FORMULA:  a(n) = (2n+1) * A000139(n). - _F. Chapoton_, Feb 23 2024
COMMENT (the conjecture):
  Conjecture: a(n) is odd iff n = A022341(k) for some k. - _Peter Bala_, Mar 13 2023
```

A022341: "a(n) = 4*A003714(n) + 1; the odd Fibbinary numbers", and A003714
(Fibbinary numbers) are the "numbers whose binary representation contains no
two adjacent 1's", i.e. the `m` with `m AND 2m = 0`.

**Definitional-fidelity note.**  The entry's NAME is a determinant ratio; its
first FORMULA line `a(n) = (2/(n+1)) binomial(3n, n)` is the closed form used by
every program in the entry and by the triage.  The definition below is that
closed form, checked against the first 15 DATA terms; the `Nat` division is
shown exact (`a_mul_succ`).

## Status

Triage: open (no proof in the entry).  Literature: the problem list of the
Third International Conference on Permutation Patterns (2005,
arXiv:math/0505504) records as known, crediting Miklós Bóna, that the number
of 2-stack-sortable permutations (A000139) of length `n` is odd iff the binary
expansion of `n` ends in `1` with no two adjacent `1`s.  Since
`A007226(n) = (2n+1) A000139(n)` (Chapoton's formula) and `2n+1` is odd, this
conjecture is a direct corollary of that known result.  The proof below is
elementary and self-contained.  Computational check (Python, 2026-10-21): the parity
claim holds for every `0 ≤ n < 20000` (direct binomials), and the first 25
DATA terms agree with the closed form.

## Proof outline (formalized below, no `sorry`)

1. Callan's identity `a(n) = 2 C(3n,n) - C(3n,n+1)`, so `a(n) ≡ C(3n,n+1) (mod 2)`.
2. Lucas at `p = 2`: `C(a+b, a)` is odd iff `a AND b = 0`; for `n ≥ 1`,
   `C(3n, n+1) = C((n+1) + (2n-1), n+1)`.
3. Bit bridge: `(n+1) AND (2n-1) = 0` iff `n = 4m+1` with `m AND 2m = 0`.

The bitwise helpers and the Lucas step duplicate those of the sibling card
`Proofs/Sorry/Enumerative/A000139TwoStackParity.lean` (a `Sorry` module, which
may not be imported).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A007226FibbinaryParity

/-! ## Definition layer -/

/-- OEIS A007226 (first FORMULA line): `a(n) = 2 binomial(3n, n) / (n + 1)`,
offset `0`.  The `Nat` division is exact (`a_mul_succ`). -/
def a (n : ℕ) : ℕ := 2 * (3 * n).choose n / (n + 1)

/-- Fibbinary numbers (OEIS A003714): no two adjacent `1`s in binary, i.e.
`m AND 2m = 0`. -/
def IsFibbinary (m : ℕ) : Prop := m &&& (2 * m) = 0

/-- `IsFibbinary` is decided by evaluating `m AND 2m`. -/
instance : DecidablePred IsFibbinary := fun m => inferInstanceAs (Decidable (m &&& (2 * m) = 0))

-- Ground truth against the OEIS DATA line `2,3,10,42,198,1001,5304,…`.
example : (List.range 15).map a =
    [2, 3, 10, 42, 198, 1001, 5304, 29070, 163438, 937365, 5462730, 32256120,
      192565800, 1160346492, 7048030544] := by
  decide

-- Ground truth against the A003714 DATA line `0,1,2,4,5,8,9,10,16,17,18,20,21,32`.
example : (List.range 33).filter (fun m => decide (IsFibbinary m)) =
    [0, 1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21, 32] := by
  decide

/-! ## Helper lemmas -/

/-- `(2a) AND (2b) = 2 (a AND b)`. -/
theorem land_ee (a b : ℕ) : (2 * a) &&& (2 * b) = 2 * (a &&& b) := by
  have h := Nat.land_bit false a false b
  simpa [Nat.bit] using h
/-- `(2a) AND (2b+1) = 2 (a AND b)`. -/
theorem land_eo (a b : ℕ) : (2 * a) &&& (2 * b + 1) = 2 * (a &&& b) := by
  have h := Nat.land_bit false a true b
  simpa [Nat.bit] using h
/-- `(2a+1) AND (2b) = 2 (a AND b)`. -/
theorem land_oe (a b : ℕ) : (2 * a + 1) &&& (2 * b) = 2 * (a &&& b) := by
  have h := Nat.land_bit true a false b
  simpa [Nat.bit] using h
/-- `(2a+1) AND (2b+1) = 2 (a AND b) + 1`. -/
theorem land_oo (a b : ℕ) : (2 * a + 1) &&& (2 * b + 1) = 2 * (a &&& b) + 1 := by
  have h := Nat.land_bit true a true b
  simpa [Nat.bit] using h

/-- Lucas's theorem at `p = 2`, one digit at a time (Mathlib's
`Choose.choose_modEq_choose_mod_mul_choose_div_nat` unfolded as an equation of residues). -/
theorem choose_mod_two_lucas (n k : ℕ) :
    Nat.choose n k % 2 = (Nat.choose (n % 2) (k % 2) * Nat.choose (n / 2) (k / 2)) % 2 :=
  Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := n) (k := k)

/-- Lucas/Kummer at `p = 2`: `C(a+b, a)` is odd iff `a` and `b` share no binary
`1` digit, i.e. `a AND b = 0`. -/
theorem odd_choose_add_iff (a b : ℕ) : Odd (Nat.choose (a + b) a) ↔ a &&& b = 0 := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
  subst h
  rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩ <;>
    rcases Nat.even_or_odd' b with ⟨b', rfl | rfl⟩
  · -- even, even
    by_cases h0 : a' + b' = 0
    · obtain ⟨rfl, rfl⟩ : a' = 0 ∧ b' = 0 := by omega
      simp
    have hl := choose_mod_two_lucas (2 * a' + 2 * b') (2 * a')
    have e1 : (2 * a' + 2 * b') % 2 = 0 := by omega
    have e2 : (2 * a') % 2 = 0 := by omega
    have e3 : (2 * a' + 2 * b') / 2 = a' + b' := by omega
    have e4 : (2 * a') / 2 = a' := by omega
    rw [e1, e2, e3, e4, Nat.choose_zero_right, one_mul] at hl
    rw [Nat.odd_iff, hl, ← Nat.odd_iff, ih (a' + b') (by omega) a' b' rfl, land_ee]
    omega
  · -- even, odd
    have hl := choose_mod_two_lucas (2 * a' + (2 * b' + 1)) (2 * a')
    have e1 : (2 * a' + (2 * b' + 1)) % 2 = 1 := by omega
    have e2 : (2 * a') % 2 = 0 := by omega
    have e3 : (2 * a' + (2 * b' + 1)) / 2 = a' + b' := by omega
    have e4 : (2 * a') / 2 = a' := by omega
    rw [e1, e2, e3, e4, Nat.choose_zero_right, one_mul] at hl
    rw [Nat.odd_iff, hl, ← Nat.odd_iff, ih (a' + b') (by omega) a' b' rfl, land_eo]
    omega
  · -- odd, even
    have hl := choose_mod_two_lucas (2 * a' + 1 + 2 * b') (2 * a' + 1)
    have e1 : (2 * a' + 1 + 2 * b') % 2 = 1 := by omega
    have e2 : (2 * a' + 1) % 2 = 1 := by omega
    have e3 : (2 * a' + 1 + 2 * b') / 2 = a' + b' := by omega
    have e4 : (2 * a' + 1) / 2 = a' := by omega
    rw [e1, e2, e3, e4, Nat.choose_self, one_mul] at hl
    rw [Nat.odd_iff, hl, ← Nat.odd_iff, ih (a' + b') (by omega) a' b' rfl, land_oe]
    omega
  · -- odd, odd
    have hl := choose_mod_two_lucas (2 * a' + 1 + (2 * b' + 1)) (2 * a' + 1)
    have e1 : (2 * a' + 1 + (2 * b' + 1)) % 2 = 0 := by omega
    have e2 : (2 * a' + 1) % 2 = 1 := by omega
    rw [e1, e2, Nat.choose_zero_succ, zero_mul] at hl
    rw [Nat.odd_iff, hl, land_oo]
    omega

/-- `(k+1) AND (2k+1)` is never `0`. -/
theorem land_succ_two_mul_succ_ne_zero (k : ℕ) : (k + 1) &&& (2 * k + 1) ≠ 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have e : 2 * j + 1 &&& 2 * (2 * j) + 1 = 2 * (j &&& 2 * j) + 1 := land_oo j (2 * j)
    rw [e]; omega
  · have e : 2 * j + 1 + 1 &&& 2 * (2 * j + 1) + 1 = 2 * (j + 1 &&& 2 * j + 1) := by
      have h := land_eo (j + 1) (2 * j + 1)
      rwa [show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
        show 2 * (2 * j + 1) + 1 = 2 * (2 * j + 1) + 1 from rfl] at h
    rw [e]
    have := ih j (by omega)
    omega

/-- `(m+1) AND 2m = 0` iff `m AND (2m+1) = 0`. -/
theorem land_succ_two_mul_iff (m : ℕ) : (m + 1) &&& (2 * m) = 0 ↔ m &&& (2 * m + 1) = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have e1 : 2 * k + 1 &&& 2 * (2 * k) = 2 * (k &&& 2 * k) := land_oe k (2 * k)
    have e2 : 2 * k &&& 2 * (2 * k) + 1 = 2 * (k &&& 2 * k) := land_eo k (2 * k)
    rw [e1, e2]
  · have e1 : 2 * k + 1 + 1 &&& 2 * (2 * k + 1) = 2 * (k + 1 &&& 2 * k + 1) := by
      have h := land_ee (k + 1) (2 * k + 1)
      rwa [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h
    have e2 : 2 * k + 1 &&& 2 * (2 * k + 1) + 1 = 2 * (k &&& 2 * k + 1) + 1 :=
      land_oo k (2 * k + 1)
    rw [e1, e2]
    have := land_succ_two_mul_succ_ne_zero k
    omega

/-- Bit bridge with `n = m + 1`: `(n+1) AND (2n-1) = 0` iff `n` is odd and
`n AND 2n = 0`. -/
theorem land_bridge (m : ℕ) :
    (m + 2) &&& (2 * m + 1) = 0 ↔ Odd (m + 1) ∧ (m + 1) &&& (2 * (m + 1)) = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · -- n = 2k+1 odd
    have e1 : 2 * k + 2 &&& 2 * (2 * k) + 1 = 2 * (k + 1 &&& 2 * k) := by
      have h := land_eo (k + 1) (2 * k)
      rwa [show 2 * (k + 1) = 2 * k + 2 by ring] at h
    have e2 : 2 * k + 1 &&& 2 * (2 * k + 1) = 2 * (k &&& 2 * k + 1) := by
      have h := land_oe k (2 * k + 1)
      exact h
    rw [e1, e2]
    have hc := land_succ_two_mul_iff k
    have ho : Odd (2 * k + 1) := ⟨k, rfl⟩
    simp only [ho, true_and]
    omega
  · -- n = 2k+2 even
    have e1 : 2 * k + 1 + 2 &&& 2 * (2 * k + 1) + 1 = 2 * (k + 1 &&& 2 * k + 1) + 1 := by
      have h := land_oo (k + 1) (2 * k + 1)
      rwa [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring] at h
    have hne : ¬ Odd (2 * k + 1 + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩
    rw [e1]
    simp only [hne, false_and, iff_false]
    omega

/-- Odd Fibbinary numbers (A022341) are exactly `4f + 1` with `f` Fibbinary
(A003714, `f AND 2f = 0`): `n` odd with `n AND 2n = 0` iff `n = 4f + 1` for such `f`. -/
theorem odd_and_land_iff (n : ℕ) :
    Odd n ∧ n &&& (2 * n) = 0 ↔ ∃ f : ℕ, f &&& (2 * f) = 0 ∧ n = 4 * f + 1 := by
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    have e1 : 2 * k + 1 &&& 2 * (2 * k + 1) = 2 * (k &&& 2 * k + 1) := land_oe k (2 * k + 1)
    rw [e1] at hk
    have hk' : k &&& 2 * k + 1 = 0 := by omega
    rcases Nat.even_or_odd' k with ⟨f, rfl | rfl⟩
    · have e2 : 2 * f &&& 2 * (2 * f) + 1 = 2 * (f &&& 2 * f) := land_eo f (2 * f)
      rw [e2] at hk'
      exact ⟨f, by omega, by ring⟩
    · have e2 : 2 * f + 1 &&& 2 * (2 * f + 1) + 1 = 2 * (f &&& 2 * f + 1) + 1 :=
        land_oo f (2 * f + 1)
      rw [e2] at hk'
      omega
  · rintro ⟨f, hf, rfl⟩
    refine ⟨⟨2 * f, by ring⟩, ?_⟩
    have e1 : 2 * (2 * f) + 1 &&& 2 * (2 * (2 * f) + 1) = 2 * (2 * f &&& 2 * (2 * f) + 1) :=
      land_oe (2 * f) (2 * (2 * f) + 1)
    have e2 : 2 * f &&& 2 * (2 * f) + 1 = 2 * (f &&& 2 * f) := land_eo f (2 * f)
    rw [show 4 * f + 1 = 2 * (2 * f) + 1 by ring, e1, e2, hf]

/-! ## Callan's identity and exactness of the division -/

/-- `C(3n, n+1) (n+1) = 2n C(3n, n)`. -/
theorem choose_succ_mul (n : ℕ) :
    (3 * n).choose (n + 1) * (n + 1) = (3 * n).choose n * (2 * n) := by
  rw [Nat.choose_succ_right_eq, show 3 * n - n = 2 * n by omega]

/-- The division defining `a` is exact: `a(n) (n+1) = 2 C(3n, n)`. -/
theorem a_mul_succ (n : ℕ) : a n * (n + 1) = 2 * (3 * n).choose n := by
  have hz : ((n + 1 : ℕ) : ℤ) ∣ ((2 * (3 * n).choose n : ℕ) : ℤ) := by
    refine ⟨2 * ((3 * n).choose n : ℤ) - ((3 * n).choose (n + 1) : ℤ), ?_⟩
    have h := congrArg (Nat.cast : ℕ → ℤ) (choose_succ_mul n)
    push_cast at h ⊢
    linear_combination h
  exact Nat.div_mul_cancel (Int.natCast_dvd_natCast.mp hz)

/-- **Callan's identity** (A007226 FORMULA, David Callan, Oct 25 2004):
`a(n) = 2 C(3n, n) - C(3n, n+1)`, stated in `ℤ`. -/
theorem a_eq_callan (n : ℕ) :
    (a n : ℤ) = 2 * ((3 * n).choose n : ℤ) - ((3 * n).choose (n + 1) : ℤ) := by
  have h1 := congrArg (Nat.cast : ℕ → ℤ) (choose_succ_mul n)
  have h2 := congrArg (Nat.cast : ℕ → ℤ) (a_mul_succ n)
  push_cast at h1 h2
  have hne : ((n : ℤ) + 1) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  linear_combination h2 + h1

/-- `a(n)` has the parity of `C(3n, n+1)`. -/
theorem odd_a_iff (n : ℕ) : Odd (a n) ↔ Odd ((3 * n).choose (n + 1)) := by
  have h := a_eq_callan n
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-! ## The conjecture -/

/-- **Bala's conjecture (A007226, Peter Bala, Mar 13 2023), proved.**

Verbatim: "Conjecture: a(n) is odd iff n = A022341(k) for some k."  With
`a(n) = 2 binomial(3n, n)/(n+1)` (offset `0`) and A022341 the odd Fibbinary
numbers `4m + 1` (`m` Fibbinary, `m AND 2m = 0`), this says: `a(n)` is odd iff
`n = 4m + 1` for some Fibbinary `m`. -/
theorem a_odd_iff (n : ℕ) : Odd (a n) ↔ ∃ m : ℕ, IsFibbinary m ∧ n = 4 * m + 1 := by
  rw [odd_a_iff]
  rcases n with _ | k
  · simp
  · have hc : (3 * (k + 1)).choose (k + 1 + 1) = ((k + 2) + (2 * k + 1)).choose (k + 2) := by
      congr 1; ring
    rw [hc, odd_choose_add_iff, land_bridge, odd_and_land_iff]
    rfl

/-! ## Sanity layer -/

-- Both sides are inhabited: `n = 1` (`m = 0`, `a(1) = 3` odd), `n = 5`
-- (`m = 1`, `a(5) = 1001` odd), and `n = 13` is `4·3 + 1` with `3` not
-- Fibbinary, `a(13) = 1160346492` even.
example : Odd (a 1) ∧ IsFibbinary 0 ∧ Odd (a 5) ∧ IsFibbinary 1 := by decide
example : ¬ Odd (a 13) ∧ ¬ IsFibbinary 3 := by decide

end Candidates.A007226FibbinaryParity
