/-
# Parity of A000139

For `twoStack n = 2 (3n)! / ((2n+1)! (n+1)!)`, oddness is equivalent to
`Odd n ∧ n AND 2n = 0`, or membership in A022341: `n = 4f+1` with
`f AND 2f = 0` (A003714). This includes `n = 0`, where `twoStack 0 = 2`.
Source: Peter Bala's comment in OEIS A000139 (Jul 24 2025).
The permutation-pattern problem list arXiv:math/0505504 attributes the
positive-index parity characterization to Miklós Bóna.

The proof reduces parity to `C(3n,n+1)`, then applies Lucas's theorem and
an elementary bitwise identity.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A000139TwoStackParity

/-! ## Definitions -/

/-- OEIS A000139: `a(n) = 2*(3n)! / ((2n+1)! (n+1)!)`, with offset `0`.  The
`Nat` division is exact (established inside the proof of `twoStack_succ_eq`;
`n = 0` gives `2`), so the definition carries no truncation junk. -/
def twoStack (n : ℕ) : ℕ :=
  2 * (3 * n).factorial / ((2 * n + 1).factorial * (n + 1).factorial)

-- Listed terms from the OEIS DATA line `2,1,2,6,22,91,408,1938,9614,49335,…`.
example : (List.range 10).map twoStack = [2, 1, 2, 6, 22, 91, 408, 1938, 9614, 49335] := by
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

/-- Integer identity, with `n = m + 1`:
`(2n+1)! (n+1)! * (2 C(3n,n) + C(3n,n+1) - 8 C(3n,n-1)) = 2 (3n)!`. -/
theorem key_identity (m : ℕ) :
    (((2 * m + 3).factorial * (m + 2).factorial : ℕ) : ℤ) *
      (2 * (Nat.choose (3 * m + 3) (m + 1) : ℤ) + (Nat.choose (3 * m + 3) (m + 2) : ℤ)
        - 8 * (Nat.choose (3 * m + 3) m : ℤ)) = 2 * ((3 * m + 3).factorial : ℤ) := by
  have h1 : Nat.choose (3 * m + 3) (m + 1) * (2 * m + 2).factorial * (m + 1).factorial =
      (3 * m + 3).factorial := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (2 * m + 2) (m + 1)
    rwa [show 2 * m + 2 + (m + 1) = 3 * m + 3 by ring] at h
  have h2 : Nat.choose (3 * m + 3) (m + 2) * (2 * m + 1).factorial * (m + 2).factorial =
      (3 * m + 3).factorial := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (2 * m + 1) (m + 2)
    rwa [show 2 * m + 1 + (m + 2) = 3 * m + 3 by ring] at h
  have h3 : Nat.choose (3 * m + 3) m * (2 * m + 3).factorial * m.factorial =
      (3 * m + 3).factorial := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (2 * m + 3) m
    rwa [show 2 * m + 3 + m = 3 * m + 3 by ring] at h
  have f1 : (2 * m + 3).factorial = (2 * m + 3) * ((2 * m + 2) * (2 * m + 1).factorial) := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 by ring, Nat.factorial_succ,
      show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ]
  have f2 : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  have f3 : (2 * m + 2).factorial = (2 * m + 2) * (2 * m + 1).factorial := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ]
  have f4 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
  rw [f3, f4] at h1
  rw [f2] at h2
  rw [f1] at h3
  rw [f1, f2]
  have i1 := congrArg (Nat.cast : ℕ → ℤ) h1
  have i2 := congrArg (Nat.cast : ℕ → ℤ) h2
  have i3 := congrArg (Nat.cast : ℕ → ℤ) h3
  push_cast at i1 i2 i3 ⊢
  linear_combination (2 * ((2 * (m : ℤ) + 3) * ((m : ℤ) + 2))) * i1 + (2 * (2 * (m : ℤ) + 3) * (m + 1)) * i2
    - 8 * ((m : ℤ) + 2) * (m + 1) * i3

/-- Integer closed form, for `n = m + 1`:
`a(n) = 2 C(3n,n) + C(3n,n+1) - 8 C(3n,n-1)` in `ℤ`.  The proof shows that
`(2n+1)! (n+1)!` divides `2 (3n)!`, so the `Nat` division in `twoStack` is exact. -/
theorem twoStack_succ_eq (m : ℕ) :
    (twoStack (m + 1) : ℤ) = 2 * (Nat.choose (3 * m + 3) (m + 1) : ℤ)
      + (Nat.choose (3 * m + 3) (m + 2) : ℤ) - 8 * (Nat.choose (3 * m + 3) m : ℤ) := by
  set D : ℕ := (2 * m + 3).factorial * (m + 2).factorial with hD
  set F : ℕ := (3 * m + 3).factorial with hF
  have hkey := key_identity m
  rw [← hD, ← hF] at hkey
  have hDpos : 0 < D := by positivity
  have hdvd : D ∣ 2 * F := by
    have hz : (D : ℤ) ∣ ((2 * F : ℕ) : ℤ) := by
      push_cast
      exact ⟨_, hkey.symm⟩
    exact Int.natCast_dvd_natCast.mp hz
  have hdef : twoStack (m + 1) = 2 * F / D := by
    simp only [twoStack, hD, hF]
    congr 2
  have hmul : twoStack (m + 1) * D = 2 * F := by
    rw [hdef]; exact Nat.div_mul_cancel hdvd
  have hmulz : (twoStack (m + 1) : ℤ) * (D : ℤ) = 2 * (F : ℤ) := by
    exact_mod_cast hmul
  have hDz : (D : ℤ) ≠ 0 := by exact_mod_cast hDpos.ne'
  apply mul_right_cancel₀ hDz
  rw [hmulz, ← hkey]
  ring

/-- For `n = m + 1`, `a(n)` has the parity of `C(3n, n+1)`. -/
theorem odd_twoStack_succ_iff (m : ℕ) :
    Odd (twoStack (m + 1)) ↔ Odd (Nat.choose (3 * m + 3) (m + 2)) := by
  have h := twoStack_succ_eq m
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-! ## The conjecture -/

/-- The A000139 quotient is odd iff `n` is odd with `n AND 2n = 0`.
The equivalent A022341 form is `twoStack_odd_iff_A022341` (Bala). -/
theorem twoStack_odd_iff (n : ℕ) : Odd (twoStack n) ↔ Odd n ∧ n &&& (2 * n) = 0 := by
  rcases n with _ | m
  · have h0 : twoStack 0 = 2 := by decide
    rw [h0]
    simp
  · rw [odd_twoStack_succ_iff m, ← land_bridge m]
    have hc : Nat.choose (3 * m + 3) (m + 2) = Nat.choose ((m + 2) + (2 * m + 1)) (m + 2) := by
      congr 1; ring
    rw [hc, odd_choose_add_iff]

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

/-- **Bala's conjecture in the entry's own wording**: `a(n)` is odd iff `n` is a
term of A022341, i.e. `n = 4f + 1` with `f` a Fibbinary number (`f AND 2f = 0`). -/
theorem twoStack_odd_iff_A022341 (n : ℕ) :
    Odd (twoStack n) ↔ ∃ f : ℕ, f &&& (2 * f) = 0 ∧ n = 4 * f + 1 := by
  rw [twoStack_odd_iff, odd_and_land_iff]

/-! ## Examples -/

-- Satisfiability of both sides: `n = 1` (in A022341, `a(1) = 1` odd) and
-- `n = 3` (odd but `3 AND 6 = 2`, `a(3) = 6` even).
example : Odd (twoStack 1) ∧ Odd 1 ∧ 1 &&& (2 * 1) = 0 := by decide
example : ¬ Odd (twoStack 3) ∧ 3 &&& (2 * 3) ≠ 0 := by decide

end Candidates.A000139TwoStackParity
