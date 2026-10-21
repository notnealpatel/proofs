/-
# A068779 — Dale: least `k` with `⌊k / rev k⌋ = n` is a multiple of 10 for `n ≥ 5`

## OEIS source (retrieved with `oeis show A068779`, 2026-10-21)

```
NAME:     Least number k such that floor( k / digit reversal of k ) = n.
TERMS:    1,31,51,71,120,350,230,450,890,10,650,430,320,850,530,950,210,2110,
          730,520,830,1800,310,3310,4910,720,3110,4610,410,4410,920,4310,4210,
          510,5510,4110,2700,610,5310,7910,710,29600,6410,5110,810,6310,910
COMMENT (the conjecture):
  Conjecture: every term after a(4) is a multiple of 10.
  - _Harvey P. Dale_, May 28 2015
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  The argument is elementary: if `k` does not end in `0` then
`k` and `rev k` have the same number of decimal digits, so `k / rev k < 10`;
hence for `n ≥ 10` the least `k` ends in `0`.  The five cases `n = 5, …, 9`
are a finite check (`a(5..9) = 120, 350, 230, 450, 890`).

Computation (Python, 2026-10-21): all `a(n)`, `n ≤ 200`, were found among
`k < 3·10^6`; every `a(n)` with `5 ≤ n ≤ 200` is a multiple of 10, and the
first 47 values agree with the listed terms.

## Definition fidelity

"Digit reversal of `k`" is `Nat.ofDigits 10 (Nat.digits 10 k).reverse`
(leading zeros of the reversal dropped, so `rev 120 = 21`, as in the entry's
Mathematica program `FromDigits[Reverse[IntegerDigits[k]]]`).  For `k ≥ 1`
we have `rev k ≥ 1`, so `k / rev k` (natural-number division) is exactly
`floor(k / rev k)`.  The index set is the positive integers, as in the entry.
-/
import Mathlib

set_option autoImplicit false
-- Sequential elaboration: under the agent memory cap (`ulimit -v`) the
-- asynchronous elaborator fails to create worker threads for this file.
set_option Elab.async false

namespace Candidates.A068779LeastFloorRev

/-- Decimal digit reversal: `rev k` reads the base-10 digits of `k` backwards
(leading zeros of the result dropped). -/
def rev (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

example : rev 123 = 321 := by decide
example : rev 120 = 21 := by decide +kernel
example : rev 0 = 0 := by decide

/-- The set of positive `k` with `floor(k / rev k) = n`; A068779(n) is its
least element. -/
def floorRevSet (n : ℕ) : Set ℕ := {k | 0 < k ∧ k / rev k = n}

/-- Fuel-bounded digit reversal with accumulator, used only to make the finite
checks below cheap for the kernel; `rev_eq_revAux` identifies it with `rev`. -/
def revAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, k, acc => if k = 0 then acc else revAux fuel (k / 10) (acc * 10 + k % 10)

/-- With enough fuel, `revAux` appends the reversal of `k` to the accumulator:
`revAux fuel k acc = acc * 10 ^ (number of digits of k) + rev k`. -/
theorem revAux_eq (fuel : ℕ) : ∀ k acc : ℕ, k ≤ fuel →
    revAux fuel k acc = acc * 10 ^ (Nat.digits 10 k).length + rev k := by
  induction fuel with
  | zero =>
    intro k acc hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    simp [revAux, rev]
  | succ fuel ih =>
    intro k acc hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp [revAux, rev]
    · have hkf : k / 10 ≤ fuel := by omega
      have hcons : Nat.digits 10 k = k % 10 :: Nat.digits 10 (k / 10) :=
        Nat.digits_def' (by norm_num) hk0
      have hrev : rev k = rev (k / 10) + 10 ^ (Nat.digits 10 (k / 10)).length * (k % 10) := by
        simp only [rev, hcons, List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits_singleton,
          List.length_reverse]
      rw [revAux, if_neg hk0.ne', ih (k / 10) _ hkf, hrev, hcons, List.length_cons, pow_succ]
      ring

/-- `rev k` is computed by `revAux k k 0`. -/
theorem rev_eq_revAux (k : ℕ) : rev k = revAux k k 0 := by
  rw [revAux_eq k k 0 le_rfl, zero_mul, zero_add]

/-! Ground truth: the listed terms `a(1..10) = 1, 31, 51, 71, 120, 350, 230,
450, 890, 10` are least elements of the corresponding sets. -/

/-- Membership plus minimality, reduced to a decidable check on `revAux`. -/
theorem isLeast_floorRevSet_of_check (n a : ℕ)
    (ha : 0 < a ∧ a / revAux a a 0 = n) (hmin : ∀ j < a, 0 < j → j / revAux j j 0 ≠ n) :
    IsLeast (floorRevSet n) a := by
  refine ⟨⟨ha.1, by rw [rev_eq_revAux]; exact ha.2⟩, fun j hj => ?_⟩
  by_contra hlt
  have hj2 : j / revAux j j 0 = n := by rw [← rev_eq_revAux]; exact hj.2
  exact hmin j (Nat.lt_of_not_le hlt) hj.1 hj2

example : IsLeast (floorRevSet 1) 1 :=
  isLeast_floorRevSet_of_check 1 1 (by decide +kernel) (by decide +kernel)
example : IsLeast (floorRevSet 2) 31 :=
  isLeast_floorRevSet_of_check 2 31 (by decide +kernel) (by decide +kernel)
example : IsLeast (floorRevSet 4) 71 :=
  isLeast_floorRevSet_of_check 4 71 (by decide +kernel) (by decide +kernel)
example : IsLeast (floorRevSet 10) 10 :=
  isLeast_floorRevSet_of_check 10 10 (by decide +kernel) (by decide +kernel)

/-- **Least elements for `n = 5, …, 9`.** `a(5..9) = 120, 350, 230, 450, 890`. -/
theorem isLeast_floorRevSet_five : IsLeast (floorRevSet 5) 120 :=
  isLeast_floorRevSet_of_check 5 120 (by decide +kernel) (by decide +kernel)

/-- `a(6) = 350`. -/
theorem isLeast_floorRevSet_six : IsLeast (floorRevSet 6) 350 :=
  isLeast_floorRevSet_of_check 6 350 (by decide +kernel) (by decide +kernel)

/-- `a(7) = 230`. -/
theorem isLeast_floorRevSet_seven : IsLeast (floorRevSet 7) 230 :=
  isLeast_floorRevSet_of_check 7 230 (by decide +kernel) (by decide +kernel)

/-- `a(8) = 450`. -/
theorem isLeast_floorRevSet_eight : IsLeast (floorRevSet 8) 450 :=
  isLeast_floorRevSet_of_check 8 450 (by decide +kernel) (by decide +kernel)

/-- `a(9) = 890`. -/
theorem isLeast_floorRevSet_nine : IsLeast (floorRevSet 9) 890 :=
  isLeast_floorRevSet_of_check 9 890 (by decide +kernel) (by decide +kernel)

/-- **Digit-length bound.** If `k` does not end in `0` then `k / rev k < 10`:
`k < 10 ^ d` and, since the reversal keeps all `d` digits, `10 ^ d ≤ 10 * rev k`. -/
theorem div_rev_lt_ten_of_not_dvd (k : ℕ) (hk : ¬ 10 ∣ k) : k / rev k < 10 := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk (dvd_zero 10))
  set L := Nat.digits 10 k with hL
  have hcons : L = k % 10 :: Nat.digits 10 (k / 10) := Nat.digits_def' (by norm_num) hk0
  have hhead : k % 10 ≠ 0 := fun h => hk (Nat.dvd_of_mod_eq_zero h)
  have hdig : Nat.digits 10 (rev k) = L.reverse := by
    refine Nat.digits_ofDigits 10 (by norm_num) L.reverse ?_ ?_
    · intro l hl
      exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
    · intro hne
      rw [List.getLast_reverse]
      simpa [hcons] using hhead
  have hrev0 : rev k ≠ 0 := by
    intro h0
    have hnil : L.reverse = [] := by rw [← hdig, h0, Nat.digits_zero]
    rw [hcons] at hnil
    simp at hnil
  have hupper : k < 10 ^ L.length := Nat.lt_base_pow_length_digits (by norm_num)
  have hlower : 10 ^ L.length ≤ 10 * rev k := by
    have h := Nat.base_pow_length_digits_le 10 (rev k) (by norm_num) hrev0
    rwa [hdig, List.length_reverse] at h
  rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hrev0)]
  calc k < 10 ^ L.length := hupper
    _ ≤ 10 * rev k := hlower

/-- **Dale's conjecture (A068779, Harvey P. Dale, May 28 2015).**

Verbatim: "Conjecture: every term after a(4) is a multiple of 10."

Formal reading: for every `n ≥ 5`, if `k` is the least positive integer with
`floor(k / rev k) = n`, then `10 ∣ k`.  (Stated for any least element, so it
does not presuppose that every `n` is attained.) -/
theorem dvd_ten_of_isLeast (n k : ℕ) (hn : 5 ≤ n) (hk : IsLeast (floorRevSet n) k) :
    10 ∣ k := by
  by_cases h10 : 10 ≤ n
  · by_contra hnd
    have hlt := div_rev_lt_ten_of_not_dvd k hnd
    rw [hk.1.2] at hlt
    omega
  · have hcases : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · rw [hk.unique isLeast_floorRevSet_five]; norm_num
    · rw [hk.unique isLeast_floorRevSet_six]; norm_num
    · rw [hk.unique isLeast_floorRevSet_seven]; norm_num
    · rw [hk.unique isLeast_floorRevSet_eight]; norm_num
    · rw [hk.unique isLeast_floorRevSet_nine]; norm_num

/-- Non-vacuity: the hypothesis of `dvd_ten_of_isLeast` is satisfiable, e.g.
at `n = 11` with `k = 650 = a(11)`. -/
example : IsLeast (floorRevSet 11) 650 :=
  isLeast_floorRevSet_of_check 11 650 (by decide +kernel) (by decide +kernel)

end Candidates.A068779LeastFloorRev
