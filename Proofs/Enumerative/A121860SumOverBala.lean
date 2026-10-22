/-
# A121860: eventual residue 2

OEIS A121860, Peter Bala (Aug 08 2025).
For the divisor sum `a(n) = Σ_{d∣n} n!/(d!(n/d)!)`,
`((n-4)/2)!` divides `a(n)-2` in `ℤ` whenever `n ≥ 4`.
Consequently, for every positive `k`, `a(n) ≡ 2 (mod k)` for `n ≥ 2k+4`.
The divisors `1` and `n` contribute `1` each; the other terms have the
required factorial divisibility.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A121860SumOverBala

open Nat

/-- OEIS A121860: `a(n) = Σ_{d ∣ n} n! / (d! * (n/d)!)`.  The division is exact
(each summand is a multinomial-type coefficient). -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, n ! / (d ! * (n / d) !)

example : a 1 = 1 := by decide
example : a 2 = 2 := by decide
example : a 3 = 2 := by decide
example : a 4 = 8 := by decide
example : a 5 = 2 := by decide
example : a 6 = 122 := by decide
example : a 8 = 1682 := by decide
example : a 9 = 10082 := by decide
example : a 10 = 30242 := by decide

/-- For `2 ≤ d, e`, `2 * (d + e) ≤ d * e + 4`, i.e. `(d - 2) * (e - 2) ≥ 0`. -/
lemma two_mul_add_le (d e : ℕ) (hd : 2 ≤ d) (he : 2 ≤ e) :
    2 * (d + e) ≤ d * e + 4 := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le he
  ring_nf
  omega

/-- A nontrivial summand is divisible by `((n - 4)/2)!`: if `n = d * e` with
`2 ≤ d, e`, then `((d * e - 4)/2)! ∣ (d * e)! / (d! * e!)`. -/
lemma factorial_dvd_term (d e : ℕ) (hd : 2 ≤ d) (he : 2 ≤ e) :
    ((d * e - 4) / 2)! ∣ (d * e)! / (d ! * e !) := by
  have hle := two_mul_add_le d e hd he
  set r := d * e - d - e with hr
  have hsum : d + e + r = d * e := by omega
  have h1 : d ! * e ! * r ! ∣ (d * e)! := by
    rw [← hsum]
    exact (Nat.mul_dvd_mul_right (Nat.factorial_mul_factorial_dvd_factorial_add d e) _).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add (d + e) r)
  obtain ⟨c, hc⟩ := h1
  have hpos : 0 < d ! * e ! := Nat.mul_pos (Nat.factorial_pos d) (Nat.factorial_pos e)
  have hq : (d * e)! / (d ! * e !) = r ! * c := by
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hpos]
  rw [hq]
  exact (Nat.factorial_dvd_factorial (by omega)).mul_right c

/-- The trivial divisors `1` and `n` each contribute `1`, so for `2 ≤ n`,
`a n = 2 + Σ_{d ∣ n, d ≠ 1, d ≠ n} n!/(d! (n/d)!)`. -/
lemma a_eq_two_add (n : ℕ) (hn : 2 ≤ n) :
    a n = 2 + ∑ d ∈ (n.divisors.erase 1).erase n, n ! / (d ! * (n / d) !) := by
  have hn0 : n ≠ 0 := by omega
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have hnmem : n ∈ n.divisors.erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors_self n hn0⟩
  have hf1 : n ! / (1 ! * (n / 1) !) = 1 := by
    rw [Nat.div_one, Nat.factorial_one, one_mul, Nat.div_self (Nat.factorial_pos n)]
  have hfn : n ! / (n ! * (n / n) !) = 1 := by
    rw [Nat.div_self (by omega), Nat.factorial_one, mul_one,
      Nat.div_self (Nat.factorial_pos n)]
  unfold a
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ hnmem, hf1, hfn]
  ring

/-- **Strong form.** For every `n ≥ 4`, `((n - 4)/2)!` divides `a(n) - 2`. -/
theorem factorial_dvd_a_sub_two (n : ℕ) (hn : 4 ≤ n) :
    (((n - 4) / 2)! : ℤ) ∣ (a n : ℤ) - 2 := by
  rw [a_eq_two_add n (by omega)]
  push_cast
  rw [add_sub_cancel_left]
  refine Finset.dvd_sum fun d hd => ?_
  obtain ⟨hdn, hd1, hdvd⟩ : d ≠ n ∧ d ≠ 1 ∧ d ∈ n.divisors := by
    simp only [Finset.mem_erase] at hd
    exact ⟨hd.1, hd.2.1, hd.2.2⟩
  have hn0 : n ≠ 0 := by omega
  have hdiv : d ∣ n := Nat.dvd_of_mem_divisors hdvd
  obtain ⟨e, he⟩ := hdiv
  have hd0 : d ≠ 0 := by rintro rfl; omega
  have he0 : e ≠ 0 := by rintro rfl; omega
  have hd2 : 2 ≤ d := by omega
  have he1 : e ≠ 1 := by rintro rfl; omega
  have he2 : 2 ≤ e := by omega
  have hq : n / d = e := by rw [he, Nat.mul_div_cancel_left _ (by omega)]
  rw [hq, he]
  exact_mod_cast factorial_dvd_term d e hd2 he2

/-- **Bala's conjecture, explicit form.** For every `k ≥ 1` and every
`n ≥ 2k + 4`, `a(n) ≡ 2 (mod k)`. -/
theorem a_modEq_two_of_le (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : 2 * k + 4 ≤ n) :
    a n ≡ 2 [MOD k] := by
  have hkf : (k : ℤ) ∣ (((n - 4) / 2)! : ℤ) := by
    exact_mod_cast Nat.dvd_factorial hk (by omega)
  exact (Nat.modEq_iff_dvd.mpr (hkf.trans (factorial_dvd_a_sub_two n (by omega)))).symm

/-- **Bala's conjecture (A121860, Peter Bala, Aug 08 2025).** Verbatim:
"the sequence a(n) taken modulo a positive integer k >= 3 eventually becomes
constant equal to 2."  For every `k ≥ 3` there is `N` such that
`a(n) ≡ 2 (mod k)` for all `n ≥ N` (one may take `N = 2k + 4`). -/
theorem bala_conjecture (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n ≡ 2 [MOD k] :=
  ⟨2 * k + 4, fun n hn => a_modEq_two_of_le k (by omega) n hn⟩

/-- Non-vacuity of the residue: for `k ≥ 3` the constant `2` is a genuine residue,
and the sequence is not identically `2 (mod k)` from the start
(`a 4 = 8 ≢ 2 (mod 5)`). -/
example : ¬ a 4 ≡ 2 [MOD 5] := by decide

end Candidates.A121860SumOverBala
