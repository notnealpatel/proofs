/-
# A188648 — Yanev: the binomial square sum is a terminating 4F3

## OEIS source (retrieved with `oeis show A188648`, 2026-10-21)

```
NAME:     Binomial sums a(n) = Sum_{k=0..n} (binomial(2n-k,k))^2.
TERMS:    1,2,11,63,376,2317,14545,92512,594169,3844787,25027296,163701327,...
FORMULA (the conjecture):
  Conjecture: a(n) = hypergeom([-n,-n,n+1,n+1], [1/2,1/2,1], 1/16).
  - _Velin Yanev_, Oct 31 2019
```

## Status

Triage status: open (no proof recorded in the entry or found in the
literature).  The identity is elementary: the `k`-th hypergeometric term
equals `C(n+k,2k)^2`, and reflecting `k ↦ n-k` in the defining sum gives
`Σ C(n+k,2k)^2`.  Computationally re-checked (exact rationals) for
`0 ≤ n < 80`.

## Definitional choices

* `hypergeom([a₁..a₄],[b₁..b₃],z) = Σ_{k ≥ 0} (a₁)_k⋯(a₄)_k / ((b₁)_k⋯(b₃)_k) · z^k / k!`
  with `(x)_k` the rising factorial, Mathlib's `(ascPochhammer ℚ k).eval x`.
  The series is stated as a genuine `tsum` over `ℚ`; it terminates because
  `(-n)_k = 0` for `k > n` (`term_eq_zero_of_lt`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A188648SumYanev

open Finset Polynomial

/-- OEIS A188648: `a(n) = Σ_{k=0..n} C(2n-k,k)^2`.  (`2 * n - k` never
truncates since `k ≤ n`.) -/
def a (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (Nat.choose (2 * n - k) k) ^ 2

example : a 0 = 1 := by decide
example : a 1 = 2 := by decide
example : a 2 = 11 := by decide
example : a 3 = 63 := by decide
example : a 4 = 376 := by decide
example : a 5 = 2317 := by decide

/-- The rising factorial (Pochhammer symbol) `(x)_k = x (x+1) ⋯ (x+k-1)` over `ℚ`. -/
noncomputable def rising (x : ℚ) (k : ℕ) : ℚ := (ascPochhammer ℚ k).eval x

example : rising (1 / 2) 2 = 3 / 4 := by
  norm_num [rising, ascPochhammer_succ_eval]

/-- The `k`-th term of `₄F₃([-n,-n,n+1,n+1],[1/2,1/2,1]; 1/16)`. -/
noncomputable def term (n k : ℕ) : ℚ :=
  rising (-n) k * rising (-n) k * rising (n + 1) k * rising (n + 1) k /
    (rising (1 / 2) k * rising (1 / 2) k * rising 1 k) * (1 / 16) ^ k / (k.factorial : ℚ)

/-- The hypergeometric value `₄F₃([-n,-n,n+1,n+1],[1/2,1/2,1]; 1/16)` as a series. -/
noncomputable def hyp (n : ℕ) : ℚ := ∑' k : ℕ, term n k

/-- `(-n)_k = (-1)^k n (n-1) ⋯ (n-k+1)`. -/
theorem rising_neg_natCast (n k : ℕ) :
    rising (-(n : ℚ)) k = (-1) ^ k * (n.descFactorial k : ℚ) := by
  rw [rising, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

/-- `(n+1)_k = (n+1)(n+2)⋯(n+k)`. -/
theorem rising_natCast_add_one (n k : ℕ) :
    rising ((n : ℚ) + 1) k = ((n + 1).ascFactorial k : ℚ) := by
  have hcast : (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; rfl
  rw [rising, hcast, ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial]

/-- `(1)_k = k!`. -/
theorem rising_one (k : ℕ) : rising 1 k = (k.factorial : ℚ) := ascPochhammer_eval_one ℚ k

/-- `(1/2)_k · 4^k · k! = (2k)!`. -/
theorem rising_half_mul (k : ℕ) :
    rising (1 / 2) k * 4 ^ k * (k.factorial : ℚ) = ((2 * k).factorial : ℚ) := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [rising, ascPochhammer_succ_eval, ← rising]
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [h2, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [← ih]
    ring

/-- Termination: the `k`-th term vanishes for `n < k`. -/
theorem term_eq_zero_of_lt {n k : ℕ} (h : n < k) : term n k = 0 := by
  rw [term, rising_neg_natCast, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

/-- For `k ≤ n` the `k`-th term equals `C(n+k,2k)^2`. -/
theorem term_eq_choose_sq {n k : ℕ} (h : k ≤ n) :
    term n k = ((Nat.choose (n + k) (2 * k) : ℕ) : ℚ) ^ 2 := by
  have hr := rising_half_mul k
  have hD : ((n - k).factorial : ℚ) * (n.descFactorial k : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial h
  have hA : (n.factorial : ℚ) * ((n + 1).ascFactorial k : ℚ) = ((n + k).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n k
  have hc : ((n + k).choose (2 * k) : ℚ) * ((2 * k).factorial : ℚ) * ((n - k).factorial : ℚ)
      = ((n + k).factorial : ℚ) := by
    have hsub : n + k - 2 * k = n - k := by omega
    have := Nat.choose_mul_factorial_mul_factorial (n := n + k) (k := 2 * k) (by omega)
    rw [hsub] at this
    exact_mod_cast this
  have hk0 : (k.factorial : ℚ) ≠ 0 := by positivity
  have hnk0 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  have hn0 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2k0 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
  have hr' : rising (1 / 2) k = ((2 * k).factorial : ℚ) / (4 ^ k * (k.factorial : ℚ)) := by
    rw [← hr]; field_simp
  have hD' : (n.descFactorial k : ℚ) = (n.factorial : ℚ) / ((n - k).factorial : ℚ) := by
    rw [← hD]; field_simp
  have hA' : ((n + 1).ascFactorial k : ℚ) = ((n + k).factorial : ℚ) / (n.factorial : ℚ) := by
    rw [← hA]; field_simp
  have hc' : ((n + k).choose (2 * k) : ℚ)
      = ((n + k).factorial : ℚ) / (((2 * k).factorial : ℚ) * ((n - k).factorial : ℚ)) := by
    rw [← hc]; field_simp
  rw [term, rising_neg_natCast, rising_natCast_add_one, rising_one, hr', hD', hA', hc']
  field_simp
  rw [← pow_mul, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
  norm_num

/-- The series `hyp n` reduces to the finite sum `Σ_{k=0..n} C(n+k,2k)^2`. -/
theorem hyp_eq_sum (n : ℕ) :
    hyp n = ∑ k ∈ range (n + 1), ((Nat.choose (n + k) (2 * k) : ℕ) : ℚ) ^ 2 := by
  rw [hyp, tsum_eq_sum (s := range (n + 1))]
  · refine sum_congr rfl fun k hk => term_eq_choose_sq (Nat.lt_succ_iff.mp (mem_range.mp hk))
  · intro k hk
    exact term_eq_zero_of_lt (by simpa [mem_range, Nat.lt_succ_iff] using hk)

/-- Reflection `k ↦ n - k`: `a(n) = Σ_{k=0..n} C(n+k,2k)^2`. -/
theorem a_eq_sum_choose (n : ℕ) :
    a n = ∑ k ∈ range (n + 1), (Nat.choose (n + k) (2 * k)) ^ 2 := by
  rw [a, ← sum_range_reflect (fun k => (n + k).choose (2 * k) ^ 2)]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have e1 : n + (n + 1 - 1 - k) = 2 * n - k := by omega
  have e2 : 2 * (n + 1 - 1 - k) = 2 * n - k - k := by omega
  simp only [e1, e2]
  rw [Nat.choose_symm (by omega)]

/-- **Yanev's conjecture (A188648, Velin Yanev, Oct 31 2019).**
`Σ_{k=0..n} C(2n-k,k)^2 = ₄F₃([-n,-n,n+1,n+1],[1/2,1/2,1]; 1/16)` for all `n ≥ 0`. -/
theorem a_eq_hyp (n : ℕ) : (a n : ℚ) = hyp n := by
  rw [hyp_eq_sum, a_eq_sum_choose]
  push_cast
  rfl

end Candidates.A188648SumYanev
