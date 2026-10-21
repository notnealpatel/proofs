/-
# A002457 — Shunia: `a(n) = floor(sqrt((16^n + 1)^(2n+1))) mod 16^n`

## OEIS source (`oeis show A002457`, retrieved 2026-10-21)

```
NAME:     a(n) = (2n+1)!/n!^2.
TERMS:    1,6,30,140,630,2772,12012,51480,218790,923780,3879876,16224936,...
FORMULA (the conjecture, verbatim):
  Conjecture: a(n) = floor(sqrt((16^n + 1)^(2*n+1))) mod 16^n, for n > 0.
  - _Joseph M. Shunia_, Sep 11 2025
```

## Status

Triage literature status: open (no proof in the entry or the literature as far
as the triage could tell).  Verified numerically for `1 ≤ n ≤ 120` (Python
`math.isqrt`, 2026-10-21).  This module proves it for all `n > 0`.

## Proof

Put `X = 4^n`, `t = 1/X^2 = 16^(-n)`, and let `P_n(t) = ∑_{j ≤ n} C(n+1/2, j) t^j`
be the Taylor polynomial of `(1+t)^(n+1/2)`.  By induction on `n` with
`d/dt (1+t)^(n+3/2) = (n+3/2)(1+t)^(n+1/2)` one gets, for `t ≥ 0`,
`0 ≤ (1+t)^(n+1/2) - P_n(t) ≤ C(n+1/2, n+1) t^(n+1)` (`taylor_bound`).
Multiplying by `X^(2n+1)`: `G = sqrt((16^n+1)^(2n+1))` and
`N = X^(2n+1) P_n(t)` satisfy `N ≤ G ≤ N + C(n+1/2,n+1)/X < N + 1`.  Since
`4^j C(n+1/2, j)` is a natural number (`c_integral`), `N` is the natural number
`∑_{j ≤ n} 4^j C(n+1/2,j) (4·16^n)^(n-j)`, so `floor G = N`; every term with
`j < n` is divisible by `16^n`, and the `j = n` term is `4^n C(n+1/2,n) = a(n) < 16^n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A002457FloorSqrtMod

/-- OEIS A002457: `a(n) = (2n+1)!/n!^2`. -/
def a (n : ℕ) : ℕ := (2 * n + 1).factorial / n.factorial ^ 2

example : a 0 = 1 := rfl
example : a 1 = 6 := rfl
example : a 2 = 30 := rfl
example : a 3 = 140 := rfl
example : a 4 = 630 := rfl
example : a 5 = 2772 := rfl

/-- The generalized binomial coefficient `C(n + 1/2, j)` as a real number. -/
noncomputable def c (n j : ℕ) : ℝ :=
  (∏ i ∈ Finset.range j, ((n : ℝ) + 1 / 2 - i)) / j.factorial

/-- `C(n + 1/2, 0) = 1`. -/
theorem c_zero_right (n : ℕ) : c n 0 = 1 := by simp [c]

/-- Horizontal recursion `C(α, j+1) = C(α, j) (α - j) / (j+1)`. -/
theorem c_succ_right (n j : ℕ) :
    c n (j + 1) = c n j * ((n : ℝ) + 1 / 2 - j) / (j + 1) := by
  simp only [c, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have h1 : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  field_simp

/-- Derivative recursion `(j+1) C(α+1, j+1) = (α+1) C(α, j)`. -/
theorem c_succ_succ (n j : ℕ) :
    ((j : ℝ) + 1) * c (n + 1) (j + 1) = ((n : ℝ) + 3 / 2) * c n j := by
  simp only [c, Finset.prod_range_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_zero]
  have h1 : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  have hprod : ∏ i ∈ Finset.range j, (((n + 1 : ℕ) : ℝ) + 1 / 2 - ((i + 1 : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range j, ((n : ℝ) + 1 / 2 - i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast; ring
  push_cast at hprod ⊢
  rw [hprod]
  field_simp
  ring

/-- Pascal's rule `C(α+1, j+1) = C(α, j+1) + C(α, j)`. -/
theorem c_pascal (n j : ℕ) : c (n + 1) (j + 1) = c n (j + 1) + c n j := by
  have h1 := c_succ_succ n j
  have h2 := c_succ_right n j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [h2]
  field_simp
  linarith

/-- Closed form `a(n) = (2n+1) * C(2n, n)`. -/
theorem a_eq (n : ℕ) : a n = (2 * n + 1) * n.centralBinom := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have h2 : 2 * n - n = n := by omega
  rw [h2] at h
  unfold a
  rw [Nat.factorial_succ, ← h, Nat.centralBinom]
  have hpos : 0 < n.factorial ^ 2 := by positivity
  rw [show (2 * n + 1) * ((2 * n).choose n * n.factorial * n.factorial) =
      (2 * n + 1) * (2 * n).choose n * n.factorial ^ 2 by ring]
  exact Nat.mul_div_cancel _ hpos

/-- The diagonal coefficient: `4^n C(n + 1/2, n) = (2n+1) C(2n, n)`. -/
theorem c_diag (n : ℕ) : (4 : ℝ) ^ n * c n n = ((2 * n + 1) * n.centralBinom : ℕ) := by
  induction n with
  | zero => simp [c_zero_right]
  | succ n ih =>
    have h1 := c_succ_succ n n
    have h2 := Nat.succ_mul_centralBinom_succ n
    have h2' : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by exact_mod_cast h2
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast at ih ⊢
    apply mul_left_cancel₀ hn.ne'
    calc ((n : ℝ) + 1) * ((4 : ℝ) ^ (n + 1) * c (n + 1) (n + 1))
        = 4 * ((n : ℝ) + 3 / 2) * ((4 : ℝ) ^ n * c n n) := by rw [pow_succ]; linear_combination (4 : ℝ) ^ n * 4 * h1
      _ = ((n : ℝ) + 1) * ((2 * ((n : ℝ) + 1) + 1) * ((n + 1).centralBinom : ℝ)) := by
        rw [ih]; linear_combination (-(2 : ℝ) * (n : ℝ) - 3) * h2'

/-- The superdiagonal coefficient: `4^(n+1) C(n + 1/2, n+1) = C(2n+2, n+1)`. -/
theorem c_superdiag (n : ℕ) : (4 : ℝ) ^ (n + 1) * c n (n + 1) = ((n + 1).centralBinom : ℕ) := by
  induction n with
  | zero =>
    rw [c_succ_right, c_zero_right]
    norm_num [Nat.centralBinom, Nat.choose]
  | succ n ih =>
    have h1 := c_succ_succ n (n + 1)
    have h2 := Nat.succ_mul_centralBinom_succ (n + 1)
    have h2' : ((n : ℝ) + 2) * ((n + 2).centralBinom : ℝ) =
        2 * (2 * n + 3) * ((n + 1).centralBinom : ℝ) := by
      have h3 := congrArg (Nat.cast (R := ℝ)) h2
      push_cast at h3
      linear_combination h3
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    push_cast at ih h1 ⊢
    apply mul_left_cancel₀ hn.ne'
    calc ((n : ℝ) + 2) * ((4 : ℝ) ^ (n + 1 + 1) * c (n + 1) (n + 1 + 1))
        = 4 * ((n : ℝ) + 3 / 2) * ((4 : ℝ) ^ (n + 1) * c n (n + 1)) := by
          rw [pow_succ]; linear_combination (4 : ℝ) ^ (n + 1) * 4 * h1
      _ = ((n : ℝ) + 2) * ((n + 1 + 1).centralBinom : ℝ) := by
        rw [ih]; linear_combination (-1 : ℝ) * h2'

/-- The superdiagonal coefficient is at most one. -/
theorem c_superdiag_le_one (n : ℕ) : c n (n + 1) ≤ 1 := by
  have h := c_superdiag n
  have hle : ((n + 1).centralBinom : ℝ) ≤ (4 : ℝ) ^ (n + 1) := by
    exact_mod_cast Nat.centralBinom_le_four_pow (n + 1)
  have hpos : (0 : ℝ) < (4 : ℝ) ^ (n + 1) := by positivity
  by_contra hc
  rw [not_le] at hc
  have : (4 : ℝ) ^ (n + 1) < (4 : ℝ) ^ (n + 1) * c n (n + 1) := by
    nlinarith
  linarith

/-- Integrality: `4^j C(n + 1/2, j)` is a natural number for `j ≤ n + 1`. -/
theorem c_integral (n : ℕ) : ∀ j ≤ n + 1, ∃ b : ℕ, (4 : ℝ) ^ j * c n j = b := by
  induction n with
  | zero =>
    intro j hj
    interval_cases j
    · exact ⟨1, by simp [c_zero_right]⟩
    · exact ⟨2, by rw [c_succ_right, c_zero_right]; norm_num⟩
  | succ n ih =>
    intro j hj
    rcases j with _ | i
    · exact ⟨1, by simp [c_zero_right]⟩
    · rcases Nat.lt_or_ge (i + 1) (n + 2) with hi | hi
      · obtain ⟨b1, hb1⟩ := ih (i + 1) (by omega)
        obtain ⟨b2, hb2⟩ := ih i (by omega)
        refine ⟨b1 + 4 * b2, ?_⟩
        rw [c_pascal, pow_succ]
        push_cast
        rw [← hb1, ← hb2, pow_succ]
        ring
      · have hin : i = n + 1 := by omega
        subst hin
        exact ⟨_, c_superdiag (n + 1)⟩

/-! ## Taylor bound for `(1 + t)^(m + 1/2)` -/

/-- The function `(1 + t)^(m + 1/2)`, written as `(1 + t)^m * √(1 + t)`. -/
noncomputable def F (m : ℕ) (t : ℝ) : ℝ := (1 + t) ^ m * √(1 + t)

/-- The degree-`m` Taylor polynomial of `(1 + t)^(m + 1/2)` at `t = 0`. -/
noncomputable def P (m : ℕ) (t : ℝ) : ℝ := ∑ j ∈ Finset.range (m + 1), c m j * t ^ j

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t) (hf' : ∀ t, 0 < t → 0 ≤ f' t) :
    ∀ t, 0 ≤ t → 0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Ici 0) ?_ ?_ ?_
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (le_of_lt ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact hf' t ht
  intro t ht
  have := hmono (Set.mem_Ici.mpr le_rfl) ht ht
  rwa [h0] at this

/-- Derivative of `(1 + t)^(m+1+1/2)` is `(m + 3/2) (1 + t)^(m + 1/2)` for `t > -1`. -/
theorem hasDerivAt_F (m : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (F (m + 1)) (((m : ℝ) + 3 / 2) * F m t) t := by
  have hpos : 0 < 1 + t := by linarith
  have hs : 0 < √(1 + t) := Real.sqrt_pos.mpr hpos
  have hsq : √(1 + t) ^ 2 = 1 + t := Real.sq_sqrt hpos.le
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => (1 + x) ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * (1 + t) ^ m * 1) t :=
    h1.pow (m + 1)
  have h3 : HasDerivAt (fun x : ℝ => √(1 + x)) (1 / (2 * √(1 + t))) t := h1.sqrt hpos.ne'
  have h4 : HasDerivAt (F (m + 1)) (((m + 1 : ℕ) : ℝ) * (1 + t) ^ m * 1 * √(1 + t) +
      (1 + t) ^ (m + 1) * (1 / (2 * √(1 + t)))) t := h2.mul h3
  convert h4 using 1
  unfold F
  field_simp
  push_cast
  rw [hsq, pow_succ]
  ring

/-- Derivative of the Taylor polynomial: `P_{m+1}' = (m + 3/2) P_m`. -/
theorem hasDerivAt_P (m : ℕ) (t : ℝ) :
    HasDerivAt (P (m + 1)) (((m : ℝ) + 3 / 2) * P m t) t := by
  have h : ∀ j ∈ Finset.range (m + 1 + 1),
      HasDerivAt (fun x : ℝ => c (m + 1) j * x ^ j) (c (m + 1) j * ((j : ℝ) * t ^ (j - 1))) t :=
    fun j _ => (hasDerivAt_pow j t).const_mul _
  have hs : HasDerivAt (P (m + 1))
      (∑ j ∈ Finset.range (m + 1 + 1), c (m + 1) j * ((j : ℝ) * t ^ (j - 1))) t :=
    HasDerivAt.fun_sum h
  convert hs using 1
  rw [Finset.sum_range_succ', P, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc := c_succ_succ m j
  push_cast
  linear_combination (-(t ^ j)) * hc

/-- Taylor bound: for `t ≥ 0`,
`0 ≤ (1 + t)^(m + 1/2) - P_m(t) ≤ C(m + 1/2, m + 1) t^(m+1)`. -/
theorem taylor_bound (m : ℕ) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ F m t - P m t ∧ F m t - P m t ≤ c m (m + 1) * t ^ (m + 1) := by
  induction m with
  | zero =>
    intro t ht
    have hs0 : 0 ≤ √(1 + t) := Real.sqrt_nonneg _
    have hsq : √(1 + t) ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
    have hc : c 0 1 = 1 / 2 := by rw [c_succ_right, c_zero_right]; norm_num
    simp only [F, P, pow_zero, one_mul, zero_add, Finset.sum_range_one, c_zero_right, hc,
      pow_one]
    constructor
    · nlinarith
    · nlinarith
  | succ m ih =>
    have hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun x => F (m + 1) x - P (m + 1) x)
        (((m : ℝ) + 3 / 2) * (F m t - P m t)) t := by
      intro t ht
      have h : HasDerivAt (fun x => F (m + 1) x - P (m + 1) x)
          (((m : ℝ) + 3 / 2) * F m t - ((m : ℝ) + 3 / 2) * P m t) t :=
        (hasDerivAt_F m (show -1 < t by linarith)).sub (hasDerivAt_P m t)
      exact h.congr_deriv (by ring)
    have hzero : F (m + 1) 0 - P (m + 1) 0 = 0 := by
      simp [F, P, Finset.sum_range_succ', c_zero_right]
    intro t ht
    constructor
    · refine nonneg_of_hasDerivAt (f := fun x => F (m + 1) x - P (m + 1) x) hzero hderiv
        ?_ t ht
      intro x hx
      have hm : (0 : ℝ) ≤ (m : ℝ) + 3 / 2 := by positivity
      exact mul_nonneg hm (ih x hx.le).1
    · have hcs := c_succ_succ m (m + 1)
      have hderiv2 : ∀ x : ℝ, 0 ≤ x → HasDerivAt
          (fun y => c (m + 1) (m + 1 + 1) * y ^ (m + 1 + 1) - (F (m + 1) y - P (m + 1) y))
          (((m : ℝ) + 3 / 2) * (c m (m + 1) * x ^ (m + 1) - (F m x - P m x))) x := by
        intro x hx
        have h : HasDerivAt
            (fun y => c (m + 1) (m + 1 + 1) * y ^ (m + 1 + 1) - (F (m + 1) y - P (m + 1) y))
            (c (m + 1) (m + 1 + 1) * (((m + 1 + 1 : ℕ) : ℝ) * x ^ (m + 1 + 1 - 1)) -
              ((m : ℝ) + 3 / 2) * (F m x - P m x)) x :=
          ((hasDerivAt_pow (m + 1 + 1) x).const_mul (c (m + 1) (m + 1 + 1))).sub (hderiv x hx)
        refine h.congr_deriv ?_
        push_cast at hcs ⊢
        linear_combination (x ^ (m + 1)) * hcs
      have hzero2 : c (m + 1) (m + 1 + 1) * (0 : ℝ) ^ (m + 1 + 1) -
          (F (m + 1) 0 - P (m + 1) 0) = 0 := by
        rw [hzero]; simp
      have key := nonneg_of_hasDerivAt
        (f := fun y => c (m + 1) (m + 1 + 1) * y ^ (m + 1 + 1) - (F (m + 1) y - P (m + 1) y))
        hzero2 hderiv2 (fun x hx => mul_nonneg (by positivity) (sub_nonneg.mpr (ih x hx.le).2))
        t ht
      linarith

/-! ## Assembly -/

/-- `16^n = (4^n)^2` over the reals. -/
theorem sixteen_pow_eq (n : ℕ) : (16 : ℝ) ^ n = ((4 : ℝ) ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- The scaled Taylor polynomial `4^(n(2n+1)) P_n(16^(-n))` is the natural number
`∑_{j ≤ n} B_j (4 · 16^n)^(n-j)`, where `B_j = 4^j C(n + 1/2, j)`. -/
theorem scaled_P_eq (n : ℕ) (B : ℕ → ℕ) (hB : ∀ j ≤ n, (4 : ℝ) ^ j * c n j = B j) :
    ((4 : ℝ) ^ n) ^ (2 * n + 1) * P n (1 / (16 : ℝ) ^ n) =
      ((∑ j ∈ Finset.range (n + 1), B j * (4 * 16 ^ n) ^ (n - j) : ℕ) : ℝ) := by
  rw [P, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
  rw [← hB j hjn, sixteen_pow_eq, Nat.add_sub_cancel_left]
  set X : ℝ := (4 : ℝ) ^ (j + k) with hXdef
  have hX0 : X ≠ 0 := by positivity
  have e1 : X ^ (2 * (j + k) + 1) * (1 / X ^ 2) ^ j = X * (X ^ 2) ^ k := by
    rw [show X ^ (2 * (j + k) + 1) = X * (X ^ 2) ^ k * (X ^ 2) ^ j by ring, mul_assoc,
      ← mul_pow, mul_one_div_cancel (pow_ne_zero 2 hX0), one_pow, mul_one]
  have e2 : X = (4 : ℝ) ^ j * (4 : ℝ) ^ k := by rw [hXdef, pow_add]
  linear_combination c (j + k) j * e1 + c (j + k) j * (X ^ 2) ^ k * e2

/-- `2n + 1 < 4^n` for `n ≥ 1`. -/
theorem two_mul_add_one_lt_four_pow {n : ℕ} (hn : 0 < n) : 2 * n + 1 < 4 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have := ih h
      rw [pow_succ]
      omega

/-- `a(n) < 16^n` for `n ≥ 1`. -/
theorem a_lt_sixteen_pow {n : ℕ} (hn : 0 < n) : a n < 16 ^ n := by
  rw [a_eq]
  have h1 := two_mul_add_one_lt_four_pow hn
  have h2 := Nat.centralBinom_le_four_pow n
  have h3 : (16 : ℕ) ^ n = 4 ^ n * 4 ^ n := by
    rw [← mul_pow]; norm_num
  rw [h3]
  calc (2 * n + 1) * n.centralBinom ≤ (2 * n + 1) * 4 ^ n := Nat.mul_le_mul_left _ h2
    _ < 4 ^ n * 4 ^ n := Nat.mul_lt_mul_of_pos_right h1 (by positivity)

/-- **Shunia's conjecture (A002457, Sep 11 2025).** For `n > 0`,
`a(n) = floor(sqrt((16^n + 1)^(2n+1))) mod 16^n`, where `a(n) = (2n+1)!/n!^2`. -/
theorem floor_sqrt_mod (n : ℕ) (hn : 0 < n) :
    Nat.sqrt ((16 ^ n + 1) ^ (2 * n + 1)) % 16 ^ n = a n := by
  -- integer coefficients `B j = 4^j C(n + 1/2, j)`
  have hBex : ∀ j, ∃ b : ℕ, j ≤ n → (4 : ℝ) ^ j * c n j = b := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨b, hb⟩ := c_integral n j (by omega)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose B hB using hBex
  set N : ℕ := ∑ j ∈ Finset.range (n + 1), B j * (4 * 16 ^ n) ^ (n - j) with hN
  have hNreal := scaled_P_eq n B (fun j hj => hB j hj)
  set M : ℕ := (16 ^ n + 1) ^ (2 * n + 1) with hM
  set X : ℝ := (4 : ℝ) ^ n with hXdef
  have hX4 : (4 : ℝ) ≤ X := by
    rw [hXdef]
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hX0 : 0 < X := by linarith
  have hXne : X ≠ 0 := hX0.ne'
  set t : ℝ := 1 / (16 : ℝ) ^ n with htdef
  have ht' : t = 1 / X ^ 2 := by rw [htdef, sixteen_pow_eq]
  have ht : 0 ≤ t := by rw [ht']; positivity
  have htX : t * X ^ 2 = 1 := by rw [ht']; exact one_div_mul_cancel (pow_ne_zero 2 hXne)
  obtain ⟨hlo, hhi⟩ := taylor_bound n t ht
  set G : ℝ := X ^ (2 * n + 1) * F n t with hGdef
  -- `G = sqrt M`
  have hG2 : G ^ 2 = (M : ℝ) := by
    have hsq : √(1 + t) ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
    rw [hGdef, F, mul_pow, mul_pow, hsq, hM]
    push_cast
    rw [sixteen_pow_eq, ← hXdef]
    have e : (X ^ (2 * n + 1)) ^ 2 * (((1 + t) ^ n) ^ 2 * (1 + t)) =
        (X ^ 2 * (1 + t)) ^ (2 * n + 1) := by rw [mul_pow]; ring
    rw [e, mul_add, mul_one, mul_comm (X ^ 2) t, htX, add_comm]
  have hXpow : 0 < X ^ (2 * n + 1) := by positivity
  -- lower bound `N ≤ G`
  have hNG : (N : ℝ) ≤ G := by
    rw [← hNreal, hGdef]
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hlo) hXpow.le
  -- upper bound `G < N + 1`
  have hGN : G < (N : ℝ) + 1 := by
    have hscale : X ^ (2 * n + 1) * t ^ (n + 1) = 1 / X := by
      rw [eq_div_iff hXne]
      calc X ^ (2 * n + 1) * t ^ (n + 1) * X = (t * X ^ 2) ^ (n + 1) := by ring
        _ = 1 := by rw [htX, one_pow]
    have h1 := mul_le_mul_of_nonneg_left hhi hXpow.le
    have hcle := c_superdiag_le_one n
    have h2 : X ^ (2 * n + 1) * (c n (n + 1) * t ^ (n + 1)) ≤ 1 / X := by
      rw [mul_left_comm, hscale]
      have : 0 ≤ 1 / X := by positivity
      nlinarith
    have h3 : 1 / X < 1 := by rw [div_lt_one hX0]; linarith
    rw [← hNreal, hGdef]
    nlinarith
  have hG0 : 0 ≤ G := le_trans (Nat.cast_nonneg N) hNG
  -- `Nat.sqrt M = N`
  have hsqrt : N = Nat.sqrt M := by
    rw [Nat.eq_sqrt']
    constructor
    · have h : ((N ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) := by
        rw [← hG2]; push_cast; exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNG 2
      exact_mod_cast h
    · have h : (M : ℝ) < (((N + 1) ^ 2 : ℕ) : ℝ) := by
        rw [← hG2]; push_cast; exact pow_lt_pow_left₀ hGN hG0 (by norm_num)
      exact_mod_cast h
  rw [← hsqrt]
  -- reduce modulo `16^n`
  have hBn : B n = a n := by
    have h1 := hB n le_rfl
    rw [c_diag, ← a_eq] at h1
    exact_mod_cast h1.symm
  rw [hN, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, hBn]
  have hdvd : 16 ^ n ∣ ∑ j ∈ Finset.range n, B j * (4 * 16 ^ n) ^ (n - j) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hjn : j < n := Finset.mem_range.mp hj
    exact Dvd.dvd.mul_left (dvd_pow (dvd_mul_left _ _) (by omega)) _
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt (a_lt_sixteen_pow hn)]

/-! ## Sanity layer -/

-- The statement at `n = 1`: `Nat.sqrt (17^3) = 70` and `70 % 16 = 6 = a 1`.
example : Nat.sqrt ((16 ^ 1 + 1) ^ (2 * 1 + 1)) = 70 :=
  (Nat.eq_sqrt'.mpr ⟨by norm_num, by norm_num⟩).symm

example : Nat.sqrt ((16 ^ 1 + 1) ^ (2 * 1 + 1)) % 16 ^ 1 = a 1 := floor_sqrt_mod 1 (by norm_num)

-- The guard `0 < n` is load-bearing: at `n = 0` the left side is `1 % 1 = 0 ≠ 1 = a 0`.
example : Nat.sqrt ((16 ^ 0 + 1) ^ (2 * 0 + 1)) % 16 ^ 0 ≠ a 0 := by
  rw [pow_zero, Nat.mod_one]; decide

-- Ground truth for the coefficients: `C(3/2, 1) = 3/2`, `C(3/2, 2) = 3/8`.
example : c 1 1 = 3 / 2 := by rw [c_succ_right, c_zero_right]; norm_num
example : c 1 2 = 3 / 8 := by rw [c_succ_right, c_succ_right, c_zero_right]; norm_num

end Candidates.A002457FloorSqrtMod
