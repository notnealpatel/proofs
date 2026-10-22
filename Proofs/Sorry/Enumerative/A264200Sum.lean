/-
# A264200 — Kimberling: a quartic linear recurrence for the sums of the sets g(n)

## OEIS source (retrieved with `oeis show A264200` and the live entry, 2026-10-21)

```
NAME:     Numerator of sum of numbers in set g(n) generated as in Comments.
TERMS:    0,1,5,19,69,235,789,2603,8533,27819,90453,293547,951637,3082923,
          9983317,32320171,104617301,338602667,1095849301,3546458795,...
OFFSET:   0,3
KEYWORDS: nonn,easy
COMMENT:  Starting with g(0) = {0}, generate g(n) for n > 0 inductively using
          these rules:
          (1)  if x is in g(n-1), then x + 1 is in g(n); and
          (2)  if x is in g(n-1) and x < 2, then x/2 is in g(n).
          The sum of numbers in g(n) is a(n)/2^(n-1).
FORMULA (the conjecture):
          Conjecture: a(n) = 3*a(n-1) + 4*a(n-2) - 8*a(n-3) - 8*a(n-4).
AUTHOR:   _Clark Kimberling_, Nov 09 2015 (the conjecture line carries no
          separate signature; it falls under the entry's %A line).
MATHEMATICA:
          z = 30; x = 1/2; g[0] = {0}; g[1] = {1};
          g[n_] := g[n] = Union[1 + g[n - 1], (1/2) Select[g[n - 1], # < 2 &]]
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This file proves it (`a_rec`), sorry-free, together with the
identification of `a(n)` with the listed numerators (`num_sum_g_eq_a`).

## Definitional fidelity

* Rule (2) is applied to `x` with `0 < x < 2`, not `x < 2`: the entry's own
  program hard-codes `g[1] = {1}`, which is what the strict lower bound
  produces; with `x = 0` admitted, `g(1)` would be `{0, 1}` and `0` would
  persist, contradicting the listed terms.  Since `0 ∉ g(n)` for `n ≥ 1`, the
  lower bound only acts at the step `g(0) → g(1)`.
* `a(n)` is `2^(n-1) * ∑ g(n)` (integer exponent `(n : ℤ) - 1`, so `a 0 = 0`
  without a natural-subtraction convention), exactly as the triage records the
  conjecture and as the entry's comment "The sum of numbers in g(n) is
  a(n)/2^(n-1)" defines it.  The ground-truth examples check it against the
  listed numerators.

## Proof outline

The two images in the union are disjoint (`x + 1 ≥ 1 > y/2`) and both maps are
injective, so `∑_{g(n+1)} f = ∑_{x ∈ g(n)} (f (x+1) + [0<x<2] f (x/2))`.  For
`n ≥ 1` all elements are positive, and the six sums
`S = ∑ x`, `C = ∑ 1`, `D = ∑ [x<2]`, `T = ∑ [x<2] x`, `E = ∑ [x<1]`,
`U = ∑ [x<1] x` satisfy a linear step system.  Two invariants
`C = D + E` and `T + U = D` (true at `n = 1`, preserved by the step) cut the
eigenvalue `1` down to multiplicity one, whence
`2 S(n+4) - 3 S(n+3) - 2 S(n+2) + 2 S(n+1) + S(n) = 0` for `n ≥ 1`
(characteristic polynomial `(y - 1)(2y + 1)(y² - y - 1)`); scaling by
`2^(n-1)` gives the quartic; the case `n = 4` (which involves `a 0`) follows
from the step system started at `g 1 = {1}`.  Finally `a(n)` is shown to be an
odd integer for `n ≥ 1`, hence equal to the listed numerator of `∑ g(n)`.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Candidates.A264200Sum

/-! ## Definition layer -/

/-- The sets `g(n) ⊆ ℚ` of A264200: `g(0) = {0}` and
`g(n+1) = {x + 1 : x ∈ g(n)} ∪ {x / 2 : x ∈ g(n), 0 < x < 2}`. -/
def g : ℕ → Finset ℚ
  | 0 => {0}
  | n + 1 => (g n).image (· + 1) ∪ ((g n).filter (fun x => 0 < x ∧ x < 2)).image (· / 2)

/-- A264200 as the conjecture uses it: `a(n) = 2^(n-1) * ∑_{x ∈ g(n)} x`
(integer exponent, so `a 0 = 2⁻¹ * 0 = 0`). -/
def a (n : ℕ) : ℚ := (2 : ℚ) ^ ((n : ℤ) - 1) * ∑ x ∈ g n, x

/-! ### Ground truth -/

example : g 1 = {1} := by decide +kernel
example : g 2 = {2, 1 / 2} := by decide +kernel
example : g 3 = {3, 3 / 2, 1 / 4} := by decide +kernel
example : a 0 = 0 := by decide +kernel
example : a 1 = 1 := by decide +kernel
example : a 2 = 5 := by decide +kernel
example : a 3 = 19 := by decide +kernel
example : a 5 = 235 := by decide +kernel
example : a 6 = 789 := by decide +kernel

/-! ## Structure of the sets `g(n)` -/

/-- Unfolding equation for `g (n + 1)`. -/
theorem g_succ (n : ℕ) : g (n + 1) =
    (g n).image (· + 1) ∪ ((g n).filter (fun x => 0 < x ∧ x < 2)).image (· / 2) := rfl

/-- `g 1 = {1}`. -/
theorem g_one : g 1 = {1} := by
  simp [g, Finset.filter_singleton]

/-- Every element of every `g(n)` is nonnegative. -/
theorem nonneg_of_mem_g : ∀ (n : ℕ), ∀ x ∈ g n, 0 ≤ x
  | 0, x, hx => by
    rw [g, Finset.mem_singleton] at hx
    rw [hx]
  | n + 1, x, hx => by
    rw [g_succ, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · linarith [nonneg_of_mem_g n y hy]
    · rw [Finset.mem_filter] at hy
      linarith [hy.2.1]

/-- For `n ≥ 1`, every element of `g(n)` is positive. -/
theorem pos_of_mem_g_succ (n : ℕ) : ∀ x ∈ g (n + 1), 0 < x := by
  intro x hx
  rw [g_succ, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · linarith [nonneg_of_mem_g n y hy]
  · rw [Finset.mem_filter] at hy
    linarith [hy.2.1]

/-- Sums over `g(n+1)`: the union is disjoint (`x + 1 ≥ 1 > y / 2`) and both
maps are injective, so a sum over `g(n+1)` is a sum over `g(n)`. -/
theorem sum_g_succ (n : ℕ) (f : ℚ → ℚ) : ∑ x ∈ g (n + 1), f x =
    ∑ x ∈ g n, (f (x + 1) + if 0 < x ∧ x < 2 then f (x / 2) else 0) := by
  have hdisj : Disjoint ((g n).image (· + 1))
      (((g n).filter (fun x => 0 < x ∧ x < 2)).image (· / 2)) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [Finset.mem_image] at hz1 hz2
    obtain ⟨y, hy, rfl⟩ := hz1
    obtain ⟨w, hw, hwy⟩ := hz2
    rw [Finset.mem_filter] at hw
    linarith [nonneg_of_mem_g n y hy, hw.2.2]
  rw [g_succ, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => by simpa using h),
    Finset.sum_image (fun _ _ _ _ h => by simpa using h), Finset.sum_filter,
    Finset.sum_add_distrib]

/-! ## The six tracked sums and their step system -/

/-- Total sum `S(n) = ∑_{x ∈ g(n)} x`. -/
def S (n : ℕ) : ℚ := ∑ x ∈ g n, x
/-- Count `C(n) = |g(n)|`, as a rational sum. -/
def C (n : ℕ) : ℚ := ∑ _x ∈ g n, (1 : ℚ)
/-- Count of elements `x < 2` of `g(n)`. -/
def D (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 2 then (1 : ℚ) else 0
/-- Sum of the elements `x < 2` of `g(n)`. -/
def T (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 2 then x else 0
/-- Count of elements `x < 1` of `g(n)`. -/
def E (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 1 then (1 : ℚ) else 0
/-- Sum of the elements `x < 1` of `g(n)`. -/
def U (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 1 then x else 0

/-- Step for `S` (for `n ≥ 1`): `S(n+1) = S(n) + C(n) + T(n)/2`. -/
theorem S_step (m : ℕ) : 2 * S (m + 2) = 2 * S (m + 1) + 2 * C (m + 1) + T (m + 1) := by
  simp only [S, C, T]
  rw [sum_g_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `C` (for `n ≥ 1`): `C(n+1) = C(n) + D(n)`. -/
theorem C_step (m : ℕ) : C (m + 2) = C (m + 1) + D (m + 1) := by
  simp only [C, D]
  rw [sum_g_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `D` (for `n ≥ 1`): `D(n+1) = E(n) + D(n)`. -/
theorem D_step (m : ℕ) : D (m + 2) = E (m + 1) + D (m + 1) := by
  simp only [E, D]
  rw [sum_g_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `E` (for `n ≥ 1`): `E(n+1) = D(n)`. -/
theorem E_step (m : ℕ) : E (m + 2) = D (m + 1) := by
  simp only [E, D]
  rw [sum_g_succ]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `T` (for `n ≥ 1`): `T(n+1) = U(n) + E(n) + T(n)/2`. -/
theorem T_step (m : ℕ) : 2 * T (m + 2) = 2 * U (m + 1) + 2 * E (m + 1) + T (m + 1) := by
  simp only [T, U, E]
  rw [sum_g_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `U` (for `n ≥ 1`): `U(n+1) = T(n)/2`. -/
theorem U_step (m : ℕ) : 2 * U (m + 2) = T (m + 1) := by
  simp only [T, U]
  rw [sum_g_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- The two invariants, for `n ≥ 1`: `C(n) = D(n) + E(n)` and `T(n) + U(n) = D(n)`. -/
theorem invariants (m : ℕ) :
    C (m + 1) = D (m + 1) + E (m + 1) ∧ T (m + 1) + U (m + 1) = D (m + 1) := by
  induction m with
  | zero =>
    simp only [C, D, E, T, U, zero_add, g_one, Finset.sum_singleton]
    norm_num
  | succ k ih =>
    obtain ⟨hCDE, hTUD⟩ := ih
    have hC := C_step k
    have hD := D_step k
    have hE := E_step k
    have hT := T_step k
    have hU := U_step k
    constructor <;> linarith

/-- The recurrence for the plain sums, for `n ≥ 1`:
`2 S(n+4) - 3 S(n+3) - 2 S(n+2) + 2 S(n+1) + S(n) = 0`. -/
theorem S_rec (m : ℕ) :
    2 * S (m + 5) - 3 * S (m + 4) - 2 * S (m + 3) + 2 * S (m + 2) + S (m + 1) = 0 := by
  have i1 := invariants m
  have i2 := invariants (m + 1)
  have i3 := invariants (m + 2)
  have i4 := invariants (m + 3)
  have s1 := S_step m
  have s2 := S_step (m + 1)
  have s3 := S_step (m + 2)
  have s4 := S_step (m + 3)
  have c1 := C_step m
  have c2 := C_step (m + 1)
  have c3 := C_step (m + 2)
  have d1 := D_step m
  have d2 := D_step (m + 1)
  have d3 := D_step (m + 2)
  have e1 := E_step m
  have e2 := E_step (m + 1)
  have e3 := E_step (m + 2)
  have t1 := T_step m
  have t2 := T_step (m + 1)
  have t3 := T_step (m + 2)
  have u1 := U_step m
  have u2 := U_step (m + 1)
  have u3 := U_step (m + 2)
  linarith [i1.1, i1.2, i2.1, i2.2, i3.1, i3.2, i4.1, i4.2]

/-! ## The conjecture -/

/-- `a(k+1) = 2^k * S(k+1)`. -/
theorem a_succ (k : ℕ) : a (k + 1) = 2 ^ k * S (k + 1) := by
  simp only [a, S]
  congr 1
  rw [Nat.cast_succ, add_sub_cancel_right, zpow_natCast]

/-- The six tracked sums at `n = 1`, where `g 1 = {1}`. -/
theorem state_one : S 1 = 1 ∧ C 1 = 1 ∧ D 1 = 1 ∧ T 1 = 1 ∧ E 1 = 0 ∧ U 1 = 0 := by
  simp only [S, C, D, T, E, U, g_one, Finset.sum_singleton]
  norm_num

/-- `a 0 = 0`. -/
theorem a_zero : a 0 = 0 := by
  simp [a, g]

/-- `a 1 = 1`, `a 2 = 5`, `a 3 = 19`, `a 4 = 69`, derived from the step system. -/
theorem a_one_to_four : a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 19 ∧ a 4 = 69 := by
  obtain ⟨hS, hC, hD, hT, hE, hU⟩ := state_one
  have s1 := S_step 0
  have s2 := S_step 1
  have s3 := S_step 2
  have c1 := C_step 0
  have c2 := C_step 1
  have d1 := D_step 0
  have d2 := D_step 1
  have e1 := E_step 0
  have e2 := E_step 1
  have t1 := T_step 0
  have t2 := T_step 1
  have u1 := U_step 0
  have u2 := U_step 1
  norm_num only at s1 s2 s3 c1 c2 d1 d2 e1 e2 t1 t2 u1 u2
  rw [a_succ 0, a_succ 1, a_succ 2, a_succ 3]
  norm_num only
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The recurrence in shifted form: for every `n`,
`a(n+4) = 3 a(n+3) + 4 a(n+2) - 8 a(n+1) - 8 a(n)`. -/
theorem a_add_four (n : ℕ) :
    a (n + 4) = 3 * a (n + 3) + 4 * a (n + 2) - 8 * a (n + 1) - 8 * a n := by
  rcases n with _ | m
  · obtain ⟨h1, h2, h3, h4⟩ := a_one_to_four
    rw [a_zero, h1, h2, h3, h4]
    norm_num
  · rw [a_succ (m + 4), a_succ (m + 3), a_succ (m + 2), a_succ (m + 1), a_succ m]
    have hS := S_rec m
    rw [show m + 1 + 4 = m + 5 by ring, show m + 1 + 3 = m + 4 by ring,
      show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring,
      pow_succ, pow_succ, pow_succ, pow_succ]
    linear_combination (8 * 2 ^ m : ℚ) * hS

/-- **Kimberling's conjecture (A264200, entry by Clark Kimberling, Nov 09 2015).**

Verbatim: "Conjecture: a(n) = 3*a(n-1) + 4*a(n-2) - 8*a(n-3) - 8*a(n-4)."

Here `g(0) = {0}`, `g(n) = {x+1 : x ∈ g(n-1)} ∪ {x/2 : x ∈ g(n-1), 0 < x < 2}`
and `a(n) = 2^(n-1) * ∑ g(n)`.  The guard `4 ≤ n` keeps the natural-number
indices `n - 1, …, n - 4` off their truncated values. -/
theorem a_rec (n : ℕ) (hn : 4 ≤ n) :
    a n = 3 * a (n - 1) + 4 * a (n - 2) - 8 * a (n - 3) - 8 * a (n - 4) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa using a_add_four k

/-! ## Agreement with the listed numerators

The entry's terms are *numerators* of `∑ g(n)`; the comment asserts
`∑ g(n) = a(n)/2^(n-1)`.  The following shows that `a(n)` is an odd integer for
`n ≥ 1`, so it is exactly that numerator, and the conjecture is a statement
about the listed sequence. -/

/-- Integer sequence with the conjectured recurrence and the first four listed terms. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 19
  | n + 4 => 3 * b (n + 3) + 4 * b (n + 2) - 8 * b (n + 1) - 8 * b n

/-- `a(n) = b(n)`: the rational `a(n)` is the integer `b(n)`. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [a_zero]; rfl
    | 1, _ => rw [a_one_to_four.1]; rfl
    | 2, _ => rw [a_one_to_four.2.1]; rfl
    | 3, _ => rw [a_one_to_four.2.2.1]; rfl
    | k + 4, ih =>
      rw [a_add_four, ih (k + 3) (by omega), ih (k + 2) (by omega), ih (k + 1) (by omega),
        ih k (by omega), b]
      push_cast
      ring

/-- `b(n)` is odd for `n ≥ 1`. -/
theorem odd_b_succ (n : ℕ) : Odd (b (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | k + 3, ih =>
      have h3 : Odd (b (k + 3)) := ih (k + 2) (by omega)
      have hrec : b (k + 3 + 1) =
          b (k + 3) + 2 * (b (k + 3) + 2 * b (k + 2) - 4 * b (k + 1) - 4 * b k) := by
        rw [show k + 3 + 1 = k + 4 by rfl, b]
        ring
      rw [hrec]
      exact h3.add_even (even_two_mul _)

/-- **Numerator form.** For `n ≥ 1`, the numerator of `∑_{x ∈ g(n)} x` equals `a(n)`,
so `a` is exactly the sequence listed in A264200. -/
theorem num_sum_g_eq_a (n : ℕ) (hn : 1 ≤ n) : ((∑ x ∈ g n, x).num : ℚ) = a n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hsum : ∑ x ∈ g (k + 1), x = ((b (k + 1) : ℤ) : ℚ) / ((2 ^ k : ℤ) : ℚ) := by
    rw [← a_eq_b, a_succ, S]
    push_cast
    rw [mul_div_cancel_left₀ _ (pow_ne_zero k two_ne_zero)]
  have hcop : Nat.Coprime (b (k + 1)).natAbs (2 ^ k : ℤ).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr
      (Int.natAbs_odd.mpr (odd_b_succ k)))
  rw [hsum, Rat.num_div_eq_of_coprime (by positivity) hcop, a_eq_b]

end Candidates.A264200Sum
