/-
# A264201 — Kimberling: a sextic linear recurrence for the sums of the sets g(n)

## OEIS source (retrieved with `oeis show A264201`, 2026-10-21)

```
NAME:     Numerator of sum of numbers in set g(n) generated as in Comments.
TERMS:    0,1,7,46,265,1519,8560,47578,264076,1461439,8075011,44596708,
          246189961,1358762089,7498499272,41378660380,228330571360,...
OFFSET:   0
KEYWORDS: nonn,easy
COMMENT:  Starting with g(0) = {0}, generate g(n) for n > 0 inductively using
          these rules:
          (1)  if x is in g(n-1), then x + 1 is in g(n); and
          (2)  if x is in g(n-1) and x < 3, then x/3 is in g(n).
          The sum of numbers in g(n) is a(n)/3^(n-1).
FORMULA (the conjecture):
          Conjecture: a(n) = 4*a(n-1) + 9*a(n-2) + 18*a(n-3) - 81*a(n-4)
          - 162*a(n-5) - 243*a(n-6).
AUTHOR:   _Clark Kimberling_, Nov 09 2015 (the conjecture line carries no
          separate signature; it falls under the entry's %A line).
MATHEMATICA:
          z = 5; x = 1/3;  g[0] = {0}; g[1] = {1};
          g[n_] := g[n] = Union[1 + g[n - 1], (1/3) Select[g[n - 1], # < 3 &]]
XREF:     Cf. A264200.
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This file proves it (`a_rec`), together with the
identification of `a(n)` with the listed numerators (`num_sum_g_eq_a`).
The method is that of the sibling `Proofs/Enumerative/A264200Sum.lean`.

## Definitional fidelity

* Rule (2) is applied to `x` with `0 < x < 3`, not `x < 3`: the entry's own
  program hard-codes `g[1] = {1}`, which is what the strict lower bound
  produces; with `x = 0` admitted, `g(1)` would be `{0, 1}` and `0` would
  persist, contradicting the listed terms.  Since `0 ∉ g(n)` for `n ≥ 1`, the
  lower bound only acts at the step `g(0) → g(1)`.
* `a(n)` is `3^(n-1) * ∑ g(n)` (integer exponent `(n : ℤ) - 1`, so `a 0 = 0`
  without a natural-subtraction convention), exactly as the triage records the
  conjecture and as the entry's comment "The sum of numbers in g(n) is
  a(n)/3^(n-1)" defines it.  The ground-truth examples check it against the
  listed numerators.

## Proof outline

The two images in the union are disjoint (`x + 1 ≥ 1 > y/3`) and both maps are
injective, so `∑_{g(n+1)} f = ∑_{x ∈ g(n)} (f (x+1) + [0<x<3] f (x/3))`.  For
`n ≥ 1` all elements are positive, and the eight sums
`S = ∑ x`, `C = ∑ 1`, `Dₖ = ∑ [x<k]`, `Tₖ = ∑ [x<k] x` (`k = 1, 2, 3`) satisfy
a linear step system.  Two invariants `D₁ + D₂ + D₃ = 2 C` and
`T₁ + T₂ + T₃ + 2 D₁ + D₂ = 3 C` (true at `n = 1`, preserved by the step) cut
the eigenvalue `1` down to multiplicity one, whence
`3 S(n+6) - 4 S(n+5) - 3 S(n+4) - 2 S(n+3) + 3 S(n+2) + 2 S(n+1) + S(n) = 0`
for `n ≥ 1` (characteristic polynomial `(y - 1)(3y² + 2y + 1)(y³ - y² - y - 1)`);
scaling by `3^(n+4)` gives the sextic; the case `n = 6` (which involves `a 0`)
follows from the step system started at `g 1 = {1}`.  Finally `a(n)` is shown
to be an integer `≡ 1 (mod 3)` for `n ≥ 1`, hence equal to the listed numerator
of `∑ g(n)`.
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

namespace Candidates.A264201SameConstructionSum

/-! ## Definition layer -/

/-- The sets `g(n) ⊆ ℚ` of A264201: `g(0) = {0}` and
`g(n+1) = {x + 1 : x ∈ g(n)} ∪ {x / 3 : x ∈ g(n), 0 < x < 3}`. -/
def g : ℕ → Finset ℚ
  | 0 => {0}
  | n + 1 => (g n).image (· + 1) ∪ ((g n).filter (fun x => 0 < x ∧ x < 3)).image (· / 3)

/-- A264201 as the conjecture uses it: `a(n) = 3^(n-1) * ∑_{x ∈ g(n)} x`
(integer exponent, so `a 0 = 3⁻¹ * 0 = 0`). -/
def a (n : ℕ) : ℚ := (3 : ℚ) ^ ((n : ℤ) - 1) * ∑ x ∈ g n, x

/-! ### Ground truth -/

example : g 1 = {1} := by decide +kernel
example : g 2 = {2, 1 / 3} := by decide +kernel
example : g 3 = {3, 4 / 3, 2 / 3, 1 / 9} := by decide +kernel
example : a 0 = 0 := by decide +kernel
example : a 1 = 1 := by decide +kernel
example : a 2 = 7 := by decide +kernel
example : a 3 = 46 := by decide +kernel
example : a 5 = 1519 := by decide +kernel
example : a 6 = 8560 := by decide +kernel

/-! ## Structure of the sets `g(n)` -/

/-- Unfolding equation for `g (n + 1)`. -/
theorem g_succ (n : ℕ) : g (n + 1) =
    (g n).image (· + 1) ∪ ((g n).filter (fun x => 0 < x ∧ x < 3)).image (· / 3) := rfl

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

/-- Sums over `g(n+1)`: the union is disjoint (`x + 1 ≥ 1 > y / 3`) and both
maps are injective, so a sum over `g(n+1)` is a sum over `g(n)`. -/
theorem sum_g_succ (n : ℕ) (f : ℚ → ℚ) : ∑ x ∈ g (n + 1), f x =
    ∑ x ∈ g n, (f (x + 1) + if 0 < x ∧ x < 3 then f (x / 3) else 0) := by
  have hdisj : Disjoint ((g n).image (· + 1))
      (((g n).filter (fun x => 0 < x ∧ x < 3)).image (· / 3)) := by
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

/-! ## The eight tracked sums and their step system -/

/-- Total sum `S(n) = ∑_{x ∈ g(n)} x`. -/
def S (n : ℕ) : ℚ := ∑ x ∈ g n, x
/-- Count `C(n) = |g(n)|`, as a rational sum. -/
def C (n : ℕ) : ℚ := ∑ _x ∈ g n, (1 : ℚ)
/-- Count of elements `x < 1` of `g(n)`. -/
def D1 (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 1 then (1 : ℚ) else 0
/-- Count of elements `x < 2` of `g(n)`. -/
def D2 (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 2 then (1 : ℚ) else 0
/-- Count of elements `x < 3` of `g(n)`. -/
def D3 (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 3 then (1 : ℚ) else 0
/-- Sum of the elements `x < 1` of `g(n)`. -/
def T1 (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 1 then x else 0
/-- Sum of the elements `x < 2` of `g(n)`. -/
def T2 (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 2 then x else 0
/-- Sum of the elements `x < 3` of `g(n)`. -/
def T3 (n : ℕ) : ℚ := ∑ x ∈ g n, if x < 3 then x else 0

/-- Step for `S` (for `n ≥ 1`): `S(n+1) = S(n) + C(n) + T₃(n)/3`. -/
theorem S_step (m : ℕ) : 3 * S (m + 2) = 3 * S (m + 1) + 3 * C (m + 1) + T3 (m + 1) := by
  simp only [S, C, T3]
  rw [sum_g_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `C` (for `n ≥ 1`): `C(n+1) = C(n) + D₃(n)`. -/
theorem C_step (m : ℕ) : C (m + 2) = C (m + 1) + D3 (m + 1) := by
  simp only [C, D3]
  rw [sum_g_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `D₁` (for `n ≥ 1`): `D₁(n+1) = D₃(n)`. -/
theorem D1_step (m : ℕ) : D1 (m + 2) = D3 (m + 1) := by
  simp only [D1, D3]
  rw [sum_g_succ]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `D₂` (for `n ≥ 1`): `D₂(n+1) = D₁(n) + D₃(n)`. -/
theorem D2_step (m : ℕ) : D2 (m + 2) = D1 (m + 1) + D3 (m + 1) := by
  simp only [D1, D2, D3]
  rw [sum_g_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `D₃` (for `n ≥ 1`): `D₃(n+1) = D₂(n) + D₃(n)`. -/
theorem D3_step (m : ℕ) : D3 (m + 2) = D2 (m + 1) + D3 (m + 1) := by
  simp only [D2, D3]
  rw [sum_g_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `T₁` (for `n ≥ 1`): `T₁(n+1) = T₃(n)/3`. -/
theorem T1_step (m : ℕ) : 3 * T1 (m + 2) = T3 (m + 1) := by
  simp only [T1, T3]
  rw [sum_g_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `T₂` (for `n ≥ 1`): `T₂(n+1) = T₁(n) + D₁(n) + T₃(n)/3`. -/
theorem T2_step (m : ℕ) :
    3 * T2 (m + 2) = 3 * T1 (m + 1) + 3 * D1 (m + 1) + T3 (m + 1) := by
  simp only [T1, T2, T3, D1]
  rw [sum_g_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- Step for `T₃` (for `n ≥ 1`): `T₃(n+1) = T₂(n) + D₂(n) + T₃(n)/3`. -/
theorem T3_step (m : ℕ) :
    3 * T3 (m + 2) = 3 * T2 (m + 1) + 3 * D2 (m + 1) + T3 (m + 1) := by
  simp only [T2, T3, D2]
  rw [sum_g_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 := pos_of_mem_g_succ m x hx
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- The two invariants, for `n ≥ 1`: `D₁(n) + D₂(n) + D₃(n) = 2 C(n)` and
`T₁(n) + T₂(n) + T₃(n) + 2 D₁(n) + D₂(n) = 3 C(n)`. -/
theorem invariants (m : ℕ) :
    D1 (m + 1) + D2 (m + 1) + D3 (m + 1) = 2 * C (m + 1) ∧
      T1 (m + 1) + T2 (m + 1) + T3 (m + 1) + 2 * D1 (m + 1) + D2 (m + 1) = 3 * C (m + 1) := by
  induction m with
  | zero =>
    simp only [C, D1, D2, D3, T1, T2, T3, zero_add, g_one, Finset.sum_singleton]
    norm_num
  | succ k ih =>
    obtain ⟨hD, hT⟩ := ih
    have hC := C_step k
    have hD1 := D1_step k
    have hD2 := D2_step k
    have hD3 := D3_step k
    have hT1 := T1_step k
    have hT2 := T2_step k
    have hT3 := T3_step k
    constructor <;> linarith

/-- The recurrence for the plain sums, for `n ≥ 1`:
`3 S(n+6) - 4 S(n+5) - 3 S(n+4) - 2 S(n+3) + 3 S(n+2) + 2 S(n+1) + S(n) = 0`. -/
theorem S_rec (m : ℕ) :
    3 * S (m + 7) - 4 * S (m + 6) - 3 * S (m + 5) - 2 * S (m + 4) + 3 * S (m + 3)
      + 2 * S (m + 2) + S (m + 1) = 0 := by
  have i0 := invariants m
  have i1 := invariants (m + 1)
  have i2 := invariants (m + 2)
  have i3 := invariants (m + 3)
  have i4 := invariants (m + 4)
  have i5 := invariants (m + 5)
  have s0 := S_step m
  have s1 := S_step (m + 1)
  have s2 := S_step (m + 2)
  have s3 := S_step (m + 3)
  have s4 := S_step (m + 4)
  have s5 := S_step (m + 5)
  have c0 := C_step m
  have c1 := C_step (m + 1)
  have c2 := C_step (m + 2)
  have c3 := C_step (m + 3)
  have c4 := C_step (m + 4)
  have d10 := D1_step m
  have d11 := D1_step (m + 1)
  have d12 := D1_step (m + 2)
  have d13 := D1_step (m + 3)
  have d14 := D1_step (m + 4)
  have d20 := D2_step m
  have d21 := D2_step (m + 1)
  have d22 := D2_step (m + 2)
  have d23 := D2_step (m + 3)
  have d24 := D2_step (m + 4)
  have d30 := D3_step m
  have d31 := D3_step (m + 1)
  have d32 := D3_step (m + 2)
  have d33 := D3_step (m + 3)
  have d34 := D3_step (m + 4)
  have t10 := T1_step m
  have t11 := T1_step (m + 1)
  have t12 := T1_step (m + 2)
  have t13 := T1_step (m + 3)
  have t14 := T1_step (m + 4)
  have t20 := T2_step m
  have t21 := T2_step (m + 1)
  have t22 := T2_step (m + 2)
  have t23 := T2_step (m + 3)
  have t24 := T2_step (m + 4)
  have t30 := T3_step m
  have t31 := T3_step (m + 1)
  have t32 := T3_step (m + 2)
  have t33 := T3_step (m + 3)
  have t34 := T3_step (m + 4)
  linarith [i0.1, i0.2, i1.1, i1.2, i2.1, i2.2, i3.1, i3.2, i4.1, i4.2, i5.1, i5.2]

/-! ## The conjecture -/

/-- `a(k+1) = 3^k * S(k+1)`. -/
theorem a_succ (k : ℕ) : a (k + 1) = 3 ^ k * S (k + 1) := by
  simp only [a, S]
  congr 1
  rw [Nat.cast_succ, add_sub_cancel_right, zpow_natCast]

/-- The eight tracked sums at `n = 1`, where `g 1 = {1}`. -/
theorem state_one : S 1 = 1 ∧ C 1 = 1 ∧ D1 1 = 0 ∧ D2 1 = 1 ∧ D3 1 = 1 ∧
    T1 1 = 0 ∧ T2 1 = 1 ∧ T3 1 = 1 := by
  simp only [S, C, D1, D2, D3, T1, T2, T3, g_one, Finset.sum_singleton]
  norm_num

/-- `a 0 = 0`. -/
theorem a_zero : a 0 = 0 := by
  simp [a, g]

/-- `a 1 = 1`, …, `a 6 = 8560`, derived from the step system. -/
theorem a_one_to_six : a 1 = 1 ∧ a 2 = 7 ∧ a 3 = 46 ∧ a 4 = 265 ∧ a 5 = 1519 ∧
    a 6 = 8560 := by
  obtain ⟨hS, hC, hD1, hD2, hD3, hT1, hT2, hT3⟩ := state_one
  have s0 := S_step 0
  have s1 := S_step 1
  have s2 := S_step 2
  have s3 := S_step 3
  have s4 := S_step 4
  have c0 := C_step 0
  have c1 := C_step 1
  have c2 := C_step 2
  have c3 := C_step 3
  have d10 := D1_step 0
  have d11 := D1_step 1
  have d12 := D1_step 2
  have d20 := D2_step 0
  have d21 := D2_step 1
  have d22 := D2_step 2
  have d30 := D3_step 0
  have d31 := D3_step 1
  have d32 := D3_step 2
  have t10 := T1_step 0
  have t11 := T1_step 1
  have t12 := T1_step 2
  have t20 := T2_step 0
  have t21 := T2_step 1
  have t22 := T2_step 2
  have t30 := T3_step 0
  have t31 := T3_step 1
  have t32 := T3_step 2
  have t33 := T3_step 3
  norm_num only at s0 s1 s2 s3 s4 c0 c1 c2 c3 d10 d11 d12 d20 d21 d22 d30 d31 d32
  norm_num only at t10 t11 t12 t20 t21 t22 t30 t31 t32 t33
  rw [a_succ 0, a_succ 1, a_succ 2, a_succ 3, a_succ 4, a_succ 5]
  norm_num only
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The recurrence in shifted form: for every `n`,
`a(n+6) = 4 a(n+5) + 9 a(n+4) + 18 a(n+3) - 81 a(n+2) - 162 a(n+1) - 243 a(n)`. -/
theorem a_add_six (n : ℕ) :
    a (n + 6) = 4 * a (n + 5) + 9 * a (n + 4) + 18 * a (n + 3) - 81 * a (n + 2)
      - 162 * a (n + 1) - 243 * a n := by
  rcases n with _ | m
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := a_one_to_six
    rw [a_zero, h1, h2, h3, h4, h5, h6]
    norm_num
  · rw [a_succ (m + 6), a_succ (m + 5), a_succ (m + 4), a_succ (m + 3), a_succ (m + 2),
      a_succ (m + 1), a_succ m]
    have hS := S_rec m
    rw [show m + 1 + 6 = m + 7 by ring, show m + 1 + 5 = m + 6 by ring,
      show m + 1 + 4 = m + 5 by ring, show m + 1 + 3 = m + 4 by ring,
      show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring]
    linear_combination (3 ^ m * 3 ^ 5 : ℚ) * hS

/-- **Kimberling's conjecture (A264201, entry by Clark Kimberling, Nov 09 2015).**

Verbatim: "Conjecture: a(n) = 4*a(n-1) + 9*a(n-2) + 18*a(n-3) - 81*a(n-4)
- 162*a(n-5) - 243*a(n-6)."

Here `g(0) = {0}`, `g(n) = {x+1 : x ∈ g(n-1)} ∪ {x/3 : x ∈ g(n-1), 0 < x < 3}`
and `a(n) = 3^(n-1) * ∑ g(n)`.  The guard `6 ≤ n` keeps the natural-number
indices `n - 1, …, n - 6` off their truncated values. -/
theorem a_rec (n : ℕ) (hn : 6 ≤ n) :
    a n = 4 * a (n - 1) + 9 * a (n - 2) + 18 * a (n - 3) - 81 * a (n - 4)
      - 162 * a (n - 5) - 243 * a (n - 6) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa using a_add_six k

/-! ## Agreement with the listed numerators

The entry's terms are *numerators* of `∑ g(n)`; the comment asserts
`∑ g(n) = a(n)/3^(n-1)`.  The following shows that `a(n)` is an integer
`≡ 1 (mod 3)` for `n ≥ 1`, so it is exactly that numerator, and the conjecture is
a statement about the listed sequence. -/

/-- Integer sequence with the conjectured recurrence and the first six listed terms. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 7
  | 3 => 46
  | 4 => 265
  | 5 => 1519
  | n + 6 => 4 * b (n + 5) + 9 * b (n + 4) + 18 * b (n + 3) - 81 * b (n + 2)
      - 162 * b (n + 1) - 243 * b n

/-- `a(n) = b(n)`: the rational `a(n)` is the integer `b(n)`. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [a_zero]; rfl
    | 1, _ => rw [a_one_to_six.1]; rfl
    | 2, _ => rw [a_one_to_six.2.1]; rfl
    | 3, _ => rw [a_one_to_six.2.2.1]; rfl
    | 4, _ => rw [a_one_to_six.2.2.2.1]; rfl
    | 5, _ => rw [a_one_to_six.2.2.2.2.1]; rfl
    | k + 6, ih =>
      rw [a_add_six, ih (k + 5) (by omega), ih (k + 4) (by omega), ih (k + 3) (by omega),
        ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega), b]
      push_cast
      ring

/-- `b(n) ≡ 1 (mod 3)` for `n ≥ 1`. -/
theorem b_succ_emod_three (n : ℕ) : b (n + 1) % 3 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | k + 5, ih =>
      have h5 : b (k + 5) % 3 = 1 := ih (k + 4) (by omega)
      have hrec : b (k + 5 + 1) = b (k + 5) + 3 * (b (k + 5) + 3 * b (k + 4) + 6 * b (k + 3)
          - 27 * b (k + 2) - 54 * b (k + 1) - 81 * b k) := by
        rw [show k + 5 + 1 = k + 6 by rfl, b]
        ring
      rw [hrec, Int.add_mul_emod_self_left, h5]

/-- **Numerator form.** For `n ≥ 1`, the numerator of `∑_{x ∈ g(n)} x` equals `a(n)`,
so `a` is exactly the sequence listed in A264201. -/
theorem num_sum_g_eq_a (n : ℕ) (hn : 1 ≤ n) : ((∑ x ∈ g n, x).num : ℚ) = a n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hsum : ∑ x ∈ g (k + 1), x = ((b (k + 1) : ℤ) : ℚ) / ((3 ^ k : ℤ) : ℚ) := by
    rw [← a_eq_b, a_succ, S]
    push_cast
    rw [mul_div_cancel_left₀ _ (pow_ne_zero k three_ne_zero)]
  have hndvdZ : ¬ (3 : ℤ) ∣ b (k + 1) := by
    rw [Int.dvd_iff_emod_eq_zero, b_succ_emod_three]
    decide
  have hndvd : ¬ 3 ∣ (b (k + 1)).natAbs := fun h =>
    hndvdZ (by exact_mod_cast Int.ofNat_dvd_left.mpr h)
  have hcop : Nat.Coprime (b (k + 1)).natAbs (3 ^ k : ℤ).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd).symm
  rw [hsum, Rat.num_div_eq_of_coprime (by positivity) hcop, a_eq_b]

end Candidates.A264201SameConstructionSum
