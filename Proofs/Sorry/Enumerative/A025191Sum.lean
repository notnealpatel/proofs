/-
# A025191 — half-row sums of A025177 as first differences of A027914 and A081673

## OEIS source (re-pulled with `oeis show A025191`, retrieved 2026-10-21)

```
A025191   a(n) = Sum_{k=0..n} T(n,k), where T is the array defined in A025177.
TERMS:    1,1,4,11,33,97,288,855,2544,7577,22590,67399,201215,601017,...
COMMENT (the conjecture, verbatim):
  Conjectures: a(n) = A027914(n)-A027914(n-1) = (A081673(n)-A081673(n-1))/2.
AUTHOR:   Clark Kimberling (the comment itself carries no author or date).
```

Supporting definitions, verbatim from the referenced entries:

```
A025177   Triangular array, read by rows: first differences in n,n direction
          of trinomial array A027907.
          (formula) G.f.: (1-y*z)/[1-z*(1+y+y^2)].
A027907   Triangle of trinomial coefficients T(n,k) (n >= 0, 0 <= k <= 2*n),
          read by rows: n-th row is obtained by expanding (1 + x + x^2)^n.
A027914   T(n,0) + T(n,1) + ... + T(n,n), T given by A027907.
A081673   Expansion of exp(3*x) - exp(x)*(1-BesselI_0(2*x)).
```

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell).  The statement is elementary: it is proved below in full.

## Proof outline

* `T(n,k) = tri(n,k) - tri(n-1,k-1)`, so the half-row sum telescopes to
  `A027914(n) - A027914(n-1)` (`a025191_succ_eq_sub_a027914`).
* `(1+x+x^2)^n` is palindromic of degree `2n` and has coefficient sum `3^n`,
  so `2 * A027914(n) = 3^n + tri(n,n)` (`two_mul_a027914`).
* Expanding `(x + (1+x^2))^n` gives `tri(n,n) = Sum_j C(n,j) i(n-j)` with
  `i(2l) = C(2l,l)`, `i(odd) = 0` (`trinomial_central`); the same sum is the
  `n! [x^n]` coefficient of `exp(x) * BesselI_0(2x)`, so
  `A081673(n) = 2 * A027914(n) - 1` (`a081673_eq_two_mul_a027914_sub_one`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A025191Sum

open Polynomial Finset

/-! ## Definition layer -/

/-- A027907: the trinomial coefficient `T(n,k)`, the coefficient of `x^k` in
`(1 + x + x^2)^n`. -/
noncomputable def trinomial (n k : ℕ) : ℕ := ((1 + X + X ^ 2 : ℕ[X]) ^ n).coeff k

/-- A025177: first differences in the `n,n` direction of the trinomial array,
`T(n,k) = tri(n,k) - tri(n-1,k-1)`, with `tri(n-1,k-1) = 0` when `n = 0` or
`k = 0`.  Valued in `ℤ` so that the difference is never truncated. -/
noncomputable def T : ℕ → ℕ → ℤ
  | n + 1, k + 1 => (trinomial (n + 1) (k + 1) : ℤ) - trinomial n k
  | n, k => trinomial n k

/-- A025191: `a(n) = Sum_{k=0..n} T(n,k)` with `T` the array A025177. -/
noncomputable def a025191 (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), T n k

/-- A027914: `tri(n,0) + tri(n,1) + ... + tri(n,n)` with `tri` the trinomial
array A027907. -/
noncomputable def a027914 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), trinomial n k

/-- The power series `BesselI_0(2x) = Sum_m x^(2m) / (m!)^2` over `ℚ`. -/
noncomputable def besselI0Two : PowerSeries ℚ :=
  PowerSeries.mk fun k => if Even k then 1 / ((k / 2).factorial : ℚ) ^ 2 else 0

/-- The exponential generating function `exp(3x) - exp(x) * (1 - BesselI_0(2x))`
of A081673. -/
noncomputable def a081673Egf : PowerSeries ℚ :=
  PowerSeries.rescale (3 : ℚ) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ * (1 - besselI0Two)

/-- A081673: `a(n) = n! * [x^n] (exp(3x) - exp(x) * (1 - BesselI_0(2x)))`. -/
noncomputable def a081673 (n : ℕ) : ℚ := n.factorial * PowerSeries.coeff n a081673Egf

/-- The coefficient `i(m) = m! [x^m] BesselI_0(2x)`: `C(2l,l)` at `m = 2l`, `0` at
odd `m`. -/
def iCoef (m : ℕ) : ℕ := if Even m then m.choose (m / 2) else 0

/-! ## Computable twin, for the ground-truth checks -/

/-- Closed form of the trinomial coefficient from `(x + (1 + x^2))^n`:
`Sum_{j ≤ min(n,k)} C(n,j) [x^(k-j)] (1+x^2)^(n-j)`. -/
def trinomialSum (n k : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1),
    if j ≤ k then n.choose j * (if Even (k - j) then (n - j).choose ((k - j) / 2) else 0)
    else 0

/-- The coefficient of `x^k` in `(1 + x^2)^m`. -/
lemma coeff_one_add_X_sq_pow (m k : ℕ) :
    ((1 + X ^ 2 : ℕ[X]) ^ m).coeff k = if Even k then m.choose (k / 2) else 0 := by
  have h : (1 + X ^ 2 : ℕ[X]) ^ m = expand ℕ 2 ((1 + X) ^ m) := by simp
  rw [h, coeff_expand (by norm_num), coeff_one_add_X_pow]
  simp [even_iff_two_dvd]

/-- The trinomial coefficient agrees with its closed form `trinomialSum`. -/
lemma trinomial_eq_trinomialSum (n k : ℕ) : trinomial n k = trinomialSum n k := by
  unfold trinomial trinomialSum
  rw [show (1 + X + X ^ 2 : ℕ[X]) = X + (1 + X ^ 2) by ring, add_pow, finsetSum_coeff]
  refine sum_congr rfl fun j _ => ?_
  rw [← Nat.cast_comm, coeff_natCast_mul, coeff_X_pow_mul', Nat.cast_id]
  by_cases hjk : j ≤ k
  · rw [if_pos hjk, if_pos hjk, coeff_one_add_X_sq_pow]
  · rw [if_neg hjk, if_neg hjk, mul_zero]

/-- Function form of `trinomial_eq_trinomialSum`. -/
lemma trinomial_eq_trinomialSum_fun : trinomial = trinomialSum :=
  funext fun n => funext fun k => trinomial_eq_trinomialSum n k

/-- Computable twin of `T`. -/
def TSum : ℕ → ℕ → ℤ
  | n + 1, k + 1 => (trinomialSum (n + 1) (k + 1) : ℤ) - trinomialSum n k
  | n, k => trinomialSum n k

/-- `T` agrees with its computable twin `TSum`. -/
lemma T_eq_TSum (n k : ℕ) : T n k = TSum n k := by
  rcases n with _ | n <;> rcases k with _ | k <;>
    simp only [T, TSum, trinomial_eq_trinomialSum]

/-- Function form of `T_eq_TSum`. -/
lemma T_eq_TSum_fun : T = TSum := funext fun n => funext fun k => T_eq_TSum n k

/-- Computable form of `a025191`. -/
lemma a025191_eq_fun : a025191 = fun n => ∑ k ∈ range (n + 1), TSum n k := by
  funext n; simp only [a025191, T_eq_TSum_fun]

/-- Computable form of `a027914`. -/
lemma a027914_eq_fun : a027914 = fun n => ∑ k ∈ range (n + 1), trinomialSum n k := by
  funext n; simp only [a027914, trinomial_eq_trinomialSum_fun]

/-! ## Ground truth -/

-- A027907 rows 2 and 3: `1,2,3,2,1` and `1,3,6,7,6,3,1`.
example : (List.range 5).map (trinomial 2) = [1, 2, 3, 2, 1] := by
  rw [trinomial_eq_trinomialSum_fun]; decide

example : (List.range 7).map (trinomial 3) = [1, 3, 6, 7, 6, 3, 1] := by
  rw [trinomial_eq_trinomialSum_fun]; decide

-- A025177 rows 1 to 4: `1,0,1`, `1,1,2,1,1`, `1,2,4,4,4,2,1`, `1,3,7,10,12,10,7,3,1`.
example : (List.range 3).map (T 1) = [1, 0, 1] ∧
    (List.range 5).map (T 2) = [1, 1, 2, 1, 1] ∧
    (List.range 7).map (T 3) = [1, 2, 4, 4, 4, 2, 1] ∧
    (List.range 9).map (T 4) = [1, 3, 7, 10, 12, 10, 7, 3, 1] := by
  rw [T_eq_TSum_fun]; decide

-- A025191 DATA: `1,1,4,11,33,97,288,855`.
example : (List.range 8).map a025191 = [1, 1, 4, 11, 33, 97, 288, 855] := by
  rw [a025191_eq_fun]; decide

-- A027914 DATA: `1,2,6,17,50,147,435,1290`.
example : (List.range 8).map a027914 = [1, 2, 6, 17, 50, 147, 435, 1290] := by
  rw [a027914_eq_fun]; decide

/-! ## Telescoping: the first equality -/

/-- The first conjectured equality in shifted form:
`a(n+1) = A027914(n+1) - A027914(n)`. -/
theorem a025191_succ_eq_sub_a027914 (n : ℕ) :
    a025191 (n + 1) = (a027914 (n + 1) : ℤ) - a027914 n := by
  unfold a025191 a027914
  rw [sum_range_succ', sum_range_succ' (fun k => trinomial (n + 1) k)]
  simp only [T, Nat.cast_add, Nat.cast_sum, sum_sub_distrib]
  ring

/-! ## Symmetry, row sum, and the central coefficient -/

/-- `1 + x + x^2` has degree at most `2`. -/
lemma natDegree_q : (1 + X + X ^ 2 : ℕ[X]).natDegree ≤ 2 := by compute_degree

/-- `1 + x + x^2` is palindromic of degree `2`. -/
lemma reflect_q : reflect 2 (1 + X + X ^ 2 : ℕ[X]) = 1 + X + X ^ 2 := by
  ext i
  rw [coeff_reflect]
  rcases i with _ | _ | _ | i
  · rw [revAt_le (by norm_num)]; simp [coeff_one, coeff_X]
  · rw [revAt_le (by norm_num)]
  · rw [revAt_le (by norm_num)]; simp [coeff_one, coeff_X]
  · rw [revAt_eq_self_of_lt (by omega)]

/-- `(1 + x + x^2)^n` is palindromic of degree `2n`. -/
lemma reflect_q_pow (n : ℕ) :
    reflect (2 * n) ((1 + X + X ^ 2 : ℕ[X]) ^ n) = (1 + X + X ^ 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdeg : ((1 + X + X ^ 2 : ℕ[X]) ^ n).natDegree ≤ 2 * n := by
      calc _ ≤ n * (1 + X + X ^ 2 : ℕ[X]).natDegree := natDegree_pow_le
        _ ≤ n * 2 := Nat.mul_le_mul_left n natDegree_q
        _ = 2 * n := by ring
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_succ, reflect_mul _ _ hdeg natDegree_q, ih,
      reflect_q]

/-- Symmetry of the trinomial array: `tri(n, 2n-k) = tri(n, k)` for `k ≤ 2n`. -/
lemma trinomial_symm (n k : ℕ) (hk : k ≤ 2 * n) : trinomial n (2 * n - k) = trinomial n k := by
  unfold trinomial
  conv_rhs => rw [← reflect_q_pow n, coeff_reflect, revAt_le hk]

/-- Full row sum of the trinomial array: `Sum_{k=0..2n} tri(n,k) = 3^n`. -/
lemma sum_trinomial (n : ℕ) : ∑ k ∈ range (2 * n + 1), trinomial n k = 3 ^ n := by
  have hdeg : ((1 + X + X ^ 2 : ℕ[X]) ^ n).natDegree < 2 * n + 1 := by
    calc _ ≤ n * (1 + X + X ^ 2 : ℕ[X]).natDegree := natDegree_pow_le
        _ ≤ n * 2 := Nat.mul_le_mul_left n natDegree_q
        _ < 2 * n + 1 := by omega
  have h := eval_eq_sum_range' hdeg (1 : ℕ)
  simp only [eval_pow, eval_add, eval_one, eval_X, one_pow, mul_one] at h
  unfold trinomial
  rw [← h]; norm_num

/-- Central trinomial coefficient: `tri(n,n) = Sum_j C(n,j) i(n-j)`. -/
lemma trinomial_central (n : ℕ) :
    trinomial n n = ∑ j ∈ range (n + 1), n.choose j * iCoef (n - j) := by
  rw [trinomial_eq_trinomialSum, trinomialSum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [if_pos hj', iCoef]

/-- `2 * A027914(n) = 3^n + tri(n,n)`, from symmetry and the row sum. -/
lemma two_mul_a027914 (n : ℕ) : 2 * a027914 n = 3 ^ n + trinomial n n := by
  unfold a027914
  have hsplit : ∑ k ∈ range (2 * n + 1), trinomial n k =
      ∑ k ∈ range (n + 1), trinomial n k + ∑ k ∈ range n, trinomial n (n + 1 + k) := by
    rw [show 2 * n + 1 = (n + 1) + n by ring, sum_range_add]
  have hupper : ∑ k ∈ range n, trinomial n (n + 1 + k) = ∑ k ∈ range n, trinomial n k := by
    rw [← sum_range_reflect (fun k => trinomial n k) n]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [← trinomial_symm n (n + 1 + k) (by omega)]
    congr 1; omega
  rw [sum_trinomial, hupper, sum_range_succ] at hsplit
  rw [hsplit, sum_range_succ]; ring

/-! ## The exponential generating function of A081673 -/

/-- One term of the e.g.f. product: `(j+m)! * (1/j!) * [x^m] BesselI_0(2x) = C(j+m,j) i(m)`. -/
lemma factorial_mul_coeff_besselI0Two (j m : ℕ) :
    ((j + m).factorial : ℚ) * ((1 / (j.factorial : ℚ)) * PowerSeries.coeff m besselI0Two) =
      ((j + m).choose j * iCoef m : ℕ) := by
  rw [besselI0Two, PowerSeries.coeff_mk, iCoef]
  by_cases hm : Even m
  · obtain ⟨l, rfl⟩ := hm
    have hl : (l + l) / 2 = l := by omega
    rw [if_pos ⟨l, rfl⟩, if_pos ⟨l, rfl⟩, hl]
    have h1 := Nat.add_choose_mul_factorial_mul_factorial (l + l) j
    have h2 := Nat.add_choose_mul_factorial_mul_factorial l l
    have h1q : (((l + l + j).choose j : ℕ) : ℚ) * ((l + l).factorial : ℚ) * (j.factorial : ℚ) =
        ((l + l + j).factorial : ℚ) := by exact_mod_cast h1
    have h2q : (((l + l).choose l : ℕ) : ℚ) * (l.factorial : ℚ) * (l.factorial : ℚ) =
        ((l + l).factorial : ℚ) := by exact_mod_cast h2
    rw [add_comm j (l + l)]
    push_cast
    rw [← h1q, ← h2q]
    field_simp
  · rw [if_neg hm, if_neg hm]
    simp

/-- Coefficient extraction from the e.g.f.:
`A081673(n) = 3^n - 1 + Sum_j C(n,j) i(n-j)`. -/
theorem a081673_eq (n : ℕ) :
    a081673 n = 3 ^ n - 1 + ∑ j ∈ range (n + 1), ((n.choose j * iCoef (n - j) : ℕ) : ℚ) := by
  unfold a081673 a081673Egf
  rw [mul_sub, mul_one, map_sub, map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (PowerSeries.exp ℚ) * PowerSeries.coeff j besselI0Two)]
  simp only [PowerSeries.coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
  rw [mul_sub, mul_sub, mul_sum]
  have hterm : ∀ j ∈ range (n + 1), (n.factorial : ℚ) * (1 / (j.factorial : ℚ) *
      PowerSeries.coeff (n - j) besselI0Two) = ((n.choose j * iCoef (n - j) : ℕ) : ℚ) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h := factorial_mul_coeff_besselI0Two j (n - j)
    rwa [Nat.add_sub_cancel' hj'] at h
  rw [sum_congr rfl hterm]
  have hfact : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

-- A081673 DATA: `1,3,11,33,99,293`.
example : a081673 0 = 1 ∧ a081673 1 = 3 ∧ a081673 2 = 11 ∧ a081673 3 = 33 ∧
    a081673 4 = 99 ∧ a081673 5 = 293 := by
  simp only [a081673_eq]
  norm_num [sum_range_succ, iCoef, Nat.choose]

/-- `A081673(n) = 2 * A027914(n) - 1`. -/
theorem a081673_eq_two_mul_a027914_sub_one (n : ℕ) :
    a081673 n = 2 * (a027914 n : ℚ) - 1 := by
  have h := two_mul_a027914 n
  rw [trinomial_central] at h
  have hq : (2 : ℚ) * (a027914 n : ℚ) =
      3 ^ n + ∑ j ∈ range (n + 1), ((n.choose j * iCoef (n - j) : ℕ) : ℚ) := by
    exact_mod_cast h
  rw [a081673_eq, hq]
  ring

/-! ## The conjecture -/

/-- **A025191 conjecture (comment in the entry, unattributed, undated).**

Verbatim: "Conjectures: a(n) = A027914(n)-A027914(n-1) = (A081673(n)-A081673(n-1))/2."

Stated for `n ≥ 1` in the shifted form `n + 1` (no `ℕ` subtraction in the index):
for every `n`, `a(n+1) = A027914(n+1) - A027914(n)` (in `ℤ`) and
`a(n+1) = (A081673(n+1) - A081673(n)) / 2` (in `ℚ`).  The index `n = 0` of the
entry is excluded: there `(A081673(0) - A081673(-1))/2` is undefined (with
`A081673(-1) = 0` it is `1/2 ≠ 1 = a(0)`). -/
theorem a025191_conjecture (n : ℕ) :
    a025191 (n + 1) = (a027914 (n + 1) : ℤ) - a027914 n ∧
      (a025191 (n + 1) : ℚ) = (a081673 (n + 1) - a081673 n) / 2 := by
  refine ⟨a025191_succ_eq_sub_a027914 n, ?_⟩
  rw [a025191_succ_eq_sub_a027914, a081673_eq_two_mul_a027914_sub_one,
    a081673_eq_two_mul_a027914_sub_one]
  push_cast
  ring

end Candidates.A025191Sum
