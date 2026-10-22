/-
# A177430 / A177431 — Hanna: which powers of the greedy square log-derivative stay integral

## OEIS source (retrieved with `oeis show A177430`, `oeis show A177431` and the live
## entry https://oeis.org/A177430/internal, 2026-10-21)

```
A177430
NAME:     Least monotonically increasing logarithmic derivative consisting of only
          squares.
TERMS:    1,9,16,25,36,144,169,225,484,784,1024,1156,1444,1521,2601,3025,4489,...
COMMENT:  Conjecture: the sequence {a(n)^(m/2), n>=1} forms a logarithmic derivative
          of an integer sequence only when m is a nonnegative even integer.
FORMULA:  a(n) = A177431(n)^2.
PROGRAM:  (PARI) {a(n)=local(V,A=[1],M); V=Vec(exp(x+sum(k=2,n-1,a(k)*x^k/k)
          +t*x^n/n+x*O(x^n)));if(n==1,M=1,M=a(n-1);for(m=sqrtint(a(n-1))+1,
          9*a(n-1),if(denominator(subst(V[ #V],t,m^2))==1,M=m^2;break));M)}
AUTHOR:   Paul D. Hanna, Sep 06 2010

A177431
NAME:     a(n) = sqrt(A177430(n)) where A177430 is the least monotonically
          increasing logarithmic derivative consisting of only squares.
TERMS:    1,3,4,5,6,12,13,15,22,28,32,34,38,39,51,55,67,72,75,80,88,96,...
COMMENT:  Conjecture: the series exp(Sum_{n>=1} a(n)^m*x^n/n) consists entirely of
          integer coefficients only when m is a nonnegative even integer.
```

The conjecture is Paul D. Hanna's (entry author, Sep 06 2010; the comment carries no
separate attribution).

## Status

Triage: open (no proof in the entry or the literature as far as the triage could tell).
This file proves it, for integer exponents `m`, in both directions:

* only-when: for odd `m > 0` the Dold congruence `4 ∣ c(4) - c(2)` fails
  (`5^m - 3^m ≡ 2 mod 4`), and for `m < 0` already `c(2) = 3^m ∉ ℤ`;
* when: `exp (∑ c(n) x^n/n)` is integral iff `c(n) = ∑_{d ∣ n} d w(d)` with `w`
  integral (`integralExp_iff_ghost`), this class is closed under pointwise products
  (`IntegralExp.mul`, via `[d₁∣n] d₁ [d₂∣n] d₂ = gcd · [lcm∣n] lcm`), and A177430
  itself is integral (`integralExp_sq`; the greedy step always succeeds because the
  required residue is a square modulo each prime power `p^j ∣ n`, namely `b(n/p)^2`,
  hence modulo `n` by CRT).

## Formalization choices

* "logarithmic derivative of an integer sequence": `c` is the logarithmic derivative of
  `A` when `∑ c(n) x^n = x A'(x)/A(x)`, i.e. `A = exp (∑ c(n) x^n / n)`, i.e.
  `A 0 = 1`, `n A(n) = ∑_{k=1}^n c(k) A(n-k)` (`expCoeff`); `X_mul_derivative_expSeries`
  and `eq_expSeries_of_X_mul_derivative` check this against Mathlib's
  `PowerSeries.derivative`.
* The exponent `m` ranges over `ℤ`, and `a(n)^(m/2)` is written `b(n)^m` (`zpow` in `ℚ`).
  Real non-integer exponents are not covered: excluding them needs
  "`2^m, 3^m, 5^m ∈ ℤ` ⇒ `m ∈ ℚ`", the six exponentials theorem, absent from Mathlib.
* `b` (A177431) follows the entry's definition: `b 1 = 1` and `b n` is the least
  `m > b(n-1)` making the `n`-th coefficient integral. The PARI search cap `9 a(n-1)` is
  a computational bound and is not part of the definition; `b_admissible` shows the
  least admissible root always exists, so the junk `else` branch is never taken.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A177430HannaSquareRoots

open PowerSeries

/-- Coefficients of `exp (∑_{n ≥ 1} c n * x ^ n / n)`, i.e. the sequence `A` whose
logarithmic derivative is `c`: `A 0 = 1` and `n * A n = ∑_{k=1}^{n} c k * A (n - k)`.
The value `c 0` is never used. -/
noncomputable def expCoeff (c : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => (∑ k ∈ Finset.range (n + 1), c (k + 1) * expCoeff c (n - k)) / (n + 1)
decreasing_by omega

/-- `exp (∑ c n x^n / n)` has only integer coefficients. -/
def IntegralExp (c : ℕ → ℚ) : Prop := ∀ n, ∃ z : ℤ, expCoeff c n = z

/-- The power series `∑_{n ≥ 1} c n * X ^ n`. -/
noncomputable def cSeries (c : ℕ → ℚ) : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else c n

/-- The power series `∑ expCoeff c n * X ^ n`. -/
noncomputable def expSeries (c : ℕ → ℚ) : ℚ⟦X⟧ := PowerSeries.mk (expCoeff c)

/-- The constant coefficient is `1`. -/
theorem expCoeff_zero (c : ℕ → ℚ) : expCoeff c 0 = 1 := by
  rw [expCoeff]

/-- The defining recurrence `(n+1) A(n+1) = ∑_{k=0}^{n} c(k+1) A(n-k)`. -/
theorem expCoeff_succ (c : ℕ → ℚ) (n : ℕ) :
    expCoeff c (n + 1) =
      (∑ k ∈ Finset.range (n + 1), c (k + 1) * expCoeff c (n - k)) / (n + 1) := by
  rw [expCoeff]

/-- `X * F'` has `n`-th coefficient `n * F_n`. -/
theorem coeff_X_mul_derivative (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX ℚ f) = n * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- The defining recurrence of `expCoeff`, in power-series form, coefficientwise. -/
theorem coeff_cSeries_mul (c : ℕ → ℚ) (g : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (cSeries c * g) =
      ∑ k ∈ Finset.range (n + 1), c (k + 1) * coeff (n - k) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [cSeries, coeff_mk]
  simp

/-- `expSeries c` solves the log-derivative equation `X * F' = C * F`. -/
theorem X_mul_derivative_expSeries (c : ℕ → ℚ) :
    X * d⁄dX ℚ (expSeries c) = cSeries c * expSeries c := by
  ext n
  rw [coeff_X_mul_derivative]
  rcases n with _ | n
  · simp [cSeries, coeff_mul]
  · rw [coeff_cSeries_mul]
    simp only [expSeries, coeff_mk, expCoeff_succ]
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- Uniqueness: a series with constant coefficient `1` solving `X * G' = C * G`
is `expSeries c`. -/
theorem eq_expSeries_of_X_mul_derivative (c : ℕ → ℚ) (g : ℚ⟦X⟧) (h0 : constantCoeff g = 1)
    (hg : X * d⁄dX ℚ g = cSeries c * g) : g = expSeries c := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [expSeries, expCoeff_zero, h0]
    · have hc := congrArg (coeff (n + 1)) hg
      rw [coeff_X_mul_derivative, coeff_cSeries_mul] at hc
      simp only [expSeries, coeff_mk, expCoeff_succ]
      have hsum : ∑ k ∈ Finset.range (n + 1), c (k + 1) * coeff (n - k) g =
          ∑ k ∈ Finset.range (n + 1), c (k + 1) * expCoeff c (n - k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ih (n - k) (by omega)]
        simp [expSeries]
      rw [← hsum, ← hc]
      have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring

/-- `cSeries` is additive. -/
theorem cSeries_add (c₁ c₂ : ℕ → ℚ) : cSeries (c₁ + c₂) = cSeries c₁ + cSeries c₂ := by
  ext n
  simp only [cSeries, coeff_mk, map_add, Pi.add_apply]
  split_ifs <;> simp

/-- Additivity: the exponential of a sum of log-derivatives is the product. -/
theorem expSeries_add (c₁ c₂ : ℕ → ℚ) :
    expSeries (c₁ + c₂) = expSeries c₁ * expSeries c₂ := by
  symm
  apply eq_expSeries_of_X_mul_derivative
  · simp [expSeries, expCoeff_zero]
  · rw [Derivation.leibniz, cSeries_add]
    simp only [smul_eq_mul]
    linear_combination (expSeries c₁) * X_mul_derivative_expSeries c₂ +
      (expSeries c₂) * X_mul_derivative_expSeries c₁

/-- Locality: `expCoeff c n` depends only on `c 1, …, c n`. -/
theorem expCoeff_congr (c c' : ℕ → ℚ) (N : ℕ) (h : ∀ k, 0 < k → k ≤ N → c k = c' k) :
    ∀ n ≤ N, expCoeff c n = expCoeff c' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · simp [expCoeff_zero]
    · rw [expCoeff_succ, expCoeff_succ]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [h (k + 1) (by omega) (by omega), ih (n - k) (by omega) (by omega)]

/-- Difference lemma: if `c` and `c'` agree below `n`, the `n`-th coefficients
differ by `(c n - c' n) / n`. -/
theorem expCoeff_sub_of_agree (c c' : ℕ → ℚ) (n : ℕ) (hn : 0 < n)
    (h : ∀ k, 0 < k → k < n → c k = c' k) :
    expCoeff c n - expCoeff c' n = (c n - c' n) / n := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [expCoeff_succ, expCoeff_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum : ∑ k ∈ Finset.range n, c (k + 1) * expCoeff c (n - k) =
      ∑ k ∈ Finset.range n, c' (k + 1) * expCoeff c' (n - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [h (k + 1) (by omega) (by omega),
      expCoeff_congr c c' n (fun j hj hjn => h j hj (by omega)) (n - k) (by omega)]
  rw [hsum, Nat.sub_self, expCoeff_zero, expCoeff_zero]
  push_cast
  ring

/-- Integrality of `exp` is closed under adding log-derivatives. -/
theorem IntegralExp.add {c₁ c₂ : ℕ → ℚ} (h₁ : IntegralExp c₁) (h₂ : IntegralExp c₂) :
    IntegralExp (c₁ + c₂) := by
  intro n
  have hcoeff : expCoeff (c₁ + c₂) n = coeff n (expSeries c₁ * expSeries c₂) := by
    rw [← expSeries_add]
    simp [expSeries]
  choose z₁ hz₁ using h₁
  choose z₂ hz₂ using h₂
  refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, z₁ p.1 * z₂ p.2, ?_⟩
  rw [hcoeff, coeff_mul]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [expSeries, hz₁, hz₂]

/-- The basic log-derivative `n ↦ d * [d ∣ n]`, that of `1 / (1 - x ^ d)`. -/
def basic (d : ℕ) : ℕ → ℚ := fun n => if d ∣ n then (d : ℚ) else 0

/-- The geometric series `∑_j X ^ (d * j) = 1 / (1 - X ^ d)`. -/
noncomputable def geomSeries (d : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun n => if d ∣ n then 1 else 0

/-- `(∑_j X^(d j)) * (1 - X^d) = 1` for `d > 0`. -/
theorem geomSeries_mul (d : ℕ) (hd : 0 < d) : geomSeries d * (1 - X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one]
  simp only [geomSeries, coeff_mk]
  by_cases hn : d ≤ n
  · have hiff : d ∣ n - d ↔ d ∣ n := by
      rw [Nat.dvd_sub_iff_left hn dvd_rfl]
    have hn0 : n ≠ 0 := by omega
    simp [hn, hiff, hn0]
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hn]
    · have hnd : ¬ d ∣ n := fun hdvd => hn (Nat.le_of_dvd hpos hdvd)
      simp [hn, hnd, hpos.ne']

/-- `∑_{n ≥ 1, d ∣ n} d X^n = d X^d / (1 - X^d)`. -/
theorem cSeries_basic (d : ℕ) (hd : 0 < d) :
    cSeries (basic d) = C (d : ℚ) * X ^ d * geomSeries d := by
  ext n
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [cSeries, basic, geomSeries, coeff_mk]
  by_cases hn : d ≤ n
  · have hiff : d ∣ n - d ↔ d ∣ n := by
      rw [Nat.dvd_sub_iff_left hn dvd_rfl]
    have hn0 : n ≠ 0 := by omega
    simp [hn, hiff, hn0]
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hn]
    · have hnd : ¬ d ∣ n := fun hdvd => hn (Nat.le_of_dvd hpos hdvd)
      simp [hn, hnd, hpos.ne']

/-- `cSeries` commutes with negation. -/
theorem cSeries_neg (c : ℕ → ℚ) : cSeries (-c) = -cSeries c := by
  ext n
  simp only [cSeries, coeff_mk, map_neg, Pi.neg_apply]
  split_ifs <;> simp

/-- The zero log-derivative exponentiates to `1`. -/
theorem expSeries_zero : expSeries 0 = 1 := by
  symm
  apply eq_expSeries_of_X_mul_derivative
  · simp
  · have h0 : cSeries 0 = 0 := by
      ext n
      simp [cSeries]
    simp [h0]

/-- `X * (X^d)' = d X^d`. -/
theorem X_mul_derivative_X_pow (d : ℕ) : X * d⁄dX ℚ (X ^ d : ℚ⟦X⟧) = C (d : ℚ) * X ^ d := by
  ext n
  rw [coeff_X_mul_derivative, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h
    simp
  · simp

/-- `exp (-∑_{d ∣ n} d x^n / n) = 1 - x ^ d`. -/
theorem expSeries_neg_basic (d : ℕ) (hd : 0 < d) : expSeries (-basic d) = 1 - X ^ d := by
  symm
  apply eq_expSeries_of_X_mul_derivative
  · simp [hd.ne']
  · rw [cSeries_neg, cSeries_basic d hd, map_sub, Derivation.map_one_eq_zero, zero_sub,
      mul_neg, X_mul_derivative_X_pow]
    linear_combination (C (d : ℚ) * X ^ d) * geomSeries_mul d hd

/-- `exp (∑_{d ∣ n} d x^n / n) = 1 / (1 - x ^ d)`. -/
theorem expSeries_basic (d : ℕ) (hd : 0 < d) : expSeries (basic d) = geomSeries d := by
  have hprod : expSeries (basic d) * (1 - X ^ d) = 1 := by
    rw [← expSeries_neg_basic d hd, ← expSeries_add, add_neg_cancel, expSeries_zero]
  have hne : (1 - X ^ d : ℚ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [hd.ne'] at this
  exact mul_right_cancel₀ hne (hprod.trans (geomSeries_mul d hd).symm)

/-- The zero log-derivative has integral exponential. -/
theorem integralExp_zero : IntegralExp 0 := by
  intro n
  refine ⟨if n = 0 then 1 else 0, ?_⟩
  have h := congrArg (coeff n) expSeries_zero
  simp only [expSeries, coeff_mk, coeff_one] at h
  rw [h]
  split_ifs <;> simp

/-- `1 / (1 - x^d)` has integer coefficients. -/
theorem integralExp_basic (d : ℕ) (hd : 0 < d) : IntegralExp (basic d) := by
  intro n
  refine ⟨if d ∣ n then 1 else 0, ?_⟩
  have h := congrArg (coeff n) (expSeries_basic d hd)
  simp only [expSeries, geomSeries, coeff_mk] at h
  rw [h]
  split_ifs <;> simp

/-- `1 - x^d` has integer coefficients. -/
theorem integralExp_neg_basic (d : ℕ) (hd : 0 < d) : IntegralExp (-basic d) := by
  intro n
  refine ⟨if n = 0 then 1 else if n = d then -1 else 0, ?_⟩
  have h := congrArg (coeff n) (expSeries_neg_basic d hd)
  simp only [expSeries, coeff_mk, map_sub, coeff_one, coeff_X_pow] at h
  rw [h]
  split_ifs <;> simp_all

/-- `(1 - x^d)^(-k)` has integer coefficients for every `k : ℤ`. -/
theorem integralExp_zsmul_basic (k : ℤ) (d : ℕ) (hd : 0 < d) :
    IntegralExp (fun n => (k : ℚ) * basic d n) := by
  induction k using Int.induction_on with
  | zero =>
    have h0 : (fun n => ((0 : ℤ) : ℚ) * basic d n) = 0 := by
      funext n
      simp
    rw [h0]
    exact integralExp_zero
  | succ k ih =>
    have hs : (fun n => (((k : ℤ) + 1 : ℤ) : ℚ) * basic d n) =
        (fun n => ((k : ℤ) : ℚ) * basic d n) + basic d := by
      funext n
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [hs]
    exact ih.add (integralExp_basic d hd)
  | pred k ih =>
    have hs : (fun n => ((-(k : ℤ) - 1 : ℤ) : ℚ) * basic d n) =
        (fun n => ((-(k : ℤ)) : ℚ) * basic d n) + -basic d := by
      funext n
      simp only [Pi.add_apply, Pi.neg_apply]
      push_cast
      ring
    rw [hs]
    exact ih.add (integralExp_neg_basic d hd)

/-- Finite `ℤ`-combinations of basic log-derivatives have integral exponentials. -/
theorem integralExp_sum_basic {ι : Type*} (s : Finset ι) (k : ι → ℤ) (d : ι → ℕ)
    (hd : ∀ i ∈ s, 0 < d i) :
    IntegralExp (fun n => ∑ i ∈ s, (k i : ℚ) * basic (d i) n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (fun n => ∑ i ∈ (∅ : Finset ι), (k i : ℚ) * basic (d i) n) = 0 := by
      funext n
      simp
    rw [h0]
    exact integralExp_zero
  | insert a s ha ih =>
    have hs : (fun n => ∑ i ∈ insert a s, (k i : ℚ) * basic (d i) n) =
        (fun n => (k a : ℚ) * basic (d a) n) + (fun n => ∑ i ∈ s, (k i : ℚ) * basic (d i) n) := by
      funext n
      simp [Finset.sum_insert ha]
    rw [hs]
    exact (integralExp_zsmul_basic (k a) (d a) (hd a (Finset.mem_insert_self a s))).add
      (ih fun i hi => hd i (Finset.mem_insert_of_mem hi))

/-- The ghost map `n ↦ ∑_{d ∣ n} d * w d` (for `n ≥ 1`). -/
def ghost (w : ℕ → ℤ) : ℕ → ℚ := fun n => ∑ d ∈ n.divisors, (d : ℚ) * w d

/-- For `0 < k ≤ N`, the ghost sum at `k` is the `ℤ`-combination of basic sequences with
indices `1, …, N`. -/
theorem ghost_eq_sum_basic (w : ℕ → ℤ) (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    ghost w k = ∑ d ∈ Finset.Icc 1 N, (w d : ℚ) * basic d k := by
  classical
  simp only [ghost, basic, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfil : (Finset.Icc 1 N).filter (· ∣ k) = k.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hdk⟩
      exact ⟨hdk, hk.ne'⟩
    · rintro ⟨hdk, -⟩
      have hle := Nat.le_of_dvd hk hdk
      have hpos := Nat.pos_of_dvd_of_pos hdk hk
      exact ⟨⟨hpos, hle.trans hkN⟩, hdk⟩
  rw [hfil]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- Ghost sequences of integer vectors have integral exponentials. -/
theorem integralExp_ghost (w : ℕ → ℤ) : IntegralExp (ghost w) := by
  intro n
  obtain ⟨z, hz⟩ := integralExp_sum_basic (Finset.Icc 1 n) w id
    (fun i hi => (Finset.mem_Icc.1 hi).1) n
  refine ⟨z, ?_⟩
  rw [← hz]
  exact expCoeff_congr _ _ n (fun k hk hkn => ghost_eq_sum_basic w n k hk hkn) n le_rfl

/-- The (rational) Witt vector of `c`: `n * witt c n = c n - ∑_{d ∣ n, d < n} d * witt c d`. -/
noncomputable def witt (c : ℕ → ℚ) (n : ℕ) : ℚ :=
  (c n - ∑ d ∈ n.properDivisors.attach, ((d : ℕ) : ℚ) * witt c d) / n
termination_by n
decreasing_by exact (Nat.mem_properDivisors.1 d.2).2

/-- The rational Witt coordinates invert the ghost map: `∑_{d ∣ n} d * witt c d = c n`. -/
theorem sum_divisors_witt (c : ℕ → ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (d : ℚ) * witt c d = c n := by
  rw [← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons]
  have hw : witt c n = (c n - ∑ d ∈ n.properDivisors, (d : ℚ) * witt c d) / n := by
    rw [witt, Finset.sum_attach n.properDivisors (fun d => (d : ℚ) * witt c d)]
  rw [hw]
  have hn' : (n : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- The Witt coordinates of `c` below `n`, rounded to integers, and `0` from `n` on. -/
noncomputable def wittTrunc (c : ℕ → ℚ) (n : ℕ) : ℕ → ℤ := fun d => if d < n then ⌊witt c d⌋ else 0

/-- Below `n`, the truncated coordinates are the Witt coordinates when those are integral. -/
theorem wittTrunc_eq {c : ℕ → ℚ} {n : ℕ} (hw : ∀ d, 0 < d → d < n → ∃ z : ℤ, witt c d = z)
    {d : ℕ} (hd : 0 < d) (hdn : d < n) : (wittTrunc c n d : ℚ) = witt c d := by
  obtain ⟨z, hz⟩ := hw d hd hdn
  simp [wittTrunc, hdn, hz]

/-- If the Witt coordinates below `n` are integral, the truncated ghost sequence agrees with
`c` below `n`. -/
theorem ghost_wittTrunc_of_lt {c : ℕ → ℚ} {n : ℕ}
    (hw : ∀ d, 0 < d → d < n → ∃ z : ℤ, witt c d = z) {k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ghost (wittTrunc c n) k = c k := by
  rw [← sum_divisors_witt c k hk, ghost]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdk := Nat.dvd_of_mem_divisors hd
  rw [wittTrunc_eq hw (Nat.pos_of_dvd_of_pos hdk hk) ((Nat.le_of_dvd hk hdk).trans_lt hkn)]

/-- At `n` itself the truncated ghost sequence misses exactly `n * witt c n`. -/
theorem ghost_wittTrunc_self {c : ℕ → ℚ} {n : ℕ} (hn : 0 < n)
    (hw : ∀ d, 0 < d → d < n → ∃ z : ℤ, witt c d = z) :
    ghost (wittTrunc c n) n = c n - n * witt c n := by
  rw [← sum_divisors_witt c n hn, ghost, ← Nat.cons_self_properDivisors hn.ne',
    Finset.sum_cons, Finset.sum_cons]
  have hrest : ∑ d ∈ n.properDivisors, (d : ℚ) * wittTrunc c n d =
      ∑ d ∈ n.properDivisors, (d : ℚ) * witt c d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdn, hlt⟩ := Nat.mem_properDivisors.1 hd
    rw [wittTrunc_eq hw (Nat.pos_of_dvd_of_pos hdn hn) hlt]
  have hwn : wittTrunc c n n = 0 := by simp [wittTrunc]
  rw [hrest, hwn]
  push_cast
  ring

/-- Integrality of the first `N` exponential coefficients forces integrality of the first
`N` Witt coordinates. -/
theorem witt_isInt_of_le {c : ℕ → ℚ} (N : ℕ) (hc : ∀ j ≤ N, ∃ z : ℤ, expCoeff c j = z)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) : ∃ z : ℤ, witt c n = z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hw : ∀ d, 0 < d → d < n → ∃ z : ℤ, witt c d = z :=
      fun d hd hdn => ih d hdn hd (hdn.le.trans hnN)
    have hagree : ∀ k, 0 < k → k < n → c k = ghost (wittTrunc c n) k :=
      fun k hk hkn => (ghost_wittTrunc_of_lt hw hk hkn).symm
    have hdiff := expCoeff_sub_of_agree c (ghost (wittTrunc c n)) n hn hagree
    rw [ghost_wittTrunc_self hn hw] at hdiff
    have hn' : (n : ℚ) ≠ 0 := by positivity
    have hwitt : witt c n = expCoeff c n - expCoeff (ghost (wittTrunc c n)) n := by
      rw [hdiff]
      field_simp
      ring
    obtain ⟨z₁, hz₁⟩ := hc n hnN
    obtain ⟨z₂, hz₂⟩ := integralExp_ghost (wittTrunc c n) n
    exact ⟨z₁ - z₂, by rw [hwitt, hz₁, hz₂]; push_cast; ring⟩

/-- Integral exponential forces integral Witt coordinates. -/
theorem witt_isInt_of_integralExp {c : ℕ → ℚ} (hc : IntegralExp c) (n : ℕ) (hn : 0 < n) :
    ∃ z : ℤ, witt c n = z :=
  witt_isInt_of_le n (fun j _ => hc j) n hn le_rfl

/-- **Ghost characterization.** `exp (∑ c n x^n / n)` has integer coefficients iff
`c n = ∑_{d ∣ n} d * w d` for an integer sequence `w` (the necklace/Dold criterion). -/
theorem integralExp_iff_ghost (c : ℕ → ℚ) :
    IntegralExp c ↔ ∃ w : ℕ → ℤ, ∀ n, 0 < n → c n = ghost w n := by
  constructor
  · intro hc
    refine ⟨fun d => ⌊witt c d⌋, fun n hn => ?_⟩
    rw [← sum_divisors_witt c n hn, ghost]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn := Nat.dvd_of_mem_divisors hd
    obtain ⟨z, hz⟩ := witt_isInt_of_integralExp hc d (Nat.pos_of_dvd_of_pos hdn hn)
    simp [hz]
  · rintro ⟨w, hw⟩ n
    obtain ⟨z, hz⟩ := integralExp_ghost w n
    exact ⟨z, by rw [← hz]; exact expCoeff_congr _ _ n (fun k hk _ => hw k hk) n le_rfl⟩

/-- `[d₁ ∣ k] d₁ * [d₂ ∣ k] d₂ = gcd(d₁, d₂) * [lcm(d₁, d₂) ∣ k] lcm(d₁, d₂)`. -/
theorem basic_mul_basic (d₁ d₂ : ℕ) (k : ℕ) :
    basic d₁ k * basic d₂ k = (Nat.gcd d₁ d₂ : ℚ) * basic (Nat.lcm d₁ d₂) k := by
  simp only [basic]
  by_cases h₁ : d₁ ∣ k <;> by_cases h₂ : d₂ ∣ k
  · have hl : Nat.lcm d₁ d₂ ∣ k := Nat.lcm_dvd h₁ h₂
    rw [if_pos h₁, if_pos h₂, if_pos hl]
    exact_mod_cast (Nat.gcd_mul_lcm d₁ d₂).symm
  all_goals
    have hl : ¬ Nat.lcm d₁ d₂ ∣ k := fun hl =>
      by simp_all [Nat.lcm_dvd_iff]
    simp [h₁, h₂, hl]

/-- **Product closure.** Integrality of the exponential is preserved under pointwise
products of log-derivatives. -/
theorem IntegralExp.mul {c₁ c₂ : ℕ → ℚ} (h₁ : IntegralExp c₁) (h₂ : IntegralExp c₂) :
    IntegralExp (c₁ * c₂) := by
  obtain ⟨w₁, hw₁⟩ := (integralExp_iff_ghost c₁).1 h₁
  obtain ⟨w₂, hw₂⟩ := (integralExp_iff_ghost c₂).1 h₂
  intro n
  let s := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  obtain ⟨z, hz⟩ := integralExp_sum_basic s
    (fun p => w₁ p.1 * w₂ p.2 * (Nat.gcd p.1 p.2 : ℤ)) (fun p => Nat.lcm p.1 p.2)
    (fun p hp => by
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      exact Nat.lcm_pos (Finset.mem_Icc.1 hp1).1 (Finset.mem_Icc.1 hp2).1) n
  refine ⟨z, ?_⟩
  rw [← hz]
  refine expCoeff_congr _ _ n (fun k hk hkn => ?_) n le_rfl
  rw [Pi.mul_apply, hw₁ k hk, hw₂ k hk, ghost_eq_sum_basic w₁ n k hk hkn,
    ghost_eq_sum_basic w₂ n k hk hkn, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  linear_combination ((w₁ p.1 : ℚ) * w₂ p.2) * basic_mul_basic p.1 p.2 k

/-- Integrality of the exponential is preserved under pointwise natural powers. -/
theorem IntegralExp.pow {c : ℕ → ℚ} (hc : IntegralExp c) (k : ℕ) :
    IntegralExp (fun n => c n ^ k) := by
  induction k with
  | zero =>
    have h1 : (fun n => c n ^ 0) = basic 1 := by
      funext n
      simp [basic]
    rw [h1]
    exact integralExp_basic 1 one_pos
  | succ k ih =>
    have hs : (fun n => c n ^ (k + 1)) = (fun n => c n ^ k) * c := by
      funext n
      simp [pow_succ]
    rw [hs]
    exact ih.mul hc

/-- The candidate log-derivative at step `n` with trial root `m`: `pre k ^ 2` for `k < n`
and `m ^ 2` from `n` on (only the value at `n` matters for the `n`-th coefficient). -/
def cand (pre : ℕ → ℕ) (n m : ℕ) : ℕ → ℚ := fun k => if k < n then (pre k : ℚ) ^ 2 else (m : ℚ) ^ 2

/-- `m` is an admissible `n`-th root: it exceeds the previous root and makes the `n`-th
coefficient of `exp (∑ cand x^k / k)` an integer. -/
def Admissible (pre : ℕ → ℕ) (n m : ℕ) : Prop :=
  pre (n - 1) < m ∧ ∃ z : ℤ, expCoeff (cand pre n m) n = z

open Classical in
/-- **A177431**: `b 1 = 1`, and for `n ≥ 2`, `b n` is the least `m > b (n - 1)` such that
`exp (∑_{k < n} b(k)^2 x^k/k + m^2 x^n/n)` has an integer `x^n` coefficient; so
`A177430 n = b n ^ 2` is the least strictly increasing sequence of squares that is the
logarithmic derivative of an integer sequence. (`b 0 = 1` is a junk value; the junk value
`0` in the `else` branch is never taken, see `b_admissible`.) -/
noncomputable def b (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else
    if h : ∃ m, Admissible (fun k => if _hk : k < n then b k else 0) n m then Nat.find h else 0
termination_by n
decreasing_by all_goals omega

/-- `b 0 = b 1 = 1`. -/
theorem b_of_le_one {n : ℕ} (hn : n ≤ 1) : b n = 1 := by
  rw [b, if_pos hn]

/-- Admissibility at step `n` only depends on the prefix below `n`. -/
theorem admissible_congr {pre pre' : ℕ → ℕ} {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, pre k = pre' k) (m : ℕ) : Admissible pre n m ↔ Admissible pre' n m := by
  have hc : cand pre n m = cand pre' n m := by
    funext k
    by_cases hk : k < n
    · simp [cand, hk, h k hk]
    · simp [cand, hk]
  rw [Admissible, Admissible, hc, h (n - 1) (by omega)]

/-- For `n ≥ 2`, whenever an admissible root exists, `b n` is the least one. -/
theorem b_spec {n : ℕ} (hn : 2 ≤ n) (h : ∃ m, Admissible b n m) :
    Admissible b n (b n) ∧ ∀ m, Admissible b n m → b n ≤ m := by
  classical
  have hcongr : ∀ m, Admissible (fun k => if _hk : k < n then b k else 0) n m ↔
      Admissible b n m :=
    admissible_congr (by omega) (fun k hk => by simp [hk])
  have h' : ∃ m, Admissible (fun k => if _hk : k < n then b k else 0) n m := by
    simpa only [hcongr] using h
  have hb : b n = Nat.find h' := by
    rw [b, if_neg (by omega), dif_pos h']
  rw [hb]
  exact ⟨(hcongr _).1 (Nat.find_spec h'), fun m hm => Nat.find_min' h' ((hcongr m).2 hm)⟩

/-- A rational with denominator `≠ 1` is not an integer. -/
theorem not_exists_int_of_den {q : ℚ} (h : q.den ≠ 1) : ¬ ∃ z : ℤ, q = z := by
  rintro ⟨z, rfl⟩
  exact h (Rat.den_intCast z)

/-- Characterization used for the ground-truth values: `b n = m` as soon as `m` is
admissible and no smaller root is. -/
theorem b_eq_of {n m : ℕ} (hn : 2 ≤ n) (hm : Admissible b n m)
    (hlt : ∀ j < m, ¬ Admissible b n j) : b n = m := by
  obtain ⟨hadm, hmin⟩ := b_spec hn ⟨m, hm⟩
  have hle := hmin m hm
  by_contra hne
  exact hlt (b n) (lt_of_le_of_ne hle hne) hadm

/-- Ground truth: `A177431(1) = 1`. -/
theorem b_one : b 1 = 1 := b_of_le_one le_rfl

/-- Ground truth: `A177431(2) = 3`. -/
theorem b_two : b 2 = 3 := by
  refine b_eq_of le_rfl ⟨by simp [b_one], 5, ?_⟩ fun j hj => ?_
  · norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one]
  · rintro ⟨hj1, hj2⟩
    simp only [b_one, Nat.reduceSub] at hj1
    obtain rfl : j = 2 := by omega
    refine not_exists_int_of_den ?_ hj2
    norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one]

/-- Ground truth: `A177431(3) = 4`. -/
theorem b_three : b 3 = 4 := by
  refine b_eq_of (by norm_num) ⟨by simp [b_two], 10, ?_⟩ fun j hj => ?_
  · norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one, b_two]
  · rintro ⟨hj1, -⟩
    simp only [b_two, Nat.reduceSub] at hj1
    omega

/-- Ground truth: `A177431(4) = 5`. -/
theorem b_four : b 4 = 5 := by
  refine b_eq_of (by norm_num) ⟨by simp [b_three], 24, ?_⟩ fun j hj => ?_
  · norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one, b_two, b_three]
  · rintro ⟨hj1, -⟩
    simp only [b_three, Nat.reduceSub] at hj1
    omega

/-- Ground truth: `A177431(5) = 6`. -/
theorem b_five : b 5 = 6 := by
  refine b_eq_of (by norm_num) ⟨by simp [b_four], 51, ?_⟩ fun j hj => ?_
  · norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one, b_two, b_three,
      b_four]
  · rintro ⟨hj1, -⟩
    simp only [b_four, Nat.reduceSub] at hj1
    omega

/-- Ground truth: `A177431(6) = 12` (the roots `7, …, 11` are rejected). -/
theorem b_six : b 6 = 12 := by
  refine b_eq_of (by norm_num) ⟨by simp [b_five], 122, ?_⟩ fun j hj => ?_
  · norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one, b_two, b_three,
      b_four, b_five]
  · rintro ⟨hj1, hj2⟩
    simp only [b_five, Nat.reduceSub] at hj1
    refine not_exists_int_of_den ?_ hj2
    interval_cases j <;>
    · norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, cand, b_one, b_two, b_three,
        b_four, b_five]

/-- A log-derivative with integral exponential takes integer values at positive indices. -/
theorem exists_int_of_integralExp {c : ℕ → ℚ} (hc : IntegralExp c) {n : ℕ} (hn : 0 < n) :
    ∃ z : ℤ, c n = z := by
  obtain ⟨w, hw⟩ := (integralExp_iff_ghost c).1 hc
  refine ⟨∑ d ∈ n.divisors, (d : ℤ) * w d, ?_⟩
  rw [hw n hn, ghost]
  push_cast
  rfl

/-- The Dold congruence at `n = 4`: `4 ∣ c 4 - c 2`. -/
theorem dold_four {c : ℕ → ℚ} (hc : IntegralExp c) : ∃ z : ℤ, c 4 - c 2 = 4 * z := by
  obtain ⟨w, hw⟩ := (integralExp_iff_ghost c).1 hc
  refine ⟨w 4, ?_⟩
  have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
  have h2 : Nat.divisors 2 = {1, 2} := by decide
  rw [hw 4 (by norm_num), hw 2 (by norm_num), ghost, ghost, h4, h2]
  simp

/-- **Only-when direction.** If `exp (∑ b(n)^m x^n / n)` has integer coefficients for an
integer exponent `m`, then `m` is a nonnegative even integer. Only `b 2 = 3` and
`b 4 = 5` are used. -/
theorem nonneg_even_of_integralExp (m : ℤ) (h : IntegralExp (fun n => (b n : ℚ) ^ m)) :
    0 ≤ m ∧ Even m := by
  have hnonneg : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨z, hz⟩ := exists_int_of_integralExp h (n := 2) (by norm_num)
    simp only [b_two, Nat.cast_ofNat] at hz
    have hlt : (3 : ℚ) ^ m < 1 := zpow_lt_one_of_neg₀ (by norm_num) hneg
    have hpos : (0 : ℚ) < 3 ^ m := zpow_pos (by norm_num) m
    rw [hz] at hlt hpos
    have hlt' : z < 1 := by exact_mod_cast hlt
    have hpos' : 0 < z := by exact_mod_cast hpos
    omega
  refine ⟨hnonneg, ?_⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 2 * k + 1 := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j.toNat, by omega⟩
  obtain ⟨z, hz⟩ := dold_four h
  simp only [b_two, b_four, hk] at hz
  have hz' : (5 : ℤ) ^ (2 * k + 1) - 3 ^ (2 * k + 1) = 4 * z := by
    have hcast : ((5 : ℚ) ^ (2 * (k : ℤ) + 1) - 3 ^ (2 * (k : ℤ) + 1)) =
        (((5 : ℤ) ^ (2 * k + 1) - 3 ^ (2 * k + 1) : ℤ) : ℚ) := by
      push_cast
      rw [← zpow_natCast, ← zpow_natCast]
      push_cast
      ring_nf
    have := hz
    push_cast at this
    rw [hcast] at this
    exact_mod_cast this
  have hmod := congrArg (Int.cast : ℤ → ZMod 4) hz'
  push_cast at hmod
  rw [pow_succ, pow_succ, pow_mul, pow_mul] at hmod
  have h5 : (5 : ZMod 4) ^ 2 = 1 := by decide
  have h3 : (3 : ZMod 4) ^ 2 = 1 := by decide
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [h5, h3, h4, one_pow, one_mul, one_mul, zero_mul] at hmod
  revert hmod
  decide

/-- Chinese remainder step: a square residue modulo coprime `a` and `b` is a square
residue modulo `a * b`. -/
theorem exists_sq_dvd_mul {G : ℤ} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ∃ x : ℤ, (a : ℤ) ∣ x ^ 2 - G) (hb : ∃ x : ℤ, (b : ℤ) ∣ x ^ 2 - G) :
    ∃ x : ℤ, ((a * b : ℕ) : ℤ) ∣ x ^ 2 - G := by
  obtain ⟨xa, ta, hta⟩ := ha
  obtain ⟨xb, tb, htb⟩ := hb
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  let x : ℤ := xa * v * b + xb * u * a
  refine ⟨x, ?_⟩
  push_cast
  refine (Nat.isCoprime_iff_coprime.2 hab).mul_dvd ⟨u * (xb - xa) * (x + xa) + ta, ?_⟩
    ⟨v * (xa - xb) * (x + xb) + tb, ?_⟩
  · linear_combination (xa * (x + xa)) * huv + hta
  · linear_combination (xb * (x + xb)) * huv + htb

/-- A residue that is a square modulo every prime-power divisor of `n > 0` is a square
modulo `n`. -/
theorem exists_sq_dvd_of_primePow (G : ℤ) (n : ℕ) (hn : 0 < n)
    (h : ∀ q : ℕ, IsPrimePow q → q ∣ n → ∃ x : ℤ, (q : ℤ) ∣ x ^ 2 - G) :
    ∃ x : ℤ, (n : ℤ) ∣ x ^ 2 - G := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, by simp⟩
    · exact h (p ^ k) ⟨p, k, hp.prime, hk, rfl⟩ dvd_rfl
  | coprime a b ha hb hab iha ihb =>
    exact exists_sq_dvd_mul hab
      (iha (by omega) fun q hq hqa => h q hq (hqa.trans (dvd_mul_right a b)))
      (ihb (by omega) fun q hq hqb => h q hq (hqb.trans (dvd_mul_left b a)))

/-- A divisor of `n` that does not divide `n / p` is divisible by every power of `p`
dividing `n`. -/
theorem pow_dvd_of_not_dvd_div {p j n d : ℕ} (hp : p.Prime) (hpj : p ^ j ∣ n) (hdn : d ∣ n)
    (hnot : ¬ d ∣ n / p) : p ^ j ∣ d := by
  obtain ⟨e, rfl⟩ := hdn
  have hpe : ¬ p ∣ e := by
    rintro ⟨f, rfl⟩
    apply hnot
    refine ⟨f, ?_⟩
    rw [show d * (p * f) = (d * f) * p by ring, Nat.mul_div_cancel _ hp.pos]
  have hcop : Nat.Coprime (p ^ j) e := Nat.Coprime.pow_left j ((hp.coprime_iff_not_dvd).2 hpe)
  exact hcop.dvd_of_dvd_mul_right hpj

/-- Prime-power congruence for truncated ghost sums: modulo `q = p ^ j ∣ n`, the sum of
`d * w d` over the proper divisors of `n` agrees with the full ghost sum at `n / p`. -/
theorem primePow_dvd_properDivisors_sub (w : ℕ → ℤ) {n p j : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hj : 0 < j) (hpj : p ^ j ∣ n) :
    ((p ^ j : ℕ) : ℤ) ∣ (∑ d ∈ n.properDivisors, (d : ℤ) * w d) -
      ∑ d ∈ (n / p).divisors, (d : ℤ) * w d := by
  classical
  have hpn : p ∣ n := (dvd_pow_self p hj.ne').trans hpj
  have hsub : (n / p).divisors ⊆ n.properDivisors := by
    intro d hd
    obtain ⟨hdnp, -⟩ := Nat.mem_divisors.1 hd
    have hnp : n / p < n := Nat.div_lt_self hn hp.one_lt
    have hnp0 : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
    refine Nat.mem_properDivisors.2 ⟨hdnp.trans (Nat.div_dvd_of_dvd hpn), ?_⟩
    exact (Nat.le_of_dvd hnp0 hdnp).trans_lt hnp
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Finset.dvd_sum fun d hd => ?_
  obtain ⟨hdprop, hdnot⟩ := Finset.mem_sdiff.1 hd
  have hdn := (Nat.mem_properDivisors.1 hdprop).1
  have hnot : ¬ d ∣ n / p := fun hdvd =>
    hdnot (Nat.mem_divisors.2 ⟨hdvd, (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos).ne'⟩)
  exact (Int.natCast_dvd_natCast.2 (pow_dvd_of_not_dvd_div hp hpj hdn hnot)).mul_right _

/-- **A177430** as a rational sequence: `sq n = b n ^ 2`. -/
noncomputable def sq : ℕ → ℚ := fun n => (b n : ℚ) ^ 2

/-- Below `n`, the candidate sequence is `A177430`. -/
theorem cand_of_lt {n m k : ℕ} (hk : k < n) : cand b n m k = sq k := by
  simp [cand, sq, hk]

/-- **Existence step.** If the first `n - 1` coefficients of `exp (∑ sq k x^k / k)` are
integers, then an admissible `n`-th root exists: the required residue `c(n) mod n` is a
square modulo every prime power `p ^ j ∣ n` (it is `b (n / p) ^ 2` there), hence a square
modulo `n` by the Chinese remainder theorem. -/
theorem exists_admissible {n : ℕ} (hn : 2 ≤ n)
    (hprefix : ∀ j < n, ∃ z : ℤ, expCoeff sq j = z) : ∃ m, Admissible b n m := by
  have hn0 : 0 < n := by omega
  have hw : ∀ d, 0 < d → d < n → ∃ z : ℤ, witt sq d = z := fun d hd hdn =>
    witt_isInt_of_le (n - 1) (fun j hj => hprefix j (by omega)) d hd (by omega)
  set w := wittTrunc sq n with hw_def
  have hagree : ∀ k, 0 < k → k < n → ghost w k = sq k :=
    fun k hk hkn => ghost_wittTrunc_of_lt hw hk hkn
  let G : ℤ := ∑ d ∈ n.properDivisors, (d : ℤ) * w d
  have hGn : ghost w n = G := by
    have hwn : w n = 0 := by simp [hw_def, wittTrunc]
    rw [ghost, ← Nat.cons_self_properDivisors hn0.ne', Finset.sum_cons, hwn]
    simp [G]
  -- square residue modulo each prime power
  have hloc : ∀ q : ℕ, IsPrimePow q → q ∣ n → ∃ x : ℤ, (q : ℤ) ∣ x ^ 2 - G := by
    rintro q ⟨p, j, hp, hj, rfl⟩ hqn
    have hp' : p.Prime := Nat.prime_iff.2 hp
    have hpn : p ∣ n := (dvd_pow_self p hj.ne').trans hqn
    have hnp : n / p < n := Nat.div_lt_self hn0 hp'.one_lt
    have hnp0 : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp'.pos
    refine ⟨(b (n / p) : ℤ), ?_⟩
    have hsq : ((b (n / p) : ℤ) ^ 2 : ℤ) = ∑ d ∈ (n / p).divisors, (d : ℤ) * w d := by
      have h := hagree (n / p) hnp0 hnp
      rw [ghost, sq] at h
      exact_mod_cast h.symm
    rw [hsq, ← neg_sub]
    exact (primePow_dvd_properDivisors_sub w hn0 hp' hj hqn).neg_right
  obtain ⟨x, t, ht⟩ := exists_sq_dvd_of_primePow G n hn0 hloc
  obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ℤ) ^ 2 = x ^ 2 := ⟨x.natAbs, Int.natAbs_pow_two x⟩
  set s := b (n - 1) + 1 with hs
  refine ⟨y + n * s, ?_, ?_⟩
  · have : s ≤ n * s := Nat.le_mul_of_pos_left s hn0
    omega
  · have hcand : ∀ k, 0 < k → k < n → cand b n (y + n * s) k = ghost w k :=
      fun k _ hkn => by rw [cand_of_lt hkn, hagree k (by omega) hkn]
    have hdiff := expCoeff_sub_of_agree _ _ n hn0 hcand
    have hcn : cand b n (y + n * s) n = ((y + n * s : ℕ) : ℚ) ^ 2 := by
      simp [cand]
    rw [hcn, hGn] at hdiff
    have hkey : (((y + n * s : ℕ) : ℤ) ^ 2 - G) = n * ((s : ℤ) * (2 * y + n * s) + t) := by
      push_cast
      linear_combination hy + ht
    have hkeyQ : (((y + n * s : ℕ) : ℚ) ^ 2 - G) = n * ((s : ℚ) * (2 * y + n * s) + t) := by
      have h := congrArg (Int.cast : ℤ → ℚ) hkey
      push_cast at h ⊢
      exact h
    obtain ⟨z, hz⟩ := integralExp_ghost w n
    refine ⟨z + ((s : ℤ) * (2 * y + n * s) + t), ?_⟩
    have hn' : (n : ℚ) ≠ 0 := by positivity
    rw [hkeyQ, mul_div_cancel_left₀ _ hn', hz] at hdiff
    rw [eq_add_of_sub_eq' hdiff]
    push_cast
    ring

/-- **A177430 is a logarithmic derivative of an integer sequence**: every coefficient of
`exp (∑ b(n)^2 x^n / n)` is an integer. -/
theorem integralExp_sq : IntegralExp sq := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact ⟨1, by simp [expCoeff_zero]⟩
      · exact ⟨1, by simp [expCoeff_succ, expCoeff_zero, sq, b_one]⟩
    · obtain ⟨⟨-, z, hz⟩, -⟩ := b_spec hn (exists_admissible hn ih)
      refine ⟨z, ?_⟩
      rw [← hz]
      refine expCoeff_congr _ _ n (fun k hk hkn => ?_) n le_rfl
      rcases lt_or_eq_of_le hkn with hlt | rfl
      · exact (cand_of_lt hlt).symm
      · simp [cand, sq]

/-- The junk branch of `b` is never taken: for every `n ≥ 2`, `b n` is the least admissible
root. -/
theorem b_admissible {n : ℕ} (hn : 2 ≤ n) :
    Admissible b n (b n) ∧ ∀ m, Admissible b n m → b n ≤ m :=
  b_spec hn (exists_admissible hn fun j _ => integralExp_sq j)

/-- **If direction.** For every nonnegative even exponent `m`, `exp (∑ b(n)^m x^n / n)` has
integer coefficients. -/
theorem integralExp_of_nonneg_even (m : ℤ) (hm : 0 ≤ m) (he : Even m) :
    IntegralExp (fun n => (b n : ℚ) ^ m) := by
  obtain ⟨k, hk⟩ := he
  have hfun : (fun n => (b n : ℚ) ^ m) = fun n => sq n ^ k.toNat := by
    funext n
    have hm' : m = ((2 * k.toNat : ℕ) : ℤ) := by omega
    rw [hm', zpow_natCast, pow_mul, sq]
  rw [hfun]
  exact integralExp_sq.pow k.toNat

/-- **Hanna's conjecture (A177430 / A177431), integer exponents.** With `b = A177431`,
`exp (∑_{n ≥ 1} b(n)^m x^n / n)` has integer coefficients if and only if `m` is a
nonnegative even integer. -/
theorem conjecture (m : ℤ) : IntegralExp (fun n => (b n : ℚ) ^ m) ↔ 0 ≤ m ∧ Even m :=
  ⟨nonneg_even_of_integralExp m, fun h => integralExp_of_nonneg_even m h.1 h.2⟩

/-! ## Ground truth -/

/-- `exp (∑ x^n / n) = 1 / (1 - x)`: all coefficients `1` (checked at `n = 3`). -/
example : expCoeff (fun _ => 1) 3 = 1 := by
  norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ]

/-- First terms of A177430 = `b ^ 2`: `1, 9, 16, 25, 36, 144`. -/
example : (sq 1, sq 2, sq 3, sq 4, sq 5, sq 6) = (1, 9, 16, 25, 36, 144) := by
  norm_num [sq, b_one, b_two, b_three, b_four, b_five, b_six]

/-- First terms of A177432 = `exp (∑ A177430(n) x^n / n)`: `1, 1, 5, 10, 24, 51, 122`. -/
example : (expCoeff sq 0, expCoeff sq 1, expCoeff sq 2, expCoeff sq 3, expCoeff sq 4,
    expCoeff sq 5, expCoeff sq 6) = (1, 1, 5, 10, 24, 51, 122) := by
  norm_num [expCoeff_succ, expCoeff_zero, Finset.sum_range_succ, sq, b_one, b_two, b_three,
    b_four, b_five, b_six]

/-- Non-vacuity of the integrality predicate: `m = 1` fails (first at `n = 4`). -/
example : ¬ IntegralExp (fun n => (b n : ℚ) ^ (1 : ℤ)) := fun h =>
  absurd (nonneg_even_of_integralExp 1 h).2 (by decide)

end Candidates.A177430HannaSquareRoots
