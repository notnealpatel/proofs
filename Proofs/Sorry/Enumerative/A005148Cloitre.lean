/-
# A005148 — Cloitre: `v_2(a(k)) = 3 (s_2(k) - 1)` for the Shanks–Beukers sequence

## OEIS source (retrieved with `oeis show A005148`, 2026-10-21)

```
NAME:     Sequence of coefficients arising in connection with a rapidly
          converging series for Pi.
TERMS:    0,1,47,2488,138799,7976456,467232200,27736348480,1662803271215,...
FORMULA:  a(n) = (1/24) * coefficient of x^n in
          Product_{k>=1} (1+x^(2k-1))^(24n).
FORMULA:  A076657(n) = Sum_{i=0..n} binomial(2*n-2*i, n-i)^3 a(i)
          = (1/24)*binomial(2*n, n)*(16^n-binomial(2*n, n)^2)
          (Shanks and Beukers). - _Ralf Stephan_, Oct 24 2002
COMMENT (the conjecture):
  Conjecture: The following 2 definitions give the same sequence: (1) numbers
  k such that 8^m is the highest power of 2 dividing a(k), and (2) numbers k
  such that k has exactly (m+1) 1's in its binary representation. A018900 is
  the special case m=1. - _Benoit Cloitre_, Jun 22 2002, edited by
  _Hugo Pfoertner_, Aug 21 2021
```

Equivalent valuation form used here: for every `k ≥ 1`,
`v_2(a(k)) = 3 * (s_2(k) - 1)`, where `s_2` is the binary digit sum.

## Status

The case `m = 0` is a theorem: M. Newman and D. Shanks, "On a sequence
arising in series for π", Math. Comp. 42 (1984) 199–217, Theorem 3 (their
statement (14)), prove that `a_n` is odd iff `n` is a power of `2`, i.e.
`v_2(a(k)) = 0` iff `s_2(k) = 1`.  The same paper's statement (13) proves
that `24 · a_n` is the coefficient of `x^n` in `∏_{k≥1} (1+x^(2k-1))^(24n)`,
the product definition used here.  For `m ≥ 1` the entry carries no
resolution and the triage web search found no proof of the general law (no
match is not evidence of novelty).

The Shanks–Beukers convolution identity used below is not an open
obligation: it is known in the literature (see `shanksBeukers_identity`),
but not yet formalized here.  Given that identity, the sorry-free
`cloitre_of_shanksBeukers` below yields the full law, so the informal status
of the conjecture is: proved modulo a cited, unformalized identity.
Numerically: the product definition satisfies the valuation law and the
Shanks–Beukers convolution for all `1 ≤ n ≤ 430` (Python, this session;
triage checked the valuation law to `n ≤ 400`).

## What this module proves

* `exists_odd_of_conv` (sorry-free): **any** integer sequence `h` with
  `∑_{i=1}^{n} C(2n-2i, n-i)^3 h(i) = C(2n,n)(16^n - C(2n,n)^2)` for all
  `n ≥ 1` satisfies `h(n) = 2^(3 s_2(n)) * (odd)` for `n ≥ 1`.  The proof is a
  2-adic strong induction (Legendre/Kummer in digit-sum form, and the parity
  of `∑_{0<i<n} C(n,i) = 2^n - 2`).
* `cloitre_of_shanksBeukers` (sorry-free): Cloitre's valuation law for the
  product-defined `a`, *conditional on* the Shanks–Beukers identity, which is
  an explicit hypothesis.
* `cloitre_conjecture`: the unconditional conjecture, whose only gap is the
  single `sorry` in `shanksBeukers_identity` (the entry's FORMULA line, cited
  there to Shanks and Beukers, for the product definition).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A005148Cloitre

open Polynomial Finset

/-! ## Definition layer -/

/-- The binary digit sum `s_2(n)` (number of `1`s in the binary expansion of `n`). -/
def digitSum2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

example : digitSum2 0 = 0 := by decide
example : digitSum2 7 = 3 := by decide
example : digitSum2 12 = 2 := by decide

/-- `coeffProd n` is the coefficient of `x^n` in `∏_{k ≥ 1} (1 + x^(2k-1))^(24n)`.
The infinite product is truncated to the factors `k = 1, …, n` (exponents
`1, 3, …, 2n-1`); the omitted factors are `≡ 1 mod x^(n+1)` and do not change
the coefficient of `x^n`, see `coeff_prod_range_pow_stable`. -/
noncomputable def coeffProd (n : ℕ) : ℤ :=
  ((∏ k ∈ Finset.range n, (1 + X ^ (2 * k + 1) : ℤ[X])) ^ (24 * n)).coeff n

/-- The OEIS sequence A005148: `a(0) = 0` (the entry's offset-0 term) and
`a(n) = (1/24) [x^n] ∏_{k ≥ 1} (1 + x^(2k-1))^(24n)` for `n ≥ 1`.  It is valued in
`ℚ` so that the factor `1/24` is literal; no integrality is presupposed. -/
noncomputable def a (n : ℕ) : ℚ := if n = 0 then 0 else (coeffProd n : ℚ) / 24

/-- The right-hand side of the Shanks–Beukers identity multiplied by `24`:
`C(2n,n) (16^n - C(2n,n)^2)`. -/
def shanksBeukersRhs (n : ℕ) : ℤ :=
  (n.centralBinom : ℤ) * (16 ^ n - (n.centralBinom : ℤ) ^ 2)

example : shanksBeukersRhs 0 = 0 := by decide
example : shanksBeukersRhs 1 = 24 := by decide
example : shanksBeukersRhs 2 = 24 * 47 + 24 * 8 := by decide

/-- Coefficients of `(1 + x^d)^m`: `[x^j] (1 + x^d)^m = C(m, j/d)` if `d ∣ j`, else `0`. -/
theorem coeff_one_add_X_pow_pow {d : ℕ} (hd : 0 < d) (m j : ℕ) :
    ((1 + X ^ d : ℤ[X]) ^ m).coeff j = if d ∣ j then ((m.choose (j / d) : ℕ) : ℤ) else 0 := by
  have hexp : (1 + X ^ d : ℤ[X]) ^ m = expand ℤ d ((1 + X) ^ m) := by
    simp [map_pow, map_add, expand_X]
  rw [hexp, coeff_expand hd, coeff_one_add_X_pow]

/-! Ground truth against the OEIS DATA line `0, 1, 47, 2488, …`. -/

example : coeffProd 1 = 24 * 1 := by
  simp [coeffProd, coeff_one_add_X_pow]

example : coeffProd 2 = 24 * 47 := by
  simp only [coeffProd, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, mul_pow,
    coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]
  simp only [Nat.reduceAdd, zero_add, map_singleton, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map_apply, Nat.succ_eq_add_one, Function.Embedding.refl_apply,
    cons_eq_insert, map_insert, mul_zero, pow_one, Nat.reduceMul, coeff_one_add_X_pow, mul_one,
    Nat.ofNat_pos, coeff_one_add_X_pow_pow, mul_ite, mem_insert, Prod.mk.injEq, zero_ne_one,
    OfNat.ofNat_ne_one, and_self, mem_singleton, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, or_self,
    not_false_eq_true, sum_insert, Nat.reduceDvd, ↓reduceIte, OfNat.one_ne_ofNat, one_ne_zero,
    Nat.dvd_one, sum_singleton, dvd_zero, Nat.zero_div, Nat.choose_zero_right, Nat.cast_one,
    Int.reduceMul]
  decide

example : coeffProd 3 = 24 * 2488 := by
  simp only [coeffProd, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, mul_pow,
    coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero]
  simp only [Nat.reduceAdd, zero_add, map_singleton, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map_apply, Nat.succ_eq_add_one, Function.Embedding.refl_apply,
    cons_eq_insert, map_insert, mul_zero, pow_one, Nat.reduceMul, coeff_one_add_X_pow, mul_one,
    Nat.ofNat_pos, coeff_one_add_X_pow_pow, mul_ite, mem_insert, Prod.mk.injEq, zero_ne_one,
    Nat.succ_ne_self, and_self, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, mem_singleton,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, sum_insert, Nat.reduceDvd, ↓reduceIte,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, one_ne_zero, Nat.dvd_one, sum_singleton, dvd_zero,
    Nat.zero_div, Nat.choose_zero_right, Nat.cast_one, Int.reduceMul]
  decide

example : a 0 = 0 := by simp [a]

example : a 1 = 1 := by
  simp [a, coeffProd, coeff_one_add_X_pow]

/-! ## Truncation fidelity -/

/-- The factors `1 + x^(2k+1)` with `n ≤ k` are all `≡ 1 mod x^(n+1)`. -/
theorem X_pow_dvd_prod_Ico_sub_one (n N : ℕ) :
    (X : ℤ[X]) ^ (n + 1) ∣ (∏ k ∈ Ico n N, (1 + X ^ (2 * k + 1) : ℤ[X])) - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases le_or_gt n N with hnN | hNn
    · rw [Finset.prod_Ico_succ_top hnN]
      set A := ∏ k ∈ Ico n N, (1 + X ^ (2 * k + 1) : ℤ[X])
      have hB : (X : ℤ[X]) ^ (n + 1) ∣ X ^ (2 * N + 1) := pow_dvd_pow X (by omega)
      have e : A * (1 + X ^ (2 * N + 1)) - 1 = (A - 1) + A * X ^ (2 * N + 1) := by ring
      rw [e]
      exact dvd_add ih (dvd_mul_of_dvd_right hB A)
    · rw [Finset.Ico_eq_empty_of_le (by omega)]
      simp

/-- Truncation stability: for `n ≤ N` and any exponent `m`, the coefficient of
`x^n` in `(∏_{k<N} (1 + x^(2k+1)))^m` does not depend on `N`.  Hence `coeffProd n`
is the coefficient of `x^n` in the power of the infinite product. -/
theorem coeff_prod_range_pow_stable {n N : ℕ} (hN : n ≤ N) (m : ℕ) :
    ((∏ k ∈ range N, (1 + X ^ (2 * k + 1) : ℤ[X])) ^ m).coeff n =
      ((∏ k ∈ range n, (1 + X ^ (2 * k + 1) : ℤ[X])) ^ m).coeff n := by
  rw [← Finset.prod_range_mul_prod_Ico _ hN]
  set P := ∏ k ∈ range n, (1 + X ^ (2 * k + 1) : ℤ[X])
  set Q := ∏ k ∈ Ico n N, (1 + X ^ (2 * k + 1) : ℤ[X])
  have hQ : (X : ℤ[X]) ^ (n + 1) ∣ Q ^ m - 1 := by
    have h1 := sub_dvd_pow_sub_pow Q 1 m
    rw [one_pow] at h1
    exact (X_pow_dvd_prod_Ico_sub_one n N).trans h1
  have hz : (P ^ m * (Q ^ m - 1)).coeff n = 0 :=
    (Polynomial.X_pow_dvd_iff.mp (dvd_mul_of_dvd_right hQ _)) n (by omega)
  have e : (P * Q) ^ m = P ^ m + P ^ m * (Q ^ m - 1) := by ring
  rw [e, coeff_add, hz, add_zero]

/-! ## Arithmetic helpers (Legendre and Kummer in digit-sum form) -/

/-- Every nonzero `n` is `2^(v_2 n)` times an odd number. -/
theorem two_pow_padicValNat_mul_odd {n : ℕ} (hn : n ≠ 0) :
    ∃ w : ℕ, Odd w ∧ n = 2 ^ padicValNat 2 n * w := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hv : padicValNat 2 m = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hm)
  refine ⟨m, hm, ?_⟩
  rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow, hv, add_zero]

/-- Legendre at `p = 2`: `v_2(n!) + s_2(n) = n`. -/
theorem padicValNat_factorial_add_digitSum2 (n : ℕ) :
    padicValNat 2 n.factorial + digitSum2 n = n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := Nat.digit_sum_le 2 n
  simp only [Nat.add_one_sub_one, one_mul] at h
  unfold digitSum2
  omega

/-- Kummer at `p = 2`: `s_2(i) + s_2(n-i) = s_2(n) + v_2(C(n,i))` for `i ≤ n`. -/
theorem digitSum2_add_digitSum2 {n i : ℕ} (hi : i ≤ n) :
    digitSum2 i + digitSum2 (n - i) = digitSum2 n + padicValNat 2 (n.choose i) := by
  have hfac := Nat.choose_mul_factorial_mul_factorial hi
  have hc : n.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  have hv := congrArg (padicValNat 2) hfac
  rw [padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul hc (by positivity)] at hv
  have h1 := padicValNat_factorial_add_digitSum2 n
  have h2 := padicValNat_factorial_add_digitSum2 i
  have h3 := padicValNat_factorial_add_digitSum2 (n - i)
  omega

/-- Doubling does not change the binary digit sum. -/
theorem digitSum2_two_mul (k : ℕ) : digitSum2 (2 * k) = digitSum2 k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold digitSum2
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

/-- `v_2(C(2k,k)) = s_2(k)`. -/
theorem padicValNat_centralBinom (k : ℕ) : padicValNat 2 k.centralBinom = digitSum2 k := by
  have h := digitSum2_add_digitSum2 (n := 2 * k) (i := k) (by omega)
  rw [show 2 * k - k = k by omega, digitSum2_two_mul, Nat.centralBinom_eq_two_mul_choose] at *
  omega

/-- `C(2k,k) = 2^(s_2 k) * (odd)`. -/
theorem centralBinom_eq_two_pow_mul_odd (k : ℕ) :
    ∃ w : ℕ, Odd w ∧ k.centralBinom = 2 ^ digitSum2 k * w := by
  obtain ⟨w, hw, h⟩ := two_pow_padicValNat_mul_odd (Nat.centralBinom_ne_zero k)
  exact ⟨w, hw, by rw [← padicValNat_centralBinom]; exact h⟩

/-- For `n ≥ 1`, `C(2n,n)(16^n - C(2n,n)^2) = 2^(3 s_2 n) * (odd)`. -/
theorem shanksBeukersRhs_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ u : ℤ, Odd u ∧ shanksBeukersRhs n = 2 ^ (3 * digitSum2 n) * u := by
  obtain ⟨w, hw, hcb⟩ := centralBinom_eq_two_pow_mul_odd n
  have hle : digitSum2 n ≤ n := Nat.digit_sum_le 2 n
  set s := digitSum2 n with hs
  have hw' : Odd (w : ℤ) := by exact_mod_cast hw
  refine ⟨w * (2 ^ (4 * n - 2 * s) - (w : ℤ) ^ 2), ?_, ?_⟩
  · have h1 : Even ((2 : ℤ) ^ (4 * n - 2 * s)) := (Int.even_pow).mpr ⟨even_two, by omega⟩
    exact hw'.mul (h1.sub_odd (hw'.pow))
  · have h16 : (16 : ℤ) ^ n = 2 ^ (2 * s) * 2 ^ (4 * n - 2 * s) := by
      rw [← pow_add, show 2 * s + (4 * n - 2 * s) = 4 * n by omega, pow_mul]; norm_num
    rw [shanksBeukersRhs, hcb]
    push_cast
    rw [h16]
    ring

/-- Parity of a sum is determined termwise by parities. -/
theorem even_sum_iff_of_forall {s : Finset ℕ} {f g : ℕ → ℤ}
    (h : ∀ i ∈ s, (Even (f i) ↔ Even (g i))) :
    (Even (∑ i ∈ s, f i) ↔ Even (∑ i ∈ s, g i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Int.even_add, Int.even_add,
      h a (Finset.mem_insert_self a s), ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

/-- `∑_{0<i<n} C(n,i) + 2 = 2^n` for `n ≥ 1`. -/
theorem sum_Ico_choose_add_two {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Ico 1 n, ((n.choose i : ℕ) : ℤ) + 2 = 2 ^ n := by
  have h := Nat.sum_range_choose n
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.sum_Ico_succ_top hn] at h
  simp only [Nat.choose_zero_right, Nat.choose_self] at h
  have h' : ((1 + (∑ i ∈ Ico 1 n, n.choose i + 1) : ℕ) : ℤ) = ((2 ^ n : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

/-! ## The load-bearing 2-adic induction -/

/-- **Valuation law for any solution of the Shanks–Beukers convolution.**
If `h : ℕ → ℤ` satisfies `∑_{i=1}^{n} C(2(n-i), n-i)^3 h(i) = C(2n,n)(16^n - C(2n,n)^2)`
for every `n ≥ 1`, then `h(n) = 2^(3 s_2(n)) * u` with `u` odd for every `n ≥ 1`.

Proof: strong induction.  Each term `C(2(n-i),n-i)^3 h(i)` with `0 < i < n` equals
`2^(3 s_2 n) * t_i` where `t_i ≡ C(n,i) mod 2` (Kummer), and
`∑_{0<i<n} C(n,i) = 2^n - 2` is even; the right side is `2^(3 s_2 n) * (odd)`. -/
theorem exists_odd_of_conv (h : ℕ → ℤ)
    (hconv : ∀ n, 1 ≤ n →
      ∑ i ∈ Icc 1 n, ((n - i).centralBinom : ℤ) ^ 3 * h i = shanksBeukersRhs n) :
    ∀ n, 1 ≤ n → ∃ u : ℤ, Odd u ∧ h n = 2 ^ (3 * digitSum2 n) * u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  set s := digitSum2 n with hs
  have hrec : h n = shanksBeukersRhs n - ∑ i ∈ Ico 1 n, ((n - i).centralBinom : ℤ) ^ 3 * h i := by
    have hc := hconv n hn
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hn] at hc
    simp only [Nat.sub_self, Nat.centralBinom_zero, Nat.cast_one, one_pow, one_mul] at hc
    linarith
  have key : ∀ i ∈ Ico 1 n, ∃ t : ℤ, ((n - i).centralBinom : ℤ) ^ 3 * h i = 2 ^ (3 * s) * t ∧
      (Even t ↔ Even ((n.choose i : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨u, hu, hhi⟩ := ih i hi.2 hi.1
    obtain ⟨w, hw, hcb⟩ := centralBinom_eq_two_pow_mul_odd (n - i)
    have hsum := digitSum2_add_digitSum2 (n := n) (i := i) hi.2.le
    set v := padicValNat 2 (n.choose i) with hv
    have hw' : Odd (w : ℤ) := by exact_mod_cast hw
    refine ⟨2 ^ (3 * v) * (w : ℤ) ^ 3 * u, ?_, ?_⟩
    · rw [hhi, hcb]
      push_cast
      have e : (2 : ℤ) ^ (digitSum2 (n - i) * 3) * 2 ^ (3 * digitSum2 i) =
          2 ^ (3 * s) * 2 ^ (3 * v) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [mul_pow, ← pow_mul]
      linear_combination ((w : ℤ) ^ 3 * u) * e
    · have hc0 : n.choose i ≠ 0 := (Nat.choose_pos hi.2.le).ne'
      rw [Int.even_coe_nat]
      rcases Nat.eq_zero_or_pos v with hv0 | hvpos
      · have hodd : Odd (2 ^ (3 * v) * (w : ℤ) ^ 3 * u) := by
          rw [hv0]; simpa using hw'.pow.mul hu
        have hnd : ¬ 2 ∣ n.choose i := fun hd =>
          absurd (one_le_padicValNat_of_dvd hc0 hd) (by omega)
        exact iff_of_false (Int.not_even_iff_odd.mpr hodd) (by rwa [even_iff_two_dvd])
      · have hev : Even (2 ^ (3 * v) * (w : ℤ) ^ 3 * u) :=
          Even.mul_right (Even.mul_right ((Int.even_pow).mpr ⟨even_two, by omega⟩) _) _
        have hd : 2 ∣ n.choose i := dvd_of_one_le_padicValNat hvpos
        exact iff_of_true hev (even_iff_two_dvd.mpr hd)
  choose! t ht using key
  have hsumt : ∑ i ∈ Ico 1 n, ((n - i).centralBinom : ℤ) ^ 3 * h i =
      2 ^ (3 * s) * ∑ i ∈ Ico 1 n, t i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => (ht i hi).1
  have hevt : Even (∑ i ∈ Ico 1 n, t i) := by
    rw [even_sum_iff_of_forall fun i hi => (ht i hi).2]
    have hc := sum_Ico_choose_add_two hn
    have h2n : Even ((2 : ℤ) ^ n) := (Int.even_pow).mpr ⟨even_two, by omega⟩
    rw [← hc, Int.even_add] at h2n
    exact h2n.mpr even_two
  obtain ⟨uF, huF, hF⟩ := shanksBeukersRhs_eq hn
  refine ⟨uF - ∑ i ∈ Ico 1 n, t i, huF.sub_even hevt, ?_⟩
  rw [hrec, hsumt, hF]
  ring

/-! ### Non-vacuity of the convolution hypothesis -/

/-- The unique solution of the Shanks–Beukers convolution, by strong recursion:
`g(n) = C(2n,n)(16^n - C(2n,n)^2) - ∑_{0<i<n} C(2(n-i),n-i)^3 g(i)`. -/
def convSeq (n : ℕ) : ℤ :=
  shanksBeukersRhs n -
    ∑ i ∈ (Finset.Ico 1 n).attach, ((n - (i : ℕ)).centralBinom : ℤ) ^ 3 * convSeq i
termination_by n
decreasing_by exact (Finset.mem_Ico.mp i.2).2

/-- `convSeq` satisfies the convolution hypothesis of `exists_odd_of_conv`, so that
hypothesis is satisfiable. -/
theorem convSeq_conv (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Icc 1 n, ((n - i).centralBinom : ℤ) ^ 3 * convSeq i = shanksBeukersRhs n := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hn]
  simp only [Nat.sub_self, Nat.centralBinom_zero, Nat.cast_one, one_pow, one_mul]
  conv_lhs => rw [convSeq]
  rw [Finset.sum_attach (Finset.Ico 1 n) (fun i => ((n - i).centralBinom : ℤ) ^ 3 * convSeq i)]
  ring

example : ∀ n, 1 ≤ n → ∃ u : ℤ, Odd u ∧ convSeq n = 2 ^ (3 * digitSum2 n) * u :=
  exists_odd_of_conv convSeq convSeq_conv

/-! ## From the integer law to the rational valuation of `a` -/

/-- `v_2((2^e u) / 24) = e - 3` for odd `u`. -/
theorem padicValRat_two_pow_mul_odd_div_24 {e : ℕ} {u : ℤ} (hu : Odd u) :
    padicValRat 2 (((2 : ℤ) ^ e * u : ℤ) / 24 : ℚ) = (e : ℤ) - 3 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hpu : padicValRat 2 (u : ℚ) = 0 := by
    rw [padicValRat.of_int]
    have hnd : ¬ ((2 : ℕ) : ℤ) ∣ u := by
      rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]; exact hu
    simp [padicValInt.eq_zero_of_not_dvd hnd]
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    exact_mod_cast padicValRat.self (p := 2) (by norm_num)
  have h3 : padicValRat 2 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  have h24 : padicValRat 2 (24 : ℚ) = 3 := by
    rw [show (24 : ℚ) = 2 ^ 3 * 3 by norm_num, padicValRat.mul (by norm_num) (by norm_num),
      padicValRat.pow (2 : ℚ), h2, h3]
    norm_num
  push_cast
  rw [padicValRat.div (by positivity) (by norm_num),
    padicValRat.mul (by positivity) (by exact_mod_cast hu0),
    padicValRat.pow (2 : ℚ), h2, hpu, h24]
  ring

/-- **Cloitre's law, conditional on the Shanks–Beukers identity.**  If
`∑_{i=1}^{n} C(2(n-i),n-i)^3 · 24 a(i) = C(2n,n)(16^n - C(2n,n)^2)` for all `n ≥ 1`
(the entry's FORMULA line times `24`), then `v_2(a(k)) = 3 (s_2(k) - 1)` for all
`k ≥ 1`.  The identity is an explicit hypothesis here. -/
theorem cloitre_of_shanksBeukers
    (hSB : ∀ n, 1 ≤ n →
      ∑ i ∈ Icc 1 n, ((n - i).centralBinom : ℤ) ^ 3 * coeffProd i = shanksBeukersRhs n)
    (k : ℕ) (hk : 1 ≤ k) :
    padicValRat 2 (a k) = 3 * ((digitSum2 k : ℤ) - 1) := by
  obtain ⟨u, hu, hC⟩ := exists_odd_of_conv coeffProd hSB k hk
  have ha : a k = ((((2 : ℤ) ^ (3 * digitSum2 k) * u : ℤ)) / 24 : ℚ) := by
    rw [a, if_neg (by omega), hC]
  rw [ha, padicValRat_two_pow_mul_odd_div_24 hu]
  push_cast
  ring

/-! ## The remaining bridge and the conjecture -/

/-- **Shanks–Beukers identity** (OEIS A005148 FORMULA, attributed to Shanks and
Beukers, entered by Ralf Stephan, Oct 24 2002), multiplied by `24`:
for `n ≥ 1`, `∑_{i=1}^{n} C(2n-2i, n-i)^3 [x^i] ∏_k (1+x^(2k-1))^(24 i)
= C(2n,n)(16^n - C(2n,n)^2)`.

Status: known in the literature, not yet formalized.  This is the single
`sorry` of the module, and it is not an open problem.  The entry cites it to
F. Beukers (letter to D. Shanks, 13 March 1984) and to D. Shanks, *Solved and
Unsolved Problems in Number Theory*, pp. 255–257 and 276.  It also follows
from J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Exercise 6(a)(i):
`∑ a_n t^n = ((π/2K)^2 / (1 - 2k^2) - 1) / 24` with `t = (k k'/4)^2`, together
with Clausen's formula `∑ C(2n,n)^3 t^n = (2K/π)^2` and
`1 - 64 t = (1 - 2k^2)^2`: multiplying, `(∑ C(2n,n)^3 t^n)(∑ a_n t^n) =
((1 - 64t)^(-1/2) - ∑ C(2n,n)^3 t^n) / 24`, and `(1 - 64t)^(-1/2) =
∑ C(2n,n) 16^n t^n`; comparing coefficients of `t^n` gives the identity.  The
identification of these `a_n` with the product coefficients is Newman–Shanks,
Math. Comp. 42 (1984), statement (13).  Formalizing this needs the elliptic
integral `K`, Clausen's formula and the Borweins' theta-function evaluation,
none of which this module provides.  Checked numerically for `n ≤ 430`. -/
theorem shanksBeukers_identity (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Icc 1 n, ((n - i).centralBinom : ℤ) ^ 3 * coeffProd i = shanksBeukersRhs n := by
  sorry

/-- **Cloitre's conjecture (OEIS A005148, Benoit Cloitre, Jun 22 2002; edited by
Hugo Pfoertner, Aug 21 2021)**, valuation form: for every `k ≥ 1`,
`v_2(a(k)) = 3 (s_2(k) - 1)`, where `a(k) = (1/24) [x^k] ∏_{j≥1} (1+x^(2j-1))^(24k)`
and `s_2` is the binary digit sum.  Depends only on `shanksBeukers_identity`. -/
theorem cloitre_conjecture (k : ℕ) (hk : 1 ≤ k) :
    padicValRat 2 (a k) = 3 * ((digitSum2 k : ℤ) - 1) :=
  cloitre_of_shanksBeukers shanksBeukers_identity k hk

/-- **Cloitre's conjecture, as worded in the entry**: for `k ≥ 1` and `m ≥ 0`,
`8^m` is the highest power of `2` dividing `a(k)` (that is, `v_2(a(k)) = 3m`)
iff `k` has exactly `m + 1` ones in binary. -/
theorem cloitre_conjecture_iff (k m : ℕ) (hk : 1 ≤ k) :
    padicValRat 2 (a k) = 3 * (m : ℤ) ↔ digitSum2 k = m + 1 := by
  rw [cloitre_conjecture k hk]
  omega

end Candidates.A005148Cloitre
