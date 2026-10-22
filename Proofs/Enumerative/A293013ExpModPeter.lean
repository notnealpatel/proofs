/-
# A congruence for factorial-scaled exponential coefficients (A293013)

Source: Peter Bala's OEIS A293013 comment (Mar 12 2023).
For `entry(n)=n! [x^n] exp(x/(1-x)^n)`, the difference
`entry(n+k)-entry(n)` is an integer multiple of `k` for all natural `n,k`.
The degenerate case `k=0` is included trivially.
The coefficient is identified with the natural sum
`Σ_{i≤n} C(n,i) (n(n-i))^{(i)}`. Vandermonde and rising-factorial
congruences then give the result.
-/
import Mathlib

set_option autoImplicit false

open Finset PowerSeries
open scoped Nat

namespace Candidates.A293013ExpModPeter

/-! ## The entry's definition: `n! [x^n] exp(x/(1-x)^n)` over `ℚ` -/

/-- The inner series `x/(1-x)^n` in `ℚ⟦X⟧`; the inverse is the power-series
inverse, which is genuine because `(1-x)^n` has constant coefficient `1`. -/
noncomputable def innerSeries (n : ℕ) : ℚ⟦X⟧ := X * ((1 - X) ^ n)⁻¹

/-- The series `exp(x/(1-x)^n)`, the substitution of `x/(1-x)^n` into the
exponential series. -/
noncomputable def egf (n : ℕ) : ℚ⟦X⟧ := (exp ℚ).subst (innerSeries n)

/-- A293013 as the entry defines it: `a(n) = n! [x^n] exp(x/(1-x)^n)`.  At
`n = 0` this is `[x^0] exp(x) = 1`, matching the entry's `a(0) = 1`. -/
noncomputable def entry (n : ℕ) : ℚ := (n ! : ℚ) * coeff n (egf n)

/-! ## Closed form -/

/-- Closed form of A293013: `a(n) = ∑_{i=0}^{n} C(n,i) · (n(n-i))^{(i)}`,
with `m^{(i)} = m(m+1)⋯(m+i-1)` the rising factorial (`Nat.ascFactorial`).
`entry_eq_a` proves that it equals the entry's definition `entry`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ range (n + 1), n.choose i * (n * (n - i)).ascFactorial i

/-- The closed form reproduces the first eight listed terms. -/
example : (List.range 8).map a = [1, 1, 5, 55, 961, 24101, 818821, 36053515] := by decide

/-! ## Fidelity bridge: the entry's series equals the closed form -/

/-- In `ℚ⟦X⟧`, the inverse of `(1-X)^m` is Mathlib's `invOneSubPow ℚ m`. -/
theorem inv_one_sub_pow_eq (m : ℕ) : (((1 : ℚ⟦X⟧) - X) ^ m)⁻¹ = (invOneSubPow ℚ m).val := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp), ← invOneSubPow_inv_eq_one_sub_pow]
  exact (invOneSubPow ℚ m).val_inv

/-- `[x^j] (1-x)^{-m} = m^{(j)} / j!` for every `m`, including `m = 0`. -/
theorem coeff_invOneSubPow (m j : ℕ) :
    coeff j (invOneSubPow ℚ m).val = (m.ascFactorial j : ℚ) / j ! := by
  rcases m with _ | d
  · rw [invOneSubPow_zero, Units.val_one, coeff_one]
    rcases j with _ | j
    · simp
    · simp [Nat.zero_ascFactorial]
  · rw [invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk,
      Nat.ascFactorial_eq_factorial_mul_choose, Nat.choose_symm_add]
    push_cast
    field_simp

/-- `(x/(1-x)^n)^d = x^d (1-x)^{-nd}`. -/
theorem innerSeries_pow (n d : ℕ) :
    innerSeries n ^ d = X ^ d * (invOneSubPow ℚ (n * d)).val := by
  rw [innerSeries, inv_one_sub_pow_eq, mul_pow, ← Units.val_pow_eq_pow_val,
    invOneSubPow_eq_inv_one_sub_pow, invOneSubPow_eq_inv_one_sub_pow, ← pow_mul]

/-- `[x^e] (x/(1-x)^n)^d = (nd)^{(e-d)} / (e-d)!` when `d ≤ e`, and `0` otherwise. -/
theorem coeff_innerSeries_pow (n d e : ℕ) :
    coeff e (innerSeries n ^ d) =
      if d ≤ e then ((n * d).ascFactorial (e - d) : ℚ) / (e - d)! else 0 := by
  rw [innerSeries_pow, coeff_X_pow_mul', coeff_invOneSubPow]

/-- `[x^n] exp(x/(1-x)^n) = ∑_{d=0}^{n} [x^n] (x/(1-x)^n)^d / d!`: the
substitution's coefficient is a finite sum because `(x/(1-x)^n)^d` starts at
`x^d`. -/
theorem coeff_egf (n : ℕ) :
    coeff n (egf n) = ∑ d ∈ range (n + 1), (1 / d ! : ℚ) * coeff n (innerSeries n ^ d) := by
  have hsub : HasSubst (innerSeries n) :=
    HasSubst.of_constantCoeff_zero' (by simp [innerSeries])
  rw [egf, coeff_subst' hsub, finsum_eq_sum_of_support_subset _ (s := range (n + 1))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [coeff_exp, smul_eq_mul]
    rfl
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    apply hd
    rw [coeff_innerSeries_pow, if_neg (by omega), smul_zero]

/-- **Fidelity bridge.** The entry's definition `n! [x^n] exp(x/(1-x)^n)`
equals the closed form `a n` for every `n`. -/
theorem entry_eq_a (n : ℕ) : entry n = a n := by
  rw [entry, coeff_egf, a, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  have hd' : d ≤ n := by omega
  rw [show n + 1 - 1 - d = n - d by omega, coeff_innerSeries_pow, if_pos (Nat.sub_le n d),
    show n - (n - d) = d by omega, Nat.cast_mul, Nat.cast_choose ℚ hd']
  field_simp

/-- Examples on the entry's own definition: `n! [x^n] exp(x/(1-x)^n)` is
`55` at `n = 3` and `961` at `n = 4`. -/
example : entry 3 = 55 ∧ entry 4 = 961 := by
  rw [entry_eq_a, entry_eq_a]
  decide

/-! ## The congruence -/

/-- The rising factorial `m^{(i)}` modulo `k` depends only on `m` modulo `k`. -/
theorem ascFactorial_cast_zmod {k m m' i : ℕ} (h : (m : ZMod k) = m') :
    ((m.ascFactorial i : ℕ) : ZMod k) = (m'.ascFactorial i : ℕ) := by
  rw [Nat.cast_ascFactorial, Nat.cast_ascFactorial, h]

/-- For `1 ≤ q ≤ i`, `k ∣ C(k,q) · b^{(i)}`: `C(k,q) q!` is the falling
factorial of `k`, which `k` divides, and `q! ∣ i! ∣ b^{(i)}`. -/
theorem dvd_choose_mul_ascFactorial (k q i : ℕ) (hq : 0 < q) (hqi : q ≤ i) (b : ℕ) :
    k ∣ k.choose q * b.ascFactorial i := by
  obtain ⟨t, ht⟩ :=
    (Nat.factorial_dvd_factorial hqi).trans (Nat.factorial_dvd_ascFactorial b i)
  have hdesc : k ∣ k.descFactorial q := by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    rcases k with _ | k'
    · simp
    · rw [Nat.succ_descFactorial_succ]
      exact Dvd.intro _ rfl
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  rw [ht, ← mul_assoc, mul_comm (k.choose q)]
  exact Dvd.dvd.mul_right hdesc t

/-- Modulo `k`, `C(n+k,i) · b^{(i)} ≡ C(n,i) · b^{(i)}`: by Vandermonde, every
term `C(n,p) C(k,q) b^{(i)}` with `q ≥ 1` vanishes. -/
theorem choose_add_mul_cast_zmod (n k i b : ℕ) :
    (((n + k).choose i * b.ascFactorial i : ℕ) : ZMod k) =
      ((n.choose i * b.ascFactorial i : ℕ) : ZMod k) := by
  rw [Nat.add_choose_eq, Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun p q => n.choose p * k.choose q * b.ascFactorial i), Finset.sum_range_succ,
    Nat.sub_self, Nat.choose_zero_right, mul_one, Nat.cast_add, add_eq_right, Nat.cast_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [ZMod.natCast_eq_zero_iff, mul_assoc]
  exact Dvd.dvd.mul_left (dvd_choose_mul_ascFactorial k (i - p) i (by omega) (by omega) b) _

/-- The congruence on the closed form: `a(n + k) ≡ a(n) (mod k)` for all
`n, k` (at `k = 0` it is the identity `a n = a n`). -/
theorem a_add_modEq (n k : ℕ) : a (n + k) ≡ a n [MOD k] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  unfold a
  rw [Nat.cast_sum, Nat.cast_sum]
  simp_rw [choose_add_mul_cast_zmod n k]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : n + 1 ≤ n + k + 1))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Nat.cast_mul, Nat.cast_mul]
    congr 1
    apply ascFactorial_cast_zmod
    rw [show n + k - i = (n - i) + k by omega]
    push_cast
    rw [ZMod.natCast_self]
    ring
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul, Nat.cast_zero]

/-- Bala's congruence on the coefficient definition of A293013:
`entry(n+k)-entry(n)` is an integer multiple of `k` for all natural `n,k`.
The case `k=0` is trivial and included. -/
theorem a293013_add_modEq (n k : ℕ) : ∃ m : ℤ, entry (n + k) - entry n = k * m := by
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd.1 (a_add_modEq n k).symm)
  refine ⟨m, ?_⟩
  rw [entry_eq_a, entry_eq_a]
  exact_mod_cast hm

end Candidates.A293013ExpModPeter
