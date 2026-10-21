/-
# A000364 — Bala: secant numbers mod `k` are purely periodic with period dividing `φ(k)`

## OEIS source (retrieved with `oeis show A000364`, 2026-10-21)

```
NAME:     Euler (or secant or "Zig") numbers: e.g.f. (even powers only)
          sec(x) = 1/cos(x).
TERMS:    1,1,5,61,1385,50521,2702765,199360981,19391512145,2404879675441,...
COMMENT (the conjecture, verbatim):
  Conjecture: taking the sequence [a(n) : n >= 1] modulo an integer k gives a
  purely periodic sequence with period dividing phi(k). For example, the
  sequence taken modulo 21 begins [1, 5, 19, 20, 16, 2, 1, 5, 19, 20, 16, 2, 1,
  5, 19, 20, 16, 2, 1, 5, 19, ...] with an apparent period of 6 = phi(21)/2.
  - _Peter Bala_, May 08 2023
```

No later comment in the entry retracts or amends the conjecture.  The adjacent
comment (Allen Stenger, Aug 03 2020, citing Knuth & Buckholtz 1967, Thm. 2)
proves pure periodicity modulo every odd *prime*; the conjecture extends this
to every modulus `k`.

## Status

This module **refutes** the conjecture.  At `k = 27` (`φ(27) = 18`) the
sequence `a(n) mod 27`, `n ≥ 1`, begins

  1, 5, 7, 8, 4, 11, 1, 14, 25, 17, 22, 20, 19, 23, 16, 26, 13, 2, 10, 5, ...

so `a(19) ≡ 10` while `a(1) ≡ 1 (mod 27)`.  Every period `p ∣ 18` of the
sequence would make `18` a period too, hence `a(19) ≡ a(1)`; no such `p`
exists.  Computation (Python, `a(n)` for `n ≤ 700`, all `k ≤ 300`; evidence
only) finds failures exactly at the multiples of `27` or `125` (`27, 54, 81,
108, 125, 135, 162, 189, 216, 243, 250, 270, 297`), each failing at `n = 1`
(and at `k = 243` also at `n = 2`).  The data suggest the intended statement
is *eventual* periodicity (here from `n = 2`).

## Definition layer

The entry defines `a(n)` through the e.g.f. `sec x = Σ a(n) x^(2n)/(2n)!`.
Comparing coefficients of `x^(2n)` in `sec x · cos x = 1` gives, for `n ≥ 1`,
`Σ_{j ≤ n} (-1)^(n-j) C(2n,2j) a(j) = 0`, i.e. the recurrence of
`secant_succ`.  `secant` is computed from this recurrence (with the binomial
coefficient written through factorials so that the kernel evaluates it in
linear time), and `secantEGF_eq_inv_cos` proves that its e.g.f. is exactly
`(cos x)⁻¹` in `ℚ⟦X⟧`.  The definition therefore matches the entry's e.g.f.
definition for every `n`, not merely on the listed terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A000364Refutation

/-- `secantTable n = [a(0), a(1), …, a(n)]`, computed by the recurrence
`a(m+1) = Σ_{j ≤ m} (-1)^(m+j) C(2m+2, 2j) a(j)` from `a(0) = 1`, where
`C(2m+2, 2j)` is written as `(2m+2)! / ((2j)! (2m+2-2j)!)` (exact, since
`2j ≤ 2m+2`). -/
def secantTable : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
    let t := secantTable n
    t ++ [∑ j ∈ Finset.range (n + 1), (-1) ^ (n + j) *
      (((2 * n + 2).factorial / ((2 * j).factorial * (2 * n + 2 - 2 * j).factorial) : ℕ) : ℤ) *
        t.getD j 0]

/-- The secant (Euler, "Zig") number `a(n) = |E_{2n}|` of OEIS A000364, as an
integer: `(2n)!` times the coefficient of `x^(2n)` in `sec x`
(see `secantEGF_eq_inv_cos`). -/
def secant (n : ℕ) : ℤ := (secantTable n).getD n 0

/-! ### Ground truth against the OEIS DATA line -/

example : (List.range 10).map secant =
    [1, 1, 5, 61, 1385, 50521, 2702765, 199360981, 19391512145, 2404879675441] := by
  decide +kernel

example : secant 17 = 80723299235887898062168247453281 := by decide +kernel

/-! ### The recurrence and the e.g.f. -/

/-- The table has one entry for each index `0, …, n`. -/
theorem secantTable_length (n : ℕ) : (secantTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [secantTable, ih]

/-- Every earlier entry of the table is the corresponding secant number. -/
theorem secantTable_getD {n j : ℕ} (h : j ≤ n) : (secantTable n).getD j 0 = secant j := by
  induction n with
  | zero =>
    obtain rfl : j = 0 := by omega
    rfl
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with hlt | rfl
    · rw [secantTable, List.getD_append _ _ _ _ (by rw [secantTable_length]; omega)]
      exact ih (by omega)
    · rfl

/-- The defining recurrence, with the genuine binomial coefficient:
`a(n+1) = Σ_{j ≤ n} (-1)^(n+j) C(2n+2, 2j) a(j)`. -/
theorem secant_succ (n : ℕ) : secant (n + 1) = ∑ j ∈ Finset.range (n + 1),
    (-1) ^ (n + j) * ((2 * n + 2).choose (2 * j) : ℤ) * secant j := by
  have hlast : secant (n + 1) = ∑ j ∈ Finset.range (n + 1), (-1) ^ (n + j) *
      (((2 * n + 2).factorial / ((2 * j).factorial * (2 * n + 2 - 2 * j).factorial) : ℕ) : ℤ) *
        (secantTable n).getD j 0 := by
    simp only [secant, secantTable]
    rw [List.getD_append_right _ _ _ _ (by rw [secantTable_length])]
    simp [secantTable_length]
  rw [hlast]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  rw [secantTable_getD hj', Nat.choose_eq_factorial_div_factorial (by omega)]

/-- Coefficient form of `sec x · cos x = 1` at `x^(2n+2)`:
`Σ_{j ≤ n+1} (-1)^(n+1+j) C(2n+2, 2j) a(j) = 0`. -/
theorem secant_cos_sum (n : ℕ) : ∑ j ∈ Finset.range (n + 2),
    (-1) ^ (n + 1 + j) * ((2 * n + 2).choose (2 * j) : ℤ) * secant j = 0 := by
  have hpow : ∀ x : ℕ, (-1 : ℤ) ^ (n + 1 + x) = -(-1) ^ (n + x) := fun x => by
    rw [show n + 1 + x = (n + x) + 1 by ring, pow_succ]; ring
  have hlast : (-1 : ℤ) ^ (n + 1 + (n + 1)) = 1 := by
    rw [show n + 1 + (n + 1) = 2 * (n + 1) by ring, pow_mul]; simp
  rw [Finset.sum_range_succ, secant_succ n, hlast, show 2 * (n + 1) = 2 * n + 2 by ring,
    Nat.choose_self]
  simp only [hpow, neg_mul, Finset.sum_neg_distrib, Nat.cast_one, one_mul]
  ring

/-- The exponential generating function `Σ a(n) x^(2n) / (2n)!` (even powers
only) over `ℚ`. -/
noncomputable def secantEGF : PowerSeries ℚ :=
  PowerSeries.mk fun m => if Even m then (secant (m / 2) : ℚ) / m.factorial else 0

/-- Splitting a sum over `[0, 2N]` into its even and odd indices. -/
theorem sum_range_two_mul_add_one (g : ℕ → ℚ) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N + 1), g k =
      ∑ j ∈ Finset.range (N + 1), g (2 * j) + ∑ j ∈ Finset.range N, g (2 * j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring_nf

/-- `sec x · cos x = 1`: the e.g.f. of `secant` times `cos x` is `1` in `ℚ⟦X⟧`. -/
theorem secantEGF_mul_cos : secantEGF * PowerSeries.cos ℚ = 1 := by
  ext m
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [secantEGF, PowerSeries.cos, PowerSeries.coeff_mk]
  rcases Nat.even_or_odd m with ⟨N, rfl⟩ | ⟨N, rfl⟩
  · rcases N with _ | n
    · simp [secant, secantTable]
    · rw [if_neg (by omega), show (n + 1 + (n + 1)).succ = 2 * (n + 1) + 1 by omega,
        sum_range_two_mul_add_one]
      have hodd : ∑ j ∈ Finset.range (n + 1),
          (if Even (2 * j + 1) then (secant ((2 * j + 1) / 2) : ℚ) / (2 * j + 1).factorial
            else 0) *
          (if Even (n + 1 + (n + 1) - (2 * j + 1)) then
            (algebraMap ℚ ℚ) ((-1) ^ ((n + 1 + (n + 1) - (2 * j + 1)) / 2) /
              (n + 1 + (n + 1) - (2 * j + 1)).factorial) else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp
      rw [hodd, add_zero]
      have hfac : ((2 * n + 2).factorial : ℚ) ≠ 0 := by positivity
      have hterm : ∀ j ∈ Finset.range (n + 2),
          (if Even (2 * j) then (secant (2 * j / 2) : ℚ) / (2 * j).factorial else 0) *
          (if Even (n + 1 + (n + 1) - 2 * j) then
            (algebraMap ℚ ℚ) ((-1) ^ ((n + 1 + (n + 1) - 2 * j) / 2) /
              (n + 1 + (n + 1) - 2 * j).factorial) else 0) =
          (((-1) ^ (n + 1 + j) * ((2 * n + 2).choose (2 * j) : ℤ) * secant j : ℤ) : ℚ) /
            (2 * n + 2).factorial := by
        intro j hj
        have hjn : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hj
        have h1 : n + 1 + (n + 1) - 2 * j = 2 * (n + 1 - j) := by omega
        have h2 : 2 * n + 2 - 2 * j = 2 * (n + 1 - j) := by omega
        have hsign : (-1 : ℚ) ^ (n + 1 - j) = (-1) ^ (n + 1 + j) := by
          rw [show n + 1 + j = (n + 1 - j) + 2 * j by omega, pow_add, pow_mul]
          simp
        rw [h1]
        push_cast
        rw [Nat.cast_choose ℚ (by omega : 2 * j ≤ 2 * n + 2), h2]
        simp only [even_two_mul, if_true, Nat.mul_div_cancel_left _ two_pos, hsign]
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Int.cast_sum, secant_cos_sum]
      simp
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ 2 * N + 1 := by simpa [Nat.lt_succ_iff] using hk
    rcases Nat.even_or_odd k with hke | hko
    · have hodd : ¬ Even (2 * N + 1 - k) := by
        rw [Nat.not_even_iff_odd]
        obtain ⟨r, rfl⟩ := hke
        exact ⟨N - r, by omega⟩
      simp [hodd]
    · simp [Nat.not_even_iff_odd.mpr hko]

/-- **Faithfulness bridge.** The e.g.f. of `secant` is `sec x = (cos x)⁻¹` in
`ℚ⟦X⟧`, which is the defining property of A000364. -/
theorem secantEGF_eq_inv_cos : secantEGF = (PowerSeries.cos ℚ)⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one (by simp [PowerSeries.cos])).mpr secantEGF_mul_cos

/-! ### The conjecture -/

/-- **Bala's conjecture (A000364, Peter Bala, May 08 2023).**

Verbatim: "Conjecture: taking the sequence [a(n) : n >= 1] modulo an integer k
gives a purely periodic sequence with period dividing phi(k)."

Formalized: for every modulus `k ≥ 1` there is a period `p > 0` with
`p ∣ φ(k)` such that `a(n + p) ≡ a(n) (mod k)` for every `n ≥ 1` (pure
periodicity of the sequence indexed from `n = 1`). -/
def BalaSecantPeriodic : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
    ∀ n : ℕ, 1 ≤ n → secant (n + p) ≡ secant n [ZMOD k]

/-! ### Sanity: Bala's own example and the eventual periodicity at `k = 27` -/

-- Bala's example: modulo `21` the sequence has period `6 = φ(21)/2` on a window.
example : ∀ n ∈ Finset.Icc 1 24, secant (n + 6) ≡ secant n [ZMOD 21] := by decide +kernel

-- At `k = 27` the period `18 = φ(27)` holds from `n = 2` on a window
-- (computational evidence only, not a general theorem).
example : ∀ n ∈ Finset.Icc 2 24, secant (n + 18) ≡ secant n [ZMOD 27] := by decide +kernel

/-! ### The refutation -/

/-- `a(19) ≡ 10 (mod 27)`. -/
theorem secant_nineteen_emod : secant 19 % 27 = 10 := by decide +kernel

/-- `a(1) ≡ 1 (mod 27)`. -/
theorem secant_one_emod : secant 1 % 27 = 1 := by decide +kernel

/-- **Bala's conjecture is false.**  Counterexample: `k = 27`, `φ(27) = 18`.
Any period `p ∣ 18` would give `a(1 + 18) ≡ a(1) (mod 27)`, but
`a(19) = |E_38| ≡ 10` and `a(1) = 1 (mod 27)`.  The sequence mod 27 is periodic
with period `18` only from `n = 2`; the hypothesis the author probably intended
is eventual (not pure) periodicity, or pure periodicity for moduli not
divisible by `27` or `125` (the failures observed for `k ≤ 300`). -/
theorem bala_secant_periodic_false : ¬ BalaSecantPeriodic := by
  intro h
  obtain ⟨p, -, hdvd, hper⟩ := h 27 (by norm_num)
  have htot : Nat.totient 27 = 18 := by decide +kernel
  have hmul : ∀ m : ℕ, secant (1 + m * p) ≡ secant 1 [ZMOD 27] := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 1 + (m + 1) * p = (1 + m * p) + p by ring]
      exact (hper (1 + m * p) (by omega)).trans ih
  obtain ⟨m, hm⟩ := hdvd
  have h19 : secant 19 ≡ secant 1 [ZMOD 27] := by
    have hidx : 1 + m * p = 19 := by rw [mul_comm, ← hm, htot]
    simpa [hidx] using hmul m
  have hcontra : (10 : ℤ) = 1 := by
    rw [← secant_nineteen_emod, ← secant_one_emod]
    exact h19
  norm_num at hcontra

end Candidates.A000364Refutation
