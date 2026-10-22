/-
# A000364: refutation of Bala's pure-period conjecture

OEIS A000364, Peter Bala (May 08 2023). The integer secant recurrence has
rational e.g.f. `(cos x)⁻¹`, as proved by `secantEGF_eq_inv_cos`.
At modulus `27`, any positive period dividing `φ(27) = 18` on `n ≥ 1`
would force `a(19) ≡ a(1)`, but these residues are `10` and `1`.
The finite-window examples below do not establish eventual periodicity.
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

/-! ### Examples against the OEIS DATA line -/

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

/-- The e.g.f. of `secant` is `sec x = (cos x)⁻¹` in
`ℚ⟦X⟧`, which is the defining property of A000364. -/
theorem secantEGF_eq_inv_cos : secantEGF = (PowerSeries.cos ℚ)⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one (by simp [PowerSeries.cos])).mpr secantEGF_mul_cos

/-! ### The conjecture -/

/-- Bala's conjecture (OEIS A000364): for every `k ≥ 1`, there is a
positive period `p ∣ φ(k)` such that `a(n+p) ≡ a(n) (mod k)` for all `n ≥ 1`.
This is pure periodicity from index `1`, not eventual periodicity. -/
def BalaSecantPeriodic : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
    ∀ n : ℕ, 1 ≤ n → secant (n + p) ≡ secant n [ZMOD k]

/-! ### Examples: residues modulo 21 and 27 -/

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

/-- Bala's pure-period conjecture fails at `k = 27`, where `φ(27) = 18`.
Any positive period dividing `18` would imply `a(19) ≡ a(1) (mod 27)`,
but the residues are `10` and `1`. -/
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
