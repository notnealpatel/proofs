/-
# Partitions into parts 3 and 5 (A008676)

Source: John W. Layman's OEIS A008676 formula (Sep 23 2009), with the
partition interpretation recorded by Andrew Baxter (Jun 20 2011).
For every `n`, the number of pairs `3a+5b=n` equals the coefficient of
`x^n` in `1/((1-x³)(1-x⁵))` and equals
`floor(2(n+3)/3)-floor(3(n+3)/5)`. Subtraction is in `ℤ` after casting.
The count is a residue-class count for `b ≤ n/5`, `b ≡ 2n (mod 3)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A008676PartitionsPartsCoefficient

/-! ## Definitions -/

/-- `partsThreeFive n` is the number of partitions of `n` into parts 3 and 5:
the number of pairs `(a, b)` of naturals with `3a + 5b = n` (`a` threes and `b`
fives).  Both coordinates are at most `n`, so the search box is exhaustive. -/
def partsThreeFive (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => 3 * p.1 + 5 * p.2 = n)).card

/-! ## Helper lemmas -/

/-- A partition of `n` into parts 3 and 5 is determined by its number `b` of
fives, which ranges over `b ≤ n / 5` with `b ≡ 2n (mod 3)`. -/
theorem partsThreeFive_eq_card_filter_modEq (n : ℕ) :
    partsThreeFive n =
      ((Finset.range (n / 5 + 1)).filter (fun b => b ≡ 2 * n [MOD 3])).card := by
  unfold partsThreeFive
  apply Finset.card_nbij' Prod.snd (fun b => ((n - 5 * b) / 3, b))
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    unfold Nat.ModEq
    omega
  · intro b h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    unfold Nat.ModEq at h
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_ofPred_eq] at h ⊢
    ext
    · simp only
      omega
    · rfl
  · intro b _
    rfl

/-- Closed form from counting a residue class: the number of `b < n / 5 + 1`
with `b ≡ 2n (mod 3)`. -/
theorem partsThreeFive_eq_count (n : ℕ) :
    partsThreeFive n =
      (n / 5 + 1) / 3 + if 2 * n % 3 < (n / 5 + 1) % 3 then 1 else 0 := by
  rw [partsThreeFive_eq_card_filter_modEq, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card _ (by norm_num : 0 < 3)]

/-! ## Examples -/

-- The definition reproduces the first 30 DATA terms directly.
example : (List.range 30).map partsThreeFive =
    [1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2,
      2, 2, 2, 2, 2] := by
  decide +kernel

-- Baxter's example `a(25) = 2`: `5+5+5+5+5` and `5+5+3+3+3+3+3+3`.
example : partsThreeFive 25 = 2 := by decide +kernel

-- All 78 listed DATA terms, through the proved reduction
-- `partsThreeFive_eq_card_filter_modEq`.
example : (List.range 78).map partsThreeFive =
    [1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2,
      2, 2, 2, 2, 2, 3, 2, 2, 3, 2, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 4, 3,
      4, 4, 3, 4, 4, 4, 4, 4, 4, 4, 5, 4, 4, 5, 4, 5, 5, 4, 5, 5, 5, 5, 5, 5, 5,
      6, 5, 5] := by
  rw [show partsThreeFive = fun n =>
      ((Finset.range (n / 5 + 1)).filter (fun b => b ≡ 2 * n [MOD 3])).card from
    funext partsThreeFive_eq_card_filter_modEq]
  decide +kernel

/-! ## Generating-function bridge

The entry's NAME defines `a(n)` as the coefficient of `x^n` in
`1/((1-x^3)(1-x^5))`.  The lemmas below identify that coefficient (in `PowerSeries ℚ`)
with `partsThreeFive n`, so Layman's formula is also proved in the NAME form. -/

/-- The power series `∑_{k ∣ i} x^i = 1/(1-x^k)` (for `0 < k`), with
coefficient `1` at multiples of `k` and `0` elsewhere. -/
noncomputable def multiplesSeries (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun i => if k ∣ i then 1 else 0

-- `1/(1-x^3) = 1 + x^3 + x^6 + ⋯`.
example : PowerSeries.coeff 6 (multiplesSeries 3) = 1 ∧
    PowerSeries.coeff 7 (multiplesSeries 3) = 0 := by
  simp [multiplesSeries]

/-- `(1 - x^k) · ∑_{k ∣ i} x^i = 1` for `0 < k`. -/
theorem one_sub_X_pow_mul_multiplesSeries (k : ℕ) (hk : 0 < k) :
    (1 - PowerSeries.X ^ k) * multiplesSeries k = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one,
    multiplesSeries, PowerSeries.coeff_mk]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn, PowerSeries.coeff_mk, if_neg (show n ≠ 0 by omega)]
    have hdvd : k ∣ n ↔ k ∣ n - k := by
      constructor
      · intro h
        exact Nat.dvd_sub h dvd_rfl
      · intro h
        have hadd : k ∣ n - k + k := Nat.dvd_add h dvd_rfl
        rwa [Nat.sub_add_cancel hkn] at hadd
    by_cases h : k ∣ n
    · rw [if_pos h, if_pos (hdvd.mp h)]
      simp
    · rw [if_neg h, if_neg (fun h' => h (hdvd.mpr h'))]
      simp
  · rw [if_neg hkn, sub_zero]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn, if_neg]
      intro h
      exact hkn (Nat.le_of_dvd (by omega) h)

/-- The coefficient of `x^n` in `(∑_{3 ∣ i} x^i)(∑_{5 ∣ j} x^j)` is the number
of partitions of `n` into parts 3 and 5. -/
theorem coeff_multiplesSeries_mul (n : ℕ) :
    PowerSeries.coeff n (multiplesSeries 3 * multiplesSeries 5) = partsThreeFive n := by
  rw [PowerSeries.coeff_mul]
  simp only [multiplesSeries, PowerSeries.coeff_mk, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.sum_boole, Finset.filter_filter, partsThreeFive]
  congr 1
  apply Finset.card_nbij' (fun p => (p.1 / 3, p.2 / 5)) (fun q => (3 * q.1, 5 * q.2))
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_filter, Finset.HasAntidiagonal.mem_antidiagonal,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b⟩ _
    simp only [Prod.mk.injEq]
    omega

/-- The coefficient of `x^n` in `1/((1-x^3)(1-x^5))` (over `ℚ`) is the number of
partitions of `n` into parts 3 and 5 (Baxter's comment on A008676). -/
theorem coeff_inv_eq_partsThreeFive (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.X ^ 3) * (1 - PowerSeries.X ^ 5) : PowerSeries ℚ)⁻¹ =
      partsThreeFive n := by
  have hinv : ((1 - PowerSeries.X ^ 3) * (1 - PowerSeries.X ^ 5) : PowerSeries ℚ)⁻¹ =
      multiplesSeries 3 * multiplesSeries 5 := by
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
    calc multiplesSeries 3 * multiplesSeries 5 *
          ((1 - PowerSeries.X ^ 3) * (1 - PowerSeries.X ^ 5))
        = ((1 - PowerSeries.X ^ 3) * multiplesSeries 3) *
            ((1 - PowerSeries.X ^ 5) * multiplesSeries 5) := by ring
      _ = 1 := by
        rw [one_sub_X_pow_mul_multiplesSeries 3 (by norm_num),
          one_sub_X_pow_mul_multiplesSeries 5 (by norm_num), one_mul]
  rw [hinv, coeff_multiplesSeries_mul]

/-! ## The conjecture -/

/-- Layman's formula: the number of partitions into parts 3 and 5 is
`floor(2(n+3)/3)-floor(3(n+3)/5)`. The floors are natural divisions;
subtraction is in `ℤ` after casting. -/
theorem layman_partsThreeFive_eq (n : ℕ) :
    (partsThreeFive n : ℤ) = ((2 * (n + 3) / 3 : ℕ) : ℤ) - ((3 * (n + 3) / 5 : ℕ) : ℤ) := by
  rw [partsThreeFive_eq_count]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 15 ∧ n = 15 * q + r :=
    ⟨n / 15, n % 15, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 15).symm⟩
  interval_cases r <;> split_ifs <;> omega

/-- **Layman's conjecture, generating-function form (A008676 NAME).**  The
coefficient of `x^n` in `1/((1-x^3)(1-x^5))` equals
`⌊2(n+3)/3⌋ - ⌊3(n+3)/5⌋` for every `n ≥ 0`. -/
theorem layman_coeff_inv_eq (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.X ^ 3) * (1 - PowerSeries.X ^ 5) : PowerSeries ℚ)⁻¹ =
      ((2 * (n + 3) / 3 : ℕ) : ℚ) - ((3 * (n + 3) / 5 : ℕ) : ℚ) := by
  rw [coeff_inv_eq_partsThreeFive]
  exact_mod_cast layman_partsThreeFive_eq n

end Candidates.A008676PartitionsPartsCoefficient
