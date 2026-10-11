import Enumerative.MultiperfectZumkeller

/-!
# Explicit divisor certificates for two multiperfect slices

Even triperfect numbers and 4-perfect multiples of six admit small half-sum
subsets of their divisors. These are unconditional slices of the proposed
A007691 to A083207 inclusion, not a proof of its full closure.
-/

set_option autoImplicit false

namespace Nat

/-- A positive even number with divisor sum `3 * n` is Zumkeller.
The half-sum subset is `{n, n / 2}`, represented without division as `{2*t, t}`. -/
theorem isZumkeller_of_two_dvd_of_sum_divisors_eq_three_mul
    {n : ℕ} (hn : 0 < n) (h2 : 2 ∣ n)
    (hs : ∑ d ∈ n.divisors, d = 3 * n) : IsZumkeller n := by
  obtain ⟨t, rfl⟩ := h2
  have ht : 0 < t := by omega
  have hne : 2 * t ≠ t := by omega
  refine (isZumkeller_iff_two_mul_sum_eq_sum_divisors hn).mpr
    ⟨{2 * t, t}, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact mem_divisors.mpr ⟨dvd_refl _, hn.ne'⟩
    · exact mem_divisors.mpr ⟨⟨2, by omega⟩, hn.ne'⟩
  · rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton, hs]
    omega

/-- A positive multiple of six with divisor sum `4 * n` is Zumkeller.
Writing `n = 6*t`, the half-sum subset is `{6*t, 3*t, 2*t, t}`. -/
theorem isZumkeller_of_six_dvd_of_sum_divisors_eq_four_mul
    {n : ℕ} (hn : 0 < n) (h6 : 6 ∣ n)
    (hs : ∑ d ∈ n.divisors, d = 4 * n) : IsZumkeller n := by
  obtain ⟨t, rfl⟩ := h6
  have ht : 0 < t := by omega
  have h63 : 6 * t ≠ 3 * t := by omega
  have h62 : 6 * t ≠ 2 * t := by omega
  have h61 : 6 * t ≠ t := by omega
  have h32 : 3 * t ≠ 2 * t := by omega
  have h31 : 3 * t ≠ t := by omega
  have h21 : 2 * t ≠ t := by omega
  refine (isZumkeller_iff_two_mul_sum_eq_sum_divisors hn).mpr
    ⟨{6 * t, 3 * t, 2 * t, t}, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact mem_divisors.mpr ⟨dvd_refl _, hn.ne'⟩
    · exact mem_divisors.mpr ⟨⟨2, by omega⟩, hn.ne'⟩
    · exact mem_divisors.mpr ⟨⟨3, by omega⟩, hn.ne'⟩
    · exact mem_divisors.mpr ⟨⟨6, by omega⟩, hn.ne'⟩
  · have h6mem : 6 * t ∉ ({3 * t, 2 * t, t} : Finset ℕ) := by
      simp [h63, h62, h61]
    have h3mem : 3 * t ∉ ({2 * t, t} : Finset ℕ) := by
      simp [h32, h31]
    have h2mem : 2 * t ∉ ({t} : Finset ℕ) := by
      simp [h21]
    rw [Finset.sum_insert h6mem, Finset.sum_insert h3mem,
      Finset.sum_insert h2mem, Finset.sum_singleton, hs]
    omega

/-- The triperfect certificate applies at `120`, with all hypotheses checked
jointly and without searching the divisor powerset. -/
theorem isZumkeller_120_of_triperfect_certificate : IsZumkeller 120 := by
  have hguards : 0 < (120 : ℕ) ∧ 2 ∣ (120 : ℕ) ∧
      (∑ d ∈ (120 : ℕ).divisors, d) = 3 * 120 := by decide
  exact isZumkeller_of_two_dvd_of_sum_divisors_eq_three_mul
    hguards.1 hguards.2.1 hguards.2.2

set_option maxRecDepth 40000 in
/-- The 4-perfect certificate applies at `30240`, a multiple of six.
The divisor-sum check splits over coprime `864` and `35`; it does not search
for a partition or use a practicality certificate. -/
theorem isZumkeller_30240_of_four_perfect_certificate : IsZumkeller 30240 := by
  have hs : (∑ d ∈ (30240 : ℕ).divisors, d) = 4 * 30240 := by
    rw [show (30240 : ℕ) = 864 * 35 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide)]
    decide
  have hguards : 0 < (30240 : ℕ) ∧ 6 ∣ (30240 : ℕ) ∧
      (∑ d ∈ (30240 : ℕ).divisors, d) = 4 * 30240 :=
    ⟨by norm_num, by norm_num, hs⟩
  exact isZumkeller_of_six_dvd_of_sum_divisors_eq_four_mul
    hguards.1 hguards.2.1 hguards.2.2

end Nat
