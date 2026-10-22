import Sorry.Enumerative.ZumkellerDoubling
import Enumerative.ZumkellerUniqueDivisor

set_option autoImplicit false

/-- The quotient of a positive integer by its unique Zumkeller divisor is odd. -/
theorem IsZumkeller.quotient_odd_of_unique {n z : ℕ} (hn : 0 < n)
    (hz : IsZumkeller z) (hzn : z ∣ n)
    (hunique : ∀ d, d ∣ n → IsZumkeller d → d = z) : Odd (n / z) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  have htwo : 2 ∣ n / z := even_iff_two_dvd.mp heven
  have hdouble : z * 2 ∣ n := by
    calc
      z * 2 ∣ z * (n / z) := Nat.mul_dvd_mul_left z htwo
      _ = n := Nat.mul_div_cancel' hzn
  have heq : z * 2 = z := hunique _ hdouble hz.mul_two
  have hzpos : 0 < z := hz.pos
  omega

/-- For a positive integer with a unique Zumkeller divisor, the quotient is odd
and itself divides that divisor. -/
theorem IsZumkeller.quotient_odd_and_dvd_of_unique {n z : ℕ} (hn : 0 < n)
    (hz : IsZumkeller z) (hzn : z ∣ n)
    (hunique : ∀ d, d ∣ n → IsZumkeller d → d = z) :
    Odd (n / z) ∧ n / z ∣ z := by
  exact ⟨hz.quotient_odd_of_unique hn hzn hunique,
    hz.quotient_dvd_of_unique hn hzn hunique⟩

example : 0 < (6 : ℕ) ∧ IsZumkeller 6 ∧ 6 ∣ 6 ∧
    (∀ d, d ∣ 6 → IsZumkeller d → d = 6) := by
  refine ⟨by decide, by decide, dvd_refl _, ?_⟩
  intro d hd hz
  have hdmem : d ∈ (6 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
    have hdivisors : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
    simpa only [hdivisors, Finset.mem_insert, Finset.mem_singleton] using hdmem
  rcases hcases with rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬IsZumkeller 1) hz)
  · exact False.elim ((by decide : ¬IsZumkeller 2) hz)
  · exact False.elim ((by decide : ¬IsZumkeller 3) hz)
  · rfl
