import Enumerative.ZumkellerDivisorBlocks

set_option autoImplicit false

/-- If a positive integer has exactly one Zumkeller divisor `z`, its quotient by
`z` divides `z`. Uniqueness includes the case in which the integer itself is `z`. -/
theorem IsZumkeller.quotient_dvd_of_unique {n z : ℕ} (hn : 0 < n)
    (hz : IsZumkeller z) (hzn : z ∣ n)
    (hunique : ∀ d, d ∣ n → IsZumkeller d → d = z) : n / z ∣ z := by
  have hz0 : z ≠ 0 := hz.pos.ne'
  have hq0 : n / z ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hn hzn) hz.pos).ne'
  apply (Nat.factorization_le_iff_dvd hq0 hz0).mp
  intro p
  by_cases hp : p.Prime
  · by_contra hle
    let a := z.factorization p
    have hexp : a + 1 ≤ (n / z).factorization p := by omega
    have hqpow : p ^ (a + 1) ∣ n / z :=
      (hp.pow_dvd_iff_le_factorization hq0).mpr hexp
    have hzpow : p ^ a ∣ z := (hp.pow_dvd_iff_le_factorization hz0).mpr le_rfl
    obtain ⟨m, hm⟩ := hzpow
    have heq : z = m * p ^ a := by simpa only [Nat.mul_comm] using hm
    have hpm : ¬p ∣ m := by
      intro hd
      apply Nat.pow_succ_factorization_not_dvd hz0 hp
      change p ^ (a + 1) ∣ z
      calc
        p ^ (a + 1) = p * p ^ a := by rw [pow_succ, Nat.mul_comm]
        _ ∣ m * p ^ a := Nat.mul_dvd_mul_right hd _
        _ = z := heq.symm
    have hzm : IsZumkeller (m * p ^ a) := by rw [← heq]; exact hz
    have hblock := IsZumkeller.prime_power_blocks (t := 2) hp hpm (by decide) hzm
    have he : 2 * (a + 1) - 1 = a + (a + 1) := by omega
    have hbig : IsZumkeller (z * p ^ (a + 1)) := by
      rw [heq, Nat.mul_assoc, ← pow_add]
      simpa only [he] using hblock
    have hbigdvd : z * p ^ (a + 1) ∣ n := by
      calc
        z * p ^ (a + 1) ∣ z * (n / z) := Nat.mul_dvd_mul_left z hqpow
        _ = n := Nat.mul_div_cancel' hzn
    have hbig_eq : z * p ^ (a + 1) = z := hunique _ hbigdvd hbig
    have hpowone : p ^ (a + 1) = 1 :=
      Nat.eq_of_mul_eq_mul_left hz.pos (by simpa only [Nat.mul_one] using hbig_eq)
    have hpowlarge : 1 < p ^ (a + 1) := by
      exact one_lt_pow₀ hp.one_lt (by omega)
    omega
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, le_refl]

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
