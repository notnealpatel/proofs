import NumberComplexity.Quasilog

set_option autoImplicit false

namespace NumberComplexity

/-- The quasi-logarithm is bounded by twice the real base-two logarithm on positive inputs. -/
theorem quasilog_le_two_div_log_two_mul_log (n : ℕ) (hn : 0 < n) :
    (quasilog n : ℝ) ≤ (2 / Real.log 2) * Real.log n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  suffices H : ∀ n : ℕ, 0 < n → (quasilog n : ℝ) * Real.log 2 ≤ 2 * Real.log n by
    have h := H n hn
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog).mpr h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      simp
    have h2 : 2 ≤ n := by omega
    by_cases hp : n.Prime
    · by_cases hn2 : n = 2
      · subst n
        have hq : quasilog 2 = 1 := by norm_num [quasilog_of_prime]
        rw [hq]
        norm_num
        linarith
      have hodd : n % 2 = 1 := hp.eq_two_or_odd.resolve_left hn2
      let m := (n - 1) / 2
      have hm : 0 < m := by dsimp [m]; omega
      have hmlt : m < n := by dsimp [m]; omega
      have hfac : n - 1 = 2 * m := by dsimp [m]; omega
      have hq2 : quasilog 2 = 1 := by norm_num [quasilog_of_prime]
      have hq : quasilog n = 2 + quasilog m := by
        rw [quasilog_of_prime hp, hfac, quasilog_mul 2 m (by norm_num) hm, hq2]
        omega
      have hIH := ih m hmlt hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hlogfac : Real.log (n - 1 : ℕ) = Real.log 2 + Real.log m := by
        rw [hfac, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hmR.ne']
      have hmono : Real.log (n - 1 : ℕ) ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast (show 0 < n - 1 by omega))
          (by exact_mod_cast Nat.sub_le n 1)
      rw [hq, Nat.cast_add, Nat.cast_ofNat]
      nlinarith
    · have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hple : n.minFac ≤ n := Nat.minFac_le (by omega)
      have hplt : n.minFac < n := lt_of_le_of_ne hple (fun h => hp (h ▸ hpp))
      have hqpos : 0 < n / n.minFac := Nat.div_pos hple hpp.pos
      have hqlt : n / n.minFac < n := Nat.div_lt_self hn hpp.one_lt
      have hIH1 := ih n.minFac hplt hpp.pos
      have hIH2 := ih (n / n.minFac) hqlt hqpos
      have hfac : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
      have hlogfac : Real.log n = Real.log n.minFac + Real.log (n / n.minFac : ℕ) := by
        have hcast : (n : ℝ) = (n.minFac : ℝ) * (n / n.minFac : ℕ) := by
          exact_mod_cast hfac.symm
        rw [hcast, Real.log_mul
          (by exact_mod_cast hpp.pos.ne') (by exact_mod_cast hqpos.ne')]
      rw [quasilog_of_not_prime h2 hp, Nat.cast_add]
      nlinarith

example : (quasilog 2 : ℝ) ≤ (2 / Real.log 2) * Real.log 2 :=
  quasilog_le_two_div_log_two_mul_log 2 (by norm_num)

end NumberComplexity
