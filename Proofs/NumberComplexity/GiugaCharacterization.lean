/-
# Giuga numbers and the arithmetic derivative

The positive-multiplier characterization is due to J. M. Grau and
A. M. Oller-Marcén, arXiv:1103.2298, §2. Positivity of the multiplier
excludes primes; this is not the open assertion that the multiplier is one.
-/
import NumberComplexity.GiugaStructure

set_option autoImplicit false

namespace GiugaDerivative

/-- An arithmetic derivative congruent to one via an exact natural multiplier
forces squarefreeness. -/
theorem squarefree_of_ad_eq_mul_add_one {n a : ℕ}
    (h : ad n = a * n + 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hsq
  have hpn : p ∣ n := (dvd_mul_right p p).trans hsq
  have hpm : p ∣ a * n := dvd_mul_of_dvd_right hpn a
  have hpsucc : p ∣ a * n + 1 := h ▸ dvd_ad_of_sq_dvd hp hsq
  have hp1 : p ∣ 1 := by
    have hd : p ∣ a * n + 1 - a * n := Nat.dvd_sub hpsucc hpm
    simpa using hd
  exact hp.ne_one (Nat.dvd_one.mp hp1)

/-- The positive-multiplier direction of Grau–Oller-Marcén's characterization:
`ad n = a*n + 1`, with `a` positive and `n > 1`, implies that `n` is Giuga. -/
theorem isGiuga_of_ad_eq_mul_add_one {n a : ℕ} (hn : 1 < n) (ha : 0 < a)
    (h : ad n = a * n + 1) : IsGiuga n := by
  have hsf : Squarefree n := squarefree_of_ad_eq_mul_add_one h
  have hnp : ¬n.Prime := by
    intro hp
    have hmul : 0 < a * n := Nat.mul_pos ha (by omega)
    rw [ad_prime hp] at h
    omega
  refine ⟨hnp, hn, fun p hp => ?_⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hsum : n / p + ∑ q ∈ n.primeFactors.erase p, n / q = a * n + 1 := by
    rw [Finset.add_sum_erase _ _ hp, ← ad_eq_sum_div_of_squarefree hsf]
    exact h
  have hSdvd : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q :=
    Finset.dvd_sum fun q hq =>
      prime_dvd_div hpP
        (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
        (Finset.ne_of_mem_erase hq).symm hpn
        (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
  have hmod : n / p + ∑ q ∈ n.primeFactors.erase p, n / q ≡ n / p + 0 [MOD p] :=
    Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr hSdvd)
  have hmod' : a * n + 1 ≡ 0 + 1 [MOD p] :=
    Nat.ModEq.add_right _
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hpn a))
  calc n / p = n / p + 0 := (add_zero _).symm
    _ ≡ n / p + ∑ q ∈ n.primeFactors.erase p, n / q [MOD p] := hmod.symm
    _ = a * n + 1 := hsum
    _ ≡ 0 + 1 [MOD p] := hmod'
    _ = 1 := zero_add 1

/-- A squarefree composite natural number greater than one has arithmetic
 derivative greater than one: some prime-divisor quotient is at least two. -/
theorem one_lt_ad_of_squarefree_of_not_prime {n : ℕ} (hn : 1 < n)
    (hsf : Squarefree n) (hnp : ¬n.Prime) : 1 < ad n := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
  have hdiv : n / p * p = n := Nat.div_mul_cancel hpn
  have hquot : 1 < n / p := by
    have hne : n / p ≠ 1 := by
      intro heq
      rw [heq, one_mul] at hdiv
      exact hnp (hdiv ▸ hp)
    have hpos : 0 < n / p :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    omega
  have hle : n / p ≤ ∑ q ∈ n.primeFactors, n / q :=
    Finset.single_le_sum (fun q _ => Nat.zero_le (n / q)) hmem
  rw [← ad_eq_sum_div_of_squarefree hsf] at hle
  exact lt_of_lt_of_le hquot hle

/-- Every Giuga number has arithmetic derivative `a*n + 1` for a positive
natural multiplier, as proved by Grau and Oller-Marcén in arXiv:1103.2298, §2. -/
theorem exists_pos_multiplier_of_isGiuga {n : ℕ} (h : IsGiuga n) :
    ∃ a : ℕ, 0 < a ∧ ad n = a * n + 1 := by
  have had : 1 < ad n :=
    one_lt_ad_of_squarefree_of_not_prime h.2.1 (isGiuga_squarefree h) h.1
  have hle : 1 ≤ ad n := Nat.le_of_lt had
  have hmod : 1 ≡ ad n [MOD n] := (giuga_ad_modEq_one h).symm
  have hdvd : n ∣ ad n - 1 := (Nat.modEq_iff_dvd' hle).mp hmod
  have hsub : 0 < ad n - 1 := Nat.sub_pos_of_lt had
  let a : ℕ := (ad n - 1) / n
  have ha : 0 < a :=
    Nat.div_pos (Nat.le_of_dvd hsub hdvd) (lt_trans Nat.zero_lt_one h.2.1)
  have heq : a * n = ad n - 1 := Nat.div_mul_cancel hdvd
  refine ⟨a, ha, ?_⟩
  calc
    ad n = (ad n - 1) + 1 := (Nat.sub_add_cancel hle).symm
    _ = a * n + 1 := congrArg (fun x : ℕ => x + 1) heq.symm

/-- Grau–Oller-Marcén's positive-multiplier characterization of Giuga numbers
(arXiv:1103.2298, §2). The stable export name is `grauRibas_isGiuga_iff`;
positivity excludes primes and does not assert that the multiplier is one. -/
theorem grauRibas_isGiuga_iff (n : ℕ) (hn : 1 < n) :
    IsGiuga n ↔ ∃ a : ℕ, 0 < a ∧ ad n = a * n + 1 := by
  constructor
  · exact exists_pos_multiplier_of_isGiuga
  · rintro ⟨a, ha, heq⟩
    exact isGiuga_of_ad_eq_mul_add_one hn ha heq

example : 1 < (30 : ℕ) ∧ 0 < (1 : ℕ) ∧ ad 30 = 1 * 30 + 1 := by
  exact ⟨by norm_num, by norm_num, ad_30⟩

example : IsGiuga 30 :=
  isGiuga_of_ad_eq_mul_add_one (by norm_num) (by norm_num : 0 < (1 : ℕ)) ad_30

example : 1 < ad 30 := by rw [ad_30]; norm_num

example : IsGiuga 30 ∧ ∃ a : ℕ, 0 < a ∧ ad 30 = a * 30 + 1 :=
  ⟨isGiuga_30, (grauRibas_isGiuga_iff 30 (by norm_num)).mp isGiuga_30⟩

end GiugaDerivative
