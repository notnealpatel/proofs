import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum

/-!
# A necessary dominant-prime bound for tau-sigma witnesses

This module supplies a necessary bound for the witness families considered in
`Enumerative/ZumkellerTauSigma`, without importing that conjecture-bearing module.
The proof uses divisor inclusion and coprime cancellation, then treats the genuine
`A = 1` boundary in the sole prime-power equality case. No novelty is claimed.
-/

set_option autoImplicit false

open Finset

namespace ZumkellerTauSigma

private lemma sigma_one_le_of_dvd {e A : ℕ} (hA : 0 < A) (he : e ∣ A) :
    ArithmeticFunction.sigma 1 e ≤ ArithmeticFunction.sigma 1 A := by
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply]
  exact sum_le_sum_of_subset (Nat.divisors_subset_of_dvd (by omega) he)

private lemma self_le_sigma_one {A : ℕ} (hA : 0 < A) :
    A ≤ ArithmeticFunction.sigma 1 A := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨dvd_refl A, by omega⟩)

private lemma geometric_mod {p j : ℕ} (hp : p.Prime) :
    (∑ i ∈ range (j + 1), p ^ i) % p = 1 := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt hp.one_lt]
  | succ j ih =>
    rw [sum_range_succ, Nat.add_mod, ih, pow_succ, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hp.one_lt]

private lemma prime_power_small {p b j : ℕ} (hp : p.Prime) (hb : 1 ≤ b)
    (hj : j ≤ b) (hpow : p ^ b ≤ j + 1) : p = 2 ∧ b = 1 ∧ j = 1 := by
  have hstrict : ∀ k : ℕ, k + 3 < 2 ^ (k + 2) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
      omega
  have hb1 : b = 1 := by
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
    have hbase := Nat.pow_le_pow_left hp.two_le b
    have hlarge := hstrict k
    rw [← hk] at hlarge
    omega
  subst b
  simp only [pow_one] at hpow
  have hp2 := hp.two_le
  omega

/-- A tau-sigma divisor witness of `A * p^b`, with positive cofactor coprime to the
prime `p` and positive exponent, forces `p` to be at most the divisor sum of `A`.
This excludes dominant-prime cofactor families from the witnesses in Ianakiev's
implication; it does not assert that implication. -/
theorem prime_le_sigma_one_of_tau_sigma_witness
    {A p b d : ℕ} (hA : 0 < A) (hp : p.Prime) (hpA : ¬p ∣ A)
    (hb : 1 ≤ b) (_hd : 1 < d) (hdvd : d ∣ A * p ^ b)
    (hEq : ArithmeticFunction.sigma 0 d * ArithmeticFunction.sigma 1 d = A * p ^ b) :
    p ≤ ArithmeticFunction.sigma 1 A := by
  by_contra hbound
  have hsmall : ArithmeticFunction.sigma 1 A < p := by omega
  obtain ⟨e, q, he, hq, hdshape⟩ := Nat.dvd_mul.mp hdvd
  obtain ⟨j, hj, hqshape⟩ := (Nat.dvd_prime_pow hp).mp hq
  rw [hqshape] at hdshape
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hA
  have hpe : ¬p ∣ e := fun h => hpA (h.trans he)
  have hcop : e.Coprime (p ^ j) :=
    ((hp.coprime_iff_not_dvd.mpr hpe).pow_left j).symm
  have hspos : 0 < ArithmeticFunction.sigma 1 e :=
    ArithmeticFunction.sigma_pos_iff.mpr hepos
  have htpos : 0 < ArithmeticFunction.sigma 0 e :=
    ArithmeticFunction.sigma_pos_iff.mpr hepos
  have hslt : ArithmeticFunction.sigma 1 e < p :=
    lt_of_le_of_lt (sigma_one_le_of_dvd hA he) hsmall
  have htlt : ArithmeticFunction.sigma 0 e < p :=
    lt_of_le_of_lt (ArithmeticFunction.sigma_mono 0 1 e (by omega)) hslt
  have hpt : p.Coprime (ArithmeticFunction.sigma 0 e) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt htpos htlt)
  have hps : p.Coprime (ArithmeticFunction.sigma 1 e) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hspos hslt)
  let g := ∑ i ∈ range (j + 1), p ^ i
  have hpg : p.Coprime g := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hmod : g % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hone : g % p = 1 := geometric_mod hp
    omega
  have hidentity :
      (ArithmeticFunction.sigma 0 e * ArithmeticFunction.sigma 1 e * g) * (j + 1) =
        A * p ^ b := by
    rw [← hdshape,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      ArithmeticFunction.sigma_one_apply_prime_pow hp] at hEq
    simpa only [g, mul_assoc, mul_left_comm, mul_comm] using hEq
  have hdiv : p ^ b ∣ j + 1 := by
    have hprod : p ^ b ∣
        (ArithmeticFunction.sigma 0 e * ArithmeticFunction.sigma 1 e * g) * (j + 1) := by
      rw [hidentity]
      exact dvd_mul_left (p ^ b) A
    exact (((hpt.mul_right hps).mul_right hpg).pow_left b).dvd_mul_left.mp hprod
  have hpow : p ^ b ≤ j + 1 := Nat.le_of_dvd (by omega) hdiv
  obtain ⟨hp2, hb1, hj1⟩ := prime_power_small hp hb hj hpow
  have hA1 : A = 1 := by
    have hself := self_le_sigma_one hA
    rw [hp2] at hsmall
    omega
  have he1 : e = 1 := Nat.dvd_one.mp (hA1 ▸ he)
  have hd2 : d = 2 := by simpa [he1, hp2, hj1] using hdshape.symm
  have ht2 : ArithmeticFunction.sigma 0 2 = 2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) Nat.prime_two
  have hs2 : ArithmeticFunction.sigma 1 2 = 3 := by
    simpa using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
  rw [hd2, ht2, hs2, hA1, hp2, hb1] at hEq
  norm_num at hEq

-- Joint satisfiability: the witness d = 2 for A = 3, p = 2, b = 1.
example : 0 < (3 : ℕ) ∧ Nat.Prime 2 ∧ ¬2 ∣ (3 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    1 < (2 : ℕ) ∧ 2 ∣ (3 : ℕ) * 2 ^ 1 ∧
    ArithmeticFunction.sigma 0 2 * ArithmeticFunction.sigma 1 2 = 3 * 2 ^ 1 := by
  decide

end ZumkellerTauSigma
