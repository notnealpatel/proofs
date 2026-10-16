import Enumerative.ZumkellerTauSigma
import Enumerative.ZumkellerDivisorBlocks
import Enumerative.ZumkellerDominantPrime

/-!
# Zumkeller numbers with two prime factors

This is the classification in Mahanta–Saikia–Yaqubi, arXiv:2008.11096,
Theorem 2.6 (source label `Thm4`): for an odd prime `p` and `0 < b`,
`2^a * p^b` is Zumkeller exactly when `p + 1 ≤ 2^(a+1)` and `b` is odd.
The exponent `a = 0` is allowed. This is a known-result formalization,
not a classification of arbitrary unique-divisor prime quotients.
-/

set_option autoImplicit false

open Finset

namespace ZumkellerTwoPrime

private lemma sigma_two_pow_add_one (a : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ a) + 1 = 2 ^ (a + 1) := by
  simpa only [ArithmeticFunction.sigma_one_apply] using
    ZumkellerTauSigma.sum_divisors_two_pow_add_one a

private lemma sigma_two_pow_odd (a : ℕ) :
    Odd (ArithmeticFunction.sigma 1 (2 ^ a)) := by
  have hs := sigma_two_pow_add_one a
  have he : Even (2 ^ (a + 1)) := by
    rw [pow_succ]
    exact even_two.mul_left _
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  omega

private lemma not_isZumkeller_two_pow (a : ℕ) : ¬ IsZumkeller (2 ^ a) := by
  intro hz
  have he : Even (ArithmeticFunction.sigma 1 (2 ^ a)) := by
    rw [ArithmeticFunction.sigma_one_apply, even_iff_two_dvd]
    exact hz.two_dvd_sum_divisors
  exact (Nat.not_even_iff_odd.mpr (sigma_two_pow_odd a)) he

private lemma sigma_prime_pow_even_iff {p b : ℕ} (hp : p.Prime) (hodd : Odd p) :
    Even (ArithmeticFunction.sigma 1 (p ^ b)) ↔ Odd b := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  simp only [mul_one]
  rw [Finset.even_sum_iff_even_card_odd]
  have hf : (range (b + 1)).filter (fun i => Odd (p ^ i)) = range (b + 1) := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact hodd.pow
  rw [hf, Finset.card_range, Nat.even_add_one, Nat.not_even_iff_odd]

/-- The known two-prime classification (Mahanta–Saikia–Yaqubi, Theorem 2.6):
for an odd prime `p` and positive `b`, `2^a * p^b` is Zumkeller if and only if
`p + 1 ≤ 2^(a+1)` and `b` is odd. The case `a = 0` is included. -/
theorem isZumkeller_two_pow_mul_prime_pow_iff {a b p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hb : 0 < b) :
    IsZumkeller (2 ^ a * p ^ b) ↔ (p + 1 ≤ 2 ^ (a + 1) ∧ Odd b) := by
  have hcop : (2 ^ a).Coprime p :=
    (Nat.coprime_two_left.mpr hodd).pow_left a
  have hpm : ¬ p ∣ 2 ^ a := hp.coprime_iff_not_dvd.mp hcop.symm
  constructor
  · intro hz
    have hthreshold : p + 1 ≤ 2 ^ (a + 1) := by
      by_contra hn
      have hs := sigma_two_pow_add_one a
      have hdom : ArithmeticFunction.sigma 1 (2 ^ a) < p := by omega
      have hz2 : IsZumkeller (2 ^ a) :=
        (isZumkeller_mul_prime_pow_iff (Nat.two_pow_pos a) hp hpm hb hdom).mp hz
      exact not_isZumkeller_two_pow a hz2
    have he : Even (ArithmeticFunction.sigma 1 (2 ^ a * p ^ b)) := by
      rw [ArithmeticFunction.sigma_one_apply, even_iff_two_dvd]
      exact hz.two_dvd_sum_divisors
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (hcop.pow_right b), Nat.even_mul] at he
    have heprime : Even (ArithmeticFunction.sigma 1 (p ^ b)) :=
      he.resolve_left (Nat.not_even_iff_odd.mpr (sigma_two_pow_odd a))
    exact ⟨hthreshold, (sigma_prime_pow_even_iff hp hodd).mp heprime⟩
  · rintro ⟨hle, k, hk⟩
    have hbase : IsZumkeller (2 ^ a * p ^ 1) := by
      simpa only [pow_one] using
        ZumkellerTauSigma.isZumkeller_two_pow_mul_prime hp hodd hle
    have hblocks := IsZumkeller.prime_power_blocks hp hpm (Nat.succ_pos k) hbase
    have hexp : (k + 1) * (1 + 1) - 1 = b := by omega
    simpa only [hexp] using hblocks

-- Joint satisfiability and a positive, nonvacuous instance: 6 = 2 * 3.
example : Nat.Prime 3 ∧ Odd (3 : ℕ) ∧ 0 < (1 : ℕ) ∧
    3 + 1 ≤ 2 ^ (1 + 1) ∧ Odd (1 : ℕ) ∧ IsZumkeller (2 ^ 1 * 3 ^ 1) := by
  decide

example : IsZumkeller 6 := by
  exact (isZumkeller_two_pow_mul_prime_pow_iff (a := 1) (b := 1) (p := 3)
    (by decide) (by decide) (by decide)).mpr (by decide)

-- The permitted zero exponent is genuinely excluded, not silently omitted.
example : ¬ IsZumkeller (2 ^ 0 * 3 ^ 1) := by
  rw [isZumkeller_two_pow_mul_prime_pow_iff (by decide) (by decide) (by decide)]
  decide

end ZumkellerTwoPrime
