import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos1052

/-- For a positive natural y, the cubic successor has its usual quadratic factor.
The side condition prevents truncated subtraction from changing that factor. -/
theorem cubic_successor_factorization (y : ℕ) (hy : 1 ≤ y) :
    (y + 1) * (y ^ 2 + 1 - y) = y ^ 3 + 1 := by
  have hle : y ≤ y ^ 2 + 1 := by nlinarith
  have hsub := Nat.sub_add_cancel hle
  nlinarith [hsub]

/-- If y is one modulo three, its successor is coprime to the quadratic cubic
factor. A common prime would divide three, which the residue excludes. -/
theorem coprime_successor_cubic_factor (y : ℕ) (hy : y % 3 = 1) :
    Nat.Coprime (y + 1) (y ^ 2 + 1 - y) := by
  have hypos : 1 ≤ y := by omega
  have hle : y ≤ y ^ 2 + 1 := by nlinarith
  have hsub := Nat.sub_add_cancel hle
  apply Nat.coprime_of_dvd
  intro r hr hfirst hsecond
  letI : Fact r.Prime := ⟨hr⟩
  have hcast1 : (y : ZMod r) + 1 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff (y + 1) r).mpr hfirst
  have hcast2 : ((y ^ 2 + 1 - y : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ r).mpr hsecond
  have hcastsub := congrArg (fun n : ℕ => (n : ZMod r)) hsub
  have hyneg : (y : ZMod r) = -1 := eq_neg_iff_add_eq_zero.mpr hcast1
  have hthree : (3 : ZMod r) = 0 := by
    have heq : (1 : ZMod r) + 1 = -1 := by
      simpa [hyneg, hcast2] using hcastsub.symm
    linear_combination heq
  have hr3 : r ∣ 3 := (ZMod.natCast_eq_zero_iff 3 r).mp hthree
  have hre : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by decide)).mp hr3
  subst r
  have hzero : (y + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hfirst
  omega

/-- Dividing an odd cubic successor by two preserves the exact factorization;
this is natural division with an explicitly divisible numerator. -/
theorem half_cubic_successor_factorization (y : ℕ) (hy : 1 ≤ y) (hodd : Odd y) :
    (y ^ 3 + 1) / 2 = ((y + 1) / 2) * (y ^ 2 + 1 - y) := by
  have htwo : 2 ∣ y + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  rw [← cubic_successor_factorization y hy, Nat.mul_comm (y + 1),
    Nat.mul_div_assoc _ htwo, Nat.mul_comm]

/-- Cubing an odd natural greater than one which is one modulo three adds at
least one distinct prime to the support of its half successor. -/
theorem primeFactors_half_cube_card_growth (y : ℕ) (hy : 1 < y)
    (hodd : Odd y) (hmod : y % 3 = 1) :
    ((y + 1) / 2).primeFactors.card + 1 ≤ ((y ^ 3 + 1) / 2).primeFactors.card := by
  have htwo : 2 ∣ y + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have hcop : Nat.Coprime ((y + 1) / 2) (y ^ 2 + 1 - y) :=
    (coprime_successor_cubic_factor y hmod).coprime_dvd_left
      (Nat.div_dvd_of_dvd htwo)
  have hfactor : 1 < y ^ 2 + 1 - y := by
    have hle : y ≤ y ^ 2 + 1 := by nlinarith
    have hsub := Nat.sub_add_cancel hle
    nlinarith [hsub]
  have hcard : 0 < (y ^ 2 + 1 - y).primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hfactor)
  rw [half_cubic_successor_factorization y (by omega) hodd, hcop.primeFactors_mul,
    Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
  omega

/-- The cubic tower over an odd x greater than one, with x one modulo three,
has at least k+1 distinct prime divisors in its half successor. Each new cubic
factor is coprime to the entire preceding half successor, not merely its neighbor. -/
theorem primeFactors_half_cubic_tower_card_lower_bound (x k : ℕ)
    (hx : 1 < x) (hodd : Odd x) (hmod : x % 3 = 1) :
    k + 1 ≤ ((x ^ (3 ^ k) + 1) / 2).primeFactors.card := by
  induction k with
  | zero =>
      have hxmod2 := Nat.odd_iff.mp hodd
      have hhalf : 1 < (x + 1) / 2 := by omega
      have hcard : 1 ≤ ((x + 1) / 2).primeFactors.card :=
        Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hhalf)
      simpa using hcard
  | succ k ih =>
      have hy : 1 < x ^ (3 ^ k) :=
        Nat.one_lt_pow (pow_ne_zero k (by decide)) hx
      have hymod : x ^ (3 ^ k) % 3 = 1 := by
        rw [Nat.pow_mod, hmod]
        simp
      have hgrowth := primeFactors_half_cube_card_growth (x ^ (3 ^ k))
        hy hodd.pow hymod
      rw [pow_succ (3 : ℕ) k, pow_mul]
      omega

/-- For every positive c, if the natural half successor of 61^(2c) has at most
four distinct prime divisors, then 81 does not divide c. Support containment
from a unitary-perfect identity is an upstream obligation, not assumed derived here. -/
theorem not_dvd_eighty_one_of_primeFactors_card_le_four (c : ℕ) (hc : 0 < c)
    (hsupport : ((61 ^ (2 * c) + 1) / 2).primeFactors.card ≤ 4) : ¬ 81 ∣ c := by
  intro hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hmpos : 0 < m := by omega
  let x : ℕ := 61 ^ (2 * m)
  have hx : 1 < x := Nat.one_lt_pow (by omega) (by decide)
  have hodd : Odd x := (by decide : Odd (61 : ℕ)).pow
  have hmod : x % 3 = 1 := by
    dsimp [x]
    rw [Nat.pow_mod]
    norm_num
  have hcard := primeFactors_half_cubic_tower_card_lower_bound x 4 hx hodd hmod
  change 5 ≤ ((x ^ 81 + 1) / 2).primeFactors.card at hcard
  have hpower : x ^ 81 = 61 ^ (2 * c) := by
    dsimp [x]
    rw [← pow_mul]
    congr 1
    omega
  rw [hpower] at hcard
  omega

-- All general factorization and coprimality premises hold together at y=7.
example : 1 < (7 : ℕ) ∧ Odd (7 : ℕ) ∧ (7 : ℕ) % 3 = 1 := by decide

-- A nonempty prime support satisfies the target's premises at c=1.
example : 0 < (1 : ℕ) ∧ ((61 ^ (2 * 1) + 1) / 2).primeFactors.card ≤ 4 := by
  have hp : Nat.Prime 1861 := by norm_num
  constructor
  · decide
  · change (1861 : ℕ).primeFactors.card ≤ 4
    rw [hp.primeFactors]
    simp

-- Positivity is essential: c=0 has empty support, but 81 divides zero.
example : ((61 ^ (2 * 0) + 1) / 2).primeFactors.card ≤ 4 ∧ 81 ∣ (0 : ℕ) := by
  norm_num

end Erdos1052
