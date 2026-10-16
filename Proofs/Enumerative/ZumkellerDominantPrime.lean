import Enumerative.IsZumkeller
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Zumkeller reduction at a dominant prime

A prime larger than the divisor sum of a positive cofactor cannot create a
Zumkeller partition. For an odd prime and an even cofactor divisor sum, the
stronger bound `sigma 1 A < 2 * p` suffices. Reduction modulo that prime retains
just the divisors of the cofactor. This supplies a dominant-prime family reduction
alongside the necessary bound in `Enumerative.TauSigmaDominantPrime`; it does not prove
Ianakiev's implication and makes no novelty claim.
-/

set_option autoImplicit false

open Finset

private lemma sum_mod_inter_divisors {A p b : ℕ} (hA : 0 < A)
    (hp : p.Prime) {S : Finset ℕ} (hS : S ⊆ (A * p ^ b).divisors) :
    (∑ d ∈ S, d) % p = (∑ d ∈ S ∩ A.divisors, d) % p := by
  have hremoved : p ∣ ∑ d ∈ S \ A.divisors, d := by
    apply Finset.dvd_sum
    intro d hd
    obtain ⟨hdS, hdnot⟩ := Finset.mem_sdiff.mp hd
    have hdprod : d ∣ A * p ^ b := (Nat.mem_divisors.mp (hS hdS)).1
    by_contra hpd
    have hcop : d.Coprime (p ^ b) :=
      (hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right b
    have hdA : d ∣ A := hcop.dvd_of_dvd_mul_right hdprod
    exact hdnot (Nat.mem_divisors.mpr ⟨hdA, hA.ne'⟩)
  rw [← Finset.sum_inter_add_sum_sdiff S A.divisors (fun d => d), Nat.add_mod,
    Nat.mod_eq_zero_of_dvd hremoved, add_zero, Nat.mod_mod]

/-- For a positive cofactor `A` not divisible by a prime `p`, and a positive
exponent `b`, if `sigma 1 A < p` then `A * p^b` is Zumkeller exactly when `A` is.
The forward direction restricts a divisor partition to the bottom prime layer;
the reverse direction is coprime closure. -/
theorem isZumkeller_mul_prime_pow_iff {A p b : ℕ} (hA : 0 < A)
    (hp : p.Prime) (hpA : ¬p ∣ A) (hb : 1 ≤ b)
    (hdom : ArithmeticFunction.sigma 1 A < p) :
    IsZumkeller (A * p ^ b) ↔ IsZumkeller A := by
  constructor
  · intro hZ
    obtain ⟨_, S, hS, hbalance⟩ := (isZumkeller_iff_exists_subset _).mp hZ
    let S₀ := S ∩ A.divisors
    let T := (A * p ^ b).divisors \ S
    have hT : T ⊆ (A * p ^ b).divisors := Finset.sdiff_subset
    have hincl : A.divisors ⊆ (A * p ^ b).divisors :=
      Nat.divisors_subset_of_dvd (Nat.mul_pos hA (pow_pos hp.pos b)).ne'
        (dvd_mul_right A (p ^ b))
    have hcomplement : T ∩ A.divisors = A.divisors \ S₀ := by
      ext d
      simp only [T, S₀, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hdprod, hdS⟩, hdA⟩
        exact ⟨hdA, fun h => hdS h.1⟩
      · rintro ⟨hdA, hdS⟩
        exact ⟨⟨hincl hdA, fun h => hdS ⟨h, hdA⟩⟩, hdA⟩
    have hmod : (∑ d ∈ S₀, d) % p = (∑ d ∈ A.divisors \ S₀, d) % p := by
      calc
        (∑ d ∈ S₀, d) % p = (∑ d ∈ S, d) % p :=
          (sum_mod_inter_divisors hA hp hS).symm
        _ = (∑ d ∈ T, d) % p := congrArg (fun x => x % p) hbalance
        _ = (∑ d ∈ A.divisors \ S₀, d) % p := by
          rw [sum_mod_inter_divisors hA hp hT, hcomplement]
    have hS₀ : S₀ ⊆ A.divisors := Finset.inter_subset_right
    have hsmallS : (∑ d ∈ S₀, d) < p := by
      apply lt_of_le_of_lt (Finset.sum_le_sum_of_subset hS₀)
      simpa only [ArithmeticFunction.sigma_one_apply] using hdom
    have hsmallT : (∑ d ∈ A.divisors \ S₀, d) < p := by
      apply lt_of_le_of_lt (Finset.sum_le_sum_of_subset Finset.sdiff_subset)
      simpa only [ArithmeticFunction.sigma_one_apply] using hdom
    rw [Nat.mod_eq_of_lt hsmallS, Nat.mod_eq_of_lt hsmallT] at hmod
    exact (isZumkeller_iff_exists_subset A).mpr ⟨hA, S₀, hS₀, hmod⟩
  · intro hZ
    have hcop : A.Coprime (p ^ b) :=
      (Nat.coprime_pow_right_iff (by omega : 0 < b) A p).mpr
        (hp.coprime_iff_not_dvd.mpr hpA).symm
    exact hZ.mul_of_coprime hcop

/-- For a positive cofactor `A` not divisible by an odd prime `p`, and a positive
exponent `b`, an even divisor sum `sigma 1 A < 2 * p` implies that `A * p^b` is
Zumkeller exactly when `A` is. Restricting a partition gives congruence modulo
`p`; evenness gives congruence modulo `2`, hence modulo `2 * p`. The strict
bound forces equality without using truncated subtraction. -/
theorem isZumkeller_mul_prime_pow_iff_of_even_sigma {A p b : ℕ} (hA : 0 < A)
    (hp : p.Prime) (hodd : Odd p) (hpA : ¬p ∣ A) (hb : 1 ≤ b)
    (heven : Even (ArithmeticFunction.sigma 1 A))
    (hdom : ArithmeticFunction.sigma 1 A < 2 * p) :
    IsZumkeller (A * p ^ b) ↔ IsZumkeller A := by
  constructor
  · intro hZ
    obtain ⟨_, S, hS, hbalance⟩ := (isZumkeller_iff_exists_subset _).mp hZ
    let S₀ := S ∩ A.divisors
    let T := (A * p ^ b).divisors \ S
    have hT : T ⊆ (A * p ^ b).divisors := Finset.sdiff_subset
    have hincl : A.divisors ⊆ (A * p ^ b).divisors :=
      Nat.divisors_subset_of_dvd (Nat.mul_pos hA (pow_pos hp.pos b)).ne'
        (dvd_mul_right A (p ^ b))
    have hcomplement : T ∩ A.divisors = A.divisors \ S₀ := by
      ext d
      simp only [T, S₀, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hdprod, hdS⟩, hdA⟩
        exact ⟨hdA, fun h => hdS h.1⟩
      · rintro ⟨hdA, hdS⟩
        exact ⟨⟨hincl hdA, fun h => hdS ⟨h, hdA⟩⟩, hdA⟩
    have hmod : (∑ d ∈ S₀, d) % p = (∑ d ∈ A.divisors \ S₀, d) % p := by
      calc
        (∑ d ∈ S₀, d) % p = (∑ d ∈ S, d) % p :=
          (sum_mod_inter_divisors hA hp hS).symm
        _ = (∑ d ∈ T, d) % p := congrArg (fun x => x % p) hbalance
        _ = (∑ d ∈ A.divisors \ S₀, d) % p := by
          rw [sum_mod_inter_divisors hA hp hT, hcomplement]
    have hS₀ : S₀ ⊆ A.divisors := Finset.inter_subset_right
    have hsplit : (∑ d ∈ A.divisors \ S₀, d) + (∑ d ∈ S₀, d) =
        ArithmeticFunction.sigma 1 A := by
      simpa only [ArithmeticFunction.sigma_one_apply] using Finset.sum_sdiff hS₀
    have htwo : Nat.ModEq 2 (∑ d ∈ S₀, d) (∑ d ∈ A.divisors \ S₀, d) := by
      have hparity := Nat.even_iff.mp heven
      unfold Nat.ModEq
      omega
    have hmod_two_p : Nat.ModEq (2 * p) (∑ d ∈ S₀, d)
        (∑ d ∈ A.divisors \ S₀, d) :=
      (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.mpr hodd)).mp
        ⟨htwo, hmod⟩
    have hsmallS : (∑ d ∈ S₀, d) < 2 * p := by omega
    have hsmallT : (∑ d ∈ A.divisors \ S₀, d) < 2 * p := by omega
    exact (isZumkeller_iff_exists_subset A).mpr
      ⟨hA, S₀, hS₀, hmod_two_p.eq_of_lt_of_lt hsmallS hsmallT⟩
  · intro hZ
    have hcop : A.Coprime (p ^ b) :=
      (Nat.coprime_pow_right_iff (by omega : 0 < b) A p).mpr
        (hp.coprime_iff_not_dvd.mpr hpA).symm
    exact hZ.mul_of_coprime hcop

-- All contract hypotheses hold jointly, with a genuine Zumkeller cofactor.
example : 0 < (6 : ℕ) ∧ Nat.Prime 13 ∧ ¬13 ∣ (6 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    ArithmeticFunction.sigma 1 6 < 13 ∧ IsZumkeller 6 := by decide

-- The parity-enhanced hypotheses hold beyond the old dominant-prime range.
set_option maxRecDepth 4096 in
example : 0 < (738 : ℕ) ∧ Nat.Prime 821 ∧ Odd (821 : ℕ) ∧
    ¬821 ∣ (738 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    Even (ArithmeticFunction.sigma 1 738) ∧
    ArithmeticFunction.sigma 1 738 < 2 * 821 ∧
    ¬ArithmeticFunction.sigma 1 738 < 821 := by decide

set_option maxRecDepth 4096 in
example : IsZumkeller (738 * 821 ^ 1) ↔ IsZumkeller 738 := by
  apply isZumkeller_mul_prime_pow_iff_of_even_sigma <;> decide
