import Enumerative.IsZumkeller
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Zumkeller reduction at a dominant prime

A prime larger than the divisor sum of a positive cofactor cannot create a
Zumkeller partition. Reduction modulo that prime retains just the divisors of
the cofactor. This supplies a dominant-prime family reduction alongside the
necessary bound in `Enumerative.TauSigmaDominantPrime`; it does not prove
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

-- All contract hypotheses hold jointly, with a genuine Zumkeller cofactor.
example : 0 < (6 : ℕ) ∧ Nat.Prime 13 ∧ ¬13 ∣ (6 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧
    ArithmeticFunction.sigma 1 6 < 13 ∧ IsZumkeller 6 := by decide
