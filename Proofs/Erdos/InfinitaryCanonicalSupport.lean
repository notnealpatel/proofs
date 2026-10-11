import Erdos.InfinitarySuperperfect
import Erdos.InfinitarySuccessorOrigins

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- A prime with the specified residues cannot divide the canonical infinitary
sum when the actual prime support lies in `{2,3,5}` and its valuations are even.
This includes zero and one, whose canonical sums are empty products. -/
theorem not_dvd_sigma_of_support_two_three_five (n q : ℕ)
    (hsupport : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 ∨ p = 5)
    (heven : ∀ p ∈ n.primeFactors, Even (n.factorization p))
    (hq : q.Prime) (hq4 : q % 4 = 1) (hq3 : q % 3 = 2) (hq5 : q % 5 = 4)
    (hq16 : q % 16 = 9 ∨ q % 16 = 13) : ¬ q ∣ sigma n := by
  intro hdiv
  obtain ⟨p, hp, hlocal⟩ := (hq.prime.dvd_finsetProd_iff
    (fun p => localSigma p (n.factorization p))).mp hdiv
  obtain ⟨h, hh, hslot⟩ := (hq.prime.dvd_finsetProd_iff
    (fun h => 1 + p ^ (2 ^ h))).mp hlocal
  have hheight : 1 ≤ h :=
    one_le_of_mem_binarySupport_of_even (n.factorization p) h (heven p hp) hh
  have hexclude := Erdos.InfinitarySuccessorOrigins.not_dvd_successors
    q hq hq4 hq3 hq5 hq16 h hheight
  rcases hsupport p hp with hp2 | hp3 | hp5
  · subst p
    exact hexclude.1 (by simpa only [Nat.add_comm] using hslot)
  · subst p
    exact hexclude.2.1 (by simpa only [Nat.add_comm] using hslot)
  · subst p
    exact hexclude.2.2 (by simpa only [Nat.add_comm] using hslot)

example : sigma 0 = 1 ∧ ¬29 ∣ sigma 0 := by
  norm_num [sigma]

example : sigma 1 = 1 ∧ ¬29 ∣ sigma 1 := by
  norm_num [sigma]

example :
    (4 : ℕ).primeFactors.Nonempty ∧
    (∀ p ∈ (4 : ℕ).primeFactors, p = 2 ∨ p = 3 ∨ p = 5) ∧
    (∀ p ∈ (4 : ℕ).primeFactors, Even ((4 : ℕ).factorization p)) ∧
    Nat.Prime 29 ∧ 29 % 4 = 1 ∧ 29 % 3 = 2 ∧ 29 % 5 = 4 ∧
    (29 % 16 = 9 ∨ 29 % 16 = 13) := by
  have hsupport4 : (4 : ℕ).primeFactors = {2} := by
    exact Nat.primeFactors_prime_pow (p := 2) (by decide : (2 : ℕ) ≠ 0) (by norm_num)
  have hvaluation4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow,
      Nat.Prime.factorization (by norm_num : Nat.Prime 2)]
    simp
  norm_num [hsupport4, hvaluation4]

example : ¬29 ∣ sigma 4 := by
  have hsupport4 : (4 : ℕ).primeFactors = {2} := by
    exact Nat.primeFactors_prime_pow (p := 2) (by decide : (2 : ℕ) ≠ 0) (by norm_num)
  have hvaluation4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow,
      Nat.Prime.factorization (by norm_num : Nat.Prime 2)]
    simp
  apply not_dvd_sigma_of_support_two_three_five
  all_goals norm_num [hsupport4, hvaluation4]

end InfinitarySuperperfect
