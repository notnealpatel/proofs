import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-!
# Fixed divisors from finite covering certificates

This is the standalone statement surface for the Palomar package. A certificate
is a finite literal set of triples `(a, d, p)`: an exponent residue, its
modulus, and a proposed divisor. The criterion works for the integer family
`A * b ^ n + B` at an arbitrary natural base `b`.
-/

set_option autoImplicit false

namespace Palomar.FixedDivisorCovering

/-- The exponent classes obtained by forgetting the divisor in each certificate
triple `(a, d, p)`. -/
def residueClasses (T : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.image fun t => (t.1, t.2.1)

/-- The finite set of proposed divisors listed by a certificate. -/
def fixedDivisors (T : Finset (ℕ × ℕ × ℕ)) : Finset ℕ :=
  T.image fun t => t.2.2

/-- A finite collection of residue classes covers every integer exponent. -/
def Covers (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ q ∈ S, n ≡ (q.1 : ℤ) [ZMOD (q.2 : ℤ)]

/-- A finite fixed-divisor certificate for the arbitrary-base integer family
`n ↦ A * b ^ n + B`. Each triple is `(residue, modulus, divisor)`. -/
structure IsFixedDivisorSystemBase (b : ℕ) (A B : ℤ)
    (T : Finset (ℕ × ℕ × ℕ)) : Prop where
  /-- Every listed divisor is nontrivial. -/
  one_lt_divisor : ∀ t ∈ T, 1 < t.2.2
  /-- The listed exponent residue classes cover all integers. -/
  covers : Covers (residueClasses T)
  /-- The base raised to each class modulus is one modulo its divisor. -/
  pow_modEq_one : ∀ t ∈ T, b ^ t.2.1 ≡ 1 [MOD t.2.2]
  /-- The proposed divisor divides the family at its class representative. -/
  divisor_dvd : ∀ t ∈ T, (t.2.2 : ℤ) ∣ A * (b : ℤ) ^ t.1 + B

example : residueClasses ({(0, 1, 3)} : Finset (ℕ × ℕ × ℕ)) = {(0, 1)} := by
  decide

example : fixedDivisors ({(0, 1, 3)} : Finset (ℕ × ℕ × ℕ)) = {3} := by
  decide

example : Covers ({(0, 1)} : Finset (ℕ × ℕ)) := by
  intro n
  refine ⟨(0, 1), by decide, ?_⟩
  change n % 1 = (0 : ℤ) % 1
  simp

/-- The hypotheses are jointly satisfiable at a non-binary base: the single
class modulo one certifies that `3` divides `2 * 4 ^ n + 1`. -/
example : IsFixedDivisorSystemBase 4 2 1 {(0, 1, 3)} := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro n
  refine ⟨(0, 1), by decide, ?_⟩
  change n % 1 = (0 : ℤ) % 1
  simp

/-- **Arbitrary-base fixed-divisor covering criterion.** If the literal finite
triples cover the exponents, `b ^ d` is one modulo the paired `p`, and `p`
divides `A * b ^ a + B`, then every value `A * b ^ n + B` has a listed
divisor. The family and divisibility conclusion are over the integers. -/
theorem IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd {b : ℕ}
    {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)}
    (h : IsFixedDivisorSystemBase b A B T) (n : ℕ) :
    ∃ p ∈ fixedDivisors T, (p : ℤ) ∣ A * (b : ℤ) ^ n + B := by
  sorry

/-- A fixed-divisor certificate proves non-primality only when a listed divisor
is explicitly bounded by `M` and `M < N`; divisibility alone does not exclude
the possibility that the divisor equals the whole value. -/
theorem IsFixedDivisorSystemBase.not_prime {b : ℕ} {A B : ℤ}
    {T : Finset (ℕ × ℕ × ℕ)} (h : IsFixedDivisorSystemBase b A B T)
    {M N n : ℕ} (hM : ∀ p ∈ fixedDivisors T, p ≤ M)
    (hN : (N : ℤ) = A * (b : ℤ) ^ n + B) (hMN : M < N) : ¬ N.Prime := by
  obtain ⟨p, hpT, hpDvd⟩ := h.exists_mem_fixedDivisors_dvd n
  obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp hpT
  have hpOne : 1 < t.2.2 := h.one_lt_divisor t htT
  have hpBound : t.2.2 < N := (hM t.2.2 hpT).trans_lt hMN
  have hpDvdNat : t.2.2 ∣ N := by
    apply Int.natCast_dvd_natCast.mp
    rw [hN]
    exact hpDvd
  intro hPrime
  rcases hPrime.eq_one_or_self_of_dvd t.2.2 hpDvdNat with hpEq | hpEq
  · exact hpOne.ne' hpEq
  · exact hpBound.ne hpEq

#check @Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd
#check @Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.not_prime

end Palomar.FixedDivisorCovering
