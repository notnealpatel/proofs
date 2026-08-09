/-
  Erdős's 1950 fixed-divisor theorem, re-derived as the `A = -1`,
  `B = m` instance of the general theorem of
  `Erdos.Covering.FixedDivisor`.

  ── Why this file exists, and why it is a leaf ──────────────────────
  `Erdos.Covering.NotTwoPowerPlusPrime` (committed, reviewed,
  axiom-swept) proves Erdős's 1950 theorem by a bespoke argument: the
  six-class system `erdosSystem1950`, the six partner primes
  `erdosPrimes1950`, and the hand-rolled one-class lemma
  `dvd_sub_two_pow_of_modEq` with a six-way case split.

  This file re-derives that file's *fixed-divisor core* from the
  general theorem, at `A = -1`, `B = m`, so that
  `m - 2 ^ k = -1 · 2 ^ k + m` is literally a member of the certified
  family.  `NotTwoPowerPlusPrime.lean` is not modified; the
  type-identity checks below confirm the re-derived statements are
  exactly the committed ones.

  The material lives here rather than in `FixedDivisor.lean` so that
  the framework does not depend on any of its applications.  The
  dependency graph is

      Basic ──▸ FixedDivisor ──▸ { Sierpinski, Riesel }
        │             │
        │             └──────────▸ Erdos1950Instance ◂── NotTwoPowerPlusPrime
        └──────────────────────────────────────────────┘

  and this module is a leaf: nothing imports it.  The framework is
  therefore not an after-the-fact generalization of the 1950 proof —
  it stands alone on `Basic` and Mathlib, and this file is one of
  three consumers.

  What is *not* re-derived: §7–§8 of `NotTwoPowerPlusPrime` (the
  dyadic-block removal of the side condition `2 ^ k + 241 < m`, and
  the infinitude packaging).  Those sit downstream of the fixed-divisor
  core and use no covering machinery; re-proving them would duplicate
  arithmetic, not demonstrate reuse.

  ── Contents ────────────────────────────────────────────────────────
  * `erdosCert1950` — the six classes of `erdosSystem1950` with their
    partner primes attached, projecting onto the committed data.
  * `isFixedDivisorSystem_erdosCert1950_residue` — the certificate at
    the base residue `M`, by kernel `decide` at `L = 24`.
  * `isFixedDivisorSystem_erdosCert1950` — the certificate along the
    whole progression `m ≡ M (mod P)`, by
    `IsFixedDivisorSystem.of_dvd_sub_const`.
  * `exists_mem_erdosPrimes1950_dvd_of_general`,
    `not_prime_sub_two_pow_of_general` — the committed conclusions,
    re-proved through the general theorem, with type-identity checks
    against the originals.
  * `dvd_sub_two_pow_of_modEq_of_general` — the committed one-class
    lemma, re-proved through `dvd_affine_two_pow_of_mod_eq`.

  Axiom audit: see the `#print axioms` block at the end.  Every
  declaration is sorry-free.  No `native_decide`, no custom axioms.
-/

import Mathlib
import Erdos.Covering.Basic
import Erdos.Covering.FixedDivisor
import Erdos.Covering.NotTwoPowerPlusPrime

set_option autoImplicit false

namespace Erdos.Covering

-- ════════════════════════════════════════════════════════════════════
-- §1 THE ERDŐS-1950 CERTIFICATE
-- ════════════════════════════════════════════════════════════════════

/-- The Erdős-1950 certificate: the six classes of `erdosSystem1950`
    with their partner primes attached.  `residueClasses` and
    `fixedDivisors` recover exactly `erdosSystem1950` and
    `erdosPrimes1950`. -/
def erdosCert1950 : Finset (ℕ × ℕ × ℕ) :=
  {(0, 2, 3), (0, 3, 7), (1, 4, 5), (3, 8, 17), (7, 12, 13), (23, 24, 241)}

-- Ground checks: the certificate has six triples and projects onto the
-- committed covering system and prime set.
example : erdosCert1950.card = 6 := by decide

/-- The classes of the Erdős-1950 certificate are the committed
    covering system `erdosSystem1950`. -/
theorem residueClasses_erdosCert1950 : residueClasses erdosCert1950 = erdosSystem1950 := by
  decide

/-- The divisors of the Erdős-1950 certificate are the committed prime
    set `erdosPrimes1950 = {3, 5, 7, 13, 17, 241}`. -/
theorem fixedDivisors_erdosCert1950 : fixedDivisors erdosCert1950 = erdosPrimes1950 := by
  decide

/-- **Satisfiability witness for `IsFixedDivisorSystem`.**  The
    Erdős-1950 certificate is valid for the family
    `n ↦ -1 · 2 ^ n + M` at the base residue `M = erdosResidue1950`:
    all four fields hold jointly, verified by kernel `decide` through
    `isFixedDivisorSystem_iff` at the common multiple `L = 24`.

    This is the mandated joint instantiation of the hypotheses of
    `IsFixedDivisorSystem`; the drop-one negative controls of
    `Erdos.Covering.FixedDivisor` §5 pin the predicate from the other
    side. -/
theorem isFixedDivisorSystem_erdosCert1950_residue :
    IsFixedDivisorSystem (-1) (erdosResidue1950 : ℤ) erdosCert1950 :=
  (isFixedDivisorSystem_iff (-1) (erdosResidue1950 : ℤ) erdosCert1950 24
    (by decide) (by decide)).mpr (by decide)

/-- The certificate stays valid along the whole progression
    `m ≡ M (mod P)`: shifting the constant term by a multiple of `P`
    shifts it by a multiple of every divisor, since each divides `P`.
    This is `IsFixedDivisorSystem.of_dvd_sub_const`. -/
theorem isFixedDivisorSystem_erdosCert1950 (m : ℕ)
    (hm : m % erdosModulus1950 = erdosResidue1950) :
    IsFixedDivisorSystem (-1) (m : ℤ) erdosCert1950 := by
  refine isFixedDivisorSystem_erdosCert1950_residue.of_dvd_sub_const ?_
  intro p hp
  rw [fixedDivisors_erdosCert1950] at hp
  have hall : ∀ q ∈ erdosPrimes1950, q ∣ erdosModulus1950 := by decide
  exact (Int.natCast_dvd_natCast.mpr (hall p hp)).trans (intCast_dvd_sub_of_mod_eq hm)

/-- **Erdős 1950's fixed-divisor theorem, as an instance.**  Identical
    in statement to `Erdos.Covering.exists_mem_erdosPrimes1950_dvd`,
    proved by instantiating the general theorem at `A = -1`, `B = m`
    instead of by the bespoke six-way case split. -/
theorem exists_mem_erdosPrimes1950_dvd_of_general (m k : ℕ)
    (hm : m % erdosModulus1950 = erdosResidue1950) :
    ∃ p ∈ erdosPrimes1950, (p : ℤ) ∣ (m : ℤ) - 2 ^ k := by
  obtain ⟨p, hp, hdvd⟩ :=
    (isFixedDivisorSystem_erdosCert1950 m hm).exists_mem_fixedDivisors_dvd k
  rw [fixedDivisors_erdosCert1950] at hp
  refine ⟨p, hp, ?_⟩
  have heq : (-1 : ℤ) * 2 ^ k + (m : ℤ) = (m : ℤ) - 2 ^ k := by ring
  rwa [heq] at hdvd

/-- **Erdős 1950's compositeness theorem, as an instance.**  Identical
    in statement to `Erdos.Covering.not_prime_sub_two_pow` up to the
    unused hypothesis `1 ≤ k`, proved from
    `IsFixedDivisorSystem.not_prime` with divisor bound `M = 241`. -/
theorem not_prime_sub_two_pow_of_general (m k : ℕ)
    (hm : m % erdosModulus1950 = erdosResidue1950) (hlt : 2 ^ k + 241 < m) :
    ¬ Nat.Prime (m - 2 ^ k) := by
  have h2k : 2 ^ k ≤ m := by omega
  have hbound : ∀ p ∈ fixedDivisors erdosCert1950, p ≤ 241 := by decide
  have hcast : ((m - 2 ^ k : ℕ) : ℤ) = (-1 : ℤ) * 2 ^ k + (m : ℤ) := by
    rw [Nat.cast_sub h2k]
    push_cast
    ring
  exact (isFixedDivisorSystem_erdosCert1950 m hm).not_prime hbound hcast (by omega)

/-! ── Type-identity checks ─────────────────────────────────────────
Each pair below elaborates the committed bespoke theorem and its
instance-of-the-general-theorem replacement against *one* expected
type, so the two really do prove the same proposition. -/

example : ∀ m k : ℕ, m % erdosModulus1950 = erdosResidue1950 →
    ∃ p ∈ erdosPrimes1950, (p : ℤ) ∣ (m : ℤ) - 2 ^ k :=
  exists_mem_erdosPrimes1950_dvd
example : ∀ m k : ℕ, m % erdosModulus1950 = erdosResidue1950 →
    ∃ p ∈ erdosPrimes1950, (p : ℤ) ∣ (m : ℤ) - 2 ^ k :=
  exists_mem_erdosPrimes1950_dvd_of_general

example : ∀ m k : ℕ, m % erdosModulus1950 = erdosResidue1950 → 1 ≤ k →
    2 ^ k + 241 < m → ¬ Nat.Prime (m - 2 ^ k) :=
  not_prime_sub_two_pow
example : ∀ m k : ℕ, m % erdosModulus1950 = erdosResidue1950 → 1 ≤ k →
    2 ^ k + 241 < m → ¬ Nat.Prime (m - 2 ^ k) :=
  fun m k hm _ hlt => not_prime_sub_two_pow_of_general m k hm hlt

/-- The one-class lemma `Erdos.Covering.dvd_sub_two_pow_of_modEq` is
    the `A = -1`, `B = m` case of `dvd_affine_two_pow_of_mod_eq`
    combined with the progression translation: `p ∣ m - M` (because
    `p ∣ P` and `P ∣ m - M`) plus `p ∣ M - 2 ^ a` give the base
    divisibility `p ∣ -1 · 2 ^ a + m`.

    ROUTING, stated because the `_of_general` suffix could suggest
    otherwise: this goes through the PER-CLASS step
    `dvd_affine_two_pow_of_mod_eq`, NOT through the general theorem
    `IsFixedDivisorSystem.exists_mem_fixedDivisors_dvd`, and it cannot
    go through the latter — a single residue class does not cover ℤ, so
    the covering hypothesis is unavailable here. The per-class step is
    itself fully general (arbitrary `A B : ℤ` and arbitrary `(a, d, p)`)
    and is the sole engine of the general theorem, so the content is
    subsumed; but this declaration is not an instance of the covering
    theorem and is not claimed as one. The genuine instances are
    `exists_mem_erdosPrimes1950_dvd_of_general` and
    `not_prime_sub_two_pow_of_general` below. -/
theorem dvd_sub_two_pow_of_modEq_of_general {P M p d a m k : ℕ} (hm : m % P = M)
    (hpP : p ∣ P) (hpow : 2 ^ d ≡ 1 [MOD p]) (hres : M ≡ 2 ^ a [MOD p])
    (hk : k % d = a) :
    (p : ℤ) ∣ (m : ℤ) - 2 ^ k := by
  -- `k % d = a` forces `a` to be already reduced mod `d`.
  have hkd : k % d = a % d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using hk
    · have hlt : a < d := hk ▸ Nat.mod_lt k hd
      rw [hk, Nat.mod_eq_of_lt hlt]
  -- `p ∣ m - M`.
  have hmM : (p : ℤ) ∣ (m : ℤ) - (M : ℤ) :=
    (Int.natCast_dvd_natCast.mpr hpP).trans (intCast_dvd_sub_of_mod_eq hm)
  -- `p ∣ M - 2 ^ a`, from the ℕ congruence `M ≡ 2 ^ a (mod p)`.
  have hMa : (p : ℤ) ∣ (M : ℤ) - 2 ^ a := by
    have hcast : (M : ℤ) ≡ 2 ^ a [ZMOD (p : ℤ)] := by
      have h := Int.natCast_modEq_iff.mpr hres
      push_cast at h
      exact h
    exact (Int.modEq_iff_dvd.mp hcast.symm)
  -- Base divisibility of the family at the exponent `a`.
  have hbase : (p : ℤ) ∣ (-1 : ℤ) * 2 ^ a + (m : ℤ) := by
    have hsum := dvd_add hmM hMa
    have heq : (m : ℤ) - (M : ℤ) + ((M : ℤ) - 2 ^ a) = (-1 : ℤ) * 2 ^ a + (m : ℤ) := by ring
    rwa [heq] at hsum
  have hmain := dvd_affine_two_pow_of_mod_eq (A := -1) (B := (m : ℤ)) hpow hbase hkd
  have heq : (-1 : ℤ) * 2 ^ k + (m : ℤ) = (m : ℤ) - 2 ^ k := by ring
  rwa [heq] at hmain

example : ∀ {P M p d a m k : ℕ}, m % P = M → p ∣ P → 2 ^ d ≡ 1 [MOD p] →
    M ≡ 2 ^ a [MOD p] → k % d = a → (p : ℤ) ∣ (m : ℤ) - 2 ^ k :=
  fun hm hpP hpow hres hk => dvd_sub_two_pow_of_modEq hm hpP hpow hres hk
example : ∀ {P M p d a m k : ℕ}, m % P = M → p ∣ P → 2 ^ d ≡ 1 [MOD p] →
    M ≡ 2 ^ a [MOD p] → k % d = a → (p : ℤ) ∣ (m : ℤ) - 2 ^ k :=
  fun hm hpP hpow hres hk => dvd_sub_two_pow_of_modEq_of_general hm hpP hpow hres hk


-- ════════════════════════════════════════════════════════════════════
-- §2 CROSS-CHECK: THE RIESEL DATA REUSES THIS PRIME SET
-- ════════════════════════════════════════════════════════════════════

-- `Erdos.Covering.Riesel` states the same two literals for
-- `rieselCert509203`.  Only the residues differ between the two
-- constructions, so every `2 ^ d ≡ 1 (mod p)` fact — and the six
-- `orderOf (2 : ZMod p) = d` theorems of `NotTwoPowerPlusPrime` §2 —
-- transfers with nothing new to prove.
example : fixedDivisors erdosCert1950 = {3, 5, 7, 13, 17, 241} := by decide
example : (residueClasses erdosCert1950).image Prod.snd = {2, 3, 4, 8, 12, 24} := by decide

-- ════════════════════════════════════════════════════════════════════
-- §3 AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms erdosCert1950
#print axioms residueClasses_erdosCert1950
#print axioms fixedDivisors_erdosCert1950
#print axioms isFixedDivisorSystem_erdosCert1950_residue
#print axioms isFixedDivisorSystem_erdosCert1950
#print axioms exists_mem_erdosPrimes1950_dvd_of_general
#print axioms not_prime_sub_two_pow_of_general
#print axioms dvd_sub_two_pow_of_modEq_of_general

end Erdos.Covering
