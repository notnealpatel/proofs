/-
# A394815 — Sulaiman: twin-prime averages `k` with `gcd(k, σ(k)) = 2` are divisible by 36

## OEIS source (retrieved with `oeis show A394815` and the live internal entry, 2026-10-21)

```
NAME:     Numbers k in A014574 (averages of twin prime pairs) such that
          gcd(k, sigma(k)) = 2.
TERMS:    5652,6948,16452,20772,27792,44532,65700,67428,126612,143568,180288,
          194868,195732,212868,216900,218628,236772,276372,299700,328788,369828,
          377172,390672,400068,402768,425988,437652,441108,463248,483408,491328,
          530532,536868,539712
COMMENT (the conjecture, unsigned, in the entry of _Aied Sulaiman_, May 01 2026):
  Conjecture: every term is divisible by 36.
COMMENT:
  Conjecturally, A394757 is the disjoint union of this sequence and A394399.
EXAMPLE:
  For k = 5652: k-1 = 5651 and k+1 = 5653 are prime; also sigma(5652) = 14378
  and gcd(5652, 14378) = 2, so 5652 is a term.
CROSSREF: Subsequence of A394757.  Cf. A014574, A392199, A394399.
AUTHOR:   _Aied Sulaiman_, May 01 2026
```

## Literature status (triage)

Open as far as the triage could tell: the entry gives no proof.  Computation
(2026-10-21, Python): the 91 terms below `2 · 10^6` include the 34 listed
terms and are all divisible by `36`; moreover every `k ≤ 2 · 10^6` with
`6 ∣ k` and `gcd(k, σ k) = 2` is divisible by `36`.

## Proof (kernel-checked below)

A term is a term of A394757 (`2` is prime), so `6 ∣ k` and `9 ∣ k` (A394757
module).  Write `k = 2^a m` with `m` odd.  If `a` were odd then
`3 ∣ 2^(a+1) - 1 = σ(2^a) ∣ σ(k)` and `3 ∣ k`, so `3 ∣ gcd(k, σ k) = 2`,
absurd.  So `a` is even and nonzero (`2 ∣ k`), hence `4 ∣ k`, and `36 ∣ k`.
-/
import Mathlib
import NumberComplexity.A394757TwinPrimeSigma

set_option autoImplicit false

namespace Candidates.A394815BothPrimeGcd

open ArithmeticFunction
open Candidates.A394757TwinPrimeSigma (IsTwinPrimeAverage)

/-! ## Definition layer

`IsTwinPrimeAverage k := 0 < k ∧ (k - 1).Prime ∧ (k + 1).Prime` (A014574
membership) is reused from `Proofs/NumberComplexity/A394757TwinPrimeSigma.lean`.
-/

/-- A394815 membership: `k` is a twin-prime average (A014574) and
`gcd(k, σ(k)) = 2`. -/
def IsTerm (k : ℕ) : Prop :=
  IsTwinPrimeAverage k ∧ Nat.gcd k (sigma 1 k) = 2

instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm; infer_instance

/-! ## Ground truth -/

-- The entry's example: `5651, 5653` are prime, `σ(5652) = 14378`, `gcd = 2`.
example : (5651 : ℕ).Prime ∧ (5653 : ℕ).Prime := by norm_num

/-- `σ(5652) = 14378` (the entry's example; `5652 = 2² · 3² · 157`). -/
theorem sigma_5652 : sigma 1 5652 = 14378 := by
  have h157 : Nat.Prime 157 := by norm_num
  rw [show (5652 : ℕ) = 2 ^ 2 * (3 ^ 2 * 157) by norm_num,
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow Nat.prime_three,
    ← pow_one 157, sigma_one_apply_prime_pow h157]
  simp [Finset.sum_range_succ]

/-- `gcd(5652, σ(5652)) = 2`. -/
theorem gcd_sigma_5652 : Nat.gcd 5652 (sigma 1 5652) = 2 := by
  rw [sigma_5652]
  norm_num

/-- The first listed term `5652` is a term. -/
theorem isTerm_5652 : IsTerm 5652 := by
  rw [IsTerm, sigma_5652]
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

-- The entry's second example: `18` is a twin-prime average but not a term (`gcd = 3`).
example : IsTwinPrimeAverage 18 ∧ ¬ IsTerm 18 := by decide

-- Small twin-prime averages are not terms: `gcd(4, 7) = 1`, `gcd(6, 12) = 6`,
-- `gcd(12, 28) = 4`, `gcd(30, 72) = 6`, `gcd(42, 96) = 6`, `gcd(60, 168) = 12`.
example : ∀ k < 61, ¬ IsTerm k := by decide

/-! ## Proof -/

/-- A term of A394815 is a term of A394757 (`2` is prime). -/
theorem isTerm_a394757_of_isTerm {k : ℕ} (hk : IsTerm k) :
    Candidates.A394757TwinPrimeSigma.IsTerm k :=
  ⟨hk.1, by rw [hk.2]; exact Nat.prime_two⟩

/-- If `6 ∣ k` and `gcd(k, σ k) = 2`, then `4 ∣ k`: in `k = 2^a m` with `m`
odd, an odd `a` would give `3 ∣ σ(2^a) ∣ σ(k)`, hence `3 ∣ gcd(k, σ k) = 2`. -/
theorem four_dvd_of_six_dvd_of_gcd_eq_two {k : ℕ} (h6 : 6 ∣ k)
    (hg : Nat.gcd k (sigma 1 k) = 2) : 4 ∣ k := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hg
  obtain ⟨a, m, hm, hkam⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.coprime_two_left).mpr hm)
  have hσ : sigma 1 k = sigma 1 (2 ^ a) * sigma 1 m := by
    rw [hkam]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have ha : Even a := by
    rcases Nat.even_or_odd a with ha | ha
    · exact ha
    · have h3σ : 3 ∣ sigma 1 k := by
        rw [hσ]
        exact Dvd.dvd.mul_right
          (Candidates.A394757TwinPrimeSigma.three_dvd_sigma_two_pow_of_odd ha) _
      have h3g : 3 ∣ Nat.gcd k (sigma 1 k) :=
        Nat.dvd_gcd (Nat.dvd_trans (by norm_num) h6) h3σ
      rw [hg] at h3g
      omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h2k : 2 ∣ k := Nat.dvd_trans (by norm_num) h6
    rw [hkam, pow_zero, one_mul] at h2k
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2k)
  obtain ⟨c, hc⟩ := ha
  have hc0 : c ≠ 0 := by omega
  have h4 : 4 ∣ 2 ^ a := by
    rw [hc, ← two_mul, pow_mul]
    exact dvd_pow (by norm_num) hc0
  rw [hkam]
  exact Dvd.dvd.mul_right h4 m

/-- **General form.**  If `6 ∣ k` and `gcd(k, σ k) = 2`, then `36 ∣ k`. -/
theorem thirtysix_dvd_of_six_dvd_of_gcd_eq_two {k : ℕ} (h6 : 6 ∣ k)
    (hg : Nat.gcd k (sigma 1 k) = 2) : 36 ∣ k := by
  have h4 : 4 ∣ k := four_dvd_of_six_dvd_of_gcd_eq_two h6 hg
  have h9 : 9 ∣ k :=
    Candidates.A394757TwinPrimeSigma.nine_dvd_of_six_dvd h6 (by rw [hg]; exact Nat.prime_two)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h9

/-! ## The conjecture -/

/-- **A394815 conjecture (unsigned, in the entry of Aied Sulaiman, May 01 2026).**

Verbatim: "Conjecture: every term is divisible by 36."  That is: if `k - 1` and
`k + 1` are both prime and `gcd(k, σ(k)) = 2`, then `36 ∣ k`. -/
theorem a394815_thirtysix_dvd {k : ℕ} (hk : IsTerm k) : 36 ∣ k :=
  thirtysix_dvd_of_six_dvd_of_gcd_eq_two
    (Candidates.A394757TwinPrimeSigma.six_dvd_of_isTerm (isTerm_a394757_of_isTerm hk)) hk.2

/-! ## Sanity layer -/

-- Satisfiability of the hypotheses of the general form: `k = 5652`.
example : 6 ∣ 5652 ∧ Nat.gcd 5652 (sigma 1 5652) = 2 :=
  ⟨by norm_num, gcd_sigma_5652⟩

end Candidates.A394815BothPrimeGcd
