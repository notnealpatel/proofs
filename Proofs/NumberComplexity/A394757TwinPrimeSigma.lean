/-
# A394757 — Sulaiman: twin-prime averages `k` with `gcd(k, σ(k))` prime satisfy `18 ∣ k`

## OEIS source (retrieved with `oeis show A394757` and the live text entry, 2026-10-21)

```
NAME:     Numbers k in A014574 (averages of twin prime pairs) such that
          gcd(k, sigma(k)) is prime.
TERMS:    18,72,1152,4050,5652,6948,15138,16452,20772,20808,27792,44532,46818,
          65700,67428,126612,143568,176418,180288,194868,195732,206082,212868,
          216900,218628,236772,276372,281250,299700,328788,362952,369828,377172,
          388962,390672,400068,402768
COMMENT (the conjectures, unsigned, in the entry of _Aied Sulaiman_, Mar 31 2026):
  Conjecture: all terms are divisible by 18.
  Conjecture: gcd(k, sigma(k)) is in {2,3}.
EXAMPLE:
  For k = 18: sigma(18) = 39 and gcd(18, 39) = 3, which is prime, so 18 is a term.
  For k = 12: sigma(12) = 28 and gcd(12, 28) = 4, which is not prime, so 12 is
  not a term.
CROSSREF: Intersection of A014574 and A392199.
AUTHOR:   _Aied Sulaiman_, Mar 31 2026
```

## Literature status (triage)

Open as far as the triage could tell: the entry (Mar 2026) gives no proof, and
the literature search was limited to the entry and its cross-references
(A392199, A014574).  Computation (2026-10-21, Sage): all 529 terms below
`2 · 10^7` satisfy both conjectures; the general form below (`6 ∣ k`, `k` not a
square) has no counterexample with `k < 2 · 10^6`.

## Proof (kernel-checked below)

Let `g = gcd(k, σ k)` be prime and `6 ∣ k`.
* `9 ∣ k`: otherwise `k = 3 j` with `3 ∤ j`, so `σ k = 4 σ j` and `2 ∣ g`,
  whence `g = 2`; then `4 ∤ k`, so `k = 2 l` with `l` odd, `σ k = 3 σ l`, and
  `3 ∣ g = 2`, absurd.
* `g ∈ {2, 3}` when `k` is not a square: otherwise `σ k` is coprime to `6`.
  Write `k = 2^a m`, `m` odd.  `σ(2^a) = 2^(a+1) - 1` is divisible by `3` when
  `a` is odd, so `a` is even; `σ m` is odd, so (multiplicativity and
  `σ(p^e) ≡ e + 1 (mod 2)` for odd `p`) `m` is a square; then `k` is a square.
* A twin-prime average `k` with `g` prime has `6 ∣ k` (`k = 4` gives `g = 1`)
  and is not a square (`n² - 1 = (n - 1)(n + 1)` prime forces `n = 2`).
The non-square hypothesis of the general form is needed for the second part:
`k = 86436 = 2² · 3² · 7⁴` has `gcd(k, σ k) = 7`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A394757TwinPrimeSigma

open ArithmeticFunction

/-! ## Definition layer -/

/-- A014574 membership: `k` is the average of a twin prime pair, i.e. `k - 1` and
`k + 1` are both prime.  The guard `0 < k` keeps the truncated subtraction off
its junk value (it is implied by `(k - 1).Prime` anyway). -/
def IsTwinPrimeAverage (k : ℕ) : Prop :=
  0 < k ∧ (k - 1).Prime ∧ (k + 1).Prime

instance (k : ℕ) : Decidable (IsTwinPrimeAverage k) := by
  unfold IsTwinPrimeAverage; infer_instance

/-- A394757 membership: `k` is a twin-prime average and `gcd(k, σ(k))` is prime. -/
def IsTerm (k : ℕ) : Prop :=
  IsTwinPrimeAverage k ∧ (Nat.gcd k (sigma 1 k)).Prime

instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm; infer_instance

/-! ## Ground truth -/

-- The entry's worked examples: `σ(18) = 39`, `gcd(18, 39) = 3`; `σ(12) = 28`.
example : sigma 1 18 = 39 ∧ Nat.gcd 18 39 = 3 ∧ sigma 1 12 = 28 := by decide

-- The first two listed terms are exactly the terms below `80`.
example : ∀ k < 80, IsTerm k ↔ (k = 18 ∨ k = 72) := by decide

-- `12` is a twin-prime average but not a term (`gcd = 4`).
example : IsTwinPrimeAverage 12 ∧ ¬ IsTerm 12 := by decide

/-! ## Helper lemmas -/

/-- For an odd prime `p`, `σ(p^e) ≡ e + 1 (mod 2)`. -/
theorem sigma_prime_pow_mod_two {p e : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (sigma 1 (p ^ e) : ZMod 2) = (e + 1 : ℕ) := by
  rw [sigma_one_apply_prime_pow hp]
  have h1 : (p : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hodd
  push_cast
  simp [h1]

/-- An odd number with odd divisor sum is a perfect square. -/
theorem isSquare_of_odd_of_odd_sigma (m : ℕ) (hm : Odd m) (hs : Odd (sigma 1 m)) :
    IsSquare m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    have hpo : Odd p := Odd.of_dvd_nat hm (dvd_pow_self p (by omega))
    have h2 := sigma_prime_pow_mod_two (e := n) hp hpo
    rw [(ZMod.natCast_eq_one_iff_odd).mpr hs] at h2
    have hodd : Odd (n + 1) := (ZMod.natCast_eq_one_iff_odd).mp h2.symm
    have heven : Even n := by
      rcases Nat.even_or_odd n with hn' | hn'
      · exact hn'
      · exact absurd hodd (Nat.not_odd_iff_even.mpr hn'.add_one)
    exact heven.isSquare_pow p
  | zero => exact ⟨0, rfl⟩
  | one => exact ⟨1, rfl⟩
  | coprime a b _ _ hab iha ihb =>
    have hσ : sigma 1 (a * b) = sigma 1 a * sigma 1 b :=
      isMultiplicative_sigma.map_mul_of_coprime hab
    rw [hσ, Nat.odd_mul] at hs
    rw [Nat.odd_mul] at hm
    obtain ⟨x, hx⟩ := iha hm.1 hs.1
    obtain ⟨y, hy⟩ := ihb hm.2 hs.2
    exact ⟨x * y, by rw [hx, hy]; ring⟩

/-- Multiplicativity at a prime factor of multiplicity one:
if `p` is prime and `p ∤ j`, then `σ(p j) = (p + 1) σ(j)`. -/
theorem sigma_prime_mul_of_not_dvd {p j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) :
    sigma 1 (p * j) = (p + 1) * sigma 1 j := by
  have hcop : Nat.Coprime p j := (Nat.Prime.coprime_iff_not_dvd hp).mpr hj
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  congr 1
  simpa [Finset.sum_range_succ, add_comm] using sigma_one_apply_prime_pow (i := 1) hp

/-- `3 ∣ σ(2^a)` when `a` is odd (`σ(2^a) = 2^(a+1) - 1 = 4^((a+1)/2) - 1`). -/
theorem three_dvd_sigma_two_pow_of_odd {a : ℕ} (ha : Odd a) : 3 ∣ sigma 1 (2 ^ a) := by
  obtain ⟨b, rfl⟩ := ha
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq le_rfl]
  have h4 : 2 ^ (2 * b + 1 + 1) = 4 ^ (b + 1) := by
    rw [show 2 * b + 1 + 1 = 2 * (b + 1) by ring, pow_mul]; norm_num
  rw [h4, show (2 - 1 : ℕ) = 1 from rfl, Nat.div_one]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 (b + 1)

/-- If `6 ∣ k` and `gcd(k, σ k)` is prime, then `9 ∣ k`. -/
theorem nine_dvd_of_six_dvd {k : ℕ} (h6 : 6 ∣ k) (hp : (Nat.gcd k (sigma 1 k)).Prime) :
    9 ∣ k := by
  by_contra h9
  set g := Nat.gcd k (sigma 1 k) with hg
  obtain ⟨j, rfl⟩ : 3 ∣ k := (Nat.dvd_trans (by norm_num) h6)
  have hj3 : ¬ 3 ∣ j := fun h => h9 (by obtain ⟨i, rfl⟩ := h; exact ⟨i, by ring⟩)
  have hσ3 : sigma 1 (3 * j) = 4 * sigma 1 j := sigma_prime_mul_of_not_dvd Nat.prime_three hj3
  have h2k : 2 ∣ 3 * j := Nat.dvd_trans (by norm_num) h6
  have h2g : 2 ∣ g := Nat.dvd_gcd h2k (by rw [hσ3]; exact Dvd.dvd.mul_right (by norm_num) _)
  have hg2 : g = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2g).symm
  -- `4 ∤ k`, so `k = 2 l` with `l` odd
  have h4k : ¬ 4 ∣ 3 * j := by
    intro h4
    have h4g : 4 ∣ g := Nat.dvd_gcd h4 (by rw [hσ3]; exact Dvd.intro _ rfl)
    rw [hg2] at h4g
    omega
  obtain ⟨l, hl⟩ := h2k
  have hl2 : ¬ 2 ∣ l := fun h => h4k (by rw [hl]; exact Nat.mul_dvd_mul_left 2 h)
  have hσ2 : sigma 1 (3 * j) = 3 * sigma 1 l := by
    rw [hl]; exact sigma_prime_mul_of_not_dvd Nat.prime_two hl2
  have h3g : 3 ∣ g := Nat.dvd_gcd (Dvd.intro _ rfl) (by rw [hσ2]; exact Dvd.intro _ rfl)
  rw [hg2] at h3g
  omega

/-- If `6 ∣ k`, `k` is not a square, and `gcd(k, σ k)` is prime, then the gcd is
`2` or `3`. -/
theorem gcd_sigma_eq_two_or_three {k : ℕ} (h6 : 6 ∣ k) (hsq : ¬ IsSquare k)
    (hp : (Nat.gcd k (sigma 1 k)).Prime) :
    Nat.gcd k (sigma 1 k) = 2 ∨ Nat.gcd k (sigma 1 k) = 3 := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact Nat.not_prime_zero (by simpa using hp)
  set g := Nat.gcd k (sigma 1 k) with hg
  by_contra hne
  push Not at hne
  have h2 : ¬ 2 ∣ sigma 1 k := fun h =>
    hne.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.dvd_gcd (Nat.dvd_trans (by norm_num) h6) h)).symm
  have h3 : ¬ 3 ∣ sigma 1 k := fun h =>
    hne.2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_gcd (Nat.dvd_trans (by norm_num) h6) h)).symm
  obtain ⟨a, m, hm, hkam⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.coprime_two_left).mpr hm)
  have hσ : sigma 1 k = sigma 1 (2 ^ a) * sigma 1 m := by
    rw [hkam]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have ha : Even a := by
    rcases Nat.even_or_odd a with ha | ha
    · exact ha
    · exact absurd (by rw [hσ]; exact Dvd.dvd.mul_right (three_dvd_sigma_two_pow_of_odd ha) _) h3
  have hσm : Odd (sigma 1 m) := by
    have hodd : Odd (sigma 1 k) := Nat.odd_iff.mpr (by omega)
    rw [hσ, Nat.odd_mul] at hodd
    exact hodd.2
  obtain ⟨s, hs⟩ := isSquare_of_odd_of_odd_sigma m hm hσm
  obtain ⟨c, hc⟩ := ha
  exact hsq ⟨2 ^ c * s, by rw [hkam, hs, hc, pow_add]; ring⟩

/-- **General form.**  If `6 ∣ k`, `k` is not a perfect square, and `gcd(k, σ k)`
is prime, then `18 ∣ k` and `gcd(k, σ k) ∈ {2, 3}`.  (The divisibility part does
not need the non-square hypothesis; the second part does, see `k = 86436`.) -/
theorem eighteen_dvd_and_gcd_sigma_of_six_dvd {k : ℕ} (h6 : 6 ∣ k) (hsq : ¬ IsSquare k)
    (hp : (Nat.gcd k (sigma 1 k)).Prime) :
    18 ∣ k ∧ (Nat.gcd k (sigma 1 k) = 2 ∨ Nat.gcd k (sigma 1 k) = 3) := by
  refine ⟨?_, gcd_sigma_eq_two_or_three h6 hsq hp⟩
  have h9 := nine_dvd_of_six_dvd h6 hp
  omega

/-- A twin-prime average `k` with `gcd(k, σ k)` prime is divisible by `6`. -/
theorem six_dvd_of_isTerm {k : ℕ} (hk : IsTerm k) : 6 ∣ k := by
  obtain ⟨⟨hk0, hm, hp⟩, hg⟩ := hk
  have hk3 : 3 ≤ k := by have := hm.two_le; omega
  by_cases hk5 : 5 ≤ k
  · have hn2m : ¬ 2 ∣ k - 1 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hm).mp h; omega
    have hn3m : ¬ 3 ∣ k - 1 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hm).mp h; omega
    have hn2p : ¬ 2 ∣ k + 1 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
    have hn3p : ¬ 3 ∣ k + 1 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
    have h2 : 2 ∣ k := by omega
    have h3 : 3 ∣ k := by
      have hr := Nat.mod_lt k (show 0 < 3 by norm_num)
      have hm1 : (k - 1) % 3 ≠ 0 := fun h => hn3m (Nat.dvd_of_mod_eq_zero h)
      have hp1 : (k + 1) % 3 ≠ 0 := fun h => hn3p (Nat.dvd_of_mod_eq_zero h)
      apply Nat.dvd_of_mod_eq_zero
      interval_cases hk : k % 3
      · rfl
      · exfalso; apply hm1; omega
      · exfalso; apply hp1; omega
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  · interval_cases k
    · exact absurd hp (by decide)
    · exact absurd hg (by decide)

/-- A twin-prime average divisible by `6` is not a perfect square: `n² - 1 =
(n + 1)(n - 1)` is prime only for `n = 2`, and `6 ∤ 4`. -/
theorem not_isSquare_of_isTwinPrimeAverage {k : ℕ} (hk : IsTwinPrimeAverage k) (h6 : 6 ∣ k) :
    ¬ IsSquare k := by
  rintro ⟨n, rfl⟩
  obtain ⟨hk0, hm, _⟩ := hk
  rw [show n * n - 1 = n * n - 1 * 1 from rfl, Nat.mul_self_sub_mul_self_eq] at hm
  rcases Nat.prime_mul_iff.mp hm with ⟨_, h1⟩ | ⟨_, h1⟩
  · have hn : n = 2 := by omega
    subst hn
    omega
  · have hn : n = 0 := by omega
    subst hn
    omega

/-! ## The conjectures -/

/-- **A394757, first conjecture (Aied Sulaiman, Mar 31 2026).**

Verbatim: "Conjecture: all terms are divisible by 18."  That is: if `k - 1` and
`k + 1` are both prime and `gcd(k, σ(k))` is prime, then `18 ∣ k`. -/
theorem a394757_eighteen_dvd {k : ℕ} (hk : IsTerm k) : 18 ∣ k := by
  have h6 := six_dvd_of_isTerm hk
  have h9 := nine_dvd_of_six_dvd h6 hk.2
  omega

/-- **A394757, second conjecture (Aied Sulaiman, Mar 31 2026).**

Verbatim: "Conjecture: gcd(k, sigma(k)) is in {2,3}."  That is: if `k - 1` and
`k + 1` are both prime and `gcd(k, σ(k))` is prime, then that gcd is `2` or `3`. -/
theorem a394757_gcd_sigma_eq_two_or_three {k : ℕ} (hk : IsTerm k) :
    Nat.gcd k (sigma 1 k) = 2 ∨ Nat.gcd k (sigma 1 k) = 3 := by
  have h6 := six_dvd_of_isTerm hk
  exact gcd_sigma_eq_two_or_three h6 (not_isSquare_of_isTwinPrimeAverage hk.1 h6) hk.2

/-! ## Sanity layer -/

-- Satisfiability of the hypotheses of the conjecture theorems: `18` is a term.
example : IsTerm 18 := by decide

-- Satisfiability of the hypotheses of the general form at `k = 18`.
example : 6 ∣ 18 ∧ ¬ IsSquare 18 ∧ (Nat.gcd 18 (sigma 1 18)).Prime := by
  refine ⟨by norm_num, ?_, by decide⟩
  rintro ⟨r, hr⟩
  have hr5 : r ≤ 5 := by nlinarith
  interval_cases r <;> omega

-- The non-square hypothesis of the general form is load-bearing for the second
-- part: `86436 = 294² = 2² · 3² · 7⁴` has `6 ∣ 86436` and `gcd(86436, σ 86436) = 7`.
example : Nat.gcd 86436 (sigma 1 86436) = 7 ∧ 6 ∣ 86436 ∧ IsSquare 86436 := by
  have h1 : sigma 1 86436 = sigma 1 (2 ^ 2) * (sigma 1 (3 ^ 2) * sigma 1 (7 ^ 4)) := by
    rw [show (86436 : ℕ) = 2 ^ 2 * (3 ^ 2 * 7 ^ 4) by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [h1, sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow Nat.prime_three,
    sigma_one_apply_prime_pow (by norm_num : (7 : ℕ).Prime)]
  refine ⟨?_, by norm_num, ⟨294, by norm_num⟩⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end Candidates.A394757TwinPrimeSigma
