/-
# A280098 — Wilson: `k ∣ σ(k n - 1)` for all `n` iff `k ∈ {1, 3, 4, 6, 8, 12, 24}`

## OEIS source (retrieved with `oeis show A280098`, 2026-10-21)

```
NAME:     The sum of the divisors of 24*n - 1, divided by 24.
TERMS:    1,2,3,5,6,7,7,8,11,10,11,14,13,17,15,16,19,18,28,20,21,24,25,31,25,
          30,27,31,35,30,31,35,38,41,35,36,37,38,54,46,41,45,43,53,49,46,57,48,
          62,55,51,55,56,76,55,60,57,63,71,60,80,62,63,77,65,66,67
COMMENT (the conjecture):
  Conjecture: only the integers k in {1, 3, 4, 6, 8, 12, 24} have the property
  that the sum of the divisors of (k*n-1)/k is always an integer.
  - _Robert G. Wilson v_, Dec 25 2016
FORMULA:
  24 * a(n) = sum of the divisors of A183010(n).
  a(n) = A280097(n)/24. - _Omar E. Pol_, Dec 25 2016
```

The comment's wording "the sum of the divisors of (k*n-1)/k" is read, as the
NAME line and the formula `24 * a(n) = sigma(24 n - 1)` dictate, as
"`sigma(k n - 1) / k` is an integer", i.e. `k ∣ sigma(k n - 1)`, for every
`n ≥ 1` with `k n - 1 ≥ 1` (for `k = 1, n = 1` the argument `0` is excluded).

## Literature status (triage)

Open as far as the triage could tell: the `k = 24` direction is the classical
fact cited in A280097 (every divisor `d` of `N ≡ -1 (mod 24)` satisfies
`d + N/d ≡ 0 (mod 24)`), but the converse appears in the entry only as
Wilson's 2016 conjecture, and a web search found no published proof of the
full equivalence (it may be folklore).  Computation (2026-10-21): for
`k ≤ 400` and `k n - 1 ≤ 60000`, exactly `k ∈ {1,3,4,6,8,12,24}` pass.

## Proof (kernel-checked below)

* If: for `k ∈ {3,4,6,8,12,24}`, every `x, y ∈ ZMod k` with `x y = -1`
  satisfy `x + y = 0` and `x ≠ y` (finite check).  Pair each divisor `d` of
  `N = k n - 1` with `N / d` (`Finset.sum_involution`).
* Only if: `k = 2` fails at `n = 1`.  Otherwise, given a unit `u` of
  `ZMod k`, Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`)
  gives distinct primes `p ≡ u`, `q ≡ -u⁻¹`; then `N = p q ≡ -1` and
  `σ(N) = (1 + p)(1 + q) ≡ u - u⁻¹`, so `u² = 1`.  Every unit of `ZMod k`
  squaring to `1` forces `k ∣ 24` (pass to `ZMod 16`, `ZMod 9`, `ZMod p`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A280098SigmaDivisibility

open ArithmeticFunction

/-! ## Definition layer -/

/-- A280098 (offset 1): `a(n) = sigma(24 n - 1) / 24`. -/
def a (n : ℕ) : ℕ := sigma 1 (24 * n - 1) / 24

/-- Wilson's property of `k`: `k ∣ sigma(k n - 1)` for every `n` with
`k n > 1` (so the argument `k n - 1` is a positive integer). -/
def SigmaDivProperty (k : ℕ) : Prop :=
  ∀ n : ℕ, 1 < k * n → k ∣ sigma 1 (k * n - 1)

/-- The conjectured exceptional set `{1, 3, 4, 6, 8, 12, 24}`. -/
def exceptionalSet : Finset ℕ := {1, 3, 4, 6, 8, 12, 24}

/-! ### Ground truth -/

example : (List.range 10).map (fun i => a (i + 1)) = [1, 2, 3, 5, 6, 7, 7, 8, 11, 10] := by
  simp only [a, sigma_one_apply]; decide

example : 24 * a 19 = sigma 1 455 := by simp only [a, sigma_one_apply]; decide

/-! ## The "if" direction -/

/-- Finite table: in `ZMod k` for `k ∈ {3,4,6,8,12,24}`, if `x * y = -1` then
`x + y = 0` and `x ≠ y`. -/
theorem add_eq_zero_and_ne_of_mul_eq_neg_one (k : ℕ)
    (hk : k ∈ ({3, 4, 6, 8, 12, 24} : Finset ℕ)) :
    ∀ x y : ZMod k, x * y = -1 → x + y = 0 ∧ x ≠ y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Divisor pairing: if `x * y = -1 → x + y = 0 ∧ x ≠ y` in `ZMod k` and
`N ≡ -1 (mod k)`, then `k ∣ sigma(N)`. -/
theorem dvd_sigma_of_pairing (k N : ℕ)
    (hT : ∀ x y : ZMod k, x * y = -1 → x + y = 0 ∧ x ≠ y)
    (hN : (N : ZMod k) = -1) : k ∣ sigma 1 N := by
  rw [← ZMod.natCast_eq_zero_iff, sigma_one_apply, Nat.cast_sum]
  have hmul : ∀ d ∈ N.divisors, (d : ZMod k) * ((N / d : ℕ) : ZMod k) = -1 := by
    intro d hd
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), hN]
  refine Finset.sum_involution (fun d _ => N / d) ?_ ?_ ?_ ?_
  · intro d hd
    exact (hT _ _ (hmul d hd)).1
  · intro d hd _ heq
    exact (hT _ _ (hmul d hd)).2 (by rw [heq])
  · intro d hd
    have hN0 : N ≠ 0 := (Nat.mem_divisors.1 hd).2
    exact Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hN0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (Nat.mem_divisors.1 hd).2

/-- The "if" direction: every `k ∈ {1,3,4,6,8,12,24}` has Wilson's property. -/
theorem sigmaDivProperty_of_mem (k : ℕ) (hk : k ∈ exceptionalSet) :
    SigmaDivProperty k := by
  intro n hn
  rcases Finset.mem_insert.1 hk with rfl | hk'
  · exact one_dvd _
  have hN : ((k * n - 1 : ℕ) : ZMod k) = -1 := by
    rw [Nat.cast_sub hn.le, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one,
      zero_sub]
  exact dvd_sigma_of_pairing k _ (add_eq_zero_and_ne_of_mul_eq_neg_one k hk') hN

/-! ## The "only if" direction -/

/-- `sigma(p q) = (p + 1)(q + 1)` for distinct primes `p, q`. -/
theorem sigma_one_mul_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigma 1 (p * q) = (p + 1) * (q + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hp hq).2 hpq),
    sigma_one_apply, sigma_one_apply, Nat.Prime.sum_divisors hp, Nat.Prime.sum_divisors hq]

/-- Wilson's property forces every unit of `ZMod k` to square to `1`
(via Dirichlet's theorem on primes in arithmetic progressions). -/
theorem units_sq_eq_one_of_sigmaDivProperty {k : ℕ} (hk : 0 < k)
    (hP : SigmaDivProperty k) (u : (ZMod k)ˣ) : u ^ 2 = 1 := by
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨p, -, hp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0
  obtain ⟨q, hqp, hq, hqu⟩ := Nat.forall_exists_prime_gt_and_eq_mod (-u⁻¹).isUnit p
  have hinv : (u : ZMod k) * ((u⁻¹ : (ZMod k)ˣ) : ZMod k) = 1 := Units.mul_inv u
  have hN : ((p * q + 1 : ℕ) : ZMod k) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hpu, hqu, Units.val_neg, Nat.cast_one]
    linear_combination (-1 : ZMod k) * hinv
  obtain ⟨n, hn⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hN
  have h1 : 1 < k * n := by
    rw [← hn]
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    nlinarith
  have hdiv := hP n h1
  rw [← hn, Nat.add_sub_cancel, sigma_one_mul_of_prime hp hq (by omega)] at hdiv
  have h0 := (ZMod.natCast_eq_zero_iff _ _).2 hdiv
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add, hpu, hqu, Units.val_neg, Nat.cast_one] at h0
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  linear_combination (u : ZMod k) * h0 + ((u : ZMod k) + 1) * hinv

/-- Squaring-to-one of all units passes to divisors (units of `ZMod` surject). -/
theorem units_sq_eq_one_of_dvd {m k : ℕ} [NeZero k] (hmk : m ∣ k)
    (H : ∀ u : (ZMod k)ˣ, u ^ 2 = 1) (u : (ZMod m)ˣ) : u ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hmk u
  rw [← map_pow, H, map_one]

/-- In `ZMod 16`, the unit `3` does not square to `1`. -/
theorem not_units_sq_sixteen : ¬ ∀ u : (ZMod 16)ˣ, u ^ 2 = 1 := by
  intro H
  have h := congrArg Units.val (H (ZMod.unitOfCoprime 3 (by norm_num)))
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h
  exact absurd h (by decide)

/-- In `ZMod 9`, the unit `2` does not square to `1`. -/
theorem not_units_sq_nine : ¬ ∀ u : (ZMod 9)ˣ, u ^ 2 = 1 := by
  intro H
  have h := congrArg Units.val (H (ZMod.unitOfCoprime 2 (by norm_num)))
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h
  exact absurd h (by decide)

/-- For a prime `p ≥ 5`, the unit `2` of `ZMod p` does not square to `1`. -/
theorem not_units_sq_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ ∀ u : (ZMod p)ˣ, u ^ 2 = 1 := by
  intro H
  have h := congrArg Units.val
    (H (ZMod.unitOfCoprime 2 ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))))
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow,
    ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ 2 < p), Nat.mod_eq_of_lt (by omega : 1 < p)] at h
  omega

/-- If every unit of `ZMod k` squares to `1`, then `k ∣ 24`. -/
theorem dvd_twentyFour_of_units_sq {k : ℕ} (hk : 0 < k)
    (H : ∀ u : (ZMod k)ˣ, u ^ 2 = 1) : k ∣ 24 := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have h16 : ¬ 16 ∣ k := fun h => not_units_sq_sixteen (units_sq_eq_one_of_dvd h H)
  have h9 : ¬ 9 ∣ k := fun h => not_units_sq_nine (units_sq_eq_one_of_dvd h H)
  have hsmall : ∀ p, p.Prime → p ∣ k → p ≤ 3 := by
    intro p hp hpk
    by_contra hlt
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    exact not_units_sq_prime hp (by omega) (units_sq_eq_one_of_dvd hpk H)
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
  obtain ⟨b, r, hr3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.pos.ne' 3 (by norm_num)
  have hr : r = 1 := by
    by_contra hr1
    have hpr := Nat.minFac_prime hr1
    have hdvd : r.minFac ∣ 2 ^ a * (3 ^ b * r) :=
      Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.minFac_dvd r) _) _
    have hle := hsmall _ hpr hdvd
    have hodd : Odd r := Nat.Odd.of_mul_right hm
    have h2 : r.minFac ≠ 2 := by
      intro h
      have h2r : 2 ∣ r := h ▸ Nat.minFac_dvd r
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2r)
    have h3 : r.minFac ≠ 3 := fun h => hr3 (h ▸ Nat.minFac_dvd r)
    have hpr2 := hpr.two_le
    omega
  subst hr
  have ha : a ≤ 3 := by
    by_contra ha
    exact h16 (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega : 4 ≤ a)) _)
  have hb : b ≤ 1 := by
    by_contra hb
    exact h9 (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.pow_dvd_pow 3 (by omega : 2 ≤ b)) _) _)
  interval_cases a <;> interval_cases b <;> decide

/-- `k = 2` fails Wilson's property at `n = 1`: `sigma(1) = 1` is odd. -/
theorem not_sigmaDivProperty_two : ¬ SigmaDivProperty 2 := by
  intro hP
  have h := hP 1 (by norm_num)
  rw [sigma_one_apply] at h
  exact absurd h (by decide)

/-! ## The conjecture -/

/-- **Wilson's conjecture (A280098, Robert G. Wilson v, Dec 25 2016)**, proved.

Verbatim: "Conjecture: only the integers k in {1, 3, 4, 6, 8, 12, 24} have the
property that the sum of the divisors of (k*n-1)/k is always an integer."

Formal reading: for `k ≥ 1`, `k ∣ sigma(k n - 1)` for every `n` with
`1 < k n` if and only if `k ∈ {1, 3, 4, 6, 8, 12, 24}`.  The guard `0 < k`
is needed: for `k = 0` the property holds vacuously. -/
theorem sigmaDivProperty_iff (k : ℕ) (hk : 0 < k) :
    SigmaDivProperty k ↔ k ∈ exceptionalSet := by
  refine ⟨fun hP => ?_, sigmaDivProperty_of_mem k⟩
  have h24 := dvd_twentyFour_of_units_sq hk (units_sq_eq_one_of_sigmaDivProperty hk hP)
  have h2 : k ≠ 2 := by
    rintro rfl
    exact not_sigmaDivProperty_two hP
  have hle : k ≤ 24 := Nat.le_of_dvd (by norm_num) h24
  interval_cases k <;> simp_all [exceptionalSet]

/-- Corollary (the `k = 24` case, the defining property of A280098): for
`n ≥ 1`, `24 * a(n) = sigma(24 n - 1)`. -/
theorem twentyFour_mul_a (n : ℕ) (hn : 1 ≤ n) : 24 * a n = sigma 1 (24 * n - 1) :=
  Nat.mul_div_cancel' (sigmaDivProperty_of_mem 24 (by decide) n (by omega))

end Candidates.A280098SigmaDivisibility
