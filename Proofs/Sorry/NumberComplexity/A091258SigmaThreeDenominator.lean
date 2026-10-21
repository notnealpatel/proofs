/-
# A091258 — denominators of sigma_3(n)/sigma(n) are exactly A004611

## OEIS source (retrieved with `oeis show A091258`, 2026-10-21)

```
A091258
NAME:     Denominator of sigma_3(n)/sigma(n).
TERMS:    1,1,1,7,1,1,1,1,13,1,1,1,1,1,1,1,1,13,1,1,1,1,1,1,31,1,1,7,1,1,1,7,
          1,1,1,91,1,1,1,1,1,1,1,7,13,1,1,1,19,31,1,7,...
KEYWORDS: easy,nonn,frac
PROGRAM:  (PARI) a(n) = denominator(sigma(n, 3)/sigma(n));
COMMENT (the conjecture):
  Conjecture: The set of distinct terms is A004611. - _Michel Marcus_, Aug 10 2024

A004611
NAME:     Divisible only by primes congruent to 1 mod 3.
TERMS:    1,7,13,19,31,37,43,49,61,67,73,79,91,97,103,109,127,133,139,...
```

## Status

Triage: open (the entry gives no proof; no proof found in the literature by
the triage).  Computation (2026-10-21): every reduced denominator for
`n ≤ 400000` has only prime factors `≡ 1 (mod 3)`.

This module proves the conjecture, both inclusions, with no `sorry`:

* `⊆` — local identity `σ₁(p^k)·(X²+X+1) = σ₃(p^k)·(p²+p+1)` with
  `X = p^(k+1)`; the local denominator divides `p²+p+1`, whose prime factors
  other than `3` are `1 mod 3`, and `3` cancels since `9 ∤ p²+p+1`.
* `⊇` — a strengthened realizability statement (`Realizable`) closed under
  products, and for a prime `q ≡ 1 (mod 3)` the witness `n = p²·r` with
  primes `p, r` from Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`):
  `v_q(p²+p+1) = 1` and `r ≡ -p` modulo the cofactor `(p²+p+1)/q`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A091258SigmaThreeDenominator

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Definition layer -/

/-- The rational number `σ₃(n)/σ₁(n)` (the value at `n = 0` is the junk `0/0 = 0`;
every statement below restricts to `0 < n`). -/
noncomputable def sigmaRatio (n : ℕ) : ℚ := (σ 3 n : ℚ) / σ 1 n

/-- OEIS A091258: the reduced denominator of `σ₃(n)/σ₁(n)`. -/
noncomputable def a091258 (n : ℕ) : ℕ := (sigmaRatio n).den

/-- OEIS A004611: positive integers all of whose prime factors are `≡ 1 (mod 3)`
(`1` included). -/
def IsA004611 (m : ℕ) : Prop := 0 < m ∧ ∀ q ∈ m.primeFactors, q % 3 = 1

/-! ### Ground truth against the listed terms -/

example : a091258 1 = 1 := by
  rw [a091258, sigmaRatio, show σ 3 1 = 1 by decide, show σ 1 1 = 1 by decide]
  norm_num

example : a091258 4 = 7 := by
  rw [a091258, sigmaRatio, show σ 3 4 = 73 by decide, show σ 1 4 = 7 by decide]
  norm_num

example : a091258 6 = 1 := by
  rw [a091258, sigmaRatio, show σ 3 6 = 252 by decide, show σ 1 6 = 12 by decide]
  norm_num

example : a091258 9 = 13 := by
  rw [a091258, sigmaRatio, show σ 3 9 = 757 by decide, show σ 1 9 = 13 by decide]
  norm_num

example : a091258 36 = 91 := by
  rw [a091258, sigmaRatio, show σ 3 36 = 55261 by decide, show σ 1 36 = 91 by decide]
  norm_num

example : IsA004611 1 := ⟨one_pos, by simp⟩

example : IsA004611 91 := ⟨by norm_num, by simp [Nat.primeFactors]⟩

example : ¬ IsA004611 3 := fun h => by simpa using h.2 3 (by simp [Nat.primeFactors])

example : ¬ IsA004611 14 := fun h => by simpa using h.2 2 (by simp [Nat.primeFactors])

/-! ## Inclusion: every denominator lies in A004611 -/

/-- A prime `ℓ ≠ 3` dividing `p² + p + 1` is `≡ 1 (mod 3)`: `p` has order `3` modulo `ℓ`. -/
theorem prime_mod_three_of_dvd {ℓ p : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hdvd : ℓ ∣ p ^ 2 + p + 1) : ℓ % 3 = 1 := by
  haveI := Fact.mk hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu : (p : ZMod ℓ) ^ 2 + p + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (p ^ 2 + p + 1) ℓ).2 hdvd
    push_cast at this
    exact this
  have hu3 : (p : ZMod ℓ) ^ 3 = 1 := by linear_combination ((p : ZMod ℓ) - 1) * hu
  have hne1 : (p : ZMod ℓ) ≠ 1 := by
    intro h1
    have h3 : ((3 : ℕ) : ZMod ℓ) = 0 := by
      rw [h1] at hu
      push_cast
      linear_combination hu
    have hdvd3 : ℓ ∣ 3 := (ZMod.natCast_eq_zero_iff 3 ℓ).1 h3
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hdvd3)
  have hne0 : (p : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0] at hu
    norm_num at hu
  have hord : orderOf (p : ZMod ℓ) = 3 := orderOf_eq_prime hu3 hne1
  have hdvd' := ZMod.orderOf_dvd_card_sub_one hne0
  rw [hord] at hdvd'
  have h2 := hℓ.two_le
  omega

/-- `9` never divides `p² + p + 1`. -/
theorem not_nine_dvd (p : ℕ) : ¬ 9 ∣ p ^ 2 + p + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h : (p ^ 2 + p + 1) % 9 = ((p % 9) ^ 2 + p % 9 + 1) % 9 := by
    simp [Nat.add_mod, Nat.pow_mod]
  rw [h]
  have : p % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases (p % 9) <;> norm_num

/-- Local identity: `σ₁(p^k)·(X²+X+1) = σ₃(p^k)·(p²+p+1)` with `X = p^(k+1)`. -/
theorem sigma_prime_pow_identity {p : ℕ} (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) * ((p ^ (k + 1)) ^ 2 + p ^ (k + 1) + 1) = σ 3 (p ^ k) * (p ^ 2 + p + 1) := by
  rw [sigma_apply_prime_pow hp, sigma_apply_prime_pow hp]
  have h1 : (p : ℤ) - 1 ≠ 0 := by
    have := hp.two_le
    omega
  have g1 := geom_sum_mul (p : ℤ) (k + 1)
  have g3 := geom_sum_mul ((p : ℤ) ^ 3) (k + 1)
  have e1 : ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ (j * 1) = ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
    simp
  have e3 : ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ (j * 3) = ∑ j ∈ Finset.range (k + 1), ((p : ℤ) ^ 3) ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  zify
  rw [e1, e3]
  apply mul_right_cancel₀ h1
  have hX : ((p : ℤ) ^ 3) ^ (k + 1) = ((p : ℤ) ^ (k + 1)) ^ 3 := by ring
  rw [hX] at g3
  linear_combination (((p : ℤ) ^ (k + 1)) ^ 2 + (p : ℤ) ^ (k + 1) + 1) * g1 - g3

/-- The reduced denominator of `a / b` for naturals `a`, `b ≠ 0` is `b / gcd(b, a)`. -/
theorem den_natCast_div (a b : ℕ) (hb : b ≠ 0) : ((a : ℚ) / b).den = b / Nat.gcd b a := by
  have h := Rat.den_divInt (a : ℤ) (b : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  rw [h, if_neg (by exact_mod_cast hb)]
  simp [Int.gcd_natCast_natCast]

/-- If `3 ∣ p² + p + 1` then `3 ∣ X² + X + 1` for every power `X = p^(k+1)`. -/
theorem three_dvd_of_three_dvd {p : ℕ} (k : ℕ) (h : 3 ∣ p ^ 2 + p + 1) :
    3 ∣ (p ^ (k + 1)) ^ 2 + p ^ (k + 1) + 1 := by
  have hp : p % 3 = 1 := by
    have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hmod : (p ^ 2 + p + 1) % 3 = ((p % 3) ^ 2 + p % 3 + 1) % 3 := by
      simp [Nat.add_mod, Nat.pow_mod]
    rw [Nat.dvd_iff_mod_eq_zero, hmod] at h
    interval_cases hr : (p % 3) <;> simp_all
  have hpm : p ≡ 1 [MOD 3] := hp
  have hX : p ^ (k + 1) ≡ 1 [MOD 3] := by simpa using hpm.pow (k + 1)
  have hA : (p ^ (k + 1)) ^ 2 + p ^ (k + 1) + 1 ≡ 1 ^ 2 + 1 + 1 [MOD 3] :=
    ((hX.pow 2).add hX).add_right 1
  exact (Nat.modEq_zero_iff_dvd.1 (hA.trans (by decide)))

/-- Local step: every prime factor of the reduced denominator of
`σ₃(p^k)/σ₁(p^k)` is `1 mod 3`. -/
theorem den_local_prime_mod_three {p : ℕ} (hp : p.Prime) (k ℓ : ℕ) (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ ((σ 3 (p ^ k) : ℚ) / σ 1 (p ^ k)).den) : ℓ % 3 = 1 := by
  set X := p ^ (k + 1) with hXdef
  set a := X ^ 2 + X + 1 with ha
  set b := p ^ 2 + p + 1 with hb
  have hb0 : b ≠ 0 := by positivity
  have hs1 : (σ 1 (p ^ k)) ≠ 0 := (sigma_pos 1 (p ^ k) (pow_ne_zero _ hp.ne_zero)).ne'
  have hid := sigma_prime_pow_identity hp k
  have hq : ((σ 3 (p ^ k) : ℚ) / σ 1 (p ^ k)) = (a : ℚ) / b := by
    rw [div_eq_div_iff (by exact_mod_cast hs1) (by exact_mod_cast hb0)]
    have hid' : σ 3 (p ^ k) * b = a * σ 1 (p ^ k) := by rw [mul_comm a]; exact hid.symm
    exact_mod_cast hid'
  rw [hq, den_natCast_div a b hb0] at hdvd
  have hgb : Nat.gcd b a ∣ b := Nat.gcd_dvd_left b a
  have hbeq : b = Nat.gcd b a * (b / Nat.gcd b a) := (Nat.mul_div_cancel' hgb).symm
  have hℓb : ℓ ∣ b := hdvd.trans (Nat.div_dvd_of_dvd hgb)
  by_cases hℓ3 : ℓ = 3
  · exfalso
    subst hℓ3
    have h3a : 3 ∣ a := three_dvd_of_three_dvd k hℓb
    have h3g : 3 ∣ Nat.gcd b a := Nat.dvd_gcd hℓb h3a
    have h9 : 9 ∣ b := by
      rw [hbeq]
      exact (Nat.mul_dvd_mul h3g hdvd : 3 * 3 ∣ _)
    exact not_nine_dvd p h9
  · exact prime_mod_three_of_dvd hℓ hℓ3 hℓb

/-- The reduced denominator of a finite product divides the product of the denominators. -/
theorem den_prod_dvd {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℚ) :
    (∏ i ∈ s, g i).den ∣ ∏ i ∈ s, (g i).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- Multiplicativity: `σ₃(n)/σ₁(n)` is the product of its prime-power local factors. -/
theorem sigma_ratio_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ((σ 3 n : ℚ) / σ 1 n) =
      ∏ p ∈ n.primeFactors, ((σ 3 (p ^ n.factorization p) : ℚ) / σ 1 (p ^ n.factorization p)) := by
  rw [IsMultiplicative.multiplicative_factorization (σ 3) isMultiplicative_sigma hn,
    IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hn,
    Finsupp.prod, Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Nat.cast_prod,
    Finset.prod_div_distrib]

/-- Every prime factor of the reduced denominator of `σ₃(n)/σ₁(n)`, `n ≠ 0`, is `≡ 1 (mod 3)`. -/
theorem den_prime_mod_three {n : ℕ} (hn : n ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ ((σ 3 n : ℚ) / σ 1 n).den) : ℓ % 3 = 1 := by
  rw [sigma_ratio_eq_prod hn] at hdvd
  obtain ⟨p, hp, hℓp⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1
    (hdvd.trans (den_prod_dvd _ _))
  exact den_local_prime_mod_three (Nat.prime_of_mem_primeFactors hp) _ ℓ hℓ hℓp

/-! ## Surjectivity: every member of A004611 is a denominator -/

/-- For a prime `q ≡ 1 (mod 3)`, `X² + X + 1` has a root modulo `q` (Cauchy's theorem in `(ZMod q)ˣ`). -/
theorem exists_root_mod_prime {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    ∃ w : ℕ, q ∣ w ^ 2 + w + 1 := by
  haveI := Fact.mk hq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Fintype.card (ZMod q)ˣ := by
    rw [ZMod.card_units]
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hg3 : ((g : ZMod q)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have hg1 : (g : ZMod q) ≠ 1 := by
    intro h1
    have : g = 1 := Units.ext h1
    rw [this, orderOf_one] at hg
    omega
  have hroot : (g : ZMod q) ^ 2 + g + 1 = 0 := by
    have hmul : ((g : ZMod q) - 1) * ((g : ZMod q) ^ 2 + g + 1) = 0 := by
      linear_combination hg3
    exact (mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hg1)
  refine ⟨(g : ZMod q).val, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hroot

/-- For a prime `q ≡ 1 (mod 3)` there is `w` with `q ∣ w² + w + 1` and `q² ∤ w² + w + 1`. -/
theorem exists_exact_root_mod_prime {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    ∃ w : ℕ, q ∣ w ^ 2 + w + 1 ∧ ¬ q ^ 2 ∣ w ^ 2 + w + 1 := by
  obtain ⟨w, hw⟩ := exists_root_mod_prime hq hq3
  by_cases hw2 : q ^ 2 ∣ w ^ 2 + w + 1
  · refine ⟨w + q, ?_, ?_⟩
    · have he : (w + q) ^ 2 + (w + q) + 1 = (w ^ 2 + w + 1) + q * (2 * w + 1 + q) := by ring
      rw [he]
      exact dvd_add hw (dvd_mul_right _ _)
    · intro h
      have he : (w + q) ^ 2 + (w + q) + 1 = (w ^ 2 + w + 1) + q * (2 * w + 1) + q ^ 2 := by ring
      rw [he] at h
      have h1 : q ^ 2 ∣ q * (2 * w + 1) :=
        (Nat.dvd_add_right hw2).1 ((Nat.dvd_add_left (dvd_refl (q ^ 2))).1 h)
      have h2 : q ∣ 2 * w + 1 := by
        rw [pow_two] at h1
        exact Nat.dvd_of_mul_dvd_mul_left hq.pos h1
      have h3 : q ∣ (2 * w + 1) ^ 2 + 3 := by
        have : (2 * w + 1) ^ 2 + 3 = 4 * (w ^ 2 + w + 1) := by ring
        rw [this]
        exact dvd_mul_of_dvd_right hw _
      have h4 : q ∣ 3 := (Nat.dvd_add_right (dvd_pow h2 two_ne_zero)).1 h3
      have h5 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h4
      omega
  · exact ⟨w, hw, hw2⟩

/-- Dirichlet's theorem with two coprime moduli: arbitrarily large primes in prescribed unit
residue classes modulo `M₁` and `M₂`. -/
theorem exists_prime_modEq (M₁ M₂ a₁ a₂ B : ℕ) (hM : Nat.Coprime M₁ M₂) (hM0 : M₁ * M₂ ≠ 0)
    (h₁ : Nat.Coprime a₁ M₁) (h₂ : Nat.Coprime a₂ M₂) :
    ∃ p, B < p ∧ p.Prime ∧ p ≡ a₁ [MOD M₁] ∧ p ≡ a₂ [MOD M₂] := by
  obtain ⟨c, hc₁, hc₂⟩ := Nat.chineseRemainder hM a₁ a₂
  have hc : Nat.Coprime c (M₁ * M₂) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, hc₁.gcd_eq]; exact h₁
    · rw [Nat.Coprime, hc₂.gcd_eq]; exact h₂
  haveI : NeZero (M₁ * M₂) := ⟨hM0⟩
  have hu : IsUnit (c : ZMod (M₁ * M₂)) := (ZMod.isUnit_iff_coprime c _).2 hc
  obtain ⟨p, hpB, hp, hpc⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu B
  have hpc' : p ≡ c [MOD M₁ * M₂] := (ZMod.natCast_eq_natCast_iff p c _).1 hpc
  exact ⟨p, hpB, hp, (hpc'.of_mul_right M₂).trans hc₁, (hpc'.of_mul_left M₁).trans hc₂⟩

/-- Strengthened surjectivity predicate: for every `N > 0` with `3 ∤ N` and every bound `B`,
`m` is the reduced denominator of `σ₃(n)/σ₁(n)` for some `n > 0` whose prime factors all exceed
`B` and whose reduced numerator is coprime to `N`. -/
def Realizable (m : ℕ) : Prop :=
  ∀ N B : ℕ, 0 < N → ¬ 3 ∣ N → ∃ n, 0 < n ∧ (∀ ℓ, ℓ.Prime → ℓ ∣ n → B < ℓ) ∧
    (sigmaRatio n).den = m ∧ Nat.Coprime (sigmaRatio n).num.natAbs N

/-- `σ₃/σ₁` is multiplicative on coprime arguments. -/
theorem sigmaRatio_mul {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaRatio (m * n) = sigmaRatio m * sigmaRatio n := by
  simp only [sigmaRatio]
  rw [isMultiplicative_sigma.map_mul_of_coprime h, isMultiplicative_sigma.map_mul_of_coprime h,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

/-- If the numerator of each factor is coprime to the denominator of the other, the reduced
fraction of the product has denominator and numerator the products. -/
theorem den_num_mul_of_coprime (x y : ℚ) (hxy : Nat.Coprime x.num.natAbs y.den)
    (hyx : Nat.Coprime y.num.natAbs x.den) :
    (x * y).den = x.den * y.den ∧ (x * y).num = x.num * y.num := by
  have hg : Nat.gcd (x.num * y.num).natAbs (x.den * y.den) = 1 := by
    rw [Int.natAbs_mul]
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right x.reduced hxy)
      (Nat.Coprime.mul_right hyx y.reduced)
  rw [Rat.mul_den, Rat.mul_num, hg]
  simp

/-- `1` is realizable (by `n = 1`). -/
theorem realizable_one : Realizable 1 := by
  intro N B _ _
  refine ⟨1, one_pos, fun ℓ hℓ hdvd => absurd (Nat.dvd_one.1 hdvd) hℓ.one_lt.ne', ?_, ?_⟩
  · simp [sigmaRatio]
  · simp [sigmaRatio]

/-- Realizability is closed under products of positive factors prime to `3`. -/
theorem realizable_mul {m₁ m₂ : ℕ} (h₁ : Realizable m₁) (h₂ : Realizable m₂)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (h3₁ : ¬ 3 ∣ m₁) (h3₂ : ¬ 3 ∣ m₂) :
    Realizable (m₁ * m₂) := by
  intro N B hN hN3
  have h3mul : ∀ a b : ℕ, ¬ 3 ∣ a → ¬ 3 ∣ b → ¬ 3 ∣ a * b := fun a b ha hb h =>
    (Nat.prime_three.dvd_mul.1 h).elim ha hb
  obtain ⟨n₁, hn₁, hB₁, hd₁, hc₁⟩ := h₁ (N * m₂) B (Nat.mul_pos hN hm₂) (h3mul _ _ hN3 h3₂)
  obtain ⟨n₂, hn₂, hB₂, hd₂, hc₂⟩ := h₂ (N * m₁) (B + n₁) (Nat.mul_pos hN hm₁)
    (h3mul _ _ hN3 h3₁)
  have hcop : Nat.Coprime n₁ n₂ := by
    refine Nat.coprime_of_dvd fun k hk hk₁ hk₂ => ?_
    have := hB₂ k hk hk₂
    have := Nat.le_of_dvd hn₁ hk₁
    omega
  have hx := den_num_mul_of_coprime (sigmaRatio n₁) (sigmaRatio n₂)
    (by rw [hd₂]; exact Nat.Coprime.coprime_mul_left_right hc₁)
    (by rw [hd₁]; exact Nat.Coprime.coprime_mul_left_right hc₂)
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, fun ℓ hℓ hdvd => ?_, ?_, ?_⟩
  · rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h | h
    · exact hB₁ ℓ hℓ h
    · have := hB₂ ℓ hℓ h
      omega
  · rw [sigmaRatio_mul hcop, hx.1, hd₁, hd₂]
  · rw [sigmaRatio_mul hcop, hx.2, Int.natAbs_mul]
    exact Nat.Coprime.mul_left (Nat.Coprime.coprime_mul_right_right hc₁)
      (Nat.Coprime.coprime_mul_right_right hc₂)

/-- `σ₃(p²) = 1 + p³ + p⁶` for a prime `p`. -/
theorem sigma_three_prime_sq {p : ℕ} (hp : p.Prime) : σ 3 (p ^ 2) = 1 + p ^ 3 + p ^ 6 := by
  rw [sigma_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- `σ₁(p²) = 1 + p + p²` for a prime `p`. -/
theorem sigma_one_prime_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- `σ_k(p) = 1 + p^k` for a prime `p`. -/
theorem sigma_prime (k : ℕ) {p : ℕ} (hp : p.Prime) : σ k p = 1 + p ^ k := by
  have h := sigma_apply_prime_pow (k := k) (i := 1) hp
  rw [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ]

/-- Every prime `q ≡ 1 (mod 3)` is realizable, by `n = p²·r` with Dirichlet primes `p ≡ w
(mod q²)`, `p ≡ 2 (mod 3)`, `p ≡ 1` modulo the prime-to-`q` part of `N`, and `r ≡ -p` modulo
`(p²+p+1)/q`, `r ≡ 1 (mod 3qN)`. -/
theorem realizable_prime {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) : Realizable q := by
  intro N B hN hN3
  obtain ⟨w, hw1, hw2⟩ := exists_exact_root_mod_prime hq hq3
  obtain ⟨a, N', hqN', hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.one_lt.ne'
  have hN'N : N' ∣ N := hNeq ▸ dvd_mul_left _ _
  have hN'0 : N' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hNeq
    omega
  have h3N' : Nat.Coprime 3 N' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hN3 (h.trans hN'N)
  have hq_ne3 : q ≠ 3 := by
    rintro rfl
    norm_num at hq3
  have hq3c : Nat.Coprime q 3 := (Nat.coprime_primes hq Nat.prime_three).2 hq_ne3
  have hqN'c : Nat.Coprime q N' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN'
  -- the residue of `p` modulo `3 * N'`
  obtain ⟨c, hc3, hcN'⟩ := Nat.chineseRemainder h3N' 2 1
  have hc : Nat.Coprime c (3 * N') := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, hc3.gcd_eq]
      norm_num
    · rw [Nat.Coprime, hcN'.gcd_eq]
      exact Nat.coprime_one_left _
  have hwq : Nat.Coprime w (q ^ 2) := by
    refine Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 ?_))
    intro hqw
    have h' : w ^ 2 + w + 1 = w * (w + 1) + 1 := by ring
    rw [h'] at hw1
    exact hq.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_mul_of_dvd_left hqw _)).1 hw1))
  have hM : Nat.Coprime (q ^ 2) (3 * N') :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right hq3c hqN'c)
  obtain ⟨p, hpB, hp, hpw, hpc⟩ := exists_prime_modEq (q ^ 2) (3 * N') w c B hM
    (mul_ne_zero (pow_ne_zero 2 hq.ne_zero) (mul_ne_zero three_ne_zero hN'0)) hwq hc
  have hp3 : p ≡ 2 [MOD 3] := (hpc.of_mul_right N').trans hc3
  have hpN' : p ≡ 1 [MOD N'] := (hpc.of_mul_left 3).trans hcN'
  -- the local denominator `D = p^2 + p + 1 = q * R`
  set D := p ^ 2 + p + 1 with hD
  have hDw : D ≡ w ^ 2 + w + 1 [MOD q ^ 2] := ((hpw.pow 2).add hpw).add_right 1
  have hqD : q ∣ D := (hDw.dvd_iff (dvd_pow_self q two_ne_zero)).2 hw1
  have hq2D : ¬ q ^ 2 ∣ D := fun h => hw2 ((hDw.dvd_iff dvd_rfl).1 h)
  obtain ⟨R, hR⟩ := hqD
  have hqR : ¬ q ∣ R := fun h => hq2D (by rw [hR, pow_two]; exact Nat.mul_dvd_mul_left q h)
  have hR0 : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · rw [h, mul_zero] at hR
      omega
    · exact h
  have hRD : R ∣ D := Dvd.intro_left q hR.symm
  have hD3 : Nat.Coprime D 3 := by
    have h7 : D ≡ 2 ^ 2 + 2 + 1 [MOD 3] := ((hp3.pow 2).add hp3).add_right 1
    rw [Nat.Coprime, h7.gcd_eq]
    norm_num
  have hDN' : Nat.Coprime D N' := by
    have h3 : D ≡ 1 ^ 2 + 1 + 1 [MOD N'] := ((hpN'.pow 2).add hpN').add_right 1
    rw [Nat.Coprime, h3.gcd_eq]
    exact h3N'
  have hDp : Nat.Coprime D p := by
    have h0 : p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 dvd_rfl
    have h1 : D ≡ 0 ^ 2 + 0 + 1 [MOD p] := ((h0.pow 2).add h0).add_right 1
    rw [Nat.Coprime, h1.gcd_eq]
    simp
  have hRq : Nat.Coprime R q := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqR)
  have hRN : Nat.Coprime R N := by
    rw [hNeq]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right a hRq) (hDN'.coprime_dvd_left hRD)
  have hRK : Nat.Coprime R (3 * q * N) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (hD3.coprime_dvd_left hRD) hRq) hRN
  have ha₁ : Nat.Coprime ((R - 1) * p) R := by
    refine Nat.Coprime.mul_left ?_ (Nat.coprime_comm.1 (hDp.coprime_dvd_left hRD))
    obtain ⟨s, hs⟩ : ∃ s, R = s + 1 := ⟨R - 1, by omega⟩
    rw [hs]
    simp
  have hK0 : 3 * q * N ≠ 0 :=
    mul_ne_zero (mul_ne_zero three_ne_zero hq.ne_zero) hN.ne'
  obtain ⟨r, hrB, hr, hrR, hrK⟩ := exists_prime_modEq R (3 * q * N) ((R - 1) * p) 1 (B + p) hRK
    (mul_ne_zero hR0.ne' hK0) ha₁ (Nat.coprime_one_left _)
  have hpr : p ≠ r := by omega
  have hcop : Nat.Coprime (p ^ 2) r := Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp hr).2 hpr)
  -- the factor `E = r^2 - r + 1 = R * T` contributed by `r`
  have hRpr : (R : ℤ) ∣ (r : ℤ) + p := by
    have h := Nat.modEq_iff_dvd.1 hrR
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one] at h
    have he : ((r : ℤ) + p) = (R : ℤ) * p - (((R : ℤ) - 1) * p - r) := by ring
    rw [he]
    exact dvd_sub (dvd_mul_right _ _) h
  have hRDz : (R : ℤ) ∣ (p : ℤ) ^ 2 + p + 1 := by
    have := Int.natCast_dvd_natCast.2 hRD
    push_cast [hD] at this
    exact this
  have hRE : (R : ℤ) ∣ (r : ℤ) ^ 2 - r + 1 := by
    have he : (r : ℤ) ^ 2 - r + 1 = ((r : ℤ) + p) * (r - p - 1) + ((p : ℤ) ^ 2 + p + 1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hRpr _) hRDz
  obtain ⟨T, hT⟩ := hRE
  have hEK : IsCoprime ((r : ℤ) ^ 2 - r + 1) ((3 * q * N : ℕ) : ℤ) := by
    obtain ⟨s, hs⟩ := Nat.modEq_iff_dvd.1 hrK
    refine ⟨1, r * s, ?_⟩
    push_cast at hs ⊢
    linear_combination (-(r : ℤ)) * hs
  have hTK : IsCoprime T ((3 * q * N : ℕ) : ℤ) := by
    rw [hT] at hEK
    exact hEK.of_mul_left_right
  push_cast at hTK
  have hTq : Nat.Coprime T.natAbs q :=
    Int.isCoprime_iff_gcd_eq_one.1 (hTK.of_mul_right_left.of_mul_right_right)
  have hTN : Nat.Coprime T.natAbs N :=
    Int.isCoprime_iff_gcd_eq_one.1 hTK.of_mul_right_right
  -- the numerator factor `A = 1 + p^3 + p^6` contributed by `p^2`
  set A := 1 + p ^ 3 + p ^ 6 with hA
  have hp3D : p ^ 3 ≡ 1 [MOD D] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨1 - (p : ℤ), ?_⟩
    push_cast [hD]
    ring
  have hAD : A ≡ 1 + 1 + 1 ^ 2 [MOD D] := by
    have h6 : p ^ 6 = (p ^ 3) ^ 2 := by ring
    rw [hA, h6]
    exact (hp3D.add_left 1).add (hp3D.pow 2)
  have hAq : Nat.Coprime A q := by
    have h := hAD.of_dvd (Dvd.intro R hR.symm)
    rw [Nat.Coprime, h.gcd_eq]
    exact hq3c.symm
  have hAN' : Nat.Coprime A N' := by
    have h : A ≡ 1 + 1 ^ 3 + 1 ^ 6 [MOD N'] := ((hpN'.pow 3).add_left 1).add (hpN'.pow 6)
    rw [Nat.Coprime, h.gcd_eq]
    exact h3N'
  have hAN : Nat.Coprime A N := by
    rw [hNeq]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right a hAq) hAN'
  -- the ratio for `n = p^2 * r`
  have hratio : sigmaRatio (p ^ 2 * r) = (((A : ℤ) * T : ℤ) : ℚ) / ((q : ℤ) : ℚ) := by
    rw [sigmaRatio_mul hcop]
    simp only [sigmaRatio]
    rw [sigma_three_prime_sq hp, sigma_one_prime_sq hp, sigma_prime 3 hr, sigma_prime 1 hr]
    have hDq : (1 + (p : ℚ) + (p : ℚ) ^ 2) = (q : ℚ) * R := by
      have := congrArg (fun x : ℕ => (x : ℚ)) hR
      push_cast [hD] at this
      linear_combination this
    have hEq : ((r : ℚ) ^ 2 - r + 1) = (R : ℚ) * T := by exact_mod_cast hT
    have hr1 : (1 + (r : ℚ) ^ 1) ≠ 0 := by positivity
    have hD0 : (1 + (p : ℚ) + (p : ℚ) ^ 2) ≠ 0 := by positivity
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hAQ : (A : ℚ) = 1 + (p : ℚ) ^ 3 + (p : ℚ) ^ 6 := by
      rw [hA]
      push_cast
      ring
    push_cast
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hD0 hr1) hq0]
    linear_combination (-(A : ℚ) * T * (1 + r)) * hDq + ((A : ℚ) * q * (1 + r)) * hEq -
      ((q : ℚ) * (1 + (r : ℚ) ^ 3)) * hAQ
  have hcopAT : Nat.Coprime ((A : ℤ) * T).natAbs (q : ℤ).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.Coprime.mul_left hAq hTq
  have hq0z : (0 : ℤ) < q := by exact_mod_cast hq.pos
  refine ⟨p ^ 2 * r, Nat.mul_pos (pow_pos hp.pos 2) hr.pos, fun ℓ hℓ hdvd => ?_, ?_, ?_⟩
  · rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h)]
      exact hpB
    · rw [(Nat.prime_dvd_prime_iff_eq hℓ hr).1 h]
      omega
  · rw [hratio]
    exact_mod_cast Rat.den_div_eq_of_coprime hq0z hcopAT
  · rw [hratio, Rat.num_div_eq_of_coprime hq0z hcopAT, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.Coprime.mul_left hAN hTN

/-- Every member of A004611 is realizable (strong induction on the least prime factor). -/
theorem realizable_of_isA004611 (m : ℕ) (hm : IsA004611 m) : Realizable m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨hm0, hgood⟩ := hm
    by_cases h1 : m = 1
    · subst h1
      exact realizable_one
    have hq : m.minFac.Prime := Nat.minFac_prime h1
    obtain ⟨k, hk⟩ := Nat.minFac_dvd m
    have hq3 : m.minFac % 3 = 1 :=
      hgood _ (Nat.mem_primeFactors.2 ⟨hq, Nat.minFac_dvd m, hm0.ne'⟩)
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    have hklt : k < m := by
      have := hq.two_le
      rw [hk]
      nlinarith
    have hkgood : ∀ q ∈ k.primeFactors, q % 3 = 1 := fun q hqk =>
      hgood q (Nat.primeFactors_mono (Dvd.intro_left _ hk.symm) hm0.ne' hqk)
    have hk3 : ¬ 3 ∣ k := fun h3 =>
      absurd (hkgood 3 (Nat.mem_primeFactors.2 ⟨Nat.prime_three, h3, hk0.ne'⟩)) (by norm_num)
    rw [hk]
    exact realizable_mul (realizable_prime hq hq3) (ih k hklt ⟨hk0, hkgood⟩) hq.pos hk0
      (by omega) hk3

/-! ## The conjecture -/

/-- Inclusion: every term `a091258 n` (`n ≥ 1`) belongs to A004611. -/
theorem isA004611_a091258 {n : ℕ} (hn : 0 < n) : IsA004611 (a091258 n) :=
  ⟨Rat.den_pos _, fun _ hq =>
    den_prime_mod_three hn.ne' (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)⟩

/-- Surjectivity: every member of A004611 occurs as a term `a091258 n` with `n ≥ 1`. -/
theorem exists_a091258_eq {m : ℕ} (hm : IsA004611 m) : ∃ n, 0 < n ∧ a091258 n = m := by
  obtain ⟨n, hn, -, hden, -⟩ := realizable_of_isA004611 m hm 1 0 one_pos (by norm_num)
  exact ⟨n, hn, hden⟩

/-- **Marcus's conjecture (A091258, Michel Marcus, Aug 10 2024).**

Verbatim: "Conjecture: The set of distinct terms is A004611."

The set of reduced denominators of `σ₃(n)/σ₁(n)` over `n ≥ 1` equals the set of positive
integers all of whose prime factors are `≡ 1 (mod 3)`. -/
theorem a091258_range_eq :
    {m : ℕ | ∃ n, 0 < n ∧ a091258 n = m} = {m : ℕ | IsA004611 m} := by
  ext m
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact isA004611_a091258 hn
  · exact exists_a091258_eq

end Candidates.A091258SigmaThreeDenominator
