/-
# A328919 — `σ_k(n) mod n` purely periodic only for `n = 1, 12`

## OEIS source (`oeis show A328919` and https://oeis.org/A328919, retrieved 2026-10-21)

```
NAME:   Smallest index m such that from the m-th term on, the sequence
        {sigma_k(n) mod n: k >= 0} enters into a cycle.
TERMS:  0,1,1,2,1,1,1,3,2,1,1,0,1,1,1,4,1,1,1,1,1,1,1,1,2,1,3,1,1,1,1,5,...
AUTHOR: Jianing Song, Oct 31 2019
COMMENT: Conjecture: a(n) = 0 only for n = 1, 12. If {sigma_k(n) mod n: k >= 0}
  is purely periodic, then sigma_0(n) == sigma_psi(n)(n) (mod n). [...] So
  sigma_0(n) == sigma_psi(n)(n) (mod n) means that p^e divides e*d(s) for every
  p dividing n, which seems highly impossible for n > 12. [...]
COMMENT: Every number occurs in this sequence, because a(p^e) = e for primes p.
  Conjecture: a(2^e) is always the earliest occurrence of e.
```

The comments carry no separate signature; the attribution is the entry
author, Jianing Song, Oct 31 2019.

## Status

Triage: open (no proof in the entry or the literature found; the entry gives only
the necessary condition `p^e ∣ e·d(s)` and the heuristic "seems highly
impossible"). Recomputed 2026-10-21: the necessary condition holds only for
`n ∈ {1, 12}` up to `3·10^5`, `a(n) = 0` only for `n ∈ {1, 12}` up to `2·10^4`, and the first
occurrence of each value `e ≤ 14` is at `2^e`.

This module proves both conjectures. Route: (1) the entry's necessary condition
with `M = T·n·φ(n)`; (2) `n ∣ ∏ e_p(e_p+1)`; (3) a weighted product bound forces
`n ∣ 144`; (4) a finite check on the divisors of `144`; (5) period `2` for `n = 12`.
The second conjecture follows from periodicity from index `⌊log₂ n⌋` with period
`φ(n)` and an explicit computation of `σ_{e-1}(2^e) mod 2^e`.
-/
import Mathlib

set_option autoImplicit false

open ArithmeticFunction

namespace Candidates.A328919SigmaModPurely

/-- The sequence `k ↦ σ_k(n) mod n` (`k ≥ 0`) is *purely periodic*: there is a period
`T > 0` with `σ_{k+T}(n) ≡ σ_k(n) [MOD n]` for every `k ≥ 0`. -/
def PurelyPeriodic (n : ℕ) : Prop :=
  ∃ T, 0 < T ∧ ∀ k, sigma (k + T) n ≡ sigma k n [MOD n]

/-- From the `m`-th term on (`k ≥ m`, terms indexed from `k = 0`), the sequence
`k ↦ σ_k(n) mod n` has entered a cycle: some `T > 0` has
`σ_{k+T}(n) ≡ σ_k(n) [MOD n]` for all `k ≥ m`. -/
def PeriodicFrom (n m : ℕ) : Prop :=
  ∃ T, 0 < T ∧ ∀ k, m ≤ k → sigma (k + T) n ≡ sigma k n [MOD n]

/-- **A328919.** `a n` is the smallest index `m` such that from the `m`-th term on the
sequence `{σ_k(n) mod n : k ≥ 0}` enters a cycle. The defining set is nonempty for
`0 < n` (`periodicFrom_of_lt_two_pow`); the value at `n = 0` (outside the entry's
domain `n ≥ 1`) is irrelevant. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | PeriodicFrom n m}

/-- `σ_k(n)` cast into `ZMod m` is the sum of the `k`-th powers of the cast divisors. -/
theorem sigma_natCast (k n m : ℕ) :
    ((sigma k n : ℕ) : ZMod m) = ∑ d ∈ n.divisors, (d : ZMod m) ^ k := by
  rw [sigma_apply]; push_cast; rfl

/-- For a prime `p` and `e ≤ M`, `σ_M(p^e) ≡ 1 (mod p^e)`. -/
theorem sigma_prime_pow_zmod {p e M : ℕ} (hp : p.Prime) (he : e ≤ M) :
    ((sigma M (p ^ e) : ℕ) : ZMod (p ^ e)) = 1 := by
  rw [sigma_apply_prime_pow hp, Finset.sum_range_succ']
  push_cast
  rw [Finset.sum_eq_zero]
  · simp
  · intro j _
    exact ZMod.natCast_pow_eq_zero_of_le p (le_trans he (Nat.le_mul_of_pos_left M j.succ_pos))

/-- `σ_0(p^e) = e + 1` for a prime `p`. -/
theorem sigma_zero_prime_pow {p e : ℕ} (hp : p.Prime) : sigma 0 (p ^ e) = e + 1 := by
  rw [sigma_apply_prime_pow hp]; simp

/-- If `p ∤ s` and `φ(p^e) ∣ M`, then `σ_M(s) ≡ d(s) (mod p^e)`. -/
theorem sigma_coprime_zmod {p e s M : ℕ} (hp : p.Prime) (hs : ¬ p ∣ s)
    (hM : (p ^ e).totient ∣ M) :
    ((sigma M s : ℕ) : ZMod (p ^ e)) = s.divisors.card := by
  rw [sigma_natCast]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdp : ¬ p ∣ d := fun h => hs (h.trans (Nat.dvd_of_mem_divisors hd))
  have hcop : d.Coprime (p ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hdp))
  obtain ⟨c, rfl⟩ := hM
  have h1 : d ^ ((p ^ e).totient * c) ≡ 1 [MOD p ^ e] := by
    rw [pow_mul]
    simpa using (Nat.ModEq.pow_totient hcop).pow c
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  push_cast at h2
  simpa using h2

/-- Core step (entry comment): if `p ∤ s`, `e ≤ M`, `φ(p^e) ∣ M` and
`σ_M(p^e s) ≡ σ_0(p^e s) (mod p^e)`, then `p^e ∣ e · d(s)`. -/
theorem dvd_of_sigma_modEq {p e s M : ℕ} (hp : p.Prime) (hs : ¬ p ∣ s) (he : e ≤ M)
    (hM : (p ^ e).totient ∣ M)
    (h : sigma M (p ^ e * s) ≡ sigma 0 (p ^ e * s) [MOD p ^ e]) :
    p ^ e ∣ e * s.divisors.card := by
  have hcop : (p ^ e).Coprime s :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hs)
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
    isMultiplicative_sigma.map_mul_of_coprime hcop] at hz
  push_cast at hz
  rw [sigma_prime_pow_zmod hp he, sigma_coprime_zmod hp hs hM, sigma_zero_prime_pow hp,
    sigma_zero_apply] at hz
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast at hz ⊢
  linear_combination -hz


/-- A period `T` of `k ↦ σ_k(n) mod n` gives the congruence at every multiple of `T`. -/
theorem modEq_add_mul_of_period {n T : ℕ}
    (hT : ∀ k, sigma (k + T) n ≡ sigma k n [MOD n]) (j k : ℕ) :
    sigma (k + j * T) n ≡ sigma k n [MOD n] := by
  induction j with
  | zero => simp [Nat.ModEq]
  | succ j ih =>
    have h := hT (k + j * T)
    rw [show k + j * T + T = k + (j + 1) * T by ring] at h
    exact h.trans ih

/-- Necessary condition from the entry: if `σ_k(n) mod n` is purely periodic and
`n = p^e s` with `p` prime, `p ∤ s`, then `p^e ∣ e · d(s)`. -/
theorem dvd_of_purelyPeriodic {n p e s : ℕ} (hper : PurelyPeriodic n) (hp : p.Prime)
    (hn : n = p ^ e * s) (hs : ¬ p ∣ s) (hn0 : 0 < n) :
    p ^ e ∣ e * s.divisors.card := by
  obtain ⟨T, hT0, hT⟩ := hper
  have hmod := modEq_add_mul_of_period hT (n * n.totient) 0
  rw [zero_add] at hmod
  have hpe : p ^ e ∣ n := hn ▸ dvd_mul_right _ _
  have he : e ≤ n * n.totient * T := by
    have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ e ≤ n := Nat.le_of_dvd hn0 hpe
    have h3 : 0 < n.totient := Nat.totient_pos.2 hn0
    have h4 : n ≤ n * n.totient * T :=
      Nat.le_mul_of_pos_right _ hT0 |>.trans' (Nat.le_mul_of_pos_right _ h3)
    omega
  have hM : (p ^ e).totient ∣ n * n.totient * T :=
    (Nat.totient_dvd_of_dvd hpe).trans ((dvd_mul_left _ _).mul_right _)
  have hmod' := hmod.of_dvd hpe
  generalize n * n.totient * T = M at hmod' he hM
  rw [hn] at hmod'
  exact dvd_of_sigma_modEq hp hs he hM hmod'

/-- A single prime-power witness violating `p^e ∣ e · d(s)` rules out pure periodicity. -/
theorem not_purelyPeriodic_of {n p e s : ℕ} (hp : p.Prime) (hn : n = p ^ e * s)
    (hs : ¬ p ∣ s) (hbad : ¬ p ^ e ∣ e * s.divisors.card) : ¬ PurelyPeriodic n := by
  intro hper
  have hn0 : 0 < n := by
    rw [hn]; exact Nat.mul_pos (pow_pos hp.pos _) (Nat.pos_of_ne_zero fun h => hs (h ▸ dvd_zero p))
  exact hbad (dvd_of_purelyPeriodic hper hp hn hs hn0)

/-- `σ_k(1) mod 1` is purely periodic (everything is `0` modulo `1`). -/
theorem purelyPeriodic_one : PurelyPeriodic 1 :=
  ⟨1, one_pos, fun _ => Nat.modEq_one⟩

/-- `σ_k(12) mod 12` is purely periodic with period `2` (values `6, 4, 6, 4, …`). -/
theorem purelyPeriodic_twelve : PurelyPeriodic 12 := by
  refine ⟨2, two_pos, fun k => ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, sigma_natCast, sigma_natCast]
  have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rcases k with _ | _ | k
  · rw [hdiv]; decide
  · rw [hdiv]; decide
  · refine Finset.sum_congr rfl fun d _ => ?_
    have h4 : ∀ x : ZMod 12, x ^ 4 = x ^ 2 := by decide
    calc (d : ZMod 12) ^ (k + 2 + 2) = (d : ZMod 12) ^ k * (d : ZMod 12) ^ 4 := by ring
      _ = (d : ZMod 12) ^ k * (d : ZMod 12) ^ 2 := by rw [h4]
      _ = (d : ZMod 12) ^ (k + 2) := by ring

/-- No divisor of `144` other than `1` and `12` has a purely periodic sequence. -/
theorem not_purelyPeriodic_of_dvd_144 {n : ℕ} (hn : n ∣ 144) (h1 : n ≠ 1) (h12 : n ≠ 12) :
    ¬ PurelyPeriodic n := by
  have hmem : n ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by
    rw [show ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ)
      = Nat.divisors 144 by decide]
    exact Nat.mem_divisors.2 ⟨hn, by norm_num⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact absurd rfl h1
  · exact not_purelyPeriodic_of (p := 2) (e := 1) (s := 1) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 3) (e := 1) (s := 1) Nat.prime_three rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 2) (s := 1) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 3) (e := 1) (s := 2) Nat.prime_three rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 3) (s := 1) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 3) (e := 2) (s := 1) Nat.prime_three rfl (by decide) (by decide)
  · exact absurd rfl h12
  · exact not_purelyPeriodic_of (p := 2) (e := 4) (s := 1) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 3) (e := 2) (s := 2) Nat.prime_three rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 3) (s := 3) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 2) (s := 9) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 4) (s := 3) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 3) (s := 9) Nat.prime_two rfl (by decide) (by decide)
  · exact not_purelyPeriodic_of (p := 2) (e := 4) (s := 9) Nat.prime_two rfl (by decide) (by decide)


/-- `e (e + 1) < 2^e` for `e ≥ 5`. -/
theorem mul_succ_lt_two_pow {e : ℕ} (he : 5 ≤ e) : e * (e + 1) < 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih => rw [pow_succ]; nlinarith

/-- `3 e (e + 1) < 2 · 3^e` for `e ≥ 3`. -/
theorem three_mul_mul_succ_lt_two_mul_three_pow {e : ℕ} (he : 3 ≤ e) :
    3 * e * (e + 1) < 2 * 3 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih => rw [pow_succ]; nlinarith

/-- `3 e (e + 1) < 2 · 5^e` for `e ≥ 1`. -/
theorem three_mul_mul_succ_lt_two_mul_five_pow {e : ℕ} (he : 1 ≤ e) :
    3 * e * (e + 1) < 2 * 5 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih => rw [pow_succ]; nlinarith

/-- `2 e (e + 1) ≤ 3 · 2^e` for every `e`. -/
theorem two_mul_mul_succ_le_three_mul_two_pow (e : ℕ) :
    2 * e * (e + 1) ≤ 3 * 2 ^ e := by
  rcases Nat.lt_or_ge e 2 with h | h
  · interval_cases e <;> norm_num
  · induction e, h using Nat.le_induction with
    | base => norm_num
    | succ e he ih => rw [pow_succ]; nlinarith

/-- `e (e + 1) ≤ q^e` for `q ≥ 3`. -/
theorem mul_succ_le_pow {q : ℕ} (hq : 3 ≤ q) (e : ℕ) : e * (e + 1) ≤ q ^ e := by
  have h3 : e * (e + 1) ≤ 3 ^ e := by
    induction e with
    | zero => norm_num
    | succ e ih =>
      rw [pow_succ]
      rcases Nat.eq_zero_or_pos e with rfl | he
      · norm_num
      · nlinarith
  exact h3.trans (Nat.pow_le_pow_left hq e)


/-- `d(n) = (v_p(n) + 1) · d(n / p^{v_p(n)})` for `n ≠ 0` and `p` prime. -/
theorem card_divisors_eq_mul_ordCompl {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    n.divisors.card = (n.factorization p + 1) * (n / p ^ n.factorization p).divisors.card := by
  have hcop : (p ^ n.factorization p).Coprime (n / p ^ n.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn)
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [Nat.Coprime.card_divisors_mul hcop, ← sigma_zero_apply, sigma_zero_prime_pow hp]

/-- If `p^{e_p} ∣ e_p · d(n / p^{e_p})` for every prime `p ∣ n`, then
`n ∣ ∏_{p ∣ n} e_p (e_p + 1)`. -/
theorem dvd_prod_of_forall_dvd {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors,
      p ^ n.factorization p ∣ n.factorization p * (n / p ^ n.factorization p).divisors.card) :
    n ∣ ∏ p ∈ n.primeFactors, n.factorization p * (n.factorization p + 1) := by
  have hX : ∏ p ∈ n.primeFactors, n.factorization p * (n.factorization p + 1)
      = (∏ p ∈ n.primeFactors, n.factorization p) * n.divisors.card := by
    rw [Finset.prod_mul_distrib, Nat.card_divisors hn]
  have hpp : ∀ p ∈ n.primeFactors, p ^ n.factorization p ∣
      (∏ p ∈ n.primeFactors, n.factorization p) * n.divisors.card := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    refine (h p hp).trans (mul_dvd_mul (Finset.dvd_prod_of_mem _ hp) ?_)
    rw [card_divisors_eq_mul_ordCompl hn hp']
    exact Dvd.intro_left _ rfl
  rw [hX]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ n).2 fun q k hq hqk => ?_
  have hk : k ≤ n.factorization q := (hq.pow_dvd_iff_le_factorization hn).1 hqk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have hmem : q ∈ n.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, (dvd_pow_self q hk0.ne').trans hqk, hn⟩
    exact (pow_dvd_pow q hk).trans (hpp q hmem)


/-- If `n ≤ ∏_{p ∣ n} e_p (e_p + 1)` then every prime factor of `n` is `2` with
exponent `≤ 4` or `3` with exponent `≤ 2`. The proof weighs each factor
`p^{e_p} / (e_p (e_p + 1))` (times `3/2` for `p = 2`) against `1`. -/
theorem prime_pow_cases {n : ℕ} (hn : n ≠ 0)
    (hle : n ≤ ∏ p ∈ n.primeFactors, n.factorization p * (n.factorization p + 1)) :
    ∀ q ∈ n.primeFactors, (q = 2 ∧ n.factorization q ≤ 4) ∨ (q = 3 ∧ n.factorization q ≤ 2) := by
  set P := n.primeFactors with hP
  set f := n.factorization with hf
  let c : ℕ → ℚ≥0 := fun q => if q = 2 then 3 / 2 else 1
  let u : ℕ → ℚ≥0 := fun q => ((q : ℚ≥0) ^ f q * c q) / ((f q : ℚ≥0) * (f q + 1))
  have hfpos : ∀ q ∈ P, 0 < f q := fun q hq =>
    (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hq)
  have hden : ∀ q ∈ P, (0 : ℚ≥0) < (f q : ℚ≥0) * (f q + 1) := by
    intro q hq
    have := hfpos q hq
    positivity
  -- each factor is at least one
  have hu1 : ∀ q ∈ P, 1 ≤ u q := by
    intro q hq
    rw [one_le_div₀ (hden q hq)]
    by_cases h2 : q = 2
    · have hc : c q = 3 / 2 := if_pos h2
      rw [hc, h2]
      have hN := two_mul_mul_succ_le_three_mul_two_pow (f 2)
      have hN' : ((2 * f 2 * (f 2 + 1) : ℕ) : ℚ) ≤ ((3 * 2 ^ f 2 : ℕ) : ℚ) := by
        exact_mod_cast hN
      push_cast at hN'
      rw [← NNRat.coe_le_coe]
      push_cast
      linarith
    · have hc : c q = 1 := if_neg h2
      rw [hc, mul_one]
      have hq3 : 3 ≤ q := ((Nat.prime_of_mem_primeFactors hq).two_le).lt_of_ne' h2
      have hN := mul_succ_le_pow hq3 (f q)
      exact_mod_cast hN
  -- the product of all factors is at most `3 / 2`
  have hnP : ∏ q ∈ P, (q : ℚ≥0) ^ f q = n := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact_mod_cast h
  have hXpos : (0 : ℚ≥0) < ∏ q ∈ P, (f q : ℚ≥0) * (f q + 1) :=
    Finset.prod_pos hden
  have hle' : (n : ℚ≥0) ≤ ∏ q ∈ P, (f q : ℚ≥0) * (f q + 1) := by exact_mod_cast hle
  have hC : ∏ q ∈ P, c q ≤ 3 / 2 := by
    rw [Finset.prod_ite_eq' P 2 (fun _ => (3 / 2 : ℚ≥0))]
    split_ifs
    · exact le_rfl
    · rw [← NNRat.coe_le_coe]; norm_num
  have hprod : ∏ q ∈ P, u q ≤ 3 / 2 := by
    calc ∏ q ∈ P, u q
        = (∏ q ∈ P, (q : ℚ≥0) ^ f q) * (∏ q ∈ P, c q) /
            ∏ q ∈ P, (f q : ℚ≥0) * (f q + 1) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
      _ ≤ ∏ q ∈ P, c q := by
          rw [div_le_iff₀ hXpos, hnP, mul_comm (∏ q ∈ P, c q)]
          exact mul_le_mul_of_nonneg_right hle' zero_le
      _ ≤ 3 / 2 := hC
  intro q hq
  have huq : u q ≤ 3 / 2 := (Finset.single_le_prod' hu1 hq).trans hprod
  have hfq := hfpos q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  by_cases h2 : q = 2
  · left
    refine ⟨h2, ?_⟩
    have hc : c q = 3 / 2 := if_pos h2
    have h' : (q : ℚ≥0) ^ f q * c q ≤ 3 / 2 * ((f q : ℚ≥0) * (f q + 1)) :=
      (div_le_iff₀ (hden q hq)).1 huq
    rw [hc, h2, ← NNRat.coe_le_coe] at h'
    push_cast at h'
    have hQ : ((2 ^ f 2 : ℕ) : ℚ) ≤ ((f 2 * (f 2 + 1) : ℕ) : ℚ) := by
      push_cast; linarith
    have hN : 2 ^ f 2 ≤ f 2 * (f 2 + 1) := by exact_mod_cast hQ
    rw [h2]
    by_contra hcon
    exact absurd hN (not_le.2 (mul_succ_lt_two_pow (by omega)))
  · right
    have hc : c q = 1 := if_neg h2
    have h' : (q : ℚ≥0) ^ f q * c q ≤ 3 / 2 * ((f q : ℚ≥0) * (f q + 1)) :=
      (div_le_iff₀ (hden q hq)).1 huq
    rw [hc, mul_one, ← NNRat.coe_le_coe] at h'
    push_cast at h'
    have hQ : ((2 * q ^ f q : ℕ) : ℚ) ≤ ((3 * f q * (f q + 1) : ℕ) : ℚ) := by
      push_cast; linarith
    have hN : 2 * q ^ f q ≤ 3 * f q * (f q + 1) := by exact_mod_cast hQ
    have hq3 : 3 ≤ q := hqp.two_le.lt_of_ne' h2
    have hq5 : q < 5 := by
      by_contra hcon
      have h5 : 5 ^ f q ≤ q ^ f q := Nat.pow_le_pow_left (by omega) _
      have := three_mul_mul_succ_lt_two_mul_five_pow hfq
      omega
    have hq3' : q = 3 := by
      interval_cases q
      · rfl
      · exact absurd hqp (by decide)
    refine ⟨hq3', ?_⟩
    subst hq3'
    by_contra hcon
    have := three_mul_mul_succ_lt_two_mul_three_pow (e := f 3) (by omega)
    omega


/-- A purely periodic `n > 0` divides `144 = 2^4 · 3^2`. -/
theorem dvd_144_of_purelyPeriodic {n : ℕ} (hn : 0 < n) (hper : PurelyPeriodic n) : n ∣ 144 := by
  have hn0 : n ≠ 0 := hn.ne'
  have hdvd := dvd_prod_of_forall_dvd hn0 fun p hp =>
    dvd_of_purelyPeriodic hper (Nat.prime_of_mem_primeFactors hp)
      (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      (Nat.not_dvd_ordCompl (Nat.prime_of_mem_primeFactors hp) hn0) hn
  have hXpos : 0 < ∏ p ∈ n.primeFactors, n.factorization p * (n.factorization p + 1) :=
    Finset.prod_pos fun q hq => Nat.mul_pos
      ((Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hn0
        (Nat.dvd_of_mem_primeFactors hq)) (Nat.succ_pos _)
  have hcases := prime_pow_cases hn0 (Nat.le_of_dvd hXpos hdvd)
  refine (Nat.dvd_iff_prime_pow_dvd_dvd 144 n).2 fun q k hq hqk => ?_
  have hk : k ≤ n.factorization q := (hq.pow_dvd_iff_le_factorization hn0).1 hqk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have hmem : q ∈ n.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, (dvd_pow_self q hk0.ne').trans hqk, hn0⟩
    rcases hcases q hmem with ⟨rfl, h4⟩ | ⟨rfl, h2⟩
    · exact (pow_dvd_pow 2 (hk.trans h4)).trans (by norm_num)
    · exact (pow_dvd_pow 3 (hk.trans h2)).trans (by norm_num)

/-- **A328919 conjecture (Jianing Song, Oct 31 2019), periodicity form.**
For `n ≥ 1`, the sequence `{σ_k(n) mod n : k ≥ 0}` is purely periodic iff
`n ∈ {1, 12}`. -/
theorem purelyPeriodic_iff {n : ℕ} (hn : 0 < n) : PurelyPeriodic n ↔ n = 1 ∨ n = 12 := by
  constructor
  · intro hper
    by_contra hne
    push Not at hne
    exact not_purelyPeriodic_of_dvd_144 (dvd_144_of_purelyPeriodic hn hper) hne.1 hne.2 hper
  · rintro (rfl | rfl)
    · exact purelyPeriodic_one
    · exact purelyPeriodic_twelve

/-- If `n < 2^(m+1)`, `d > 0` and `k ≥ m`, then `d^(k + φ(n)) ≡ d^k (mod n)`. -/
theorem pow_add_totient_modEq {n m d k : ℕ} (hn : 0 < n) (hm : n < 2 ^ (m + 1)) (hd : 0 < d)
    (hk : m ≤ k) : d ^ (k + n.totient) ≡ d ^ k [MOD n] := by
  have hle : d ^ k ≤ d ^ (k + n.totient) := Nat.pow_le_pow_right hd (Nat.le_add_right _ _)
  refine ((Nat.modEq_iff_dvd' hle).2 ?_).symm
  have hfac : d ^ (k + n.totient) - d ^ k = d ^ k * (d ^ n.totient - 1) := by
    rw [pow_add, Nat.mul_sub_one]
  rw [hfac]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ n).2 fun q j hq hqj => ?_
  have hjk : j ≤ k := by
    by_contra hcon
    have h1 : 2 ^ j ≤ q ^ j := Nat.pow_le_pow_left hq.two_le j
    have h2 : q ^ j ≤ n := Nat.le_of_dvd hn hqj
    have h3 : 2 ^ (m + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hqd : q ∣ d
  · exact ((pow_dvd_pow q hjk).trans (pow_dvd_pow_of_dvd hqd k)).mul_right _
  · have hcop : d.Coprime (q ^ j) :=
      Nat.Coprime.pow_right j ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd))
    obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hqj
    have h1 : d ^ n.totient ≡ 1 [MOD q ^ j] := by
      rw [hc, pow_mul]
      simpa using (Nat.ModEq.pow_totient hcop).pow c
    have h2 : q ^ j ∣ d ^ n.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hd)).1 h1.symm
    exact h2.mul_left _

/-- If `0 < n < 2^(m+1)`, the sequence `σ_k(n) mod n` is periodic from the `m`-th
term on, with period `φ(n)`. -/
theorem periodicFrom_of_lt_two_pow {n m : ℕ} (hn : 0 < n) (hm : n < 2 ^ (m + 1)) :
    PeriodicFrom n m := by
  refine ⟨n.totient, Nat.totient_pos.2 hn, fun k hk => ?_⟩
  rw [sigma_apply, sigma_apply]
  exact Nat.ModEq.sum fun d hd =>
    pow_add_totient_modEq hn hm (Nat.pos_of_mem_divisors hd) hk

/-- `a(n) ≤ m` whenever `0 < n < 2^(m+1)`. -/
theorem a_le_of_lt_two_pow {n m : ℕ} (hn : 0 < n) (hm : n < 2 ^ (m + 1)) : a n ≤ m :=
  Nat.sInf_le (periodicFrom_of_lt_two_pow hn hm)

/-- `a(n) < e` whenever `0 < n < 2^e`. -/
theorem a_lt_of_lt_two_pow {n e : ℕ} (hn : 0 < n) (he : n < 2 ^ e) : a n < e := by
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · rw [pow_zero] at he; omega
  · have := a_le_of_lt_two_pow (m := e - 1) hn (by rwa [Nat.sub_add_cancel he0])
    omega

/-- **A328919 conjecture (Jianing Song, Oct 31 2019).** "a(n) = 0 only for
n = 1, 12": for `n ≥ 1`, `a(n) = 0 ↔ n = 1 ∨ n = 12`. -/
theorem a_eq_zero_iff {n : ℕ} (hn : 0 < n) : a n = 0 ↔ n = 1 ∨ n = 12 := by
  rw [← purelyPeriodic_iff hn]
  have hne : {m | PeriodicFrom n m}.Nonempty :=
    ⟨n, periodicFrom_of_lt_two_pow hn
      (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)))⟩
  rw [a, Nat.sInf_eq_zero, or_iff_left hne.ne_empty]
  constructor
  · rintro ⟨T, hT, h⟩
    exact ⟨T, hT, fun k => h k (Nat.zero_le k)⟩
  · rintro ⟨T, hT, h⟩
    exact ⟨T, hT, fun k _ => h k⟩

/-- `σ_{e-1}(2^e) ≡ 1 + 2^{e-1} (mod 2^e)` for `e ≥ 1`. -/
theorem sigma_pred_two_pow_zmod {e : ℕ} (he : 0 < e) :
    ((sigma (e - 1) (2 ^ e) : ℕ) : ZMod (2 ^ e)) = 1 + 2 ^ (e - 1) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [Nat.add_sub_cancel, sigma_apply_prime_pow Nat.prime_two, Finset.sum_range_succ',
    Finset.sum_range_succ']
  push_cast
  rw [Finset.sum_eq_zero]
  · ring
  · intro i hi
    have hi' : i < e' := Finset.mem_range.1 hi
    have h := ZMod.natCast_pow_eq_zero_of_le 2 (m := (i + 1 + 1) * e') (n := e' + 1)
      (by nlinarith)
    exact_mod_cast h

/-- `a(2^e) = e` (the case `p = 2` of the entry's remark `a(p^e) = e`). -/
theorem a_two_pow (e : ℕ) : a (2 ^ e) = e := by
  refine le_antisymm (a_le_of_lt_two_pow (pow_pos two_pos e)
    (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self e))) ?_
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact Nat.zero_le _
  refine le_csInf ⟨e, periodicFrom_of_lt_two_pow (pow_pos two_pos e)
    (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self e))⟩ fun m hm => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨T, hT, h⟩ := hm
  have hk := h (e - 1) (by omega)
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).2 hk
  rw [sigma_prime_pow_zmod Nat.prime_two (by omega), sigma_pred_two_pow_zmod he] at hz
  have h0 : ((2 ^ (e - 1) : ℕ) : ZMod (2 ^ e)) = 0 := by
    push_cast; linear_combination -hz
  rw [ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h0
  omega

/-- **A328919 second conjecture (Jianing Song, Oct 31 2019).** "a(2^e) is always
the earliest occurrence of e": `a(2^e) = e`, and `a(n) ≠ e` for every
`1 ≤ n < 2^e`. -/
theorem a_two_pow_first_occurrence (e : ℕ) :
    a (2 ^ e) = e ∧ ∀ n, 0 < n → n < 2 ^ e → a n ≠ e :=
  ⟨a_two_pow e, fun _ hn hlt => (a_lt_of_lt_two_pow hn hlt).ne⟩

/-! ## Ground truth against the listed terms
`a(1..16) = 0, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 0, 1, 1, 1, 4` (OEIS data). -/

example : a 1 = 0 := (a_eq_zero_iff one_pos).2 (Or.inl rfl)
example : a 2 = 1 := by simpa using a_two_pow 1
example : a 3 = 1 := by
  have h1 := a_lt_of_lt_two_pow (n := 3) (e := 2) (by norm_num) (by norm_num)
  have h0 : a 3 ≠ 0 := fun h => by
    rcases (a_eq_zero_iff (n := 3) (by norm_num)).1 h with h | h <;> norm_num at h
  omega
example : a 4 = 2 := by simpa using a_two_pow 2
example : a 8 = 3 := by simpa using a_two_pow 3
example : a 12 = 0 := (a_eq_zero_iff (by norm_num)).2 (Or.inr rfl)
example : a 16 = 4 := by simpa using a_two_pow 4

end Candidates.A328919SigmaModPurely
