/-
# Ishikawa analog for cyclic numbers: `c_n + c_{n+1} > c_{n+2}`

## Source

* Joel E. Cohen, "Conjectures about cyclic numbers" (arXiv:2508.08335;
  J. Integer Seq. 28 (2025), Article 25.4.7), Section "Additive and
  multiplicative inequalities", Conjecture `conj:Ishik1` ("Ishikawa analog
  for cyclics"; Conjecture 54 in the JIS version). Verbatim:

  > For all $n>2$,
  > $$c_n + c_{n+1} > c_{n+2}.$$
  > When $n=1$ or $n=2$, equality holds: $c_1 + c_2 = c_3 = 3$ and
  > $c_2+c_3=c_4 = 5$.

  Here $c_1 = 1 < c_2 = 2 < c_3 = 3 < c_4 = 5 < \dots$ enumerates the cyclic
  numbers (OEIS A003277): $n \in \mathbb{N}$ is cyclic iff
  $\gcd(n, \varphi(n)) = 1$ (Szele's criterion, which the paper uses as the
  working definition).

Date recorded: 2026-10-21.

## Status

Stated as a conjecture in the paper (checked there for the cyclics below
`10^8`); no refereed proof was located (a withdrawn preprint,
arXiv:2509.26138v1, sketches one via Nagura's theorem). This module proves
it in full.

## Proof

The bridge is Ramanujan's `R₂ = 11`: for `n ≥ 6` there are two primes
`p < q` in `(n, 2n]` (`exists_two_primes`). For `n ≥ 512` this follows
the Erdős proof of Bertrand's postulate in Mathlib: if `(n, 2n]` held only
one prime `p₀`, it contributes at most `2n` to `centralBinom n`, which is
compensated by the fact that the primes `≤ √(2n)` number at most
`√(2n) - 1` (the integer `1` is not prime), so Mathlib's
`bertrand_main_inequality` still gives a contradiction. Small `n` are
covered by a prime chain. Primes are cyclic, so for consecutive cyclics
`a < b < c` with `a ≥ 6`, `c ≤ q ≤ 2a < a + b`; the cases `a ∈ {3, 5}` are
direct.

Indexing: Lean's `Nat.nth` is `0`-indexed, so Cohen's `c_n` is
`Nat.nth IsCyclicNumber (n - 1)` and the hypothesis `n > 2` becomes
`2 ≤ k` for `k = n - 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.CyclicNumbersIshikawaInequality

open Nat

/-! ## Two primes in `(n, 2n]` (Ramanujan's `R₂ = 11`) -/

/-- Variant of Mathlib's `centralBinom_le_of_no_bertrand_prime`: if `p₀` is the only prime
in `(n, 2n]`, then `centralBinom n ≤ (2n)^⌊√(2n)⌋ · 4^⌊2n/3⌋`. The single large prime
contributes at most `2n`; this is absorbed because at most `⌊√(2n)⌋ - 1` primes lie
below `⌊√(2n)⌋`. -/
theorem centralBinom_le_of_unique_prime (n p₀ : ℕ) (n_large : 2 < n) (hnp : n < p₀)
    (hp2n : p₀ ≤ 2 * n)
    (huniq : ∀ p : ℕ, p.Prime → n < p → p ≤ 2 * n → p = p₀) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := by omega
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hp₀_notMem : p₀ ∉ Finset.range (2 * n / 3 + 1) := by
    rw [Finset.mem_range]; omega
  -- Step 1: the factorization splits off the single large prime `p₀`.
  have hsplit : centralBinom n = f p₀ * ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    rw [← Finset.prod_insert hp₀_notMem]
    refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
    apply Finset.prod_subset
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_range] at hx
      rw [Finset.mem_range]
      omega
    intro x hx hx'
    rw [Finset.mem_insert, Finset.mem_range, not_or] at hx'
    rw [Finset.mem_range] at hx
    by_cases hxp : x.Prime
    · rcases le_or_gt x n with hxn | hxn
      · show x ^ _ = 1
        rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hxn (by omega),
          pow_zero]
      · exact absurd (huniq x hxp hxn (by omega)) hx'.1
    · show x ^ _ = 1
      rw [factorization_eq_zero_of_not_prime n.centralBinom hxp, pow_zero]
  -- Step 2: the large prime contributes at most `2 n`.
  have hfp₀ : f p₀ ≤ 2 * n := pow_factorization_choose_le (by omega)
  -- Step 3: the remaining primes, with the improved count of small primes.
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  have hS : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  have hrest : ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤
      (2 * n) ^ (sqrt (2 * n) - 1) * 4 ^ (2 * n / 3) := by
    rw [← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
      have hcard : (Finset.Icc 2 (sqrt (2 * n))).card = sqrt (2 * n) - 1 := by
        rw [card_Icc]; omega
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans hcard.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.two_le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  have hsqrt : 1 ≤ sqrt (2 * n) := Nat.le_sqrt.mpr (by omega)
  calc centralBinom n = f p₀ * ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := hsplit
    _ ≤ (2 * n) * ((2 * n) ^ (sqrt (2 * n) - 1) * 4 ^ (2 * n / 3)) :=
        Nat.mul_le_mul hfp₀ hrest
    _ = (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
        rw [← mul_assoc, ← pow_succ']
        congr 2
        omega

/-- Two primes in `(n, 2n]` for all `n ≥ 512` (large case of Ramanujan's `R₂ = 11`). -/
theorem exists_two_primes_eventually (n : ℕ) (n_large : 512 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q ≤ 2 * n := by
  obtain ⟨p₀, hp₀, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  by_contra hcon
  have huniq : ∀ p : ℕ, p.Prime → n < p → p ≤ 2 * n → p = p₀ := by
    intro p hp hnp' hp2n'
    rcases lt_trichotomy p p₀ with h | h | h
    · exact absurd ⟨p, p₀, hp, hp₀, hnp', h, hp2n⟩ hcon
    · exact h
    · exact absurd ⟨p₀, p, hp₀, hp, hnp, h, hp2n'⟩ hcon
  have hlow : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hup := centralBinom_le_of_unique_prime n p₀ (by omega) hnp hp2n huniq
  have hmain := bertrand_main_inequality n_large
  have hmul : n * n.centralBinom ≤ n * ((2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
    Nat.mul_le_mul_left n hup
  rw [← mul_assoc] at hmul
  omega

/-- Chain step for small `n`: if `b < c` are primes with `c ≤ 2a`, then every `n` with
`a ≤ n < b` has the two primes `b < c` in `(n, 2n]`; smaller `n` are delegated to `H`. -/
theorem two_primes_step {n : ℕ} (a b c : ℕ) (hb : b.Prime) (hc : c.Prime) (hbc : b < c)
    (hca : c ≤ 2 * a)
    (H : n < a → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q ≤ 2 * n) (hn : n < b) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q ≤ 2 * n := by
  rcases lt_or_ge n a with hna | hna
  · exact H hna
  · exact ⟨b, c, hb, hc, hn, hbc, by omega⟩

/-- **Ramanujan's `R₂ = 11`** (two-prime Bertrand): for every `n ≥ 6` there are primes
`p < q` with `n < p < q ≤ 2n`. -/
theorem exists_two_primes (n : ℕ) (hn : 6 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q ≤ 2 * n := by
  rcases le_or_gt 512 n with h | h
  · exact exists_two_primes_eventually n h
  refine two_primes_step 311 617 619 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ (by omega)
  refine two_primes_step 157 311 313 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 83 157 163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 47 83 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 29 47 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 17 29 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 11 17 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 7 11 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine two_primes_step 6 7 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro h6
  omega

/-- The bound `n ≥ 6` in `exists_two_primes` is sharp: `(5, 10]` contains only the
prime `7`. -/
example : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 5 < p ∧ p < q ∧ q ≤ 2 * 5 := by
  rintro ⟨p, q, hp, hq, h5p, hpq, hq10⟩
  have hp10 : p < 10 := by omega
  interval_cases p <;> interval_cases q
  all_goals revert hp hq; decide

/-! ## Cyclic numbers -/

/-- `n` is a *cyclic number* (OEIS A003277) if `gcd(n, φ(n)) = 1` (Szele's criterion,
Cohen's working definition: there is exactly one group of order `n`). The value `n = 0`
is excluded automatically since `gcd(0, φ 0) = 0`. -/
def IsCyclicNumber (n : ℕ) : Prop := n.Coprime n.totient

instance : DecidablePred IsCyclicNumber := fun n => inferInstanceAs (Decidable (n.Coprime _))

example : ¬ IsCyclicNumber 0 := by decide
example : IsCyclicNumber 1 := by decide
example : IsCyclicNumber 15 := by decide
example : ¬ IsCyclicNumber 4 := by decide
example : ¬ IsCyclicNumber 6 := by decide
example : ¬ IsCyclicNumber 21 := by decide

/-- The cyclic numbers below `30` are exactly `1, 2, 3, 5, 7, 11, 13, 15, 17, 19, 23, 29`
(OEIS A003277). -/
example : (Finset.range 30).filter IsCyclicNumber =
    {1, 2, 3, 5, 7, 11, 13, 15, 17, 19, 23, 29} := by decide

/-- Every prime is cyclic: `gcd(p, p - 1) = 1`. -/
theorem isCyclicNumber_of_prime {p : ℕ} (hp : p.Prime) : IsCyclicNumber p := by
  unfold IsCyclicNumber
  rw [Nat.totient_prime hp]
  exact Nat.coprime_of_lt_prime (by have := hp.two_le; omega) (by have := hp.two_le; omega) hp

/-- There are infinitely many cyclic numbers (they include the primes). -/
theorem infinite_setOf_isCyclicNumber : (Set.ofPred IsCyclicNumber).Infinite :=
  Nat.infinite_setOfPred_prime.mono fun _ hp => isCyclicNumber_of_prime hp

/-! ## The consecutive-triple form -/

/-- **Ishikawa analog, consecutive form.** If `a < b < c` are consecutive cyclic numbers
(no cyclic number strictly between `a` and `b`, or between `b` and `c`) and `3 ≤ a`, then
`c < a + b`. The cyclicity of `c` itself is not needed and is omitted. -/
theorem lt_add_of_consecutive {a b c : ℕ} (ha : IsCyclicNumber a) (hb : IsCyclicNumber b)
    (h3 : 3 ≤ a) (hab : a < b) (hbc : b < c)
    (g1 : ∀ m, a < m → m < b → ¬ IsCyclicNumber m)
    (g2 : ∀ m, b < m → m < c → ¬ IsCyclicNumber m) : c < a + b := by
  -- `b` and `c` are bounded by any cyclic number beyond `a`, resp. `b`.
  have hb_le : ∀ m, a < m → IsCyclicNumber m → b ≤ m := fun m ham hm =>
    not_lt.mp fun hmb => g1 m ham hmb hm
  have hc_le : ∀ m, b < m → IsCyclicNumber m → c ≤ m := fun m hbm hm =>
    not_lt.mp fun hmc => g2 m hbm hmc hm
  rcases le_or_gt 6 a with h6 | h6
  · obtain ⟨p, q, hp, hq, hap, hpq, hq2a⟩ := exists_two_primes a h6
    have hbp : b ≤ p := hb_le p hap (isCyclicNumber_of_prime hp)
    have hcq : c ≤ q := hc_le q (by omega) (isCyclicNumber_of_prime hq)
    omega
  · have hb_ne : ∀ m, m ∈ ({4, 6} : Finset ℕ) → b ≠ m := by
      intro m hm hbm
      subst hbm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> revert hb <;> decide
    have h5 : IsCyclicNumber 5 := by decide
    have h7 : IsCyclicNumber 7 := by decide
    have h11 : IsCyclicNumber 11 := by decide
    interval_cases a
    · have hb5 := hb_le 5 (by norm_num) h5
      have hb4 := hb_ne 4 (by simp)
      have hc7 := hc_le 7 (by omega) h7
      omega
    · exact absurd ha (by decide)
    · have hb7 := hb_le 7 (by norm_num) h7
      have hb6 := hb_ne 6 (by simp)
      have hc11 := hc_le 11 (by omega) h11
      omega

/-! ## The conjecture in `Nat.nth` form -/

/-- `c₁ = 1, c₂ = 2, c₃ = 3, c₄ = 5` in Lean's `0`-indexed enumeration. -/
theorem nth_isCyclicNumber_small :
    nth IsCyclicNumber 0 = 1 ∧ nth IsCyclicNumber 1 = 2 ∧ nth IsCyclicNumber 2 = 3 ∧
      nth IsCyclicNumber 3 = 5 := by
  have e : ∀ m k, IsCyclicNumber m → count IsCyclicNumber m = k → nth IsCyclicNumber k = m :=
    fun m k hm hk => hk ▸ nth_count hm
  exact ⟨e 1 0 (by decide) (by decide), e 2 1 (by decide) (by decide),
    e 3 2 (by decide) (by decide), e 5 3 (by decide) (by decide)⟩

/-- The paper's equality cases `n = 1, 2`: `c₁ + c₂ = c₃` and `c₂ + c₃ = c₄`. -/
example : nth IsCyclicNumber 2 = nth IsCyclicNumber 0 + nth IsCyclicNumber 1 ∧
    nth IsCyclicNumber 3 = nth IsCyclicNumber 1 + nth IsCyclicNumber 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := nth_isCyclicNumber_small
  rw [h0, h1, h2, h3]
  decide

/-- **Cohen's Conjecture (Ishikawa analog for cyclics)**, arXiv:2508.08335,
Conjecture `conj:Ishik1`: with `c₁ < c₂ < …` the cyclic numbers, `c_n + c_{n+1} > c_{n+2}`
for all `n > 2`. Stated with the `0`-indexed `Nat.nth`, so Cohen's `n` is `k + 1` and
`n > 2` reads `2 ≤ k`. -/
theorem cyclic_ishikawa (k : ℕ) (hk : 2 ≤ k) :
    nth IsCyclicNumber (k + 2) < nth IsCyclicNumber k + nth IsCyclicNumber (k + 1) := by
  have hinf : (Set.ofPred IsCyclicNumber).Infinite := infinite_setOf_isCyclicNumber
  have hmono : StrictMono (nth IsCyclicNumber) := nth_strictMono hinf
  have hmem : ∀ j, IsCyclicNumber (nth IsCyclicNumber j) := fun j => nth_mem_of_infinite hinf j
  have hgap : ∀ j m, nth IsCyclicNumber j < m → m < nth IsCyclicNumber (j + 1) →
      ¬ IsCyclicNumber m := fun j m hjm hmj hm =>
    (le_nth_of_lt_nth_succ hmj hm).not_gt hjm
  have h3 : 3 ≤ nth IsCyclicNumber k := by
    rw [← nth_isCyclicNumber_small.2.2.1]
    exact hmono.monotone hk
  exact lt_add_of_consecutive (hmem k) (hmem (k + 1)) h3
    (hmono (Nat.lt_succ_self k)) (hmono (Nat.lt_succ_self (k + 1))) (hgap k) (hgap (k + 1))

end Candidates.CyclicNumbersIshikawaInequality
