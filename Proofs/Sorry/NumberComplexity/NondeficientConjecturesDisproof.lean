/-
# Ross's Conjecture 17 on `{-1,1}`-perfect numbers is false

## Source

* arXiv:2607.11043, John M. Campbell, "Disproofs of two conjectures
  concerning nondeficient numbers".  Section 3 ("Disproof of Ross's second
  conjecture"), the unnumbered Theorem 3.1, with Lemma 2.1 (the criterion
  `lem:criterion`) from Section 2.
* The refuted conjecture: J. Ross, J. Integer Seq. 27 (2024),
  Art. 24.7.5, Conjecture 17.

Recorded 2026-10-21.

## Verbatim informal claims (from the paper)

Definition: "letting the positive divisors of a positive integer `n` be
written as `1 = d_0 < d_1 < ... < d_k < d_{k+1} = n`, ... if there exist
values `λ_j ∈ S` such that `1 + Σ_{j=1}^k λ_j d_j = n`, then `n` is said to
be an `S`-perfect number."

Ross's Conjecture 17 (as quoted): "every nonsquare odd nondeficient number is
`{-1,1}`-perfect", where `n` is nondeficient if `σ(n) ≥ 2n`.

Lemma 2.1: "For an integer `n` exceeding `1` ... `n ∈ P` if and only if
`(σ(n) - 2n)/2` is a sum of distinct divisors chosen from `d_1, ..., d_k`,
allowing for the possibility of an empty sum."

Theorem 3.1: "Let `a` be an odd abundant square.  If `p` is a prime such
that `p > σ(a)`, then `n = ap` is an odd nonsquare abundant number, but
`n ∉ P`."

## Status

Proved in the paper.  The paper suggests `a = 945^2`; this module uses the
smaller instance `a = 105^2 = 11025` (`σ(11025) = 22971`) with the prime
`p = 22973`, giving the counterexample `n = 253277325`.  (Triage reports an
exhaustive search finding this to be the least counterexample; that
minimality is *not* formalized here.)

## Formalization notes

* `SignPerfect n` is Ross's `{-1,1}`-perfectness: `0 < n` and some sign
  assignment `ε : ℕ → ℤ` with values in `{1, -1}` gives
  `1 + Σ_{d ∈ D} ε d * d = n`, where
  `D = n.properDivisors.erase 1` is exactly the set `{d_1, ..., d_k}` of
  divisors of `n` other than `1` and `n`.  For `n = 1` the paper's indexing
  degenerates; our definition makes `1` sign-perfect, which is irrelevant to
  every statement below (all concern `n > 1`).
* Abundance uses Mathlib's `Nat.Abundant` (`n < Σ properDivisors`), shown
  equivalent to `2n < σ(n)` in `abundant_iff_two_mul_lt_sigma`.
-/
import Mathlib

set_option autoImplicit false

namespace NondeficientConjecturesDisproof

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Ross's `{-1,1}`-perfect numbers: a positive integer `n` such that, for
the divisors `d_1 < ... < d_k` of `n` other than `1` and `n`, there are signs
`λ_j ∈ {-1, 1}` with `1 + Σ λ_j d_j = n`. -/
def SignPerfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
    1 + ∑ d ∈ n.properDivisors.erase 1, ε d * (d : ℤ) = n

/-- Mathlib's `Nat.Abundant` agrees with the paper's `σ(n) > 2n`. -/
theorem abundant_iff_two_mul_lt_sigma (n : ℕ) : n.Abundant ↔ 2 * n < σ 1 n := by
  unfold Nat.Abundant
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- A signed sum with signs in `{1, -1}` equals the plain sum minus twice the
sum over the negatively signed terms. -/
theorem signed_sum_eq (D : Finset ℕ) (ε : ℕ → ℤ) (hε : ∀ d, ε d = 1 ∨ ε d = -1) :
    ∑ d ∈ D, ε d * (d : ℤ) =
      ∑ d ∈ D, (d : ℤ) - 2 * ∑ d ∈ D.filter (fun d => ε d = -1), (d : ℤ) := by
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rcases hε d with h | h
  · rw [h, if_neg (by norm_num)]
    ring
  · rw [h, if_pos rfl]
    ring

/-- For `n > 1`, the divisors of `n` other than `1` and `n` sum to
`σ(n) - n - 1`. -/
theorem sum_nontrivial_divisors {n : ℕ} (hn : 1 < n) :
    ∑ d ∈ n.properDivisors.erase 1, (d : ℤ) = (σ 1 n : ℤ) - n - 1 := by
  have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.2 hn
  have hnat : 1 + ∑ d ∈ n.properDivisors.erase 1, d = ∑ d ∈ n.properDivisors, d :=
    Finset.add_sum_erase _ (fun d => d) h1
  have hσ : σ 1 n = ∑ d ∈ n.properDivisors, d + n := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  rw [← Nat.cast_sum]
  omega

/-- **Lemma 2.1** (criterion).  For `n > 1`, `n` is `{-1,1}`-perfect iff
`σ(n) - 2n` is twice a (possibly empty) sum of distinct divisors of `n`
other than `1` and `n`. -/
theorem signPerfect_iff {n : ℕ} (hn : 1 < n) :
    SignPerfect n ↔ ∃ T ⊆ n.properDivisors.erase 1,
      2 * ∑ d ∈ T, (d : ℤ) = (σ 1 n : ℤ) - 2 * n := by
  have hD := sum_nontrivial_divisors hn
  constructor
  · rintro ⟨_, ε, hε, heq⟩
    refine ⟨(n.properDivisors.erase 1).filter (fun d => ε d = -1),
      Finset.filter_subset _ _, ?_⟩
    rw [signed_sum_eq _ ε hε] at heq
    linarith
  · rintro ⟨T, hT, heq⟩
    refine ⟨by omega, fun d => if d ∈ T then -1 else 1, ?_, ?_⟩
    · intro d
      by_cases hd : d ∈ T <;> simp [hd]
    · have hfil : (n.properDivisors.erase 1).filter
          (fun d => (if d ∈ T then (-1 : ℤ) else 1) = -1) = T := by
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_, h⟩
          by_contra hdT
          simp [hdT] at h
        · intro hd
          exact ⟨hT hd, by simp [hd]⟩
      rw [signed_sum_eq _ _ (fun d => by by_cases hd : d ∈ T <;> simp [hd]), hfil]
      linarith

/-- An odd square has an odd number of divisors. -/
theorem odd_card_divisors_of_isSquare {a : ℕ} (ha : a ≠ 0) (hsq : IsSquare a) :
    Odd a.divisors.card := by
  obtain ⟨m, rfl⟩ := hsq
  have hm : m ≠ 0 := by
    rintro rfl
    simp at ha
  rw [Nat.card_divisors ha]
  apply Finset.prod_induction _ Odd (fun _ _ hx hy => hx.mul hy) odd_one
  intro q _
  rw [Nat.factorization_mul hm hm, Finsupp.add_apply]
  exact ⟨m.factorization q, by ring⟩

/-- `σ(a)` is odd when `a` is an odd square. -/
theorem odd_sigma_one_of_odd_of_isSquare {a : ℕ} (ha : Odd a) (hsq : IsSquare a) :
    Odd (σ 1 a) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  rw [sigma_one_apply, Finset.odd_sum_iff_odd_card_odd]
  have hfil : a.divisors.filter (fun x => Odd x) = a.divisors := by
    apply Finset.filter_true_of_mem
    intro d hd
    exact ha.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  rw [hfil]
  exact odd_card_divisors_of_isSquare ha0 hsq

/-- Every sum of distinct divisors of `a * p` (`p` prime, `a ≠ 0`) has the
form `A * p + B` with `B ≤ σ(a)`. -/
theorem exists_sum_eq_mul_add {a p : ℕ} (hp : p.Prime) (ha : a ≠ 0) (T : Finset ℕ)
    (hT : ∀ d ∈ T, d ∣ a * p) :
    ∃ A B : ℕ, ∑ d ∈ T, d = A * p + B ∧ B ≤ σ 1 a := by
  rw [← Finset.sum_filter_add_sum_filter_not T (· ∣ a)]
  have hB : ∑ d ∈ T.filter (· ∣ a), d ≤ σ 1 a := by
    rw [sigma_one_apply]
    apply Finset.sum_le_sum_of_subset
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.2 ⟨hd.2, ha⟩
  have hA : p ∣ ∑ d ∈ T.filter (fun d => ¬ d ∣ a), d := by
    apply Finset.dvd_sum
    intro d hd
    rw [Finset.mem_filter] at hd
    by_contra hpd
    have hcop : d.Coprime p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd)
    exact hd.2 (hcop.dvd_of_dvd_mul_right (hT d hd.1))
  obtain ⟨A, hAeq⟩ := hA
  refine ⟨A, ∑ d ∈ T.filter (· ∣ a), d, ?_, hB⟩
  rw [hAeq]
  ring

/-- The arithmetic heart of Theorem 3.1: with `0 ≤ B ≤ s < p` and `s` odd,
`2 (A p + B) = s (p + 1) - 2 a p` is impossible. -/
theorem core_arith (s p a A B : ℤ) (hB0 : 0 ≤ B) (hBs : B ≤ s) (hsp : s < p)
    (hs : Odd s) (h : 2 * (A * p + B) = s * (p + 1) - 2 * (a * p)) : False := by
  obtain ⟨t, rfl⟩ := hs
  have key : 2 * B = (2 * t + 1 - 2 * a - 2 * A) * p + (2 * t + 1) := by linarith
  rcases lt_trichotomy (2 * t + 1 - 2 * a - 2 * A) 0 with hk | hk | hk
  · have hkp : (2 * t + 1 - 2 * a - 2 * A) * p ≤ -p := by nlinarith
    linarith
  · rw [hk] at key
    omega
  · have hkp : p ≤ (2 * t + 1 - 2 * a - 2 * A) * p := by nlinarith
    linarith

/-- **Theorem 3.1** (Campbell).  If `a` is an odd abundant square and `p` is
a prime with `σ(a) < p`, then `n = a p` is odd, not a square, abundant, and
not `{-1,1}`-perfect. -/
theorem thm_3_1 {a p : ℕ} (ha : Odd a) (hsq : IsSquare a) (hab : a.Abundant)
    (hp : p.Prime) (hpa : σ 1 a < p) :
    Odd (a * p) ∧ ¬ IsSquare (a * p) ∧ (a * p).Abundant ∧ ¬ SignPerfect (a * p) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hσa : 2 * a < σ 1 a := (abundant_iff_two_mul_lt_sigma a).1 hab
  have hap : a < p := by omega
  have hndvd : ¬ p ∣ a := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) h) (by omega)
  have hcop : a.Coprime p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
  have hσp : σ 1 p = p + 1 := by
    simpa [Finset.sum_range_succ, add_comm] using sigma_one_apply_prime_pow (i := 1) hp
  have hσn : σ 1 (a * p) = σ 1 a * (p + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, hσp]
  refine ⟨ha.mul (hp.odd_of_ne_two (by omega)), ?_, ?_, ?_⟩
  · -- the exponent of `p` in `a p` is `1`
    rintro ⟨m, hm⟩
    have hpm : p ∣ m := by
      have hdvd : p ∣ m * m := hm ▸ dvd_mul_left p a
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h <;> exact h
    obtain ⟨r, rfl⟩ := hpm
    have hpos : 0 < p := hp.pos
    have hcancel : a = r * (p * r) := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hm]
      ring
    exact hndvd ⟨r * r, by rw [hcancel]; ring⟩
  · rw [abundant_iff_two_mul_lt_sigma, hσn]
    nlinarith
  · intro hsp
    have hn1 : 1 < a * p := by nlinarith [Nat.pos_of_ne_zero ha0]
    obtain ⟨T, hT, heq⟩ := (signPerfect_iff hn1).1 hsp
    have hTdvd : ∀ d ∈ T, d ∣ a * p := fun d hd =>
      (Nat.mem_properDivisors.1 (Finset.mem_of_mem_erase (hT hd))).1
    obtain ⟨A, B, hsum, hBle⟩ := exists_sum_eq_mul_add hp ha0 T hTdvd
    have hodd : Odd (σ 1 a : ℤ) := by exact_mod_cast odd_sigma_one_of_odd_of_isSquare ha hsq
    have h' : 2 * ((A : ℤ) * p + B) = (σ 1 a : ℤ) * (p + 1) - 2 * (a * p) := by
      rw [← Nat.cast_sum, hsum, hσn] at heq
      push_cast at heq
      linarith
    exact core_arith (σ 1 a) p a A B (by positivity) (by exact_mod_cast hBle)
      (by exact_mod_cast hpa) hodd h'

/-- `σ(105^2) = σ(9) σ(25) σ(49) = 13 · 31 · 57 = 22971`. -/
theorem sigma_one_11025 : σ 1 11025 = 22971 := by
  have h1 : σ 1 (9 * (25 * 49)) = σ 1 9 * (σ 1 25 * σ 1 49) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have h9 : σ 1 9 = 13 := by decide
  have h25 : σ 1 25 = 31 := by decide
  have h49 : σ 1 49 = 57 := by decide
  rw [h9, h25, h49] at h1
  exact h1

/-- The explicit counterexample `n = 253277325 = 105^2 · 22973` to Ross's
Conjecture 17: it is odd, not a square, abundant, and not `{-1,1}`-perfect. -/
theorem counterexample_253277325 :
    Odd 253277325 ∧ ¬ IsSquare 253277325 ∧ Nat.Abundant 253277325 ∧
      ¬ SignPerfect 253277325 := by
  have hodd : Odd 11025 := ⟨5512, by norm_num⟩
  have hsq : IsSquare 11025 := ⟨105, by norm_num⟩
  have hab : Nat.Abundant 11025 := by
    rw [abundant_iff_two_mul_lt_sigma, sigma_one_11025]
    norm_num
  have hp : Nat.Prime 22973 := by norm_num
  have hlt : σ 1 11025 < 22973 := by
    rw [sigma_one_11025]
    norm_num
  have h := thm_3_1 hodd hsq hab hp hlt
  have hn : (11025 * 22973 : ℕ) = 253277325 := by norm_num
  rwa [hn] at h

/-- **Ross's Conjecture 17 is false** (Campbell, arXiv:2607.11043, §3): it is
not the case that every odd, nonsquare, nondeficient (`2n ≤ σ(n)`) number is
`{-1,1}`-perfect. -/
theorem not_ross_conjecture_17 :
    ¬ ∀ n : ℕ, Odd n → ¬ IsSquare n → 2 * n ≤ σ 1 n → SignPerfect n := by
  intro h
  obtain ⟨hodd, hsq, hab, hnot⟩ := counterexample_253277325
  exact hnot (h _ hodd hsq ((abundant_iff_two_mul_lt_sigma _).1 hab).le)

/-! ## Ground-truth checks -/

/-- `12` is `{-1,1}`-perfect: `1 - 2 + 3 + 4 + 6 = 12`. -/
example : SignPerfect 12 := by
  rw [signPerfect_iff (by norm_num)]
  refine ⟨{2}, by decide, ?_⟩
  have h : σ 1 12 = 28 := by decide
  rw [h]
  norm_num

/-- `18` is nondeficient (`σ(18) = 39`) but not `{-1,1}`-perfect, as Ross
observed: `σ(18) - 36 = 3` is odd. -/
example : 2 * 18 ≤ σ 1 18 ∧ ¬ SignPerfect 18 := by
  have h : σ 1 18 = 39 := by decide
  refine ⟨by rw [h]; norm_num, ?_⟩
  rw [signPerfect_iff (by norm_num), h]
  rintro ⟨T, _, hT⟩
  omega

end NondeficientConjecturesDisproof
