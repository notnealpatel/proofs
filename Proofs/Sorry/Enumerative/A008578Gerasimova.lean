/-
# A008578 — Gerasimova: `sigma(k) > k * Omega(k)` iff `k = 1` or `k` prime

## OEIS source (retrieved with `oeis show A008578`, 2026-10-21)

```
NAME:     Prime numbers at the beginning of the 20th century (today 1 is no
          longer regarded as a prime).
TERMS:    1,2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,...
COMMENT:  Positive integers that have no divisors other than 1 and itself (the
          old definition of prime numbers). - _Omar E. Pol_, Aug 10 2012
COMMENT (the conjecture):
  Conjecture: the sequence contains exactly those k such that
  sigma(k) > k*BigOmega(k). - _Irina Gerasimova_, Jun 08 2013
COMMENT (status note in the entry):
  Note on the Gerasimova conjecture: all terms in the sequence obviously
  satisfy the inequality, because sigma(p) = 1+p and BigOmega(p) = 1 for
  primes p, so 1+p > p*1. For composites, the (opposite) inequality is
  heuristically correct at least up to k <= 4400000. The general proof
  requires to show that BigOmega(k) is an upper limit of the abundancy
  sigma(k)/k for composite k. [...] - _R. J. Mathar_, Jun 12 2013
```

## Status

Triage status: open (the entry asks for a general proof; a web search found no
published one).  Computation (this campaign): the characterization holds for
every `k ≤ 10^6`, and `sigma(k) = k * Omega(k)` occurs there only at `k = 6`.

## Proof outline (kernel-checked below)

Let `S` be the set of prime factors of a composite `k`, `r = |S| = omega(k)`.
Removing the largest element `a` of a finset of integers `≥ 2` leaves at most
`a - 2` elements, which drives two finset inductions:

* `∏_{p ∈ S} p ≤ (r + 1) ∏_{p ∈ S} (p - 1)`, hence (with
  `sigma(p^e) (p - 1) ≤ p^e p`) `sigma(k) ≤ (omega(k) + 1) k`;
* `2 ∏_{p ∈ S} (p + 1) ≤ (r + 2) ∏_{p ∈ S} p`, hence for squarefree `k`,
  `2 sigma(k) ≤ (omega(k) + 2) k`.

If `k` is not squarefree then `omega(k) + 1 ≤ Omega(k)`; if it is squarefree
and composite then `omega(k) = Omega(k) ≥ 2`, so `(omega + 2)/2 ≤ Omega`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A008578Gerasimova

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega ArithmeticFunction.omega

/-! ## Definition layer -/

/-- Membership in A008578, following Omar E. Pol's comment in the entry:
positive integers that have no divisors other than `1` and itself. -/
def IsA008578 (k : ℕ) : Prop :=
  0 < k ∧ ∀ d, d ∣ k → d = 1 ∨ d = k

/-- The entry's definition agrees with "`k = 1` or `k` is prime". -/
theorem isA008578_iff (k : ℕ) : IsA008578 k ↔ k = 1 ∨ k.Prime := by
  constructor
  · rintro ⟨hpos, hdiv⟩
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · left; omega
    · right; exact Nat.prime_def.mpr ⟨hge, hdiv⟩
  · rintro (rfl | hp)
    · exact ⟨Nat.one_pos, fun d hd => Or.inl (Nat.dvd_one.mp hd)⟩
    · exact ⟨hp.pos, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

instance (k : ℕ) : Decidable (IsA008578 k) :=
  decidable_of_iff _ (isA008578_iff k).symm

/-- Ground truth: the members of A008578 below `50` are exactly the first
sixteen listed terms `1, 2, 3, 5, …, 47`. -/
example : (Finset.range 50).filter IsA008578 =
    {1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by
  decide

/-- Ground truth for the arithmetic functions in the statement. -/
example : σ 1 12 = 28 ∧ σ 1 6 = 12 ∧ σ 1 7 = 8 := by
  decide

/-- Ground truth for `Omega`: `Omega(12) = 3`, `Omega(6) = 2`, `Omega(7) = 1`. -/
example : Ω 12 = 3 ∧ Ω 6 = 2 ∧ Ω 7 = 1 := by
  have h7 : Nat.Prime 7 := by norm_num
  refine ⟨?_, ?_, cardFactors_apply_prime h7⟩
  · rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, cardFactors_mul (by norm_num) (by norm_num),
      cardFactors_apply_prime_pow Nat.prime_two, cardFactors_apply_prime Nat.prime_three]
  · rw [show (6 : ℕ) = 2 * 3 by norm_num, cardFactors_mul (by norm_num) (by norm_num),
      cardFactors_apply_prime Nat.prime_two, cardFactors_apply_prime Nat.prime_three]

/-! ## Finset inductions on a set of integers `≥ 2` -/

/-- If every element of `s` is `≥ 2` and below `a`, then `|s| + 2 ≤ a`. -/
theorem card_add_two_le_of_forall_lt {s : Finset ℕ} {a : ℕ}
    (h2 : ∀ p ∈ s, 2 ≤ p) (hlt : ∀ p ∈ s, p < a) (ha : 2 ≤ a) : s.card + 2 ≤ a := by
  have hsub : s ⊆ Finset.Ico 2 a := fun p hp =>
    Finset.mem_Ico.mpr ⟨h2 p hp, hlt p hp⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  omega

/-- For a finset `S` of integers `≥ 2`: `∏ p ≤ (|S| + 1) ∏ (p - 1)`, i.e.
`∏ p/(p-1) ≤ |S| + 1`. -/
theorem prod_le_card_succ_mul_prod_pred (S : Finset ℕ) (h2 : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, p ≤ (S.card + 1) * ∏ p ∈ S, (p - 1) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hcard := card_add_two_le_of_forall_lt h2s hlt ha
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.card_insert_of_notMem has]
    have hkey : a * (s.card + 1) ≤ (s.card + 1 + 1) * (a - 1) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    calc a * ∏ p ∈ s, p ≤ a * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
          Nat.mul_le_mul_left a (ih h2s)
      _ = (a * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((s.card + 1 + 1) * (a - 1)) * ∏ p ∈ s, (p - 1) :=
          Nat.mul_le_mul_right _ hkey
      _ = _ := by ring

/-- For a finset `S` of integers `≥ 2`: `2 ∏ (p + 1) ≤ (|S| + 2) ∏ p`, i.e.
`∏ (1 + 1/p) ≤ (|S| + 2)/2`. -/
theorem two_mul_prod_succ_le (S : Finset ℕ) (h2 : ∀ p ∈ S, 2 ≤ p) :
    2 * ∏ p ∈ S, (p + 1) ≤ (S.card + 2) * ∏ p ∈ S, p := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hcard := card_add_two_le_of_forall_lt h2s hlt ha
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.card_insert_of_notMem has]
    have hkey : (a + 1) * (s.card + 2) ≤ (s.card + 1 + 2) * a := by nlinarith
    calc 2 * ((a + 1) * ∏ p ∈ s, (p + 1)) = (a + 1) * (2 * ∏ p ∈ s, (p + 1)) := by ring
      _ ≤ (a + 1) * ((s.card + 2) * ∏ p ∈ s, p) := Nat.mul_le_mul_left _ (ih h2s)
      _ = ((a + 1) * (s.card + 2)) * ∏ p ∈ s, p := by ring
      _ ≤ ((s.card + 1 + 2) * a) * ∏ p ∈ s, p := Nat.mul_le_mul_right _ hkey
      _ = _ := by ring

/-! ## Abundancy bounds -/

/-- Geometric sum bound: `(1 + p + ⋯ + p^e)(p - 1) ≤ p^e · p`. -/
theorem geom_sum_mul_pred_le (p e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) * (p - 1) ≤ p ^ e * p := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, add_mul]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have hsplit : p ^ (e + 1) * (p - 1) + p ^ (e + 1) = p ^ (e + 1) * p := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      calc _ ≤ p ^ e * p + p ^ (e + 1) * (p - 1) := Nat.add_le_add_right ih _
        _ = _ := by rw [← pow_succ]; omega

/-- `omega(k)` is the number of prime factors of `k`. -/
theorem cardDistinctFactors_eq_card_primeFactors (k : ℕ) : ω k = k.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- `omega(k) ≤ Omega(k)`. -/
theorem cardDistinctFactors_le_cardFactors (k : ℕ) : ω k ≤ Ω k := by
  rw [cardDistinctFactors_apply, cardFactors_apply]
  exact (List.dedup_sublist _).length_le

/-- `sigma(p) = p + 1` for a prime `p`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- Abundancy bound: `sigma(k) ≤ (omega(k) + 1) k` for every `k`. -/
theorem sigma_le_cardDistinctFactors_succ_mul (k : ℕ) : σ 1 k ≤ (ω k + 1) * k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h2 : ∀ p ∈ k.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hsig : σ 1 k =
      ∏ p ∈ k.primeFactors, ∑ i ∈ Finset.range (k.factorization p + 1), p ^ i := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hk.ne']
    simp only [mul_one]
  have hk_eq : ∏ p ∈ k.primeFactors, p ^ k.factorization p = k :=
    (Nat.prod_primeFactors_pow_factorization hk.ne').symm
  have hpos : 0 < ∏ p ∈ k.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := h2 p hp; omega
  have hlocal : (σ 1 k) * ∏ p ∈ k.primeFactors, (p - 1) ≤ k * ∏ p ∈ k.primeFactors, p :=
    calc (σ 1 k) * ∏ p ∈ k.primeFactors, (p - 1)
        = ∏ p ∈ k.primeFactors,
            (∑ i ∈ Finset.range (k.factorization p + 1), p ^ i) * (p - 1) := by
          rw [hsig, ← Finset.prod_mul_distrib]
      _ ≤ ∏ p ∈ k.primeFactors, p ^ k.factorization p * p :=
          Finset.prod_le_prod' fun p _ => geom_sum_mul_pred_le p _
      _ = k * ∏ p ∈ k.primeFactors, p := by rw [Finset.prod_mul_distrib, hk_eq]
  have hprod := prod_le_card_succ_mul_prod_pred k.primeFactors h2
  rw [cardDistinctFactors_eq_card_primeFactors]
  have hchain : (σ 1 k) * ∏ p ∈ k.primeFactors, (p - 1) ≤
      ((k.primeFactors.card + 1) * k) * ∏ p ∈ k.primeFactors, (p - 1) :=
    calc (σ 1 k) * ∏ p ∈ k.primeFactors, (p - 1) ≤ k * ∏ p ∈ k.primeFactors, p := hlocal
      _ ≤ k * ((k.primeFactors.card + 1) * ∏ p ∈ k.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left k hprod
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hchain hpos

/-- Squarefree abundancy bound: `2 sigma(k) ≤ (omega(k) + 2) k` for squarefree `k`. -/
theorem two_mul_sigma_le_of_squarefree {k : ℕ} (hsq : Squarefree k) :
    2 * σ 1 k ≤ (ω k + 2) * k := by
  have hprime : ∀ p ∈ k.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hk_eq : ∏ p ∈ k.primeFactors, p = k := Nat.prod_primeFactors_of_squarefree hsq
  have hsig : σ 1 k = ∏ p ∈ k.primeFactors, (p + 1) := by
    calc σ 1 k = σ 1 (∏ p ∈ k.primeFactors, p) := by rw [hk_eq]
      _ = ∏ p ∈ k.primeFactors, σ 1 p :=
          isMultiplicative_sigma.map_prod_of_prime k.primeFactors hprime
      _ = _ := Finset.prod_congr rfl fun p hp => sigma_one_prime (hprime p hp)
  have hb := two_mul_prod_succ_le k.primeFactors fun p hp => (hprime p hp).two_le
  rw [hk_eq] at hb
  rw [cardDistinctFactors_eq_card_primeFactors, hsig]
  exact hb

/-! ## The conjecture -/

/-- The composite half: for every composite `k` (`1 < k`, not prime),
`sigma(k) ≤ k * Omega(k)`; that is, `Omega(k)` bounds the abundancy
`sigma(k)/k`, the bound R. J. Mathar's note in A008578 asks for. -/
theorem sigma_le_mul_cardFactors {k : ℕ} (h1 : 1 < k) (hp : ¬ k.Prime) :
    σ 1 k ≤ k * Ω k := by
  have hk0 : k ≠ 0 := by omega
  have hΩ2 : 2 ≤ Ω k := by
    have hpos : 0 < Ω k := cardFactors_pos_iff_one_lt.mpr h1
    have hne : Ω k ≠ 1 := fun h => hp (cardFactors_eq_one_iff_prime.mp h)
    omega
  by_cases hsq : Squarefree k
  · have hωΩ : ω k = Ω k := (cardDistinctFactors_eq_cardFactors_iff_squarefree hk0).mpr hsq
    have hb := two_mul_sigma_le_of_squarefree hsq
    rw [hωΩ] at hb
    have hstep : (Ω k + 2) * k ≤ 2 * (k * Ω k) := by nlinarith
    omega
  · have hne : ω k ≠ Ω k := fun h =>
      hsq ((cardDistinctFactors_eq_cardFactors_iff_squarefree hk0).mp h)
    have hlt : ω k + 1 ≤ Ω k := by
      have := cardDistinctFactors_le_cardFactors k
      omega
    calc σ 1 k ≤ (ω k + 1) * k := sigma_le_cardDistinctFactors_succ_mul k
      _ ≤ Ω k * k := Nat.mul_le_mul_right k hlt
      _ = k * Ω k := Nat.mul_comm _ _

/-- **Gerasimova's conjecture (A008578, Irina Gerasimova, Jun 08 2013).**

Verbatim: "Conjecture: the sequence contains exactly those k such that
sigma(k) > k*BigOmega(k)."  Here the sequence is A008578 (`1` and the primes,
`IsA008578`), `sigma = σ 1` and `BigOmega = Ω`.  The statement is given for every
natural `k`; at `k = 0` both sides are false (`σ 1 0 = 0`), so it contains the
statement over positive integers. -/
theorem gerasimova (k : ℕ) : k * Ω k < σ 1 k ↔ IsA008578 k := by
  rw [isA008578_iff]
  constructor
  · intro hlt
    by_contra hcon
    push Not at hcon
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp at hlt
      · exact hcon.1 rfl
    · exact absurd (sigma_le_mul_cardFactors (by omega) hcon.2) (not_le.mpr hlt)
  · rintro (rfl | hp)
    · simp
    · rw [cardFactors_apply_prime hp, sigma_one_prime hp]
      omega

end Candidates.A008578Gerasimova
