/-
# Weird number times a large prime is weird; infinitely many weird numbers

## Source

* MathOverflow answer https://mathoverflow.net/a/501379 (answer id 501379),
  in a thread around Erdős problem #470 ("Are there any odd weird numbers?
  Are there infinitely many primitive weird numbers?"; Guy, UPINT B2).
* Benkoski and Erdős, "On weird and pseudoperfect numbers", Math. Comp. 28
  (1974), 617-623, where the lemma below is stated and proved.
* OEIS A006037 (weird numbers), comment by M. F. Hasler: a weird number `k`
  times a prime `p > sigma(k)` is again weird.
* No arXiv identifiers are involved.

## Informal claim (verbatim from the triage spec)

"Benkoski-Erdős lemma: if n is weird, p is prime and sigma(n) < p, then n*p
is weird. Corollary: the set {n | Nat.Weird n} is infinite, using Mathlib's
Nat.weird_seventy."

## Status (recorded 2026-10-21)

Proved in the literature (Benkoski-Erdős 1974) and restated in the
MathOverflow thread and the OEIS comment. Mathlib's
`Mathlib/NumberTheory/FactorisationProperties.lean` defines `Nat.Abundant`,
`Nat.Pseudoperfect`, `Nat.Weird` and proves `Nat.weird_seventy`, but contains
no closure or infinitude result for weird numbers. The open questions of
Erdős #470 (odd weird numbers; infinitely many primitive weird numbers) are
NOT addressed here.

## Definitions

Mathlib's notions are used verbatim:
* `Nat.Abundant n := n < ∑ i ∈ properDivisors n, i`,
* `Nat.Pseudoperfect n := 0 < n ∧ ∃ s ⊆ properDivisors n, ∑ i ∈ s, i = n`,
* `Nat.Weird n := Abundant n ∧ ¬ Pseudoperfect n`.
`sigma(n)` is spelled `∑ i ∈ n.divisors, i`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.WeirdNumbersInfinite

open Finset

/-- Ground truth: `sigma(70) = 144`, so every prime `p > 144` qualifies below. -/
theorem sum_divisors_seventy : ∑ i ∈ Nat.divisors 70, i = 144 := by decide

/-- Ground truth: `12` is abundant but pseudoperfect (`12 = 2 + 4 + 6`), hence not weird. -/
example : ¬ Nat.Weird 12 := by decide

/-- Ground truth: `70` is weird (Mathlib's `Nat.weird_seventy`). -/
example : Nat.Weird 70 := Nat.weird_seventy

/-- Non-pseudoperfect part of the Benkoski-Erdős lemma: if a positive `n` is not
pseudoperfect, `p` is prime and `sigma(n) < p`, then `n * p` is not pseudoperfect.
A subset of proper divisors of `n * p` summing to `n * p` splits into the
elements prime to `p` (divisors of `n`, total `< p` yet divisible by `p`, hence
total `0`) and multiples of `p`, which divided by `p` give proper divisors of
`n` summing to `n`. -/
theorem not_pseudoperfect_mul_prime {n p : ℕ} (hn : 0 < n) (hnp : ¬ n.Pseudoperfect)
    (hp : p.Prime) (hlt : ∑ i ∈ n.divisors, i < p) : ¬ (n * p).Pseudoperfect := by
  rintro ⟨-, s, hs, hsum⟩
  set A := s.filter (fun d => ¬ p ∣ d) with hA
  set B := s.filter (fun d => p ∣ d) with hB
  have hsplit : ∑ d ∈ B, d + ∑ d ∈ A, d = n * p :=
    (sum_filter_add_sum_filter_not s (fun d => p ∣ d) id).trans hsum
  -- elements of `A` divide `n`
  have hAsub : A ⊆ n.divisors := by
    intro d hd
    rw [hA, mem_filter] at hd
    have hdnp : d ∣ n * p := (Nat.mem_properDivisors.mp (hs hd.1)).1
    have hcop : d.Coprime p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd.2))
    exact Nat.mem_divisors.mpr ⟨hcop.dvd_of_dvd_mul_right hdnp, hn.ne'⟩
  have hAlt : ∑ d ∈ A, d < p := lt_of_le_of_lt (sum_le_sum_of_subset hAsub) hlt
  have hBdvd : p ∣ ∑ d ∈ B, d := dvd_sum fun d hd => (mem_filter.mp hd).2
  have hAdvd : p ∣ ∑ d ∈ A, d := by
    have h1 : p ∣ ∑ d ∈ B, d + ∑ d ∈ A, d := hsplit ▸ dvd_mul_left p n
    exact (Nat.dvd_add_right hBdvd).mp h1
  have hA0 : ∑ d ∈ A, d = 0 := Nat.eq_zero_of_dvd_of_lt hAdvd hAlt
  have hBsum : ∑ d ∈ B, d = n * p := by omega
  -- divide `B` by `p`
  have hinj : Set.InjOn (fun d => d / p) (B : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : p ∣ x := (mem_filter.mp hx).2
    have hy' : p ∣ y := (mem_filter.mp hy).2
    exact (Nat.div_left_inj hx' hy').mp hxy
  have hsumB' : (∑ e ∈ B.image (fun d => d / p), e) * p = n * p := by
    rw [sum_image hinj, sum_mul, ← hBsum]
    exact sum_congr rfl fun d hd => Nat.div_mul_cancel (mem_filter.mp hd).2
  have hsubB' : B.image (fun d => d / p) ⊆ n.properDivisors := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    have hpd : p ∣ d := (mem_filter.mp hd).2
    have hdpd := Nat.mem_properDivisors.mp (hs (mem_filter.mp hd).1)
    obtain ⟨k, rfl⟩ := hpd
    rw [Nat.mul_div_cancel_left k hp.pos]
    refine Nat.mem_properDivisors.mpr ⟨?_, ?_⟩
    · have hkdvd : p * k ∣ p * n := by rw [mul_comm p n]; exact hdpd.1
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos hkdvd
    · have hklt : p * k < p * n := by rw [mul_comm p n]; exact hdpd.2
      exact lt_of_mul_lt_mul_left hklt (Nat.zero_le p)
  exact hnp ⟨hn, _, hsubB', Nat.eq_of_mul_eq_mul_right hp.pos hsumB'⟩

/-- Benkoski-Erdős lemma (Math. Comp. 1974; MathOverflow answer 501379;
OEIS A006037 comment by M. F. Hasler): if `n` is weird, `p` is prime and
`sigma(n) < p`, then `n * p` is weird. -/
theorem weird_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime)
    (hlt : ∑ i ∈ n.divisors, i < p) : (n * p).Weird := by
  have hnpos : 0 < n := hn.pos
  have habund : (n * p).Abundant :=
    hn.1.of_dvd (dvd_mul_right n p) (Nat.mul_ne_zero hnpos.ne' hp.ne_zero)
  exact ⟨habund, not_pseudoperfect_mul_prime hnpos hn.2 hp hlt⟩

/-- Non-vacuity of `weird_mul_prime`: its hypotheses hold jointly at `n = 70`,
`p = 149`, giving the weird number `10430`. -/
example : Nat.Weird (70 * 149) :=
  weird_mul_prime Nat.weird_seventy (by norm_num) (by rw [sum_divisors_seventy]; norm_num)

/-- Corollary (Benkoski-Erdős; MathOverflow answer 501379): there are infinitely
many weird numbers. For every bound `a`, a prime `p > max a 144` gives the weird
number `70 * p > a`. -/
theorem infinite_weird : {n : ℕ | n.Weird}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (max a 144 + 1)
  have hap : a < p := by omega
  have hsig : ∑ i ∈ Nat.divisors 70, i < p := by rw [sum_divisors_seventy]; omega
  refine ⟨70 * p, weird_mul_prime Nat.weird_seventy hp hsig, ?_⟩
  omega

end Candidates.WeirdNumbersInfinite
