/-
Copyright (c) 2026 Neal Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neal Patel
-/
import Mathlib

/-!
# Erdős Problem 673: consecutive divisor ratios

For a positive natural number `n`, let its divisors be
`1 = d₁ < ⋯ < d_{τ(n)} = n`. This file defines

`G(n) = ∑ i, dᵢ / dᵢ₊₁`

and formalizes pointwise comparisons with the divisor-counting function.
The upper estimate is `G(n) ≤ τ(n)`. The lower estimate is
`τ(n / m) / m ≤ G(n)` when `m ∣ n` and `2 ≤ m`.

The live Erdős entry attributes the lower inequality to Tao, but its literal
`m = 1` boundary is false for the displayed definition of `G`: for example,
`τ(7) = 2` whereas `G(7) = 1 / 7`. This module proves the corrected `2 ≤ m`
form; it does not attribute that correction to Tao.

No almost-everywhere limit or asymptotic mean is asserted here. This is a
known-theorem formalization of the pointwise inequalities and their even-`n`
corollary.
-/

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos673

/-- The positive divisors of `n`, listed in nondecreasing order without repetition. -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- Membership in `divisorList n` is membership in `n.divisors`. -/
theorem mem_divisorList {n d : ℕ} : d ∈ divisorList n ↔ d ∈ n.divisors := by
  simp [divisorList]

/-- The list `divisorList n` is sorted in nondecreasing order. -/
theorem divisorList_pairwise (n : ℕ) : (divisorList n).Pairwise (· ≤ ·) := by
  exact Finset.pairwise_sort n.divisors (· ≤ ·)

/-- The list `divisorList n` contains no repeated divisor. -/
theorem divisorList_nodup (n : ℕ) : (divisorList n).Nodup := by
  exact Finset.sort_nodup n.divisors (· ≤ ·)

example : 3 ∈ divisorList 12 := by
  simp [mem_divisorList, Nat.mem_divisors]

example : (divisorList 12).length = 6 := by
  rw [divisorList, Finset.length_sort]
  decide

/-- The least divisor of `n` strictly larger than `d`, or `0` if no such divisor exists. -/
def nextDivisor (n d : ℕ) : ℕ :=
  if h : (n.divisors.filter (d < ·)).Nonempty then
    (n.divisors.filter (d < ·)).min' h
  else 0

example : nextDivisor 12 3 = 4 := by
  decide

example : nextDivisor 12 12 = 0 := by
  decide

/-- `G n` is the sum of `d / e` over consecutive positive divisors `d < e` of `n`.
Here `e = nextDivisor n d`; summing over all divisors other than the terminal
one `n` is exactly summing over adjacent entries of `divisorList n`. -/
def G (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors.erase n, (d : ℚ) / nextDivisor n d

example : G 1 = 0 := by
  rw [G, show (1 : ℕ).divisors.erase 1 = ∅ by
    ext d
    simp]
  simp

private lemma divisors_twelve :
    (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    have hdle : d ≤ 12 := Nat.le_of_dvd (by norm_num) hd.1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by norm_num)
    interval_cases d <;> simp_all
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

example : G 12 = 37 / 12 := by
  rw [G, divisors_twelve]
  have h1 : nextDivisor 12 1 = 2 := by decide
  have h2 : nextDivisor 12 2 = 3 := by decide
  have h3 : nextDivisor 12 3 = 4 := by decide
  have h4 : nextDivisor 12 4 = 6 := by decide
  have h6 : nextDivisor 12 6 = 12 := by decide
  have h12 : nextDivisor 12 12 = 0 := by decide
  norm_num [h1, h2, h3, h4, h6, h12]

/-- For a proper divisor `d` of positive `n`, `nextDivisor n d` is a divisor
strictly larger than `d`. -/
theorem nextDivisor_spec {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors.erase n) :
    d < nextDivisor n d ∧ nextDivisor n d ∈ n.divisors := by
  have hdn : d ∈ n.divisors := Finset.mem_of_mem_erase hd
  have hdne : d ≠ n := Finset.ne_of_mem_erase hd
  have hdle : d ≤ n := Nat.divisor_le hdn
  have hdlt : d < n := lt_of_le_of_ne hdle hdne
  have hnonempty : (n.divisors.filter (d < ·)).Nonempty := by
    refine ⟨n, Finset.mem_filter.mpr ⟨?_, hdlt⟩⟩
    exact Nat.mem_divisors_self n hn.ne'
  rw [nextDivisor, dif_pos hnonempty]
  have hmem := Finset.min'_mem (n.divisors.filter (d < ·)) hnonempty
  exact ⟨(Finset.mem_filter.mp hmem).2, (Finset.mem_filter.mp hmem).1⟩

/-- If `e` is a divisor of `n` larger than `d`, then the next divisor after
`d` is at most `e`. -/
theorem nextDivisor_le {n d e : ℕ} (hediv : e ∈ n.divisors) (hde : d < e) :
    nextDivisor n d ≤ e := by
  have hnonempty : (n.divisors.filter (d < ·)).Nonempty := by
    exact ⟨e, Finset.mem_filter.mpr ⟨hediv, hde⟩⟩
  rw [nextDivisor, dif_pos hnonempty]
  exact Finset.min'_le _ e (Finset.mem_filter.mpr ⟨hediv, hde⟩)

example : 0 < (12 : ℕ) := by norm_num

/-- Tao's upper pointwise inequality `G(n) ≤ τ(n)` for positive `n`. -/
theorem G_le_tau (n : ℕ) (hn : 0 < n) : G n ≤ n.divisors.card := by
  have hterm : ∀ d ∈ n.divisors.erase n,
      (d : ℚ) / nextDivisor n d ≤ 1 := by
    intro d hd
    have hspec := nextDivisor_spec hn hd
    have hpos : (0 : ℚ) < nextDivisor n d := by
      exact_mod_cast (Nat.zero_lt_of_lt hspec.1)
    apply (div_le_one hpos).2
    exact_mod_cast hspec.1.le
  calc
    G n ≤ ∑ _d ∈ n.divisors.erase n, (1 : ℚ) := by
      exact Finset.sum_le_sum fun d hd => hterm d hd
    _ = ((n.divisors.erase n).card : ℚ) := by simp
    _ ≤ (n.divisors.card : ℚ) := by
      exact_mod_cast (Finset.card_erase_le :
        (n.divisors.erase n).card ≤ n.divisors.card)

#check @G_le_tau

example : 0 < (12 : ℕ) ∧ 2 ∣ 12 ∧ 2 ≤ 2 := by norm_num

/-- The corrected lower pointwise inequality:
`τ(n / m) / m ≤ G(n)` when `n` is positive, `m ∣ n`, and `2 ≤ m`.
The live Erdős entry attributes the unqualified lower inequality to Tao, but
its literal `m = 1` boundary is false.

Each divisor `d` of `n / m` is a proper divisor of `n`. Its own distinct
outgoing edge in the ordered divisor list ends at `nextDivisor n d`, which is
at most `d * m`; hence that edge contributes at least `1 / m`. This direct
charging by edge origins requires no disjoint interval or overlap assumption. -/
theorem tau_div_le_G (n m : ℕ) (hn : 0 < n) (hm : m ∣ n) (hm2 : 2 ≤ m) :
    ((n / m).divisors.card : ℚ) / m ≤ G n := by
  have hmpos : 0 < m := by omega
  have hmle : m ≤ n := Nat.le_of_dvd hn hm
  have hqpos : 0 < n / m := Nat.div_pos hmle hmpos
  have hsubset : (n / m).divisors ⊆ n.divisors.erase n := by
    intro d hd
    have hddvdq : d ∣ n / m := (Nat.mem_divisors.mp hd).1
    have hddvdn : d ∣ n := hddvdq.trans (Nat.div_dvd_of_dvd hm)
    have hdleq : d ≤ n / m := Nat.divisor_le hd
    have hqltn : n / m < n := Nat.div_lt_self hn hm2
    exact Finset.mem_erase.mpr
      ⟨by omega, Nat.mem_divisors.mpr ⟨hddvdn, hn.ne'⟩⟩
  have hcharge : ∀ d ∈ (n / m).divisors,
      (1 : ℚ) / m ≤ (d : ℚ) / nextDivisor n d := by
    intro d hd
    have hddvdq : d ∣ n / m := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddvdq hqpos
    have hmuldiv : d * m ∣ n := by
      rw [Nat.mul_comm]
      exact (Nat.dvd_div_iff_mul_dvd hm).mp hddvdq
    have hmuldmem : d * m ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨hmuldiv, hn.ne'⟩
    have hdltdm : d < d * m := by nlinarith
    have hnextle : nextDivisor n d ≤ d * m :=
      nextDivisor_le hmuldmem hdltdm
    have hproper : d ∈ n.divisors.erase n := hsubset hd
    have hnextpos : 0 < nextDivisor n d :=
      Nat.zero_lt_of_lt (nextDivisor_spec hn hproper).1
    apply (div_le_div_iff₀ (by exact_mod_cast hmpos)
      (by exact_mod_cast hnextpos)).2
    norm_num
    exact_mod_cast hnextle
  calc
    ((n / m).divisors.card : ℚ) / m =
        ∑ _d ∈ (n / m).divisors, (1 : ℚ) / m := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ d ∈ (n / m).divisors, (d : ℚ) / nextDivisor n d := by
      exact Finset.sum_le_sum fun d hd => hcharge d hd
    _ ≤ ∑ d ∈ n.divisors.erase n, (d : ℚ) / nextDivisor n d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d _hd _hnot
      positivity
    _ = G n := rfl

#check @tau_div_le_G

private lemma divisors_seven : (7 : ℕ).divisors = {1, 7} := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    have hdle : d ≤ 7 := Nat.le_of_dvd (by norm_num) hd.1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by norm_num)
    interval_cases d <;> simp_all
  · intro hd
    rcases hd with rfl | rfl <;> norm_num

/-- The exact value `G(7) = 1 / 7`, used to audit the `m = 1` boundary. -/
theorem G_seven : G 7 = 1 / 7 := by
  rw [G, divisors_seven]
  have h1 : nextDivisor 7 1 = 7 := by decide
  have h7 : nextDivisor 7 7 = 0 := by decide
  norm_num [h1, h7]

/-- The blanket lower estimate at `m = 1` is false: `τ(7) = 2 > G(7) = 1/7`. -/
theorem tau_div_le_G_m_one_counterexample :
    ¬(((7 / 1).divisors.card : ℚ) / 1 ≤ G 7) := by
  rw [G_seven]
  norm_num [divisors_seven]

/-- For even `n`, the divisor count is at most twice that of `n / 2`. -/
theorem card_divisors_le_two_mul_half (n : ℕ) (heven : 2 ∣ n) :
    n.divisors.card ≤ 2 * (n / 2).divisors.card := by
  conv_lhs => rw [← Nat.div_mul_cancel heven, Nat.divisors_mul]
  calc
    ((n / 2).divisors * (2 : ℕ).divisors).card ≤
        (n / 2).divisors.card * (2 : ℕ).divisors.card := Finset.card_mul_le
    _ = 2 * (n / 2).divisors.card := by
      have htwo : (2 : ℕ).divisors.card = 2 := by decide
      rw [htwo]
      omega

/-- For positive even `n`, Tao's inequalities give `τ(n) / 4 ≤ G(n) ≤ τ(n)`. -/
theorem G_even_bounds (n : ℕ) (hn : 0 < n) (heven : 2 ∣ n) :
    (n.divisors.card : ℚ) / 4 ≤ G n ∧ G n ≤ n.divisors.card := by
  have hlower := tau_div_le_G n 2 hn heven (by norm_num)
  have hcard := card_divisors_le_two_mul_half n heven
  constructor
  · have hcardQ : (n.divisors.card : ℚ) ≤
        2 * ((n / 2).divisors.card : ℚ) := by
      exact_mod_cast hcard
    linarith
  · exact G_le_tau n hn

#check @G_even_bounds

#print axioms G_le_tau
#print axioms tau_div_le_G
#print axioms tau_div_le_G_m_one_counterexample
#print axioms G_even_bounds

end Erdos673
