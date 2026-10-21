/-
# A210445 — Sun: the least `k` with `k * n` practical is below `n` (and below `n / 2`)

## OEIS source (retrieved with `oeis show A210445` and from oeis.org, 2026-10-21)

```
NAME:     Least positive integer k with k*n practical.
TERMS:    1,1,2,1,4,1,4,1,2,2,6,1,6,2,2,1,12,1,12,1,2,3,12,1,4,3,2,1,12,1,16,1,
          2,6,4,1,18,6,2,1,20,1,20,2,2,6,24,1,4,2,4,2,24,1,4,1,4,6,24,1,24,8,...
COMMENT (the conjecture):
  Conjecture: a(n) < n for all n>1, and a(n) < n/2 for all n>47.
AUTHOR:   Zhi-Wei Sun, Jan 20 2013
LINKS:    Zhi-Wei Sun, Table of n, a(n) for n = 1..10000;
          Zhi-Wei Sun, Conjectures involving primes and quadratic forms,
          arXiv:1211.1588 [math.NT], 2012-2015.
```

The conjecture line carries no signature of its own; it belongs to the entry's
author, Zhi-Wei Sun (Jan 20 2013).

## Literature status (triage)

Open as far as the triage could tell: neither the entry, nor Sun's
arXiv:1211.1588, nor the A210444 comment (which derives part (i) from a
twin-prime-type conjecture) contains a proof.

## Result of this module

Both parts are proved here, from Melfi's Lemma 4
(`Nat.Practical.mul_of_le_one_add_sum_divisors`: `m` practical and
`0 < t ≤ 1 + σ(m)` give `m * t` practical).  It suffices to find a practical `m`
with `m < n` (resp. `2 * m < n`) and `n ≤ 1 + σ(m)`, and take `k = m`.

* (i) `m = 2 ^ c` with `2 ^ c < n ≤ 2 ^ (c + 1) = 1 + σ(2 ^ c)`.
* (ii) For `n > 96` take `w = 2 ^ e` with `96 w < n ≤ 192 w`; the three
  practical numbers `48 w`, `60 w`, `72 w` have Lemma-4 windows
  `(96 w, 128 w - 3]`, `(120 w, 192 w - 23]`, `(144 w, 208 w - 12]`, which cover
  `(96 w, 192 w]`.  For `48 ≤ n ≤ 96` the witnesses are `k = 1` (`n = 48`) and
  `m = 24, 30, 36, 42`.

The bound `47` is sharp: `a 47 = 24` (`a_forty_seven`), and `2 * 24 = 48`.
Computation agrees: a brute-force run of `a(n)` for `n ≤ 20000` via Stewart's
criterion (first 100 values match the DATA line) finds no failure of (i) or (ii),
`a(47) = 24`, and `max 2 a(n) / n = 96/101` over `47 < n ≤ 20000`; the triage's
family check reached `10 ^ 6`.
-/
import Mathlib
import Enumerative.Practical
import Enumerative.StewartCriterion
import Enumerative.MelfiPracticalSum

set_option autoImplicit false

namespace Candidates.A210445MinPracticalSun

/-! ## Definition layer

`Nat.Practical` is the repo definition (`Proofs/Enumerative/Practical.lean`):
`0 < n` and every `m ≤ n` is a sum of distinct divisors of `n`; it is equivalent
to the OEIS A005153 name form by `Nat.practical_iff_forall_le_sum_divisors`. -/

open Classical in
/-- **A210445**: `a n` is the least positive integer `k` with `k * n` practical.

When no such `k` exists the value is the junk `0`; this happens only at `n = 0`
(`k * 0 = 0` is not practical), and every `n ≥ 1` has such a `k`
(`exists_practical_mul`), so on the entry's domain `n ≥ 1` the junk branch is
never taken. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ (k * n).Practical then Nat.find h else 0

/-- If some positive `k` makes `k * n` practical, then `a n` is positive, `a n * n`
is practical, and `a n ≤ k`. -/
theorem a_spec {n k : ℕ} (hk : 0 < k) (hkn : (k * n).Practical) :
    0 < a n ∧ (a n * n).Practical ∧ a n ≤ k := by
  classical
  have h : ∃ k, 0 < k ∧ (k * n).Practical := ⟨k, hk, hkn⟩
  have ha : a n = Nat.find h := by
    unfold a
    rw [dif_pos h]
  rw [ha]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, Nat.find_min' h ⟨hk, hkn⟩⟩

/-- Characterisation used for ground truth: if `k > 0`, `k * n` is practical and no
smaller positive `j` makes `j * n` practical, then `a n = k`. -/
theorem a_eq_of_isLeast {n k : ℕ} (hk : 0 < k) (hkn : (k * n).Practical)
    (hmin : ∀ j, 0 < j → j < k → ¬ (j * n).Practical) : a n = k := by
  obtain ⟨hpos, hprac, hle⟩ := a_spec hk hkn
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact absurd hprac (hmin (a n) hpos hlt)
  · exact heq

/-! ## Arithmetic helpers -/

/-- `σ(2 ^ a * b) = (2 ^ (a + 1) - 1) σ(b)` for odd `b`, stated subtraction-free:
`σ(2 ^ a * b) + σ(b) = 2 ^ (a + 1) * σ(b)`. -/
theorem sum_divisors_two_pow_mul_add {e b : ℕ} (hb : Odd b) :
    ∑ d ∈ (2 ^ e * b).divisors, d + ∑ d ∈ b.divisors, d
      = 2 ^ (e + 1) * ∑ d ∈ b.divisors, d := by
  have hcop : Nat.Coprime (2 ^ e) b :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hb)
  rw [Nat.Coprime.sum_divisors_mul hcop, ← Nat.one_add_sum_divisors_two_pow e]
  ring

/-- Multiplying a practical number by a power of `2` keeps it practical (Melfi's
Lemma 4 at `t = 2`, iterated). -/
theorem practical_mul_two_pow {m : ℕ} (hm : m.Practical) (e : ℕ) :
    (m * 2 ^ e).Practical := by
  induction e with
  | zero => simpa using hm
  | succ e ih =>
    have h1 : 1 ≤ m * 2 ^ e := ih.pos
    have hstep : (m * 2 ^ e * 2).Practical :=
      ih.mul_of_le_two_mul (by norm_num) (by omega)
    rwa [pow_succ, ← mul_assoc]

/-- Non-practicality test at a prime: if `0 < j < p`, `p` prime, and it is not the
case that `j` is practical with `p ≤ 1 + σ(j)`, then `j * p` is not practical
(Stewart's criterion, `Nat.practical_mul_prime_pow_iff`). -/
theorem not_practical_mul_prime {j p : ℕ} (hp : p.Prime) (hj : 0 < j) (hjp : j < p)
    (h : ¬ (j.Practical ∧ p ≤ 1 + ∑ d ∈ j.divisors, d)) : ¬ (j * p).Practical := by
  intro hjp'
  have hpow : (j * p ^ 1).Practical := by simpa using hjp'
  rw [Nat.practical_mul_prime_pow_iff hp hj
    (Nat.forall_mem_primeFactors_lt_of_lt hj.ne' hjp) one_ne_zero] at hpow
  exact h hpow

/-! ## Small practical numbers, certified by Melfi's Lemma 4 -/

/-- `6 = 2 · 3` is practical. -/
theorem practical_six : (6 : ℕ).Practical := by
  simpa using Nat.practical_two.mul_of_le_two_mul (t := 3) (by norm_num) (by norm_num)

/-- `12 = 6 · 2` is practical. -/
theorem practical_twelve : (12 : ℕ).Practical := by
  simpa using practical_six.mul_of_le_two_mul (t := 2) (by norm_num) (by norm_num)

/-- `24 = 12 · 2` is practical. -/
theorem practical_twenty_four : (24 : ℕ).Practical := by
  simpa using practical_twelve.mul_of_le_two_mul (t := 2) (by norm_num) (by norm_num)

/-- `30 = 6 · 5` is practical. -/
theorem practical_thirty : (30 : ℕ).Practical := by
  simpa using practical_six.mul_of_le_two_mul (t := 5) (by norm_num) (by norm_num)

/-- `36 = 12 · 3` is practical. -/
theorem practical_thirty_six : (36 : ℕ).Practical := by
  simpa using practical_twelve.mul_of_le_two_mul (t := 3) (by norm_num) (by norm_num)

/-- `42 = 6 · 7` is practical. -/
theorem practical_forty_two : (42 : ℕ).Practical := by
  simpa using practical_six.mul_of_le_two_mul (t := 7) (by norm_num) (by norm_num)

/-- `48 = 24 · 2` is practical. -/
theorem practical_forty_eight : (48 : ℕ).Practical := by
  simpa using practical_twenty_four.mul_of_le_two_mul (t := 2) (by norm_num) (by norm_num)

/-- `60 = 12 · 5` is practical. -/
theorem practical_sixty : (60 : ℕ).Practical := by
  simpa using practical_twelve.mul_of_le_two_mul (t := 5) (by norm_num) (by norm_num)

/-- `72 = 24 · 3` is practical. -/
theorem practical_seventy_two : (72 : ℕ).Practical := by
  simpa using practical_twenty_four.mul_of_le_two_mul (t := 3) (by norm_num) (by norm_num)

/-! ## The window lemma -/

/-- **Window lemma.** If `m` is practical and `0 < n ≤ 1 + σ(m)`, then `m * n` is
practical (Melfi's Lemma 4 with `t = n`). -/
theorem practical_mul_of_window {m n : ℕ} (hm : m.Practical) (hn : 0 < n)
    (hle : n ≤ 1 + ∑ d ∈ m.divisors, d) : (m * n).Practical :=
  hm.mul_of_le_one_add_sum_divisors hn hle

/-! ## Part (i) -/

/-- **Part (i), existence form.** For `n > 1` some `k` with `0 < k < n` makes `k * n`
practical: `k = 2 ^ c` with `2 ^ c < n ≤ 2 ^ (c + 1)`. -/
theorem exists_lt_practical_mul {n : ℕ} (hn : 1 < n) :
    ∃ k, 0 < k ∧ k < n ∧ (k * n).Practical := by
  set c := Nat.log 2 (n - 1) with hc
  have hlo : 2 ^ c ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
  have hhi : n - 1 < 2 ^ (c + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n - 1)
  have hbudget : n ≤ 1 + ∑ d ∈ ((2 : ℕ) ^ c).divisors, d := by
    rw [Nat.one_add_sum_divisors_two_pow c]
    omega
  exact ⟨2 ^ c, pow_pos (by norm_num) c, by omega,
    practical_mul_of_window (Nat.practical_two_pow c) (by omega) hbudget⟩

/-- Every `n ≥ 1` has a positive `k` with `k * n` practical, so `a n` is not the
junk value on the entry's domain. -/
theorem exists_practical_mul {n : ℕ} (hn : 0 < n) : ∃ k, 0 < k ∧ (k * n).Practical := by
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hn) with h | h
  · obtain ⟨k, hk, -, hkn⟩ := exists_lt_practical_mul h
    exact ⟨k, hk, hkn⟩
  · exact ⟨1, by norm_num, by simpa [← h] using Nat.practical_one⟩

/-! ## Part (ii) -/

/-- A Lemma-4 window certifies part (ii): a practical `m` with `2 m < n ≤ 1 + σ(m)`
gives `k = m`. -/
theorem exists_two_mul_lt_of_window {m n : ℕ} (hm : m.Practical) (h2 : 2 * m < n)
    (hle : n ≤ 1 + ∑ d ∈ m.divisors, d) :
    ∃ k, 0 < k ∧ 2 * k < n ∧ (k * n).Practical :=
  ⟨m, hm.pos, h2, practical_mul_of_window hm (by omega) hle⟩

/-- Part (ii) on the finite range `48 ≤ n ≤ 96`: `k = 1` at `48`, and the windows
of `24`, `30`, `36`, `42` (with `σ = 60, 72, 91, 96`) cover `49 … 96`. -/
theorem exists_two_mul_lt_small {n : ℕ} (hlo : 47 < n) (hhi : n ≤ 96) :
    ∃ k, 0 < k ∧ 2 * k < n ∧ (k * n).Practical := by
  have h24 : ∑ d ∈ (24 : ℕ).divisors, d = 60 := by decide
  have h30 : ∑ d ∈ (30 : ℕ).divisors, d = 72 := by decide
  have h36 : ∑ d ∈ (36 : ℕ).divisors, d = 91 := by decide
  have h42 : ∑ d ∈ (42 : ℕ).divisors, d = 96 := by decide
  by_cases h48 : n = 48
  · subst h48
    exact ⟨1, by norm_num, by norm_num, by simpa using practical_forty_eight⟩
  by_cases h61 : n ≤ 61
  · exact exists_two_mul_lt_of_window practical_twenty_four (by omega) (by omega)
  by_cases h73 : n ≤ 73
  · exact exists_two_mul_lt_of_window practical_thirty (by omega) (by omega)
  by_cases h92 : n ≤ 92
  · exact exists_two_mul_lt_of_window practical_thirty_six (by omega) (by omega)
  · exact exists_two_mul_lt_of_window practical_forty_two (by omega) (by omega)

/-- Part (ii) for `n > 96`: with `w = 2 ^ e` and `96 w < n ≤ 192 w`, one of
`48 w`, `60 w`, `72 w` has a Lemma-4 window containing `n`. -/
theorem exists_two_mul_lt_large {n : ℕ} (hn : 96 < n) :
    ∃ k, 0 < k ∧ 2 * k < n ∧ (k * n).Practical := by
  set e := Nat.log 2 ((n - 1) / 96) with he
  set w : ℕ := 2 ^ e with hw
  have hwlo : w ≤ (n - 1) / 96 := Nat.pow_log_le_self 2 (by omega)
  have hwhi : (n - 1) / 96 < 2 ^ (e + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hw2 : 2 ^ (e + 1) = 2 * w := by rw [hw, pow_succ, mul_comm]
  have hlow : 96 * w < n := by omega
  have hhigh : n ≤ 192 * w := by omega
  have hwpos : 0 < w := pow_pos (by norm_num) e
  -- the three budgets, from `σ(2 ^ a * b) + σ(b) = 2 ^ (a + 1) σ(b)`
  have hσ48 : ∑ d ∈ (48 * w).divisors, d + 4 = 128 * w := by
    have h := sum_divisors_two_pow_mul_add (e := e + 4) (b := 3) (by decide)
    have h3 : ∑ d ∈ (3 : ℕ).divisors, d = 4 := by decide
    have heq : 2 ^ (e + 4) * 3 = 48 * w := by rw [hw, pow_add]; ring
    have hp : (2 : ℕ) ^ (e + 4 + 1) = 32 * w := by rw [hw, pow_add]; ring
    rw [heq, h3, hp] at h
    omega
  have hσ60 : ∑ d ∈ (60 * w).divisors, d + 24 = 192 * w := by
    have h := sum_divisors_two_pow_mul_add (e := e + 2) (b := 15) (by decide)
    have h15 : ∑ d ∈ (15 : ℕ).divisors, d = 24 := by decide
    have heq : 2 ^ (e + 2) * 15 = 60 * w := by rw [hw, pow_add]; ring
    have hp : (2 : ℕ) ^ (e + 2 + 1) = 8 * w := by rw [hw, pow_add]; ring
    rw [heq, h15, hp] at h
    omega
  have hσ72 : ∑ d ∈ (72 * w).divisors, d + 13 = 208 * w := by
    have h := sum_divisors_two_pow_mul_add (e := e + 3) (b := 9) (by decide)
    have h9 : ∑ d ∈ (9 : ℕ).divisors, d = 13 := by decide
    have heq : 2 ^ (e + 3) * 9 = 72 * w := by rw [hw, pow_add]; ring
    have hp : (2 : ℕ) ^ (e + 3 + 1) = 16 * w := by rw [hw, pow_add]; ring
    rw [heq, h9, hp] at h
    omega
  have hp48 : (48 * w).Practical := practical_mul_two_pow practical_forty_eight e
  have hp60 : (60 * w).Practical := practical_mul_two_pow practical_sixty e
  have hp72 : (72 * w).Practical := practical_mul_two_pow practical_seventy_two e
  by_cases h1 : n ≤ 128 * w - 3
  · exact exists_two_mul_lt_of_window hp48 (by omega) (by omega)
  by_cases h2 : n ≤ 192 * w - 23
  · exact exists_two_mul_lt_of_window hp60 (by omega) (by omega)
  · exact exists_two_mul_lt_of_window hp72 (by omega) (by omega)

/-- **Part (ii), existence form.** For `n > 47` some `k > 0` with `2 k < n` makes
`k * n` practical. -/
theorem exists_two_mul_lt_practical_mul {n : ℕ} (hn : 47 < n) :
    ∃ k, 0 < k ∧ 2 * k < n ∧ (k * n).Practical := by
  by_cases h : n ≤ 96
  · exact exists_two_mul_lt_small hn h
  · exact exists_two_mul_lt_large (by omega)

/-! ## The conjecture -/

/-- **Sun's conjecture, part (i)** (A210445, Zhi-Wei Sun, Jan 20 2013): `a(n) < n`
for all `n > 1`. -/
theorem a_lt {n : ℕ} (hn : 1 < n) : a n < n := by
  obtain ⟨k, hk, hkn, hprac⟩ := exists_lt_practical_mul hn
  exact (a_spec hk hprac).2.2.trans_lt hkn

/-- **Sun's conjecture, part (ii)** (A210445, Zhi-Wei Sun, Jan 20 2013):
`a(n) < n / 2`, i.e. `2 * a(n) < n`, for all `n > 47`. -/
theorem two_mul_a_lt {n : ℕ} (hn : 47 < n) : 2 * a n < n := by
  obtain ⟨k, hk, hkn, hprac⟩ := exists_two_mul_lt_practical_mul hn
  have hle := (a_spec hk hprac).2.2
  omega

/-- **Sun's conjecture (A210445).** Verbatim: "Conjecture: a(n) < n for all n>1, and
a(n) < n/2 for all n>47." (Zhi-Wei Sun, Jan 20 2013), where `a(n)` is the least
positive integer `k` with `k * n` practical.  The real inequality `a(n) < n / 2` is
stated division-free as `2 * a n < n`. -/
theorem sun_conjecture :
    (∀ n : ℕ, 1 < n → a n < n) ∧ (∀ n : ℕ, 47 < n → 2 * a n < n) :=
  ⟨fun _ hn => a_lt hn, fun _ hn => two_mul_a_lt hn⟩

/-! ## Ground truth and sharpness -/

example : a 1 = 1 :=
  a_eq_of_isLeast (by norm_num) (by simpa using Nat.practical_one)
    (fun j hj hj1 => absurd hj1 (by omega))

example : a 2 = 1 :=
  a_eq_of_isLeast (by norm_num) (by simpa using Nat.practical_two)
    (fun j hj hj1 => absurd hj1 (by omega))

example : a 3 = 2 :=
  a_eq_of_isLeast (by norm_num) (by simpa using practical_six) (by
    intro j hj hj2
    interval_cases j
    decide)

example : a 5 = 4 :=
  a_eq_of_isLeast (by norm_num) (by decide) (by
    intro j hj hj4
    exact not_practical_mul_prime (by norm_num) hj (by omega) (by
      interval_cases j <;> decide))

example : a 11 = 6 :=
  a_eq_of_isLeast (by norm_num) (by decide) (by
    intro j hj hj6
    exact not_practical_mul_prime (by norm_num) hj (by omega) (by
      interval_cases j <;> decide))

/-- **Sharpness of part (ii):** `a 47 = 24`, so `2 * a 47 = 48 > 47`; the threshold
`47` in Sun's conjecture cannot be lowered. -/
theorem a_forty_seven : a 47 = 24 := by
  have h24 : (24 * 47 : ℕ).Practical :=
    practical_twenty_four.mul_of_le_one_add_sum_divisors (by norm_num) (by decide)
  refine a_eq_of_isLeast (by norm_num) h24 ?_
  intro j hj hj24
  exact not_practical_mul_prime (by norm_num) hj (by omega) (by
    interval_cases j <;> decide)

/-- **Sharpness of part (i):** at `n = 1` the inequality fails, `a 1 = 1`. -/
example : ¬ a 1 < 1 := by
  have h : a 1 = 1 :=
    a_eq_of_isLeast (by norm_num) (by simpa using Nat.practical_one)
      (fun j hj hj1 => absurd hj1 (by omega))
  omega

example : ¬ 2 * a 47 < 47 := by
  rw [a_forty_seven]
  norm_num

end Candidates.A210445MinPracticalSun
