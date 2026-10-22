/-
# A014865 — Dale: terms are odd, and terms > 1 are divisible by 3, 5 or 7

Harvey P. Dale's conjecture in OEIS A014865 (2020): positive `k` dividing
`s(k)`, where `s(1)=1` and `s(j)=15s(j-1)+j`, are odd; those greater than one
are divisible by `3`, `5` or `7`, hence those greater than seven are composite.

## Argument

* Closed form: `196 s(k) + 14 k + 15 = 15^(k+1)`.
* Oddness: if `k = 2^a m` with `a ≥ 1`, `m` odd, then `2^(a+2)` divides both
  `196 s(k)` and `15^k - 1` (as `2^(a+2) ∣ 15^(2^a) - 1`), hence divides
  `14 k = 15 (15^k - 1) - 196 s(k) = 2^(a+1) · 7m`, contradicting `m` odd.
* Factor `3`, `5` or `7`: let `p = minFac k`.  If `p ∉ {2,3,5,7}` then in
  `ZMod p`, `15 = 15^(k+1)` and `15 ≠ 0`, so `15^k = 1`; with Fermat
  `15^(p-1) = 1` and `gcd(k, p-1) = 1` this forces `15 = 1`, i.e. `p ∣ 14`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A014865OddCorollaryPrime

/-- The OEIS A014865 auxiliary sequence: `s 0 = 0`, `s j = 15 * s (j-1) + j`
(so `s 1 = 1`, matching the entry's `s(1)=1`). -/
def s : ℕ → ℕ
  | 0 => 0
  | j + 1 => 15 * s j + (j + 1)

example : s 1 = 1 := by decide
example : s 2 = 17 := by decide
example : s 3 = 258 := by decide
example : s 4 = 3874 := by decide

/-- The first listed terms `1, 3, 5, 7, 15` of A014865 are exactly the `k ∈ [1, 15]`
with `k ∣ s k`. -/
example : (Finset.Icc 1 15).filter (fun k => k ∣ s k) = {1, 3, 5, 7, 15} := by decide

/-- Closed form: `196 * s k + 14 * k + 15 = 15 ^ (k + 1)`. -/
theorem closed_form (k : ℕ) : 196 * s k + 14 * k + 15 = 15 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ← ih, s]
    ring

/-- For `a ≥ 1`, `2 ^ (a + 2)` divides `15 ^ (2 ^ a) - 1` (over `ℤ`). -/
theorem two_pow_dvd_fifteen_pow_two_pow_sub_one (a : ℕ) (ha : 1 ≤ a) :
    (2 : ℤ) ^ (a + 2) ∣ 15 ^ (2 ^ a) - 1 := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
    have hfactor : (15 : ℤ) ^ (2 ^ (n + 1)) - 1 =
        (15 ^ (2 ^ n) - 1) * (15 ^ (2 ^ n) + 1) := by
      rw [pow_succ, pow_mul]
      ring
    have hodd : Odd ((15 : ℤ) ^ (2 ^ n)) := Odd.pow (by decide)
    have heven : (2 : ℤ) ∣ 15 ^ (2 ^ n) + 1 := (hodd.add_one).two_dvd
    rw [hfactor, pow_succ]
    exact mul_dvd_mul ih heven

/-- Every `k ≥ 1` with `k ∣ s k` is odd. -/
theorem odd_of_dvd_s (k : ℕ) (hk : 0 < k) (h : k ∣ s k) : Odd k := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
  rcases Nat.eq_zero_or_pos a with ha | ha
  · simpa [ha] using hm
  exfalso
  set k := 2 ^ a * m with hkdef
  -- `2 ^ (a+2)` divides `196 * s k`.
  have hs : (2 : ℤ) ^ (a + 2) ∣ 196 * (s k : ℤ) := by
    have h1 : (2 : ℤ) ^ a ∣ (s k : ℤ) := by
      exact_mod_cast (Dvd.intro m rfl).trans h
    have h2 : (196 : ℤ) * s k = 49 * (2 ^ 2 * s k) := by ring
    rw [h2, pow_add, mul_comm ((2 : ℤ) ^ a)]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left _ h1) 49
  -- `2 ^ (a+2)` divides `15 ^ k - 1`.
  have hpow : (2 : ℤ) ^ (a + 2) ∣ 15 ^ k - 1 := by
    have h1 : (15 : ℤ) ^ (2 ^ a) - 1 ∣ 15 ^ k - 1 := by
      have := sub_dvd_pow_sub_pow ((15 : ℤ) ^ (2 ^ a)) 1 m
      rwa [one_pow, ← pow_mul] at this
    exact (two_pow_dvd_fifteen_pow_two_pow_sub_one a ha).trans h1
  -- Hence `2 ^ (a+2)` divides `14 * k`.
  have hcf : (14 * k : ℤ) = 15 * (15 ^ k - 1) - 196 * s k := by
    have := closed_form k
    have hz : (196 * s k + 14 * k + 15 : ℤ) = 15 ^ (k + 1) := by exact_mod_cast this
    rw [pow_succ] at hz
    linear_combination hz
  have h14 : (2 : ℤ) ^ (a + 2) ∣ 14 * k := by
    rw [hcf]
    exact dvd_sub (Dvd.dvd.mul_left hpow 15) hs
  have h14n : 2 ^ (a + 1) * 2 ∣ 2 ^ (a + 1) * (7 * m) := by
    have : (2 : ℤ) ^ (a + 2) ∣ ((2 ^ (a + 1) * (7 * m) : ℕ) : ℤ) := by
      have hk : (14 * k : ℤ) = ((2 ^ (a + 1) * (7 * m) : ℕ) : ℤ) := by
        rw [hkdef]; push_cast; ring
      rwa [← hk]
    rw [← pow_succ]
    exact_mod_cast this
  have h2m : 2 ∣ 7 * m := Nat.dvd_of_mul_dvd_mul_left (by positivity) h14n
  have h7m : Odd (7 * m) := Odd.mul (by decide) hm
  exact (Nat.not_even_iff_odd.mpr h7m) (even_iff_two_dvd.mpr h2m)

/-- A prime dividing `210 = 2 * 3 * 5 * 7` is one of `2, 3, 5, 7`. -/
theorem prime_dvd_210 (p : ℕ) (hp : p.Prime) (hd : p ∣ 210) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hd' : p ∣ 2 * 3 * 5 * 7 := hd
  have hq (q : ℕ) (hq : q.Prime) (hpq : p ∣ q) : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases hp.dvd_mul.mp hd' with h235 | h7
  · rcases hp.dvd_mul.mp h235 with h23 | h5
    · rcases hp.dvd_mul.mp h23 with h2 | h3
      · exact Or.inl (hq 2 Nat.prime_two h2)
      · exact Or.inr (Or.inl (hq 3 Nat.prime_three h3))
    · exact Or.inr (Or.inr (Or.inl (hq 5 Nat.prime_five h5)))
  · exact Or.inr (Or.inr (Or.inr (hq 7 (by norm_num) h7)))

/-- If `k > 1` is odd and `k ∣ s k`, then `3 ∣ k`, `5 ∣ k` or `7 ∣ k`. -/
theorem dvd_three_or_five_or_seven (k : ℕ) (hk : 1 < k) (hodd : Odd k) (h : k ∣ s k) :
    3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h3, h5, h7⟩ := hcon
  set p := k.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hk.ne'
  have hpk : p ∣ k := Nat.minFac_dvd k
  haveI : Fact p.Prime := ⟨hp⟩
  -- The smallest prime factor of `k` avoids `2, 3, 5, 7`.
  have hp_not : ¬ p ∣ 210 := by
    intro hd
    rcases prime_dvd_210 p hp hd with h2 | h3' | h5' | h7'
    · rw [h2] at hpk
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpk)
    · exact h3 (h3' ▸ hpk)
    · exact h5 (h5' ▸ hpk)
    · exact h7 (h7' ▸ hpk)
  have hk0 : (k : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff k p).mpr hpk
  have hs0 : (s k : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (s k) p).mpr (hpk.trans h)
  have hcf : (196 * s k + 14 * k + 15 : ZMod p) = 15 ^ (k + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) (closed_form k)
  rw [hs0, hk0, mul_zero, mul_zero, zero_add, zero_add, pow_succ] at hcf
  have h15 : (15 : ZMod p) ≠ 0 := by
    intro h0
    apply hp_not
    have h0' : ((15 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    exact ((ZMod.natCast_eq_zero_iff 15 p).mp h0').trans (by norm_num)
  -- `15 ^ k = 1` and, by Fermat, `15 ^ (p - 1) = 1` in `ZMod p`.
  have hk1 : (15 : ZMod p) ^ k = 1 :=
    mul_right_cancel₀ h15 (by rw [one_mul]; exact hcf.symm)
  have hp1 : (15 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h15
  -- `gcd k (p - 1) = 1` since every prime factor of `k` is at least `p`.
  have hcop : Nat.gcd k (p - 1) = 1 := by
    by_contra hne
    have hq := Nat.minFac_prime hne
    have hqk : (Nat.gcd k (p - 1)).minFac ∣ k :=
      (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
    have hqp : (Nat.gcd k (p - 1)).minFac ∣ p - 1 :=
      (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
    have hle1 : p ≤ (Nat.gcd k (p - 1)).minFac := Nat.minFac_le_of_dvd hq.two_le hqk
    have hp2 := hp.two_le
    have hle2 : (Nat.gcd k (p - 1)).minFac ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  have h151 : (15 : ZMod p) = 1 := by
    have hg := pow_gcd_eq_one.mpr ⟨hk1, hp1⟩
    rwa [hcop, pow_one] at hg
  apply hp_not
  have h14 : ((14 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h151
  exact ((ZMod.natCast_eq_zero_iff 14 p).mp h14).trans (by norm_num)

/-- Dale's conjecture (OEIS A014865, 2020): every positive `k` with `k ∣ s k`
is odd, and if `1 < k` then `3 ∣ k`, `5 ∣ k` or `7 ∣ k`. -/
theorem a014865_odd_and_dvd_three_five_seven (k : ℕ) (hk : 0 < k) (h : k ∣ s k) :
    Odd k ∧ (1 < k → 3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k) :=
  ⟨odd_of_dvd_s k hk h, fun hk1 => dvd_three_or_five_or_seven k hk1 (odd_of_dvd_s k hk h) h⟩

/-- **Corollary (A014865, Dale's "all terms greater than 7 are composite").**
No prime `p > 7` divides `s p`. -/
theorem not_prime_dvd_s (p : ℕ) (hp : p.Prime) (h7 : 7 < p) : ¬ p ∣ s p := by
  intro h
  have hq (q : ℕ) (hq : q.Prime) (hqp : q ∣ p) : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  rcases (a014865_odd_and_dvd_three_five_seven p hp.pos h).2 hp.one_lt with h3 | h5 | h7'
  · have := hq 3 Nat.prime_three h3; omega
  · have := hq 5 Nat.prime_five h5; omega
  · have := hq 7 (by norm_num) h7'; omega

/-- **Corollary (A014865).** Every term `k > 7` of A014865 (`k ∣ s k`) is not prime. -/
theorem not_prime_of_dvd_s (k : ℕ) (h7 : 7 < k) (h : k ∣ s k) : ¬ k.Prime :=
  fun hp => not_prime_dvd_s k hp h7 h

/-- Non-vacuity: the hypotheses of the main theorem hold jointly at `k = 15`,
and the corollary's hypotheses hold at the prime `11`. -/
example : 0 < 15 ∧ 15 ∣ s 15 ∧ Nat.Prime 11 ∧ 7 < 11 := by
  refine ⟨by norm_num, by decide, by norm_num, by norm_num⟩

end Candidates.A014865OddCorollaryPrime
