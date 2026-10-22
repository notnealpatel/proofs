/-
# Tiebekabe, Problem 5.2: `5^a = 3^y - 2^(y-2)` and the equation `5^x + 6^y = z^2`

Pagdame Tiebekabe, *The Diophantine equation p^x + 6^y = z^{2n}: a complete
solution for half of the primes*, arXiv:2609.09214, Problem 5.2, asks to prove
that `5^a = 3^y-2^(y-2)` has only `(a,y) = (2,3)` in positive integers with
`y` odd, and deduce the unique positive solution `(4,3,29)` to
`5^x+6^y = z²`. The reduction is in the paper's proof of the main theorem.

Both statements are proved below by elementary congruences and
factorization.

* Problem 5.2: for odd `y ≥ 5`, `3^y ≡ 3 (mod 8)` while `2^(y-2) ≡ 0` and
  `5^a ∈ {1, 5} (mod 8)`; `y = 3` gives `5^a = 25`.  The helper
  `five_pow_add_two_pow_eq_three_pow` proves the stronger statement without
  the parity hypothesis on `y` (even `y` is excluded by a mod-3 argument).
* `5^x + 6^y = z^2`: `x` is even by a mod-3 argument; writing `x = 2a`,
  `z = 5^a + 2s` gives the coprime factorisation
  `s (s + 5^a) = 2^(y-2) 3^y`, whose four branches are closed by mod-4,
  mod-5, size and the Problem 5.2 helper.
-/
import Mathlib

set_option autoImplicit false

namespace Tiebekabe.ProblemFive

/-! ## Residues of powers -/

/-- `5^a mod 8` is `1` or `5`. -/
theorem five_pow_mod_eight (a : ℕ) : 5 ^ a % 8 = 1 ∨ 5 ^ a % 8 = 5 := by
  induction a with
  | zero => simp
  | succ n ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> simp

/-- `5^a ≡ 1 (mod 8)` exactly when `a` is even. -/
theorem five_pow_mod_eight_eq_one_iff (a : ℕ) : 5 ^ a % 8 = 1 ↔ Even a := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, Nat.even_add_one, ← ih]
    rcases five_pow_mod_eight n with h | h <;> rw [h] <;> simp

/-- `3^n mod 8` is `1` or `3`. -/
theorem three_pow_mod_eight (n : ℕ) : 3 ^ n % 8 = 1 ∨ 3 ^ n % 8 = 3 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> simp

/-- `3^n ≡ 1 (mod 8)` exactly when `n` is even. -/
theorem three_pow_mod_eight_eq_one_iff (n : ℕ) : 3 ^ n % 8 = 1 ↔ Even n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, Nat.even_add_one, ← ih]
    rcases three_pow_mod_eight n with h | h <;> rw [h] <;> simp

/-- For even `a`, `5^a ≡ 1 (mod 3)`. -/
theorem five_pow_mod_three_of_even {a : ℕ} (ha : Even a) : 5 ^ a % 3 = 1 := by
  obtain ⟨b, rfl⟩ := ha
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

/-- For even `k`, `2^k ≡ 1 (mod 3)`. -/
theorem two_pow_mod_three_of_even {k : ℕ} (hk : Even k) : 2 ^ k % 3 = 1 := by
  obtain ⟨b, rfl⟩ := hk
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

/-! ## Problem 5.2 -/

/-- The equation `5^a + 2^k = 3^(k+2)` (that is, `5^a = 3^y - 2^(y-2)` with
`y = k + 2 ≥ 2`, of either parity) has `(a, k) = (2, 1)` as its only solution
in natural numbers. -/
theorem five_pow_add_two_pow_eq_three_pow {a k : ℕ}
    (h : 5 ^ a + 2 ^ k = 3 ^ (k + 2)) : a = 2 ∧ k = 1 := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · -- `5^a = 8`
      have h5 := five_pow_mod_eight a
      norm_num at h
      omega
    · -- `5^a = 25`
      norm_num at h
      have h25 : (5 : ℕ) ^ a = 5 ^ 2 := by omega
      exact ⟨Nat.pow_right_injective (by norm_num : 2 ≤ 5) h25, rfl⟩
    · -- `5^a = 77`
      norm_num at h
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; norm_num at h
      · have hd : 5 ∣ 5 ^ a := dvd_pow_self 5 ha.ne'
        omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exfalso
    have h8 : 2 ^ (3 + j) % 8 = 0 := by
      rw [pow_add]; norm_num [Nat.mul_mod]
    have h5 := five_pow_mod_eight a
    have h3 := three_pow_mod_eight (3 + j + 2)
    have hmod : (5 ^ a + 2 ^ (3 + j)) % 8 = 3 ^ (3 + j + 2) % 8 := by rw [h]
    have h5one : 5 ^ a % 8 = 1 := by omega
    have h3one : 3 ^ (3 + j + 2) % 8 = 1 := by omega
    have hae : Even a := (five_pow_mod_eight_eq_one_iff a).1 h5one
    have hke : Even (3 + j) := by
      have hk2 := (three_pow_mod_eight_eq_one_iff (3 + j + 2)).1 h3one
      rwa [Nat.even_add, iff_true_right even_two] at hk2
    have hm5 := five_pow_mod_three_of_even hae
    have hm2 := two_pow_mod_three_of_even hke
    have hm3 : 3 ^ (3 + j + 2) % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
    have hmod3 : (5 ^ a + 2 ^ (3 + j)) % 3 = 3 ^ (3 + j + 2) % 3 := by rw [h]
    omega

/-- **Problem 5.2 of arXiv:2609.09214 (Tiebekabe).** For odd `y ≥ 3`, the
equation `5^a = 3^y - 2^(y-2)` (difference taken in `ℤ`) holds exactly when
`(a, y) = (2, 3)`.  The statement allows `a = 0`, which is a (harmless)
strengthening of "positive integers". -/
theorem problem_5_2 (a y : ℕ) (hy : Odd y) (hy3 : 3 ≤ y) :
    (5 : ℤ) ^ a = 3 ^ y - 2 ^ (y - 2) ↔ a = 2 ∧ y = 3 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ y by omega)
    rw [Nat.add_sub_cancel] at h
    have hN : 5 ^ a + 2 ^ k = 3 ^ (k + 2) := by
      have hZ : (5 : ℤ) ^ a + 2 ^ k = 3 ^ (k + 2) := by linarith
      exact_mod_cast hZ
    obtain ⟨ha, hk⟩ := five_pow_add_two_pow_eq_three_pow hN
    exact ⟨ha, by omega⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

/-! ## The equation `5^x + 6^y = z^2` -/

/-- If `p` is prime and `s, t` are coprime, a power of `p` dividing `s * t`
divides one of the factors. -/
theorem prime_pow_dvd_of_coprime_mul {p e s t : ℕ} (hp : p.Prime) (hst : s.Coprime t)
    (h : p ^ e ∣ s * t) : p ^ e ∣ s ∨ p ^ e ∣ t := by
  by_cases hs : p ∣ s
  · left
    have ht : ¬ p ∣ t := fun ht => hp.one_lt.ne'
      (Nat.eq_one_of_dvd_one (Nat.Coprime.gcd_eq_one hst ▸ Nat.dvd_gcd hs ht))
    have hcop : (p ^ e).Coprime t := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 ht)
    exact hcop.dvd_of_dvd_mul_right h
  · right
    have hcop : (p ^ e).Coprime s := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hs)
    exact hcop.dvd_of_dvd_mul_left h

/-- A coprime factorisation `s * t = 2^k * 3^n` is one of the four obvious
ones. -/
theorem coprime_mul_eq_two_pow_mul_three_pow {s t k n : ℕ} (hst : s.Coprime t)
    (h : s * t = 2 ^ k * 3 ^ n) :
    (s = 1 ∧ t = 2 ^ k * 3 ^ n) ∨ (s = 2 ^ k ∧ t = 3 ^ n) ∨
      (s = 3 ^ n ∧ t = 2 ^ k) ∨ (s = 2 ^ k * 3 ^ n ∧ t = 1) := by
  have hN : 0 < 2 ^ k * 3 ^ n := by positivity
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have h23 : (2 ^ k).Coprime (3 ^ n) := Nat.Coprime.pow k n (by norm_num)
  have h2 := prime_pow_dvd_of_coprime_mul (e := k) Nat.prime_two hst (h ▸ dvd_mul_right _ _)
  have h3 := prime_pow_dvd_of_coprime_mul (e := n) Nat.prime_three hst (h ▸ dvd_mul_left _ _)
  rcases h2 with ⟨c, hc⟩ | ⟨c, hc⟩ <;> rcases h3 with ⟨d, hd⟩ | ⟨d, hd⟩
  · -- both prime powers divide `s`, so `t = 1`
    have hdvd : 2 ^ k * 3 ^ n ∣ s := h23.mul_dvd_of_dvd_of_dvd ⟨c, hc⟩ ⟨d, hd⟩
    have hle : s * t ≤ s := h ▸ Nat.le_of_dvd hs0 hdvd
    have ht1 : t = 1 := by nlinarith
    subst ht1
    exact Or.inr (Or.inr (Or.inr ⟨by simpa using h, rfl⟩))
  · -- `2^k ∣ s` and `3^n ∣ t`
    have hcd : 2 ^ k * 3 ^ n * (c * d) = 2 ^ k * 3 ^ n * 1 := by
      rw [mul_one]
      calc 2 ^ k * 3 ^ n * (c * d) = s * t := by rw [hc, hd]; ring
        _ = 2 ^ k * 3 ^ n := h
    have hcd1 : c * d = 1 := Nat.eq_of_mul_eq_mul_left hN hcd
    rw [mul_eq_one] at hcd1
    obtain ⟨rfl, rfl⟩ := hcd1
    exact Or.inr (Or.inl ⟨by simpa using hc, by simpa using hd⟩)
  · -- `3^n ∣ s` and `2^k ∣ t`
    have hcd : 2 ^ k * 3 ^ n * (c * d) = 2 ^ k * 3 ^ n * 1 := by
      rw [mul_one]
      calc 2 ^ k * 3 ^ n * (c * d) = s * t := by rw [hc, hd]; ring
        _ = 2 ^ k * 3 ^ n := h
    have hcd1 : c * d = 1 := Nat.eq_of_mul_eq_mul_left hN hcd
    rw [mul_eq_one] at hcd1
    obtain ⟨rfl, rfl⟩ := hcd1
    exact Or.inr (Or.inr (Or.inl ⟨by simpa using hd, by simpa using hc⟩))
  · -- both prime powers divide `t`, so `s = 1`
    have hdvd : 2 ^ k * 3 ^ n ∣ t := h23.mul_dvd_of_dvd_of_dvd ⟨c, hc⟩ ⟨d, hd⟩
    have hle : s * t ≤ t := h ▸ Nat.le_of_dvd ht0 hdvd
    have hs1 : s = 1 := by nlinarith
    subst hs1
    exact Or.inl ⟨rfl, by simpa using h⟩

/-- For `a ≥ 1`, `5^a + 1 = 2^k * 3^(k+2)` has no solution (the branch
`5^a = 2^(y-2) 3^y - 1` of the reduction). -/
theorem five_pow_add_one_ne {a k : ℕ} (ha : 0 < a) : 5 ^ a + 1 ≠ 2 ^ k * 3 ^ (k + 2) := by
  intro h
  have h5 := five_pow_mod_eight a
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · norm_num at h; omega
    · norm_num at h
      have hd : 5 ∣ 5 ^ a := dvd_pow_self 5 ha.ne'
      omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h4 : 2 ^ (2 + j) * 3 ^ (2 + j + 2) % 4 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact Dvd.dvd.mul_right (by rw [pow_add]; exact dvd_mul_right _ _) _
    omega

/-- In `5^x + 6^y = z^2` with `y > 0`, the exponent `x` is even
(otherwise `z^2 ≡ 2 (mod 3)`). -/
theorem even_of_five_pow_add_six_pow_eq_sq {x y z : ℕ} (hy : 0 < y)
    (h : 5 ^ x + 6 ^ y = z ^ 2) : Even x := by
  by_contra hx
  obtain ⟨b, rfl⟩ := Nat.not_even_iff_odd.1 hx
  have hZ := congrArg (Nat.cast : ℕ → ZMod 3) h
  push_cast at hZ
  have h6 : (6 : ZMod 3) = 0 := by decide
  have h5 : (5 : ZMod 3) ^ (2 * b + 1) = 2 := by
    rw [pow_succ, pow_mul]
    have h25 : (5 : ZMod 3) ^ 2 = 1 := by decide
    rw [h25, one_pow]; decide
  rw [h6, zero_pow hy.ne', h5, add_zero] at hZ
  generalize (z : ZMod 3) = w at hZ
  revert w hZ
  decide

/-- **Consequence of Problem 5.2 of arXiv:2609.09214 (Tiebekabe).** In positive
integers `x, y` (and natural `z`), `5^x + 6^y = z^2` holds exactly when
`(x, y, z) = (4, 3, 29)`. -/
theorem five_pow_add_six_pow_eq_sq_iff (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) :
    5 ^ x + 6 ^ y = z ^ 2 ↔ x = 4 ∧ y = 3 ∧ z = 29 := by
  constructor
  · intro h
    -- Step 1: `x = 2a`.
    obtain ⟨a, rfl⟩ := even_of_five_pow_add_six_pow_eq_sq hy h
    have ha : 0 < a := by omega
    set c := 5 ^ a with hc
    have hcsq : 5 ^ (a + a) = c ^ 2 := by rw [hc, ← pow_mul, ← two_mul, mul_comm]
    rw [hcsq] at h
    -- Step 2: `z = c + u` and `u (u + 2c) = 6^y`.
    have h6pos : 0 < 6 ^ y := by positivity
    have hcz : c ≤ z := by nlinarith
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hcz
    have hu : 6 ^ y = u * (u + 2 * c) := by nlinarith
    -- Step 3: `u = 2s`.
    have hev : Even (u * (u + 2 * c)) := hu ▸ (Nat.even_pow.2 ⟨by decide, hy.ne'⟩)
    have hue : Even u := by
      rcases Nat.even_mul.1 hev with hu' | hu'
      · exact hu'
      · exact (Nat.even_add.1 hu').2 (even_two_mul c)
    obtain ⟨s, rfl⟩ := hue
    have hs4 : 6 ^ y = 4 * (s * (s + c)) := by rw [hu]; ring
    -- Step 4: `y = k + 2`.
    have hy2 : 2 ≤ y := by
      by_contra hlt
      have hy1 : y = 1 := by omega
      subst hy1
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hy2
    have h6 : (6 : ℕ) ^ (k + 2) = 4 * (2 ^ k * 3 ^ (k + 2)) := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow, pow_add 2 k 2]; ring
    have hst : s * (s + c) = 2 ^ k * 3 ^ (k + 2) := by omega
    -- Step 5: `s` and `s + c` are coprime.
    have hn5 : ¬ 5 ∣ s := by
      intro h5
      have h5' : 5 ∣ 2 ^ k * 3 ^ (k + 2) := hst ▸ Dvd.dvd.mul_right h5 _
      rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5' with h2 | h3
      · have h52 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h2; omega
      · have h53 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h3; omega
    have hcop : s.Coprime (s + c) := by
      rw [add_comm, Nat.coprime_add_self_right, hc]
      exact Nat.Coprime.pow_right a
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hn5))
    have hcpos : 0 < c := by positivity
    -- Step 6: the four branches.
    rcases coprime_mul_eq_two_pow_mul_three_pow hcop hst with
      ⟨rfl, h1⟩ | ⟨rfl, h2⟩ | ⟨rfl, h3⟩ | ⟨rfl, h4⟩
    · exact absurd (by rw [hc] at h1; omega) (five_pow_add_one_ne (k := k) ha)
    · have h52 : 5 ^ a + 2 ^ k = 3 ^ (k + 2) := by rw [← h2, hc]; ring
      obtain ⟨rfl, rfl⟩ := five_pow_add_two_pow_eq_three_pow h52
      refine ⟨rfl, rfl, ?_⟩
      rw [hc]; norm_num
    · exfalso
      have hlt : 2 ^ k < 3 ^ (k + 2) :=
        lt_of_le_of_lt (Nat.pow_le_pow_left (by norm_num) k)
          (Nat.pow_lt_pow_right (by norm_num) (by omega))
      omega
    · exfalso
      have hpos : 0 < 2 ^ k * 3 ^ (k + 2) := by positivity
      omega
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- Non-vacuity: the solution `(4, 3, 29)` of `5^x + 6^y = z^2`. -/
example : 5 ^ 4 + 6 ^ 3 = 29 ^ 2 := by norm_num

/-- Non-vacuity: the solution `(a, y) = (2, 3)` of `5^a = 3^y - 2^(y-2)`. -/
example : (5 : ℤ) ^ 2 = 3 ^ 3 - 2 ^ (3 - 2) := by norm_num

end Tiebekabe.ProblemFive
