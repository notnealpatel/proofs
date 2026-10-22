/-
# A051064 — 3-adic valuation of Fibonacci numbers (R. J. Mathar, 2025)

OEIS A051064, R. J. Mathar: for `n ≥ 1`,
`v_3(F(4n)) = v_3(n) + 1`, and `v_3(F(m)) = 0` when `4 ∤ m`.
This is the classical rank-of-apparition law with `α(3) = 4`; see
T. Lengyel, “The order of the Fibonacci and Lucas numbers”,
Fibonacci Quart. 33 (1995).

* `F(n+24) ≡ F(n) (mod 9)` from `Nat.fib_add`, so `F mod 9` is read off a
  finite table; this gives `3 ∤ F(m)` for `4 ∤ m` and `v_3(F(4k)) = 1` for
  `3 ∤ k`.
* Tripling: `F(3m) = F(m) (2F(m)^2 + 3F(m+1)^2 - 3F(m)F(m+1))` in `ℤ`;
  when `3 ∣ F(m)` the cofactor has 3-adic valuation exactly `1`.
* Induction on the exponent `e` in `n = 3^e k`, `3 ∤ k`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A051064DivideFibonacciAdic

/-! ## Definitions -/

/-- OEIS A051064: `a(n)` is the exponent of the exact power of `3` dividing
`3n`, i.e. the 3-adic valuation of `3n`. -/
def a (n : ℕ) : ℕ := padicValNat 3 (3 * n)

/-- OEIS A007949: the 3-adic valuation of `n` (with `A007949(0) = 0` by the
Mathlib junk convention; the conjecture only evaluates it at `F(m)`). -/
def A007949 (n : ℕ) : ℕ := padicValNat 3 n

/-- Examples: the first twelve listed terms of A051064. -/
example : (List.range 12).map (fun n => a (n + 1)) = [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2] := by
  simp only [a, ← Nat.fst_maxPowDvdDiv]
  decide +kernel

/-- Examples: terms 25..30 of A051064 (containing the first `4`). -/
example : (List.range 6).map (fun n => a (n + 25)) = [1, 1, 4, 1, 1, 2] := by
  simp only [a, ← Nat.fst_maxPowDvdDiv]
  decide +kernel

/-- Examples: `A007949(F(12)) = A007949(144) = 2 = a(3)`. -/
example : A007949 (Nat.fib 12) = 2 := by
  simp only [A007949, ← Nat.fst_maxPowDvdDiv]
  decide +kernel

/-! ## Fibonacci numbers modulo 9 -/

/-- `F(n + 24) ≡ F(n) (mod 9)`: the Pisano period of `9` divides `24`. -/
theorem fib_add_twentyfour_mod_nine (n : ℕ) : Nat.fib (n + 24) % 9 = Nat.fib n % 9 := by
  have hadd : Nat.fib (n + 23 + 1) = Nat.fib n * Nat.fib 23 + Nat.fib (n + 1) * Nat.fib 24 :=
    Nat.fib_add n 23
  have h23 : Nat.fib 23 % 9 = 1 := by decide
  have h24 : Nat.fib 24 % 9 = 0 := by decide
  rw [show n + 24 = n + 23 + 1 by ring, hadd, Nat.add_mod, Nat.mul_mod, h23,
    Nat.mul_mod (Nat.fib (n + 1)), h24]
  simp

/-- `F(n) mod 9` depends only on `n mod 24`. -/
theorem fib_mod_nine (n : ℕ) : Nat.fib n % 9 = Nat.fib (n % 24) % 9 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 24 with hn | hn
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 24 := ⟨n - 24, by omega⟩
      rw [fib_add_twentyfour_mod_nine, ih k (by omega), Nat.add_mod_right]

/-- **Second clause.** If `4 ∤ m` then `3 ∤ F(m)`. -/
theorem three_not_dvd_fib_of_not_four_dvd (m : ℕ) (hm : ¬ 4 ∣ m) : ¬ 3 ∣ Nat.fib m := by
  have htable : ∀ r < 24, r % 4 ≠ 0 → Nat.fib r % 9 % 3 ≠ 0 := by decide
  have hr : m % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hr4 : m % 24 % 4 ≠ 0 := by omega
  have h3 : Nat.fib m % 3 = Nat.fib m % 9 % 3 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  rw [Nat.dvd_iff_mod_eq_zero, h3, fib_mod_nine]
  exact htable _ hr hr4

/-- Base case: if `3 ∤ k` then `3 ∣ F(4k)` but `9 ∤ F(4k)`. -/
theorem fib_four_mul_mod_nine (k : ℕ) (hk : ¬ 3 ∣ k) :
    Nat.fib (4 * k) % 9 = 3 ∨ Nat.fib (4 * k) % 9 = 6 := by
  have htable : ∀ s < 6, s % 3 ≠ 0 →
      Nat.fib (4 * s) % 9 = 3 ∨ Nat.fib (4 * s) % 9 = 6 := by decide
  have hs : 4 * k % 24 = 4 * (k % 6) := by omega
  rw [fib_mod_nine, hs]
  exact htable _ (Nat.mod_lt _ (by norm_num)) (by omega)

/-! ## The tripling formula -/

/-- `F(3m) = F(m) (2F(m)^2 + 3F(m+1)^2 - 3F(m)F(m+1))` in `ℤ`. -/
theorem fib_three_mul_int (m : ℕ) :
    (Nat.fib (3 * m) : ℤ) = (Nat.fib m : ℤ) *
      (2 * (Nat.fib m : ℤ) ^ 2 + 3 * (Nat.fib (m + 1) : ℤ) ^ 2
        - 3 * (Nat.fib m : ℤ) * (Nat.fib (m + 1) : ℤ)) := by
  have h1 : Nat.fib (m + m + 1) = Nat.fib m * Nat.fib m + Nat.fib (m + 1) * Nat.fib (m + 1) :=
    Nat.fib_add m m
  have h2 : Nat.fib (m + (m + 1) + 1)
      = Nat.fib m * Nat.fib (m + 1) + Nat.fib (m + 1) * Nat.fib (m + 1 + 1) :=
    Nat.fib_add m (m + 1)
  have h3 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
  have h4 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have h5 : Nat.fib (2 * m + 1 + m + 1)
      = Nat.fib (2 * m + 1) * Nat.fib m + Nat.fib (2 * m + 1 + 1) * Nat.fib (m + 1) :=
    Nat.fib_add (2 * m + 1) m
  have h6 : Nat.fib (2 * m + m + 1)
      = Nat.fib (2 * m) * Nat.fib m + Nat.fib (2 * m + 1) * Nat.fib (m + 1) :=
    Nat.fib_add (2 * m) m
  have h7 : Nat.fib (3 * m + 2) = Nat.fib (3 * m) + Nat.fib (3 * m + 1) := Nat.fib_add_two
  rw [show m + m + 1 = 2 * m + 1 by ring] at h1
  rw [show m + (m + 1) + 1 = 2 * m + 2 by ring, show m + 1 + 1 = m + 2 by ring] at h2
  rw [show 2 * m + 1 + m + 1 = 3 * m + 2 by ring, show 2 * m + 1 + 1 = 2 * m + 2 by ring] at h5
  rw [show 2 * m + m + 1 = 3 * m + 1 by ring] at h6
  have z1 := congrArg (fun x : ℕ => (x : ℤ)) h1
  have z2 := congrArg (fun x : ℕ => (x : ℤ)) h2
  have z3 := congrArg (fun x : ℕ => (x : ℤ)) h3
  have z4 := congrArg (fun x : ℕ => (x : ℤ)) h4
  have z5 := congrArg (fun x : ℕ => (x : ℤ)) h5
  have z6 := congrArg (fun x : ℕ => (x : ℤ)) h6
  have z7 := congrArg (fun x : ℕ => (x : ℤ)) h7
  push_cast at z1 z2 z3 z4 z5 z6 z7
  set A : ℤ := (Nat.fib m : ℤ)
  set B : ℤ := (Nat.fib (m + 1) : ℤ)
  -- `F(2m) = 2AB - A^2`
  have hc : (Nat.fib (2 * m) : ℤ) = 2 * A * B - A ^ 2 := by
    linear_combination -z3 + z2 + B * z4 - z1
  -- `F(3m) = F(2m+1) A + F(2m) (B - A)`
  have hg : (Nat.fib (3 * m) : ℤ)
      = (Nat.fib (2 * m + 1) : ℤ) * A + (Nat.fib (2 * m) : ℤ) * (B - A) := by
    linear_combination -z7 + z5 - z6 + B * z3
  linear_combination hg + A * z1 + (B - A) * hc

/-! ## Valuations -/

/-- If `x ≡ 3` or `x ≡ 6 (mod 9)` then `v_3(x) = 1`. -/
theorem padicValNat_three_eq_one_of_mod_nine (x : ℕ) (hx : x % 9 = 3 ∨ x % 9 = 6) :
    padicValNat 3 x = 1 := by
  have hdecomp : x = 3 * (x / 3) := by omega
  have hy : ¬ 3 ∣ x / 3 := by omega
  have hy0 : x / 3 ≠ 0 := by omega
  rw [hdecomp, padicValNat.mul (by norm_num) hy0, padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd hy]

/-- **Tripling step.** If `3 ∣ F(m)` and `F(m) ≠ 0` then `v_3(F(3m)) = v_3(F(m)) + 1`. -/
theorem padicValNat_three_fib_three_mul (m : ℕ) (h3 : 3 ∣ Nat.fib m) (h0 : Nat.fib m ≠ 0) :
    padicValNat 3 (Nat.fib (3 * m)) = padicValNat 3 (Nat.fib m) + 1 := by
  have hA0 : (Nat.fib m : ℤ) ≠ 0 := by exact_mod_cast h0
  obtain ⟨c, hc⟩ : (3 : ℤ) ∣ (Nat.fib m : ℤ) := by exact_mod_cast h3
  have hcop : Nat.Coprime (Nat.fib m) (Nat.fib (m + 1)) := Nat.fib_coprime_fib_succ m
  have hB3 : ¬ (3 : ℤ) ∣ (Nat.fib (m + 1) : ℤ) := by
    intro hdvd
    have hn : 3 ∣ Nat.fib (m + 1) := by exact_mod_cast hdvd
    have h1 : 3 ∣ Nat.gcd (Nat.fib m) (Nat.fib (m + 1)) := Nat.dvd_gcd h3 hn
    rw [hcop.gcd_eq_one] at h1
    omega
  set A : ℤ := (Nat.fib m : ℤ) with hA
  set B : ℤ := (Nat.fib (m + 1) : ℤ) with hB
  set R : ℤ := B ^ 2 - 3 * c * B + 6 * c ^ 2 with hR
  have hR3 : ¬ (3 : ℤ) ∣ R := by
    intro hdvd
    have hB2 : (3 : ℤ) ∣ B ^ 2 := by
      have hsplit : B ^ 2 = R - 3 * (2 * c ^ 2 - c * B) := by rw [hR]; ring
      rw [hsplit]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    exact hB3 (Int.prime_three.dvd_of_dvd_pow hB2)
  have hfac : (Nat.fib (3 * m) : ℤ) = A * (3 * R) := by
    rw [fib_three_mul_int, hR]
    rw [← hA, ← hB, hc]
    ring
  have hR0 : R ≠ 0 := fun hz => hR3 (hz ▸ dvd_zero 3)
  have hval : padicValInt 3 (Nat.fib (3 * m) : ℤ) = padicValInt 3 A + 1 := by
    rw [hfac, padicValInt.mul hA0 (mul_ne_zero (by norm_num) hR0),
      padicValInt.mul (by norm_num) hR0, padicValInt.eq_zero_of_not_dvd hR3]
    have h33 : padicValInt 3 (3 : ℤ) = 1 := by
      have := padicValInt.self (p := 3) (by norm_num)
      exact_mod_cast this
    rw [h33]
  rw [padicValInt.of_nat, hA, padicValInt.of_nat] at hval
  exact hval

/-- Induction on the exponent: if `3 ∤ k` then `v_3(F(4 · 3^e · k)) = e + 1`. -/
theorem padicValNat_three_fib_four_mul_pow_mul (k : ℕ) (hk : ¬ 3 ∣ k) (e : ℕ) :
    padicValNat 3 (Nat.fib (4 * (3 ^ e * k))) = e + 1 := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero 3)
  induction e with
  | zero =>
    rw [pow_zero, one_mul]
    exact padicValNat_three_eq_one_of_mod_nine _ (fib_four_mul_mod_nine k hk)
  | succ e ih =>
    set m : ℕ := 4 * (3 ^ e * k) with hm
    have hmpos : 0 < m := by positivity
    have hfib0 : Nat.fib m ≠ 0 := (Nat.fib_pos.mpr hmpos).ne'
    have h3 : 3 ∣ Nat.fib m := by
      apply dvd_of_one_le_padicValNat
      rw [ih]
      omega
    have hidx : 4 * (3 ^ (e + 1) * k) = 3 * m := by rw [hm]; ring
    rw [hidx, padicValNat_three_fib_three_mul m h3 hfib0, ih]

/-- **First clause, valuation form.** For `n ≥ 1`, `v_3(F(4n)) = v_3(n) + 1`. -/
theorem padicValNat_three_fib_four_mul (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 3 (Nat.fib (4 * n)) = padicValNat 3 n + 1 := by
  obtain ⟨e, k, hk, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 3 (by norm_num)
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero 3)
  rw [padicValNat_three_fib_four_mul_pow_mul k hk e,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hk0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hk, add_zero]

/-- `a(n) = v_3(n) + 1` for `n ≥ 1` (the entry's formula `a(n) = A007949(n) + 1`). -/
theorem a_eq_padicValNat_add_one (n : ℕ) (hn : 1 ≤ n) : a n = padicValNat 3 n + 1 := by
  rw [a, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num), add_comm]

/-! ## The conjecture -/

/-- **Mathar's conjecture (A051064, R. J. Mathar, 2025).**

For every `n ≥ 1`, `a(n) = v_3(F(4n))`; and for every `m`
with `4 ∤ m`, `v_3(F(m)) = 0`.  The guard `1 ≤ n` mirrors the entry's
offset (A051064 starts at `n = 1`); at `n = 0` both sides are the junk value
`padicValNat 3 0 = 0`, so the guard is not needed for this form, but it is
needed for the valuation form `padicValNat_three_fib_four_mul`.
Classical (Lucas / Carmichael / Lengyel 1995); proved here from `Nat.fib_add`. -/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → a n = A007949 (Nat.fib (4 * n))) ∧
      (∀ m : ℕ, ¬ 4 ∣ m → A007949 (Nat.fib m) = 0) := by
  refine ⟨fun n hn => ?_, fun m hm => ?_⟩
  · rw [A007949, padicValNat_three_fib_four_mul n hn, a_eq_padicValNat_add_one n hn]
  · exact padicValNat.eq_zero_of_not_dvd (three_not_dvd_fib_of_not_four_dvd m hm)

end Candidates.A051064DivideFibonacciAdic
