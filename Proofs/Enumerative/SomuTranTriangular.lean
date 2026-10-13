import Enumerative.MelfiPracticalSum
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace Nat

/-- An odd square root of `8*n+1` modulo `2^(m+2)` can be chosen below `2^m`
for every positive exponent `m`. The integer coefficient records the congruence. -/
theorem exists_bounded_odd_square_root (n m : ℕ) (hm : 1 ≤ m) :
    ∃ x : ℕ, 1 ≤ x ∧ x < 2 ^ m ∧ x % 2 = 1 ∧
      ∃ k : ℤ, (8 * n + 1 : ℤ) = (x : ℤ)^2 + (2 : ℤ)^(m+2) * k := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨1, by omega, by norm_num, by norm_num, (n : ℤ), ?_⟩
    norm_num
    ring
  | succ m hm ih =>
    obtain ⟨x, hx, hxb, hxo, k, hk⟩ := ih
    have heven : 2 ∣ 2 ^ m := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      simp [pow_succ]
    have hpar : (2 ^ m : ℕ) % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
    by_cases hkpar : k % 2 = 0
    · refine ⟨x, hx, ?_, hxo, k / 2, ?_⟩
      · simp only [pow_succ]; omega
      · have hke : k = 2 * (k / 2) := by omega
        have hpnext : (2 : ℤ)^(m+1+2) = (2 : ℤ)^(m+2)*2 := by
          rw [show m+1+2 = (m+2)+1 by omega, pow_succ]
        rw [hpnext]
        nlinarith [hk, congrArg (fun z : ℤ => (2 : ℤ)^(m+2)*z) hke]
    · let y := 2 ^ (m+1) - x
      have hyid : (y : ℤ) = 2 * (2 : ℤ)^m - x := by
        dsimp [y]
        rw [Int.natCast_sub (by simp only [pow_succ]; omega)]
        push_cast
        rw [pow_succ]
        ring
      have hy : 1 ≤ y ∧ y < 2 ^ (m+1) ∧ y % 2 = 1 := by
        dsimp [y]
        simp only [pow_succ]
        omega
      have hdiff : (2 : ℤ)^m - x ≡ k [ZMOD 2] := by
        change ((2 : ℤ)^m - x) % 2 = k % 2
        have hpmod : (2 : ℤ)^m % 2 = 0 := by exact_mod_cast hpar
        have hxmod : (x : ℤ) % 2 = 1 := by exact_mod_cast hxo
        omega
      have hdiv : k - ((2 : ℤ)^m - x) =
          2 * ((k - ((2 : ℤ)^m - x)) / 2) := by
        have hrem := hdiff
        change ((2 : ℤ)^m - x) % 2 = k % 2 at hrem
        omega
      refine ⟨y, hy.1, hy.2.1, hy.2.2,
        (k - ((2 : ℤ)^m - x)) / 2, ?_⟩
      have hid : (y : ℤ)^2 - (x : ℤ)^2 =
          (2 : ℤ)^(m+2) * ((2 : ℤ)^m - x) := by
        rw [hyid]
        simp only [pow_add]
        ring
      have hpnext : (2 : ℤ)^(m+1+2) = (2 : ℤ)^(m+2)*2 := by
        rw [show m+1+2 = (m+2)+1 by omega, pow_succ]
      rw [hpnext]
      nlinarith [hk, hid, congrArg (fun z : ℤ => (2 : ℤ)^(m+2)*z) hdiv]

example : ∃ x : ℕ, 1 ≤ x ∧ x < 2 ^ 1 ∧ x % 2 = 1 ∧
    ∃ k : ℤ, (8 * 1 + 1 : ℤ) = (x : ℤ)^2 + (2 : ℤ)^(1+2) * k := by
  exact ⟨1, by norm_num, by norm_num, by norm_num, 1, by norm_num⟩

/-- Somu–Tran Theorem 1: every positive natural number is a practical number
plus a triangular number, expressed without division as `2*n = 2*q + t*(t+1)`.
The bounded-root lemma above supplies the elementary lifting argument used in
the paper's proof (arXiv:2403.13533, Section 2). -/
theorem exists_practical_add_triangular (n : ℕ) (hn : 0 < n) :
    ∃ q t : ℕ, q.Practical ∧ 2 * n = 2 * q + t * (t + 1) := by
  let m := Nat.log 4 (8*n+1)
  have hm : 1 ≤ m := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlo : 4^m ≤ 8*n+1 := Nat.pow_log_le_self 4 (by omega)
  have hhi : 8*n+1 < 4^(m+1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hfour : 4^m = (2^m)^2 := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
    norm_num
  rw [hfour] at hlo
  rw [pow_succ, hfour] at hhi
  obtain ⟨x, hx, hxb, hxo, k, hk⟩ := exists_bounded_odd_square_root n m hm
  have hsquare : x^2 < 8*n+1 := by nlinarith
  have hpowerpos : (0 : ℤ) < 2^m := by positivity
  have hmodulus : (2 : ℤ)^(m+2) = 4*(2 : ℤ)^m := by
    rw [pow_add]; norm_num; ring
  rw [hmodulus] at hk
  have hsqz : (x : ℤ)^2 < 8*(n : ℤ)+1 := by exact_mod_cast hsquare
  have hhiz : 8*(n : ℤ)+1 < ((2 : ℤ)^m)^2*4 := by exact_mod_cast hhi
  have hkpos : 0 < k := by nlinarith [sq_nonneg (x : ℤ)]
  have hkbound : k ≤ (2 : ℤ)^m := by nlinarith [sq_nonneg (x : ℤ)]
  let s := k.toNat
  have hsz : (s : ℤ) = k := Int.toNat_of_nonneg (by omega)
  have hspos : 0 < s := by exact_mod_cast (show (0 : ℤ) < s by omega)
  have hsbound : s ≤ 2^m := by exact_mod_cast (show (s : ℤ) ≤ (2 : ℤ)^m by omega)
  let a := 2^(m-1)
  have ha : 2^m = 2*a := by
    calc
      2^m = 2^((m-1)+1) := by congr 1; omega
      _ = 2*a := by dsimp [a]; rw [pow_succ]; ring
  let q := a*s
  have hq : q.Practical :=
    (Nat.practical_two_pow (m-1)).mul_of_le_two_mul hspos (by rw [← ha]; exact hsbound)
  let t := x/2
  have hxt : x = 2*t+1 := by dsimp [t]; omega
  have haz : (2 : ℤ)^m = 2*(a : ℤ) := by exact_mod_cast ha
  have hxtz : (x : ℤ) = 2*(t : ℤ)+1 := by exact_mod_cast hxt
  have heqz : 2*(n : ℤ) = 2*(q : ℤ)+(t : ℤ)*(t+1) := by
    have hqz : (q : ℤ) = (a : ℤ)*s := by dsimp [q]
    rw [← hsz, haz, hxtz] at hk
    rw [hqz]
    nlinarith [hk]
  exact ⟨q, t, hq, by exact_mod_cast heqz⟩

example : ∃ q t : ℕ, q.Practical ∧ 2 * 1 = 2 * q + t * (t + 1) := by
  refine ⟨1, 0, ?_, by norm_num⟩
  simpa using Nat.practical_two_pow 0

end Nat
