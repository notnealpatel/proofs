/-
# A036284 — the (x^3+1)-power dividing the vertical Fibonacci bit vectors

OEIS A036284 encodes bit `n` of the Fibonacci numbers for `0 ≤ k < 3·2^n`
as a binary integer. Its two divisibility conjectures concern
`(x^3+1)^(2^(n-1)-1)` and an extra `x+1` factor for `n ≥ 1`.
Antti Karttunen's companion entries A136380 and A136384 encode the quotient;
the evenness in A136384 gives the additional factor `x`.

Both conjectures are proved below (`conjecture_one`, `conjecture_two`, and
the combined `X_mul_X_add_one_mul_pow_dvd`), stated on `gf2Poly (a n)`, the
literal `GF(2)[X]`-reading of A036284(n); `colF_eq_gf2Poly_a` identifies it with
`F_n = ∑_{k<3·2^n} bit_n(F(k)) x^k`.
The argument: with `h = 3·2^(n-1)`, the Pisano facts `2^n ∣ F(h)` and
`F(h-1) ≡ 1 (mod 2^n)` give `F(k+h) = F(k) + 2^n (α F(k) + β F(k+1))`, so
bit `n` of `F(k+h)` is bit `n` of `F(k)` plus a 3-periodic correction `e_k`
with `e_0 + e_1 + e_2 = 0` in `GF(2)`.  In characteristic `2`,
`1 + x^h = (1 + x^3)^(2^(n-1))` and `∑_{j<2^(n-1)} x^(3j) = (1+x^3)^(2^(n-1)-1)`,
whence `F_n = (1+x^3)^(2^(n-1)-1) · ((1+x^3) Q + x^h R)`; the cofactor
vanishes at `0` (since `F(0) = 0`) and at `1` (since `R(1) = ∑ e_i = 0`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A036284SumBitFib

open Polynomial

/-! ## Definitions -/

/-- `fibBit n k` is bit `n` of the Fibonacci number `F(k)`, i.e.
`floor(F(k) / 2^n) mod 2`, exactly as in the A036284 formula. -/
def fibBit (n k : ℕ) : ℕ := Nat.fib k / 2 ^ n % 2

/-- A036284: `a(n) = ∑_{k=0}^{3·2^n - 1} (bit n of F(k)) · 2^k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (3 * 2 ^ n), fibBit n k * 2 ^ k

/-- Reading a natural number `m` as a `GF(2)[X]`-polynomial: bit `i` of `m`
becomes the coefficient of `X^i`.  (Bits of index `≥ m` vanish, so the range
`m` loses nothing.) -/
noncomputable def gf2Poly (m : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range m, C ((m / 2 ^ i % 2 : ℕ) : ZMod 2) * X ^ i

/-- `F_n(x) = ∑_{k=0}^{3·2^n - 1} bit_n(F(k)) x^k ∈ GF(2)[x]`, the polynomial
whose coefficient vector is the bit vector defining A036284(n). -/
noncomputable def colF (n : ℕ) : (ZMod 2)[X] :=
  ∑ k ∈ Finset.range (3 * 2 ^ n), C ((fibBit n k : ℕ) : ZMod 2) * X ^ k

/-! the first five listed terms of A036284. -/

example : a 0 = 6 := by decide
example : a 1 = 24 := by decide
example : a 2 = 1440 := by decide
example : a 3 = 5728448 := by decide
example : a 4 = 92568198012160 := by decide

/-! ## Fibonacci arithmetic -/

/-- Pisano facts modulo `2^(m+1)`: `2^(m+1) ∣ F(3·2^m)` and
`F(3·2^m + 1) ≡ 1 (mod 2^(m+1))`, in explicit witness form. -/
theorem pisano (m : ℕ) : (∃ x, Nat.fib (3 * 2 ^ m) = 2 ^ (m + 1) * x) ∧
    ∃ y, Nat.fib (3 * 2 ^ m + 1) = 2 ^ (m + 1) * y + 1 := by
  induction m with
  | zero => exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
  | succ m ih =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := ih
    have h2 : 3 * 2 ^ (m + 1) = 2 * (3 * 2 ^ m) := by ring
    refine ⟨?_, ?_⟩
    · rw [h2, Nat.fib_two_mul]
      have hev : 2 ∣ 2 * Nat.fib (3 * 2 ^ m + 1) - Nat.fib (3 * 2 ^ m) := by
        apply Nat.dvd_sub (dvd_mul_right 2 _)
        rw [hx]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero m)) x
      obtain ⟨c, hc⟩ := hev
      exact ⟨x * c, by rw [hc, hx]; ring⟩
    · rw [h2, Nat.fib_two_mul_add_one, hx, hy]
      exact ⟨y + 2 ^ m * y ^ 2 + 2 ^ m * x ^ 2, by ring⟩

/-- Shift by the half-period `3·2^m`: there are `α β` with
`F(k + 3·2^m) = F(k) + 2^(m+1) (α F(k) + β F(k+1))` for every `k`. -/
theorem fib_shift (m : ℕ) : ∃ α β : ℕ, ∀ k, Nat.fib (k + 3 * 2 ^ m) =
    Nat.fib k + 2 ^ (m + 1) * (α * Nat.fib k + β * Nat.fib (k + 1)) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := pisano m
  set g := 3 * 2 ^ m - 1 with hg
  have hh : 3 * 2 ^ m = g + 1 := by
    have : 1 ≤ 3 * 2 ^ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  rw [hh] at hx hy
  have heq : Nat.fib g + 2 ^ (m + 1) * x = 1 + 2 ^ (m + 1) * y := by
    rw [← hx, add_comm 1, ← hy, ← Nat.fib_add_two]
  have hmod : Nat.fib g % 2 ^ (m + 1) = 1 := by
    have h1 := congrArg (· % 2 ^ (m + 1)) heq
    simp only [Nat.add_mul_mod_self_left] at h1
    rw [h1]
    exact Nat.one_mod_eq_one.mpr (Nat.one_lt_two_pow (Nat.succ_ne_zero m)).ne'
  refine ⟨Nat.fib g / 2 ^ (m + 1), x, fun k => ?_⟩
  have hg' : Nat.fib g = 2 ^ (m + 1) * (Nat.fib g / 2 ^ (m + 1)) + 1 := by
    have := Nat.div_add_mod (Nat.fib g) (2 ^ (m + 1))
    omega
  rw [hh, show k + (g + 1) = g + k + 1 by ring, Nat.fib_add, hx]
  conv_lhs => rw [hg']
  ring

/-- Bit `m+1` of `F(k + 3·2^m)` equals bit `m+1` of `F(k)` plus the correction
`α F(k) + β F(k+1)`, in `GF(2)`. -/
theorem fibBit_shift (m α β : ℕ) (hshift : ∀ k, Nat.fib (k + 3 * 2 ^ m) =
    Nat.fib k + 2 ^ (m + 1) * (α * Nat.fib k + β * Nat.fib (k + 1))) (k : ℕ) :
    ((fibBit (m + 1) (k + 3 * 2 ^ m) : ℕ) : ZMod 2) =
      ((fibBit (m + 1) k : ℕ) : ZMod 2) + ((α * Nat.fib k + β * Nat.fib (k + 1) : ℕ) : ZMod 2) := by
  unfold fibBit
  rw [hshift, Nat.add_mul_div_left _ _ (by positivity)]
  simp only [ZMod.natCast_mod, Nat.cast_add]

/-! ## Polynomial identities over `GF(2)` -/

/-- `∑_{j<2^m} X^(3j) = (X^3 + 1)^(2^m - 1)` in `GF(2)[X]`. -/
theorem geom_X3 (m : ℕ) :
    (∑ j ∈ Finset.range (2 ^ m), (X : (ZMod 2)[X]) ^ (3 * j)) = (X ^ 3 + 1) ^ (2 ^ m - 1) := by
  have hne : (X ^ 3 + 1 : (ZMod 2)[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  apply mul_right_cancel₀ hne
  have h1 : (∑ j ∈ Finset.range (2 ^ m), (X : (ZMod 2)[X]) ^ (3 * j)) * (X ^ 3 + 1)
      = (X ^ 3) ^ (2 ^ m) - 1 := by
    rw [← geom_sum_mul, CharTwo.sub_eq_add]
    simp_rw [pow_mul]
  rw [h1, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, add_pow_char_pow, one_pow,
    CharTwo.sub_eq_add]

/-- A 3-periodic coefficient sequence over `3M` terms factors as
`(e₀ + e₁ X + e₂ X²) · ∑_{j<M} X^(3j)`. -/
theorem periodic_sum (e : ℕ → ZMod 2) (he : ∀ k, e (k + 3) = e k) (M : ℕ) :
    ∑ k ∈ Finset.range (3 * M), C (e k) * X ^ k
      = (C (e 0) + C (e 1) * X + C (e 2) * X ^ 2) *
          ∑ j ∈ Finset.range M, (X : (ZMod 2)[X]) ^ (3 * j) := by
  have hper : ∀ j x, e (3 * j + x) = e x := by
    intro j x
    induction j with
    | zero => simp
    | succ j ih => rw [show 3 * (j + 1) + x = (3 * j + x) + 3 by ring, he, ih]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 3 * (M + 1) = 3 * M + 3 by ring, Finset.sum_range_add, ih, Finset.sum_range_succ _ M]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hper, pow_add]
    ring

/-- Splitting identity: if `s (k + 3·2^m) = s k + e k` with `e` 3-periodic, then
`∑_{k<3·2^(m+1)} s_k X^k = (X^3+1)^(2^m-1) · ((X^3+1) Q + X^(3·2^m) R)` where
`Q = ∑_{k<3·2^m} s_k X^k` and `R = e₀ + e₁ X + e₂ X²`. -/
theorem split_sum (m : ℕ) (s e : ℕ → ZMod 2) (he : ∀ k, e (k + 3) = e k)
    (hs : ∀ k, s (k + 3 * 2 ^ m) = s k + e k) :
    ∑ k ∈ Finset.range (3 * 2 ^ (m + 1)), C (s k) * X ^ k
      = (X ^ 3 + 1) ^ (2 ^ m - 1) *
          ((X ^ 3 + 1) * ∑ k ∈ Finset.range (3 * 2 ^ m), C (s k) * X ^ k
            + X ^ (3 * 2 ^ m) * (C (e 0) + C (e 1) * X + C (e 2) * X ^ 2)) := by
  set h := 3 * 2 ^ m with hh
  set Q := ∑ k ∈ Finset.range h, C (s k) * X ^ k with hQ
  set R : (ZMod 2)[X] := C (e 0) + C (e 1) * X + C (e 2) * X ^ 2 with hR
  set G : (ZMod 2)[X] := (X ^ 3 + 1) ^ (2 ^ m - 1) with hG
  have hE : ∑ k ∈ Finset.range h, C (e k) * X ^ k = R * G := by
    rw [hh, periodic_sum e he, geom_X3]
  have hcomb : G * (X ^ 3 + 1) = X ^ h + 1 := by
    rw [hG, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, add_pow_char_pow, one_pow,
      ← pow_mul]
  have htop : ∑ x ∈ Finset.range h, C (s (h + x)) * X ^ (h + x)
      = X ^ h * (Q + ∑ k ∈ Finset.range h, C (e k) * X ^ k) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_comm h x, hs, C_add, pow_add]
    ring
  rw [show 3 * 2 ^ (m + 1) = h + h by rw [hh]; ring, Finset.sum_range_add, htop, hE]
  linear_combination (-Q) * hcomb

/-! ## The factorisation of `F_n` -/

/-- `F(k+3) ≡ F(k) (mod 2)`. -/
theorem fib_add_three_cast (k : ℕ) : ((Nat.fib (k + 3) : ℕ) : ZMod 2) = Nat.fib k := by
  have h : Nat.fib (k + 3) = Nat.fib k + 2 * Nat.fib (k + 1) := by
    rw [show k + 3 = (k + 1) + 2 by ring, Nat.fib_add_two, Nat.fib_add_two]
    ring
  rw [h]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

/-- For `n = m + 1`: `F_n = (X^3+1)^(2^m - 1) · P` with a cofactor `P` vanishing
at `0` and at `1`. -/
theorem colF_factor (m : ℕ) : ∃ P : (ZMod 2)[X],
    colF (m + 1) = (X ^ 3 + 1) ^ (2 ^ m - 1) * P ∧ P.eval 0 = 0 ∧ P.eval 1 = 0 := by
  obtain ⟨α, β, hshift⟩ := fib_shift m
  set s : ℕ → ZMod 2 := fun k => ((fibBit (m + 1) k : ℕ) : ZMod 2) with hs
  set e : ℕ → ZMod 2 := fun k => ((α * Nat.fib k + β * Nat.fib (k + 1) : ℕ) : ZMod 2) with he
  have hper : ∀ k, e (k + 3) = e k := by
    intro k
    simp only [he, Nat.cast_add, Nat.cast_mul, fib_add_three_cast,
      show k + 3 + 1 = (k + 1) + 3 by ring]
  have hsh : ∀ k, s (k + 3 * 2 ^ m) = s k + e k := fibBit_shift m α β hshift
  refine ⟨(X ^ 3 + 1) * ∑ k ∈ Finset.range (3 * 2 ^ m), C (s k) * X ^ k
      + X ^ (3 * 2 ^ m) * (C (e 0) + C (e 1) * X + C (e 2) * X ^ 2), ?_, ?_, ?_⟩
  · exact split_sum m s e hper hsh
  · have hs0 : s 0 = 0 := by simp [hs, fibBit]
    have hh : 3 * 2 ^ m ≠ 0 := by positivity
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_finsetSum, eval_C]
    rw [zero_pow hh, Finset.sum_eq_single 0]
    · simp [hs0]
    · intro b _ hb
      simp [zero_pow hb]
    · simp
  · simp only [eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_finsetSum, eval_C, one_pow,
      mul_one, he]
    rw [show (1 + 1 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    simp only [Nat.fib_zero, Nat.fib_one, zero_add, Nat.fib_two, Nat.cast_add, Nat.cast_mul,
      Nat.cast_zero, Nat.cast_one]
    generalize (α : ZMod 2) = u
    generalize (β : ZMod 2) = v
    revert u v
    decide

/-- `X (X + 1)` divides every `P ∈ GF(2)[X]` vanishing at `0` and at `1`. -/
theorem X_mul_X_add_one_dvd (P : (ZMod 2)[X]) (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    X * (X + 1) ∣ P := by
  have hX : X ∣ P := by
    have h := (dvd_iff_isRoot (a := (0 : ZMod 2)) (p := P)).mpr h0
    simpa using h
  have hX1 : X + 1 ∣ P := by
    have h := (dvd_iff_isRoot (a := (1 : ZMod 2)) (p := P)).mpr h1
    rwa [C_1, CharTwo.sub_eq_add] at h
  have hcop : IsCoprime (X : (ZMod 2)[X]) (X + 1) := ⟨-1, 1, by ring⟩
  exact hcop.mul_dvd hX hX1

/-- `(X^3 + 1)^k` is monic. -/
theorem monic_X_pow_three_add_one_pow (k : ℕ) : ((X ^ 3 + 1 : (ZMod 2)[X]) ^ k).Monic := by
  have h : (X ^ 3 + C 1 : (ZMod 2)[X]).Monic := monic_X_pow_add_C 1 (by norm_num)
  rw [C_1] at h
  exact h.pow k

/-! ## Bridge: `F_n` is `A036284(n)` read as a `GF(2)[X]`-polynomial -/

/-- Binary digits of `∑_{k<L} b_k 2^k` for a `0/1` sequence `b`: digit `i` is
`b_i` for `i < L` and `0` otherwise. -/
theorem sum_bits_div_mod (L : ℕ) (b : ℕ → ℕ) (hb : ∀ k, b k < 2) (i : ℕ) :
    (∑ k ∈ Finset.range L, b k * 2 ^ k) / 2 ^ i % 2 = if i < L then b i else 0 := by
  induction L generalizing b i with
  | zero => simp
  | succ L ih =>
    have hsplit : ∑ k ∈ Finset.range (L + 1), b k * 2 ^ k
        = b 0 + 2 * ∑ k ∈ Finset.range L, b (k + 1) * 2 ^ k := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsplit]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hb 0),
        Nat.zero_lt_succ, if_true]
    | succ i =>
      have hdiv : (b 0 + 2 * ∑ k ∈ Finset.range L, b (k + 1) * 2 ^ k) / 2
          = ∑ k ∈ Finset.range L, b (k + 1) * 2 ^ k := by
        rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hb 0), zero_add]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv, ih (fun k => b (k + 1)) (fun k => hb _) i]
      simp only [Nat.add_lt_add_iff_right]

/-- The coefficient of `X^i` in the `GF(2)`-reading of `m` is bit `i` of `m`. -/
theorem gf2Poly_coeff (m i : ℕ) : (gf2Poly m).coeff i = ((m / 2 ^ i % 2 : ℕ) : ZMod 2) := by
  unfold gf2Poly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have hlt : m < 2 ^ i :=
      (Nat.lt_two_pow_self).trans_le
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp (Finset.mem_range.not.mp h)))
    rw [Nat.div_eq_of_lt hlt]
    rfl

/-- `F_n` is exactly A036284(n) read as a `GF(2)[X]`-polynomial. -/
theorem colF_eq_gf2Poly_a (n : ℕ) : colF n = gf2Poly (a n) := by
  ext i
  rw [gf2Poly_coeff, a, sum_bits_div_mod _ (fibBit n) (fun k => Nat.mod_lt _ (by norm_num)), colF,
    finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Finset.mem_range.mp h1) h2
  · exact absurd (Finset.mem_range.mpr h2) h1
  · rfl

/-! ## The conjectures -/

/-- `F_n` form of Conjecture 1: for `n ≥ 1`, `(x^3 + 1)^(2^(n-1) - 1)` divides
`F_n(x) = ∑_{k<3·2^n} bit_n(F(k)) x^k` in `GF(2)[X]`. -/
theorem pow_dvd_colF (n : ℕ) (hn : 1 ≤ n) :
    (X ^ 3 + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 1) - 1) ∣ colF n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, hP, -, -⟩ := colF_factor m
  rw [hP, Nat.add_sub_cancel]
  exact dvd_mul_right _ _

/-- `F_n` form of Conjecture 2: for `n ≥ 1`, the exact quotient
`F_n /ₘ (x^3 + 1)^(2^(n-1) - 1)` is divisible by `x (x + 1)` in `GF(2)[X]`. -/
theorem X_mul_X_add_one_dvd_colF_divByMonic (n : ℕ) (hn : 1 ≤ n) :
    X * (X + 1) ∣ colF n /ₘ (X ^ 3 + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 1) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, hP, h0, h1⟩ := colF_factor m
  rw [hP, Nat.add_sub_cancel, mul_divByMonic_cancel_left P (monic_X_pow_three_add_one_pow _)]
  exact X_mul_X_add_one_dvd P h0 h1

/-- **A036284, Conjecture 1** (comment in A036284, see also A136380).

"For n>=1, each term a(n), when considered as a GF(2)[X]-polynomial,
is divisible by GF(2)[X] -polynomial (x^3 + 1) ^ A000225(n-1)."
Here `A000225(n-1) = 2^(n-1) - 1` (the `Nat` subtraction is exact since
`1 ≤ 2^(n-1)`), and `gf2Poly (a n)` is A036284(n) read as a `GF(2)[X]`-polynomial. -/
theorem conjecture_one (n : ℕ) (hn : 1 ≤ n) :
    (X ^ 3 + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 1) - 1) ∣ gf2Poly (a n) := by
  rw [← colF_eq_gf2Poly_a]
  exact pow_dvd_colF n hn

/-- **A036284, Conjecture 2** (comment in A036284, see A136380 and A136384).

"Conjecture 2: there is also one extra (x^1 + 1) factor present, see
A136384."  A136384(n) is the quotient of `A136380(n)/2` by `x + 1`, where
A136380(n) is the quotient of A036284(n) by `(x^3+1)^A000225(n-1)` in
`GF(2)[X]`; so the claim is that this quotient (computed here as the exact
monic division `/ₘ`) is divisible by `x (x + 1)` for every `n ≥ 1`. -/
theorem conjecture_two (n : ℕ) (hn : 1 ≤ n) :
    X * (X + 1) ∣ gf2Poly (a n) /ₘ (X ^ 3 + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 1) - 1) := by
  rw [← colF_eq_gf2Poly_a]
  exact X_mul_X_add_one_dvd_colF_divByMonic n hn

/-- Combined form of both conjectures: for `n ≥ 1`,
`x (x + 1) (x^3 + 1)^(2^(n-1) - 1)` divides A036284(n) read in `GF(2)[X]`. -/
theorem X_mul_X_add_one_mul_pow_dvd (n : ℕ) (hn : 1 ≤ n) :
    X * (X + 1) * (X ^ 3 + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 1) - 1) ∣ gf2Poly (a n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, hP, h0, h1⟩ := colF_factor m
  rw [← colF_eq_gf2Poly_a, hP, Nat.add_sub_cancel, mul_comm (X * (X + 1))]
  exact mul_dvd_mul_left _ (X_mul_X_add_one_dvd P h0 h1)

/-! Example: the hypothesis `1 ≤ n` is met, e.g. at `n = 3`, where the
divisor `(x^3+1)^3` is a genuine (degree 9) factor. -/

example : (X ^ 3 + 1 : (ZMod 2)[X]) ^ 3 ∣ gf2Poly (a 3) := conjecture_one 3 (by norm_num)

end Candidates.A036284SumBitFib
