/-
# A110735 — the "no term is zero" conjecture is false

## OEIS source (retrieved 2026-10-21, `oeis show A110735`)

```
A110735   Let n = a_1a_2...a_k, where the a_i are digits. a(n) = least multiple
          of n of the type b_1a_1b_2a_2...a_kb_{k+1}, obtained by inserting
          single digits b_i in the gaps and both ends; 0 if no such number
          exists.
DATA      110,120,132,140,150,162,175,184,198,11000,11011,11028,11037,11046,
          11055,11168,11271,11088,11096,12000,12012,12122,12236,12048,12050,
          12064,12177,12180,12093,13200,13113,13024,13035,13940,13055,13068
COMMENT   Conjecture: no term is zero. For a k-digit number there are k+1
          spaces and 10^(k+1) candidates, so the chances that one of them is a
          multiple of n increases with k on the one hand although the
          probability decreases because n becomes large.
COMMENT   It may well be the case that no term is zero, but the probabilistic
          argument above is not sufficient to establish it. ...
          - _Franklin T. Adams-Watters_, Sep 25 2006
```

The conjecture comment is unsigned (it belongs to the original 2005
submission).  The entry has no formula or program lines.  The DATA values
(`a(1) = 110`, `a(10) = 11000`) show that the inserted leading digit `b_1` is
nonzero: a candidate for a `k`-digit `n` has exactly `2k + 1` digits.

## Status

Literature status (triage): no proof or disproof is recorded in the entry or on
the live page (which still has data only for `n ≤ 36`); no zero term has been
recorded anywhere.  This module **refutes** the conjecture: `a(101) = 0`
(`a_101`, `not_conjecture`).  It also proves the infinite zero family
`a(10^(2m) + 1) = 0` for every `m ≥ 1` (`a_ten_pow_two_mul_add_one`), so even
the weakening "a(n) ≠ 0 for all large n" is false (`not_eventually_ne_zero`).
Computation (outside Lean) lists the zeros below 1000 as 101, 202, 303, 398,
404, 597, 606, 625, 707, 804, 808, 909.

Proof for `n = 101`.  A candidate is
`C = b₁·10⁶ + 10⁵ + b₂·10⁴ + b₃·10² + 10 + b₄`, and
`C + b₁ + b₃ = 101·K + (20 + b₂ + b₄)`, so `101 ∣ C` would force
`b₁ + b₃ ≡ 20 + b₂ + b₄ (mod 101)`, impossible since `b₁ + b₃ ≤ 18 < 20`.

Proof of the family (`m ≥ 2`).  Put `X = 10^(2m)` and split a candidate as
`C = (H·X + M)·X + L` with `L, M < X`.  Then
`C = (X + 1)(H·X - H + M) + (H - M + L)`.  The digit constraints give
`H < 1000`, `10·L < X` (digit `2m - 1` of `C` is `0`), so
`|H - M + L| < X + 1`, whence `H - M + L = 0`.  Reducing mod `100` with the
tens digits `H ≡ 10`, `L ≡ 10`, `M ≡ 0` gives `20 + h₀ + l₀ ≡ m₀ (mod 100)` for
units digits `h₀, l₀, m₀ ≤ 9`, impossible.  The case `m = 1` is `n = 101`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A110735Refutation

/-! ## Definitions -/

/-- The number `k` of decimal digits of `n` (for `n ≥ 1`). -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-- `Weave k n m`: writing `n = a_1 a_2 … a_k` in decimal (`k` digits), `m` is
of the form `b_1 a_1 b_2 a_2 … a_k b_{k+1}` for some digits `b_i` with
`b_1 ≠ 0`.  Encoded arithmetically: `m` has exactly `2k + 1` digits
(`10^(2k) ≤ m < 10^(2k+1)`, i.e. the leading inserted digit `b_1` is nonzero),
and the digit of `m` at position `2i + 1` (counting from the units digit,
position `0`) equals the digit of `n` at position `i`, for every `i < k`.  The
even positions of `m` (the inserted `b_i`) are unconstrained. -/
def Weave (k n m : ℕ) : Prop :=
  10 ^ (2 * k) ≤ m ∧ m < 10 ^ (2 * k + 1) ∧
    ∀ i < k, m / 10 ^ (2 * i + 1) % 10 = n / 10 ^ i % 10

instance (k n m : ℕ) : Decidable (Weave k n m) := by
  unfold Weave
  infer_instance

/-- `IsWeave n m`: `m` is obtained from `n` by inserting one digit in each of
the `k - 1` gaps between consecutive decimal digits of `n` and at both ends,
the leading inserted digit being nonzero. -/
def IsWeave (n m : ℕ) : Prop := Weave (numDigits n) n m

instance (n m : ℕ) : Decidable (IsWeave n m) := by
  unfold IsWeave
  infer_instance

/-- **A110735.** `a n` is the least multiple of `n` of the form
`b_1 a_1 b_2 a_2 … a_k b_{k+1}` (`IsWeave n m`), or `0` if there is none.
Every such multiple `n·q` has `n·q < 10^(2k+1)`, so for `n ≥ 1` its cofactor
satisfies `q < 10^(2k+1)`; scanning `q = 0, 1, …, 10^(2k+1) - 1` in increasing
order and taking the first hit gives the least multiple. -/
def a (n : ℕ) : ℕ :=
  let k := numDigits n
  n * ((List.range (10 ^ (2 * k + 1))).find? (fun q => decide (Weave k n (n * q)))).getD 0

/-! ## Ground truth against the OEIS DATA line (offset 1) -/

example : (List.range' 1 36).map a =
    [110, 120, 132, 140, 150, 162, 175, 184, 198, 11000, 11011, 11028, 11037, 11046, 11055,
      11168, 11271, 11088, 11096, 12000, 12012, 12122, 12236, 12048, 12050, 12064, 12177,
      12180, 12093, 13200, 13113, 13024, 13035, 13940, 13055, 13068] := by
  decide +kernel

/- Non-vacuity of the weave predicate at the counterexample: `1100010`
(`b = 1, 0, 0, 0`) and `9190919` (`b = 9, 9, 9, 9`) are weaves of `101`; none
is a multiple of `101`. -/
example : IsWeave 101 1100010 ∧ IsWeave 101 9190919 := by decide +kernel

/-! ## Reduction of `a n = 0` to the absence of weave multiples -/

/-- If no weave of `n` is a multiple of `n`, then `a n = 0`. -/
theorem a_eq_zero_of_forall (n : ℕ) (h : ∀ m, IsWeave n m → ¬ n ∣ m) : a n = 0 := by
  have hnone : (List.range (10 ^ (2 * numDigits n + 1))).find?
      (fun q => decide (Weave (numDigits n) n (n * q))) = none := by
    rw [List.find?_eq_none]
    intro q _ hq
    exact h (n * q) (of_decide_eq_true hq) (dvd_mul_right n q)
  simp only [a, hnone, Option.getD_none, mul_zero]

/-! ## The counterexample `n = 101` -/

/-- `101` has three decimal digits. -/
theorem numDigits_101 : numDigits 101 = 3 := by
  norm_num [numDigits]

/-- No weave `b₁ 1 b₂ 0 b₃ 1 b₄` of `101` is a multiple of `101`: modulo
`101` such a number is `20 + b₂ + b₄ - b₁ - b₃ ∈ [2, 38]`. -/
theorem not_dvd_of_weave_101 (m : ℕ) (hw : Weave 3 101 m) : ¬ 101 ∣ m := by
  obtain ⟨hlo, hhi, hd⟩ := hw
  have h0 := hd 0 (by norm_num)
  have h1 := hd 1 (by norm_num)
  have h2 := hd 2 (by norm_num)
  norm_num at h0 h1 h2 hlo hhi
  have hm : m = m / 10 ^ 6 * 10 ^ 6 + 10 ^ 5 + m / 10 ^ 4 % 10 * 10 ^ 4 + m / 100 % 10 * 100
      + 10 + m % 10 := by omega
  have hb1 : m / 10 ^ 6 < 10 := by omega
  have hb2 : m / 10 ^ 4 % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hb3 : m / 100 % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hb4 : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  clear h0 h1 h2 hlo hhi hd
  generalize m / 10 ^ 6 = b1 at hm hb1
  generalize m / 10 ^ 4 % 10 = b2 at hm hb2
  generalize m / 100 % 10 = b3 at hm hb3
  generalize m % 10 = b4 at hm hb4
  subst hm
  rintro ⟨e, he⟩
  have key : b1 * 10 ^ 6 + 10 ^ 5 + b2 * 10 ^ 4 + b3 * 100 + 10 + b4 + b1 + b3 =
      101 * (9901 * b1 + 990 + 99 * b2 + b3) + (20 + b2 + b4) := by ring
  rw [he] at key
  generalize 9901 * b1 + 990 + 99 * b2 + b3 = K at key
  rcases Nat.lt_or_ge K e with hKe | heK
  · omega
  · omega

/-- **Counterexample.** `a(101) = 0`. -/
theorem a_101 : a 101 = 0 := by
  apply a_eq_zero_of_forall
  intro m hm
  rw [IsWeave, numDigits_101] at hm
  exact not_dvd_of_weave_101 m hm

/-- **The A110735 conjecture is false.**  The entry's comment "Conjecture: no
term is zero" asserts `a n ≠ 0` for every `n ≥ 1` (the offset is `1`); this is
refuted by `n = 101`. -/
theorem not_conjecture : ¬ ∀ n : ℕ, 1 ≤ n → a n ≠ 0 :=
  fun h => h 101 (by norm_num) a_101

/-! ## The zero family `n = 10^(2m) + 1` -/

/-- Shifting: digit `b` of `C / 10^a` is digit `a + b` of `C`. -/
theorem digit_div_pow (C a b : ℕ) : C / 10 ^ a / 10 ^ b % 10 = C / 10 ^ (a + b) % 10 := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Truncation: for `j < e`, digit `j` of `C % 10^e` is digit `j` of `C`. -/
theorem digit_mod_pow (C e j : ℕ) (h : j < e) : C % 10 ^ e / 10 ^ j % 10 = C / 10 ^ j % 10 := by
  rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd, Nat.mod_mul_right_div_self]
  rw [← pow_succ]
  exact Nat.pow_dvd_pow 10 h

/-- `10^(2m) + 1` has `2m + 1` decimal digits. -/
theorem numDigits_ten_pow_add_one (m : ℕ) : numDigits (10 ^ (2 * m) + 1) = 2 * m + 1 := by
  have h : 1 ≤ 10 ^ (2 * m) := Nat.one_le_pow _ _ (by norm_num)
  unfold numDigits
  rw [Nat.length_digits 10 _ (by norm_num) (by omega)]
  congr 1
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]
    omega

/-- The units digit of `10^(2m) + 1` (`m ≥ 1`) is `1`. -/
theorem digit_zero_ten_pow_add_one (m : ℕ) (hm : 1 ≤ m) :
    (10 ^ (2 * m) + 1) / 10 ^ 0 % 10 = 1 := by
  obtain ⟨d, hd⟩ : ∃ d, 2 * m = d + 1 := ⟨2 * m - 1, by omega⟩
  rw [hd, pow_succ, pow_zero, Nat.div_one]
  omega

/-- The middle digits of `10^(2m) + 1` vanish: digit `i` is `0` for
`1 ≤ i < 2m`. -/
theorem digit_mid_ten_pow_add_one (m i : ℕ) (hi1 : 1 ≤ i) (hi2 : i < 2 * m) :
    (10 ^ (2 * m) + 1) / 10 ^ i % 10 = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, 2 * m = i + (d + 1) := ⟨2 * m - i - 1, by omega⟩
  have hpos : 0 < 10 ^ i := pow_pos (by norm_num) i
  have hone : 1 / 10 ^ i = 0 := by
    rw [Nat.div_eq_zero_iff]
    right
    calc 1 < 10 ^ 1 := by norm_num
      _ ≤ 10 ^ i := Nat.pow_le_pow_right (by norm_num) hi1
  rw [hd, pow_add, Nat.mul_add_div hpos, hone, add_zero, pow_succ]
  omega

/-- The leading digit (position `2m`) of `10^(2m) + 1` (`m ≥ 1`) is `1`. -/
theorem digit_top_ten_pow_add_one (m : ℕ) (hm : 1 ≤ m) :
    (10 ^ (2 * m) + 1) / 10 ^ (2 * m) % 10 = 1 := by
  have hpos : 0 < 10 ^ (2 * m) := pow_pos (by norm_num) _
  have hone : 1 / 10 ^ (2 * m) = 0 := by
    rw [Nat.div_eq_zero_iff]
    right
    calc 1 < 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show 10 ^ (2 * m) + 1 = 10 ^ (2 * m) * 1 + 1 by ring, Nat.mul_add_div hpos, hone]

/-- **Integer core of the family.**  If `X ≥ 1100`, `H < 1000`, `M < X`,
`10·L < X`, and the tens digits of `H, M, L` are `1, 0, 1`, then `X + 1` does
not divide `(H·X + M)·X + L`.  (Modulo `X + 1` the number is `H - M + L`,
which has absolute value `< X + 1`, hence would vanish; its value mod `100`
excludes that.) -/
theorem int_core (X H M L : ℕ) (hX : 1100 ≤ X) (hH : H < 1000) (hM : M < X) (hL : 10 * L < X)
    (hH1 : H / 10 % 10 = 1) (hM1 : M / 10 % 10 = 0) (hL1 : L / 10 % 10 = 1)
    (hdvd : (X + 1) ∣ (H * X + M) * X + L) : False := by
  have hdvdZ : ((X : ℤ) + 1) ∣ (H : ℤ) - M + L := by
    have h1 : ((X : ℤ) + 1) ∣ (((H * X + M) * X + L : ℕ) : ℤ) := by exact_mod_cast hdvd
    have h2 : ((H : ℤ) - M + L) = (((H * X + M) * X + L : ℕ) : ℤ)
        - ((X : ℤ) + 1) * (H * X - H + M) := by push_cast; ring
    rw [h2]
    exact dvd_sub h1 (dvd_mul_right _ _)
  have hzero : (H : ℤ) - M + L = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvdZ
    rw [abs_lt]
    constructor <;> omega
  have hH' : H = 100 * (H / 100) + 10 + H % 10 := by omega
  have hL' : L = 100 * (L / 100) + 10 + L % 10 := by omega
  have hM' : M = 100 * (M / 100) + M % 10 := by omega
  have hh0 : H % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hl0 : L % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hm0 : M % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hnat : H + L = M := by omega
  rw [hH', hL', hM'] at hnat
  generalize H / 100 = h' at hnat
  generalize L / 100 = l' at hnat
  generalize M / 100 = m' at hnat
  generalize H % 10 = h0 at hnat hh0
  generalize L % 10 = l0 at hnat hl0
  generalize M % 10 = m0 at hnat hm0
  rcases Nat.lt_or_ge (h' + l') m' with hlt | hge
  · omega
  · omega

/-- **Zero family, `m ≥ 2`.**  No weave of `n = 10^(2m) + 1` is a multiple
of `n`. -/
theorem not_dvd_of_weave_ten_pow_add_one (m : ℕ) (hm : 2 ≤ m) (C : ℕ)
    (hw : Weave (2 * m + 1) (10 ^ (2 * m) + 1) C) : ¬ (10 ^ (2 * m) + 1) ∣ C := by
  obtain ⟨_, hhi, hd⟩ := hw
  set X := 10 ^ (2 * m) with hXdef
  have hXpos : 0 < X := pow_pos (by norm_num) _
  -- the four digit constraints used (positions `1`, `2m - 1`, `2m + 1`, `4m + 1`)
  have hd0 : C / 10 ^ 1 % 10 = 1 := by
    have h := hd 0 (by omega)
    rwa [digit_zero_ten_pow_add_one m (by omega)] at h
  have hdA : C / 10 ^ (2 * m - 1) % 10 = 0 := by
    have h := hd (m - 1) (by omega)
    rwa [digit_mid_ten_pow_add_one m (m - 1) (by omega) (by omega),
      show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at h
  have hdB : C / 10 ^ (2 * m + 1) % 10 = 0 := by
    have h := hd m (by omega)
    rwa [digit_mid_ten_pow_add_one m m (by omega) (by omega)] at h
  have hdC : C / 10 ^ (2 * m + (2 * m + 1)) % 10 = 1 := by
    have h := hd (2 * m) (by omega)
    rwa [digit_top_ten_pow_add_one m (by omega),
      show 2 * (2 * m) + 1 = 2 * m + (2 * m + 1) by omega] at h
  -- block decomposition `C = (H·X + M)·X + L`
  have hdecomp : C = (C / X / X * X + C / X % X) * X + C % X := by
    rw [Nat.div_add_mod' (C / X) X, Nat.div_add_mod' C X]
  have hL1 : C % X / 10 % 10 = 1 := by
    have h := digit_mod_pow C (2 * m) 1 (by omega)
    rw [pow_one, ← hXdef] at h
    rw [pow_one] at hd0
    exact h.trans hd0
  have hL : 10 * (C % X) < X := by
    have hYpos : 0 < 10 ^ (2 * m - 1) := pow_pos (by norm_num) _
    have hX' : X = 10 ^ (2 * m - 1) * 10 := by
      rw [hXdef, ← pow_succ]
      congr 1
      omega
    have hdig : C % X / 10 ^ (2 * m - 1) % 10 = 0 := by
      have h := digit_mod_pow C (2 * m) (2 * m - 1) (by omega)
      rw [← hXdef] at h
      exact h.trans hdA
    have hlt : C % X / 10 ^ (2 * m - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul hYpos, mul_comm, ← hX']
      exact Nat.mod_lt _ hXpos
    have hq : C % X / 10 ^ (2 * m - 1) = 0 := by
      generalize C % X / 10 ^ (2 * m - 1) = t at hdig hlt ⊢
      omega
    rw [Nat.div_eq_zero_iff] at hq
    rcases hq with hq | hq
    · exact absurd hq hYpos.ne'
    · calc 10 * (C % X) < 10 * 10 ^ (2 * m - 1) := by omega
        _ = X := by rw [hX', mul_comm]
  have hM1 : C / X % X / 10 % 10 = 0 := by
    have h1 := digit_mod_pow (C / X) (2 * m) 1 (by omega)
    have h2 := digit_div_pow C (2 * m) 1
    rw [pow_one, ← hXdef] at h1 h2
    exact h1.trans (h2.trans hdB)
  have hH1 : C / X / X / 10 % 10 = 1 := by
    have h3 := digit_div_pow (C / X) (2 * m) 1
    have h4 := digit_div_pow C (2 * m) (2 * m + 1)
    rw [pow_one, ← hXdef] at h3
    rw [← hXdef] at h4
    exact h3.trans (h4.trans hdC)
  have hH : C / X / X < 1000 := by
    rw [Nat.div_lt_iff_lt_mul hXpos, Nat.div_lt_iff_lt_mul hXpos]
    have h : 10 ^ (2 * (2 * m + 1) + 1) = 1000 * X * X := by
      rw [hXdef, show 2 * (2 * m + 1) + 1 = 3 + 2 * m + 2 * m by ring, pow_add, pow_add]
      norm_num
    rw [← h]
    exact hhi
  have hX : 1100 ≤ X := by
    calc 1100 ≤ 10 ^ 4 := by norm_num
      _ ≤ X := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro hdvd
  rw [hdecomp] at hdvd
  exact int_core X (C / X / X) (C / X % X) (C % X) hX hH (Nat.mod_lt _ hXpos) hL hH1 hM1 hL1
    hdvd

/-- **Zero family.** `a(10^(2m) + 1) = 0` for every `m ≥ 1`
(`a(101) = a(10001) = a(1000001) = … = 0`). -/
theorem a_ten_pow_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) : a (10 ^ (2 * m) + 1) = 0 := by
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    exact a_101
  · apply a_eq_zero_of_forall
    intro C hC
    rw [IsWeave, numDigits_ten_pow_add_one] at hC
    exact not_dvd_of_weave_ten_pow_add_one m h2 C hC

/-- **The weakening "eventually nonzero" is also false.**  There is no `N`
with `a n ≠ 0` for all `n ≥ N`, by the family `n = 10^(2m) + 1`. -/
theorem not_eventually_ne_zero : ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n ≠ 0 := by
  rintro ⟨N, hN⟩
  have hle : N ≤ 10 ^ (2 * (N + 1)) + 1 := by
    have h1 : N < 10 ^ N := Nat.lt_pow_self (by norm_num)
    have h2 : 10 ^ N ≤ 10 ^ (2 * (N + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hN _ hle (a_ten_pow_two_mul_add_one (N + 1) (by omega))

end Candidates.A110735Refutation
