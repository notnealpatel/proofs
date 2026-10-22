/-
# A277216 — the product of the decimal digits of `σ(n)` equals `n` only for `n = 1, 210`

Jaroslav Krizek's conjecture in OEIS A277216 asserts that the product of
the decimal digits of `σ(n)` equals positive `n` only at `1` and `210`.
At `210`, `σ(210) = 576` and `5·7·6 = 210`.

Let `P(m)` be the product of the decimal digits of `m` and suppose `P(σ n) = n` with `0 < n`.

1. Every digit is `< 10` and `P(σ n) = n ≠ 0`, so `n = 2^a 3^b 5^c 7^d`.
2. Multiplicativity of `σ` gives `σ n = g₂(a) g₃(b) g₅(c) g₇(d)` with `g_p(k) = ∑_{j ≤ k} p^j`,
   and `(p - 1) g_p(k) < p^(k+1)` gives `8 σ n < 35 n`.
3. With `ℓ` decimal digits, `10^ℓ P(m) 9 ≤ 9^ℓ m 10` (the leading digit dominates), so
   `72 · 10^ℓ < 350 · 9^ℓ`, hence `ℓ ≤ 15` and `n = P(σ n) ≤ 9^ℓ ≤ 9^15`.
4. A kernel `decide` (no `native_decide`) over the 28075 seven-smooth `n ≤ 9^15`, split by
   the exponent of `2` into 48 checks, finds only `n = 1` and `n = 210`.
-/
import Mathlib

set_option autoImplicit false
-- The 48 kernel checks below are elaborated sequentially to bound peak memory.
set_option Elab.async false

namespace Candidates.A277216ProductDecimalDigits

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Definitions -/

/-- A277216: the product of the decimal digits of `σ(n)` (`A007954 ∘ A000203`).
`Nat.digits 10 m` lists the digits little-endian; `(Nat.digits 10 0).prod = 1`. -/
def a277216 (n : ℕ) : ℕ := (Nat.digits 10 (σ 1 n)).prod

/-- Examples against the first listed terms `1,3,4,7,6,2,8,5,3,8,2,16`. -/
example : (List.range 12).map (fun i => a277216 (i + 1)) = [1, 3, 4, 7, 6, 2, 8, 5, 3, 8, 2, 16] := by
  decide

/-! ## Computable helpers -/

/-- `geo p k = 1 + p + ⋯ + p ^ k`, by the Horner recursion `geo p (k + 1) = p * geo p k + 1`. -/
def geo (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => p * geo p k + 1

/-- Fuelled decimal digit product: `dprod f m` multiplies the last `f` decimal digits of `m`,
stopping at `m = 0`; it equals `(Nat.digits 10 m).prod` once `m < 10 ^ f` (`dprod_eq`). -/
def dprod : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f + 1, m => if m = 0 then 1 else (m % 10) * dprod f (m / 10)

/-- `scan p B g fuel j x` checks `g (j + k) (x * p ^ k)` for `k = 0, 1, …` while
`x * p ^ k ≤ B` and `k < fuel` (soundness: `scan_sound`). -/
def scan (p B : ℕ) (g : ℕ → ℕ → Bool) (fuel : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih k x => if x ≤ B then g k x && ih (k + 1) (x * p) else true) fuel

/-- The leaf test for `n = 2^a 3^b 5^c 7^d`: either the digit product of
`σ n = geo 2 a * geo 3 b * geo 5 c * geo 7 d` differs from `n`, or `n ∈ {1, 210}`. -/
def leaf (a b c d n : ℕ) : Bool :=
  dprod 20 (geo 2 a * geo 3 b * geo 5 c * geo 7 d) != n || n == 1 || n == 210

/-- The leaf test over all `n = 2^a 3^b 5^c 7^d ≤ 9 ^ 15` with fixed exponent `a`. -/
def checkA (a : ℕ) : Bool :=
  scan 3 (9 ^ 15) (fun b y => scan 5 (9 ^ 15) (fun c z =>
    scan 7 (9 ^ 15) (fun d w => leaf a b c d w) 48 0 z) 48 0 y) 48 0 (2 ^ a)

/-- `geo` agrees with `leaf`'s intended meaning on `n = 210`: `σ 210 = 576` digitwise. -/
example : leaf 1 1 1 1 210 = true := by decide

/-! ## Bridge lemmas -/

/-- `geo p k = ∑_{j ≤ k} p ^ j`. -/
theorem geo_eq_sum (p k : ℕ) : geo p k = ∑ j ∈ Finset.range (k + 1), p ^ j := by
  induction k with
  | zero => simp [geo]
  | succ k ih =>
    rw [geo, ih, Finset.mul_sum, Finset.sum_range_succ' (fun j => p ^ j) (k + 1)]
    simp only [pow_succ', pow_zero]

/-- The geometric-sum identity `q · geo (q + 1) k + 1 = (q + 1) ^ (k + 1)`. -/
theorem geo_mul_add_one (q k : ℕ) : q * geo (q + 1) k + 1 = (q + 1) ^ (k + 1) := by
  induction k with
  | zero => simp [geo]
  | succ k ih =>
    rw [geo, pow_succ, ← ih]
    ring

/-- `σ(p ^ k) = geo p k` for a prime `p`. -/
theorem sigma_prime_pow (p k : ℕ) (hp : p.Prime) : σ 1 (p ^ k) = geo p k := by
  rw [sigma_apply_prime_pow hp, geo_eq_sum]
  simp

/-- Multiplicativity: `σ(2^a 3^b 5^c 7^d) = geo 2 a · geo 3 b · geo 5 c · geo 7 d`. -/
theorem sigma_smooth (a b c d : ℕ) :
    σ 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) = geo 2 a * geo 3 b * geo 5 c * geo 7 d := by
  have hm := (isMultiplicative_sigma (k := 1))
  have h23 : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  have h235 : Nat.Coprime (2 ^ a * 3 ^ b) (5 ^ c) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow a c (by norm_num)) (Nat.Coprime.pow b c (by norm_num))
  have h2357 : Nat.Coprime (2 ^ a * 3 ^ b * 5 ^ c) (7 ^ d) :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.pow a d (by norm_num))
      (Nat.Coprime.pow b d (by norm_num))) (Nat.Coprime.pow c d (by norm_num))
  rw [hm.map_mul_of_coprime h2357, hm.map_mul_of_coprime h235, hm.map_mul_of_coprime h23,
    sigma_prime_pow 2 a Nat.prime_two, sigma_prime_pow 3 b Nat.prime_three,
    sigma_prime_pow 5 c Nat.prime_five, sigma_prime_pow 7 d (by norm_num)]

/-- Abundancy bound for seven-smooth numbers: `σ(n)/n < 2 · 3/2 · 5/4 · 7/6 = 35/8`. -/
theorem sigma_smooth_lt (a b c d : ℕ) :
    8 * σ 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) < 35 * (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) := by
  rw [sigma_smooth]
  have h2 := geo_mul_add_one 1 a
  have h3 := geo_mul_add_one 2 b
  have h5 := geo_mul_add_one 4 c
  have h7 := geo_mul_add_one 6 d
  norm_num [pow_succ] at h2 h3 h5 h7
  have e2 : geo 2 a < 2 * 2 ^ a := by omega
  have e3 : 2 * geo 3 b < 3 * 3 ^ b := by omega
  have e5 : 4 * geo 5 c < 5 * 5 ^ c := by omega
  have e7 : 6 * geo 7 d < 7 * 7 ^ d := by omega
  have key : 48 * (geo 2 a * geo 3 b * geo 5 c * geo 7 d) <
      210 * (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) := by
    calc 48 * (geo 2 a * geo 3 b * geo 5 c * geo 7 d)
        = geo 2 a * (2 * geo 3 b) * (4 * geo 5 c) * (6 * geo 7 d) := by ring
      _ < (2 * 2 ^ a) * (3 * 3 ^ b) * (5 * 5 ^ c) * (7 * 7 ^ d) := by
        gcongr
      _ = 210 * (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) := by ring
  omega


/-- Every nonzero decimal digit is of the form `2^a 3^b 5^c 7^d`. -/
theorem smooth_of_lt_ten (x : ℕ) (hx : x < 10) (h0 : x ≠ 0) :
    ∃ a b c d : ℕ, x = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  interval_cases x
  · exact absurd rfl h0
  · exact ⟨0, 0, 0, 0, rfl⟩
  · exact ⟨1, 0, 0, 0, rfl⟩
  · exact ⟨0, 1, 0, 0, rfl⟩
  · exact ⟨2, 0, 0, 0, rfl⟩
  · exact ⟨0, 0, 1, 0, rfl⟩
  · exact ⟨1, 1, 0, 0, rfl⟩
  · exact ⟨0, 0, 0, 1, rfl⟩
  · exact ⟨3, 0, 0, 0, rfl⟩
  · exact ⟨0, 2, 0, 0, rfl⟩

/-- A nonzero product of decimal digits is seven-smooth. -/
theorem smooth_of_prod (L : List ℕ) (hL : ∀ x ∈ L, x < 10) (h0 : L.prod ≠ 0) :
    ∃ a b c d : ℕ, L.prod = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  induction L with
  | nil => exact ⟨0, 0, 0, 0, rfl⟩
  | cons x L ih =>
    rw [List.prod_cons] at h0 ⊢
    obtain ⟨a₁, b₁, c₁, d₁, hx⟩ :=
      smooth_of_lt_ten x (hL x List.mem_cons_self) (left_ne_zero_of_mul h0)
    obtain ⟨a₂, b₂, c₂, d₂, hp⟩ :=
      ih (fun y hy => hL y (List.mem_cons_of_mem x hy)) (right_ne_zero_of_mul h0)
    refine ⟨a₁ + a₂, b₁ + b₂, c₁ + c₂, d₁ + d₂, ?_⟩
    rw [hx, hp]
    ring

/-- The decimal digit product of `m` is at most `9 ^ ℓ` with `ℓ` the number of digits. -/
theorem prod_digits_le (m : ℕ) : (Nat.digits 10 m).prod ≤ 9 ^ (Nat.digits 10 m).length := by
  have key : ∀ L : List ℕ, (∀ x ∈ L, x < 10) → L.prod ≤ 9 ^ L.length := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      intro hL
      rw [List.prod_cons, List.length_cons, pow_succ']
      have hx : x ≤ 9 := Nat.lt_succ_iff.mp (hL x List.mem_cons_self)
      exact Nat.mul_le_mul hx (ih fun y hy => hL y (List.mem_cons_of_mem x hy))
  exact key _ fun x hx => Nat.digits_lt_base (by norm_num) hx

/-- Leading-digit bound: for `0 < m` with `ℓ` digits, `10^ℓ · P(m) · 9 ≤ 9^ℓ · m · 10`. -/
theorem digits_bound (m : ℕ) (hm : 0 < m) :
    10 ^ (Nat.digits 10 m).length * (Nat.digits 10 m).prod * 9 ≤
      9 ^ (Nat.digits 10 m).length * m * 10 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [Nat.digits_def' (by norm_num) hm, List.length_cons, List.prod_cons]
    have hr : m % 10 < 10 := Nat.mod_lt m (by norm_num)
    have hdiv : m = 10 * (m / 10) + m % 10 := (Nat.div_add_mod m 10).symm
    rcases Nat.eq_zero_or_pos (m / 10) with hq | hq
    · rw [hq, Nat.digits_zero]
      simp only [List.length_nil, List.prod_nil]
      omega
    · have ihq := ih (m / 10) (Nat.div_lt_self hm (by norm_num)) hq
      set q := m / 10 with hqdef
      set r := m % 10 with hrdef
      set ℓ := (Nat.digits 10 q).length
      set P := (Nat.digits 10 q).prod
      have hr9 : r ≤ 9 := by omega
      calc 10 ^ (ℓ + 1) * (r * P) * 9 = 10 * r * (10 ^ ℓ * P * 9) := by ring
        _ ≤ 10 * r * (9 ^ ℓ * q * 10) := Nat.mul_le_mul_left _ ihq
        _ = 9 ^ ℓ * (100 * r * q) := by ring
        _ ≤ 9 ^ ℓ * (9 * (10 * q + r) * 10) := by
          apply Nat.mul_le_mul_left
          nlinarith
        _ = 9 ^ (ℓ + 1) * m * 10 := by rw [hdiv]; ring

/-- `72 · 10^k < 350 · 9^k` forces `k ≤ 15`. -/
theorem length_le_fifteen (k : ℕ) (hk : 72 * 10 ^ k < 350 * 9 ^ k) : k ≤ 15 := by
  by_contra hlt
  rw [not_le] at hlt
  have key : ∀ j, 16 ≤ j → 350 * 9 ^ j ≤ 72 * 10 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j _ ihj =>
      rw [pow_succ, pow_succ]
      linarith [Nat.zero_le (10 ^ j)]
  exact absurd hk (not_lt.mpr (key k hlt))

/-- The fuelled digit product agrees with `(Nat.digits 10 m).prod` once `m < 10 ^ f`. -/
theorem dprod_eq (f m : ℕ) (hm : m < 10 ^ f) : dprod f m = (Nat.digits 10 m).prod := by
  induction f generalizing m with
  | zero =>
    have h0 : m = 0 := by simpa using hm
    simp [dprod, h0]
  | succ f ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · simp [dprod, h0]
    · rw [dprod, if_neg hpos.ne', Nat.digits_def' (by norm_num) hpos, List.prod_cons,
        ih (m / 10) (by rw [pow_succ] at hm; omega)]

/-- Soundness of `scan`: every visited point `x * p ^ k ≤ B` with `k < fuel` passes `g`. -/
theorem scan_sound (p B : ℕ) (hp : 1 ≤ p) (g : ℕ → ℕ → Bool) (fuel j x : ℕ)
    (h : scan p B g fuel j x = true) (k : ℕ) (hk : k < fuel) (hB : x * p ^ k ≤ B) :
    g (j + k) (x * p ^ k) = true := by
  induction fuel generalizing j x k with
  | zero => omega
  | succ fuel ih =>
    have hx : x ≤ B := le_trans (Nat.le_mul_of_pos_right x (Nat.pow_pos (n := k) hp)) hB
    have h' : (if x ≤ B then g j x && scan p B g fuel (j + 1) (x * p) else true) = true := h
    rw [if_pos hx, Bool.and_eq_true] at h'
    rcases k with _ | k
    · simpa using h'.1
    · have := ih (j + 1) (x * p) h'.2 k (by omega) (by rw [mul_assoc, ← pow_succ']; exact hB)
      rw [show j + (k + 1) = j + 1 + k by ring, show x * p ^ (k + 1) = x * p * p ^ k by ring]
      exact this


/-! ## The finite check -/

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 0. -/
theorem checkA_0 : checkA 0 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 1. -/
theorem checkA_1 : checkA 1 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 2. -/
theorem checkA_2 : checkA 2 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 3. -/
theorem checkA_3 : checkA 3 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 4. -/
theorem checkA_4 : checkA 4 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 5. -/
theorem checkA_5 : checkA 5 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 6. -/
theorem checkA_6 : checkA 6 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 7. -/
theorem checkA_7 : checkA 7 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 8. -/
theorem checkA_8 : checkA 8 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 9. -/
theorem checkA_9 : checkA 9 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 10. -/
theorem checkA_10 : checkA 10 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 11. -/
theorem checkA_11 : checkA 11 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 12. -/
theorem checkA_12 : checkA 12 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 13. -/
theorem checkA_13 : checkA 13 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 14. -/
theorem checkA_14 : checkA 14 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 15. -/
theorem checkA_15 : checkA 15 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 16. -/
theorem checkA_16 : checkA 16 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 17. -/
theorem checkA_17 : checkA 17 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 18. -/
theorem checkA_18 : checkA 18 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 19. -/
theorem checkA_19 : checkA 19 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 20. -/
theorem checkA_20 : checkA 20 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 21. -/
theorem checkA_21 : checkA 21 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 22. -/
theorem checkA_22 : checkA 22 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 23. -/
theorem checkA_23 : checkA 23 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 24. -/
theorem checkA_24 : checkA 24 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 25. -/
theorem checkA_25 : checkA 25 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 26. -/
theorem checkA_26 : checkA 26 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 27. -/
theorem checkA_27 : checkA 27 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 28. -/
theorem checkA_28 : checkA 28 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 29. -/
theorem checkA_29 : checkA 29 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 30. -/
theorem checkA_30 : checkA 30 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 31. -/
theorem checkA_31 : checkA 31 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 32. -/
theorem checkA_32 : checkA 32 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 33. -/
theorem checkA_33 : checkA 33 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 34. -/
theorem checkA_34 : checkA 34 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 35. -/
theorem checkA_35 : checkA 35 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 36. -/
theorem checkA_36 : checkA 36 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 37. -/
theorem checkA_37 : checkA 37 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 38. -/
theorem checkA_38 : checkA 38 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 39. -/
theorem checkA_39 : checkA 39 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 40. -/
theorem checkA_40 : checkA 40 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 41. -/
theorem checkA_41 : checkA 41 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 42. -/
theorem checkA_42 : checkA 42 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 43. -/
theorem checkA_43 : checkA 43 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 44. -/
theorem checkA_44 : checkA 44 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 45. -/
theorem checkA_45 : checkA 45 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 46. -/
theorem checkA_46 : checkA 46 = true := by decide +kernel

/-- Kernel check of the seven-smooth `n ≤ 9 ^ 15` with `2`-adic valuation 47. -/
theorem checkA_47 : checkA 47 = true := by decide +kernel

/-- All 48 exponent-of-two slices pass. -/
theorem checkA_true (a : ℕ) (ha : a < 48) : checkA a = true := by
  interval_cases a
  exacts [checkA_0, checkA_1, checkA_2, checkA_3, checkA_4, checkA_5, checkA_6, checkA_7, checkA_8, checkA_9, checkA_10, checkA_11, checkA_12, checkA_13, checkA_14, checkA_15, checkA_16, checkA_17, checkA_18, checkA_19, checkA_20, checkA_21, checkA_22, checkA_23, checkA_24, checkA_25, checkA_26, checkA_27, checkA_28, checkA_29, checkA_30, checkA_31, checkA_32, checkA_33, checkA_34, checkA_35, checkA_36, checkA_37, checkA_38, checkA_39, checkA_40, checkA_41, checkA_42, checkA_43, checkA_44, checkA_45, checkA_46, checkA_47]

/-! ## Assembly -/

/-- `geo p k` is positive. -/
theorem geo_pos (p k : ℕ) : 0 < geo p k := by
  cases k <;> simp [geo]

/-- An exponent `k` with `p ^ k ≤ 9 ^ 15` and `2 ≤ p` satisfies `k < 48`. -/
theorem exp_lt_48 (p k : ℕ) (hp : 2 ≤ p) (h : p ^ k ≤ 9 ^ 15) : k < 48 := by
  by_contra hk
  rw [not_lt] at hk
  have h1 : 2 ^ 48 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp k
  have h3 : (9 : ℕ) ^ 15 < 2 ^ 48 := by norm_num
  omega

/-- **Reduction.** If `0 < n` and the digit product of `σ n` is `n`, then `n` is
seven-smooth and `n ≤ 9 ^ 15`. -/
theorem smooth_and_bound (n : ℕ) (hn : 0 < n) (h : (Nat.digits 10 (σ 1 n)).prod = n) :
    ∃ a b c d : ℕ, n = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d ∧ n ≤ 9 ^ 15 := by
  obtain ⟨a, b, c, d, hsm⟩ := smooth_of_prod (Nat.digits 10 (σ 1 n))
    (fun x hx => Nat.digits_lt_base (by norm_num) hx) (by rw [h]; exact hn.ne')
  rw [h] at hsm
  refine ⟨a, b, c, d, hsm, ?_⟩
  set m := σ 1 n with hmdef
  have hσ : 8 * m < 35 * n := by rw [hmdef, hsm]; exact sigma_smooth_lt a b c d
  have hmpos : 0 < m := by
    rw [hmdef, hsm, sigma_smooth]
    have := geo_pos 2 a; have := geo_pos 3 b; have := geo_pos 5 c; have := geo_pos 7 d
    positivity
  set ℓ := (Nat.digits 10 m).length
  have h1 : 10 ^ ℓ * n * 9 ≤ 9 ^ ℓ * m * 10 := by
    have := digits_bound m hmpos
    rwa [h] at this
  have h3 : 72 * 10 ^ ℓ * n < 350 * 9 ^ ℓ * n := by
    calc 72 * 10 ^ ℓ * n = 8 * (10 ^ ℓ * n * 9) := by ring
      _ ≤ 8 * (9 ^ ℓ * m * 10) := Nat.mul_le_mul_left 8 h1
      _ = 10 * 9 ^ ℓ * (8 * m) := by ring
      _ < 10 * 9 ^ ℓ * (35 * n) := Nat.mul_lt_mul_of_pos_left hσ (by positivity)
      _ = 350 * 9 ^ ℓ * n := by ring
  have hℓ : ℓ ≤ 15 := length_le_fifteen ℓ (Nat.lt_of_mul_lt_mul_right h3)
  calc n = (Nat.digits 10 m).prod := h.symm
    _ ≤ 9 ^ ℓ := prod_digits_le m
    _ ≤ 9 ^ 15 := Nat.pow_le_pow_right (by norm_num) hℓ

/-- `n = 210` is a solution: `σ 210 = 576` and `5 · 7 · 6 = 210`. -/
theorem a277216_210 : a277216 210 = 210 := by
  have hσ : σ 1 210 = 576 := by
    have := sigma_smooth 1 1 1 1
    norm_num [geo] at this
    exact this
  rw [a277216, hσ]
  norm_num

/-- `n = 1` is a solution: `σ 1 = 1`. -/
theorem a277216_one : a277216 1 = 1 := by
  simp [a277216]

/-- **A277216 conjecture (Jaroslav Krizek), proved.**

"Conjecture: a(n) = n only for numbers 1 and 210; sigma(210) = 576;
a(210) = 5*7*6 = 210."  For a positive integer `n`, the product of the decimal digits of
`σ(n)` equals `n` if and only if `n = 1` or `n = 210`.  The `0 < n` guard is the entry's
offset (`n ≥ 1`); at `n = 0`, `σ 0 = 0` and the empty digit product is `1 ≠ 0`. -/
theorem a277216_conjecture (n : ℕ) (hn : 0 < n) : a277216 n = n ↔ n = 1 ∨ n = 210 := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, hsm, hB⟩ := smooth_and_bound n hn h
    have hdvd : ∀ x : ℕ, x ∣ n → x ≤ 9 ^ 15 := fun x hx => (Nat.le_of_dvd hn hx).trans hB
    have h2 : 2 ^ a ≤ 9 ^ 15 := hdvd _ ⟨3 ^ b * 5 ^ c * 7 ^ d, by rw [hsm]; ring⟩
    have h23 : 2 ^ a * 3 ^ b ≤ 9 ^ 15 := hdvd _ ⟨5 ^ c * 7 ^ d, by rw [hsm]; ring⟩
    have h235 : 2 ^ a * 3 ^ b * 5 ^ c ≤ 9 ^ 15 := hdvd _ ⟨7 ^ d, hsm⟩
    have h3 : 3 ^ b ≤ 9 ^ 15 := hdvd _ ⟨2 ^ a * 5 ^ c * 7 ^ d, by rw [hsm]; ring⟩
    have h5 : 5 ^ c ≤ 9 ^ 15 := hdvd _ ⟨2 ^ a * 3 ^ b * 7 ^ d, by rw [hsm]; ring⟩
    have h7 : 7 ^ d ≤ 9 ^ 15 := hdvd _ ⟨2 ^ a * 3 ^ b * 5 ^ c, by rw [hsm]; ring⟩
    have hA := checkA_true a (exp_lt_48 2 a le_rfl h2)
    have hb := scan_sound 3 (9 ^ 15) (by norm_num) _ 48 0 (2 ^ a) hA b
      (exp_lt_48 3 b (by norm_num) h3) h23
    have hc := scan_sound 5 (9 ^ 15) (by norm_num) _ 48 0 (2 ^ a * 3 ^ b) hb c
      (exp_lt_48 5 c (by norm_num) h5) h235
    have hd := scan_sound 7 (9 ^ 15) (by norm_num) _ 48 0 (2 ^ a * 3 ^ b * 5 ^ c) hc d
      (exp_lt_48 7 d (by norm_num) h7) (by rw [← hsm]; exact hB)
    rw [← hsm, zero_add] at hd
    have hσlt : σ 1 n < 10 ^ 20 := by
      have := sigma_smooth_lt a b c d
      rw [← hsm] at this
      omega
    have hdp : dprod 20 (geo 2 a * geo 3 b * geo 5 c * geo 7 d) = n := by
      rw [← sigma_smooth, ← hsm, dprod_eq 20 _ hσlt]
      exact h
    simpa [leaf, hdp] using hd
  · rintro (rfl | rfl)
    · exact a277216_one
    · exact a277216_210

end Candidates.A277216ProductDecimalDigits
