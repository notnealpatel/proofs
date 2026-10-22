/-
# A394431 — the least digit-sum-maximizing base

Sean A. Irvine (OEIS A394431, Mar 25 2026) conjectured
`a(n) = ⌈(n+1)/2⌉` for `n > 8`, where `a(n)` is the smallest base
`1 < b < n` maximizing the base-`b` digit sum, with `a(1) = a(2) = 1`.
The bound is sharp: `a(8) = 3`, not 5.

## Proof outline

Write `s_b(n)` for the base-`b` digit sum and `q = n / b`, `r = n % b`.
* Bases `n/2 < b < n`: `n = 1·b + (n - b)`, so `s_b(n) = n - b + 1`, which is
  largest, equal to `n - ⌊n/2⌋ = ⌈n/2⌉`, at `b = ⌊n/2⌋ + 1`.
* Bases `2 ≤ b ≤ n/2`: `s_b(n) = r + s_b(q)`, and `2·s_b(n) < n`:
  for `b = 2` use `s_2(q) ≤ q % 2 + q / 2`; for `b ≥ 3, q ≥ 3` use
  `s_b(q) ≤ q` and `(b-2)(q-1) ≥ 2`; for `q = 2` use `s_b(2) = 2` and `b ≥ 4`.
Hence every base `b ≤ n/2` is strictly beaten and `a(n) = ⌊n/2⌋ + 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A394431SmallestBaseMaximizes

/-! ## Definitions -/

/-- The base-`b` digit sum `s_b(n)` of `n`, via Mathlib's `Nat.digits`. -/
def digitSum (b n : ℕ) : ℕ := (Nat.digits b n).sum

/-- `IsMaxBase n b`: `b` is a base with `1 < b < n` whose digit sum `s_b(n)` is
largest among all bases `c` with `1 < c < n`. -/
def IsMaxBase (n b : ℕ) : Prop :=
  1 < b ∧ b < n ∧ ∀ c < n, 1 < c → digitSum c n ≤ digitSum b n

instance (n : ℕ) : DecidablePred (IsMaxBase n) := fun b => by
  unfold IsMaxBase; infer_instance

/-- For `2 < n` some base `1 < b < n` maximizes the digit sum (finite range). -/
theorem exists_isMaxBase {n : ℕ} (hn : 2 < n) : ∃ b, IsMaxBase n b := by
  obtain ⟨b, hb, hmax⟩ := (Finset.Ioo 1 n).exists_max_image (fun c => digitSum c n)
    ⟨2, Finset.mem_Ioo.mpr ⟨by omega, hn⟩⟩
  rw [Finset.mem_Ioo] at hb
  exact ⟨b, hb.1, hb.2, fun c hc h1c => hmax c (Finset.mem_Ioo.mpr ⟨h1c, hc⟩)⟩

/-- **A394431.** `a(n)` is the smallest base `b` with `1 < b < n` maximizing the
base-`b` digit sum of `n`; by convention `a(1) = a(2) = 1` (and `a(0) = 1`, outside
the entry's offset). -/
def a (n : ℕ) : ℕ := if h : 2 < n then Nat.find (exists_isMaxBase h) else 1

/-- Characterization of `a(n)` for `2 < n`: it is a maximizing base and no
smaller base maximizes. -/
theorem a_eq_iff {n b : ℕ} (hn : 2 < n) :
    a n = b ↔ IsMaxBase n b ∧ ∀ c < b, ¬ IsMaxBase n c := by
  rw [a, dif_pos hn, Nat.find_eq_iff]

/-! ## Examples from the listed terms -/

example : a 1 = 1 := rfl
example : a 2 = 1 := rfl
example : a 3 = 2 := (a_eq_iff (by norm_num)).mpr (by decide)
example : a 5 = 3 := (a_eq_iff (by norm_num)).mpr (by decide)
example : a 7 = 4 := (a_eq_iff (by norm_num)).mpr (by decide)
example : a 8 = 3 := (a_eq_iff (by norm_num)).mpr (by decide)
example : a 9 = 5 := (a_eq_iff (by norm_num)).mpr (by decide)
example : a 12 = 7 := (a_eq_iff (by norm_num)).mpr (by decide)
example : a 20 = 11 := (a_eq_iff (by norm_num)).mpr (by decide)

/-- The hypothesis `8 < n` is sharp: `a(8) = 3 ≠ 5 = ⌊8/2⌋ + 1`. -/
theorem a_eight_ne : a 8 ≠ 8 / 2 + 1 := by
  rw [Ne, a_eq_iff (by norm_num)]
  decide


/-! ## Digit-sum lemmas -/

/-- One digit step: for `1 < b`, `s_b(n) = n % b + s_b(n / b)`. -/
theorem digitSum_eq_mod_add {b : ℕ} (hb : 1 < b) (n : ℕ) :
    digitSum b n = n % b + digitSum b (n / b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitSum]
  · simp only [digitSum, Nat.digits_def' hb hn, List.sum_cons]

/-- A one-digit number is its own digit sum. -/
theorem digitSum_of_lt {b m : ℕ} (hb : 1 < b) (hm : m < b) : digitSum b m = m := by
  rw [digitSum_eq_mod_add hb, Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm]
  simp [digitSum]

/-- Large bases: for `b ≤ n < 2b`, `n = 1·b + (n - b)` and `s_b(n) = n - b + 1`. -/
theorem digitSum_of_le_of_lt_two_mul {n b : ℕ} (hb : 1 < b) (hbn : b ≤ n)
    (hn : n < 2 * b) : digitSum b n = n - b + 1 := by
  have hq : n / b = 1 := by
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hr : n % b = n - b := by
    have hdm := Nat.div_add_mod n b
    rw [hq] at hdm
    omega
  rw [digitSum_eq_mod_add hb, hq, hr, digitSum_of_lt hb hb]

/-- The value at the conjectured base: `s_{⌊n/2⌋+1}(n) = n - ⌊n/2⌋ = ⌈n/2⌉`. -/
theorem digitSum_half_add_one {n : ℕ} (hn : 2 ≤ n) :
    digitSum (n / 2 + 1) n = n - n / 2 := by
  rw [digitSum_of_le_of_lt_two_mul (by omega) (by omega) (by omega)]
  omega

/-- **Load-bearing bound.** For `n > 8` and `2 ≤ b ≤ n/2`, `2·s_b(n) < n`. -/
theorem two_mul_digitSum_lt {n b : ℕ} (hn : 8 < n) (hb : 2 ≤ b) (hbn : b ≤ n / 2) :
    2 * digitSum b n < n := by
  have hb1 : 1 < b := hb
  have hdm : b * (n / b) + n % b = n := Nat.div_add_mod n b
  have hr : n % b < b := Nat.mod_lt n (by omega)
  have hq2 : 2 ≤ n / b := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hstep : digitSum b n = n % b + digitSum b (n / b) := digitSum_eq_mod_add hb1 n
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · -- base two: peel a second digit, `s_2(q) ≤ q % 2 + q / 2`
    have hb2 : b = 2 := by omega
    subst hb2
    have hq := Nat.div_add_mod (n / 2) 2
    have hstep2 : digitSum 2 (n / 2) = n / 2 % 2 + digitSum 2 (n / 2 / 2) :=
      digitSum_eq_mod_add hb1 (n / 2)
    have hle : digitSum 2 (n / 2 / 2) ≤ n / 2 / 2 := Nat.digit_sum_le 2 _
    omega
  · rcases Nat.lt_or_ge (n / b) 3 with hq3 | hq3
    · -- two leading digits `[r, 2]`
      have hq : n / b = 2 := by omega
      have h2 : digitSum b 2 = 2 := digitSum_of_lt hb1 (by omega)
      rw [hq] at hdm hstep
      omega
    · -- `s_b(q) ≤ q` and `(b - 2)(q - 1) ≥ 2`
      have hle : digitSum b (n / b) ≤ n / b := Nat.digit_sum_le b _
      have hprod : 3 * b + 3 * (n / b) ≤ b * (n / b) + 9 := by nlinarith
      omega

/-- Every base `1 < b < n` gives `s_b(n) ≤ ⌈n/2⌉ = n - ⌊n/2⌋` (for `n > 8`). -/
theorem digitSum_le_sub_half {n b : ℕ} (hn : 8 < n) (hb : 1 < b) (hbn : b < n) :
    digitSum b n ≤ n - n / 2 := by
  rcases Nat.lt_or_ge (n / 2) b with hlt | hge
  · rw [digitSum_of_le_of_lt_two_mul hb hbn.le (by omega)]
    omega
  · have htwo := two_mul_digitSum_lt hn hb hge
    omega

/-- Every base `1 < b ≤ n/2` gives `s_b(n) < ⌈n/2⌉ = n - ⌊n/2⌋` (for `n > 8`). -/
theorem digitSum_lt_sub_half {n b : ℕ} (hn : 8 < n) (hb : 1 < b) (hbn : b ≤ n / 2) :
    digitSum b n < n - n / 2 := by
  have htwo := two_mul_digitSum_lt hn hb hbn
  omega

/-! ## The conjecture -/

/-- **Irvine's conjecture, digit-sum form (A394431).**  For every `n > 8`:
the base `⌊n/2⌋ + 1` lies in `(1, n)`, attains `s_{⌊n/2⌋+1}(n) = ⌈n/2⌉ = n - ⌊n/2⌋`,
no base `1 < b < n` exceeds it, and every base `1 < b ≤ n/2` is strictly below it. -/
theorem digitSum_max_at_half_add_one (n : ℕ) (hn : 8 < n) :
    1 < n / 2 + 1 ∧ n / 2 + 1 < n ∧ digitSum (n / 2 + 1) n = n - n / 2 ∧
      (∀ b, 1 < b → b < n → digitSum b n ≤ digitSum (n / 2 + 1) n) ∧
      (∀ b, 1 < b → b ≤ n / 2 → digitSum b n < digitSum (n / 2 + 1) n) := by
  have hval := digitSum_half_add_one (n := n) (by omega)
  refine ⟨by omega, by omega, hval, fun b hb hbn => ?_, fun b hb hbn => ?_⟩
  · rw [hval]
    exact digitSum_le_sub_half hn hb hbn
  · rw [hval]
    exact digitSum_lt_sub_half hn hb hbn

/-- **Irvine's conjecture (A394431, Sean A. Irvine, Mar 25 2026), natural-number form.**

The identity `a(n) = ⌊n/2⌋ + 1` holds for every `n > 8`; see `a_eq_ceil` for the ceiling form. -/
theorem a_eq_half_add_one (n : ℕ) (hn : 8 < n) : a n = n / 2 + 1 := by
  obtain ⟨h1, hlt, -, hle, hstrict⟩ := digitSum_max_at_half_add_one n hn
  rw [a_eq_iff (by omega)]
  refine ⟨⟨h1, hlt, fun c hc h1c => hle c h1c hc⟩, fun c hc hmax => ?_⟩
  have hgt := hstrict c hmax.1 (by omega)
  have hge := hmax.2.2 (n / 2 + 1) hlt h1
  omega

/-- `⌊n/2⌋ + 1 = ⌈(n+1)/2⌉` for every natural `n`. -/
theorem half_add_one_eq_ceil (n : ℕ) :
    ((n / 2 + 1 : ℕ) : ℤ) = ⌈((n : ℚ) + 1) / 2⌉ := by
  rw [eq_comm, Int.ceil_eq_iff]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : (k + k) / 2 = k := by omega
    rw [hk]
    push_cast
    constructor <;> linarith
  · have hk : (2 * k + 1) / 2 = k := by omega
    rw [hk]
    push_cast
    constructor <;> linarith

/-- **Irvine's conjecture (A394431, Sean A. Irvine, Mar 25 2026), ceiling form.**

For every natural `n > 8`, the smallest base `1 < b < n` maximizing the base-`b` digit sum of `n` equals
`⌈(n+1)/2⌉`. -/
theorem a_eq_ceil (n : ℕ) (hn : 8 < n) : (a n : ℤ) = ⌈((n : ℚ) + 1) / 2⌉ := by
  rw [a_eq_half_add_one n hn, half_add_one_eq_ceil]

end Candidates.A394431SmallestBaseMaximizes
