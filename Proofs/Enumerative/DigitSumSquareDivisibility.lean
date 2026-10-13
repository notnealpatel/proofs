import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Decimal digit sums and square divisibility

An explicit specialization of the polynomial `t_m` of Hare, Laishram and Stoll,
*Stolarsky's conjecture and the sum of digits of polynomial values*,
arXiv:1001.4169, §3, with `m = 3`. No novelty claim is intended.
-/

set_option autoImplicit false

namespace Enumerative.DigitSumSquareDivisibility

/-- Sum of the ordinary decimal digits, using Mathlib's least-significant-first digits. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

example : digitSum 37 = 10 := by decide
example : digitSum 0 = 0 := by decide

/-- Decimal digit sums add across two blocks when the lower block fits its allotted width. -/
theorem digitSum_add_block (k n m : ℕ) (hn : n < 10 ^ k) :
    digitSum (n + 10 ^ k * m) = digitSum n + digitSum m := by
  let L := Nat.digitsAppend 10 k n ++ Nat.digits 10 m
  have hlen : (Nat.digitsAppend 10 k n).length = k :=
    Nat.length_digitsAppend (by decide) k hn
  have hval : Nat.ofDigits 10 L = n + 10 ^ k * m := by
    change Nat.ofDigits 10 (Nat.digitsAppend 10 k n ++ Nat.digits 10 m) = _
    rw [Nat.ofDigits_append, hlen, Nat.ofDigits_digits]
    have hv : Nat.ofDigits 10 (Nat.digitsAppend 10 k n) = n := by
      unfold Nat.digitsAppend
      rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
    rw [hv]
  have hsmall : ∀ x ∈ L, x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Nat.lt_of_mem_digitsAppend (by decide) k x hx
    · exact Nat.digits_lt_base (by decide) hx
  have hs := Nat.sum_digits_ofDigits_eq_sum (by decide : 1 < 10)
    (l := L.length) (L := L) ⟨rfl, hsmall⟩
  rw [hval] at hs
  simpa [digitSum, L, Nat.digitsAppend] using hs

private theorem ofDigits_nines (k : ℕ) :
    Nat.ofDigits 10 (List.replicate k 9) + 1 = 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

/-- A block of `k` decimal nines has digit sum `9*k`, including the empty block at `k=0`. -/
theorem digitSum_pow_sub_one (k : ℕ) : digitSum (10 ^ k - 1) = 9 * k := by
  have hv := ofDigits_nines k
  have he : Nat.ofDigits 10 (List.replicate k 9) = 10 ^ k - 1 := by omega
  have hs := Nat.sum_digits_ofDigits_eq_sum (by decide : 1 < 10)
    (l := k) (L := List.replicate k 9)
    ⟨List.length_replicate .., by simp⟩
  rw [he] at hs
  simpa [digitSum, Nat.mul_comm] using hs

example : digitSum (10 ^ 2 - 1) = 18 := by decide
example : digitSum (3 + 10 ^ 2 * 37) = digitSum 3 + digitSum 37 :=
  digitSum_add_block 2 3 37 (by decide)

private theorem digitSum_ofDigits_blocks (k : ℕ) (L : List ℕ)
    (hL : ∀ a ∈ L, a < 10 ^ k) :
    digitSum (Nat.ofDigits (10 ^ k) L) = (L.map digitSum).sum := by
  induction L with
  | nil => simp [digitSum, Nat.ofDigits]
  | cons a L ih =>
    rw [Nat.ofDigits_cons, digitSum_add_block k a _ (hL a (by simp))]
    rw [ih (fun x hx => hL x (by simp [hx]))]
    simp

/-- The canonical nonnegative-block form of the HLS polynomial `t₃`. -/
def polynomial (B : ℕ) : ℕ :=
  3 * B ^ 4 + 2 * B ^ 3 + (B - 1) * B ^ 2 + 3 * B + 3

example : polynomial 100 = 302990303 := by decide
example : polynomial 1 = 11 := by decide

private theorem polynomial_blocks (B : ℕ) :
    polynomial B = Nat.ofDigits B [3, 3, B - 1, 2, 3] := by
  simp only [polynomial, Nat.ofDigits_cons, Nat.ofDigits_nil]
  ring

private theorem square_blocks (B : ℕ) (hB : 1 ≤ B) :
    polynomial B * polynomial B =
      Nat.ofDigits B [9, 18, 3, 12, 37, 12, 3, 18, 9] := by
  have hb : B - 1 + 1 = B := Nat.sub_add_cancel hB
  unfold polynomial
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]
  conv_lhs => rw [← hb]
  conv_rhs => rw [← hb]
  simp only [Nat.add_sub_cancel]
  ring

/-- The input polynomial has decimal digit sum `9*k+11` for every block width at least two. -/
theorem digitSum_polynomial (k : ℕ) (hk : 2 ≤ k) :
    digitSum (polynomial (10 ^ k)) = 9 * k + 11 := by
  have hB : 100 ≤ 10 ^ k := by
    calc
      100 = 10 ^ 2 := by decide
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hp : 0 < 10 ^ k := pow_pos (by decide) k
  rw [polynomial_blocks, digitSum_ofDigits_blocks]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [digitSum_pow_sub_one]
    have h2 : digitSum 2 = 2 := by decide
    have h3 : digitSum 3 = 3 := by decide
    rw [h2, h3]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The square has decimal digit sum 58; all its nine base-`10^k` coefficients are below the base. -/
theorem digitSum_polynomial_square (k : ℕ) (hk : 2 ≤ k) :
    digitSum (polynomial (10 ^ k) * polynomial (10 ^ k)) = 58 := by
  have hB : 100 ≤ 10 ^ k := by
    calc
      100 = 10 ^ 2 := by decide
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
  rw [square_blocks _ (by omega), digitSum_ofDigits_blocks]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

example : 2 ≤ (2 : ℕ) ∧ 0 < 10 ^ (2 : ℕ) := by decide

/-- Block width for the `r`th member; the parameter includes `r=0`. -/
def exponent (r : ℕ) : ℕ := 31 + 58 * r

/-- Decimal block base for the `r`th member. -/
def base (r : ℕ) : ℕ := 10 ^ exponent r

/-- The infinite family, in safe canonical nonnegative-block form. -/
def family (r : ℕ) : ℕ :=
  3 * base r ^ 4 + 2 * base r ^ 3 + (base r - 1) * base r ^ 2 + 3 * base r + 3

example : exponent 0 = 31 := rfl
example : exponent 1 = 89 := rfl
example : base 0 = 10 ^ 31 := rfl
example : family 0 = polynomial (10 ^ 31) := rfl

/-- Exact input digit sum for every natural family parameter. -/
theorem digitSum_family (r : ℕ) : digitSum (family r) = 58 * (5 + 9 * r) := by
  change digitSum (polynomial (10 ^ exponent r)) = _
  rw [digitSum_polynomial _ (by unfold exponent; omega)]
  unfold exponent
  ring

/-- Exact square digit sum for every natural family parameter. -/
theorem digitSum_family_square (r : ℕ) : digitSum (family r * family r) = 58 := by
  exact digitSum_polynomial_square (exponent r) (by unfold exponent; omega)

private theorem base_mod_ten (r : ℕ) : base r % 10 = 0 := by
  have hk : exponent r = (exponent r - 1) + 1 := by unfold exponent; omega
  unfold base
  rw [hk, pow_succ]
  simp

/-- Every family member ends in the decimal digit three. -/
theorem family_mod_ten (r : ℕ) : family r % 10 = 3 := by
  have hb := base_mod_ten r
  simp [family, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hb]

/-- No family member has a trailing decimal zero. -/
theorem ten_not_dvd_family (r : ℕ) : ¬ 10 ∣ family r := by
  intro hd
  have hzero := Nat.mod_eq_zero_of_dvd hd
  rw [family_mod_ten] at hzero
  omega

/-- Each square digit sum divides the corresponding input digit sum. -/
theorem digitSum_square_dvd (r : ℕ) : digitSum (family r * family r) ∣ digitSum (family r) := by
  rw [digitSum_family_square, digitSum_family]
  exact dvd_mul_right 58 (5 + 9 * r)

/-- Squaring strictly decreases the decimal digit sum throughout this family. -/
theorem digitSum_square_lt (r : ℕ) : digitSum (family r * family r) < digitSum (family r) := by
  rw [digitSum_family_square, digitSum_family]
  omega

/-- The family is strictly increasing, hence its members are pairwise distinct. -/
theorem family_strictMono : StrictMono family := by
  intro r s hrs
  have hk : exponent r < exponent s := by unfold exponent; omega
  have hb : base r < base s := Nat.pow_lt_pow_right (by decide) hk
  have hpos : 1 ≤ base r := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (10 : ℕ)) _)
  unfold family
  gcongr

/-- The family is injective on all natural parameters. -/
theorem family_injective : Function.Injective family := family_strictMono.injective

/-- The family is unbounded above in the natural numbers. -/
theorem family_unbounded (N : ℕ) : ∃ r : ℕ, N < family r := by
  refine ⟨N + 1, ?_⟩
  have hle : N + 1 ≤ family (N + 1) := family_strictMono.id_le (N + 1)
  omega

example : digitSum (family 0) = 290 ∧ digitSum (family 0 * family 0) = 58 ∧
    ¬ 10 ∣ family 0 ∧ digitSum (family 0 * family 0) ∣ digitSum (family 0) ∧
    digitSum (family 0 * family 0) < digitSum (family 0) := by
  exact ⟨digitSum_family 0, digitSum_family_square 0, ten_not_dvd_family 0,
    digitSum_square_dvd 0, digitSum_square_lt 0⟩

/-- Infinitely many integers without trailing zero have strict digit-sum decrease and divisibility. -/
theorem infinite_digitSum_square_divisibility :
    Set.Infinite {n : ℕ | ¬ 10 ∣ n ∧ digitSum (n * n) ∣ digitSum n ∧
      digitSum (n * n) < digitSum n} := by
  have hr : Set.Infinite (Set.range family) := Set.infinite_range_of_injective family_injective
  apply hr.mono
  rintro n ⟨r, rfl⟩
  exact ⟨ten_not_dvd_family r, digitSum_square_dvd r, digitSum_square_lt r⟩

end Enumerative.DigitSumSquareDivisibility
