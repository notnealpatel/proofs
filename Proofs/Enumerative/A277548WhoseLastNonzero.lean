/-
# Last nonzero base-5 digits (A277548)

Source: David A. Corneth's OEIS A277548 formula (Oct 23 2016), with A033042.
For every positive `n`, the nth positive integer with last nonzero base-5
digit 4 equals `4n` iff all base-5 digits of `n` are at most 1, equivalently
`n` is a sum of distinct powers of 5. The sequence is indexed from 1.
A recursive counting identity measures the deficit by a sum of digit penalties.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A277548WhoseLastNonzero

/-! ## Definitions -/

/-- Membership in A277548, mirroring the entry's NAME: `k` is a positive
integer and `k / 5^m ≡ 4 (mod 5)`, where `5^m` is the greatest power of `5`
dividing `k` (`m = padicValNat 5 k`). -/
def InSeq (k : ℕ) : Prop := 0 < k ∧ k / 5 ^ padicValNat 5 k % 5 = 4

/-- If `5 ∤ k`, then `k` is in A277548 iff `k ≡ 4 (mod 5)`. -/
theorem inSeq_iff_of_mod_ne {k : ℕ} (h : k % 5 ≠ 0) : InSeq k ↔ k % 5 = 4 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have hv : padicValNat 5 k = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  simp [InSeq, hv, hk]

/-- Multiplying by `5` does not change membership in A277548. -/
theorem inSeq_five_mul (k : ℕ) : InSeq (5 * k) ↔ InSeq k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [InSeq]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hv : padicValNat 5 (5 * k) = padicValNat 5 k + 1 := by
    rw [padicValNat.mul (by norm_num) hk.ne', padicValNat_self]; ring
  have hdiv : 5 * k / 5 ^ (padicValNat 5 k + 1) = k / 5 ^ padicValNat 5 k := by
    rw [pow_succ, mul_comm (5 ^ _) 5, Nat.mul_div_mul_left _ _ (by norm_num)]
  simp only [InSeq, hv, hdiv]
  constructor
  · rintro ⟨-, h⟩; exact ⟨hk, h⟩
  · rintro ⟨-, h⟩; exact ⟨by omega, h⟩

/-- Fuel-bounded structural computation of the last nonzero base-5 digit of
`k` (it returns `0` for `k = 0`); correct whenever the fuel is at least `k`.
Used only to make `InSeq` decidable by kernel reduction. -/
def lnzFuel : ℕ → ℕ → ℕ
  | 0, k => k % 5
  | f + 1, k => if k % 5 = 0 then lnzFuel f (k / 5) else k % 5

/-- With fuel `f ≥ k`, membership in A277548 is "`k > 0` and the last nonzero
base-5 digit of `k` is `4`". -/
theorem inSeq_iff_lnzFuel (f k : ℕ) (hf : k ≤ f) :
    InSeq k ↔ 0 < k ∧ lnzFuel f k = 4 := by
  induction f generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp [InSeq]
  | succ f ih =>
    by_cases h : k % 5 = 0
    · obtain ⟨q, rfl⟩ : ∃ q, k = 5 * q := ⟨k / 5, by omega⟩
      have hq : 5 * q / 5 = q := by omega
      rw [inSeq_five_mul, ih q (by omega)]
      simp only [lnzFuel, h, if_true, hq]
      constructor
      · rintro ⟨hpos, h4⟩; exact ⟨by omega, h4⟩
      · rintro ⟨hpos, h4⟩; exact ⟨by omega, h4⟩
    · rw [inSeq_iff_of_mod_ne h]
      simp only [lnzFuel, h, if_false]
      constructor
      · intro h4; exact ⟨by omega, h4⟩
      · rintro ⟨-, h4⟩; exact h4

/-- Kernel-reducible decision procedure for membership in A277548. -/
instance : DecidablePred InSeq := fun k =>
  decidable_of_iff (0 < k ∧ lnzFuel k k = 4) (inSeq_iff_lnzFuel k k le_rfl).symm

/-- The sequence A277548, 1-indexed as in the entry: `a n` is the `n`-th
member (`n ≥ 1`); `Nat.nth` is 0-indexed. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InSeq (n - 1)

/-! ### Examples -/

/-- The members below `230` are exactly the listed terms of the entry. -/
example : (List.range 230).filter (fun k => decide (InSeq k)) =
    [4, 9, 14, 19, 20, 24, 29, 34, 39, 44, 45, 49, 54, 59, 64, 69, 70, 74, 79,
      84, 89, 94, 95, 99, 100, 104, 109, 114, 119, 120, 124, 129, 134, 139, 144,
      145, 149, 154, 159, 164, 169, 170, 174, 179, 184, 189, 194, 195, 199, 204,
      209, 214, 219, 220, 224, 225, 229] := by decide

example : lnzFuel 100 100 = 4 := by decide
example : lnzFuel 70 70 = 4 := by decide
example : lnzFuel 75 75 = 3 := by decide

/-- `a 1 = 4`. -/
example : a 1 = 4 := by
  have hcount : Nat.count InSeq 4 = 0 := by decide
  rw [a, Nat.sub_self, ← hcount]
  exact Nat.nth_count (by decide)

/-- `a 5 = 20`. -/
example : a 5 = 20 := by
  have hcount : Nat.count InSeq 20 = 4 := by decide
  show Nat.nth InSeq 4 = 20
  rw [← hcount]
  exact Nat.nth_count (by decide)

/-- `a 2 = 9`. -/
example : a 2 = 9 := by
  have hcount : Nat.count InSeq 9 = 1 := by decide
  show Nat.nth InSeq 1 = 9
  rw [← hcount]
  exact Nat.nth_count (by decide)

/-! ## Counting lemmas -/

/-- A block of `r + 1 ≤ 5` consecutive integers starting at `5m` contains
`[m ∈ A277548] + [r = 4]` members of A277548. -/
theorem count_block (m r : ℕ) (hr : r < 5) :
    Nat.count (fun k => InSeq (5 * m + k)) (r + 1) =
      (if InSeq m then 1 else 0) + (if r = 4 then 1 else 0) := by
  have h1 : ¬ InSeq (5 * m + 1) := by rw [inSeq_iff_of_mod_ne (by omega)]; omega
  have h2 : ¬ InSeq (5 * m + 2) := by rw [inSeq_iff_of_mod_ne (by omega)]; omega
  have h3 : ¬ InSeq (5 * m + 3) := by rw [inSeq_iff_of_mod_ne (by omega)]; omega
  have h4 : InSeq (5 * m + 4) := by rw [inSeq_iff_of_mod_ne (by omega)]; omega
  interval_cases r <;> simp [Nat.count_succ, inSeq_five_mul, h1, h2, h3, h4]

/-- `#{k < 5m : k ∈ A277548} = m + #{k < m : k ∈ A277548}`. -/
theorem count_five_mul (m : ℕ) : Nat.count InSeq (5 * m) = m + Nat.count InSeq m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : 5 * (m + 1) = 5 * m + (4 + 1) := by ring
    rw [hsplit, Nat.count_add, count_block m 4 (by norm_num), ih, Nat.count_succ]
    simp only [if_true]
    ring

/-- With `F(N) = #{k ≤ N : k ∈ A277548}`: `F(5q + r) = q + F(q) + [r = 4]`
for `r < 5`. -/
theorem count_succ_five_mul_add (q r : ℕ) (hr : r < 5) :
    Nat.count InSeq (5 * q + r + 1) =
      q + Nat.count InSeq (q + 1) + (if r = 4 then 1 else 0) := by
  rw [add_assoc, Nat.count_add, count_block q r hr, count_five_mul, Nat.count_succ]
  ring

/-- Digit penalty: `pen 4 = 0` and `pen d = d` for `d ≠ 4`. -/
def pen (d : ℕ) : ℕ := if d = 4 then 0 else d

/-- Legendre-type identity: `4 F(N) + Σ_{d ∈ digits₅ N} pen d = N`, where
`F(N) = #{k ≤ N : k ∈ A277548}`. -/
theorem four_mul_count_add_sum_pen (N : ℕ) :
    4 * Nat.count InSeq (N + 1) + ((Nat.digits 5 N).map pen).sum = N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [Nat.count_succ, InSeq]
    have hq : N / 5 < N := Nat.div_lt_self hN (by norm_num)
    have hih := ih (N / 5) hq
    have hN' : N = 5 * (N / 5) + N % 5 := (Nat.div_add_mod N 5).symm
    have hrec := count_succ_five_mul_add (N / 5) (N % 5) (Nat.mod_lt _ (by norm_num))
    rw [← hN'] at hrec
    rw [Nat.digits_def' (by norm_num) hN, List.map_cons, List.sum_cons, hrec]
    have hpen : 4 * (if N % 5 = 4 then 1 else 0) + pen (N % 5) = N % 5 := by
      unfold pen; split_ifs <;> omega
    omega

/-! ## Digit lemmas -/

/-- The total penalty vanishes iff every base-5 digit is `0` or `4`. -/
theorem sum_pen_eq_zero_iff (N : ℕ) :
    ((Nat.digits 5 N).map pen).sum = 0 ↔ ∀ d ∈ Nat.digits 5 N, d = 0 ∨ d = 4 := by
  rw [List.sum_eq_zero_iff]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h d hd
    have hpd : pen d = 0 := h (pen d) d hd rfl
    unfold pen at hpd; split_ifs at hpd <;> omega
  · rintro h _ d hd rfl
    rcases h d hd with rfl | rfl <;> rfl

/-- Every base-5 digit of `4n` is `0` or `4` iff every base-5 digit of `n` is
at most `1`. -/
theorem digits_four_mul_iff (n : ℕ) :
    (∀ d ∈ Nat.digits 5 (4 * n), d = 0 ∨ d = 4) ↔ ∀ d ∈ Nat.digits 5 n, d ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < 4 * n),
      Nat.digits_def' (by norm_num) hn, List.forall_mem_cons, List.forall_mem_cons]
    by_cases hr : n % 5 ≤ 1
    · have hdiv : 4 * n / 5 = 4 * (n / 5) := by omega
      rw [hdiv, ih (n / 5) (Nat.div_lt_self hn (by norm_num))]
      constructor
      · rintro ⟨-, h⟩; exact ⟨hr, h⟩
      · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
    · constructor
      · rintro ⟨h, -⟩; omega
      · rintro ⟨h, -⟩; omega

/-- A positive integer whose base-5 digits are all `0` or `4` lies in
A277548. -/
theorem inSeq_of_digits (N : ℕ) (hN : 0 < N)
    (h : ∀ d ∈ Nat.digits 5 N, d = 0 ∨ d = 4) : InSeq N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [Nat.digits_def' (by norm_num) hN, List.forall_mem_cons] at h
    obtain ⟨hr, htail⟩ := h
    rcases hr with hr | hr
    · obtain ⟨q, rfl⟩ : ∃ q, N = 5 * q := ⟨N / 5, by omega⟩
      have hq : 5 * q / 5 = q := by omega
      rw [hq] at htail
      rw [inSeq_five_mul]
      exact ih q (by omega) (by omega) htail
    · exact (inSeq_iff_of_mod_ne (by omega)).2 hr

/-- A277548 is infinite (it contains every `5a + 4`). -/
theorem inSeq_infinite : (Set.ofPred InSeq).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ⟨5 * a + 4, ?_, by omega⟩
  exact (inSeq_iff_of_mod_ne (by omega)).2 (by omega)

/-! ## The conjecture -/

/-- Corneth's identity: the nth positive integer with last nonzero base-5
digit 4 is `4n` iff every base-5 digit of `n` is at most 1 (A033042).
The guard `n > 0` matches the source's offset 1. -/
theorem a_eq_four_mul_iff (n : ℕ) (hn : 0 < n) :
    a n = 4 * n ↔ ∀ d ∈ Nat.digits 5 n, d ≤ 1 := by
  have key := four_mul_count_add_sum_pen (4 * n)
  rw [a, ← digits_four_mul_iff, ← sum_pen_eq_zero_iff]
  constructor
  · intro h
    have hmem : InSeq (4 * n) := h ▸ Nat.nth_mem_of_infinite inSeq_infinite (n - 1)
    have hcount : Nat.count InSeq (4 * n) = n - 1 := by
      rw [← h]; exact Nat.count_nth_of_infinite inSeq_infinite (n - 1)
    rw [Nat.count_succ, if_pos hmem, hcount] at key
    omega
  · intro h
    have hmem : InSeq (4 * n) :=
      inSeq_of_digits (4 * n) (by omega) ((sum_pen_eq_zero_iff _).1 h)
    rw [Nat.count_succ, if_pos hmem, h] at key
    have hcount : Nat.count InSeq (4 * n) = n - 1 := by omega
    rw [← hcount]
    exact Nat.nth_count hmem

/-- `a 6 = 24` and `6 = (11)₅`. -/
example : a 6 = 24 := (a_eq_four_mul_iff 6 (by norm_num)).2 (by norm_num)

/-- `a 2 ≠ 8` since `2` has base-5 digit `2`. -/
example : a 2 ≠ 8 := fun h =>
  absurd ((a_eq_four_mul_iff 2 (by norm_num)).1 h 2 (by norm_num)) (by norm_num)

end Candidates.A277548WhoseLastNonzero
