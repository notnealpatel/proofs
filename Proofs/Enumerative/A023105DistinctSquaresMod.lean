/-
# Distinct squares modulo powers of two (A023105)

Source: Tilman Neumann's OEIS A023105 comment (Sep 20 2020).
For `n ≥ 1`, the number of distinct squares in `ZMod (2^n)` is 2 plus
the number of integers below `2^n` of the form `4^i(8j+7)` (A004215).
Membership in A004215 is defined by this explicit form, not by a
formalization of the three-square theorem. The identity fails at `n = 0`.
Both counts satisfy `f(n+3) = 2^n + f(n+1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A023105DistinctSquaresMod

/-! ## Definitions -/

/-- A023105 `a(n)`: the number of distinct quadratic residues mod `2^n`, i.e. the
cardinality of the image of `x ↦ x^2` on `ZMod (2^n)`. -/
def a (n : ℕ) : ℕ := (Finset.univ.image (fun x : ZMod (2 ^ n) => x ^ 2)).card

/-- Membership in A004215: `k = 4^i (8 j + 7)` for some `i j : ℕ`. -/
def IsA004215 (k : ℕ) : Prop := ∃ i j : ℕ, k = 4 ^ i * (8 * j + 7)

/-- Bounded form of `IsA004215`, used for decidability: some `4^i` with
`i ≤ k` divides `k` with cofactor `≡ 7 (mod 8)`. -/
theorem isA004215_iff_bounded (k : ℕ) :
    IsA004215 k ↔ ∃ i ∈ Finset.range (k + 1), k % 4 ^ i = 0 ∧ k / 4 ^ i % 8 = 7 := by
  constructor
  · rintro ⟨i, j, rfl⟩
    have hpos : 0 < 4 ^ i := by positivity
    have hlt : i < 4 ^ i := Nat.lt_pow_self (by norm_num)
    refine ⟨i, Finset.mem_range.mpr ?_, Nat.mul_mod_right _ _, ?_⟩
    · nlinarith
    · rw [Nat.mul_div_cancel_left _ hpos]
      omega
  · rintro ⟨i, -, hdvd, hmod⟩
    refine ⟨i, k / 4 ^ i / 8, ?_⟩
    have hk : 4 ^ i * (k / 4 ^ i) = k := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdvd)
    have hq : k / 4 ^ i = 8 * (k / 4 ^ i / 8) + 7 := by omega
    rw [← hq, hk]

instance : DecidablePred IsA004215 := fun k =>
  decidable_of_iff _ (isA004215_iff_bounded k).symm

/-! ## Examples -/

-- A023105 DATA, `a(0..6) = 1, 2, 2, 3, 4, 7, 12`.
example : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 4 ∧ a 5 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

example : a 6 = 12 := by decide

-- A004215 DATA: `7, 15, 23, 28, 31, 39, 47, 55, 60, 63` are its entries below 64.
example : (Finset.range 64).filter IsA004215 = {7, 15, 23, 28, 31, 39, 47, 55, 60, 63} := by
  decide

/-! ## Squares mod `2^n` as a set of natural residues -/

/-- The natural-number residues `x^2 mod 2^n` for `x < 2^n`. -/
def sqSet (n : ℕ) : Finset ℕ := (Finset.range (2 ^ n)).image (fun x => x ^ 2 % 2 ^ n)

/-- `a n` counts the natural residues `sqSet n` (transport along `ZMod.val`). -/
theorem a_eq_card_sqSet (n : ℕ) : a n = (sqSet n).card := by
  unfold a sqSet
  have hinj : Function.Injective (ZMod.val : ZMod (2 ^ n) → ℕ) := ZMod.val_injective _
  rw [← Finset.card_image_of_injective _ hinj, Finset.image_image]
  congr 1
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range, Function.comp]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, ZMod.val_lt x, by rw [pow_two x, ZMod.val_mul, pow_two]⟩
  · rintro ⟨x, -, rfl⟩
    refine ⟨(x : ZMod (2 ^ n)), ?_⟩
    rw [pow_two, ZMod.val_mul, ZMod.val_natCast, pow_two, ← Nat.mul_mod]

/-- `r` is in `sqSet m` iff `r < 2^m` and `r` is `x^2 mod 2^m` for some `x`. -/
theorem mem_sqSet {m r : ℕ} : r ∈ sqSet m ↔ r < 2 ^ m ∧ ∃ x, x ^ 2 % 2 ^ m = r := by
  unfold sqSet
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨Nat.mod_lt _ (by positivity), x, rfl⟩
  · rintro ⟨-, x, rfl⟩
    exact ⟨x % 2 ^ m, Nat.mod_lt _ (by positivity), by rw [← Nat.pow_mod]⟩

/-- Odd squares are `≡ 1 (mod 8)`. -/
theorem sq_mod_eight_of_odd {x : ℕ} (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have h : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases h with h | h | h | h <;> simp [Nat.pow_mod, h]

/-- Hensel lifting at `2`: every integer `r ≡ 1 (mod 8)` is congruent to the
square of an odd integer modulo `2^(k+3)`. -/
theorem exists_odd_sq_dvd_sub (r : ℤ) (hr : r % 8 = 1) (k : ℕ) :
    ∃ x : ℤ, Odd x ∧ 2 ^ (k + 3) ∣ x ^ 2 - r := by
  induction k with
  | zero => exact ⟨1, odd_one, by norm_num; omega⟩
  | succ k ih =>
    obtain ⟨x, hx, t, ht⟩ := ih
    rcases Int.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨x, hx, s, by rw [ht, hs]; ring⟩
    · obtain ⟨u, hu⟩ := hx
      refine ⟨x + 2 ^ (k + 2), ?_, s + u + 1 + 2 ^ k, ?_⟩
      · rw [hu]
        exact ⟨u + 2 ^ (k + 1), by ring⟩
      · rw [show (x + 2 ^ (k + 2)) ^ 2 - r = (x ^ 2 - r) + 2 ^ (k + 2) * (2 * x)
            + 2 ^ (k + 2) * 2 ^ (k + 2) by ring, ht, hs, hu]
        ring

/-- Every natural residue `r ≡ 1 (mod 8)` is a square modulo `2^(k+3)`. -/
theorem exists_sq_mod_eq (r : ℕ) (hr : r % 8 = 1) (k : ℕ) :
    ∃ x : ℕ, x ^ 2 % 2 ^ (k + 3) = r % 2 ^ (k + 3) := by
  obtain ⟨x, -, hx⟩ := exists_odd_sq_dvd_sub (r : ℤ) (by omega) k
  refine ⟨x.natAbs, ?_⟩
  have hmod : x.natAbs ^ 2 ≡ r [MOD 2 ^ (k + 3)] := by
    refine (Nat.modEq_iff_dvd.mpr ?_).symm
    push_cast
    rw [sq_abs]
    exact hx
  exact hmod

/-- The squares mod `2^(n+3)` are the residues `≡ 1 (mod 8)` together with
`4 *` the squares mod `2^(n+1)`. -/
theorem sqSet_add_three (n : ℕ) :
    sqSet (n + 3) = (Finset.range (2 ^ (n + 3))).filter (fun r => r % 8 = 1) ∪
      (sqSet (n + 1)).image (fun s => 4 * s) := by
  have h8 : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
  have h4 : 2 ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
  ext r
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image, mem_sqSet]
  constructor
  · rintro ⟨hr, x, rfl⟩
    rcases Nat.even_or_odd x with ⟨y, rfl⟩ | hx
    · right
      refine ⟨y ^ 2 % 2 ^ (n + 1), ⟨Nat.mod_lt _ (by positivity), y, rfl⟩, ?_⟩
      rw [show (y + y) ^ 2 = 4 * y ^ 2 by ring, h4, Nat.mul_mod_mul_left]
    · left
      refine ⟨hr, ?_⟩
      rw [h8, Nat.mod_mul_right_mod]
      exact sq_mod_eight_of_odd (Nat.odd_iff.mp hx)
  · rintro (⟨hr, hr8⟩ | ⟨s, ⟨hs, y, rfl⟩, rfl⟩)
    · obtain ⟨x, hx⟩ := exists_sq_mod_eq r hr8 n
      exact ⟨hr, x, by rw [hx, Nat.mod_eq_of_lt hr]⟩
    · refine ⟨by omega, 2 * y, ?_⟩
      rw [show (2 * y) ^ 2 = 4 * y ^ 2 by ring, h4, Nat.mul_mod_mul_left]

/-- Exactly `N` naturals below `8 N` lie in a fixed residue class `c < 8` mod `8`. -/
theorem card_filter_mod_eight (c : ℕ) (hc : c < 8) (N : ℕ) :
    ((Finset.range (8 * N)).filter (fun r => r % 8 = c)).card = N := by
  have hset : (Finset.range (8 * N)).filter (fun r => r % 8 = c) =
      (Finset.range N).image (fun b => 8 * b + c) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨r / 8, by omega, by omega⟩
    · rintro ⟨b, hb, rfl⟩
      omega
  have hinj : Function.Injective (fun b : ℕ => 8 * b + c) := by
    intro x y hxy
    simp only at hxy
    omega
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Recursion for the left side: `|sqSet (n+3)| = 2^n + |sqSet (n+1)|`. -/
theorem card_sqSet_add_three (n : ℕ) :
    (sqSet (n + 3)).card = 2 ^ n + (sqSet (n + 1)).card := by
  have h8 : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
  have hinj : Function.Injective (fun s : ℕ => 4 * s) := by
    intro x y hxy
    simp only at hxy
    omega
  have hdisj : Disjoint ((Finset.range (2 ^ (n + 3))).filter (fun r => r % 8 = 1))
      ((sqSet (n + 1)).image (fun s => 4 * s)) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    simp only [Finset.mem_filter, Finset.mem_image] at hr hr'
    obtain ⟨s, -, rfl⟩ := hr'
    omega
  rw [sqSet_add_three, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj, h8, card_filter_mod_eight 1 (by norm_num)]

/-! ## The A004215 side -/

/-- Unfolding `4^i (8 j + 7)` one level: either `k ≡ 7 (mod 8)`, or `k = 4 s`
with `s` again in A004215. -/
theorem isA004215_iff (k : ℕ) :
    IsA004215 k ↔ k % 8 = 7 ∨ ∃ s, IsA004215 s ∧ 4 * s = k := by
  constructor
  · rintro ⟨i, j, rfl⟩
    cases i with
    | zero =>
      left
      omega
    | succ i =>
      right
      exact ⟨4 ^ i * (8 * j + 7), ⟨i, j, rfl⟩, by ring⟩
  · rintro (h | ⟨s, ⟨i, j, rfl⟩, rfl⟩)
    · exact ⟨0, k / 8, by omega⟩
    · exact ⟨i + 1, j, by ring⟩

/-- A004215 below `2^(n+3)`: the residues `≡ 7 (mod 8)` together with `4 *`
the entries below `2^(n+1)`. -/
theorem filter_isA004215_add_three (n : ℕ) :
    (Finset.range (2 ^ (n + 3))).filter IsA004215 =
      (Finset.range (2 ^ (n + 3))).filter (fun r => r % 8 = 7) ∪
        ((Finset.range (2 ^ (n + 1))).filter IsA004215).image (fun s => 4 * s) := by
  have h4 : 2 ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
  ext k
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  rw [isA004215_iff]
  constructor
  · rintro ⟨hk, h | ⟨s, hs, rfl⟩⟩
    · exact Or.inl ⟨hk, h⟩
    · exact Or.inr ⟨s, ⟨by omega, hs⟩, rfl⟩
  · rintro (⟨hk, h⟩ | ⟨s, ⟨hs, hA⟩, rfl⟩)
    · exact ⟨hk, Or.inl h⟩
    · exact ⟨by omega, Or.inr ⟨s, hA, rfl⟩⟩

/-- Recursion for the right side. -/
theorem card_filter_isA004215_add_three (n : ℕ) :
    ((Finset.range (2 ^ (n + 3))).filter IsA004215).card =
      2 ^ n + ((Finset.range (2 ^ (n + 1))).filter IsA004215).card := by
  have h8 : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
  have hinj : Function.Injective (fun s : ℕ => 4 * s) := by
    intro x y hxy
    simp only at hxy
    omega
  have hdisj : Disjoint ((Finset.range (2 ^ (n + 3))).filter (fun r => r % 8 = 7))
      (((Finset.range (2 ^ (n + 1))).filter IsA004215).image (fun s => 4 * s)) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    simp only [Finset.mem_filter, Finset.mem_image] at hr hr'
    obtain ⟨s, -, rfl⟩ := hr'
    omega
  rw [filter_isA004215_add_three, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj, h8, card_filter_mod_eight 7 (by norm_num)]

/-! ## The conjecture -/

/-- Neumann's identity: for `n ≥ 1`, the number of squares modulo `2^n`
is 2 plus the count below `2^n` of integers `4^i(8j+7)`. At `n=0`
the two sides are 1 and 2. -/
theorem a_eq_two_add_card_A004215 (n : ℕ) (hn : 1 ≤ n) :
    a n = 2 + ((Finset.range (2 ^ n)).filter IsA004215).card := by
  rw [a_eq_card_sqSet]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => decide
    | 2, _ => decide
    | m + 3, _ =>
      rw [card_sqSet_add_three, card_filter_isA004215_add_three, ih (m + 1) (by omega) (by omega)]
      ring

-- The guard is load-bearing: the identity fails at `n = 0`.
example : a 0 ≠ 2 + ((Finset.range (2 ^ 0)).filter IsA004215).card := by decide

end Candidates.A023105DistinctSquaresMod
