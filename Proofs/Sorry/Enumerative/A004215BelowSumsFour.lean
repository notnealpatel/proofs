/-
# A004215 — Neumann: terms below `2^n` number `A023105(n) - 2`

## OEIS source (retrieved with `oeis show A004215`, 2026-10-21)

```
NAME:     Numbers that are the sum of 4 but no fewer nonzero squares.
TERMS:    7,15,23,28,31,39,47,55,60,63,71,79,87,92,95,103,111,112,119,124,
          127,135,143,151,156,159,167,175,183,188,191,199,207,215,220,223,...
KEYWORDS: nonn,nice,easy
COMMENT:  Numbers of the form 4^i*(8*j+7), i >= 0, j >= 0.
          [A.-M. Legendre & C. F. Gauss]
COMMENT (the conjecture):
  Conjecture: The number of terms < 2^n is A023105(n) - 2.
  - _Tilman Neumann_, Sep 20 2020
```

A023105: "Number of distinct quadratic residues mod 2^n", terms
`1,2,2,3,4,7,12,23,44,87,...` (offset 0); formula `a(n) = floor((2^n+10)/6)`.

## Status

Triage: open (no proof in the entry or the literature found by the triage).
This module proves the conjecture for `n ≥ 1` in the form the target spec
fixes ("sums of four but no fewer nonzero squares (that is, of the form
4^i(8j+7))"): `a004215_count_below_two_pow`.  The identification of the
entry's NAME predicate with the `4^i(8j+7)` form is Legendre's three-square
theorem, which is not in Mathlib.  The easy half is proved here
(`isA004215_of_isA004215Form`, giving the unconditional lower bound
`card_image_sq_le_card_filter_isA004215_add_two`); the NAME-predicate
version of the count is proved with the hard half of Legendre's theorem as
an explicit hypothesis (`a004215_count_below_two_pow_of_three_squares`).

## Proof outline

* Squares mod `2^n`: a residue `r < 2^n` is a square iff `r = 0` or
  `r = 4^i (8j+1)` (2-adic Hensel lifting for `u ≡ 1 mod 8`, and a descent
  on even roots).
* Counting: for `c ∈ {1, 7}`, the number `F_c(n)` of `r < 2^n` of the form
  `4^i (8j+c)` satisfies `F_c(n+3) = F_c(n+1) + 2^n`, with
  `F_1(1) = F_1(2) = 1`, `F_7(1) = F_7(2) = 0`; hence `F_1 = F_7 + 1`.
* So `#squares mod 2^n = 1 + F_1(n) = F_7(n) + 2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A004215BelowSumsFour

/-- `IsFourPowOctal c m`: `m` has the form `4^i * (8 j + c)` for some naturals `i, j`. -/
def IsFourPowOctal (c m : ℕ) : Prop := ∃ i j : ℕ, m = 4 ^ i * (8 * j + c)

/-- Bounded reformulation of `IsFourPowOctal`, used for decidability. -/
theorem isFourPowOctal_iff_bounded (c m : ℕ) :
    IsFourPowOctal c m ↔
      ∃ i < m + 1, 4 ^ i ∣ m ∧ c ≤ m / 4 ^ i ∧ (m / 4 ^ i - c) % 8 = 0 := by
  constructor
  · rintro ⟨i, j, rfl⟩
    have hpos : 0 < 4 ^ i := by positivity
    rcases Nat.eq_zero_or_pos (8 * j + c) with h0 | h0
    · refine ⟨0, by omega, ?_⟩
      simp only [pow_zero, h0]
      omega
    · refine ⟨i, ?_, dvd_mul_right _ _, ?_⟩
      · have h1 : i < 4 ^ i := Nat.lt_pow_self (by norm_num)
        have h2 : 4 ^ i ≤ 4 ^ i * (8 * j + c) := Nat.le_mul_of_pos_right _ h0
        omega
      · rw [Nat.mul_div_cancel_left _ hpos]
        omega
  · rintro ⟨i, -, ⟨q, hq⟩, hc, h8⟩
    have hpos : 0 < 4 ^ i := by positivity
    rw [hq, Nat.mul_div_cancel_left _ hpos] at hc h8
    exact ⟨i, (q - c) / 8, by rw [hq]; congr 1; omega⟩

/-- Decidability of `IsFourPowOctal c` through the bounded reformulation. -/
instance (c : ℕ) : DecidablePred (IsFourPowOctal c) := fun m =>
  decidable_of_iff _ (isFourPowOctal_iff_bounded c m).symm

/-- `m` is of the form `4^i (8j + 7)` (the Legendre–Gauss description of A004215
recorded in the entry). -/
def IsA004215Form (m : ℕ) : Prop := ∃ i j : ℕ, m = 4 ^ i * (8 * j + 7)

/-- Decidability of `IsA004215Form` (definitionally `IsFourPowOctal 7`). -/
instance : DecidablePred IsA004215Form := fun m =>
  inferInstanceAs (Decidable (IsFourPowOctal 7 m))

/-! ## Ground truth -/

set_option maxRecDepth 20000 in
/-- The first ten listed terms of A004215 are exactly the members of the form below `64`. -/
example : (Finset.range 64).filter IsA004215Form = {7, 15, 23, 28, 31, 39, 47, 55, 60, 63} := by
  decide

/-! A023105 ground truth: `1, 2, 2, 3, 4, 7, 12` for `n = 0, …, 6`. -/
example : (Finset.univ.image (fun x : ZMod (2 ^ 0) => x ^ 2)).card = 1 := by decide
example : (Finset.univ.image (fun x : ZMod (2 ^ 1) => x ^ 2)).card = 2 := by decide
example : (Finset.univ.image (fun x : ZMod (2 ^ 2) => x ^ 2)).card = 2 := by decide
example : (Finset.univ.image (fun x : ZMod (2 ^ 3) => x ^ 2)).card = 3 := by decide
example : (Finset.univ.image (fun x : ZMod (2 ^ 4) => x ^ 2)).card = 4 := by decide
example : (Finset.univ.image (fun x : ZMod (2 ^ 5) => x ^ 2)).card = 7 := by decide
example : (Finset.univ.image (fun x : ZMod (2 ^ 6) => x ^ 2)).card = 12 := by decide

/-! ## Squares modulo `2^n` -/

/-- 2-adic Hensel lifting: every `u ≡ 1 (mod 8)` is congruent to an odd square
modulo `2^(k+3)`. -/
theorem exists_odd_sq_sub_dvd (u : ℤ) (hu : (8 : ℤ) ∣ u - 1) (k : ℕ) :
    ∃ v : ℤ, Odd v ∧ (2 : ℤ) ^ (k + 3) ∣ v ^ 2 - u := by
  induction k with
  | zero => exact ⟨1, odd_one, by simpa using (dvd_sub_comm.mp hu)⟩
  | succ k ih =>
    obtain ⟨v, hv, t, ht⟩ := ih
    rcases Int.even_or_odd t with ⟨s, hs⟩ | htodd
    · refine ⟨v, hv, s, ?_⟩
      rw [ht, hs, pow_succ]
      ring
    · obtain ⟨s, hs⟩ : Even (t + v) := htodd.add_odd hv
      refine ⟨v + 2 ^ (k + 2), hv.add_even ?_, s + 2 ^ k, ?_⟩
      · exact (even_two.pow_of_ne_zero (by omega))
      · have hexp : (v + 2 ^ (k + 2)) ^ 2 - u =
            (v ^ 2 - u) + 2 ^ (k + 3) * v + 2 ^ (2 * k + 4) := by
          ring
        rw [hexp, ht]
        have h2 : (2 : ℤ) ^ (k + 3) * t + 2 ^ (k + 3) * v = 2 ^ (k + 3) * (t + v) := by ring
        rw [h2, hs]
        ring

/-- Every `u ≡ 1 (mod 8)` is a square modulo `2^n`. -/
theorem exists_sq_mod_eq_of_mod_eight (u : ℕ) (hu : u % 8 = 1) (n : ℕ) :
    ∃ v : ℕ, v ^ 2 % 2 ^ n = u % 2 ^ n := by
  have hu' : (8 : ℤ) ∣ (u : ℤ) - 1 := by
    have := Nat.div_add_mod u 8
    exact ⟨(u / 8 : ℕ), by omega⟩
  obtain ⟨v, -, hdvd⟩ := exists_odd_sq_sub_dvd u hu' n
  refine ⟨v.natAbs, ?_⟩
  have hdvd' : ((2 ^ n : ℕ) : ℤ) ∣ ((u : ℕ) : ℤ) - ((v.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [← dvd_neg, neg_sub]
    push_cast
    rw [sq_abs]
    exact (pow_dvd_pow (2 : ℤ) (Nat.le_add_right n 3)).trans hdvd
  exact (Nat.modEq_iff_dvd.mpr hdvd')

/-- The square of an odd natural is `1 mod 8`. -/
theorem sq_mod_eight_of_odd {y : ℕ} (hy : y % 2 = 1) : y ^ 2 % 8 = 1 := by
  have h8 : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases h8 with h | h | h | h <;> rw [h]

/-- A nonzero square residue modulo `2^n` (as a natural below `2^n`) has the form
`4^i (8j + 1)`. -/
theorem isFourPowOctal_one_sq_mod (n : ℕ) :
    ∀ y : ℕ, y ^ 2 % 2 ^ n ≠ 0 → IsFourPowOctal 1 (y ^ 2 % 2 ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hy
  rcases Nat.even_or_odd' y with ⟨z, rfl | rfl⟩
  · -- even `y = 2 z`
    match n, ih, hy with
    | 0, _, hy => exact absurd (Nat.mod_one _) hy
    | 1, _, hy => exact absurd (by rw [pow_one, mul_pow]; omega) hy
    | m + 2, ih, hy =>
      have hsplit : (2 * z) ^ 2 % 2 ^ (m + 2) = 4 * (z ^ 2 % 2 ^ m) := by
        rw [mul_pow, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm (2 ^ m) 4,
          Nat.mul_mod_mul_left]
      rw [hsplit] at hy ⊢
      have hz : z ^ 2 % 2 ^ m ≠ 0 := by omega
      obtain ⟨i, j, hij⟩ := ih m (by omega) z hz
      exact ⟨i + 1, j, by rw [hij, pow_succ]; ring⟩
  · -- odd `y = 2 z + 1`
    have h8 : (2 * z + 1) ^ 2 % 8 = 1 := sq_mod_eight_of_odd (by omega)
    by_cases hn : 3 ≤ n
    · have hdvd : 8 ∣ 2 ^ n := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
        exact Nat.pow_dvd_pow 2 hn
      have hr : (2 * z + 1) ^ 2 % 2 ^ n % 8 = 1 := by
        rw [Nat.mod_mod_of_dvd _ hdvd, h8]
      exact ⟨0, (2 * z + 1) ^ 2 % 2 ^ n / 8, by omega⟩
    · interval_cases n
      · exact absurd (Nat.mod_one _) hy
      · exact ⟨0, 0, by omega⟩
      · exact ⟨0, 0, by omega⟩

/-- Conversely, every `r < 2^n` of the form `4^i (8j + 1)` is a square residue
modulo `2^n`. -/
theorem exists_sq_mod_of_isFourPowOctal_one {n r : ℕ} (hr : r < 2 ^ n)
    (h : IsFourPowOctal 1 r) : ∃ y : ℕ, y ^ 2 % 2 ^ n = r := by
  obtain ⟨i, j, rfl⟩ := h
  obtain ⟨v, hv⟩ := exists_sq_mod_eq_of_mod_eight (8 * j + 1) (by omega) n
  refine ⟨2 ^ i * v, ?_⟩
  have hmod : (2 ^ i * v) ^ 2 ≡ 4 ^ i * (8 * j + 1) [MOD 2 ^ n] := by
    have h4 : (2 ^ i * v) ^ 2 = 4 ^ i * v ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm i 2, pow_mul]
      norm_num
    rw [h4]
    exact Nat.ModEq.mul_left _ hv
  rw [hmod]
  exact Nat.mod_eq_of_lt hr

/-- For odd `c`, `0` is not of the form `4^i (8j + c)`. -/
theorem not_isFourPowOctal_zero {c : ℕ} (hc : c % 2 = 1) : ¬ IsFourPowOctal c 0 := by
  rintro ⟨i, j, h⟩
  have hpos : 0 < 4 ^ i := by positivity
  have := Nat.mul_pos hpos (show 0 < 8 * j + c by omega)
  omega

/-- The number of squares in `ZMod (2^n)` equals the number of `r < 2^n` with
`r = 0` or `r` of the form `4^i (8j + 1)`. -/
theorem card_image_sq_zmod (n : ℕ) :
    (Finset.univ.image (fun x : ZMod (2 ^ n) => x ^ 2)).card =
      ((Finset.range (2 ^ n)).filter (fun r => r = 0 ∨ IsFourPowOctal 1 r)).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    have hcast : y ^ 2 = ((y.val ^ 2 : ℕ) : ZMod (2 ^ n)) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [Finset.mem_filter, Finset.mem_range, hcast, ZMod.val_natCast]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    by_cases h0 : y.val ^ 2 % 2 ^ n = 0
    · exact Or.inl h0
    · exact Or.inr (isFourPowOctal_one_sq_mod n y.val h0)
  · intro x _ x' _ h
    exact ZMod.val_injective _ h
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hlt, h0 | hform⟩ := hr
    · refine ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩, ?_⟩
      rw [ZMod.val_zero, h0]
    · obtain ⟨y, hy⟩ := exists_sq_mod_of_isFourPowOctal_one hlt hform
      refine ⟨((y ^ 2 : ℕ) : ZMod (2 ^ n)), Finset.mem_image.mpr ⟨(y : ZMod (2 ^ n)),
        Finset.mem_univ _, by push_cast; rfl⟩, ?_⟩
      rw [ZMod.val_natCast, hy]

/-- Splitting off the residue `0` from the count. -/
theorem card_filter_zero_or (N : ℕ) (hN : 0 < N) {c : ℕ} (hc : c % 2 = 1) :
    ((Finset.range N).filter (fun r => r = 0 ∨ IsFourPowOctal c r)).card =
      ((Finset.range N).filter (IsFourPowOctal c)).card + 1 := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  · rw [Finset.filter_eq' (Finset.range N) 0, if_pos (Finset.mem_range.mpr hN),
      Finset.card_singleton, add_comm]
  · rw [Finset.disjoint_filter]
    rintro r - rfl
    exact not_isFourPowOctal_zero hc

/-! ## Counting the forms `4^i (8j + c)` below `2^n` -/

/-- For odd `c`, `4 s` has the form `4^i (8j + c)` iff `s` does. -/
theorem isFourPowOctal_four_mul_iff {c : ℕ} (hc : c % 2 = 1) (s : ℕ) :
    IsFourPowOctal c (4 * s) ↔ IsFourPowOctal c s := by
  constructor
  · rintro ⟨i, j, h⟩
    rcases i with _ | i
    · omega
    · exact ⟨i, j, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) (by rw [h, pow_succ]; ring)⟩
  · rintro ⟨i, j, h⟩
    exact ⟨i + 1, j, by rw [h, pow_succ]; ring⟩

/-- For `c < 8` and `4 ∤ r`, `r` has the form `4^i (8j + c)` iff `r ≡ c (mod 8)`. -/
theorem isFourPowOctal_iff_of_not_dvd {c : ℕ} (hc : c < 8) {r : ℕ} (hr : ¬ 4 ∣ r) :
    IsFourPowOctal c r ↔ r % 8 = c := by
  constructor
  · rintro ⟨i, j, h⟩
    rcases i with _ | i
    · omega
    · exact absurd ⟨4 ^ i * (8 * j + c), by rw [h, pow_succ]; ring⟩ hr
  · intro h
    exact ⟨0, r / 8, by omega⟩

/-- Exactly `K` naturals below `8 K` are `≡ c (mod 8)`, for `c < 8`. -/
theorem count_mod_eight (c : ℕ) (hc : c < 8) (K : ℕ) :
    ((Finset.range (8 * K)).filter (fun r => r % 8 = c)).card = K := by
  rw [← Nat.count_eq_card_filter_range]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [mul_add, mul_one, Nat.count_add, ih]
    have h1 : Nat.count (fun k => (8 * K + k) % 8 = c) 8 = Nat.count (fun k => k % 8 = c) 8 := by
      congr 1
      funext k
      rw [Nat.mul_add_mod]
    have h2 : Nat.count (fun k => k % 8 = c) 8 = 1 := by
      interval_cases c <;> decide
    rw [h1, h2]

/-- The count of the form `4^i (8j + c)` below `8 K` is the count below `2 K` plus `K`. -/
theorem card_filter_four_mul {c : ℕ} (hc : c % 2 = 1) (hc8 : c < 8) (K : ℕ) :
    ((Finset.range (4 * (2 * K))).filter (IsFourPowOctal c)).card =
      ((Finset.range (2 * K)).filter (IsFourPowOctal c)).card + K := by
  rw [← Finset.card_filter_add_card_filter_not
      (s := (Finset.range (4 * (2 * K))).filter (IsFourPowOctal c)) (fun r => 4 ∣ r),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  · apply Finset.card_nbij' (fun r => r / 4) (fun s => 4 * s)
    · intro r hr
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hr ⊢
      obtain ⟨hlt, hP, ⟨s, rfl⟩⟩ := hr
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      exact ⟨by omega, (isFourPowOctal_four_mul_iff hc s).mp hP⟩
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hs ⊢
      exact ⟨by omega, (isFourPowOctal_four_mul_iff hc s).mpr hs.2, dvd_mul_right 4 s⟩
    · intro r hr
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hr
      obtain ⟨-, -, ⟨s, rfl⟩⟩ := hr
      show 4 * (4 * s / 4) = 4 * s
      omega
    · intro s _
      show 4 * s / 4 = s
      omega
  · have hK := count_mod_eight c hc8 K
    rw [show 8 * K = 4 * (2 * K) by ring] at hK
    refine Eq.trans ?_ hK
    congr 1
    apply Finset.filter_congr
    intro r _
    constructor
    · rintro ⟨hP, h4⟩
      exact (isFourPowOctal_iff_of_not_dvd hc8 h4).mp hP
    · intro h
      have h4 : ¬ 4 ∣ r := by omega
      exact ⟨(isFourPowOctal_iff_of_not_dvd hc8 h4).mpr h, h4⟩

/-- Two-step recursion `F_c(n+3) = F_c(n+1) + 2^n` for the count below `2^n`. -/
theorem card_filter_two_pow_add_three {c : ℕ} (hc : c % 2 = 1) (hc8 : c < 8) (n : ℕ) :
    ((Finset.range (2 ^ (n + 3))).filter (IsFourPowOctal c)).card =
      ((Finset.range (2 ^ (n + 1))).filter (IsFourPowOctal c)).card + 2 ^ n := by
  rw [show 2 ^ (n + 3) = 4 * (2 * 2 ^ n) by ring, show 2 ^ (n + 1) = 2 * 2 ^ n by ring]
  exact card_filter_four_mul hc hc8 (2 ^ n)

/-- Below `2^(n+1)`, the form `4^i (8j+1)` occurs exactly once more than `4^i (8j+7)`. -/
theorem card_one_eq_card_seven_add_one (n : ℕ) :
    ((Finset.range (2 ^ (n + 1))).filter (IsFourPowOctal 1)).card =
      ((Finset.range (2 ^ (n + 1))).filter (IsFourPowOctal 7)).card + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n, ih with
  | 0, _ => decide
  | 1, _ => decide
  | m + 2, ih =>
    rw [card_filter_two_pow_add_three (by norm_num) (by norm_num) m,
      card_filter_two_pow_add_three (by norm_num) (by norm_num) m, ih m (by omega)]
    ring

/-! ## The conjecture -/

/-- **Neumann's conjecture (A004215, Tilman Neumann, Sep 20 2020).**

Verbatim: "Conjecture: The number of terms < 2^n is A023105(n) - 2."

For `1 ≤ n`, the number of `m < 2^n` of the form `4^i (8j + 7)` (the entry's
Legendre–Gauss description of A004215) plus `2` equals A023105(n), the number of
distinct squares in `ZMod (2^n)`.  The `+ 2` form avoids natural subtraction;
the guard `1 ≤ n` is from the target (at `n = 0`, `0 + 2 ≠ 1`). -/
theorem a004215_count_below_two_pow (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range (2 ^ n)).filter IsA004215Form).card + 2 =
      (Finset.univ.image (fun x : ZMod (2 ^ n) => x ^ 2)).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [card_image_sq_zmod, card_filter_zero_or _ (by positivity) (by norm_num),
    card_one_eq_card_seven_add_one]
  rfl

/-! ## The entry's NAME predicate -/

/-- Squares modulo `8`: odd squares are `1`, even squares are `0` or `4`. -/
theorem sq_mod_eight_cases (x : ℕ) :
    (x % 2 = 1 ∧ x ^ 2 % 8 = 1) ∨ (x % 2 = 0 ∧ (x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4)) := by
  have h8 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨
      x % 8 = 6 ∨ x % 8 = 7 := by omega
  have hp : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := Nat.pow_mod x 2 8
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hp <;> norm_num at hp <;> omega

/-- Easy half of Legendre's theorem: `4^i (8j + 7)` is not a sum of three squares. -/
theorem not_sum_three_sq_of_isA004215Form (i j : ℕ) :
    ∀ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 ≠ 4 ^ i * (8 * j + 7) := by
  induction i with
  | zero =>
    intro x y z h
    rw [pow_zero, one_mul] at h
    rcases sq_mod_eight_cases x with hx | hx <;> rcases sq_mod_eight_cases y with hy | hy <;>
      rcases sq_mod_eight_cases z with hz | hz <;> omega
  | succ i ih =>
    intro x y z h
    rw [pow_succ (4 : ℕ) i] at h
    have hx : x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
      have h4 : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by
        rw [h, show 4 ^ i * 4 * (8 * j + 7) = 4 * (4 ^ i * (8 * j + 7)) by ring,
          Nat.mul_mod_right]
      rcases sq_mod_eight_cases x with hx | hx <;> rcases sq_mod_eight_cases y with hy | hy <;>
        rcases sq_mod_eight_cases z with hz | hz <;> omega
    obtain ⟨hx, hy, hz⟩ := hx
    obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    obtain ⟨z', rfl⟩ : ∃ z', z = 2 * z' := ⟨z / 2, by omega⟩
    apply ih x' y' z'
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4)
    rw [show 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = (2 * x') ^ 2 + (2 * y') ^ 2 + (2 * z') ^ 2 by ring,
      h]
    ring

/-- `m` is a sum of exactly `k` nonzero squares (a multiset of `k` positive roots). -/
def IsSumOfNonzeroSquares (k m : ℕ) : Prop :=
  ∃ s : Multiset ℕ, Multiset.card s = k ∧ 0 ∉ s ∧ (s.map (· ^ 2)).sum = m

/-- The entry's NAME: `m` is a sum of `4` but no fewer nonzero squares. -/
def IsA004215 (m : ℕ) : Prop :=
  IsSumOfNonzeroSquares 4 m ∧ ∀ k < 4, ¬ IsSumOfNonzeroSquares k m

/-- `m` is a sum of four but no fewer nonzero squares iff `m` is not a sum of three
squares of naturals (zeros allowed); uses Lagrange's four-square theorem. -/
theorem isA004215_iff_not_sum_three_sq (m : ℕ) :
    IsA004215 m ↔ ¬ ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + z ^ 2 := by
  constructor
  · rintro ⟨-, hfew⟩ ⟨x, y, z, rfl⟩
    have hsplit := Multiset.filter_add_not (p := fun a : ℕ => a ≠ 0) ({x, y, z} : Multiset ℕ)
    set t := Multiset.filter (fun a : ℕ => a ≠ 0) ({x, y, z} : Multiset ℕ) with ht
    have hcard : Multiset.card t ≤ 3 :=
      calc Multiset.card t ≤ Multiset.card ({x, y, z} : Multiset ℕ) :=
            Multiset.card_le_card (Multiset.filter_le _ _)
        _ = 3 := by simp
    have h0 : (0 : ℕ) ∉ t := by
      rw [ht, Multiset.mem_filter]
      exact fun h => h.2 rfl
    have hzero : ((Multiset.filter (fun a : ℕ => ¬ a ≠ 0) ({x, y, z} : Multiset ℕ)).map
        (· ^ 2)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
      rw [Multiset.mem_filter] at hb
      rw [not_not.mp hb.2]
      norm_num
    have hsum : (t.map (· ^ 2)).sum = x ^ 2 + y ^ 2 + z ^ 2 := by
      have h := congrArg (fun u : Multiset ℕ => (u.map (· ^ 2)).sum) hsplit
      simp only [Multiset.map_add, Multiset.sum_add, hzero, add_zero] at h
      rw [h]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton]
      ring
    exact hfew (Multiset.card t) (by omega) ⟨t, rfl, h0, hsum⟩
  · intro hnot
    refine ⟨?_, ?_⟩
    · obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares m
      refine ⟨{a, b, c, d}, by simp, ?_, ?_⟩
      · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
        · exact hnot ⟨b, c, d, by rw [← habcd]; ring⟩
        · exact hnot ⟨a, c, d, by rw [← habcd]; ring⟩
        · exact hnot ⟨a, b, d, by rw [← habcd]; ring⟩
        · exact hnot ⟨a, b, c, by rw [← habcd]; ring⟩
      · simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
          Multiset.map_singleton, Multiset.sum_singleton]
        rw [← habcd]
        ring
    · rintro k hk ⟨s, hcard, -, hsum⟩
      set u := s + Multiset.replicate (3 - k) 0 with hu
      have hucard : Multiset.card u = 3 := by
        rw [hu, Multiset.card_add, Multiset.card_replicate, hcard]
        omega
      obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.mp hucard
      have husum : (u.map (· ^ 2)).sum = m := by
        rw [hu, Multiset.map_add, Multiset.sum_add, hsum, Multiset.map_replicate,
          Multiset.sum_replicate]
        simp
      rw [hxyz] at husum
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton] at husum
      exact hnot ⟨x, y, z, by rw [← husum]; ring⟩

/-- Every number of the form `4^i (8j + 7)` is a sum of four but no fewer nonzero
squares (no use of the hard half of Legendre's theorem). -/
theorem isA004215_of_isA004215Form {m : ℕ} (h : IsA004215Form m) : IsA004215 m := by
  obtain ⟨i, j, rfl⟩ := h
  rw [isA004215_iff_not_sum_three_sq]
  rintro ⟨x, y, z, hxyz⟩
  exact not_sum_three_sq_of_isA004215Form i j x y z hxyz.symm

/-! ### Ground truth for the NAME predicate -/

example : IsA004215 7 := isA004215_of_isA004215Form ⟨0, 0, rfl⟩
example : IsA004215 28 := isA004215_of_isA004215Form ⟨1, 0, rfl⟩
example : IsA004215 112 := isA004215_of_isA004215Form ⟨2, 0, rfl⟩
example : ¬ IsA004215 0 := fun h => h.2 0 (by norm_num) ⟨0, rfl, by simp, rfl⟩
example : ¬ IsA004215 6 := fun h => h.2 3 (by norm_num) ⟨{2, 1, 1}, rfl, by decide, rfl⟩
example : ¬ IsA004215 8 := fun h => h.2 2 (by norm_num) ⟨{2, 2}, rfl, by decide, rfl⟩

/-- Under the hard half of Legendre's three-square theorem (every `m` not of the form
`4^i (8j+7)` is a sum of three squares), the entry's NAME predicate coincides with the
`4^i (8j+7)` form.  The hypothesis is an explicit unpaid premise, not proved here. -/
theorem isA004215_iff_isA004215Form_of_three_squares
    (hL : ∀ m : ℕ, ¬ IsA004215Form m → ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + z ^ 2) (m : ℕ) :
    IsA004215 m ↔ IsA004215Form m := by
  refine ⟨fun h => ?_, isA004215_of_isA004215Form⟩
  by_contra hform
  exact (isA004215_iff_not_sum_three_sq m).mp h (hL m hform)

open Classical in
/-- Unconditional half of Neumann's conjecture for the entry's NAME predicate: for every
`n`, A023105(n) is at most the number of `m < 2^n` that are sums of four but no fewer
nonzero squares, plus `2`. -/
theorem card_image_sq_le_card_filter_isA004215_add_two (n : ℕ) :
    (Finset.univ.image (fun x : ZMod (2 ^ n) => x ^ 2)).card ≤
      ((Finset.range (2 ^ n)).filter IsA004215).card + 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  rw [← a004215_count_below_two_pow n hn]
  have hsub : (Finset.range (2 ^ n)).filter IsA004215Form ⊆
      (Finset.range (2 ^ n)).filter IsA004215 :=
by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, isA004215_of_isA004215Form hm.2⟩
  have hle := Finset.card_le_card hsub
  omega

open Classical in
/-- Neumann's conjecture for the entry's NAME predicate ("sum of 4 but no fewer nonzero
squares"), conditional on the hard half of Legendre's three-square theorem, which is an
explicit premise `hL` (not in Mathlib, not proved here): for `1 ≤ n`, the number of such
`m < 2^n`, plus `2`, equals A023105(n). -/
theorem a004215_count_below_two_pow_of_three_squares
    (hL : ∀ m : ℕ, ¬ IsA004215Form m → ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + z ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range (2 ^ n)).filter IsA004215).card + 2 =
      (Finset.univ.image (fun x : ZMod (2 ^ n) => x ^ 2)).card := by
  rw [← a004215_count_below_two_pow n hn]
  congr 2
  exact Finset.filter_congr (fun m _ => isA004215_iff_isA004215Form_of_three_squares hL m)

end Candidates.A004215BelowSumsFour
