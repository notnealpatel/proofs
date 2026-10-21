/-
# A231817 — multiplicative digital root of the concatenation of divisors is almost always 0

## OEIS source (retrieved with `oeis show A231817`, 2026-10-21)

```
NAME:     Multiplicative digital root of concatenation of all divisors of n (A037278).
TERMS:    1,2,3,8,5,8,7,8,4,0,1,6,3,0,5,0,7,0,9,0,8,8,6,8,0,4,6,0,8,0,3,0,4,6,0,0,2,
          8,8,0,4,0,2,0,0,6,6,0,0,0,0,0,5,0,0,0,0,0,0,0,6,4,0,0,0,0,8,0,2,0,7,0,2,8,
          0,0,8,0,8,0,0,6,8,0,0,0,0
COMMENT:  Also multiplicative digital root of A190997 (product of digits of all the
          divisors of n) or A007955 (product of divisors of n).
COMMENT (the conjecture, unattributed in the entry):
          Conjecture: a(n) = 0 for almost all n.
COMMENT:  793 of the first 1000 terms are zeros, and 9147 out of the first 10000 terms
          are zeros. - _Harvey P. Dale_, Jul 30 2019
```

## Status

Triage: open (no proof in the entry or the literature found by the triage), flagged as
essentially elementary.  "Almost all" is read as natural density: the set of `n ≥ 1` with
`a n ≠ 0` has natural density `0`.

## Proof outline (all kernel-checked below)

The concatenation of the divisors of `n` ends with the decimal digits of `n` itself, so a
digit `0` of `n` is a digit `0` of the concatenation, whose digit product is then `0`; hence
`a n ≠ 0` forces `n` to be zeroless.  Zeroless numbers below `10 ^ k` number at most
`9 ^ (k + 1) / 8`, so their proportion up to `N` is `O((9/10) ^ log₁₀ N) → 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A231817MultiplicativeDigitalRoot

open Filter Topology

/-! ## Definition layer -/

/-- The divisors of `n` listed in increasing order: the `d ∈ [1, n]` with `d ∣ n`.
(Bridged to `(Nat.divisors n).sort` by `divisorList_eq_sort`.) -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- `concatStep acc d` is the number whose decimal representation is that of `acc`
followed by that of `d` (for `acc = 0` it is just `d`). -/
def concatStep (acc d : ℕ) : ℕ := d + 10 ^ (Nat.digits 10 d).length * acc

/-- A037278: the decimal concatenation of the divisors of `n` in increasing order. -/
def concatDivisors (n : ℕ) : ℕ := (divisorList n).foldl concatStep 0

/-- Multiplicative digital root with explicit fuel: while the number has at least two
decimal digits, replace it by the product of its digits, at most `k` times. -/
def mdrFuel : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => if m < 10 then m else mdrFuel k (Nat.digits 10 m).prod

/-- The multiplicative digital root of `m`: iterate the product of decimal digits until a
single digit remains. The fuel `m` suffices; see `mdr_eq` for the defining recursion. -/
def mdr (m : ℕ) : ℕ := mdrFuel m m

/-- A231817: the multiplicative digital root of the concatenation of the divisors of `n`. -/
def a (n : ℕ) : ℕ := mdr (concatDivisors n)

/-! ## Ground truth -/

example : divisorList 12 = [1, 2, 3, 4, 6, 12] := by decide
example : concatStep 12 34 = 1234 := by decide +kernel
example : (List.range 30).map (fun n => concatDivisors (n + 1)) =
    [1, 12, 13, 124, 15, 1236, 17, 1248, 139, 12510, 111, 1234612, 113, 12714, 13515, 124816,
     117, 1236918, 119, 12451020, 13721, 121122, 123, 1234681224, 1525, 121326, 13927,
     12471428, 129, 12356101530] := by decide +kernel
example : mdr 39 = 4 := by decide +kernel
example : (List.range 40).map (fun n => a (n + 1)) =
    [1, 2, 3, 8, 5, 8, 7, 8, 4, 0, 1, 6, 3, 0, 5, 0, 7, 0, 9, 0, 8, 8, 6, 8, 0, 4, 6, 0, 8, 0,
     3, 0, 4, 6, 0, 0, 2, 8, 8, 0] := by decide +kernel

/-! ## Faithfulness bridges -/

/-- `divisorList n` is the increasing enumeration of `Nat.divisors n`. -/
theorem divisorList_eq_sort (n : ℕ) : divisorList n = (Nat.divisors n).sort := by
  have hnd : (divisorList n).Nodup := List.Nodup.filter _ List.nodup_range'
  have hmem : ∀ d, d ∈ divisorList n ↔ d ∈ Nat.divisors n := by
    intro d
    simp only [divisorList, List.mem_filter, List.mem_range'_1, decide_eq_true_eq,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, hn⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn), by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd; omega⟩, hd⟩
  have hperm : List.Perm (divisorList n) (Nat.divisors n).sort := by
    apply List.perm_of_nodup_nodup_toFinset_eq hnd (Finset.sort_nodup _ _)
    ext d
    simp only [List.mem_toFinset, Finset.mem_sort, hmem]
  have hsorted : (divisorList n).Pairwise (· ≤ ·) := by
    have : (List.range' 1 n).Pairwise (· < ·) := List.pairwise_lt_range'
    exact (this.filter _).imp le_of_lt
  exact hperm.eq_of_pairwise (fun x y _ _ hxy hyx => le_antisymm hxy hyx) hsorted
    (Finset.pairwise_sort _ _)

/-- For `m ≥ 1` the product of the decimal digits of `m` is at most `m`. -/
theorem digits_prod_le (m : ℕ) (hm : 0 < m) : (Nat.digits 10 m).prod ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [Nat.digits_def' (by norm_num) hm, List.prod_cons]
    rcases Nat.eq_zero_or_pos (m / 10) with h0 | hpos
    · rw [h0, Nat.digits_zero, List.prod_nil]
      omega
    · have hrec := ih (m / 10) (Nat.div_lt_self hm (by norm_num)) hpos
      calc m % 10 * (Nat.digits 10 (m / 10)).prod ≤ 9 * (m / 10) :=
            Nat.mul_le_mul (by omega) hrec
        _ ≤ m := by omega

/-- For `m ≥ 10` the product of the decimal digits of `m` is strictly smaller than `m`. -/
theorem digits_prod_lt (m : ℕ) (hm : 10 ≤ m) : (Nat.digits 10 m).prod < m := by
  rw [Nat.digits_def' (by norm_num) (by omega), List.prod_cons]
  have hrec := digits_prod_le (m / 10) (by omega)
  calc m % 10 * (Nat.digits 10 (m / 10)).prod ≤ 9 * (m / 10) :=
        Nat.mul_le_mul (by omega) hrec
    _ < m := by omega

/-- Any fuel at least `m` computes the same value of `mdrFuel` at `m`. -/
theorem mdrFuel_congr (k j m : ℕ) (hk : m ≤ k) (hj : m ≤ j) : mdrFuel k m = mdrFuel j m := by
  induction k generalizing m j with
  | zero =>
    obtain rfl : m = 0 := by omega
    cases j <;> simp [mdrFuel]
  | succ k ih =>
    cases j with
    | zero =>
      obtain rfl : m = 0 := by omega
      simp [mdrFuel]
    | succ j =>
      simp only [mdrFuel]
      split_ifs with h
      · rfl
      · have hlt := digits_prod_lt m (by omega)
        exact ih j _ (by omega) (by omega)

/-- The multiplicative digital root satisfies its defining recursion. -/
theorem mdr_eq (m : ℕ) : mdr m = if m < 10 then m else mdr (Nat.digits 10 m).prod := by
  split_ifs with h
  · unfold mdr
    cases m with
    | zero => rfl
    | succ k => simp [mdrFuel, h]
  · have hlt := digits_prod_lt m (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    unfold mdr
    simp only [mdrFuel, h, if_false]
    exact mdrFuel_congr _ _ _ (by omega) le_rfl

/-! ## The load-bearing reduction: a nonzero term forces a zeroless `n` -/

/-- Digits of a one-step concatenation. -/
theorem digits_concatStep (acc d : ℕ) :
    Nat.digits 10 (concatStep acc d) = Nat.digits 10 d ++ Nat.digits 10 acc :=
  (Nat.digits_append_digits (by norm_num)).symm

/-- The digits of every concatenated block occur among the digits of the concatenation. -/
theorem digits_subset_foldl (l : List ℕ) (acc : ℕ) :
    Nat.digits 10 acc ⊆ Nat.digits 10 (l.foldl concatStep acc) ∧
      ∀ d ∈ l, Nat.digits 10 d ⊆ Nat.digits 10 (l.foldl concatStep acc) := by
  induction l generalizing acc with
  | nil => exact ⟨fun x hx => hx, fun d hd => absurd hd List.not_mem_nil⟩
  | cons x l ih =>
    obtain ⟨ih1, ih2⟩ := ih (concatStep acc x)
    rw [digits_concatStep] at ih1
    refine ⟨fun y hy => ih1 (List.mem_append_right _ hy), ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact fun y hy => ih1 (List.mem_append_left _ hy)
    · exact ih2 d hd

/-- If `n ≥ 1` has a decimal digit `0`, so does the concatenation of its divisors. -/
theorem zero_mem_digits_concatDivisors {n : ℕ} (hn : 0 < n) (h0 : 0 ∈ Nat.digits 10 n) :
    0 ∈ Nat.digits 10 (concatDivisors n) := by
  have hmem : n ∈ divisorList n := by
    simp only [divisorList, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
    exact ⟨⟨hn, by omega⟩, dvd_rfl⟩
  exact (digits_subset_foldl (divisorList n) 0).2 n hmem h0

/-- `mdrFuel` fixes `0`. -/
theorem mdrFuel_zero (k : ℕ) : mdrFuel k 0 = 0 := by
  cases k <;> simp [mdrFuel]

/-- A number with a decimal digit `0` has multiplicative digital root `0`. -/
theorem mdr_eq_zero_of_zero_mem_digits {m : ℕ} (h : 0 ∈ Nat.digits 10 m) : mdr m = 0 := by
  have hm10 : 10 ≤ m := by
    by_contra hlt
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at h
    · rw [Nat.digits_of_lt 10 m (by omega) (by omega), List.mem_singleton] at h
      omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold mdr
  rw [mdrFuel, if_neg (by omega), List.prod_eq_zero h, mdrFuel_zero]

/-- If `a n ≠ 0` with `n ≥ 1`, then `n` has no decimal digit `0`. -/
theorem zero_not_mem_digits_of_a_ne_zero {n : ℕ} (hn : 0 < n) (h : a n ≠ 0) :
    0 ∉ Nat.digits 10 n := fun h0 =>
  h (mdr_eq_zero_of_zero_mem_digits (zero_mem_digits_concatDivisors hn h0))

/-! ## Zeroless numbers are sparse -/

/-- The numbers below `10 ^ k` whose decimal digits contain no `0` (including `0` itself,
whose digit list is empty). -/
def zeroless (k : ℕ) : Finset ℕ := (Finset.range (10 ^ k)).filter (fun n => 0 ∉ Nat.digits 10 n)

/-- Recursive count: `8 · #zeroless k + 1 ≤ 9 ^ (k + 1)`. -/
theorem card_zeroless_le (k : ℕ) : 8 * (zeroless k).card + 1 ≤ 9 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hsub : zeroless (k + 1) ⊆ insert 0 (((zeroless k) ×ˢ Finset.Icc 1 9).image
        (fun p : ℕ × ℕ => 10 * p.1 + p.2)) := by
      intro n hn
      simp only [zeroless, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hlt, h0⟩ := hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rw [Nat.digits_def' (by norm_num) hpos, List.mem_cons, not_or] at h0
        obtain ⟨hmod, hdiv⟩ := h0
        refine Finset.mem_image.mpr ⟨(n / 10, n % 10), ?_, ?_⟩
        · simp only [zeroless, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
            Finset.mem_Icc]
          refine ⟨⟨?_, hdiv⟩, by omega, by omega⟩
          rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
          exact hlt
        · exact Nat.div_add_mod n 10
    have hcard : (zeroless (k + 1)).card ≤ (zeroless k).card * 9 + 1 := by
      calc (zeroless (k + 1)).card
          ≤ (insert 0 (((zeroless k) ×ˢ Finset.Icc 1 9).image
              (fun p : ℕ × ℕ => 10 * p.1 + p.2))).card := Finset.card_le_card hsub
        _ ≤ (((zeroless k) ×ˢ Finset.Icc 1 9).image
              (fun p : ℕ × ℕ => 10 * p.1 + p.2)).card + 1 := Finset.card_insert_le _ _
        _ ≤ ((zeroless k) ×ˢ Finset.Icc 1 9).card + 1 := by
          gcongr
          exact Finset.card_image_le
        _ = (zeroless k).card * 9 + 1 := by
          rw [Finset.card_product, Nat.card_Icc]
    calc 8 * (zeroless (k + 1)).card + 1 ≤ 9 * (8 * (zeroless k).card + 1) := by omega
      _ ≤ 9 * 9 ^ (k + 1) := Nat.mul_le_mul_left 9 ih
      _ = 9 ^ (k + 1 + 1) := by ring

/-- The count of `n ∈ [1, N]` with `a n ≠ 0` is bounded by the zeroless count below
`10 ^ (log₁₀ N + 1)`. -/
theorem card_bad_le_zeroless (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => a n ≠ 0)).card ≤ (zeroless (Nat.log 10 N + 1)).card := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨h1, hN⟩, ha⟩ := hn
  simp only [zeroless, Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_le_of_lt hN (Nat.lt_pow_succ_log_self (by norm_num) N),
    zero_not_mem_digits_of_a_ne_zero h1 ha⟩

/-- Real-valued density bound: for `N ≥ 1`,
`#{n ∈ [1, N] | a n ≠ 0} / N ≤ (81 / 8) · (9 / 10) ^ log₁₀ N`. -/
theorem density_bound (N : ℕ) (hN : 0 < N) :
    (((Finset.Icc 1 N).filter (fun n => a n ≠ 0)).card : ℝ) / N ≤
      81 / 8 * (9 / 10 : ℝ) ^ Nat.log 10 N := by
  set L := Nat.log 10 N with hL
  set c := ((Finset.Icc 1 N).filter (fun n => a n ≠ 0)).card with hc
  have hcz : (8 * c : ℝ) ≤ 9 ^ (L + 2) := by
    have h1 := card_bad_le_zeroless N
    have h2 : 8 * (zeroless (L + 1)).card + 1 ≤ 9 ^ (L + 2) := card_zeroless_le (L + 1)
    rw [← hL, ← hc] at h1
    have h3 : 8 * c ≤ 9 ^ (L + 2) := by omega
    exact_mod_cast h3
  have hNL : (10 : ℝ) ^ L ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 10 hN.ne'
  have hpos : (0 : ℝ) < 10 ^ L := by positivity
  calc (c : ℝ) / N ≤ c / 10 ^ L := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hNL
    _ ≤ (9 ^ (L + 2) / 8) / 10 ^ L := by
        apply div_le_div_of_nonneg_right _ hpos.le
        linarith
    _ = 81 / 8 * (9 / 10 : ℝ) ^ L := by
        rw [div_pow, pow_add]
        field_simp
        ring

/-- `log₁₀ N → ∞` as `N → ∞`. -/
theorem tendsto_log_ten : Tendsto (Nat.log 10) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨10 ^ b, fun _ hn => Nat.le_log_of_pow_le (by norm_num) hn⟩

/-! ## The conjecture -/

/-- **A231817 conjecture.** "Conjecture: a(n) = 0 for almost all n." The set of `n ≥ 1`
whose multiplicative digital root of the concatenation of divisors is nonzero has natural
density `0`: `#{n ∈ [1, N] | a n ≠ 0} / N → 0`. -/
theorem a231817_density_zero :
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => a n ≠ 0)).card : ℝ) / N)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => 81 / 8 * (9 / 10 : ℝ) ^ Nat.log 10 N) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (9 / 10 : ℝ)) (by norm_num)
      (by norm_num)).comp tendsto_log_ten).const_mul (81 / 8)
    rw [mul_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact density_bound N hN

end Candidates.A231817MultiplicativeDigitalRoot
