/-
# A156703 — McEachen: exactly 2d+1 terms have d digits

## OEIS source (re-pulled with `oeis show A156703` and the live entry, 2026-10-21)

```
NAME:     String of digits encountered in decimal expansion of successive
          ratios k/(k+1), treating only non-repeating expansions, with decimal
          point and leading and trailing zeros removed.
OFFSET:   1
TERMS:    5,75,8,875,9,9375,95,96,96875,975,98,984375,9875,99,992,9921875,
          99375,995,996,99609375,996875,9975,998,998046875,9984,9984375,...
KEYWORDS: easy,nonn,base
AUTHOR:   Bill McEachen, Feb 13 2009
COMMENT (the conjecture, unsigned, hence the author's, Feb 13 2009):
  Conjecture: subsets of the sequence (as it fills out) will correspond to the
  odd integers by length.
  Thus, there are 3 single-digit entries in range {1-9}, ending at 9; 5
  two-digit entries in range {10-99} ending at 99; 7 three-digit entries in
  range {100-999} ending at 999, etc. The remainder set of course are all
  repeating decimals.
FORMULA:
  a(n) = 10^d*(k-1)/k where k = A003592(n+1) = 2^i*5^j and d=max(i,j).
  - _Robert Israel_, Dec 29 2015
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell), although it is an elementary consequence of Israel's formula.
This module proves it with no `sorry`.

Computation (Python, exact `Fraction` arithmetic, all ratios k/(k+1) with
k < 10^6): the counts of d-digit terms are 3, 5, 7, 9, 11, 13 for d = 1..6,
and the largest d-digit term is 10^d - 1.

## Formalization

* `Terminates q`: some `q * 10^m` is a natural number (the decimal
  expansion of `q ≥ 0` is non-repeating).
* `decimalString q`: `q * 10^m` for the least such `m`; this is the digit
  string with the decimal point and the leading and trailing zeros removed.
* `IsTerminatingIndex k`: `1 ≤ k` and `k/(k+1)` terminates.
* `a n`: `decimalString` of `k/(k+1)` for the `n`-th (0-indexed)
  terminating index `k`; so `a n` is OEIS `a(n+1)`.

The proof does not use the `2^i 5^j` parametrisation. With `K = k + 1`
and `D` the least `m` such that `K ∣ 10^m`, the term equals
`k * (10^D / K)`, which lies in `[10^(D-1), 10^D)`, so it has `D` digits.
`D = d` holds exactly when `K` divides `10^d` but not `10^(d-1)`. There are
`(d+1)^2 - d^2 = 2d+1` such divisors `K`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A156703ExactlyDigitsOne

/-- The decimal expansion of `q` is non-repeating (terminating): `q * 10^m` is a natural
number for some `m`. Intended for `0 ≤ q`. -/
def Terminates (q : ℚ) : Prop := ∃ m N : ℕ, q * 10 ^ m = N

/-- The decimal digit string of a terminating `q ∈ [0, 1)` with the decimal point and the
leading and trailing zeros removed, read as a natural number: `q * 10^m` for the least `m`
making it a natural number (the least `m` removes the trailing zeros; leading zeros do not
change the value). Off terminating `q` the value is junk; it is used only on terminating `q`. -/
noncomputable def decimalString (q : ℚ) : ℕ :=
  ⌊q * 10 ^ sInf {m : ℕ | ∃ N : ℕ, q * 10 ^ m = N}⌋₊

/-- `k` indexes a ratio of the entry: `1 ≤ k` and `k/(k+1)` has a non-repeating
decimal expansion. -/
def IsTerminatingIndex (k : ℕ) : Prop := 1 ≤ k ∧ Terminates ((k : ℚ) / (k + 1))

/-- A156703, 0-indexed: `a n` is OEIS `a(n+1)`, the digit string of `k/(k+1)` for the
`n`-th (0-indexed) index `k` whose ratio `k/(k+1)` has a non-repeating expansion. -/
noncomputable def a (n : ℕ) : ℕ :=
  decimalString ((Nat.nth IsTerminatingIndex n : ℚ) / (Nat.nth IsTerminatingIndex n + 1))

/-- `k/(k+1) * 10^m` is a natural number iff `k + 1 ∣ 10^m`. -/
theorem ratio_mul_pow_eq_nat_iff (k m : ℕ) :
    (∃ N : ℕ, (k : ℚ) / (k + 1) * 10 ^ m = N) ↔ (k + 1) ∣ 10 ^ m := by
  have hK : ((k : ℚ) + 1) ≠ 0 := by positivity
  constructor
  · rintro ⟨N, hN⟩
    have hq : ((k * 10 ^ m : ℕ) : ℚ) = ((N * (k + 1) : ℕ) : ℚ) := by
      push_cast
      field_simp at hN
      linarith
    have hnat : k * 10 ^ m = N * (k + 1) := by exact_mod_cast hq
    have hdvd : (k + 1) ∣ k * 10 ^ m := ⟨N, by rw [hnat]; ring⟩
    have hcop : Nat.Coprime (k + 1) k := by
      simp
    exact hcop.dvd_of_dvd_mul_left hdvd
  · rintro ⟨c, hc⟩
    refine ⟨k * c, ?_⟩
    have hc' : ((10 : ℚ) ^ m) = ((k : ℚ) + 1) * c := by exact_mod_cast hc
    rw [hc']
    push_cast
    field_simp

/-- A positive `K` dividing some power of ten divides `10^(K-1)`. -/
theorem dvd_ten_pow_pred_of_dvd_ten_pow {K m : ℕ} (hK : K ≠ 0) (h : K ∣ 10 ^ m) :
    K ∣ 10 ^ (K - 1) := by
  have h10 : (10 : ℕ) ^ (K - 1) ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hK h10]
  have hle := (Nat.factorization_le_iff_dvd hK (by positivity)).mpr h
  intro p
  have hp := hle p
  rw [Nat.factorization_pow] at hp ⊢
  simp only [Finsupp.smul_apply, smul_eq_mul] at hp ⊢
  have hlt := Nat.factorization_lt p hK
  rcases Nat.eq_zero_or_pos ((10 : ℕ).factorization p) with h0 | h0
  · rw [h0] at hp
    omega
  · calc K.factorization p ≤ K - 1 := by omega
      _ ≤ (K - 1) * (10 : ℕ).factorization p := Nat.le_mul_of_pos_right _ h0


/-- For terminating `k/(k+1)`, the digit string is `k * (10^D / (k+1))`, where `D` is the
least `m` with `k + 1 ∣ 10^m` (Israel's formula). -/
theorem decimalString_ratio (k : ℕ) (h : ∃ m, (k + 1) ∣ 10 ^ m) :
    decimalString ((k : ℚ) / (k + 1)) = k * (10 ^ sInf {m : ℕ | (k + 1) ∣ 10 ^ m} / (k + 1)) := by
  have hset : {m : ℕ | ∃ N : ℕ, (k : ℚ) / (k + 1) * 10 ^ m = N} = {m : ℕ | (k + 1) ∣ 10 ^ m} :=
    Set.ext fun m => ratio_mul_pow_eq_nat_iff k m
  unfold decimalString
  rw [hset]
  set D := sInf {m : ℕ | (k + 1) ∣ 10 ^ m} with hDdef
  have hD : (k + 1) ∣ 10 ^ D := Nat.sInf_mem h
  obtain ⟨c, hc⟩ := hD
  have hdiv : 10 ^ D / (k + 1) = c := by
    rw [hc]; exact Nat.mul_div_cancel_left c (Nat.succ_pos k)
  have hc' : ((10 : ℚ) ^ D) = ((k : ℚ) + 1) * c := by exact_mod_cast hc
  have hK : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hval : (k : ℚ) / (k + 1) * 10 ^ D = ((k * c : ℕ) : ℚ) := by
    rw [hc']; push_cast; field_simp
  rw [hval, Nat.floor_natCast, hdiv]

/-- For `1 ≤ d`, the least `m` with `K ∣ 10^m` equals `d` iff `K ∣ 10^d` and
`¬ K ∣ 10^(d-1)`. -/
theorem sInf_eq_iff {K d : ℕ} (hd : 1 ≤ d) :
    sInf {m : ℕ | K ∣ 10 ^ m} = d ↔ K ∣ 10 ^ d ∧ ¬ K ∣ 10 ^ (d - 1) := by
  constructor
  · intro hD
    have hne : ({m : ℕ | K ∣ 10 ^ m}).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Nat.sInf_empty] at hD
      omega
    refine ⟨hD ▸ Nat.sInf_mem hne, fun hlt => ?_⟩
    have := Nat.sInf_le (show d - 1 ∈ {m : ℕ | K ∣ 10 ^ m} from hlt)
    omega
  · rintro ⟨hdvd, hndvd⟩
    have hle : sInf {m : ℕ | K ∣ 10 ^ m} ≤ d := Nat.sInf_le hdvd
    have hmem : K ∣ 10 ^ sInf {m : ℕ | K ∣ 10 ^ m} := Nat.sInf_mem (s := {m : ℕ | K ∣ 10 ^ m}) ⟨d, hdvd⟩
    by_contra hneq
    exact hndvd (hmem.trans (pow_dvd_pow 10 (by omega)))

/-- For `1 ≤ k` with `k/(k+1)` terminating, the digit string has exactly `D` decimal digits,
where `D` is the least `m` with `k + 1 ∣ 10^m`. -/
theorem length_digits_decimalString_ratio {k : ℕ} (hk : 1 ≤ k) (h : ∃ m, (k + 1) ∣ 10 ^ m) :
    (Nat.digits 10 (decimalString ((k : ℚ) / (k + 1)))).length =
      sInf {m : ℕ | (k + 1) ∣ 10 ^ m} := by
  rw [decimalString_ratio k h]
  set D := sInf {m : ℕ | (k + 1) ∣ 10 ^ m} with hDdef
  have hD : (k + 1) ∣ 10 ^ D := Nat.sInf_mem h
  obtain ⟨c, hc⟩ := hD
  have hdiv : 10 ^ D / (k + 1) = c := by
    rw [hc]; exact Nat.mul_div_cancel_left c (Nat.succ_pos k)
  rw [hdiv]
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc; exact absurd hc (by positivity)
    · exact h0
  have hDpos : 1 ≤ D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, pow_zero] at hc
      have := Nat.eq_one_of_mul_eq_one_right hc.symm
      omega
    · exact h0
  have hpow : (10 : ℕ) ^ D = 10 * 10 ^ (D - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hupper : k * c < 10 ^ D := by rw [hc]; nlinarith
  have hlower : 10 ^ (D - 1) ≤ k * c := by nlinarith
  apply le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num) _).mpr hupper
  · have := (Nat.lt_digits_length_iff (b := 10) (k := D - 1) (by norm_num) (k * c)).mpr hlower
    omega


/-- `k` is an index of the entry iff `1 ≤ k` and `k + 1` divides a power of ten (that is,
`k + 1` lies in A003592). -/
theorem isTerminatingIndex_iff (k : ℕ) :
    IsTerminatingIndex k ↔ 1 ≤ k ∧ ∃ m, (k + 1) ∣ 10 ^ m := by
  unfold IsTerminatingIndex Terminates
  constructor
  · rintro ⟨hk, m, hm⟩
    exact ⟨hk, m, (ratio_mul_pow_eq_nat_iff k m).mp hm⟩
  · rintro ⟨hk, m, hm⟩
    exact ⟨hk, m, (ratio_mul_pow_eq_nat_iff k m).mpr hm⟩

/-- There are infinitely many indices (all `10^t - 1` with `t ≥ 1`), so `Nat.nth` enumerates
them bijectively. -/
theorem infinite_isTerminatingIndex : (Set.ofPred IsTerminatingIndex).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  have hlt : n + 1 < 10 ^ (n + 1) := Nat.lt_pow_self (by norm_num)
  refine ⟨10 ^ (n + 1) - 1, ?_, by omega⟩
  show IsTerminatingIndex (10 ^ (n + 1) - 1)
  rw [isTerminatingIndex_iff]
  refine ⟨by omega, n + 1, ?_⟩
  rw [Nat.sub_add_cancel (by omega)]

/-- `10^d` has `(d+1)^2` divisors. -/
theorem card_divisors_ten_pow (d : ℕ) : (Nat.divisors (10 ^ d)).card = (d + 1) ^ 2 := by
  have h10 : (10 : ℕ) ^ d = 2 ^ d * 5 ^ d := by rw [← mul_pow]; norm_num
  have hcop : Nat.Coprime (2 ^ d) (5 ^ d) := Nat.Coprime.pow d d (by norm_num)
  rw [h10, Nat.Coprime.card_divisors_mul hcop, Nat.divisors_prime_pow Nat.prime_two,
    Nat.divisors_prime_pow (by norm_num : Nat.Prime 5)]
  simp only [Finset.card_map, Finset.card_range]
  ring

/-- For `1 ≤ d`, exactly `2d + 1` divisors of `10^d` do not divide `10^(d-1)`. -/
theorem card_sdiff_divisors_ten_pow {d : ℕ} (hd : 1 ≤ d) :
    ((Nat.divisors (10 ^ d)) \ (Nat.divisors (10 ^ (d - 1)))).card = 2 * d + 1 := by
  have hsub : Nat.divisors (10 ^ (d - 1)) ⊆ Nat.divisors (10 ^ d) :=
    Nat.divisors_subset_of_dvd (by positivity) (pow_dvd_pow 10 (by omega))
  rw [Finset.card_sdiff_of_subset hsub, card_divisors_ten_pow, card_divisors_ten_pow]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.sub_eq_of_eq_add]
  ring

/-- Decidable form of the index predicate: `1 ≤ k` and `k + 1 ∣ 10^k`. -/
theorem isTerminatingIndex_iff_dvd_ten_pow_self (k : ℕ) :
    IsTerminatingIndex k ↔ 1 ≤ k ∧ (k + 1) ∣ 10 ^ k := by
  rw [isTerminatingIndex_iff]
  constructor
  · rintro ⟨hk, m, hm⟩
    exact ⟨hk, by simpa using dvd_ten_pow_pred_of_dvd_ten_pow (Nat.succ_ne_zero k) hm⟩
  · rintro ⟨hk, hm⟩
    exact ⟨hk, k, hm⟩

/-- Evaluation bridge for ground-truth checks: if `k` is the `n`-th index (by `Nat.count`)
and `m ≥ 1` is the least exponent with `k + 1 ∣ 10^m`, then `a n = k * (10^m / (k+1))`. -/
theorem a_eq_of_count (n k m : ℕ) (hm : 1 ≤ m)
    (hcount : Nat.count (fun j => 1 ≤ j ∧ (j + 1) ∣ 10 ^ j) k = n)
    (hk : 1 ≤ k ∧ (k + 1) ∣ 10 ^ k)
    (hdvd : (k + 1) ∣ 10 ^ m) (hndvd : ¬ (k + 1) ∣ 10 ^ (m - 1)) :
    a n = k * (10 ^ m / (k + 1)) := by
  have hpred : IsTerminatingIndex = fun j => 1 ≤ j ∧ (j + 1) ∣ 10 ^ j :=
    funext fun j => propext (isTerminatingIndex_iff_dvd_ten_pow_self j)
  have hnth : Nat.nth IsTerminatingIndex n = k := by
    rw [hpred, ← hcount]
    exact Nat.nth_count hk
  unfold a
  rw [hnth, decimalString_ratio k ⟨m, hdvd⟩, (sInf_eq_iff hm).mpr ⟨hdvd, hndvd⟩]


/-! ## Ground truth: the first ten listed terms `5, 75, 8, 875, 9, 9375, 95, 96, 96875, 975`. -/

example : a 0 = 5 :=
  (a_eq_of_count 0 1 1 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 1 = 75 :=
  (a_eq_of_count 1 3 2 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 2 = 8 :=
  (a_eq_of_count 2 4 1 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 3 = 875 :=
  (a_eq_of_count 3 7 3 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 4 = 9 :=
  (a_eq_of_count 4 9 1 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 5 = 9375 :=
  (a_eq_of_count 5 15 4 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 6 = 95 :=
  (a_eq_of_count 6 19 2 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 7 = 96 :=
  (a_eq_of_count 7 24 2 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 8 = 96875 :=
  (a_eq_of_count 8 31 5 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

example : a 9 = 975 :=
  (a_eq_of_count 9 39 3 (by norm_num) (by decide) (by decide) (by decide) (by decide)).trans
    (by norm_num)

/-- **McEachen's conjecture (A156703, Bill McEachen, Feb 13 2009).**

Verbatim: "Conjecture: subsets of the sequence (as it fills out) will correspond to the odd
integers by length. Thus, there are 3 single-digit entries in range {1-9}, ending at 9; 5
two-digit entries in range {10-99} ending at 99; 7 three-digit entries in range {100-999}
ending at 999, etc."

Formal claim: for every `d ≥ 1`, exactly `2d + 1` indices `n` give a term `a n` with `d`
decimal digits. `Set.ncard` is `0` on infinite sets, so the value `2d + 1 ≠ 0` also asserts
finiteness. The guard `1 ≤ d` is from the source; for `d = 0` the count is `0` (no term is
`0`). -/
theorem card_setOf_length_digits_a_eq (d : ℕ) (hd : 1 ≤ d) :
    {n : ℕ | (Nat.digits 10 (a n)).length = d}.ncard = 2 * d + 1 := by
  have hinf := infinite_isTerminatingIndex
  set F : Finset ℕ := (Nat.divisors (10 ^ d)) \ (Nat.divisors (10 ^ (d - 1))) with hF
  have himage : Nat.nth IsTerminatingIndex '' {n : ℕ | (Nat.digits 10 (a n)).length = d} =
      (fun K => K - 1) '' (F : Set ℕ) := by
    ext k
    have hkey : (∃ n, Nat.nth IsTerminatingIndex n = k ∧
        (Nat.digits 10 (a n)).length = d) ↔ k + 1 ∈ F := by
      constructor
      · rintro ⟨n, hnk, hlen⟩
        have hmem := Nat.nth_mem_of_infinite hinf n
        rw [hnk, isTerminatingIndex_iff] at hmem
        unfold a at hlen
        rw [hnk, length_digits_decimalString_ratio hmem.1 hmem.2, sInf_eq_iff hd] at hlen
        rw [hF, Finset.mem_sdiff, Nat.mem_divisors, Nat.mem_divisors]
        exact ⟨⟨hlen.1, by positivity⟩, fun h => hlen.2 h.1⟩
      · intro hkF
        rw [hF, Finset.mem_sdiff, Nat.mem_divisors, Nat.mem_divisors] at hkF
        have hdvd : (k + 1) ∣ 10 ^ d := hkF.1.1
        have hndvd : ¬ (k + 1) ∣ 10 ^ (d - 1) := fun h => hkF.2 ⟨h, by positivity⟩
        have hk : 1 ≤ k := by
          by_contra hk0
          have hk0' : k = 0 := by omega
          exact hndvd (by rw [hk0']; exact one_dvd _)
        have hterm : IsTerminatingIndex k := (isTerminatingIndex_iff k).mpr ⟨hk, d, hdvd⟩
        have hrange : k ∈ Set.range (Nat.nth IsTerminatingIndex) := by
          rw [Nat.range_nth_of_infinite hinf]; exact hterm
        obtain ⟨n, hn⟩ := hrange
        refine ⟨n, hn, ?_⟩
        unfold a
        rw [hn, length_digits_decimalString_ratio hk ⟨d, hdvd⟩, sInf_eq_iff hd]
        exact ⟨hdvd, hndvd⟩
    constructor
    · rintro ⟨n, hlen, hnk⟩
      exact ⟨k + 1, hkey.mp ⟨n, hnk, hlen⟩, by simp⟩
    · rintro ⟨K, hKF, rfl⟩
      have hK0 : K ≠ 0 := by
        intro h0
        rw [h0] at hKF
        simp [hF] at hKF
      have hK : K - 1 + 1 = K := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hK0)
      obtain ⟨n, hnk, hlen⟩ := hkey.mpr (by rw [hK]; exact hKF)
      exact ⟨n, hlen, hnk⟩
  have hinj : Set.InjOn (fun K : ℕ => K - 1) (F : Set ℕ) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0] at hx; simp [hF] at hx
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0] at hy; simp [hF] at hy
    simp only at hxy
    omega
  rw [← Set.ncard_image_of_injective _ (Nat.nth_injective hinf), himage,
    hinj.ncard_image, Set.ncard_coe_finset, hF, card_sdiff_divisors_ten_pow hd]

/-- Non-vacuity at `d = 1`: the three one-digit terms `5, 8, 9`. -/
example : {n : ℕ | (Nat.digits 10 (a n)).length = 1}.ncard = 3 :=
  card_setOf_length_digits_a_eq 1 le_rfl

end Candidates.A156703ExactlyDigitsOne
