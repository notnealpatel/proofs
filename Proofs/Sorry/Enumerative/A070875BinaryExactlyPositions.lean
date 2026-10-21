/-
# A070875 — Beck: the ones of A309019 - A002487 sit exactly at A070875

## OEIS source (retrieved with `oeis show A070875`, 2026-10-21)

```
NAME:     Binary expansion is 1x100...0 where x = 0 or 1.
TERMS:    5,7,10,14,20,28,40,56,80,112,160,224,320,448,640,896,1280,1792,2560,
          3584,5120,7168,10240,14336,20480,28672,40960,57344,81920,114688,...
KEYWORDS: nonn,base,easy
PROGRAM:  (PARI) a(n)=if(n%2,7,5)<<(n\2) \\ _Charles R Greathouse IV_, Sep 24 2012
COMMENT (the conjecture):
  Conjecture: a(n) = -1 + positions of the ones in A309019(n+2) - A002487(n+2).
  - _George Beck_, Mar 26 2022
```

Companion entries (same retrieval):

* A002487 (Stern's diatomic series): `a(0) = 0, a(1) = 1; for n > 0:
  a(2*n) = a(n), a(2*n+1) = a(n) + a(n+1)`.
* A309019: NAME `Expansion of x * Product_{k>=0} (1 + x^(2^k) + x^(2^(k+1)) +
  x^(2^(k+2)))`; FORMULA `a(0) = 0, a(1) = 1; a(2*n) = a(n),
  a(2*n+1) = a(n-1) + a(n) + a(n+1)`.

## Status

Triage: open (no proof in the entry or the literature found by triage).
The triage checked `m < 32768`; this campaign re-checked `m < 2^20` and also
checked the A309019 product NAME against the FORMULA recurrence for `m ≤ 200`
(Python, evidence only).  This module proves the conjecture in full.

## Reading of the index shift

Taken literally ("positions" of `A309019(n+2) - A002487(n+2)`, offset 0) the
comment does not match the data; the triage records this as a convention
mismatch.  The data fit the reading in which the difference sequence
`D(m) = A309019(m) - A002487(m)` is listed from `m = 0` and positions are
1-based (Mathematica `Position`), so "`-1 + position`" is the index `m` itself:
the `n`-th (0-based) index `m` with `D(m) = 1` is `A070875(n)`.  This is the
statement proved (`a070875_conjecture`), together with the set form
(`a309019_sub_stern_eq_one_iff_mem_range`).

## Proof outline

Write `t = A309019`, `s = A002487`, `D = t - s` (in `ℤ`).  The recurrences give
`D(2n) = D(n)` and, for `n ≥ 1`, `D(2n+1) = D(n) + D(n+1) + t(n-1)`.  Since
`t(k) ≥ 1` for `k ≥ 1`, induction gives `D ≥ 0` and `D(2n+1) = 0 → n ≤ 1`.
If `D(2n+1) = 1` then `n ≥ 2` (as `D(1) = D(3) = 0`), so `D(n) = D(n+1) = 0`;
the odd one of `n, n+1` is then `1` or `3`, so `n ∈ {2, 3}` and `2n+1 ∈ {5, 7}`.
With `D(2n) = D(n)`, `D(m) = 1 ↔ m ∈ {5·2^k, 7·2^k}`, which is the range of
A070875; `A070875` is strictly increasing, so it enumerates these `m` in order.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A070875BinaryExactlyPositions

/-! ## Definition layer -/

/-- Stern's diatomic series A002487: `s(0) = 0`, `s(1) = 1`, `s(2n) = s(n)`,
`s(2n+1) = s(n) + s(n+1)` (the entry's NAME). -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then stern ((n + 2) / 2)
    else stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
termination_by m => m
decreasing_by all_goals omega

/-- A309019 by the entry's FORMULA: `a(0) = 0`, `a(1) = 1`, `a(2n) = a(n)`,
`a(2n+1) = a(n-1) + a(n) + a(n+1)` (for `n ≥ 1`).  The entry's NAME is the
coefficient sequence of `x * Π_{k ≥ 0} (1 + x^(2^k) + x^(2^(k+1)) + x^(2^(k+2)))`;
the recurrence is checked below against all 91 listed terms. -/
def a309019 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then a309019 ((n + 2) / 2)
    else a309019 ((n + 2) / 2 - 1) + a309019 ((n + 2) / 2) + a309019 ((n + 2) / 2 + 1)
termination_by m => m
decreasing_by all_goals omega

/-- A070875 (offset 0), by the entry's PARI program `if(n%2,7,5)<<(n\2)`:
`a(2k) = 5·2^k`, `a(2k+1) = 7·2^k`.  The bridge to the NAME ("binary expansion
is `1x10...0`") is `mem_range_a070875_iff_digits`. -/
def a070875 (n : ℕ) : ℕ := (if n % 2 = 1 then 7 else 5) * 2 ^ (n / 2)

/-- The difference `A309019(m) - A002487(m)`, computed in `ℤ`. -/
def a309019SubStern (m : ℕ) : ℤ := (a309019 m : ℤ) - (stern m : ℤ)

/-! ## Ground truth against the listed terms -/

example : (List.range 91).map stern =
    [0,1,1,2,1,3,2,3,1,4,3,5,2,5,3,4,1,5,4,7,3,8,5,7,2,7,5,8,3,7,4,5,1,6,5,9,4,11,7,
     10,3,11,8,13,5,12,7,9,2,9,7,12,5,13,8,11,3,10,7,11,4,9,5,6,1,7,6,11,5,14,9,13,4,
     15,11,18,7,17,10,13,3,14,11,19,8,21,13,18,5,17,12] := by decide +kernel

example : (List.range 91).map a309019 =
    [0,1,1,2,1,4,2,4,1,7,4,7,2,10,4,7,1,12,7,12,4,18,7,13,2,19,10,16,4,21,7,12,1,20,
     12,20,7,31,12,23,4,34,18,29,7,38,13,22,2,34,19,31,10,45,16,30,4,41,21,32,7,40,12,
     20,1,33,20,33,12,52,20,39,7,58,31,50,12,66,23,39,4,61,34,56,18,81,29,54,7,74,38] := by
  decide +kernel

example : (List.range 42).map a070875 =
    [5,7,10,14,20,28,40,56,80,112,160,224,320,448,640,896,1280,1792,2560,3584,5120,7168,
     10240,14336,20480,28672,40960,57344,81920,114688,163840,229376,327680,458752,655360,
     917504,1310720,1835008,2621440,3670016,5242880,7340032] := by decide

example : (List.range 16).map a309019SubStern = [0,0,0,0,0,1,0,1,0,3,1,2,0,5,1,3] := by
  decide +kernel

/-! ## Recurrences -/

/-- `A002487(2n) = A002487(n)`. -/
theorem stern_two_mul (n : ℕ) : stern (2 * n) = stern n := by
  rcases n with _ | n
  · rfl
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, stern]
    rw [if_pos (by omega), show (2 * n + 2) / 2 = n + 1 by omega]

/-- `A002487(2n+1) = A002487(n) + A002487(n+1)`. -/
theorem stern_two_mul_add_one (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, stern]
    rw [if_neg (by omega), show (2 * n + 1 + 2) / 2 = n + 1 by omega]

/-- `A309019(2n) = A309019(n)`. -/
theorem a309019_two_mul (n : ℕ) : a309019 (2 * n) = a309019 n := by
  rcases n with _ | n
  · rfl
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, a309019]
    rw [if_pos (by omega), show (2 * n + 2) / 2 = n + 1 by omega]

/-- `A309019(2n+1) = A309019(n-1) + A309019(n) + A309019(n+1)` for `n ≥ 1`. -/
theorem a309019_two_mul_add_one (n : ℕ) (hn : 1 ≤ n) :
    a309019 (2 * n + 1) = a309019 (n - 1) + a309019 n + a309019 (n + 1) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, a309019]
  rw [if_neg (by omega), show (2 * n + 1 + 2) / 2 = n + 1 by omega]

/-! ## The difference `D = A309019 - A002487` -/

/-- `D(2n) = D(n)` for `D = A309019 - A002487`. -/
theorem a309019SubStern_two_mul (n : ℕ) :
    a309019SubStern (2 * n) = a309019SubStern n := by
  simp only [a309019SubStern, stern_two_mul, a309019_two_mul]

/-- `D(2n+1) = D(n) + D(n+1) + A309019(n-1)` for `n ≥ 1`. -/
theorem a309019SubStern_two_mul_add_one (n : ℕ) (hn : 1 ≤ n) :
    a309019SubStern (2 * n + 1) =
      a309019SubStern n + a309019SubStern (n + 1) + a309019 (n - 1) := by
  simp only [a309019SubStern, stern_two_mul_add_one, a309019_two_mul_add_one n hn]
  push_cast; ring

/-- `A309019(m) ≥ 1` for every `m ≥ 1`. -/
theorem a309019_pos (m : ℕ) (hm : 0 < m) : 0 < a309019 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [a309019_two_mul]; exact ih n (by omega) (by omega)
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [a309019]
      · rw [a309019_two_mul_add_one n hn]
        have := ih n (by omega) hn
        omega

/-- `A002487(m) ≤ A309019(m)`, i.e. `D(m) ≥ 0`. -/
theorem a309019SubStern_nonneg (m : ℕ) : 0 ≤ a309019SubStern m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [a309019SubStern, a309019, stern]
      · rw [a309019SubStern_two_mul]; exact ih n (by omega)
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [a309019SubStern, a309019, stern]
      · rw [a309019SubStern_two_mul_add_one n hn]
        have h1 := ih n (by omega)
        have h2 := ih (n + 1) (by omega)
        positivity

/-- The only odd zeros of `D` are `1` and `3`: `D(2n+1) = 0 → n ≤ 1`. -/
theorem le_one_of_a309019SubStern_odd_eq_zero (n : ℕ)
    (h : a309019SubStern (2 * n + 1) = 0) : n ≤ 1 := by
  by_contra hn
  rw [not_le] at hn
  rw [a309019SubStern_two_mul_add_one n (by omega)] at h
  have h1 := a309019SubStern_nonneg n
  have h2 := a309019SubStern_nonneg (n + 1)
  have h3 : (0 : ℤ) < a309019 (n - 1) := by exact_mod_cast a309019_pos (n - 1) (by omega)
  linarith

/-- The only odd `m` with `D(m) = 1` are `5` and `7`: `D(2n+1) = 1 → n = 2 ∨ n = 3`. -/
theorem eq_two_or_eq_three_of_a309019SubStern_odd_eq_one (n : ℕ)
    (h : a309019SubStern (2 * n + 1) = 1) : n = 2 ∨ n = 3 := by
  have hn : 2 ≤ n := by
    by_contra hn
    interval_cases n <;> simp [a309019SubStern, a309019, stern] at h
  rw [a309019SubStern_two_mul_add_one n (by omega)] at h
  have h1 := a309019SubStern_nonneg n
  have h2 := a309019SubStern_nonneg (n + 1)
  have h3 : (0 : ℤ) < a309019 (n - 1) := by exact_mod_cast a309019_pos (n - 1) (by omega)
  have hz1 : a309019SubStern n = 0 := by linarith
  have hz2 : a309019SubStern (n + 1) = 0 := by linarith
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · have := le_one_of_a309019SubStern_odd_eq_zero j hz2
    omega
  · have := le_one_of_a309019SubStern_odd_eq_zero j hz1
    omega

/-- `D(m) = 1` exactly when `m = 5·2^k` or `m = 7·2^k`. -/
theorem a309019SubStern_eq_one_iff (m : ℕ) :
    a309019SubStern m = 1 ↔ ∃ k, m = 5 * 2 ^ k ∨ m = 7 * 2 ^ k := by
  constructor
  · induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro h
      obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [a309019SubStern, a309019, stern] at h
        · rw [a309019SubStern_two_mul] at h
          obtain ⟨k, hk | hk⟩ := ih n (by omega) h
          · exact ⟨k + 1, Or.inl (by rw [hk]; ring)⟩
          · exact ⟨k + 1, Or.inr (by rw [hk]; ring)⟩
      · rcases eq_two_or_eq_three_of_a309019SubStern_odd_eq_one n h with rfl | rfl
        · exact ⟨0, Or.inl rfl⟩
        · exact ⟨0, Or.inr rfl⟩
  · rintro ⟨k, rfl | rfl⟩
    · induction k with
      | zero => decide +kernel
      | succ k ih =>
        rw [pow_succ, ← mul_assoc, mul_comm _ 2, a309019SubStern_two_mul]
        exact ih
    · induction k with
      | zero => decide +kernel
      | succ k ih =>
        rw [pow_succ, ← mul_assoc, mul_comm _ 2, a309019SubStern_two_mul]
        exact ih

/-- The terms of A070875 are exactly the numbers `5·2^k` and `7·2^k`. -/
theorem mem_range_a070875_iff (m : ℕ) :
    m ∈ Set.range a070875 ↔ ∃ k, m = 5 * 2 ^ k ∨ m = 7 * 2 ^ k := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n / 2, ?_⟩
    unfold a070875
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro ⟨k, rfl | rfl⟩
    · refine ⟨2 * k, ?_⟩
      simp [a070875]
    · refine ⟨2 * k + 1, ?_⟩
      simp only [a070875]
      rw [if_pos (by omega), show (2 * k + 1) / 2 = k by omega]

/-- Bridge to the NAME of A070875: `m` is a term iff its binary expansion
(little-endian `Nat.digits 2`) is `0^k` followed by `1, x, 1` with `x ≤ 1`,
i.e. `m` reads `1x10...0` in binary. -/
theorem mem_range_a070875_iff_digits (m : ℕ) :
    m ∈ Set.range a070875 ↔
      ∃ k x, x ≤ 1 ∧ Nat.digits 2 m = List.replicate k 0 ++ [1, x, 1] := by
  rw [mem_range_a070875_iff]
  have hval (k x : ℕ) :
      Nat.ofDigits 2 (List.replicate k 0 ++ [1, x, 1]) = (5 + 2 * x) * 2 ^ k := by
    rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate]
    simp only [Nat.ofDigits, Nat.cast_one, Nat.cast_id, mul_zero, add_zero, mul_one,
      zero_add]
    ring
  constructor
  · rintro ⟨k, rfl | rfl⟩
    · refine ⟨k, 0, zero_le_one, ?_⟩
      rw [show 5 * 2 ^ k = Nat.ofDigits 2 (List.replicate k 0 ++ [1, 0, 1]) by rw [hval]]
      apply Nat.digits_ofDigits 2 (by norm_num)
      · intro l hl
        simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
          or_false] at hl
        omega
      · intro _; simp
    · refine ⟨k, 1, le_refl 1, ?_⟩
      rw [show 7 * 2 ^ k = Nat.ofDigits 2 (List.replicate k 0 ++ [1, 1, 1]) by rw [hval]]
      apply Nat.digits_ofDigits 2 (by norm_num)
      · intro l hl
        simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
          or_false] at hl
        omega
      · intro _; simp
  · rintro ⟨k, x, hx, hd⟩
    have hm : m = (5 + 2 * x) * 2 ^ k := by
      rw [← Nat.ofDigits_digits 2 m, hd, hval]
    interval_cases x
    · exact ⟨k, Or.inl hm⟩
    · exact ⟨k, Or.inr hm⟩

/-- A070875 is strictly increasing. -/
theorem a070875_strictMono : StrictMono a070875 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [a070875]
    rw [if_neg (by omega), if_pos (by omega), show (2 * k + 1) / 2 = k by omega,
      show 2 * k / 2 = k by omega]
    have := Nat.two_pow_pos k
    omega
  · simp only [a070875]
    rw [if_pos (by omega), if_neg (by omega), show (2 * k + 1 + 1) / 2 = k + 1 by omega,
      show (2 * k + 1) / 2 = k by omega, pow_succ]
    have := Nat.two_pow_pos k
    nlinarith

/-- **Set form of Beck's conjecture.** `A309019(m) - A002487(m) = 1` iff `m`
is a term of A070875. -/
theorem a309019SubStern_eq_one_iff_mem_range (m : ℕ) :
    a309019SubStern m = 1 ↔ m ∈ Set.range a070875 := by
  rw [a309019SubStern_eq_one_iff, mem_range_a070875_iff]

/-- **Beck's conjecture (A070875, George Beck, Mar 26 2022), proved.**

Verbatim: "Conjecture: a(n) = -1 + positions of the ones in
A309019(n+2) - A002487(n+2)."

Read with the index shift recorded in the header (the difference sequence
listed from `m = 0`, 1-based positions, so "`-1 + position`" is `m`): for every
`n`, the `n`-th (0-based, increasing) index `m` with
`A309019(m) - A002487(m) = 1` is `A070875(n)`.  `Nat.nth` is meaningful here
because the set of such `m` is infinite (it is the range of `a070875`). -/
theorem a070875_conjecture (n : ℕ) :
    Nat.nth (fun m => a309019SubStern m = 1) n = a070875 n := by
  have hcomp := Nat.nth_comp_of_strictMono (p := fun m => a309019SubStern m = 1) (n := n)
    a070875_strictMono
    (fun k hk => (a309019SubStern_eq_one_iff_mem_range k).mp hk) ?_
  · have hall : (fun i => a309019SubStern (a070875 i) = 1) = fun _ => True := by
      funext i
      simp only [a309019SubStern_eq_one_iff_mem_range, Set.mem_range_self]
    rw [hall, Nat.nth_true] at hcomp
    exact hcomp.symm
  · intro hfin
    exfalso
    apply Set.infinite_range_of_injective a070875_strictMono.injective
    refine hfin.subset ?_
    intro m hm
    exact (a309019SubStern_eq_one_iff_mem_range m).mpr hm

end Candidates.A070875BinaryExactlyPositions
