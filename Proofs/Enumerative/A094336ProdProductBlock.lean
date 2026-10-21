/-
# A094336 — the triangular block products are never factorials (n ≥ 5)

## OEIS source (retrieved 2026-10-21 with `oeis show A094336` and the live entry)

```
NAME:     Product of next n numbers divided by the largest factorial divisor.
TERMS:    1,1,1,1,3003,969,16445,30566,886163135,2658968130,491796152,
          3340843549855,9129919051926,22487406253165,17391629252325717,
          2248272948937235,15415916972482007401455,50848495433999570877570
KEYWORDS: nonn
COMMENT (the conjecture):
  Conjecture: a(n) > 1 for n > 4.
EXAMPLE:  a(5) = (11*12*13*14*15)/(5!) = 3003.
          a(6) = (16*17*18*19*20*21)/(8!) = 969.
MATHEMATICA:
  Table[a := Product[i, {i, n*(n - 1)/2 + 1, n*(n + 1)/2}]; b := 1;
    While[ IntegerQ[a/(b + 1)! ], b++ ]; a/b!, {n, 1, 20}]
    (* _Stefan Steinerberger_, Mar 14 2006 *)
AUTHOR:   Amarnath Murthy, May 17 2004 (the conjecture is part of the
          original entry).
```

## Status

Open according to the triage: no proof in the entry, and the triage did not
find one in the literature (the general literature on factorial products of
consecutive integers was not searched exhaustively).  This file proves it.

## Proof outline

Write `a = n(n-1)/2`, so the `n`-th block is `a+1, …, a+n` and its product
`P` satisfies `a! * P = (a+n)!`.  If `P = m!` then `m < a + n`, and Legendre's
formula at `p = 2` (`v₂(x!) = x - s₂(x)`) gives `m ≤ n + s₂(a) + s₂(m)`.
For `n ≥ 40` one has `a + n ≤ 2^(n/4)`, so both binary digit sums are at most
`n/4`, whence `m ≤ n + 2(n/4)`; but `(n + t)!² < P²` whenever `2t ≤ n` and
`n ≥ 10`, a contradiction.  The range `5 ≤ n ≤ 39` is a kernel-checked finite
computation (`decide`) bracketing `P` strictly between consecutive factorials.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A094336ProdProductBlock

open Finset
open scoped Nat

/-! ## Definitions mirroring the entry -/

/-- The product of the `n`-th block of the triangular partition
`1 | 2 3 | 4 5 6 | …`, i.e. `∏_{i = n(n-1)/2 + 1}^{n(n+1)/2} i`
(the Mathematica `Product[i, {i, n*(n - 1)/2 + 1, n*(n + 1)/2}]`). -/
def blockProd (n : ℕ) : ℕ := ∏ i ∈ Icc (n * (n - 1) / 2 + 1) (n * (n + 1) / 2), i

/-- The largest `b` with `b! ∣ blockProd n` (searched up to `blockProd n`, which
bounds every such `b` once `blockProd n ≥ 1`). -/
def factIndex (n : ℕ) : ℕ := Nat.findGreatest (fun b => b ! ∣ blockProd n) (blockProd n)

/-- A094336: `a(n) = blockProd n / (largest factorial divisor of blockProd n)`. -/
def a (n : ℕ) : ℕ := blockProd n / (factIndex n)!

/-! ## Basic structure of the block product -/

/-- `n(n+1)/2 = n(n-1)/2 + n`. -/
theorem tri_eq (n : ℕ) : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
  have h := Nat.triangle_succ n
  rw [Nat.add_sub_cancel, Nat.mul_comm (n + 1) n] at h
  exact h

/-- The block product is the ascending factorial `(a+1)(a+2)⋯(a+n)` with
`a = n(n-1)/2`. -/
theorem blockProd_eq_ascFactorial (n : ℕ) :
    blockProd n = (n * (n - 1) / 2 + 1).ascFactorial n := by
  rw [blockProd, tri_eq, Nat.ascFactorial_eq_prod_range, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_eq_prod_range]
  have hlen : n * (n - 1) / 2 + n + 1 - (n * (n - 1) / 2 + 1) = n := by omega
  rw [hlen]

/-- `a! * blockProd n = (a + n)!` with `a = n(n-1)/2`. -/
theorem factorial_mul_blockProd (n : ℕ) :
    (n * (n - 1) / 2)! * blockProd n = (n * (n - 1) / 2 + n)! := by
  rw [blockProd_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

/-- The block product is positive. -/
theorem blockProd_pos (n : ℕ) : 0 < blockProd n := by
  rw [blockProd_eq_ascFactorial]
  exact Nat.ascFactorial_pos _ _

/-- If `b! ∣ blockProd n` but `(b+1)! ∤ blockProd n`, then `b` is the largest
factorial index (this is the stopping rule of the Mathematica program). -/
theorem factIndex_eq_of (n b : ℕ) (h1 : b ! ∣ blockProd n) (h2 : ¬ (b + 1)! ∣ blockProd n) :
    factIndex n = b := by
  have hb : b ≤ blockProd n :=
    (Nat.self_le_factorial b).trans (Nat.le_of_dvd (blockProd_pos n) h1)
  refine Nat.findGreatest_eq_iff.mpr ⟨hb, fun _ => h1, fun c hbc _ hc => h2 ?_⟩
  exact (Nat.factorial_dvd_factorial hbc).trans hc

/-- Evaluation rule for `a n` from a certified factorial index, with the block
product in ascending-factorial form. -/
theorem a_eq_of (n b : ℕ) (h1 : b ! ∣ (n * (n - 1) / 2 + 1).ascFactorial n)
    (h2 : ¬ (b + 1)! ∣ (n * (n - 1) / 2 + 1).ascFactorial n) :
    a n = (n * (n - 1) / 2 + 1).ascFactorial n / b ! := by
  rw [← blockProd_eq_ascFactorial] at h1 h2
  rw [a, factIndex_eq_of n b h1 h2, blockProd_eq_ascFactorial]

/-! ### Ground truth against the entry -/

example : blockProd 5 = 11 * 12 * 13 * 14 * 15 := by decide
example : blockProd 6 = 16 * 17 * 18 * 19 * 20 * 21 := by decide
/-- Boundary: the guard `n > 4` is load-bearing, since the fourth block is `7!`. -/
example : blockProd 4 = 7 ! := by decide
example : factIndex 5 = 5 := factIndex_eq_of 5 5 (by decide) (by decide)
example : factIndex 6 = 8 := factIndex_eq_of 6 8 (by decide) (by decide)
example : a 1 = 1 := by rw [a_eq_of 1 1 (by decide) (by decide)]; decide
example : a 2 = 1 := by rw [a_eq_of 2 3 (by decide) (by decide)]; decide
example : a 3 = 1 := by rw [a_eq_of 3 5 (by decide) (by decide)]; decide
example : a 4 = 1 := by rw [a_eq_of 4 7 (by decide) (by decide)]; decide
example : a 5 = 3003 := by rw [a_eq_of 5 5 (by decide) (by decide)]; decide
example : a 6 = 969 := by rw [a_eq_of 6 8 (by decide) (by decide)]; decide
example : a 7 = 16445 := by rw [a_eq_of 7 9 (by decide) (by decide)]; decide
example : a 8 = 30566 := by rw [a_eq_of 8 11 (by decide) (by decide)]; decide
example : a 9 = 886163135 := by rw [a_eq_of 9 9 (by decide) (by decide)]; decide
example : a 10 = 2658968130 := by rw [a_eq_of 10 11 (by decide) (by decide)]; decide
example : a 11 = 491796152 := by rw [a_eq_of 11 14 (by decide) (by decide)]; decide
example : a 12 = 3340843549855 := by rw [a_eq_of 12 13 (by decide) (by decide)]; decide

/-! ## The finite range `5 ≤ n ≤ 39` -/

/-- Scan `m!, (m+1)!, …` (with `f` the current factorial) for at most `fuel` steps:
returns `true` once a factorial strictly exceeds `P` without ever equalling it. -/
def notFactAux (P : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, m, f =>
    if f = P then false else if P < f then true else notFactAux P fuel (m + 1) (f * (m + 1))

/-- Soundness of the scan: if it succeeds from `m` with `f = m!`, then no `j!` with
`m ≤ j` equals `P`. -/
theorem notFactAux_sound (P : ℕ) :
    ∀ (fuel m : ℕ), notFactAux P fuel m (m !) = true → ∀ j, m ≤ j → j ! ≠ P := by
  intro fuel
  induction fuel with
  | zero => intro m h; simp [notFactAux] at h
  | succ fuel ih =>
    intro m h j hj
    have hne : m ! ≠ P := by
      intro heq
      simp [notFactAux, heq] at h
    by_cases hlt : P < (m !)
    · exact (Nat.lt_of_lt_of_le hlt (Nat.factorial_le hj)).ne'
    · have hrec : notFactAux P fuel (m + 1) ((m + 1)!) = true := by
        simpa [notFactAux, hne, hlt, Nat.factorial_succ, Nat.mul_comm] using h
      rcases Nat.eq_or_lt_of_le hj with hmj | hmj
      · exact hmj ▸ hne
      · exact ih (m + 1) hrec j hmj

/-- Kernel-checked computation: for `5 ≤ n ≤ 39` the block product lies strictly
between two consecutive factorials. -/
theorem small_check : ((List.range' 5 35).all fun n =>
    notFactAux ((n * (n - 1) / 2 + 1).ascFactorial n) 120 0 1) = true := by
  decide

/-- For `5 ≤ n ≤ 39` the block product is not a factorial. -/
theorem blockProd_ne_factorial_small (n m : ℕ) (hn : 5 ≤ n) (hn' : n ≤ 39) :
    blockProd n ≠ m ! := by
  have hmem : n ∈ List.range' 5 35 := by
    rw [List.mem_range']
    exact ⟨n - 5, by omega, by omega⟩
  have hn_check := List.all_eq_true.mp small_check n hmem
  rw [blockProd_eq_ascFactorial]
  exact (notFactAux_sound _ 120 0 hn_check m (Nat.zero_le m)).symm

/-! ## The asymptotic range `40 ≤ n` -/

/-- The binary digit sum of `x < 2^k` is at most `k`. -/
theorem digitSum_le_of_lt_two_pow {x k : ℕ} (hx : x < 2 ^ k) : (Nat.digits 2 x).sum ≤ k := by
  have hlen : (Nat.digits 2 x).length ≤ k := (Nat.digits_length_le_iff (by norm_num) x).mpr hx
  have hdig : ∀ d ∈ Nat.digits 2 x, d ≤ 1 := fun d hd =>
    Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hd)
  calc (Nat.digits 2 x).sum ≤ (Nat.digits 2 x).length • 1 := List.sum_le_card_nsmul _ _ hdig
    _ = (Nat.digits 2 x).length := by simp
    _ ≤ k := hlen

/-- Legendre at `p = 2`: `v₂(x!) + s₂(x) = x`. -/
theorem padicValNat_two_factorial_add (x : ℕ) :
    padicValNat 2 (x !) + (Nat.digits 2 x).sum = x := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) x
  have hle := Nat.digit_sum_le 2 x
  simp only [Nat.add_one_sub_one, one_mul] at h
  omega

/-- `(4k+3)(4k+4) ≤ 2^(k+1)` for `k ≥ 10`. -/
theorem quad_le_two_pow (k : ℕ) (hk : 10 ≤ k) : (4 * k + 3) * (4 * k + 4) ≤ 2 ^ (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

/-- For `n ≥ 40`, the block end `n(n-1)/2 + n` is at most `2^(n/4)`. -/
theorem blockEnd_le_two_pow (n : ℕ) (hn : 40 ≤ n) : n * (n - 1) / 2 + n ≤ 2 ^ (n / 4) := by
  have hk : 10 ≤ n / 4 := by omega
  have hq := quad_le_two_pow (n / 4) hk
  have hn4 : n ≤ 4 * (n / 4) + 3 := by omega
  have hmul : n * (n + 1) ≤ (4 * (n / 4) + 3) * (4 * (n / 4) + 4) :=
    Nat.mul_le_mul hn4 (by omega)
  rw [← tri_eq, pow_succ] at *
  have h2 : n * (n + 1) / 2 * 2 ≤ n * (n + 1) := Nat.div_mul_le_self _ _
  omega

/-- Size bound: for `n ≥ 10` and `2t ≤ n`, `((n+t)!)² < (block product)²`. -/
theorem factorial_sq_lt (n t : ℕ) (hn : 10 ≤ n) (ht : 2 * t ≤ n) :
    ((n + t)!) ^ 2 < ((n * (n - 1) / 2 + 1).ascFactorial n) ^ 2 := by
  set A := n * (n - 1) / 2 with hA
  have h2A : 2 * A = n * (n - 1) := by
    rw [hA]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  -- upper bound on the factorial
  have hfact : (n + t)! ≤ n ^ n * (2 * n) ^ t := by
    rw [← Nat.factorial_mul_ascFactorial]
    refine Nat.mul_le_mul (Nat.factorial_le_pow n) ?_
    calc (n + 1).ascFactorial t ≤ (n + t) ^ t := Nat.ascFactorial_le_pow_add n t
      _ ≤ (2 * n) ^ t := Nat.pow_le_pow_left (by omega) t
  have hfact2 : ((n + t)!) ^ 2 ≤ (2 * n ^ 3) ^ n := by
    calc ((n + t)!) ^ 2 ≤ (n ^ n * (2 * n) ^ t) ^ 2 := Nat.pow_le_pow_left hfact 2
      _ = (n ^ 2) ^ n * (2 * n) ^ (2 * t) := by ring
      _ ≤ (n ^ 2) ^ n * (2 * n) ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ht)
      _ = (2 * n ^ 3) ^ n := by ring
  -- lower bound on the block product
  have hbase : 2 * n ^ 3 < (A + 1) ^ 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h2A
    have hj : 9 ≤ j := by omega
    nlinarith
  have hblock : (2 * n ^ 3) ^ n < ((A + 1) ^ 2) ^ n :=
    Nat.pow_lt_pow_left hbase (by omega)
  calc ((n + t)!) ^ 2 ≤ (2 * n ^ 3) ^ n := hfact2
    _ < ((A + 1) ^ 2) ^ n := hblock
    _ = ((A + 1) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ((A + 1).ascFactorial n) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_succ_le_ascFactorial (A + 1) n) 2

/-- For `n ≥ 40` the block product is not a factorial. -/
theorem blockProd_ne_factorial_large (n m : ℕ) (hn : 40 ≤ n) : blockProd n ≠ m ! := by
  intro hPm
  set A := n * (n - 1) / 2 with hA
  have hfm := factorial_mul_blockProd n
  rw [← hA, hPm] at hfm
  -- `A ≥ 2`, so `A! ≥ 2`
  have hA2 : 2 ≤ A := by
    have h4 : 2 * 2 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    rw [hA]; exact (Nat.le_div_iff_mul_le (by norm_num)).mpr h4
  have hAfact : 2 ≤ A ! := (Nat.self_le_factorial A).trans' hA2
  -- step 1: `m < A + n`
  have hm_lt : m < A + n := by
    by_contra hge
    have hle : (A + n)! ≤ m ! := Nat.factorial_le (Nat.le_of_not_lt hge)
    have hpos : 0 < m ! := Nat.factorial_pos m
    nlinarith
  -- step 2: Legendre at 2
  have hval : padicValNat 2 ((A + n)!) = padicValNat 2 (A !) + padicValNat 2 (m !) := by
    rw [← hfm, padicValNat.mul (Nat.factorial_ne_zero A) (Nat.factorial_ne_zero m)]
  have hLa := padicValNat_two_factorial_add A
  have hLm := padicValNat_two_factorial_add m
  have hLb := padicValNat_two_factorial_add (A + n)
  have hm_le : m ≤ n + (Nat.digits 2 A).sum + (Nat.digits 2 m).sum := by omega
  -- step 3: digit sums are at most `n / 4`
  have hend := blockEnd_le_two_pow n hn
  rw [← hA] at hend
  have hsA := digitSum_le_of_lt_two_pow (x := A) (k := n / 4) (by omega)
  have hsm := digitSum_le_of_lt_two_pow (x := m) (k := n / 4) (by omega)
  have hm_le' : m ≤ n + 2 * (n / 4) := by omega
  -- step 4: size contradiction
  have hsq := factorial_sq_lt n (2 * (n / 4)) (by omega) (by omega)
  rw [← blockProd_eq_ascFactorial, hPm] at hsq
  have hlt : (n + 2 * (n / 4))! < m ! := (Nat.pow_lt_pow_iff_left (by norm_num)).mp hsq
  exact absurd (Nat.factorial_le hm_le') (Nat.not_le.mpr hlt)

/-! ## Main results -/

/-- **Block products are not factorials.** For every `n ≥ 5`, the product
`(n(n-1)/2 + 1)(n(n-1)/2 + 2)⋯(n(n+1)/2)` of the `n`-th block of
`1 | 2 3 | 4 5 6 | …` is not equal to `m!` for any `m` (for `n = 1, 2, 3, 4` it is
`1, 3!, 5!, 7!`). This is the content of the A094336 conjecture. -/
theorem blockProd_ne_factorial (n m : ℕ) (hn : 5 ≤ n) : blockProd n ≠ m ! := by
  rcases Nat.lt_or_ge n 40 with hlt | hge
  · exact blockProd_ne_factorial_small n m hn (by omega)
  · exact blockProd_ne_factorial_large n m hge

/-- `factIndex n` really indexes a factorial divisor of `blockProd n`. -/
theorem factorial_factIndex_dvd (n : ℕ) : (factIndex n)! ∣ blockProd n :=
  Nat.findGreatest_spec (P := fun b => b ! ∣ blockProd n) (Nat.zero_le _) (by simp)

/-- **A094336 conjecture (Amarnath Murthy, May 17 2004): `a(n) > 1` for `n > 4`.**
Here `a(n)` is the `n`-th block product divided by its largest factorial divisor. -/
theorem one_lt_a (n : ℕ) (hn : 4 < n) : 1 < a n := by
  obtain ⟨q, hq⟩ := factorial_factIndex_dvd n
  have hpos := blockProd_pos n
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hq
    omega
  have hq1 : q ≠ 1 := by
    rintro rfl
    rw [Nat.mul_one] at hq
    exact blockProd_ne_factorial n (factIndex n) hn hq
  have haq : a n = q := by
    rw [a, hq, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]
  omega

end Candidates.A094336ProdProductBlock
